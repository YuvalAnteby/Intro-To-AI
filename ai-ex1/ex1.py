# Use of AI 
#
# LLMs used: Claude Fable 5.2, Astra 6, and Codex.
#
# Claude Fable 5.2:
#   - Wrote the code in this file: the state representation, successor, goal_test and h_astar.
#   - Helped improving the heuristic and the successor pruning rules so that the given problems are
#     solved within the time limit (the optimisations).
#   - Wrote the mathematical arguments that the heuristic is admissible and that the pruning rules and the
#     merging of symmetric states keep an optimal plan, and the test tools used to check them against an
#     independent exhaustive solver.
#
# Astra:
#   - reviewed those proofs and the test tools, and pointed out errors that were then corrected.
# Codex:
#   - Added truck-flow and whole-sail lower bounds, corridor pruning, and caches.
#   - Extended the proofs and regression checks and ran the independent validators and benchmarks.
#   - Fixed numeric cargo and ferry bounds using integer relaxations and the checker's capacity tests.
#   - Added incremental canonicalization and a proof of equivalence to the original canonical keys.
#   - Reused ferry occupancy for BOARD checks and proved equivalence with both optimizations enabled.
#   - Cached each state's hash lazily, preserving the exact key and hash values.
#   - Added state-based stubborn-set pruning, its capacity/commutation proof, and a safe closure fallback.
#   - Disabled endpoint-only corridor pruning after proving a retained-state suffix counterexample.
#
# Claude Opus 5.5:
#   - Re-derived every part of the heuristic and wrote a complete formal admissibility proof
#     (HEURISTIC_PROOF.md).
#   - Added to the heuristic: capacity-aware visit requirements on every cut, lower bounds for road cycles
#     (ball families and per-cycle fractions), and a stronger first-entry selection, then reduced their
#     cost per state after the timings showed it. That work did not change the successor function.
#   - In a later session: proposed four state-based successor rules (lazy empty sails, effective capacities,
#     resting useless trucks, purposeful empty drives), wrote their formal proof (SUCCESSOR_RULES_PROOF.md),
#     implemented them behind the switches OPT_EMPTY_SAIL, OPT_EFFCAP, OPT_USELESS and OPT_TOWARD, and wrote
#     an independent exhaustive solver used only to check the implementation.
#   - Then, under the reading that one optimal plan from the initial state must survive, designed the
#     history-based rules H1-H4 (focus, no U-turn, fresh board, board next) from scratch, without using any
#     earlier history-based version of this file, wrote their proof (HISTORY_RULES_PROOF.md, including a
#     re-derivation of the corridor rule, which is switched on under that reading), implemented them, and
#     extended the exhaustive checker with a mode for that reading.
#   - After an outside review found that the no-U-turn filter tested the truck's position instead of the drive
#     action (so the delivery that completes a component could be dropped after the vehicle reset), fixed the
#     filter, corrected the proof, and made the checker generate the instances that expose such bugs.
#   - After a second review: Rule B's subset sums no longer overflow on huge integer weights (exact sums with
#     bounded memory, otherwise Rule B is off for the instance), the proofs state their scope more precisely,
#     and the checker compares the pruned optimum across states with equal canonical keys.
#
# Python's hash contract and tuple-hash implementation notes were consulted for the hash cache:
# https://docs.python.org/3/reference/datamodel.html#object.__hash__
# https://github.com/python/cpython/issues/131525

import ex1_check
import search
import utils

from bisect import bisect_left, insort_right
from itertools import accumulate
from operator import itemgetter, sub

id = ["212152896"]

# Pruning switches. The history-based rules further below (OPT_HISTORY ...) are proved in HISTORY_RULES_PROOF.md,
# written from scratch for this version under the reading that an optimal plan from the initial state must survive.
OPT_TWINS = True      # symmetry between identical trucks / ferries / packages
OPT_FORCED = True     # a truck standing at the goal of a package it carries may only unload it
OPT_COMP = True       # independent parts of the map are solved one after the other
OPT_SYM = True        # states that differ only by a renaming of identical objects are the same state
OPT_DEAD = True       # never enter a dead end of the map where there is nothing to do
OPT_BARREN = False    # disabled pending a proof that does not rely on truck focus
OPT_FIRST = True      # heuristic only: first-entry lower bound
OPT_CORRIDOR = True   # transfers only at anchors: valid under condition 1 (HISTORY_RULES_PROOF.md Lemma 1), not under 2

# Representation only: compute the same canonical key from the parent's key and the action.
OPT_INCREMENTAL_CANON = False
OPT_OCCUPANCY_REUSE = True  # reuse parent-state ferry counts for all BOARD checks
OPT_HASH_CACHE = False      # profiling found no benefit on the target Python 3.12 runtime
OPT_PARTIAL_ORDER = False   # proved safe; opt in to benchmark (PARTIAL_ORDER_PROOF.md)

# State-based successor rules, proved in SUCCESSOR_RULES_PROOF.md. They read only the current state. In the
# configuration that proof covers (history, corridor, barren and partial-order rules off) every retained state keeps
# its world-optimal continuation. The delivered defaults turn history and corridors on, and then the guarantee is
# the initial-state one of HISTORY_RULES_PROOF.md. Active only with integer weights and capacities.
# OPT_PARTIAL_ORDER is ignored while any of them is on (its proof assumes the old successor list).
OPT_EMPTY_SAIL = True   # Rule A: an empty ferry sails only to a port where a truck that is not useless stands
OPT_EFFCAP = True       # Rule B: twin/merge classes by effective capacity (reachable load, usable truck slots)
_DENSE_BITS = 1 << 20   # Rule B: a capacity up to this is handled with a bitset of subset sums
_SUBSET_SUMS = 1 << 16  # Rule B: above it, at most this many distinct sums, else Rule B is off for the instance
OPT_USELESS = True      # Rule C: an empty standing truck that cannot carry any undelivered package never acts
OPT_TOWARD = True       # Rule D: an empty standing truck drives only along a shortest road path to a target

# History-based normal forms, proved in HISTORY_RULES_PROOF.md under the reading "an optimal plan from the initial
# state must survive" (condition 1). The history is stored in the leading field of the state tuple and is part of
# the canonical key. Active only with integer weights and capacities.
OPT_HISTORY = True      # master switch for the four rules below
OPT_FOCUS = True        # H1: after a DRIVE or LOAD of a truck, the next action is that truck's (or an empty sail to it)
OPT_UTURN = True        # H2: a truck in focus does not drive straight back to where it came from (needs OPT_FOCUS)
OPT_FRESH = True        # H3: a truck that boarded a ferry does not disembark before the ferry sails
OPT_NEEDBOARD = True    # H4: an empty sail is immediately followed by a BOARD onto that ferry (needs OPT_FOCUS)


_NOTHING = float("inf")     # "no undelivered package" for the uselessness test of Rules A and C


def _canon_edit(items, old=None, new=None):
    """Remove/add one occurrence in an immutable sorted multiset, preserving duplicates."""
    result = list(items)
    if old is not None:
        i = bisect_left(result, old)
        if i == len(result) or result[i] != old:
            raise ValueError("Canonical descriptor missing from parent key")
        del result[i]
    if new is not None:
        insort_right(result, new)
    return tuple(result)


class _State(object):
    """A state: the tuple s described in LogisticsProblem.__init__.

    Two states are equal if one becomes the other by renaming objects that are fully interchangeable
    (trucks with the same capacity, ferries of the same line and size, packages with the same weight and
    goal). The search then expands only one of them. The key also describes the history field (state[0]),
    through the objects it names, so states with different pending obligations are never merged."""
    __slots__ = ("s", "k", "pr", "parts", "kh")

    def __init__(self, pr, s, key=None, parts=None):
        self.s = s
        self.k = key
        self.pr = pr
        # Immutable cargo-by-truck and descriptor-by-ferry tuples; no parent reference.
        self.parts = parts
        self.kh = None

    def __hash__(self):
        if self.k is None:
            self.k = self.pr._canon(self.s)
        if not OPT_HASH_CACHE:
            return hash(self.k)
        value = self.kh
        if value is None:
            value = hash(self.k)
            self.kh = value
        return value

    def __eq__(self, other):
        if self.k is None:
            self.k = self.pr._canon(self.s)
        if other.k is None:
            other.k = other.pr._canon(other.s)
        return self.k == other.k

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        return "State%r" % (self.s,)


class _Memo(dict):
    """A dictionary that computes a missing value with a function of the key."""

    def __init__(self, fn):
        dict.__init__(self)
        self.fn = fn

    def __missing__(self, key):
        value = self[key] = self.fn(key)
        return value


class _Stubborn:
    """State-based strong stubborn sets; see PARTIAL_ORDER_PROOF.md.

    Operators use their destination, not their source, as the movement ID.
    The dependency masks overapproximate interference in every legal state.
    Nonapplicable operators add a necessary enabling set. Applicable ones
    also add the representative retained by the existing twin filters.
    """

    def __init__(self, pr):
        self.pr = pr
        n, T, F, P = pr.n, pr.T, pr.F, pr.P
        self.ops = []
        self.lookup = {}
        self.drive = [[0] * n for _ in range(T)]
        self.load = [[0] * T for _ in range(P)]
        self.unload = [[0] * T for _ in range(P)]
        self.board = [[0] * F for _ in range(T)]
        self.leave = [[0] * F for _ in range(T)]
        self.sail = [[0] * n for _ in range(F)]

        def add(kind, x, y):
            bit = 1 << len(self.ops)
            self.ops.append((kind, x, y))
            return bit

        self.incoming = [set() for _ in range(n)]
        for u, neighbours in enumerate(pr.adj_go):
            for v in neighbours:
                self.incoming[v].add(u)
        for t in range(T):
            for v, sources in enumerate(self.incoming):
                if sources and (not pr.node_rank or pr.node_rank[v] == pr.trank[t]):
                    bit = self.drive[t][v] = add(0, t, v)
                    for u in sources:
                        self.lookup['DRIVE{%d,%d,%d}' % (pr.tids[t], u, v)] = bit
        for p in range(P):
            for t in range(T):
                if pr.prank[p] != pr.trank[t] or pr.pw[p] > pr.tcap[t]:
                    continue
                self.load[p][t] = add(1, p, t)
                self.unload[p][t] = add(2, p, t)
                self.lookup['LOAD{%d,%d}' % (pr.pids[p], pr.tids[t])] = self.load[p][t]
                self.lookup['UNLOAD{%d,%d}' % (pr.pids[p], pr.tids[t])] = self.unload[p][t]
        for t in range(T):
            for f in range(F):
                if pr.fdead[f] or pr.trank[t] != pr.frank[f] or pr.fcap[f] < 1:
                    continue
                self.board[t][f] = add(3, t, f)
                self.leave[t][f] = add(4, t, f)
                self.lookup['BOARD{%d,%d}' % (pr.tids[t], pr.fids[f])] = self.board[t][f]
                self.lookup['DISEMBARK{%d,%d}' % (pr.tids[t], pr.fids[f])] = self.leave[t][f]
        for f in range(F):
            for v in pr.sail_to[f]:
                bit = self.sail[f][v] = add(5, f, v)
                for u in pr.fports[f]:
                    if u != v:
                        self.lookup['SAIL{%d,%d,%d}' % (pr.fids[f], u, v)] = bit

        # Disjoint one-bit entries make sum a bitwise union here.
        self.ld = [sum(row) for row in self.load]
        self.ud = [sum(row) for row in self.unload]
        self.dm = [sum(row) for row in self.drive]
        self.bm = [sum(row) for row in self.board]
        self.em = [sum(row) for row in self.leave]
        self.sm = [sum(row) for row in self.sail]
        self.lt = [sum(self.load[p][t] for p in range(P)) for t in range(T)]
        self.ut = [sum(self.unload[p][t] for p in range(P)) for t in range(T)]
        self.bf = [sum(self.board[t][f] for t in range(T)) for f in range(F)]
        self.ef = [sum(self.leave[t][f] for t in range(T)) for f in range(F)]
        self.port_ferries = [tuple(f for f in range(F) if v in pr.fports[f]) for v in range(n)]

        self.dep = []
        for kind, x, y in self.ops:
            if kind == 0:  # DRIVE: the same truck's standing actions can interfere.
                dep = self.dm[x] | self.bm[x] | self.lt[x] | self.ut[x]
            elif kind == 1:  # LOAD: same package, or competing LOADs into the same truck.
                dep = self.dm[y] | self.bm[y] | self.ld[x] | self.lt[y]
            elif kind == 2:  # UNLOAD only frees capacity; other handling actions commute.
                dep = self.dm[y] | self.bm[y]
            elif kind == 3:  # BOARD: same truck, competing BOARDs, or moving this ferry.
                dep = self.dm[x] | self.bm[x] | self.lt[x] | self.ut[x] | self.sm[y]
                if pr.fcap[y] < T:
                    dep |= self.bf[y]
            elif kind == 4:  # DISEMBARK frees a slot; only its ferry moving interferes.
                dep = self.sm[y]
            else:  # SAIL: dock position is read by BOARD and DISEMBARK.
                dep = self.sm[x] | self.bf[x] | self.ef[x]
            self.dep.append(dep)

        self.drive_nes = [[0] * n for _ in range(T)]
        self.board_nes = [[0] * F for _ in range(T)]
        for t in range(T):
            for v, sources in enumerate(self.incoming):
                mask = sum(self.drive[t][u] for u in sources)
                for f in range(F):
                    if sources.intersection(pr.fports[f]):
                        mask |= self.leave[t][f]
                self.drive_nes[t][v] = mask
            for f in range(F):
                mask = sum(self.drive[t][v] for v in pr.fports[f])
                ports = set(pr.fports[f])
                for other in range(F):
                    if ports.intersection(pr.fports[other]):
                        mask |= self.leave[t][other]
                self.board_nes[t][f] = mask

    def keep(self, state, raw):
        """Return retained raw indices; None means retain everything, in the same order."""
        if len(raw) <= 1:
            return None
        pr = self.pr
        n, T, F, P = pr.n, pr.T, pr.F, pr.P
        truck = state[1:pr.IF]
        dock = state[pr.IF:pr.IP]
        package = state[pr.IP:]
        inside = [[] for _ in range(T)]
        weight = [0] * T
        aboard = [[] for _ in range(F)]
        seed = 0
        for p, loc in enumerate(package):
            if loc >= n:
                t = loc - n
                inside[t].append(p)
                weight[t] += pr.pw[p]
            if not seed and loc != pr.pgoal[p] and (not pr.multi or pr.prank[p] == pr._rank):
                seed = self.unload[p][loc-n] if loc >= n else self.ld[p]
        for t, loc in enumerate(truck):
            if loc >= n:
                aboard[(loc-n) >> 1].append(t)
        if not seed:
            return None

        # Make each selected applicable action's existing twin representative available.
        tr, fr, ps = list(range(T)), list(range(F)), list(range(P))
        if OPT_TWINS:
            seen = {}
            for t in range(T):
                if not inside[t]:
                    tr[t] = seen.setdefault((truck[t], pr.tcls[t]), t)
            seen = {}
            for f in range(F):
                if not aboard[f]:
                    fr[f] = seen.setdefault((dock[f], pr.fcls[f]), f)
            seen = {}
            for p in range(P):
                ps[p] = seen.setdefault((package[p], pr.pcls[p]), p)

        # Once every baseline successor is selected, further closure cannot prune anything.
        bits = [self.lookup.get(action, 0) for action, _ in raw]
        if 0 in bits:
            return None
        raw_mask = 0
        for bit in bits:
            raw_mask |= bit
        members = pending = seed
        applicable = 0
        steps = 0
        while pending:
            if members & raw_mask == raw_mask:
                return None
            steps += 1
            if steps > 96:
                return None  # Abandon the whole reduction, never use an unfinished closure.
            bit = pending & -pending
            pending ^= bit
            index = bit.bit_length()-1
            kind, x, y = self.ops[index]
            extra = 0
            enabled = False
            representative = bit
            if kind == 0:  # DRIVE(t, destination)
                loc = truck[x]
                if loc >= n:
                    extra = self.leave[x][(loc-n) >> 1]
                elif loc in self.incoming[y]:
                    enabled = True
                    representative = self.drive[tr[x]][y]
                else:
                    extra = self.drive_nes[x][y]
            elif kind == 1:  # LOAD(p, t)
                loc, tl = package[x], truck[y]
                if loc == pr.pgoal[x]:
                    pass  # Delivered packages never move again in this graph.
                elif loc >= n:
                    extra = self.unload[x][loc-n]
                elif tl >= n:
                    extra = self.leave[y][(tl-n) >> 1]
                elif tl != loc:
                    extra = self.drive[y][loc] | (self.ld[x] & ~bit)
                    for f in self.port_ferries[loc]:
                        extra |= self.leave[y][f]
                elif weight[y] + pr.pw[x] > pr.tcap[y]:
                    for p in inside[y]:
                        extra |= self.unload[p][y]
                else:
                    enabled = True
                    representative = self.load[ps[x]][tr[y]]
            elif kind == 2:  # UNLOAD(p, t)
                tl = truck[y]
                if package[x] != n+y:
                    extra = self.load[x][y]
                elif tl >= n:
                    extra = self.leave[y][(tl-n) >> 1]
                elif OPT_CORRIDOR and tl not in pr.transfer_sites:
                    extra = self.dm[y] | self.bm[y]
                else:
                    enabled = True
                    representative = self.unload[ps[x]][y]
            elif kind == 3:  # BOARD(t, f)
                loc = truck[x]
                if loc >= n:
                    extra = self.leave[x][(loc-n) >> 1]
                elif loc != dock[y]:
                    extra = self.board_nes[x][y] | self.sail[y][loc]
                elif len(aboard[y]) >= pr.fcap[y]:
                    for t in aboard[y]:
                        extra |= self.leave[t][y]
                else:
                    enabled = True
                    representative = self.board[tr[x]][fr[y]]
            elif kind == 4:  # DISEMBARK(t, f)
                if truck[x] >= n and (truck[x]-n) >> 1 == y:
                    enabled = True
                    representative = self.leave[tr[x]][y]
                else:
                    extra = self.board[x][y]
            else:  # SAIL(f, destination)
                if dock[x] != y:
                    enabled = True
                    representative = self.sail[fr[x]][y]
                else:
                    extra = self.sm[x] & ~bit
            if enabled:
                applicable |= bit
                extra = self.dep[index] | representative
            extra &= ~members
            members |= extra
            pending |= extra

        keep = [i for i, bit in enumerate(bits) if bit & applicable]
        # Retaining extra actions is always safe. An empty closure need not be used as a dead-end test.
        return keep if keep and len(keep) < len(raw) else None


class _Region:
    """One connected part of the map (roads + ferry routes) and the lower bound on the cost of moving in it.

    The auxiliary graph has a node for every location and for every ferry, a road edge for every road
    and a "port edge" (port, ferry) for every port a ferry serves. Every bridge of this graph is a cut
    that all the transport between its two sides has to cross, so the actions that cross different
    bridges are different actions and their lower bounds can be added."""

    def __init__(self, pr, nodes, rank):
        self.pr = pr
        self.rank = rank
        n, F = pr.n, pr.F
        nodeset = set(nodes)
        self.trucks = [t for t in range(pr.T) if pr.s0[1 + t] in nodeset]
        self.ntrucks = len(self.trucks)
        self.pkgs = [p for p in range(pr.P) if pr.pgoal[p] in nodeset]
        caps = [pr.bound_caps[t] for t in self.trucks]
        self.caps = caps
        self.cmax = max(max(caps), 1) if caps else 1
        cm = self.cmax
        self.pbig = {p: (1 if 2 * pr.bound_weights[p] > cm else 0) for p in self.pkgs}

        # ---- edges of the auxiliary graph: (u, v, ferry or -1)
        edges = []
        for a in nodes:
            if a < n:
                for b in pr.adj[a]:
                    if a < b:
                        edges.append((a, b, -1))
        for f in range(F):
            if n + f in nodeset:
                for a in pr.gports[f]:
                    edges.append((a, n + f, f))
        adj = {x: [] for x in nodes}
        for i, (u, v, _) in enumerate(edges):
            adj[u].append((v, i))
            adj[v].append((u, i))
        isb = self._bridges(nodes, adj, len(edges))
        self.bridge_roads = set()
        self.bridge_ports = set()
        for i, (u, v, f) in enumerate(edges):
            if isb[i]:
                if f < 0:
                    self.bridge_roads.add((u, v))
                    self.bridge_roads.add((v, u))
                else:
                    self.bridge_ports.add((f, u))

        # ---- 2-edge-connected components and the tree of bridges
        cc = {}
        ncc = 0
        for s in nodes:
            if s in cc:
                continue
            cc[s] = ncc
            stack = [s]
            while stack:
                x = stack.pop()
                for y, i in adj[x]:
                    if not isb[i] and y not in cc:
                        cc[y] = ncc
                        stack.append(y)
            ncc += 1
        self.cc = cc
        tadj = [[] for _ in range(ncc)]
        for i, (u, v, f) in enumerate(edges):
            if isb[i]:
                tadj[cc[u]].append((cc[v], i))
                tadj[cc[v]].append((cc[u], i))
        root = cc[nodes[0]]
        tin = [0] * ncc
        tout = [0] * ncc
        parent = [-1] * ncc
        pedge = [-1] * ncc
        depth = [0] * ncc
        order = []
        stack = [(root, 0)]
        seen = [False] * ncc
        seen[root] = True
        while stack:
            c, k = stack.pop()
            if k == 0:
                tin[c] = len(order)
                order.append(c)
            if k < len(tadj[c]):
                stack.append((c, k + 1))
                d, i = tadj[c][k]
                if not seen[d]:
                    seen[d] = True
                    parent[d] = c
                    pedge[d] = i
                    depth[d] = depth[c] + 1
                    stack.append((d, 0))
            else:
                tout[c] = len(order)
        self.parent, self.depth, self.tin = parent, depth, tin
        self.pos1 = {x: tin[cc[x]] + 1 for x in nodes}      # index into the array of point masses
        self.zero = [0] * (ncc + 1)

        # ---- the cuts: one for every bridge, road bridges first
        road, port = [], []
        for c in range(ncc):
            if c == root:
                continue
            u, v, f = edges[pedge[c]]
            if f < 0:
                road.append((c, None))
            else:
                port.append((c, (f, u, cc[u] == c)))     # (ferry, port, the subtree is the side of the port)
        cuts = road + port
        self.nroad = len(road)
        self.ncut = len(cuts)
        self.cut_lo = [tin[c] for c, _ in cuts]
        self.cut_hi = [tout[c] for c, _ in cuts]
        self.cut_port = [info for _, info in cuts]
        if cuts:
            self.iglo = itemgetter(*(self.cut_lo + [0]))        # the extra 0 keeps the result a tuple
            self.ighi = itemgetter(*(self.cut_hi + [0]))
        # ---- dead ends: a side of a bridge where no package starts or has to go and no truck starts.
        # Nothing useful can happen there, so no truck or ferry ever has to cross into it: whatever a
        # plan does inside could be done at the entrance instead, for less.
        mark = set(pr.s0[1 + t] for t in self.trucks)
        for p in self.pkgs:
            if pr.s0[pr.IP + p] in cc:
                mark.add(pr.s0[pr.IP + p])
            mark.add(pr.pgoal[p])
        live = [0] * (ncc + 1)
        for x in mark:
            live[tin[cc[x]] + 1] += 1
        live = list(accumulate(live))
        self.dead_drive = set()
        self.dead_sail = set()
        self.dead_ferry = set()
        self.far = {}               # (from, to) of a road bridge -> the locations on the far side, as a bit mask
        allmask = 0
        for x in nodes:
            if x < n:
                allmask |= 1 << x
        members = [0] * ncc
        for x in nodes:
            if x < n:
                members[tin[cc[x]]] |= 1 << x
        for c, info in cuts:
            u, v, f = edges[pedge[c]]
            if info is None:
                inmask = 0
                for k in range(tin[c], tout[c]):
                    inmask |= members[k]
                xin, xout = (u, v) if cc[u] == c else (v, u)
                self.far[(xout, xin)] = inmask
                self.far[(xin, xout)] = allmask & ~inmask
            inside_live = live[tout[c]] - live[tin[c]]
            outside_live = live[ncc] - inside_live
            if info is None:
                xin, xout = (u, v) if cc[u] == c else (v, u)
                if not inside_live:
                    self.dead_drive.add((xout, xin))
                if not outside_live:
                    self.dead_drive.add((xin, xout))
            else:
                port_side_live, ferry_side_live = (inside_live, outside_live) if info[2] else (outside_live, inside_live)
                if not port_side_live:
                    self.dead_sail.add((f, u))
                if not ferry_side_live:
                    self.dead_ferry.add(f)
        index = {c: i for i, (c, _) in enumerate(cuts)}
        rootmask = [0] * ncc
        for c in order:
            if c != root:
                rootmask[c] = rootmask[parent[c]] | (1 << index[c])
        self.rmask = {x: rootmask[cc[x]] for x in nodes}

        # ---- packed fields of a cut value: weight out, weight in, big packages out, big in, trucks inside
        total_w = sum(pr.bound_weights[p] for p in self.pkgs) + 1
        self.WB = WB = total_w.bit_length() + 1
        self.BB = BB = (len(self.pkgs) + 1).bit_length() + 1
        self.WM = (1 << WB) - 1
        self.BM = (1 << BB) - 1
        self.TSH = 2 * WB + 2 * BB
        self.WFM = (1 << self.TSH) - 1
        self.tbit = {t: 1 << (self.TSH + j) for j, t in enumerate(self.trucks)}
        self.upd = {p: _Memo(lambda x, p=p: self._updates(p, x)) for p in self.pkgs}
        self.gm = {}
        self.pcm = {}
        self.mstruct = {}
        self.road0 = _Memo(lambda v: self.g(v, 0, 0))
        self.road11 = _Memo(lambda v: self.g(v, 1, 1) - self.g(v, 0, 0))
        # extra crossings of a road bridge if y trucks cross it out of / into the subtree
        self.exo = _Memo(lambda y: _Memo(lambda v: self.g(v, y, 0) - self.g(v, 0, 0)))
        self.exi = _Memo(lambda y: _Memo(lambda v: self.g(v, 0, y) - self.g(v, 0, 0)))
        self.split = _Memo(self._split)
        self.first_in = _Memo(self._first_in)
        self.first_out = _Memo(self._first_out)
        self.road_extra_cache = {}
        self.rroad = range(self.nroad)
        self.flow_cost = _Memo(self._flow_cost)
        self.port_flow_cost = _Memo(self._port_flow_cost)
        self.flow_cache = {}
        self.flow_steps = {}
        self.flow_merges = {}
        self.flow_zero = (0,) * (self.ntrucks + 1)
        self.flow_root = root
        self.flow_order = [(c, parent[c], index[c]) for c in reversed(order) if c != root]
        # Two visit flags sit above the truck bits of a road-cut value (proof, Lemma 2(v)):
        # VIB: a lying package inside cannot be loaded by any truck inside, so some truck must enter.
        # VOB: the same for the outside, so some truck must leave.
        self.TMASK = (1 << self.ntrucks) - 1
        self.VSH = self.TSH + self.ntrucks
        self.VIB = 1 << self.VSH
        self.VOB = 1 << (self.VSH + 1)
        self.ALLC = (1 << self.ncut) - 1        # every bridge cut, as bits over cut indices
        self.ROADS = (1 << self.nroad) - 1      # the road-bridge cuts
        # largest capacity among the region's trucks in a bit mask (-1 for no truck)
        self.mcap = _Memo(lambda m: max((c for j, c in enumerate(caps) if (m >> j) & 1), default=-1))

        # ---- pieces: groups of locations inside a 2-edge-connected part that are joined by roads.
        # All the transport between a piece (with everything hanging on it) and the rest goes through
        # the port edges of the piece that are not bridges.
        self.pmask = dict.fromkeys(nodes, 0)
        self.piece_k = []
        self.piece_ferries = []
        self.dockpiece = {}
        done = set()
        q = 0
        for i, (u, v, f) in enumerate(edges):
            if f < 0 or isb[i] or u in done:
                continue
            piece = {u}
            stack = [u]
            while stack:
                x = stack.pop()
                for y, j in adj[x]:
                    if edges[j][2] < 0 and not isb[j] and y not in piece:
                        piece.add(y)
                        stack.append(y)
            done |= piece
            banned = set()
            served = {}
            for j, (a, b, f2) in enumerate(edges):
                if f2 >= 0 and not isb[j] and a in piece:
                    banned.add(j)
                    served.setdefault(f2, set()).add(a)
                    self.dockpiece[f2 * n + a] = q
            comp = {u}
            stack = [u]
            while stack:
                x = stack.pop()
                for y, j in adj[x]:
                    if j not in banned and y not in comp:
                        comp.add(y)
                        stack.append(y)
            for x in comp:
                self.pmask[x] |= 1 << q
            self.piece_k.append(max(1, max(pr.fk[f2] for f2 in served)))
            self.piece_ferries.append([(f2, frozenset(ports)) for f2, ports in served.items()])
            q += 1
        self.npiece = q
        self.ALLQ = (1 << q) - 1                # every piece, as bits over piece indices
        self.ferry_group = list(range(F))
        for ferries in self.piece_ferries:
            groups = {self.ferry_group[f] for f, _ in ferries}
            first = min(groups)
            self.ferry_group = [first if g in groups else g for g in self.ferry_group]
        self.port_site = {x: (self.rmask[x] >> self.nroad) | (self.pmask[x] << (self.ncut - self.nroad))
                          for x in nodes}
        self.ferry_cache = {}
        self.pgmask = {p: self.pmask[pr.pgoal[p]] for p in self.pkgs}
        self.NN = n + F + 1
        self.pcross = _Memo(self._piece_crossing)

        # ---- cycle blocks (proof, Lemma 8): for every 2-edge-connected part, its road edges that are
        # not bridges. Contracting everything else gives a small graph of "clusters"; balls around a
        # cluster are cuts whose boundaries use only these edges and are pairwise disjoint.
        nbroad = {}
        for i, (u, v, f) in enumerate(edges):
            if f < 0 and not isb[i]:
                nbroad.setdefault(cc[u], []).append(i)
        self.blocks = []
        for c in sorted(nbroad):
            eids = set(nbroad[c])
            cl = {}
            ncl = 0
            for s in nodes:
                if s in cl:
                    continue
                cl[s] = ncl
                stack = [s]
                while stack:
                    x = stack.pop()
                    for y, j in adj[x]:
                        if j not in eids and y not in cl:
                            cl[y] = ncl
                            stack.append(y)
                ncl += 1
            qadj = [set() for _ in range(ncl)]
            for j in eids:
                a, b = cl[edges[j][0]], cl[edges[j][1]]
                if a != b:
                    qadj[a].add(b)
                    qadj[b].add(a)
            if not any(qadj):
                continue
            far = ncl + 1           # stands for "unreachable"; cannot occur in a connected region
            dist = []
            for z in range(ncl):
                d = [far] * ncl
                d[z] = 0
                queue = [z]
                for x in queue:
                    for y in qadj[x]:
                        if d[y] == far:
                            d[y] = d[x] + 1
                            queue.append(y)
                dist.append(d)
            radius = [max(x for x in d if x < far) for d in dist]
            self.blocks.append((cl, dist, radius, far))
        self.cyc_cache = {}
        # fractional weights for the per-block fractional bound (proof, Lemma 7): a package that cannot
        # share a truck with any other package of positive weight counts as a full truck
        posw = [pr.bound_weights[p] for p in self.pkgs if pr.bound_weights[p] > 0]
        light = min(posw) if posw else 0
        self.cfw = {p: (cm if (pr.bound_weights[p] > 0 and pr.bound_weights[p] + light > cm)
                        else pr.bound_weights[p]) for p in self.pkgs}

        # goals shared by several packages (candidates for the merge bound)
        count = {}
        for p in self.pkgs:
            count[pr.pgoal[p]] = count.get(pr.pgoal[p], 0) + 1
        self.merge_goals = set(g for g in count if count[g] >= 2) if self.ncut else set()
        idx = [1 + t for t in self.trucks] + [pr.IF + f for f in range(F) if n + f in nodeset]
        idx += [pr.IP + p for p in self.pkgs]
        self.sig = itemgetter(*idx)
        self.cache = {}

    @staticmethod
    def _bridges(nodes, adj, m):
        """The bridges of the graph (iterative depth first search with low links)."""
        disc = {}
        low = {}
        isb = [False] * m
        timer = 0
        for s in nodes:
            if s in disc:
                continue
            disc[s] = low[s] = timer
            timer += 1
            stack = [(s, -1, 0)]
            while stack:
                x, pe, k = stack.pop()
                if k < len(adj[x]):
                    stack.append((x, pe, k + 1))
                    y, i = adj[x][k]
                    if i == pe:
                        continue
                    if y not in disc:
                        disc[y] = low[y] = timer
                        timer += 1
                        stack.append((y, i, 0))
                    elif disc[y] < low[x]:
                        low[x] = disc[y]
                elif pe >= 0:
                    par = stack[-1][0]
                    if low[x] < low[par]:
                        low[par] = low[x]
                    if low[x] > disc[par]:
                        isb[pe] = True
        return isb

    def _piece_crossing(self, key):
        """The pieces that package p at node x has to leave and to enter: (all of them as a mask, out, in)."""
        p, x = divmod(key, self.NN)
        ma = self.pmask[x]
        mg = self.pgmask[p]
        d = ma ^ mg
        outs = [q for q in range(self.npiece) if ((ma & d) >> q) & 1]
        ins = [q for q in range(self.npiece) if ((mg & d) >> q) & 1]
        return d, tuple(outs), tuple(ins)

    def _updates(self, p, x):
        """Point masses of package p when it is at node x: (index, value) pairs."""
        cc = self.cc
        a, g = cc[x], cc[self.pr.pgoal[p]]
        if a == g:
            return ()
        w = self.pr.bound_weights[p]
        big = self.pbig[p]
        out = w + (big << (2 * self.WB))
        inn = (w << self.WB) + (big << (2 * self.WB + self.BB))
        parent, depth = self.parent, self.depth
        x, y = a, g
        while x != y:
            if depth[x] >= depth[y]:
                x = parent[x]
            else:
                y = parent[y]
        tin = self.tin
        return ((tin[a] + 1, out), (tin[g] + 1, inn), (tin[x] + 1, -out - inn))

    # ------------------------------------------------------------------ road bridges
    def g(self, v, a, b):
        """Least number of crossings (out + in) of a road bridge with at least a crossings out of the subtree
        and b crossings into it. v packs the weight that has to go out and in, the number of big packages
        (heavier than half of the largest truck, so no two of them share a truck) and the trucks inside.

        A crossing out is made by a truck that is inside: one of the trucks that are inside now (each can do
        this once without coming back first), or a truck that crossed in before. So with zo crossings out, j of
        them by different trucks that are inside now, the other zo - j need zo - j <= zi crossings in, and the
        weight they carry is at most (the j largest capacities inside) + (zo - j) * (largest capacity)."""
        key = (v, a, b)
        r = self.gm.get(key)
        if r is not None:
            return r
        wo, wi, bo, bi, cs, co, vi, vo = self._decode(v)
        r = self.gm[key] = self._crossings(wo, wi, bo, bi, cs, co, max(a, vo), max(b, vi))
        return r

    def _decode(self, v):
        """Fields of a cut value: weight out, weight in, big out, big in, capacities of the trucks inside
        and outside (largest first), and the two visit flags (some truck must enter / must leave)."""
        WB, BB = self.WB, self.BB
        mask = (v >> self.TSH) & self.TMASK
        cs = sorted((c for j, c in enumerate(self.caps) if (mask >> j) & 1), reverse=True)
        co = sorted((c for j, c in enumerate(self.caps) if not (mask >> j) & 1), reverse=True)
        return (v & self.WM, (v >> WB) & self.WM, (v >> (2 * WB)) & self.BM, (v >> (2 * WB + BB)) & self.BM, cs, co,
                (v >> self.VSH) & 1, (v >> (self.VSH + 1)) & 1)

    def _crossings(self, wo, wi, bo, bi, cs, co, a, b):
        """The least zo + zi (crossings out + in) with zo >= a, zi >= b that can carry the weight, exactly.

        If zo >= zi, then d = zo - zi of the crossings out are made by d different trucks that are inside
        now and have not come in first. They carry at most the d largest capacities inside, and each of
        the other zi crossings out carries at most cm. Using more such trucks than needed never helps,
        because no truck is larger than cm. The case zi > zo is the mirror image. cs and co are sorted
        with the largest capacity first."""
        cm = self.cmax
        # every crossing carries at most cm and at most one big package
        a = max(a, bo, -(-wo // cm))
        b = max(b, bi, -(-wi // cm))
        best = None
        ps = 0
        for d in range(len(cs) + 1):            # zo = zi + d
            zi = max(b, a - d, -(-(wo - ps) // cm))
            t = 2 * zi + d
            if best is None or t < best:
                best = t
            if d < len(cs):
                ps += cs[d]
        po = 0
        for d in range(1, len(co) + 1):         # zi = zo + d
            po += co[d - 1]
            zo = max(a, b - d, -(-(wi - po) // cm))
            t = 2 * zo + d
            if t < best:
                best = t
        return best

    def _first_in(self, v):
        """A side of a road bridge without trucks: extra crossings if the first truck that enters the subtree
        brings nothing that has to go in. After this crossing there is one more truck inside.
        The suffix bound ignores the visit flags, which only makes it smaller."""
        wo, wi, bo, bi, cs, co, vi, vo = self._decode(v)
        return 1 + self._crossings(wo, wi, bo, bi, [self.cmax] + cs, co, 0, 0) - self.g(v, 0, 0)

    def _first_out(self, v):
        """The same for the side outside the subtree (all the trucks are inside the subtree)."""
        wo, wi, bo, bi, cs, co, vi, vo = self._decode(v)
        return 1 + self._crossings(wo, wi, bo, bi, cs, [self.cmax] + co, 0, 0) - self.g(v, 0, 0)

    def _flow_cost(self, v):
        """Excess road crossings for each possible number of trucks finishing beyond this bridge."""
        wo, wi, bo, bi, cs, co, vi, vo = self._decode(v)
        cm = self.cmax
        a = max(bo, -(-wo // cm), vo)
        b = max(bi, -(-wi // cm), vi)
        costs = []
        for k in range(self.ntrucks + 1):
            d = len(cs) - k
            if d >= 0:
                z = max(b, a - d, -(-(wo - sum(cs[:d])) // cm))
                costs.append(2 * z + d)
            else:
                d = -d
                z = max(a, b - d, -(-(wi - sum(co[:d])) // cm))
                costs.append(2 * z + d)
        base = min(costs)
        return tuple(c - base for c in costs)

    def _port_flow_cost(self, key):
        trucks, out, inn = key
        return tuple(2 * max(inn, out - (trucks - k)) + trucks - k - out - inn
                     for k in range(self.ntrucks + 1))

    def _flow(self, cv, pres):
        """Excess bridge crossings when all cuts agree on the trucks' final locations."""
        pattern = list(map(self.flow_cost.__getitem__, cv[:self.nroad]))
        for i in range(self.nroad, self.ncut):
            boards, disemb = pres.get(i, (0, 0))
            out, inn = (boards, disemb) if self.cut_port[i][2] else (disemb, boards)
            pattern.append(self.port_flow_cost[(((cv[i] >> self.TSH) & self.TMASK).bit_count(), out, inn)])
        pattern = tuple(pattern)
        result = self.flow_cache.get(pattern)
        if result is not None:
            return result
        dp = [self.flow_zero] * len(self.parent)
        for c, parent, i in self.flow_order:
            costs, row = pattern[i], dp[c]
            key = (costs, row)
            out = self.flow_steps.get(key)
            if out is None:
                out = []
                best = None
                for a, b in zip(costs, row):
                    value = a + b
                    if best is None or value < best:
                        best = value
                    out.append(best)
                out = self.flow_steps[key] = tuple(out)
            if dp[parent] is self.flow_zero:
                dp[parent] = out
            else:
                row = dp[parent]
                key = (row, out)
                merged = self.flow_merges.get(key)
                if merged is None:
                    merged = self.flow_merges[key] = tuple(
                        min(row[k - j] + out[j] for j in range(k + 1))
                        for k in range(self.ntrucks + 1))
                dp[parent] = merged
        result = self.flow_cache[pattern] = dp[self.flow_root][-1]
        return result

    # ------------------------------------------------------------------ ferries
    def port_cost(self, wo, bo, wi, bi, wn, bn, cargo, ts, ndock, k, here, away, vin, varr, vout):
        """Lower bound on boards + disembarks + sails at a set S of ports (twice the cost, a sail is split
        into a departure and an arrival of 1.5 each), and the bounds on boards and disembarks alone.
        wo/wi: weight that has to leave / enter S (bo/bi: big packages); wn/bn: the part of wi that is aboard
        a ferry docked at S; cargo: [weight, big] of every truck aboard a docked ferry whose packages have to
        go elsewhere; ts: trucks in S; ndock: trucks aboard docked ferries; k: largest ferry;
        here/away: ferries of S docked at S / elsewhere. Visit flags (proof, Lemma 5(a)-(c)): vin, a truck
        must enter S; varr, it must also arrive by sail; vout, a truck must leave S.
        Also returns the departure-minus-arrival bound."""
        if not cargo:
            key = (wo, bo, wi, bi, wn, bn, ts, ndock, k, here, away, vin, varr, vout)
            r = self.pcm.get(key)
            if r is None:
                r = self.pcm[key] = self._port_cost(wo, bo, wi, bi, wn, bn, None, ts, ndock, k, here, away,
                                                    vin, varr, vout)
            return r
        return self._port_cost(wo, bo, wi, bi, wn, bn, cargo, ts, ndock, k, here, away, vin, varr, vout)

    def _port_cost(self, wo, bo, wi, bi, wn, bn, cargo, ts, ndock, k, here, away, vin, varr, vout):
        cm = self.cmax
        mo = max(-(-wo // cm), bo)
        mi = max(-(-wi // cm), bi)
        to = self.ntrucks - ts
        boards = max(mo, mi - to, vout)
        disemb = max(mi, mo - ts, vin)
        if cargo:
            cw = 0
            cb = 0
            for c in cargo:
                cw += c[0]
                cb += c[1]
            d0 = max(-(-max(-(-(wo + cw) // cm), bo + cb) // k), -(-(mi - to) // k), 0)
            # the trucks that still have to arrive by sail to carry the weight out: a truck aboard a docked
            # ferry may walk in instead, but a truck with cargo brings its cargo back in with it
            free = ndock - len(cargo)
            need = None
            # every subset gives at least mo - ts - ndock, so this is a valid (weaker) bound without the loop
            for m in (range(1 << len(cargo)) if len(cargo) <= 10 else ()):
                ew = eb = cnt = 0
                for i, c in enumerate(cargo):
                    if (m >> i) & 1:
                        ew += c[0]
                        eb += c[1]
                        cnt += 1
                v = max(-(-(wo + ew) // cm), bo + eb) - ts - free - cnt
                if need is None or v < need:
                    need = v
            if need is None:
                need = mo - ts - ndock
        else:
            d0 = max(-(-mo // k), -(-(mi - to) // k), 0)
            need = mo - ts - ndock
        if vout and d0 < 1:
            d0 = 1
        if varr and need < 1:
            need = 1
        mf = max(-(-(wi - wn) // cm), bi - bn)
        a0 = max(-(-mf // k), -(-need // k), 0)
        dep = max(d0, a0 - away)
        arr = max(a0, d0 - here)
        return 2 * (boards + disemb) + 3 * (dep + arr), boards, disemb, dep - arr

    # ------------------------------------------------------------------ the bound
    def move(self, state, bucket, tnode, tfer):
        """Lower bound on the cost of the DRIVE, BOARD, SAIL and DISEMBARK actions (and of the extra LOAD and
        UNLOAD actions of packages that change trucks) that are still needed in this region.
        bucket: (package, node where it is, truck that holds it or -1) for the packages not yet delivered."""
        pr = self.pr
        n = pr.n
        IF = pr.IF
        total2 = 0
        xfer = 0
        cv = ()
        flow_extra = 0
        # lying, undelivered packages: each one still needs a truck that is able to carry it (Lemma 2(v))
        lying = [(p, site) for p, site, hol in bucket if hol < 0]
        vi = vo = 0
        if self.ncut:
            vals = self.zero[:]
            upd = self.upd
            for p, site, hol in bucket:
                for i, d in upd[p][site]:
                    vals[i] += d
            pos1 = self.pos1
            tbit = self.tbit
            for t in self.trucks:
                vals[pos1[tnode[t]]] += tbit[t]
            prefix = list(accumulate(vals))
            cv = list(map(sub, self.ighi(prefix), self.iglo(prefix)))
            R = self.nroad
            if lying:
                vi, vo = self._visit_masks(lying, tnode)
                fl = (vi | vo) & self.ROADS
                if fl:
                    VIB, VOB = self.VIB, self.VOB
                    while fl:
                        low = fl & -fl
                        i = low.bit_length() - 1
                        fl ^= low
                        if vi & low:
                            cv[i] |= VIB
                        if vo & low:
                            cv[i] |= VOB
            if R:
                total2 = 2 * sum(map(self.road0.__getitem__, cv[:R]))
        if pr.F:
            port2, pres, piece2, sail_extra2 = self._ferry_bound(state, bucket, tnode, tfer, cv, lying, vi, vo)
            total2 += port2
        else:
            pres, piece2, sail_extra2 = {}, 0, 0
        if self.ncut:
            flow_extra = self._flow(cv, pres)
            xfer = self._road_extra(bucket, cv, pres, tnode)
        # non-bridge road edges: ball families and per-block fractions (Lemmas 7 and 8), doubled
        road_cyc2 = 2 * self._cycle_bound(bucket, tnode) if self.blocks else 0

        if pr.has_frac:
            psi_r = 0
            psi_a = 0
            wr = pr.wd_road
            wa = pr.wd_all
            ab = pr.abnode
            for p, site, hol in bucket:
                if site >= n:
                    f = site - n
                    site = ab[f][state[IF + f]]
                psi_r += wr[p][site]
                psi_a += wa[p][site]
            den = pr.den
            road2 = -(-(2 * psi_r) // den)
            if road_cyc2 > road2:
                road2 = road_cyc2
            alt_a = piece2 + road2 + sail_extra2
            alt_b = -(-(2 * psi_a) // den)
            total2 += alt_a if alt_a > alt_b else alt_b
        else:
            total2 += piece2 + road_cyc2 + sail_extra2
        return (total2 + 1) // 2 + max(xfer, flow_extra)

    def _visit_masks(self, lying, tnode):
        """Visit flags of all bridge cuts at once, as bit masks over cut indices (proof, Lemma 4).
        vi has bit i when the subtree of cut i holds a lying undelivered package that no truck in that subtree
        is big enough to carry, vo the same for the other side of cut i. A truck with capacity >= w is
        "capable" for weight w. cin: the cuts whose subtree holds a capable truck, cout: the cuts whose other
        side holds one."""
        rmask = self.rmask
        ALL = self.ALLC
        caps = self.caps
        tm = [rmask[tnode[t]] for t in self.trucks]
        pw = self.pr.bound_weights
        vi = vo = 0
        seen = {}
        for p, site in lying:
            w = pw[p]
            r = seen.get(w)
            if r is None:
                cin = cout = 0
                for j, c in enumerate(caps):
                    if c >= w:
                        cin |= tm[j]
                        cout |= ALL ^ tm[j]
                r = seen[w] = (cin, cout)
            m = rmask[site]
            vi |= m & ~r[0]
            vo |= (ALL ^ m) & ~r[1]
        return vi, vo

    def _cycle_bound(self, bucket, tnode):
        """Sum over the cycle blocks of a lower bound on the DRIVE actions along the block's road edges."""
        total = 0
        pgoal = self.pr.pgoal
        for bi, (cl, dist, radius, far) in enumerate(self.blocks):
            items = []
            for p, site, hol in bucket:
                a = cl[site]
                b = cl[pgoal[p]]
                if a != b or hol < 0:
                    items.append((p, a, b, hol < 0))
            if not items:
                continue
            tcl = tuple(cl[tnode[t]] for t in self.trucks)
            key = (bi, tcl, tuple(items))
            v = self.cyc_cache.get(key)
            if v is None:
                v = self.cyc_cache[key] = self._block_bound(dist, radius, far, items, tcl)
            total += v
        return total

    def _block_bound(self, dist, radius, far, items, tcl):
        """max(per-block fractional bound, best ball family). items: (package, cluster now, goal cluster,
        lying?) for the packages that matter; tcl: the cluster of every truck of the region."""
        pw = self.pr.bound_weights
        pbig = self.pbig
        cfw = self.cfw
        cm = self.cmax
        WB, BB, TSH = self.WB, self.BB, self.TSH
        TM, mc, VIB, VOB = self.TMASK, self.mcap, self.VIB, self.VOB
        road0 = self.road0
        fr = 0
        for p, a, b, lying in items:
            d = dist[a][b]
            if d < far:
                fr += cfw[p] * d
        best = -(-fr // cm)
        # Every centre gives a valid family (Lemma 8), so any subset of centres may be tried. The clusters
        # where a package that matters is now are the natural centres: balls around them count the trip of
        # a truck to that package and of the package to its goal.
        for z in {a for p, a, b, lying in items}:
            R = radius[z]
            if R <= 0:
                continue
            dz = dist[z]
            n2 = R + 2
            wo = [0] * n2
            wi = [0] * n2
            bo = [0] * n2
            bi = [0] * n2
            tm = [0] * n2
            lin = [-1] * n2         # largest lying weight at exactly this distance (R + 1: farther)
            for p, a, b, lying in items:
                da = dz[a] if dz[a] <= R else R + 1
                db = dz[b] if dz[b] <= R else R + 1
                if da < db:         # inside the ball for r = da+1 .. db, goal outside: must go out
                    w = pw[p]
                    wo[da + 1] += w
                    wo[db + 1 if db <= R else R + 1] -= w
                    if pbig[p]:
                        bo[da + 1] += 1
                        bo[db + 1 if db <= R else R + 1] -= 1
                elif db < da:       # goal inside for r = db+1 .. da, package outside: must come in
                    w = pw[p]
                    wi[db + 1] += w
                    wi[da + 1 if da <= R else R + 1] -= w
                    if pbig[p]:
                        bi[db + 1] += 1
                        bi[da + 1 if da <= R else R + 1] -= 1
                if lying and pw[p] > lin[da]:
                    lin[da] = pw[p]
            for j, c in enumerate(tcl):
                dt = dz[c]
                if dt < R:
                    tm[dt + 1] += 1 << j
            # suffix maxima of the lying weights: the largest lying weight at distance >= r
            suf = [-1] * (n2 + 1)
            for r in range(R + 1, -1, -1):
                suf[r] = lin[r] if lin[r] > suf[r + 1] else suf[r + 1]
            s_wo = s_wi = s_bo = s_bi = s_tm = 0
            pre = -1                # the largest lying weight at distance < r
            tot = 0
            for r in range(1, R + 1):
                s_wo += wo[r]
                s_wi += wi[r]
                s_bo += bo[r]
                s_bi += bi[r]
                s_tm += tm[r]
                if lin[r - 1] > pre:
                    pre = lin[r - 1]
                v = s_wo | (s_wi << WB) | (s_bo << (2 * WB)) | (s_bi << (2 * WB + BB)) | (s_tm << TSH)
                if pre > mc[s_tm]:
                    v |= VIB
                if suf[r] > mc[TM ^ s_tm]:
                    v |= VOB
                tot += road0[v]
            if tot > best:
                best = tot
        return best

    def _ferry_bound(self, state, bucket, tnode, tfer, cv, lying, vi, vo):
        """Port and piece costs depend on island membership, not on drives within an island.
        The key does not tell a lying package from one carried by a standing truck at the same place. That is
        safe (proof, Section 16): the carrying truck is able to carry it and sits on the same side of every
        cut, so such a package never sets a visit flag, whether it lies or is carried."""
        pr = self.pr
        n, IF = pr.n, pr.IF
        pos1 = self.pos1
        site_key = self.port_site
        key = (tuple(site_key[tnode[t]] for t in self.trucks),
               tuple(tfer[t] for t in self.trucks), state[IF:pr.IP],
               tuple((p, site_key[site], hol if site >= n else -1) for p, site, hol in bucket))
        cached = self.ferry_cache.get(key)
        if cached is not None:
            return cached
        R = self.nroad
        total2 = 0
        balance = [0] * pr.F
        pres = None
        TM, mc = self.TMASK, self.mcap
        pw = pr.bound_weights
        if self.ncut > R:
            pres = {}
            WB, BB, WM, BM = self.WB, self.BB, self.WM, self.BM
            TSH = self.TSH
            rmask = self.rmask
            pbig = self.pbig
            for i in range(R, self.ncut):
                v = cv[i]
                f, a, inside = self.cut_port[i]
                docked = state[IF + f] == a
                dmask = 0                   # region trucks aboard f while f is docked at a
                if docked:
                    for j, t in enumerate(self.trucks):
                        if tfer[t] == f:
                            dmask |= 1 << j
                msub = (v >> TSH) & TM      # trucks inside the subtree
                mx = msub if inside else TM ^ msub      # trucks on the port side
                # visit flags of the port side X (the masks are oriented to the subtree side)
                bit = 1 << i
                if inside:
                    vin = 1 if vi & bit else 0
                    vout = 1 if vo & bit else 0
                else:
                    vin = 1 if vo & bit else 0
                    vout = 1 if vi & bit else 0
                varr = vin
                if vin and dmask:
                    # an arrival is needed unless a truck aboard f could walk in and carry every lying
                    # package of X that the trucks of X cannot carry
                    cap = mc[mx | dmask]
                    varr = 0
                    for p, site in lying:
                        if ((rmask[site] >> i) & 1) == inside and pw[p] > cap:
                            varr = 1
                            break
                if not (v & self.WFM) and not dmask and not vin and not vout:
                    continue
                ts = mx.bit_count()
                if inside:
                    wo = v & WM
                    wi = (v >> WB) & WM
                    bo = (v >> (2 * WB)) & BM
                    bi = (v >> (2 * WB + BB)) & BM
                else:
                    wi = v & WM
                    wo = (v >> WB) & WM
                    bi = (v >> (2 * WB)) & BM
                    bo = (v >> (2 * WB + BB)) & BM
                wn = bn = 0
                ndock = dmask.bit_count()
                cargo = None
                if dmask:
                    lo, hi = self.cut_lo[i], self.cut_hi[i]
                    per = {}
                    for p, site, hol in bucket:
                        if hol >= 0 and tfer[hol] == f:
                            gin = (lo < pos1[pr.pgoal[p]] <= hi) == inside
                            if gin:
                                wn += pw[p]
                                bn += pbig[p]
                            else:
                                c = per.get(hol)
                                if c is None:
                                    per[hol] = [pw[p], pbig[p]]
                                else:
                                    c[0] += pw[p]
                                    c[1] += pbig[p]
                    if per:
                        cargo = list(per.values())
                kf = max(pr.fk[f], 1)
                hd = 1 if docked else 0
                c2, boards, disemb, diff = self.port_cost(wo, bo, wi, bi, wn, bn, cargo, ts, ndock, kf,
                                                          hd, 1 - hd, vin, varr, vout)
                balance[self.ferry_group[f]] += diff
                total2 += c2
                if c2:
                    pres[i] = (boards, disemb)
        piece2 = 0
        Q = self.npiece
        if Q:
            pbig = self.pbig
            pm = self.pmask
            pgm = self.pgmask
            dockpiece = self.dockpiece
            Wo = [0] * Q
            Bo = [0] * Q
            Wi = [0] * Q
            Bi = [0] * Q
            Wn = [0] * Q
            Bn = [0] * Q
            cargo = None
            active = 0
            pcross = self.pcross
            NN = self.NN
            for p, site, hol in bucket:
                x, outs, ins = pcross[p * NN + site]
                if x:
                    w = pw[p]
                    b = pbig[p]
                    active |= x
                    for q in outs:
                        Wo[q] += w
                        Bo[q] += b
                    for q in ins:
                        Wi[q] += w
                        Bi[q] += b
                if hol >= 0:
                    f = tfer[hol]
                    if f >= 0:
                        q = dockpiece.get(f * n + state[IF + f])
                        if q is not None:
                            ma = pm[site]
                            mg = pgm[p]
                            if (mg >> q) & 1:
                                Wn[q] += pw[p]
                                Bn[q] += pbig[p]
                            elif not (ma >> q) & 1:
                                if cargo is None:
                                    cargo = {}
                                c = cargo.get((q, hol))
                                if c is None:
                                    cargo[(q, hol)] = [pw[p], pbig[p]]
                                else:
                                    c[0] += pw[p]
                                    c[1] += pbig[p]
                                active |= 1 << q
            # trucks with their node in X_q (tmq) and trucks aboard a ferry docked at a non-bridge port of q
            # (dmq); the two masks are disjoint because such a ferry node lies outside X_q
            tmq = [0] * Q
            dmq = [0] * Q
            for j, t in enumerate(self.trucks):
                bit = 1 << j
                o = pm[tnode[t]]
                while o:
                    low = o & -o
                    tmq[low.bit_length() - 1] |= bit
                    o ^= low
                f = tfer[t]
                if f >= 0:
                    q = dockpiece.get(f * n + state[IF + f])
                    if q is not None:
                        dmq[q] |= bit
            # visit flags of all pieces at once, as bit masks over piece indices (same rule as
            # _visit_masks): qvi has bit q when X_q holds a lying undelivered package that no truck in X_q
            # can carry, qvo the same outside X_q
            qvi = qvo = 0
            if lying:
                ALLQ = self.ALLQ
                caps = self.caps
                ptm = [pm[tnode[t]] for t in self.trucks]
                seen = {}
                for p, site in lying:
                    w = pw[p]
                    r = seen.get(w)
                    if r is None:
                        cin = cout = 0
                        for j, c in enumerate(caps):
                            if c >= w:
                                cin |= ptm[j]
                                cout |= ALLQ ^ ptm[j]
                        r = seen[w] = (cin, cout)
                    m = pm[site]
                    qvi |= m & ~r[0]
                    qvo |= (ALLQ ^ m) & ~r[1]
                active |= qvi | qvo
            o = active
            while o:
                low = o & -o
                q = low.bit_length() - 1
                o ^= low
                here = away = 0
                for f, ports in self.piece_ferries[q]:
                    if state[IF + f] in ports:
                        here += 1
                    else:
                        away += 1
                cg = None
                if cargo:
                    cg = [c for (q2, _), c in cargo.items() if q2 == q]
                vin = (qvi >> q) & 1
                vout = (qvo >> q) & 1
                varr = vin
                if vin and dmq[q]:
                    cap = mc[tmq[q] | dmq[q]]
                    varr = 0
                    for p, site in lying:
                        if (pm[site] >> q) & 1 and pw[p] > cap:
                            varr = 1
                            break
                cost = self.port_cost(Wo[q], Bo[q], Wi[q], Bi[q], Wn[q], Bn[q], cg, tmq[q].bit_count(),
                                      dmq[q].bit_count(), self.piece_k[q], here, away, vin, varr, vout)
                piece2 += cost[0]
                balance[self.ferry_group[self.piece_ferries[q][0][0]]] += cost[3]
        sail_extra2 = 3 * sum(map(abs, balance))
        result = (total2, pres or {}, piece2, sail_extra2)
        self.ferry_cache[key] = result
        return result

    def _road_extra(self, bucket, cv, pres, tnode):
        """Merge and first-entry extras. The key holds cv, which fixes on which side of every cut each truck
        is, so reading tnode below does not make the cached value depend on anything outside the key."""
        key = (tuple(cv), tuple(bucket), tuple(pres.items()))
        result = self.road_extra_cache.get(key)
        if result is not None:
            return result
        pr = self.pr
        R = self.nroad
        xfer = 0
        used = 0
        if self.merge_goals:
            xfer, used = self.merge(bucket, cv, pres or {})
        if R and OPT_FIRST and self.ntrucks:
            # Sides of road bridges that need transport and have no truck inside (U = all of them).
            # Until the first LOAD inside U the trucks carry only packages that are outside U now.
            # The truck that makes this first LOAD has entered every such side around the package it
            # loads. If no package outside U has its goal in a side, each of these crossings into it
            # (or an earlier one over the same bridge) brought nothing in: it comes on top of the
            # crossings that are needed afterwards, when one more truck is inside.
            # Candidate sides, as bit masks over the road cuts: an unreserved road bridge that some
            # package of positive weight must cross, with no truck in its subtree (cs) or no truck on the
            # other side (cc).
            rmask = self.rmask
            pgoal = pr.pgoal
            pw = pr.bound_weights
            roads = self.ROADS
            anyt = 0                # cuts whose subtree holds some truck
            allt = roads            # cuts whose subtree holds every truck
            for t in self.trucks:
                m = rmask[tnode[t]]
                anyt |= m
                allt &= m
            marks = []
            crossed = 0
            for p, site, hol in bucket:
                m = rmask[site]
                mg = rmask[pgoal[p]]
                marks.append((m, mg))
                if pw[p] > 0:
                    crossed |= m ^ mg
            cand = crossed & roads & ~used
            cs = cand & ~anyt
            cc = cand & allt
            if cs or cc:
                # Greatest set U of candidate sides such that no package outside U has its goal in a side
                # of U (proof, Lemma 10): drop the sides that receive a package from outside until stable.
                changed = True
                while changed and (cs or cc):
                    changed = False
                    for m, mg in marks:
                        if not ((m & cs) or (~m & cc)):
                            ncs = cs & ~mg
                            ncc = cc & mg
                            if ncs != cs or ncc != cc:
                                cs, cc = ncs, ncc
                                changed = True
                best = None
                if cs or cc:
                    for m, mg in marks:
                        ins = m & cs
                        outs = ~m & cc
                        if not (ins or outs):
                            continue            # this package is outside U: it cannot be the first LOAD in U
                        v = 0
                        if ins:
                            v = sum(map(self.first_in.__getitem__, map(cv.__getitem__, self.split[ins][0])))
                        if outs:
                            v += sum(map(self.first_out.__getitem__, map(cv.__getitem__, self.split[outs][0])))
                        if best is None or v < best:
                            best = v
                            if not v:
                                break
                xfer += best or 0
        self.road_extra_cache[key] = xfer
        return xfer

    def merge(self, bucket, cv, pres):
        """Packages with the same goal that are now in different places (groups) share the last part of
        their way (the chain). If y trucks carry them over the chain, then all groups but y must first be
        merged into these trucks. A merge costs at least:
          * 2 actions for every package of the group (it changes trucks: one more UNLOAD and LOAD), or
          * for a group that lies on the ground: the crossing truck fetches it itself, so it goes in and
            out over every bridge that only this group has to cross (its private bridges).
        The bound is the cheapest choice of y: the extra crossings of the chain by y trucks plus the K - y
        cheapest merges. Every bridge is used for one goal only, so the bounds of the goals can be added."""
        pr = self.pr
        pgoal = pr.pgoal
        mg = self.merge_goals
        goals = None
        for p, site, hol in bucket:
            g = pgoal[p]
            if g in mg:
                if goals is None:
                    goals = {}
                d = goals.get(g)
                if d is None:
                    d = goals[g] = {}
                key = hol if hol >= 0 else -1 - site
                e = d.get(key)
                if e is None:
                    d[key] = [site, 1]
                else:
                    e[1] += 1
        if goals is None:
            return 0, 0
        extra = 0
        used = 0
        mstruct = self.mstruct
        for g in sorted(goals):
            groups = goals[g]
            if len(groups) < 2:
                continue
            items = tuple(sorted([(k, e[0], e[1]) for k, e in groups.items()]))
            sig = (g, used, items)
            st = mstruct.get(sig)
            if st is None:
                st = mstruct[sig] = self._merge_struct(g, used, items)
            if st is False:
                continue                # no common part: nothing has to be merged
            ridx, pidx, memo = st
            key = tuple(map(cv.__getitem__, ridx))
            if pidx:
                key = (key, tuple([pres.get(i) for i in pidx]))
            r = memo.get(key)
            if r is None:
                r = memo[key] = self._merge_goal(g, used, items, cv, pres)
            if r[0]:
                extra += r[0]
                used |= r[1]
        return extra, used

    def _merge_struct(self, g, used, items):
        """The bridges that the merge bound of this goal looks at (the bound depends only on their values)."""
        rmask = self.rmask
        rg = rmask[g]
        chain = ~used
        union = 0
        twice = 0
        paths = []
        for k, site, cnt in items:
            m = rmask[site] ^ rg
            paths.append(m)
            chain &= m
            twice |= union & m
            union |= m
        if not chain:
            return False
        rel = chain
        for (k, site, cnt), m in zip(items, paths):
            if k < 0:
                rel |= m & ~twice & ~used
        ridx, pidx = self.split[rel]
        return ridx, pidx, {}

    def _merge_goal(self, g, used, items, cv, pres):
        """The merge bound of one goal and the bridges it uses. items: (key, node, number of packages) of
        every group, key < 0 for a group that lies on the ground."""
        rmask = self.rmask
        split = self.split
        K = len(items)
        rg = rmask[g]
        chain = ~used
        union = 0
        twice = 0
        paths = []
        for k, site, cnt in items:
            m = rmask[site] ^ rg
            paths.append(m)
            chain &= m
            twice |= union & m
            union |= m
        costs = []
        marks = 0
        j = 0
        for k, site, cnt in items:
            c = 2 * cnt
            if k < 0:               # the group lies on the ground: the detour over its private bridges
                priv = paths[j] & ~twice & ~used
                det = 0
                if priv:
                    marks |= priv
                    ridx, pidx = split[priv]
                    if ridx:
                        det = sum(map(self.road11.__getitem__, map(cv.__getitem__, ridx)))
                    for i in pidx:
                        b = pres.get(i)
                        if b:
                            det += max(0, 1 - b[0]) + max(0, 1 - b[1])
                if det < c:
                    c = det
            costs.append(c)
            j += 1
        costs.sort()
        ridx, pidx = split[chain & ~rg]         # bridges that the packages cross out of the subtree
        vout = list(map(cv.__getitem__, ridx)) if ridx else ()
        lbs = []
        for i in pidx:
            b = pres.get(i)
            if b:                   # the packages leave the subtree: board if the port is inside
                lbs.append(b[0] if self.cut_port[i][2] else b[1])
        ridx, pidx = split[chain & rg]          # bridges that the packages cross into the subtree
        vin = list(map(cv.__getitem__, ridx)) if ridx else ()
        for i in pidx:
            b = pres.get(i)
            if b:
                lbs.append(b[1] if self.cut_port[i][2] else b[0])
        best = None
        merges = 0
        for y in range(K, 0, -1):   # y trucks cross the chain, the K - y cheapest merges are paid
            v = merges
            if vout:
                v += sum(map(self.exo[y].__getitem__, vout))
            if vin:
                v += sum(map(self.exi[y].__getitem__, vin))
            for lb in lbs:
                if y > lb:
                    v += y - lb
            if best is None or v < best:
                best = v
            merges += costs[K - y]
        return best, chain | marks

    def _split(self, mask):
        """The cuts of a bit mask: (indices of road bridges, indices of port bridges)."""
        road, port = [], []
        R = self.nroad
        while mask:
            low = mask & -mask
            i = low.bit_length() - 1
            mask ^= low
            (road if i < R else port).append(i)
        return tuple(road), tuple(port)


class LogisticsProblem(search.Problem):
    """This class implements a logistics problem"""

    def __init__(self, initial):
        """ Constructor only needs the initial state.
        Don't forget to set the goal or implement the goal test"""
        game = initial
        n = game["Locations"]
        tids = sorted(game["Trucks"])
        fids = sorted(game["Ferries"])
        pids = sorted(game["Packages"])
        T, F, P = len(tids), len(fids), len(pids)
        self.n, self.T, self.F, self.P = n, T, F, P
        self.tids, self.fids, self.pids = tids, fids, pids
        # A state is a tuple: (history, trucks..., ferries..., packages...).
        # history: 0, or a code for "truck t is in focus" / "the next action must board ferry f" (_setup_rules).
        # truck: location l, or n + 2f + 1 aboard ferry f after it sailed, n + 2f aboard before it sailed (H3).
        #   ferry:   the port where it is docked
        #   package: location l, or n + t (inside truck t)
        self.IF = 1 + T
        self.IP = 1 + T + F

        adj = [[] for _ in range(n)]
        for a, b in game["Roads"]:
            if a != b:
                if b not in adj[a]:
                    adj[a].append(b)
                if a not in adj[b]:
                    adj[b].append(a)
        self.adj = [tuple(sorted(x)) for x in adj]

        self.tcap = [game["Trucks"][t][1] for t in tids]
        self.fports = [tuple(sorted(set(game["Ferries"][f][1]))) for f in fids]
        self.fcap = [game["Ferries"][f][2] for f in fids]
        # A ferry can never carry more than the fleet, regardless of its numeric BOARD predicate.
        self.fk = [min(k, T) if type(k) is int else T for k in self.fcap]
        # for the map graph: a ferry can also be boarded at the port where it starts, served or not
        self.gports = [tuple(sorted(set(self.fports[i]) | {game["Ferries"][f][0]})) for i, f in enumerate(fids)]
        classes = {}
        self.fcls = []
        for f, capacity in enumerate(self.fcap):
            key = (self.fports[f], self.gports[f], self.fk[f]) if type(capacity) is int else f
            self.fcls.append(classes.setdefault(key, len(classes)))
        self.pw = [game["Packages"][p][1] for p in pids]
        self.pgoal = [game["Packages"][p][2] for p in pids]
        self.integer_cargo = (all(type(w) is int and w >= 0 for w in self.pw)
                              and all(type(c) is int for c in self.tcap))
        self.package_order = range(P)
        if self.integer_cargo:
            self.bound_caps, self.bound_weights = self.tcap, self.pw
        else:
            # Any real load fits in this integer relaxation, even at a floating-point boundary.
            self.bound_caps, self.bound_weights = [P] * T, [1] * P
            index = {pid: p for p, pid in enumerate(pids)}
            self.package_order = tuple(index[pid] for pid in game["Packages"])
        # Equal numeric values can implement different LOAD comparisons.
        self.tcls = self.tcap if self.integer_cargo else range(T)


        state = [0]
        state += [game["Trucks"][t][0] for t in tids]
        state += [game["Ferries"][f][0] for f in fids]
        state += [game["Packages"][p][0] for p in pids]
        self.s0 = tuple(state)
        self.transfer_sites = {l for l in range(n) if len(self.adj[l]) != 2}
        self.transfer_sites.update(state[1:1 + T])
        self.transfer_sites.update(state[self.IP:])
        self.transfer_sites.update(self.pgoal)
        for ports in self.gports:
            self.transfer_sites.update(ports)
        search.Problem.__init__(self, _State(self, self.s0))
        pclasses = {}
        self.pcls = []
        for p in range(P):
            key = (self.pw[p], self.pgoal[p]) if self.integer_cargo else p
            self.pcls.append(pclasses.setdefault(key, len(pclasses)))
        self.npcls = len(pclasses) + 1

        self._build_regions()
        self._build_fractions()
        self.hcache = {}
        self.hcache2 = {}
        dead_drive, dead_sail, dead_ferry = set(), set(), set()
        if OPT_DEAD:
            for reg in self.regions:
                dead_drive |= reg.dead_drive
                dead_sail |= reg.dead_sail
                dead_ferry |= reg.dead_ferry
        if OPT_DEAD:
            dead_sail |= self._dominated_ports(dead_sail)
        self.adj_go = [tuple(w for w in self.adj[l] if (l, w) not in dead_drive) for l in range(n)]
        # for an empty truck: (neighbour, far side mask or 0 if the road is not a bridge)
        far = {}
        if OPT_BARREN:
            for reg in self.regions:
                far.update(reg.far)
        self.adj_far = [tuple((w, far.get((l, w), 0)) for w in self.adj_go[l]) for l in range(n)]
        self.sail_to = [() if f in dead_ferry else tuple(b for b in self.fports[f] if (f, b) not in dead_sail)
                        for f in range(F)]
        self.fdead = [f in dead_ferry for f in range(F)]
        self._setup_rules()
        self._por = (_Stubborn(self) if OPT_PARTIAL_ORDER and self.integer_cargo and not self.new_rules
                     and not self.use_history and not self.use_fresh and not OPT_CORRIDOR
                     and all(type(k) is int and k >= 1 for k in self.fcap)
                     and not OPT_BARREN else None)

    # ------------------------------------------------------------------ precomputation on the map
    @staticmethod
    def _best_load(c, ws):
        """Rule B: the largest subset sum of the weights ws that is at most c (every w in ws is at most c), or None
        when a capacity above _DENSE_BITS would need more than _SUBSET_SUMS distinct sums."""
        if c <= _DENSE_BITS:
            sums = 1                    # bit v set <=> v is a subset sum <= c
            limit = (1 << (c + 1)) - 1
            for w in ws:
                sums = (sums | (sums << w)) & limit
            return sums.bit_length() - 1
        sums = {0}                      # the same set of subset sums <= c, stored sparsely
        for w in ws:
            sums |= {v + w for v in sums if v + w <= c}
            if len(sums) > _SUBSET_SUMS:
                return None
        return max(sums)

    def _setup_rules(self):
        """Static data for Rules A-D of SUCCESSOR_RULES_PROOF.md. Everything here is computed on the map and on
        the fixed instance data (no state is searched)."""
        n, T, F, P = self.n, self.T, self.F, self.P
        exact = self.integer_cargo
        self.use_sail = OPT_EMPTY_SAIL and exact
        self.use_effcap = OPT_EFFCAP and exact
        self.use_useless = OPT_USELESS and exact
        self.use_toward = OPT_TOWARD and exact
        self.new_rules = self.use_sail or self.use_effcap or self.use_useless or self.use_toward
        hist = OPT_HISTORY and exact
        self.use_focus = hist and OPT_FOCUS
        self.use_uturn = hist and OPT_FOCUS and OPT_UTURN
        self.use_fresh = hist and OPT_FRESH
        self.use_needboard = hist and OPT_FOCUS and OPT_NEEDBOARD
        self.use_history = self.use_focus or self.use_needboard
        # history codes in state[0]: 0 none, 1 + t * (n + 1) + prev for "truck t in focus, came from prev"
        # (prev = n: no previous drive), need_base + f * (T + 1) + (t + 1 or 0) for "next: BOARD onto f"
        self.need_base = 1 + T * (n + 1)

        # Components of the auxiliary map graph (locations and ferry nodes), as in _build_regions.
        group = list(range(n + F))

        def find(x):
            while group[x] != x:
                group[x] = group[group[x]]
                x = group[x]
            return x

        for a in range(n):
            for b in self.adj[a]:
                group[find(a)] = find(b)
        for f in range(F):
            for a in self.gports[f]:
                group[find(a)] = find(n + f)
        self.tcomp = [find(self.s0[1 + t]) for t in range(T)]
        self.pcomp = [find(self.pgoal[p]) for p in range(P)]

        if self.use_effcap:
            # Rule B (Definition 3): c_bar = largest sum of package weights of the truck's component that is at
            # most its capacity. Every reachable load is such a sum, so LOAD decisions do not change (Lemma 7).
            weights = {}
            for p in range(P):
                weights.setdefault(self.pcomp[p], []).append(self.pw[p])
            cbar = []
            for t in range(T):
                c = self.tcap[t]
                ws = weights.get(self.tcomp[t], ())
                total = sum(ws)
                if c < 0:
                    cbar.append(c)          # nothing ever fits, so keep the raw value (never equal to a c_bar >= 0)
                elif c >= total:
                    cbar.append(total)
                else:
                    best = self._best_load(c, [w for w in ws if w <= c])   # a heavier package never fits
                    if best is None:
                        break
                    cbar.append(best)
            if len(cbar) < T:
                # Too many distinct subset sums under a huge capacity: Rule B is switched off for this instance,
                # which both proofs cover. tcls and fcls keep their raw values from the constructor.
                self.use_effcap = False
            else:
                self.tcls = cbar
        if self.use_effcap:
            # k_bar = min(k, trucks of the ferry's component). sail_to and fdead are in the key, so classed
            # ferries also agree on every static restriction of the graph H.
            trucks_in = {}
            for t in range(T):
                trucks_in[self.tcomp[t]] = trucks_in.get(self.tcomp[t], 0) + 1
            classes = {}
            self.fcls = []
            for f in range(F):
                k = self.fcap[f]
                if type(k) is int:
                    key = (self.fports[f], self.gports[f], self.sail_to[f], self.fdead[f],
                           min(k, trucks_in.get(find(n + f), 0)))
                else:
                    key = ("ferry", f)
                self.fcls.append(classes.setdefault(key, len(classes)))

        if self.use_toward:
            # Rule D (Definition 5): toward[l][i] has bit z set when the i-th retained neighbour m of l satisfies
            # d(m, z) = d(l, z) - 1 < infinity, with d the directed road distance over adj_go. Plain BFS on the map.
            radj = [[] for _ in range(n)]
            for x in range(n):
                for y in self.adj_go[x]:
                    radj[y].append(x)
            unreachable = n + 1
            dist = []
            for z in range(n):
                d = [unreachable] * n
                d[z] = 0
                queue = [z]
                for x in queue:
                    for y in radj[x]:
                        if d[y] == unreachable:
                            d[y] = d[x] + 1
                            queue.append(y)
                dist.append(d)
            self.toward = []
            for l in range(n):
                row = []
                for m in self.adj_go[l]:
                    mask = 0
                    for z in range(n):
                        dz = dist[z]
                        if dz[l] < unreachable and dz[m] == dz[l] - 1:
                            mask |= 1 << z
                    row.append(mask)
                self.toward.append(tuple(row))
            self.sailmask = []
            for f in range(F):
                mask = 0
                for b in self.sail_to[f]:
                    mask |= 1 << b
                self.sailmask.append(mask)

    def _build_regions(self):
        """The connected parts of the map (roads + ferry routes). A package never leaves its part, so the
        parts that have packages are independent problems. They are solved one after the other."""
        n, T, F, P = self.n, self.T, self.F, self.P
        group = list(range(n + F))

        def find(x):
            while group[x] != x:
                group[x] = group[group[x]]
                x = group[x]
            return x

        for a in range(n):
            for b in self.adj[a]:
                group[find(a)] = find(b)
        for f in range(F):
            for a in self.gports[f]:
                group[find(a)] = find(n + f)
        init = self.s0
        count = {}
        self.dead = False       # a package whose goal is in another part of the map: there is no solution
        for p in range(P):
            c = find(self.pgoal[p])
            count[c] = count.get(c, 0) + 1
            if find(init[self.IP + p]) != c:
                self.dead = True
        order = sorted(count, key=lambda c: (count[c], c))      # the smallest part first
        rank = {c: i for i, c in enumerate(order)}
        big = len(order)
        self.ncomp = big
        self.prank = [rank[find(self.pgoal[p])] for p in range(P)]
        self.trank = [rank.get(find(init[1 + t]), big) for t in range(T)]
        self.frank = [rank.get(find(n + f), big) for f in range(F)]
        self.multi = OPT_COMP and (big > 1 or big in self.trank or big in self.frank)
        members = {}
        for x in range(n + F):
            members.setdefault(find(x), []).append(x)
        self.node_rank = [rank.get(find(x), big) for x in range(n + F)] if len(members) > 1 else ()
        self.regions = [_Region(self, members[c], i) for i, c in enumerate(order)]

    def _build_fractions(self):
        """Distances for the part of the map that is not covered by bridges (cycles of roads and of ferry
        routes). There a truck of capacity C that moves a package of weight w pays at least w / C of the
        cost of every action on the way of the package, and a ferry for k trucks shares a sail between k
        trucks. The costs of the actions that the bridges already count are 0 here.
        wd_road counts only the roads, wd_all also the ferries that are not bridges."""
        n, F, P = self.n, self.F, self.P
        abnode = []
        cnt = n
        for f in range(F):
            d = {}
            for a in self.gports[f]:
                d[a] = cnt
                cnt += 1
            abnode.append(d)
        self.abnode = abnode        # node "aboard ferry f while it is docked at port a"
        lk = 1
        for k in self.fk:
            k = max(k, 1)
            a, b = lk, k
            while b:
                a, b = b, a % b
            lk = lk * k // a
        cmax = max(max(self.bound_caps), 1) if self.bound_caps else 1
        self.den = 2 * cmax * lk
        lightest = min((w for w in self.bound_weights if w > 0), default=cmax)
        # A package that cannot share a truck with any other package of positive weight pays a whole
        # truck's movement cost. Packages of weight 0 can always share, so they keep weight 0.
        self.frac_weight = [cmax if (w > 0 and w + lightest > cmax) else w for w in self.bound_weights]
        bridge_road = set()
        bridge_port = set()
        for reg in self.regions:
            bridge_road |= reg.bridge_roads
            bridge_port |= reg.bridge_ports
        self.wd_all = self._fraction_table(cnt, lk, bridge_road, bridge_port, False)
        self.wd_road = self._fraction_table(cnt, lk, bridge_road, bridge_port, True)
        self.has_frac = any(any(row) for row in self.wd_all)

    def _fraction_table(self, cnt, lk, bridge_road, bridge_port, roads_only):
        n, F, P = self.n, self.F, self.P
        abnode = self.abnode
        g = [[] for _ in range(cnt)]
        for a in range(n):
            for b in self.adj[a]:
                g[a].append((b, 0 if (a, b) in bridge_road else 2 * lk))
        for f in range(F):
            half = 3 * lk // max(self.fk[f], 1)     # half a sail, shared by the trucks aboard
            for a in self.gports[f]:
                x = abnode[f][a]
                c = 0 if ((f, a) in bridge_port or roads_only) else 2 * lk
                g[a].append((x, c))
                g[x].append((a, c))
                for b in self.gports[f]:
                    if b != a:
                        c2 = 0
                        if not roads_only:
                            if (f, a) not in bridge_port:
                                c2 += half
                            if (f, b) not in bridge_port:
                                c2 += half
                        g[x].append((abnode[f][b], c2))
        INF = float("inf")
        wd = []
        cache = {}
        for p in range(P):
            goal = self.pgoal[p]
            if goal not in cache:
                # shortest distances on the (small) map graph by repeated relaxation; all the edges
                # have a reverse edge of the same cost, so distances from the goal = distances to it
                dist = [INF] * cnt
                dist[goal] = 0
                changed = True
                while changed:
                    changed = False
                    for x in range(cnt):
                        d = dist[x]
                        if d < INF:
                            for y, c in g[x]:
                                if d + c < dist[y]:
                                    dist[y] = d + c
                                    changed = True
                cache[goal] = dist
            wd.append([self.frac_weight[p] * x if x < INF else 0 for x in cache[goal]])
        return wd

    def _dominated_ports(self, dead_sail):
        """Ports that no ferry ever has to sail to. An island (locations joined by roads) is empty if no
        package starts or has to go there, no truck starts there and no ferry is docked there at the start.
        If some port z outside it is served by every ferry that serves the island, then a plan that visits
        the island can visit z instead: replace the island by z in every action (a sail from z to z is
        dropped, drives inside the island are dropped). The plan stays legal and does not cost more."""
        n, F = self.n, self.F
        group = list(range(n))

        def find(x):
            while group[x] != x:
                group[x] = group[group[x]]
                x = group[x]
            return x

        for a in range(n):
            for b in self.adj[a]:
                group[find(a)] = find(b)
        s0 = self.s0
        marked = set(find(s0[1 + t]) for t in range(self.T))
        marked |= set(find(s0[self.IF + f]) for f in range(F))
        for p in range(self.P):
            marked.add(find(s0[self.IP + p]))
            marked.add(find(self.pgoal[p]))
        serving = {}
        for f in range(F):
            for a in self.fports[f]:
                serving.setdefault(find(a), set()).add(f)
        out = set()
        gone = set()            # islands that are already left out
        for isl in sorted(serving):
            if isl in marked:
                continue
            ferries = serving[isl]
            common = None
            for f in ferries:
                ports = set(a for a in self.fports[f] if find(a) != isl and find(a) not in gone
                            and (f, a) not in dead_sail)
                common = ports if common is None else common & ports
            if common:
                gone.add(isl)
                for f in ferries:
                    for a in self.fports[f]:
                        if find(a) == isl:
                            out.add((f, a))
        return out

    def path_cost(self, c, state1, action, state2):
        """ Do not change this. Returns the cost of reaching state2 from state1 via action,
        given cost c to reach state1: SAIL costs 3, every other action costs 1"""
        return c + (3 if action.startswith("SAIL") else 1)

    # ------------------------------------------------------------------ successors
    def _sail(self, st, f, a, b):
        ns = list(st)
        ns[self.IF + f] = b
        code0 = self.n + 2 * f
        for t in range(1, 1 + self.T):
            if ns[t] == code0:
                ns[t] = code0 + 1       # the trucks aboard have sailed: now they may disembark
        ns[0] = 0
        return ("SAIL{%d,%d,%d}" % (self.fids[f], a, b), tuple(ns))

    def _truck_standing(self, st, t, l, cont, lying, res, changes=None, aboard_count=None):
        """World-legal actions of truck t while it is standing at location l."""
        n = self.n
        T = self.T
        P = self.P
        IP = self.IP
        IF = self.IF
        pgoal = self.pgoal
        pw = self.pw
        tid = self.tids[t]
        if cont:
            forced = -1
            if OPT_FORCED and self.integer_cargo:
                for p in cont:
                    if pgoal[p] == l:
                        forced = p
                        break
            if forced >= 0:
                ns = list(st)
                ns[IP + forced] = l
                ns[0] = 0
                if self.multi and self._last == 1:
                    self._finish(ns)
                res.append(("UNLOAD{%d,%d}" % (self.pids[forced], tid), tuple(ns)))
                if changes is not None:
                    # _finish may reset several vehicles: use the original canonicalizer.
                    changes.append(None if self.multi and self._last == 1
                                   else ("unload", t, forced))
                return
            if not OPT_CORRIDOR or l in self.transfer_sites:
                seen = set()
                for p in cont:
                    if OPT_TWINS:
                        key = self.pcls[p]
                        if key in seen:
                            continue
                        seen.add(key)
                    ns = list(st)
                    ns[IP + p] = l
                    ns[0] = 0
                    if self.multi and pgoal[p] == l and self._last == 1:
                        self._finish(ns)
                    res.append(("UNLOAD{%d,%d}" % (self.pids[p], tid), tuple(ns)))
                    if changes is not None:
                        changes.append(None if self.multi and pgoal[p] == l and self._last == 1
                                       else ("unload", t, p))
        here = lying.get(l)
        if here:
            # Match World.load_of followed by World.load, including the package summation order.
            load = sum(pw[p] for p in cont) if cont else 0
            seen = set()
            for p in here:
                w = pw[p]
                if OPT_TWINS:
                    key = self.pcls[p]
                    if key in seen:
                        continue
                    seen.add(key)
                if load + w <= self.tcap[t]:
                    ns = list(st)
                    ns[IP + p] = n + t
                    ns[0] = 1 + t * (n + 1) + n if self.use_focus else 0
                    res.append(("LOAD{%d,%d}" % (self.pids[p], tid), tuple(ns)))
                    if changes is not None:
                        changes.append(("load", t, p))
        focus = 1 + t * (n + 1) + l if self.use_focus else 0
        if cont:
            for w in self.adj_go[l]:
                ns = list(st)
                ns[1 + t] = w
                ns[0] = focus
                res.append(("DRIVE{%d,%d,%d}" % (tid, l, w), tuple(ns)))
                if changes is not None:
                    changes.append(("drive", t, None))
        elif self.use_toward:
            # Rule D: an empty standing truck drives only along a shortest road path to one of its targets.
            target = self._target_mask(t)
            for w, mask in zip(self.adj_go[l], self.toward[l]):
                if mask & target:
                    ns = list(st)
                    ns[1 + t] = w
                    ns[0] = focus
                    res.append(("DRIVE{%d,%d,%d}" % (tid, l, w), tuple(ns)))
                    if changes is not None:
                        changes.append(("drive", t, None))
        else:
            # OPT_BARREN is currently disabled. The code path remains available for a future proof.
            useful = self._useful
            for w, far in self.adj_far[l]:
                if not far or far & useful:
                    ns = list(st)
                    ns[1 + t] = w
                    ns[0] = focus
                    res.append(("DRIVE{%d,%d,%d}" % (tid, l, w), tuple(ns)))
                    if changes is not None:
                        changes.append(("drive", t, None))
        F = self.F
        if F:
            seen = None
            fdead = self.fdead
            for f in range(F):
                if fdead[f] or st[IF + f] != l:
                    continue
                code0 = n + 2 * f
                if aboard_count is None:
                    cnt = 0
                    for t2 in range(1, 1 + T):
                        c = st[t2]
                        if c == code0 or c == code0 + 1:
                            cnt += 1
                else:
                    cnt = aboard_count[f]
                if not (cnt < self.fcap[f]):
                    continue
                if cnt == 0 and OPT_TWINS:
                    key = self.fcls[f]
                    if seen is None:
                        seen = set()
                    if key in seen:
                        continue
                    seen.add(key)
                ns = list(st)
                ns[1 + t] = code0 if self.use_fresh else code0 + 1      # even code: boarded, not yet sailed
                ns[0] = 0
                res.append(("BOARD{%d,%d}" % (tid, self.fids[f]), tuple(ns)))
                if changes is not None:
                    changes.append(("board", t, f))

    def _target_mask(self, t):
        """Targets of an empty standing truck t as a bit mask over locations (Definition 5): T1 from the lying
        undelivered packages it can carry, T2 and T3 from the ferries. Locations outside the truck's component
        may be set too, but toward[][] has bits only for road-reachable locations, so they never match."""
        c = self.tcap[t]
        mask = self._t_cache.get(c)
        if mask is None:
            mask = self._t_ferry
            for bit, weight in self._t_lying:
                if weight <= c:
                    mask |= bit
            self._t_cache[c] = mask
        return mask

    def _finish(self, ns):
        """The active part of the map is done: its trucks and ferries never act again, so forget where they are."""
        r = self._rank
        init = self.s0
        for t in range(self.T):
            if self.trank[t] == r:
                ns[1 + t] = init[1 + t]
        for f in range(self.F):
            if self.frank[f] == r:
                ns[self.IF + f] = init[self.IF + f]
        ns[0] = 0

    def successor(self, state):
        """ Generates the successor states returns [(action, achieved_states, ...)]"""
        if not OPT_INCREMENTAL_CANON or not OPT_SYM or self.use_history or self.use_fresh:
            return [(action, _State(self, s)) for action, s in self._successors(state.s)]
        changes = []
        raw = self._successors(state.s, changes)
        if not raw:
            return []
        if len(raw) != len(changes):
            raise ValueError("Missing canonicalization change for a successor")
        if state.k is None:
            state.k = self._canon(state.s)
        if state.parts is None:
            state.parts = self._canon_parts(state.s)
        return [(action, _State(self, s) if change is None
                 else self._canon_child(state, s, change))
                for (action, s), change in zip(raw, changes)]

    def _canon_parts(self, s):
        """Build identity-indexed metadata once for an initial or component-reset state."""
        n = self.n
        cargo = [[] for _ in range(self.T)]
        for p in range(self.P):
            pos = s[self.IP + p]
            if pos >= n:
                cargo[pos - n].append(self.pcls[p])
        cargo = tuple(tuple(sorted(c)) for c in cargo)
        aboard = [[] for _ in range(self.F)]
        for t in range(self.T):
            tc = s[1 + t]
            if tc >= n:
                aboard[(tc - n) >> 1].append((self.tcls[t], cargo[t]))
        by_ferry = tuple((self.fcls[f], s[self.IF + f], tuple(sorted(aboard[f])))
                         for f in range(self.F))
        return (cargo, by_ferry)

    def _canon_child(self, parent, s, change):
        """Compute exactly _canon(s) by editing the descriptors changed by one action.

        Both the key and the identity-indexed metadata are immutable. Component completion
        bypasses this method because _finish can change more than the named action's objects.
        See INCREMENTAL_CANONICALIZATION_PROOF.md for the invariant and all action cases.
        """
        standing, ferries, lying = parent.k
        cargo, by_ferry = parent.parts
        parts = parent.parts
        kind, obj, arg = change
        if kind == "drive":
            t = obj
            standing = _canon_edit(standing,
                                   (parent.s[1 + t], self.tcls[t], cargo[t]),
                                   (s[1 + t], self.tcls[t], cargo[t]))
        elif kind == "load" or kind == "unload":
            t, p = obj, arg
            cls = self.pcls[p]
            old_cargo = cargo[t]
            if kind == "load":
                new_cargo = _canon_edit(old_cargo, new=cls)
                lying = _canon_edit(lying, old=parent.s[self.IP + p] * self.npcls + cls)
            else:
                new_cargo = _canon_edit(old_cargo, old=cls)
                lying = _canon_edit(lying, new=s[self.IP + p] * self.npcls + cls)
            standing = _canon_edit(standing,
                                   (parent.s[1 + t], self.tcls[t], old_cargo),
                                   (s[1 + t], self.tcls[t], new_cargo))
            updated = list(cargo)
            updated[t] = new_cargo
            cargo = tuple(updated)
            parts = (cargo, by_ferry)
        elif kind in ("board", "disembark", "sail"):
            f = obj if kind == "sail" else arg
            old_ferry = by_ferry[f]
            manifest = old_ferry[2]
            if kind == "board":
                t = obj
                standing = _canon_edit(standing,
                                       old=(parent.s[1 + t], self.tcls[t], cargo[t]))
                manifest = _canon_edit(manifest, new=(self.tcls[t], cargo[t]))
            elif kind == "disembark":
                t = obj
                manifest = _canon_edit(manifest, old=(self.tcls[t], cargo[t]))
                standing = _canon_edit(standing, new=(s[1 + t], self.tcls[t], cargo[t]))
            new_ferry = (old_ferry[0], s[self.IF + f], manifest)
            ferries = _canon_edit(ferries, old_ferry, new_ferry)
            updated = list(by_ferry)
            updated[f] = new_ferry
            by_ferry = tuple(updated)
            parts = (cargo, by_ferry)
        else:
            raise ValueError("Unknown canonicalization change")
        return _State(self, s, (standing, ferries, lying), parts)

    def _canon(self, s):
        """The key of a state that is the same for all renamings of interchangeable objects: every truck
        is described by its capacity, its place and the kinds of packages inside it, and so on."""
        if not OPT_SYM:
            return s
        n = self.n
        T = self.T
        IF = self.IF
        IP = self.IP
        npc = self.npcls
        pcls = self.pcls
        cont = [None] * T
        lying = []
        for p in range(self.P):
            c = s[IP + p]
            if c < n:
                lying.append(c * npc + pcls[p])
            elif cont[c - n] is None:
                cont[c - n] = [pcls[p]]
            else:
                cont[c - n].append(pcls[p])
        lying.sort()
        standing = []
        aboard = None
        tcls = self.tcls
        for t in range(T):
            c = cont[t]
            if c is None:
                c = ()
            else:
                c.sort()
                c = tuple(c)
            tc = s[1 + t]
            if tc < n:
                standing.append((tc, tcls[t], c))
            else:
                if aboard is None:
                    aboard = {}
                f = (tc - n) >> 1
                d = (tcls[t], c, (tc - n) & 1) if self.use_fresh else (tcls[t], c)
                if f in aboard:
                    aboard[f].append(d)
                else:
                    aboard[f] = [d]
        standing.sort()
        ferries = []
        fcls = self.fcls
        for f in range(self.F):
            if aboard is not None and f in aboard:
                a = aboard[f]
                a.sort()
                ferries.append((fcls[f], s[IF + f], tuple(a)))
            else:
                ferries.append((fcls[f], s[IF + f], ()))
        ferries.sort()
        h = s[0]
        if not h:
            return (tuple(standing), tuple(ferries), tuple(lying))
        # History is described through the objects it names, so renamings of interchangeable objects agree.
        def truck_key(t):
            c = cont[t]
            return (s[1 + t], tcls[t], tuple(sorted(c)) if c else ())
        if h < self.need_base:
            t, prev = divmod(h - 1, n + 1)
            extra = ("focus", truck_key(t), prev)
        else:
            f, r = divmod(h - self.need_base, T + 1)
            extra = ("board", fcls[f], s[IF + f], truck_key(r - 1) if r else None)   # f is empty here
        return (tuple(standing), tuple(ferries), tuple(lying), extra)

    def _prepare_rules(self, state, inside, lying, aboard_count):
        """Per-expansion data of Rules A, C, D (SUCCESSOR_RULES_PROOF.md, Definitions 1, 2, 5).
        Returns (lightest undelivered weight per component, mask of locations with a truck that is not useless)
        and sets the target masks that _target_mask reads."""
        n, T, F, P, IF, IP = self.n, self.T, self.F, self.P, self.IF, self.IP
        lightest = None
        standing = 0
        if self.use_useless or self.use_sail:
            # A truck is useless if it stands empty and every undelivered package of its component is heavier
            # than its capacity, that is, if its capacity is below the lightest such package.
            lightest = {}
            pcomp, pw, pgoal = self.pcomp, self.pw, self.pgoal
            for p in range(P):
                c = state[IP + p]
                if c >= n or c != pgoal[p]:
                    k = pcomp[p]
                    w = pw[p]
                    if w < lightest.get(k, _NOTHING):
                        lightest[k] = w
            tcomp, tcap = self.tcomp, self.tcap
            for t in range(T):
                tc = state[1 + t]
                if tc < n and (inside[t] or tcap[t] >= lightest.get(tcomp[t], _NOTHING)):
                    standing |= 1 << tc
        if self.use_toward:
            ferries = 0                 # T2: docks with a free slot, T3: ports an empty ferry can sail to
            fcap = self.fcap
            for f in range(F):
                if not self.fdead[f]:
                    occupied = aboard_count[f]
                    if occupied < fcap[f]:
                        ferries |= 1 << state[IF + f]
                        if not occupied:
                            ferries |= self.sailmask[f]
            self._t_ferry = ferries
            pw = self.pw
            self._t_lying = [(1 << loc, min(pw[p] for p in here)) for loc, here in lying.items()]
            self._t_cache = {}
        return lightest, standing

    def _history_successors(self, state, hist, inside, lying, aboard_count, res):
        """Successors of a state whose leading field records history (HISTORY_RULES_PROOF.md):
        "truck t is in focus" (H1, H2) or "the next action must be a BOARD onto ferry f" (H4)."""
        n, T, IF = self.n, self.T, self.IF
        if hist < self.need_base:
            t, prev = divmod(hist - 1, n + 1)
            need = -1
        else:
            need, r = divmod(hist - self.need_base, T + 1)
            t = r - 1
            prev = n
        if need >= 0:
            # H4: only a BOARD onto `need`, by the focus truck if there is one, else by a truck standing there.
            f = need
            dock = state[IF + f]
            if not aboard_count[f] < self.fcap[f]:
                return res
            code0 = n + 2 * f
            seen = set()
            for t2 in ([t] if t >= 0 else range(T)):
                if state[1 + t2] != dock or (self.multi and self.trank[t2] != self._rank):
                    continue
                if not inside[t2] and OPT_TWINS:
                    key = (dock, self.tcls[t2])
                    if key in seen:
                        continue
                    seen.add(key)
                ns = list(state)
                ns[1 + t2] = code0 if self.use_fresh else code0 + 1
                ns[0] = 0
                res.append(("BOARD{%d,%d}" % (self.tids[t2], self.fids[f]), tuple(ns)))
            return res
        # H1: only actions of the focus truck t, which stands at l.
        l = state[1 + t]
        cont = inside[t]
        self._prepare_rules(state, inside, lying, aboard_count)
        mine = []
        self._truck_standing(state, t, l, cont, lying, mine,
                             aboard_count=aboard_count if OPT_OCCUPANCY_REUSE else None)
        back = "DRIVE{%d,%d,%d}" % (self.tids[t], l, prev) if self.use_uturn and prev < n else None
        for action, child in mine:
            if action == back:
                continue                # H2: only an actual DRIVE straight back (a forced UNLOAD that completes
                                        # a component can also put the truck at prev, through the _finish reset)
            res.append((action, child))
        forced = cont and any(self.pgoal[p] == l for p in cont)
        if self.F and not forced:
            # H1 exception: an empty ferry may come to the focus truck, which then boards it (H4 if on).
            seen = set()
            for f in range(self.F):
                if self.fdead[f] or aboard_count[f] or not 0 < self.fcap[f] or l not in self.sail_to[f]:
                    continue
                dock = state[IF + f]
                if dock == l:
                    continue
                if OPT_TWINS:
                    key = (dock, self.fcls[f])
                    if key in seen:
                        continue
                    seen.add(key)
                action, child = self._sail(state, f, dock, l)
                after = self.need_base + f * (T + 1) + t + 1 if self.use_needboard else hist
                res.append((action, (after,) + child[1:]))
        return res

    def _successors(self, state, changes=None):
        """The successors of the tuple of a state: [(action, tuple), ...]

        Current pruning rules:
        1. Never load a package that already lies at its goal.
        2. If a standing truck carries a package for its current location, unload a canonical such package now.
        3. Use one representative among truly interchangeable packages/trucks/ferries.
        4. Do not enter precomputed dead map sides / dominated ports.
        5. Solve independent map components in a canonical component order.
        6. Optional strong stubborn sets retain a provably optimal next-action choice (off while 7-10 are on).
        7. Rule A: an empty ferry sails only to a port where a truck that is not useless stands.
        8. Rule B: twins and merged states use effective capacities.
        9. Rule C: an empty standing truck that cannot carry any undelivered package never acts.
        10. Rule D: an empty standing truck drives only along a shortest road path to one of its targets.
        Rules 7-10 are proved in SUCCESSOR_RULES_PROOF.md.
        11. H1 focus, H2 no U-turn, H3 fresh board, H4 board next, and corridor transfers only at anchors
            (OPT_CORRIDOR), proved in HISTORY_RULES_PROOF.md under the initial-state reading. States with a
            history code go through _history_successors.
        OPT_BARREN stays disabled."""
        n = self.n
        T = self.T
        F = self.F
        P = self.P
        IF = self.IF
        IP = self.IP
        pgoal = self.pgoal
        res = []
        if self.dead:
            return res

        inside = [None] * T
        lying = {}
        rank = self.ncomp
        last = 0
        prank = self.prank
        for p in self.package_order:
            c = state[IP + p]
            if c < n:
                if c == pgoal[p]:
                    if not self.integer_cargo:
                        lying.setdefault(c, []).append(p)
                    continue
                if c in lying:
                    lying[c].append(p)
                else:
                    lying[c] = [p]
            elif inside[c - n] is None:
                inside[c - n] = [p]
            else:
                inside[c - n].append(p)
            r = prank[p]
            if r < rank:
                rank = r
                last = 1
            elif r == rank:
                last += 1
        if rank == self.ncomp:
            return res          # everything is delivered
        self._rank = rank
        self._last = last
        multi = self.multi
        useful = 0
        for c in lying:
            useful |= 1 << c
        fdead = self.fdead
        for f in range(F):
            if not fdead[f]:
                useful |= 1 << state[IF + f]
        self._useful = useful

        aboard_count = [0] * F
        for tc in state[1:1 + T]:
            if tc >= n:
                aboard_count[(tc - n) >> 1] += 1

        # All children are alternatives from this parent. Read these counts without
        # updating them after BOARD/DISEMBARK or passing them on to a child state.
        board_occupancy = aboard_count if OPT_OCCUPANCY_REUSE else None

        tcls = self.tcls
        trank = self.trank
        hist = state[0]
        if hist and self.use_history:
            return self._history_successors(state, hist, inside, lying, aboard_count, res)
        if OPT_FORCED and self.integer_cargo:
            for t, cargo in enumerate(inside):
                if cargo and (not multi or trank[t] == rank):
                    loc = state[1 + t]
                    if loc < n and any(pgoal[p] == loc for p in cargo):
                        self._truck_standing(state, t, loc, cargo, lying, res, changes,
                                             aboard_count=board_occupancy)
                        return res
        use_useless = self.use_useless
        use_sail = self.use_sail
        lightest, standing = self._prepare_rules(state, inside, lying, aboard_count)

        seen_t = set()
        for t in range(T):
            if multi and trank[t] != rank:
                continue
            tc = state[1 + t]
            cont = inside[t]
            if (use_useless and not cont and tc < n
                    and self.tcap[t] < lightest.get(self.tcomp[t], _NOTHING)):
                continue                # Rule C. Its twins are useless too, so no representative is lost.
            if not cont and OPT_TWINS:
                key = (tc, tcls[t])
                if key in seen_t:
                    continue
                seen_t.add(key)
            if tc < n:
                self._truck_standing(state, t, tc, cont, lying, res, changes,
                                     aboard_count=board_occupancy)
            else:
                if self.use_fresh and not (tc - n) & 1:
                    continue            # H3: boarded but not yet sailed, disembarking now would undo the BOARD
                f = (tc - n) >> 1
                ns = list(state)
                ns[1 + t] = state[IF + f]
                ns[0] = 0
                res.append(("DISEMBARK{%d,%d}" % (self.tids[t], self.fids[f]), tuple(ns)))
                if changes is not None:
                    changes.append(("disembark", t, f))
        if F:
            seen_f = set()
            frank = self.frank
            for f in range(F):
                if multi and frank[f] != rank:
                    continue
                port = state[IF + f]
                if OPT_TWINS:
                    empty = not aboard_count[f]
                    if empty:
                        key = (port, self.fcls[f])
                        if key in seen_f:
                            continue
                        seen_f.add(key)
                lazy = use_sail and not aboard_count[f]
                if lazy and not 0 < self.fcap[f]:
                    continue            # Rule A: nobody can ever board, so an empty sail is never needed
                need = self.need_base + f * (T + 1) if self.use_needboard and not aboard_count[f] else 0
                for b in self.sail_to[f]:
                    if b != port and (not lazy or (standing >> b) & 1):
                        action, child = self._sail(state, f, port, b)
                        res.append((action, (need,) + child[1:]) if need else (action, child))
                        if changes is not None:
                            changes.append(("sail", f, None))
        if OPT_PARTIAL_ORDER and self._por is not None:
            keep = self._por.keep(state, res)
            if keep is not None:
                res = [res[i] for i in keep]
                if changes is not None:
                    changes[:] = [changes[i] for i in keep]
        return res

    def goal_test(self, state):
        """ given a state, checks if this is the goal state, compares to the created goal state returns True/False"""
        s = state.s
        IP = self.IP
        pgoal = self.pgoal
        for p in range(self.P):
            if s[IP + p] != pgoal[p]:
                return False
        return True

    def h_astar(self, node):
        """ This is the heuristic. It gets a node (not a state)
        and returns a goal distance estimate"""
        state = node.state.s
        if self.dead:
            return 0            # the initial layout has a package separated from its goal
        if state[0]:
            state = (0,) + state[1:]    # the leading field only holds search history, which h never reads
        h = self.hcache.get(state)
        if h is None:
            h = self.hcache[state] = self._h(state)
        return h

    def _h(self, state):
        """Admissible lower bound = (LOAD/UNLOAD actions still needed) + (movement bound of every region).
        Every package that lies away from its goal needs a LOAD and an UNLOAD, every package inside a truck
        needs an UNLOAD. These actions are different from the movement actions, so the bounds are added."""
        n = self.n
        T = self.T
        IP = self.IP
        pgoal = self.pgoal
        tnode = [0] * T
        tfer = [-1] * T
        for t in range(T):
            tc = state[1 + t]
            if tc < n:
                tnode[t] = tc
            else:
                f = (tc - n) >> 1
                tnode[t] = n + f
                tfer[t] = f
        # Both aboard codes n + 2f (boarded, not yet sailed, rule H3) and n + 2f + 1 decode to ferry f here, so
        # the bound sees only the physical state. h_astar's cache key drops the history field state[0].
        return self._bound(state, tnode, tfer)

    def _bound(self, state, tnode, tfer):
        n = self.n
        IP = self.IP
        pgoal = self.pgoal
        # The precomputed bounds assume these docking edges and these regional truck fleets.
        for f, docks in enumerate(self.abnode):
            if state[self.IF + f] not in docks:
                return 0
        if self.node_rank:
            for t, site in enumerate(tnode):
                if self.node_rank[site] != self.trank[t]:
                    return 0
            for p, pos in enumerate(state[IP:]):
                site = pos if pos < n else tnode[pos - n]
                if self.node_rank[site] != self.prank[p]:
                    return 0
        h = 0
        if self.ncomp == 1:
            bucket = []
            for p in range(self.P):
                c = state[IP + p]
                if c < n:
                    if c != pgoal[p]:
                        h += 2
                        bucket.append((p, c, -1))
                else:
                    h += 1
                    bucket.append((p, tnode[c - n], c - n))
            if bucket:
                reg = self.regions[0]
                # The key keeps custody only for merging groups or cargo aboard a ferry. A package carried by a
                # standing truck and one lying at the same place share a key, so a LOAD or UNLOAD child may
                # reuse its parent's value. This reuse preserves admissibility only: a fresh computation for
                # either state can give a different value (the set of cycle centres can differ), and a value
                # stored for either one is a lower bound for the other (ADMISSIBILITY_PROOF.md, Lemma 13).
                key = (tuple(tnode), state[self.IF:IP],
                       tuple((p, site, hol if site >= n or pgoal[p] in reg.merge_goals else -1)
                             for p, site, hol in bucket))
                value = reg.cache.get(key)
                if value is None:
                    value = reg.cache[key] = reg.move(state, bucket, tnode, tfer)
                h += value
            return h
        buckets = [[] for _ in range(self.ncomp)]
        prank = self.prank
        for p in range(self.P):
            c = state[IP + p]
            if c < n:
                if c != pgoal[p]:
                    h += 2
                    buckets[prank[p]].append((p, c, -1))
            else:
                h += 1
                buckets[prank[p]].append((p, tnode[c - n], c - n))
        for r, bucket in enumerate(buckets):
            if bucket:
                reg = self.regions[r]
                key = reg.sig(state)        # the bound of a part depends only on the objects of this part
                v = reg.cache.get(key)
                if v is None:
                    v = reg.cache[key] = reg.move(state, bucket, tnode, tfer)
                h += v
        return h


def create_logistics_problem(game):
    print("<<create_logistics_problem")
    """ Create a logistics problem, based on the description.
    game - dictionary as described in pdf file"""
    return LogisticsProblem(game)


if __name__ == '__main__':
    ex1_check.main()
