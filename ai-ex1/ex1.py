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
#   - Added truck-flow and whole-sail lower bounds, corridor and empty-ferry pruning, and caches.
#   - Extended the proofs and regression checks and ran the independent validators and benchmarks.
#
# No other online sources were used.

import ex1_check
import search
import utils

from itertools import accumulate
from operator import itemgetter, sub

id = ["212152896"]

# Pruning switches. All of them are True in the submitted version; they exist so that every rule
# could be validated separately against an exhaustive search on small random problems.
OPT_FOCUS = True      # normal form of commuting actions (see successor)
OPT_TWINS = True      # symmetry between identical trucks / ferries / packages
OPT_FORCED = True     # a truck standing at the goal of a package it carries may only unload it
OPT_ORDER = True      # unloads before loads at a stop
OPT_COMP = True       # independent parts of the map are solved one after the other
OPT_SYM = True        # states that differ only by a renaming of identical objects are the same state
OPT_DEAD = True       # never enter a dead end of the map where there is nothing to do
OPT_UTURN = True      # remember where a driving truck came from and do not drive straight back
OPT_FL = True         # after LOAD the same truck goes on
OPT_FRESH = True      # a truck that boarded may not disembark before the ferry sails
OPT_BARREN = True     # an empty truck does not drive into a part where it can neither load nor board
OPT_FIRST = True      # heuristic: the first truck that enters a part without trucks brings nothing for it
OPT_CORRIDOR = True   # transfers on empty road corridors can be moved to an endpoint
OPT_LAZYSAIL = True   # an empty ferry waits until a truck is ready at its destination


class _State(object):
    """A state: the tuple s described in LogisticsProblem.__init__.

    Two states are equal if one becomes the other by renaming objects that are fully interchangeable
    (trucks with the same capacity, ferries of the same line and size, packages with the same weight and
    goal). The search then expands only one of them. The key that is compared is built only when needed."""
    __slots__ = ("s", "k", "pr")

    def __init__(self, pr, s):
        self.s = s
        self.k = None
        self.pr = pr

    def __hash__(self):
        if self.k is None:
            self.k = self.pr._canon(self.s)
        return hash(self.k)

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
        caps = [pr.tcap[t] for t in self.trucks]
        self.caps = caps
        self.cmax = max(max(caps), 1) if caps else 1
        cm = self.cmax
        self.pbig = {p: (1 if 2 * pr.pw[p] > cm else 0) for p in self.pkgs}

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
        total_w = sum(pr.pw[p] for p in self.pkgs) + 1
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
        self.TB = 1 << self.TSH
        self.ALLB = ((1 << self.ntrucks) - 1) << self.TSH
        self.rroad = range(self.nroad)
        self.flow_cost = _Memo(self._flow_cost)
        self.port_flow_cost = _Memo(self._port_flow_cost)
        self.flow_cache = {}
        self.flow_steps = {}
        self.flow_merges = {}
        self.flow_zero = (0,) * (self.ntrucks + 1)
        self.flow_root = root
        self.flow_order = [(c, parent[c], index[c]) for c in reversed(order) if c != root]

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
        w = self.pr.pw[p]
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
        wo, wi, bo, bi, cs, co = self._decode(v)
        r = self.gm[key] = self._crossings(wo, wi, bo, bi, cs, co, a, b)
        return r

    def _decode(self, v):
        WB, BB = self.WB, self.BB
        mask = v >> self.TSH
        cs = sorted((c for j, c in enumerate(self.caps) if (mask >> j) & 1), reverse=True)
        co = sorted((c for j, c in enumerate(self.caps) if not (mask >> j) & 1), reverse=True)
        return (v & self.WM, (v >> WB) & self.WM, (v >> (2 * WB)) & self.BM, (v >> (2 * WB + BB)) & self.BM, cs, co)

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
        brings nothing that has to go in. After this crossing there is one more truck inside."""
        wo, wi, bo, bi, cs, co = self._decode(v)
        return 1 + self._crossings(wo, wi, bo, bi, [self.cmax] + cs, co, 0, 0) - self.g(v, 0, 0)

    def _first_out(self, v):
        """The same for the side outside the subtree (all the trucks are inside the subtree)."""
        wo, wi, bo, bi, cs, co = self._decode(v)
        return 1 + self._crossings(wo, wi, bo, bi, cs, [self.cmax] + co, 0, 0) - self.g(v, 0, 0)

    def _flow_cost(self, v):
        """Excess road crossings for each possible number of trucks finishing beyond this bridge."""
        wo, wi, bo, bi, cs, co = self._decode(v)
        cm = self.cmax
        a = max(bo, -(-wo // cm))
        b = max(bi, -(-wi // cm))
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
            pattern.append(self.port_flow_cost[((cv[i] >> self.TSH).bit_count(), out, inn)])
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
    def port_cost(self, wo, bo, wi, bi, wn, bn, cargo, ts, ndock, k, here, away):
        """Lower bound on boards + disembarks + sails at a set S of ports (twice the cost, a sail is split
        into a departure and an arrival of 1.5 each), and the bounds on boards and disembarks alone.
        wo/wi: weight that has to leave / enter S (bo/bi: big packages); wn/bn: the part of wi that is aboard
        a ferry docked at S; cargo: [weight, big] of every truck aboard a docked ferry whose packages have to
        go elsewhere; ts: trucks in S; ndock: trucks aboard docked ferries; k: largest ferry;
        here/away: ferries of S docked at S / elsewhere. Also returns the departure-minus-arrival bound."""
        if not cargo:
            key = (wo, bo, wi, bi, wn, bn, ts, ndock, k, here, away)
            r = self.pcm.get(key)
            if r is None:
                r = self.pcm[key] = self._port_cost(wo, bo, wi, bi, wn, bn, None, ts, ndock, k, here, away)
            return r
        return self._port_cost(wo, bo, wi, bi, wn, bn, cargo, ts, ndock, k, here, away)

    def _port_cost(self, wo, bo, wi, bi, wn, bn, cargo, ts, ndock, k, here, away):
        cm = self.cmax
        mo = max(-(-wo // cm), bo)
        mi = max(-(-wi // cm), bi)
        to = self.ntrucks - ts
        boards = max(mo, mi - to)
        disemb = max(mi, mo - ts)
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
            if R:
                total2 = 2 * sum(map(self.road0.__getitem__, cv[:R]))
        if pr.F:
            port2, pres, piece2, sail_extra2 = self._ferry_bound(state, bucket, tnode, tfer, cv)
            total2 += port2
        else:
            pres, piece2, sail_extra2 = {}, 0, 0
        if self.ncut:
            flow_extra = self._flow(cv, pres)
            xfer = self._road_extra(bucket, cv, pres)

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
            alt_a = piece2 - (-(2 * psi_r) // den) + sail_extra2
            alt_b = -(-(2 * psi_a) // den)
            total2 += alt_a if alt_a > alt_b else alt_b
        else:
            total2 += piece2 + sail_extra2
        return (total2 + 1) // 2 + max(xfer, flow_extra)

    def _ferry_bound(self, state, bucket, tnode, tfer, cv):
        """Port and piece costs depend on island membership, not on drives within an island."""
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
        if self.ncut > R:
            pres = {}
            WB, BB, WM, BM = self.WB, self.BB, self.WM, self.BM
            pw = pr.pw
            pbig = self.pbig
            for i in range(R, self.ncut):
                v = cv[i]
                f, a, inside = self.cut_port[i]
                docked = state[IF + f] == a
                aboard = False
                if docked:
                    for t in self.trucks:
                        if tfer[t] == f:
                            aboard = True
                            break
                if not (v & self.WFM) and not aboard:
                    continue
                ts = (v >> self.TSH).bit_count()
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
                    ts = self.ntrucks - ts
                wn = bn = ndock = 0
                cargo = None
                if aboard:
                    lo, hi = self.cut_lo[i], self.cut_hi[i]
                    per = {}
                    for t in self.trucks:
                        if tfer[t] == f:
                            ndock += 1
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
                c2, boards, disemb, diff = self.port_cost(wo, bo, wi, bi, wn, bn, cargo, ts, ndock, max(pr.fk[f], 1),
                                                          1 if docked else 0, 0 if docked else 1)
                balance[self.ferry_group[f]] += diff
                total2 += c2
                if c2:
                    pres[i] = (boards, disemb)
        piece2 = 0
        Q = self.npiece
        if Q:
            pw = pr.pw
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
            if active:
                ts = [0] * Q
                nd = [0] * Q
                for t in self.trucks:
                    o = pm[tnode[t]]
                    while o:
                        low = o & -o
                        ts[low.bit_length() - 1] += 1
                        o ^= low
                    f = tfer[t]
                    if f >= 0:
                        q = dockpiece.get(f * n + state[IF + f])
                        if q is not None:
                            nd[q] += 1
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
                    cost = self.port_cost(Wo[q], Bo[q], Wi[q], Bi[q], Wn[q], Bn[q], cg, ts[q], nd[q],
                                          self.piece_k[q], here, away)
                    piece2 += cost[0]
                    balance[self.ferry_group[self.piece_ferries[q][0][0]]] += cost[3]
        sail_extra2 = 3 * sum(map(abs, balance))
        result = (total2, pres or {}, piece2, sail_extra2)
        self.ferry_cache[key] = result
        return result

    def _road_extra(self, bucket, cv, pres):
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
            TB = self.TB
            ALLB = self.ALLB
            WFM = self.WFM
            cand = [i for i in self.rroad if (cv[i] < TB or cv[i] >= ALLB) and cv[i] & WFM]
            if cand:
                cs = cc = 0
                for i in cand:
                    if not (used >> i) & 1:
                        if cv[i] < TB:
                            cs |= 1 << i
                        else:
                            cc |= 1 << i
                if cs or cc:
                    rmask = self.rmask
                    pgoal = pr.pgoal
                    # sides that get something from a package that is outside U now: no claim there
                    inside = []
                    for p, site, hol in bucket:
                        m = rmask[site]
                        if (m & cs) or (~m & cc):
                            inside.append(m)
                        else:
                            m = rmask[pgoal[p]]
                            cs &= ~m
                            cc &= m
                    best = None
                    if cs or cc:
                        for m in inside:
                            ins = m & cs
                            outs = ~m & cc
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
        # A state is a tuple: (focus, trucks..., ferries..., packages...)
        #   truck:   location l, or n + 2f (aboard ferry f, boarded at this port), or n + 2f + 1 (aboard, has sailed)
        #   ferry:   the port where it is docked
        #   package: location l, or n + t (inside truck t)
        #   focus:   0, or the truck that has to act next (it has just driven or loaded, see successor)
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
        self.fk = [game["Ferries"][f][2] for f in fids]
        # for the map graph: a ferry can also be boarded at the port where it starts, served or not
        self.gports = [tuple(sorted(set(self.fports[i]) | {game["Ferries"][f][0]})) for i, f in enumerate(fids)]
        classes = {}
        self.fcls = [classes.setdefault((self.fports[i], self.fk[i]), len(classes)) for i in range(F)]
        self.pw = [game["Packages"][p][1] for p in pids]
        self.pgoal = [game["Packages"][p][2] for p in pids]

        # focus codes
        self.FD0 = 1                        # truck t has just driven here from u
        self.FL0 = self.FD0 + T * n         # truck t has just loaded package p
        self.FE0 = self.FL0 + T * P        # empty ferry f has arrived for its next boarding
        size = self.FE0 + F
        fkind = [0] * size
        fa = [0] * size
        fb = [0] * size
        for t in range(T):
            for u in range(n):
                c = self.FD0 + t * n + u
                fkind[c], fa[c], fb[c] = 1, t, u
            for p in range(P):
                c = self.FL0 + t * P + p
                fkind[c], fa[c], fb[c] = 2, t, p
        self.fkind, self.fa, self.fb = fkind, fa, fb
        for f in range(F):
            fkind[self.FE0 + f], fa[self.FE0 + f] = 3, f

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
        self.pcls = [pclasses.setdefault((self.pw[p], self.pgoal[p]), len(pclasses)) for p in range(P)]
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
        if OPT_BARREN and OPT_FOCUS:
            for reg in self.regions:
                far.update(reg.far)
        self.adj_far = [tuple((w, far.get((l, w), 0)) for w in self.adj_go[l]) for l in range(n)]
        self.sail_to = [() if f in dead_ferry else tuple(b for b in self.fports[f] if (f, b) not in dead_sail)
                        for f in range(F)]
        self.fdead = [f in dead_ferry for f in range(F)]

    # ------------------------------------------------------------------ precomputation on the map
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
        cmax = max(max(self.tcap), 1) if self.tcap else 1
        self.den = 2 * cmax * lk
        lightest = min((w for w in self.pw if w > 0), default=cmax)
        # A package that cannot share a truck with any other package of positive weight pays a whole
        # truck's movement cost. Packages of weight 0 can always share, so they keep weight 0.
        self.frac_weight = [cmax if (w > 0 and w + lightest > cmax) else w for w in self.pw]
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

    def _truck_standing(self, st, t, l, kind, x, cont, lying, res):
        """Actions of truck t standing at l. kind/x describe the focus (kind 0: t is not the focus truck)."""
        n = self.n
        T = self.T
        P = self.P
        IP = self.IP
        IF = self.IF
        pgoal = self.pgoal
        pw = self.pw
        tid = self.tids[t]
        load = 0
        if cont:
            forced = -1
            for p in cont:
                load += pw[p]
                if forced < 0 and pgoal[p] == l:
                    forced = p
            if forced >= 0 and OPT_FORCED:
                ns = list(st)
                ns[IP + forced] = l
                ns[0] = 0
                if self.multi and self._last == 1:
                    self._finish(ns)
                res.append(("UNLOAD{%d,%d}" % (self.pids[forced], tid), tuple(ns)))
                return
            if (kind != 2 or not OPT_ORDER) and (not OPT_CORRIDOR or l in self.transfer_sites):
                seen = set()
                for p in cont:
                    if OPT_TWINS:
                        key = (pw[p], pgoal[p])
                        if key in seen:
                            continue
                        seen.add(key)
                    ns = list(st)
                    ns[IP + p] = l
                    ns[0] = 0
                    if self.multi and pgoal[p] == l and self._last == 1:
                        self._finish(ns)
                    res.append(("UNLOAD{%d,%d}" % (self.pids[p], tid), tuple(ns)))
        here = lying.get(l)
        if here:
            room = self.tcap[t] - load
            seen = set()
            fl = self.FL0 + t * P
            for p in here:
                w = pw[p]
                if OPT_TWINS:
                    key = (w, pgoal[p])
                    if key in seen:
                        continue
                    seen.add(key)
                if w <= room:
                    ns = list(st)
                    ns[IP + p] = n + t
                    ns[0] = (fl + p) if (OPT_FOCUS and OPT_FL) else 0
                    res.append(("LOAD{%d,%d}" % (self.pids[p], tid), tuple(ns)))
        back = x if kind == 1 else -1
        fd = (self.FD0 + t * n + l) if OPT_FOCUS else 0
        if cont:
            for w in self.adj_go[l]:
                if w != back:
                    ns = list(st)
                    ns[1 + t] = w
                    ns[0] = fd if OPT_UTURN else (self.FD0 + t * n + w)
                    res.append(("DRIVE{%d,%d,%d}" % (tid, l, w), tuple(ns)))
        else:
            # an empty truck drives until it loads or boards (nothing else happens in between), so it does
            # not cross a bridge to a side where no package lies and no ferry is docked
            useful = self._useful
            for w, far in self.adj_far[l]:
                if w != back and (not far or far & useful):
                    ns = list(st)
                    ns[1 + t] = w
                    ns[0] = fd if OPT_UTURN else (self.FD0 + t * n + w)
                    res.append(("DRIVE{%d,%d,%d}" % (tid, l, w), tuple(ns)))
        F = self.F
        if F:
            seen = None
            fdead = self.fdead
            for f in range(F):
                if fdead[f] or st[IF + f] != l:
                    continue
                code0 = n + 2 * f
                cnt = 0
                for t2 in range(1, 1 + T):
                    c = st[t2]
                    if c == code0 or c == code0 + 1:
                        cnt += 1
                if cnt >= self.fk[f]:
                    continue
                if cnt == 0 and OPT_TWINS:
                    key = self.fcls[f]
                    if seen is None:
                        seen = set()
                    if key in seen:
                        continue
                    seen.add(key)
                ns = list(st)
                ns[1 + t] = code0 if OPT_FRESH else code0 + 1
                ns[0] = 0
                res.append(("BOARD{%d,%d}" % (tid, self.fids[f]), tuple(ns)))

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
        return [(action, _State(self, s)) for action, s in self._successors(state.s)]

    def _canon(self, s):
        """The key of a state that is the same for all renamings of interchangeable objects: every truck
        is described by its capacity, its place and the kinds of packages inside it, and so on."""
        if not OPT_SYM:
            return s
        n = self.n
        T = self.T
        IF = self.IF
        IP = self.IP
        foc = s[0]
        kind = self.fkind[foc]
        who = self.fa[foc]
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
        tcap = self.tcap
        for t in range(T):
            c = cont[t]
            if c is None:
                c = ()
            else:
                c.sort()
                c = tuple(c)
            flag = 0
            if who == t:
                if kind == 1:
                    flag = 2 + self.fb[foc]     # has just driven here from fb
                elif kind == 2:
                    flag = 1                    # has just loaded
            tc = s[1 + t]
            if tc < n:
                standing.append((tc, tcap[t], flag, c))
            else:
                if aboard is None:
                    aboard = {}
                f = (tc - n) >> 1
                d = ((tc - n) & 1, tcap[t], c)
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
                ferries.append((fcls[f], s[IF + f], tuple(a), int(kind == 3 and who == f)))
            else:
                ferries.append((fcls[f], s[IF + f], (), int(kind == 3 and who == f)))
        ferries.sort()
        return (tuple(standing), tuple(ferries), tuple(lying))

    def _successors(self, state):
        """The successors of the tuple of a state: [(action, tuple), ...]

        Only legal actions are generated, and some legal actions are left out. Every rule below keeps at
        least one optimal plan (each was also checked against an exhaustive search on thousands of small
        random problems):

        1. Never load a package that lies at its goal (unloading it again would only cost more).
        2. Deliver packages at their goals immediately, globally when no truck has focus.
        3. Identical objects in an identical situation (two empty trucks with the same capacity at the same
           place, two packages with the same weight and goal at the same place, two empty ferries of the same
           line at the same port): only the one with the lowest index may be used first.
        4. At a stop a truck unloads before it loads.
        5. Normal form of commuting actions. An action of a truck and a later action of another truck (or
           ferry) that touch different things can be swapped without changing the result. So a DRIVE or a
           LOAD of truck t can always be moved later, to just before the next action of t. Therefore:
             - after DRIVE or LOAD of truck t the next action is again an action of t (focus on t);
             - a truck that has just driven does not drive straight back;
             - a truck does not board and disembark without a sail in between;
             - an empty truck does not cross a bridge to a side where no package lies and no ferry is
               docked (it drives without interruption until it loads or boards, and it could not).
        6. Never enter a dead end of the map (a side of a bridge where no package starts or has to go and
           no truck starts), and never sail to a port with nothing on its island if another port serves
           the same ferries: whatever a plan does there can be done elsewhere for the same cost or less.
        7. States that differ only by a renaming of interchangeable objects are one state (class _State).
        8. Independent parts of the map are solved one after the other.
        9. Move transfers on empty degree-two road corridors to their endpoints.
        10. An empty ferry sails immediately before a BOARD; this pair may continue truck focus."""
        n = self.n
        T = self.T
        F = self.F
        P = self.P
        IF = self.IF
        IP = self.IP
        pgoal = self.pgoal
        foc = state[0]
        kind = self.fkind[foc]
        res = []
        if self.dead:
            return res
        if kind == 3:
            f = self.fa[foc]
            if self.fk[f] > 0:
                for t in range(T):
                    if state[1 + t] == state[IF + f]:
                        ns = list(state)
                        ns[1 + t] = n + 2 * f + (0 if OPT_FRESH else 1)
                        ns[0] = 0
                        res.append(("BOARD{%d,%d}" % (self.tids[t], self.fids[f]), tuple(ns)))
            return res

        inside = [None] * T
        lying = {}
        rank = self.ncomp
        last = 0
        prank = self.prank
        for p in range(P):
            c = state[IP + p]
            if c < n:
                if c == pgoal[p]:
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

        standing = set()
        aboard_count = [0] * F
        for tc in state[1:1 + T]:
            if tc < n:
                standing.add(tc)
            else:
                aboard_count[(tc - n) >> 1] += 1

        if kind == 1 or kind == 2:
            t = self.fa[foc]
            self._truck_standing(state, t, state[1 + t], kind, self.fb[foc], inside[t], lying, res)
            if OPT_LAZYSAIL:
                loc = state[1 + t]
                for f in range(F):
                    port = state[IF + f]
                    if self.fk[f] > 0 and not aboard_count[f] and port != loc and loc in self.sail_to[f]:
                        action, ns = self._sail(state, f, port, loc)
                        ns = list(ns)
                        ns[0] = self.FE0 + f
                        res.append((action, tuple(ns)))
            return res
        tcap = self.tcap
        trank = self.trank
        if OPT_FORCED:
            for t, cargo in enumerate(inside):
                if cargo and (not multi or trank[t] == rank):
                    loc = state[1 + t]
                    if loc < n and any(pgoal[p] == loc for p in cargo):
                        self._truck_standing(state, t, loc, 0, -1, cargo, lying, res)
                        return res
        seen_t = set()
        for t in range(T):
            if multi and trank[t] != rank:
                continue
            tc = state[1 + t]
            cont = inside[t]
            if not cont and OPT_TWINS:
                key = (tc, tcap[t])
                if key in seen_t:
                    continue
                seen_t.add(key)
            if tc < n:
                self._truck_standing(state, t, tc, 0, -1, cont, lying, res)
            elif (tc - n) & 1 or not OPT_FOCUS:
                f = (tc - n) >> 1
                ns = list(state)
                ns[1 + t] = state[IF + f]
                ns[0] = 0
                res.append(("DISEMBARK{%d,%d}" % (self.tids[t], self.fids[f]), tuple(ns)))
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
                for b in self.sail_to[f]:
                    if b != port and (not OPT_LAZYSAIL or aboard_count[f] or b in standing):
                        action, ns = self._sail(state, f, port, b)
                        if OPT_LAZYSAIL and not aboard_count[f]:
                            ns = list(ns)
                            ns[0] = self.FE0 + f
                            ns = tuple(ns)
                        res.append((action, ns))
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
            return 0            # a package cannot reach its goal: there is no plan at all
        key = state[1:]
        h = self.hcache.get(key)
        if h is None:
            h = self.hcache[key] = self._h(state)
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
        # the bound does not depend on the bookkeeping part of the state, only on where things are
        if self.F:
            key = (tuple(tnode), state[self.IF:])
        else:
            key = state[1:]
        h = self.hcache2.get(key)
        if h is None:
            h = self.hcache2[key] = self._bound(state, tnode, tfer)
        return h

    def _bound(self, state, tnode, tfer):
        n = self.n
        IP = self.IP
        pgoal = self.pgoal
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
                # Custody affects movement only for merging groups or cargo aboard a ferry.
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
