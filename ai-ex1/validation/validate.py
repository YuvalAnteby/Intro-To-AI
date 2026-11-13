import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Independent validator for ex1.py (not part of the submission).

For a random small game it builds the WHOLE reachable world graph with a reference implementation of the
rules written from the assignment text (no code shared with ex1.py), computes the exact optimal
cost-to-goal h* of every world state, and then checks:

  A. A* (the course's search.astar_search with ex1's successor / goal_test / h_astar) returns a plan that the
     official ex1_check.World accepts, that solves the game, and whose cost equals the reference optimum
     (or returns no plan when the game is unsolvable).
  B. Every action ex1.successor generates, on every state it can reach, is legal in the reference model and
     leads to the state the reference model says it leads to.
  C. h_astar(state) <= h*(state) on every state reachable through ex1.successor (what a grader can see).
  D. h_astar(state) <= h*(state) on every reachable WORLD state (stricter: also states ex1 prunes away).
  E. h is a non-negative int, 0 on goal states; goal_test agrees with the reference.

usage: python validate.py <first seed> <count> <profile> [--jobs N]
"""
import heapq
import io
import random
import sys
import time
import contextlib
from collections import deque

import search
import ex1
import ex1_check

INF = float("inf")
CAP = 120000        # skip games whose reachable world is larger than this


# --------------------------------------------------------------------------- random games
PROFILES = {
    #        nmax Tmax Pmax Fmax
    "S": (6, 2, 3, 2),
    "M": (8, 3, 3, 3),
    "L": (12, 2, 2, 3),
    "W": (5, 2, 4, 1),
    "R": (9, 2, 3, 0),      # roads only: bridges, cycles, capacities
    "H": (7, 3, 2, 4),      # many ferries / hubs
    "T": (4, 2, 2, 1),      # tiny, building block of profile D
    "X": (6, 2, 3, 2),      # inputs outside the assignment's wording: ferry docked at a port it does not
                            # serve, ferry for 0 trucks, truck of capacity 0
}


def random_game(rng, profile):
    if profile == "D":
        # two or three independent maps side by side: several parts, for the "one part after the other" rule
        parts = [random_game(rng, "T") for _ in range(rng.choice([2, 2, 3]))]
        out = {"Locations": 0, "Roads": set(), "Ports": set(), "Trucks": {}, "Ferries": {}, "Packages": {}}
        for i, g in enumerate(parts):
            o = out["Locations"]
            if i and rng.random() < .2:
                g["Packages"] = {}                  # a part with trucks and nothing to do
            out["Roads"] |= {(a + o, b + o) for a, b in g["Roads"]}
            out["Ports"] |= {a + o for a in g["Ports"]}
            for k, (l, c) in g["Trucks"].items():
                out["Trucks"][k + 1000 * i] = (l + o, c)
            for k, (l, L, c) in g["Ferries"].items():
                out["Ferries"][k + 1000 * i] = (l + o, tuple(a + o for a in L), c)
            for k, (a, w, b) in g["Packages"].items():
                out["Packages"][k + 1000 * i] = (a + o, w, b + o)
            out["Locations"] += g["Locations"]
        return out
    nmax, Tmax, Pmax, Fmax = PROFILES[profile]
    n = rng.randint(2, nmax)
    n_isl = rng.randint(1, min(n, 4)) if Fmax else rng.choice([1, 1, 1, 2])
    isl = [[] for _ in range(n_isl)]
    locs = list(range(n))
    rng.shuffle(locs)
    for i, l in enumerate(locs):
        isl[i if i < n_isl else rng.randrange(n_isl)].append(l)
    roads = set()
    style = rng.choice(["tree", "tree", "path", "cyc", "dense"])
    for members in isl:
        for i in range(1, len(members)):
            j = i - 1 if style == "path" else rng.randrange(i)
            roads.add((members[i], members[j]) if rng.random() < .5 else (members[j], members[i]))
        if len(members) >= 3 and style in ("cyc", "dense"):
            for _ in range(1 if style == "cyc" else rng.randint(1, 3)):
                a, b = rng.sample(members, 2)
                if (a, b) not in roads and (b, a) not in roads:
                    roads.add((a, b))
    ferries = {}
    ports = set()
    F = rng.randint(0, Fmax) if n_isl == 1 else rng.randint(1, Fmax) if Fmax else 0
    fid = 20
    chain = rng.random() < .75
    for i in range(F):
        if ferries and rng.random() < .15:              # a twin ferry on the same line
            l, L, k = ferries[rng.choice(sorted(ferries))]
            ferries[fid] = (rng.choice(sorted(L)), L, k if rng.random() < .7 else rng.randint(1, 3))
            fid += 1
            continue
        cnt = min(n, rng.choice([2, 2, 2, 3, 3, 4]))
        if chain and n_isl > 1 and i < n_isl - 1:
            L = {rng.choice(isl[i]), rng.choice(isl[i + 1])}
            while len(L) < cnt and rng.random() < .5:
                L.add(rng.randrange(n))
        else:
            L = set(rng.sample(range(n), cnt))
        if len(L) < 2:
            L.add(rng.choice([x for x in range(n) if x not in L]))
        L = tuple(sorted(L)) if rng.random() < .5 else tuple(L)
        ferries[fid] = (rng.choice(L), L, rng.choice([1, 1, 2, 2, 3]))
        ports |= set(L)
        fid += 1
    for f in ferries.values():
        ports |= set(f[1])
    capset = rng.choice([[4], [5, 10], [3, 6, 7], [6, 10], [2, 5, 9], [10]])
    T = rng.randint(1, Tmax)
    trucks = {}
    tid = 10
    for _ in range(T):
        if trucks and rng.random() < .2:
            trucks[tid] = trucks[rng.choice(sorted(trucks))]
        else:
            trucks[tid] = (rng.randrange(n), rng.choice(capset))
        tid += 1
    cmax = max(c for _, c in trucks.values())
    P = rng.randint(1, Pmax)
    packages = {}
    pid = 30
    shared = rng.randrange(n)
    for _ in range(P):
        r = rng.random()
        if packages and r < .15:
            packages[pid] = packages[rng.choice(sorted(packages))]
        else:
            w = rng.randint(1, cmax) if rng.random() < .97 else cmax + 1
            if rng.random() < .3:
                w = rng.choice([cmax, (cmax + 1) // 2, cmax // 2 + 1, 1])
            goal = shared if rng.random() < .45 else rng.randrange(n)
            start = rng.randrange(n)
            if rng.random() < .05:
                start = goal
            packages[pid] = (start, w, goal)
        pid += 1
    if rng.random() < .3:       # ids in a scrambled order / odd values
        def remap(d, base):
            keys = sorted(d)
            new = rng.sample(range(base, base + 60), len(keys))
            return {new[i]: d[k] for i, k in enumerate(keys)}
        trucks, ferries, packages = remap(trucks, 100), remap(ferries, 200), remap(packages, 300)
    if profile == "X":
        for f in sorted(ferries):
            l, L, k = ferries[f]
            if rng.random() < .45:
                l = rng.randrange(n)
            if rng.random() < .12:
                k = 0
            ferries[f] = (l, L, k)
            ports.add(l)
        for t in sorted(trucks):
            if rng.random() < .08:
                trucks[t] = (trucks[t][0], 0)
    return {"Locations": n, "Roads": roads, "Ports": ports, "Trucks": trucks, "Ferries": ferries,
            "Packages": packages}


# --------------------------------------------------------------------------- reference model
class Ref:
    """World state: (truck_0.., ferry_0.., package_0..) with objects in sorted ID order.
    truck: location, or n + f (aboard ferry f); ferry: port; package: location, or n + t (inside truck t)."""

    def __init__(self, game):
        self.n = n = game["Locations"]
        self.tids = sorted(game["Trucks"])
        self.fids = sorted(game["Ferries"])
        self.pids = sorted(game["Packages"])
        self.T, self.F, self.P = len(self.tids), len(self.fids), len(self.pids)
        adj = [set() for _ in range(n)]
        for a, b in game["Roads"]:
            if a != b:
                adj[a].add(b)
                adj[b].add(a)
        self.adj = [sorted(x) for x in adj]
        self.cap = [game["Trucks"][t][1] for t in self.tids]
        self.served = [sorted(set(game["Ferries"][f][1])) for f in self.fids]
        self.k = [game["Ferries"][f][2] for f in self.fids]
        self.w = [game["Packages"][p][1] for p in self.pids]
        self.goal = [game["Packages"][p][2] for p in self.pids]
        self.init = tuple([game["Trucks"][t][0] for t in self.tids] + [game["Ferries"][f][0] for f in self.fids]
                          + [game["Packages"][p][0] for p in self.pids])
        self._parts(game)

    def _parts(self, game):
        """Connected parts of the map (roads, ferry routes, start docks), computed here, not taken from ex1."""
        n = self.n
        g = list(range(n + self.F))

        def find(x):
            while g[x] != x:
                g[x] = g[g[x]]
                x = g[x]
            return x
        for a in range(n):
            for b in self.adj[a]:
                g[find(a)] = find(b)
        for f in range(self.F):
            for a in list(self.served[f]) + [self.init[self.T + f]]:
                g[find(a)] = find(n + f)
        self.tpart = [find(self.init[t]) for t in range(self.T)]
        self.fpart = [find(n + f) for f in range(self.F)]
        self.ppart = [find(self.goal[p]) for p in range(self.P)]

    def expected(self, before, after):
        """The only deviation ex1 may show from the rules: when an action delivers the last package of a
        part of the map, the trucks and ferries of exactly that part are written back to their start
        positions. Returns the tuple ex1 must produce for a step before -> after."""
        o = self.T + self.F
        open_before = set(self.ppart[p] for p in range(self.P) if before[o + p] != self.goal[p])
        open_after = set(self.ppart[p] for p in range(self.P) if after[o + p] != self.goal[p])
        done = open_before - open_after
        if not done:
            return after
        out = list(after)
        for t in range(self.T):
            if self.tpart[t] in done:
                out[t] = self.init[t]
        for f in range(self.F):
            if self.fpart[f] in done:
                out[self.T + f] = self.init[self.T + f]
        return tuple(out)

    def is_goal(self, s):
        o = self.T + self.F
        return all(s[o + p] == self.goal[p] for p in range(self.P))

    def succ(self, s):
        """[(action string, cost, next state)] : every legal action."""
        n, T, F, P = self.n, self.T, self.F, self.P
        out = []
        oF, oP = T, T + F
        for t in range(T):
            l = s[t]
            tid = self.tids[t]
            if l < n:
                for b in self.adj[l]:
                    ns = list(s); ns[t] = b
                    out.append(("DRIVE{%d,%d,%d}" % (tid, l, b), 1, tuple(ns)))
                load = sum(self.w[p] for p in range(P) if s[oP + p] == n + t)
                for p in range(P):
                    c = s[oP + p]
                    if c == l and load + self.w[p] <= self.cap[t]:
                        ns = list(s); ns[oP + p] = n + t
                        out.append(("LOAD{%d,%d}" % (self.pids[p], tid), 1, tuple(ns)))
                    elif c == n + t:
                        ns = list(s); ns[oP + p] = l
                        out.append(("UNLOAD{%d,%d}" % (self.pids[p], tid), 1, tuple(ns)))
                for f in range(F):
                    if s[oF + f] == l and sum(1 for x in range(T) if s[x] == n + f) < self.k[f]:
                        ns = list(s); ns[t] = n + f
                        out.append(("BOARD{%d,%d}" % (tid, self.fids[f]), 1, tuple(ns)))
            else:
                f = l - n
                ns = list(s); ns[t] = s[oF + f]
                out.append(("DISEMBARK{%d,%d}" % (tid, self.fids[f]), 1, tuple(ns)))
        for f in range(F):
            a = s[oF + f]
            for b in self.served[f]:
                if b != a:
                    ns = list(s); ns[oF + f] = b
                    out.append(("SAIL{%d,%d,%d}" % (self.fids[f], a, b), 3, tuple(ns)))
        return out

    def explore(self, cap=CAP):
        """ids of all reachable states, exact h* of each (inf if no goal reachable), and the action table."""
        ids = {self.init: 0}
        states = [self.init]
        rev = [[]]
        table = [None]
        q = deque([0])
        while q:
            i = q.popleft()
            d = {}
            for a, c, ns in self.succ(states[i]):
                j = ids.get(ns)
                if j is None:
                    j = ids[ns] = len(states)
                    if j >= cap:
                        return None
                    states.append(ns)
                    rev.append([])
                    table.append(None)
                    q.append(j)
                rev[j].append((i, c))
                d[a] = j
            table[i] = d
        hs = [INF] * len(states)
        heap = []
        for i, s in enumerate(states):
            if self.is_goal(s):
                hs[i] = 0
                heap.append((0, i))
        heapq.heapify(heap)
        while heap:
            d, i = heapq.heappop(heap)
            if d > hs[i]:
                continue
            for j, c in rev[i]:
                if d + c < hs[j]:
                    hs[j] = d + c
                    heapq.heappush(heap, (d + c, j))
        return ids, states, hs, table


# --------------------------------------------------------------------------- the checks
def to_world(pr, s):
    n = pr.n
    out = []
    for t in range(pr.T):
        c = s[1 + t]
        out.append(c if c < n else n + ((c - n) >> 1))
    out.extend(s[1 + pr.T:])
    return tuple(out)


def from_world(pr, w):
    n = pr.n
    out = [0]
    for t in range(pr.T):
        c = w[t]
        out.append(c if c < n else n + 2 * (c - n) + 1)
    out.extend(w[pr.T:])
    return tuple(out)


def check_game(game, deep=True):
    """Returns (status, detail). status: 'ok', 'skip', 'unsolvable-ok' or 'FAIL ...'."""
    ref = Ref(game)
    r = ref.explore()
    if r is None:
        return "skip", "world too large"
    ids, states, hs, table = r
    opt = hs[0]
    fails = []

    # ---- A. the plan of A*
    with contextlib.redirect_stdout(io.StringIO()):
        pr = ex1.create_logistics_problem(game)
    t0 = time.perf_counter()
    res = search.astar_search(pr, pr.h_astar)
    dt = time.perf_counter() - t0
    if opt == INF:
        if res is not None:
            fails.append("A: plan returned for an unsolvable game")
    elif res is None:
        fails.append("A: no plan, optimum is %d" % opt)
    else:
        node, expanded = res
        plan = [str(x.action) for x in node.path()[::-1]][1:]
        world = ex1_check.World(game)
        try:
            for a in plan:
                world.apply(a)
            if not world.solved():
                fails.append("A: plan does not solve")
            elif world.cost != opt:
                fails.append("A: cost %d, optimum %d" % (world.cost, opt))
            if node.path_cost != world.cost:
                fails.append("A: path_cost %r != replayed cost %r" % (node.path_cost, world.cost))
        except ex1_check.IllegalAction as e:
            fails.append("A: illegal action in plan: %s" % e)
    if not deep:
        return ("FAIL " + "; ".join(fails), game) if fails else ("ok", dt)

    # ---- B, C, E: every state reachable through ex1.successor
    with contextlib.redirect_stdout(io.StringIO()):
        pr = ex1.create_logistics_problem(game)
    init = pr.initial
    if to_world(pr, init.s) != ref.init:
        fails.append("B: initial state does not match the game")
    seen = {init.s}
    q = deque([init])
    nstates = 0
    worst = None
    while q and len(fails) < 5:
        st = q.popleft()
        nstates += 1
        w = to_world(pr, st.s)
        wi = ids.get(w)
        if wi is None:
            # only the documented reset of a finished independent part may leave the reachable world
            # (a ferry put back at a start port it cannot sail to); legality is still checked below
            if not pr.multi:
                fails.append("B: ex1 reached a world state the rules cannot reach: %r" % (st.s,))
                continue
            tab = {a: ns_ for a, c_, ns_ in ref.succ(w)}
            hstar = None
        else:
            tab = None
            hstar = hs[wi]
        h = pr.h_astar(search.Node(st))
        if not isinstance(h, int) or isinstance(h, bool) or h < 0:
            fails.append("E: h = %r is not a non-negative int" % (h,))
        if hstar is not None and h > hstar:
            if worst is None or h - hstar > worst[0]:
                worst = (h - hstar, h, hstar, st.s)
        g = ref.is_goal(w)
        if bool(pr.goal_test(st)) != g:
            fails.append("E: goal_test wrong on %r" % (st.s,))
        if g and h != 0:
            fails.append("E: h = %r on a goal state" % (h,))
        before = st.s
        succ = pr.successor(st)
        if st.s != before:
            fails.append("B: successor changed its input state")
        acts = set()
        for a, ns in succ:
            if a in acts:
                fails.append("B: duplicate action %s" % a)
            acts.add(a)
            if tab is None:
                j = table[wi].get(a)
                want = states[j] if j is not None else None
            else:
                want = tab.get(a)
            if want is None:
                fails.append("B: illegal action %s in state %r" % (a, st.s))
                continue
            nw = to_world(pr, ns.s)
            if nw != want and not (pr.multi and nw == ref.expected(w, want)):
                fails.append("B: %s from %r gives %r, rules give %r" % (a, st.s, nw, want))
            if ns.s not in seen:
                seen.add(ns.s)
                q.append(ns)
    if worst is not None:
        fails.append("C: h overestimates on a successor-reachable state: h=%d h*=%s state=%r" % worst[1:])

    # ---- D: every reachable world state
    with contextlib.redirect_stdout(io.StringIO()):
        pr = ex1.create_logistics_problem(game)
    worst = None
    nbad = 0
    for i, w in enumerate(states):
        h = pr.h_astar(search.Node(ex1._State(pr, from_world(pr, w))))
        if h > hs[i]:
            nbad += 1
            if worst is None or h - hs[i] > worst[0]:
                worst = (h - hs[i], h, hs[i], w)
    if worst is not None:
        fails.append("D: h overestimates on %d world states, worst: h=%d h*=%s world=%r" % ((nbad,) + worst[1:]))
    if fails:
        return "FAIL " + "; ".join(fails), game
    if opt == INF:
        return "unsolvable-ok", (len(states), nstates)
    return "ok", (len(states), nstates, opt)


def run(seed0, count, profile, deep=True):
    stats = {"ok": 0, "skip": 0, "unsolvable-ok": 0, "FAIL": 0}
    nworld = nsucc = 0
    t0 = time.time()
    for seed in range(seed0, seed0 + count):
        game = random_game(random.Random(seed), profile)
        try:
            status, detail = check_game(game, deep)
        except Exception as e:      # a crash of ex1 is a failure too
            import traceback
            tb = traceback.format_exc(limit=6)
            r = Ref(game).explore()
            if r is not None and r[2][0] == INF:
                stats["crash-unsolvable"] = stats.get("crash-unsolvable", 0) + 1
                print("seed %d profile %s CRASH on an unsolvable game: %s" % (seed, profile, tb.strip().splitlines()[-1]), flush=True)
                continue
            status, detail = "FAIL crash: " + tb, game
        if status.startswith("FAIL"):
            stats["FAIL"] += 1
            print("seed %d profile %s %s\n   game = %r" % (seed, profile, status, detail), flush=True)
        else:
            stats[status] += 1
            if status == "ok" and deep:
                nworld += detail[0]
                nsucc += detail[1]
    print("DONE profile %s seeds %d..%d: %r world states checked %d, ex1 states checked %d, %.0f s"
          % (profile, seed0, seed0 + count - 1, stats, nworld, nsucc, time.time() - t0), flush=True)


if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], "--shallow" not in sys.argv)
