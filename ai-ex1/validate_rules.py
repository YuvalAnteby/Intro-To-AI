"""Implementation check for SUCCESSOR_RULES_PROOF.md (evidence about the code, not part of the proof).

For small random instances and every on/off combination of the four new switches, it:
  1. enumerates every raw state the successor function of ex1.py can reach from the initial state,
  2. checks that every generated action is legal in an independent world model,
  3. computes, with Dijkstra on both graphs, the cheapest goal cost from every reachable state inside the
     pruned graph and in the unrestricted world, and requires them to be equal (Theorem 1),
  4. checks h(s) <= world optimum on every reachable state, and that A* returns the world optimum.

The world model below is written from the assignment text and shares no code with ex1.py.

    python3 validate_rules.py SEED_FROM SEED_TO [--big]
"""
import heapq
import itertools
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.dirname(HERE)
sys.path[:0] = [HERE, os.path.join(WORK, "course"), WORK]   # beside ex1.py, or in tools/ of this layout

if "--file" in sys.argv:                       # check another solver file under the name ex1
    import importlib.util
    _path = os.path.abspath(sys.argv[sys.argv.index("--file") + 1])
    _spec = importlib.util.spec_from_file_location("ex1", _path)
    ex1 = importlib.util.module_from_spec(_spec)
    sys.modules["ex1"] = ex1
    _spec.loader.exec_module(ex1)
else:
    import ex1      # noqa: E402
import search       # noqa: E402

SWITCHES = ("OPT_EMPTY_SAIL", "OPT_EFFCAP", "OPT_USELESS", "OPT_TOWARD")
MODE1 = "--mode1" in sys.argv    # condition 1: only the initial state must keep its optimum
HISTORY = ("OPT_HISTORY", "OPT_FOCUS", "OPT_UTURN", "OPT_FRESH", "OPT_NEEDBOARD", "OPT_CORRIDOR")
INF = float("inf")


# ---------------------------------------------------------------------------------------------- world model
class World:
    """State: (truck places, ferry docks, package places). Truck place: location, or n + f when aboard ferry f.
    Package place: location, or n + t when inside truck t. Objects are indexed in sorted ID order."""

    def __init__(self, game):
        self.n = game["Locations"]
        self.tids = sorted(game["Trucks"])
        self.fids = sorted(game["Ferries"])
        self.pids = sorted(game["Packages"])
        self.cap = [game["Trucks"][t][1] for t in self.tids]
        self.ports = [set(game["Ferries"][f][1]) for f in self.fids]
        self.kmax = [game["Ferries"][f][2] for f in self.fids]
        self.w = [game["Packages"][p][1] for p in self.pids]
        self.goal = [game["Packages"][p][2] for p in self.pids]
        self.near = {x: set() for x in range(self.n)}
        for a, b in game["Roads"]:
            self.near[a].add(b)
            self.near[b].add(a)
        self.start = (tuple(game["Trucks"][t][0] for t in self.tids),
                      tuple(game["Ferries"][f][0] for f in self.fids),
                      tuple(game["Packages"][p][0] for p in self.pids))

    def is_goal(self, s):
        return all(pos == g for pos, g in zip(s[2], self.goal))

    def load(self, s, t):
        return sum(self.w[p] for p, pos in enumerate(s[2]) if pos == self.n + t)

    def aboard(self, s, f):
        return sum(1 for pos in s[0] if pos == self.n + f)

    def apply(self, s, act):
        """The successor of s by act = (kind, args), or None if act is illegal in s."""
        n = self.n
        trucks, docks, packs = list(s[0]), list(s[1]), list(s[2])
        kind, a = act
        if kind == "DRIVE":
            t, x, y = a
            if trucks[t] != x or x >= n or y not in self.near[x]:
                return None
            trucks[t] = y
        elif kind == "LOAD":
            p, t = a
            if trucks[t] >= n or packs[p] != trucks[t] or self.load(s, t) + self.w[p] > self.cap[t]:
                return None
            packs[p] = n + t
        elif kind == "UNLOAD":
            p, t = a
            if packs[p] != n + t or trucks[t] >= n:
                return None
            packs[p] = trucks[t]
        elif kind == "BOARD":
            t, f = a
            if trucks[t] >= n or trucks[t] != docks[f] or not self.aboard(s, f) < self.kmax[f]:
                return None
            trucks[t] = n + f
        elif kind == "SAIL":
            f, x, y = a
            if docks[f] != x or y not in self.ports[f] or y == x:
                return None
            docks[f] = y
        elif kind == "DISEMBARK":
            t, f = a
            if trucks[t] != n + f:
                return None
            trucks[t] = docks[f]
        else:
            return None
        return (tuple(trucks), tuple(docks), tuple(packs))

    def successors(self, s):
        n = self.n
        out = []
        T, F, P = len(self.tids), len(self.fids), len(self.pids)
        acts = []
        for t in range(T):
            x = s[0][t]
            if x < n:
                acts += [("DRIVE", (t, x, y)) for y in self.near[x]]
                acts += [("LOAD", (p, t)) for p in range(P)]
                acts += [("BOARD", (t, f)) for f in range(F)]
            else:
                acts.append(("DISEMBARK", (t, x - n)))
        for p in range(P):
            if s[2][p] >= n:
                acts.append(("UNLOAD", (p, s[2][p] - n)))
        for f in range(F):
            acts += [("SAIL", (f, s[1][f], y)) for y in self.ports[f]]
        for act in acts:
            nxt = self.apply(s, act)
            if nxt is not None:
                out.append((3 if act[0] == "SAIL" else 1, nxt))
        return out

    def parse(self, text):
        """Action string of ex1.py -> (kind, internal indices)."""
        kind, rest = text.split("{")
        nums = [int(v) for v in rest.rstrip("}").split(",")]
        ti = {v: i for i, v in enumerate(self.tids)}
        fi = {v: i for i, v in enumerate(self.fids)}
        pi = {v: i for i, v in enumerate(self.pids)}
        if kind == "DRIVE":
            return kind, (ti[nums[0]], nums[1], nums[2])
        if kind in ("LOAD", "UNLOAD"):
            return kind, (pi[nums[0]], ti[nums[1]])
        if kind in ("BOARD", "DISEMBARK"):
            return kind, (ti[nums[0]], fi[nums[1]])
        return kind, (fi[nums[0]], nums[1], nums[2])


def from_raw(pr, raw):
    """ex1.py raw tuple -> world state."""
    n, T, F = pr.n, pr.T, pr.F
    trucks = tuple(c if c < n else n + ((c - n) >> 1) for c in raw[1:1 + T])
    docks = tuple(raw[1 + T:1 + T + F])
    packs = tuple(raw[1 + T + F:])
    return trucks, docks, packs


def world_values(world, roots, limit):
    """Optimal goal cost in the world for every state reachable from roots (None if more than limit states)."""
    seen = set(roots)
    order = list(roots)
    back = {}
    for s in order:
        for cost, nxt in world.successors(s):
            back.setdefault(nxt, []).append((cost, s))
            if nxt not in seen:
                seen.add(nxt)
                order.append(nxt)
                if len(order) > limit:
                    return None
    value = {}
    heap = [(0, i, s) for i, s in enumerate(order) if world.is_goal(s)]
    heapq.heapify(heap)
    counter = itertools.count(len(order))
    while heap:
        v, _, s = heapq.heappop(heap)
        if s in value:
            continue
        value[s] = v
        for cost, prev in back.get(s, ()):
            if prev not in value:
                heapq.heappush(heap, (v + cost, next(counter), prev))
    return value


# ---------------------------------------------------------------------------------------------- random games
def ferry_game(rng):
    """Two or three islands, trucks and packages on different islands, ferries docked away from the trucks:
    the situations that Rules A and D act on."""
    sizes = [rng.choice([1, 2, 2, 3]) for _ in range(rng.choice([2, 2, 3]))]
    parts, roads, x = [], set(), 0
    for size in sizes:
        part = list(range(x, x + size))
        x += size
        for i in range(1, size):
            roads.add((part[i - 1], part[i]))
        parts.append(part)
    n = x
    ports, ferries = set(), {}
    for i in range(rng.choice([1, 1, 2])):
        served = sorted({rng.choice(part) for part in parts})
        ports |= set(served)
        ferries[20 + i] = (rng.choice(served), tuple(served), rng.choice([1, 1, 2]))
    truck_part = rng.randrange(len(parts))
    trucks = {10 + i: (rng.choice(parts[truck_part] if rng.random() < 0.8 else rng.choice(parts)),
                       rng.choice([1, 2, 3]))
              for i in range(rng.choice([1, 1, 2]))}
    others = [p for i, p in enumerate(parts) if i != truck_part] or parts
    packages = {30 + i: (rng.choice(rng.choice(others)), rng.choice([1, 1, 2]), rng.randrange(n))
                for i in range(rng.choice([1, 1, 2]))}
    return {"Locations": n, "Roads": roads, "Ports": ports, "Trucks": trucks,
            "Ferries": ferries, "Packages": packages}


def random_game(rng, big=False):
    if rng.random() < 0.35:
        return ferry_game(rng)
    n = rng.randint(3, 7 if big else 6)
    islands = rng.choice([1, 2, 2, 3]) if n >= 4 else rng.choice([1, 2])
    cut = sorted(rng.sample(range(1, n), islands - 1)) if islands > 1 else []
    parts = [list(range(a, b)) for a, b in zip([0] + cut, cut + [n])]
    roads = set()
    for part in parts:
        for i in range(1, len(part)):
            roads.add((part[rng.randrange(i)], part[i]))
        if len(part) >= 3 and rng.random() < 0.4:
            a, b = rng.sample(part, 2)
            if (a, b) not in roads and (b, a) not in roads:
                roads.add((a, b))
    ports = set()
    ferries = {}
    fid = 20
    if islands > 1 or rng.random() < 0.3:
        for _ in range(rng.choice([1, 1, 2]) if islands > 1 else 1):
            served = sorted({rng.choice(part) for part in rng.sample(parts, min(len(parts), rng.choice([2, 3])))})
            if len(served) < 2:
                served = sorted(set(served) | {rng.randrange(n)})
            if len(served) < 2:
                continue
            ports |= set(served)
            k = rng.choice([1, 1, 2, 2, 3, 0]) if not big else rng.choice([1, 2])
            ferries[fid] = (rng.choice(served), tuple(served), k)
            fid += 1
    trucks = {}
    for i in range(rng.choice([1, 2, 2, 3])):
        trucks[10 + i] = (rng.randrange(n), rng.choice([1, 2, 3, 4, 5]))
    packages = {}
    for i in range(rng.choice([1, 2, 2, 3] if not big else [2, 3])):
        packages[30 + i] = (rng.randrange(n), rng.choice([1, 2, 2, 3]), rng.randrange(n))
    return {"Locations": n, "Roads": roads, "Ports": ports, "Trucks": trucks,
            "Ferries": ferries, "Packages": packages}


# ---------------------------------------------------------------------------------------------- the check
def set_switches(bits):
    if isinstance(bits, dict):
        for name, on in bits.items():
            setattr(ex1, name, on)
        return
    for name, on in zip(SWITCHES, bits):
        setattr(ex1, name, bool(on))


def raw_is_goal(pr, raw):
    return all(raw[pr.IP + p] == pr.pgoal[p] for p in range(pr.P))


def check(game, bits, limit=60000):
    """Returns (status, detail). status: 'ok', 'skip' or 'FAIL'."""
    set_switches(bits)
    import io
    import contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        pr = ex1.create_logistics_problem(game)
    world = World(game)

    # 1. every raw state the successor function reaches, with its edges
    start = pr.s0
    seen = {start}
    order = [start]
    edges = {}
    for raw in order:
        kids = pr._successors(raw)
        edges[raw] = kids
        for action, kid in kids:
            if kid not in seen:
                seen.add(kid)
                order.append(kid)
                if len(order) > limit:
                    return "skip", "pruned graph too large"

    # 2. legality of every generated action
    for raw, kids in edges.items():
        ws = from_raw(pr, raw)
        for action, kid in kids:
            nxt = world.apply(ws, world.parse(action))
            if nxt is None:
                return "FAIL", "illegal action %s in %s" % (action, raw)
            got = from_raw(pr, kid)
            if got != nxt:
                # allowed only for the completed-component write-back: package places must agree
                if got[2] != nxt[2]:
                    return "FAIL", "wrong child for %s in %s" % (action, raw)

    # 3. pruned optimum versus world optimum on every reachable raw state
    roots = list({from_raw(pr, raw) for raw in order})
    value = world_values(world, roots, limit * 4)
    if value is None:
        return "skip", "world graph too large"
    back = {}
    for raw, kids in edges.items():
        for action, kid in kids:
            back.setdefault(kid, []).append((3 if action.startswith("SAIL") else 1, raw))
    pruned = {}
    heap = [(0, i, raw) for i, raw in enumerate(order) if raw_is_goal(pr, raw)]
    heapq.heapify(heap)
    counter = itertools.count(len(order))
    while heap:
        v, _, raw = heapq.heappop(heap)
        if raw in pruned:
            continue
        pruned[raw] = v
        for cost, prev in back.get(raw, ()):
            if prev not in pruned:
                heapq.heappush(heap, (v + cost, next(counter), prev))
    lost = 0
    for raw in order:
        want = value.get(from_raw(pr, raw), INF)
        have = pruned.get(raw, INF)
        if want != have:
            if not MODE1:
                return "FAIL", "state %s: pruned %s, world %s" % (raw, have, want)
            lost += 1
        h = pr.h_astar(search.Node(ex1._State(pr, raw)))
        if h > want:
            return "FAIL", "h = %s > %s at %s" % (h, want, raw)
    if MODE1 and pruned.get(start, INF) != value.get(world.start, INF):
        return "FAIL", "initial state: pruned %s, world %s" % (pruned.get(start, INF), value.get(world.start, INF))

    # 4. the real A* with the real heuristic
    best = value.get(world.start, INF)
    with contextlib.redirect_stdout(io.StringIO()):
        pr2 = ex1.create_logistics_problem(game)
        result = search.astar_search(pr2, pr2.h_astar)
    if result is None:
        if best != INF:
            return "FAIL", "A* found nothing, optimum %s" % best
    else:
        node, _ = result
        if node.path_cost != best:
            return "FAIL", "A* cost %s, optimum %s" % (node.path_cost, best)
        state = world.start
        for nd in node.path()[::-1][1:]:
            state = world.apply(state, world.parse(nd.action))
            if state is None:
                return "FAIL", "A* plan illegal at %s" % nd.action
        if not world.is_goal(state):
            return "FAIL", "A* plan does not reach the goal"
    return "ok", "%d pruned states, optimum %s, %d states without their own optimum" % (len(order), best, lost)


def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    big = "--big" in sys.argv
    combos = list(itertools.product((0, 1), repeat=4))
    if MODE1:
        # all of A-D on or off, with every history rule on, each history rule off in turn, and all history off
        combos = []
        for ad in (True, False):
            base = {s: ad for s in SWITCHES}
            combos.append(dict(base, **{h: True for h in HISTORY}))
            for h in HISTORY[1:]:
                combos.append(dict(base, **{x: x != h for x in HISTORY}))
            combos.append(dict(base, **{h: False for h in HISTORY}))
    totals = {"ok": 0, "skip": 0, "FAIL": 0}
    states = 0
    for seed in range(lo, hi):
        game = random_game(random.Random(seed), big)
        for bits in combos:
            status, detail = check(game, bits)
            totals[status] += 1
            if status == "ok":
                states += int(detail.split()[0])
            if status == "FAIL":
                print("FAIL seed=%d switches=%s: %s" % (seed, bits if isinstance(bits, dict) else dict(zip(SWITCHES, bits)), detail))
                print("     game=%r" % (game,))
                sys.stdout.flush()
    print("seeds %d..%d%s: %s, %d pruned states compared" % (lo, hi - 1, " big" if big else "", totals, states))


if __name__ == "__main__":
    main()
