import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Pruning and state merging, tested without the heuristic, against an independent exact solver.

For a small random game:
  C*  = the true optimum, from validate.Ref (all legal actions, rules written from the assignment text).
For a configuration of the OPT_* switches, the whole graph that ex1.successor generates from the start
(the "pruned graph") is enumerated on raw state tuples, and V(s) = cheapest cost from s to a goal inside that
graph is computed for every state by a backward shortest-path pass. Checks:

  P1. V(start) == C*                      at least one optimal plan survives the rules of this configuration
  P2. V is the same for all states that _State treats as equal (same _canon key)
                                          merging such states in the closed list loses nothing
  P3. every action is legal and has the effect the rules give (through Ref)

Configurations: all rules on, every rule alone, every rule left out, and the focus family in steps.

usage: python prune_check.py <first seed> <count> <profile> [cap]
"""
import contextlib, heapq, io, random, sys, time
from collections import deque
import ex1
from validate import Ref, random_game, to_world, INF

ALL = ["OPT_FOCUS", "OPT_TWINS", "OPT_FORCED", "OPT_ORDER", "OPT_COMP", "OPT_SYM", "OPT_DEAD", "OPT_UTURN",
       "OPT_FL", "OPT_FRESH", "OPT_BARREN"]
CONFIGS = {"all": set(ALL), "none": set()}
for name, on in [("only TWINS", ["OPT_TWINS"]), ("only FORCED", ["OPT_FORCED"]), ("only DEAD", ["OPT_DEAD"]),
                 ("only COMP", ["OPT_COMP"]), ("only SYM", ["OPT_SYM"]), ("only FOCUS(drive)", ["OPT_FOCUS"]),
                 ("FOCUS+FL", ["OPT_FOCUS", "OPT_FL"]), ("FOCUS+FL+ORDER", ["OPT_FOCUS", "OPT_FL", "OPT_ORDER"]),
                 ("FOCUS+UTURN", ["OPT_FOCUS", "OPT_UTURN"]), ("FOCUS+FRESH", ["OPT_FOCUS", "OPT_FRESH"]),
                 ("FOCUS+BARREN", ["OPT_FOCUS", "OPT_BARREN"]), ("TWINS+SYM", ["OPT_TWINS", "OPT_SYM"]),
                 ("FOCUS+FL+TWINS+SYM", ["OPT_FOCUS", "OPT_FL", "OPT_TWINS", "OPT_SYM"])]:
    CONFIGS[name] = set(on)
for k in ALL:
    CONFIGS["all but " + k[4:]] = set(ALL) - {k}


def analyse(game, ref, table, ids, states, cap):
    """Enumerate the pruned graph of the current switches. Returns (V(start), problems found)."""
    with contextlib.redirect_stdout(io.StringIO()):
        pr = ex1.create_logistics_problem(game)
    s0 = pr.initial.s
    idx = {s0: 0}
    order = [s0]
    rev = [[]]
    goal = []
    bad = []
    q = deque([0])
    T, F = pr.T, pr.F
    while q:
        i = q.popleft()
        s = order[i]
        if pr.goal_test(ex1._State(pr, s)):
            goal.append(i)
        w = to_world(pr, s)
        wi = ids.get(w)
        tab = table[wi] if wi is not None else None
        local = None
        for a, ns in pr._successors(s):
            # P3 legality / effect (positions of a finished independent part may be reset: compare packages)
            if tab is not None:
                j = tab.get(a)
                want = states[j] if j is not None else None
            else:
                if local is None:
                    local = {a_: ns_ for a_, c_, ns_ in ref.succ(w)}
                want = local.get(a)
            if want is None:
                bad.append("P3 illegal action %s in %r" % (a, s))
            else:
                got = to_world(pr, ns)
                if got != want and not (pr.multi and got[T + F:] == want[T + F:]):
                    bad.append("P3 wrong effect of %s in %r" % (a, s))
            k = idx.get(ns)
            if k is None:
                k = idx[ns] = len(order)
                if k >= cap:
                    return None, None
                order.append(ns)
                rev.append([])
                q.append(k)
            rev[k].append((i, 3 if a.startswith("SAIL") else 1))
    V = [INF] * len(order)
    heap = [(0, g) for g in goal]
    for g in goal:
        V[g] = 0
    while heap:
        d, i = heapq.heappop(heap)
        if d > V[i]:
            continue
        for j, c in rev[i]:
            if d + c < V[j]:
                V[j] = d + c
                heapq.heappush(heap, (d + c, j))
    if ex1.OPT_SYM:
        groups = {}
        for i, s in enumerate(order):
            key = pr._canon(s)
            v = groups.setdefault(key, V[i])
            if v != V[i]:
                bad.append("P2 merged states with different remaining cost %s / %s, e.g. %r" % (v, V[i], s))
                break
    return V[0], bad[:3]


def main():
    seed0, count, profile = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 60000
    done = {c: 0 for c in CONFIGS}
    fails = 0
    games = 0
    t0 = time.time()
    for seed in range(seed0, seed0 + count):
        game = random_game(random.Random(seed), profile)
        ref = Ref(game)
        r = ref.explore(cap)
        if r is None:
            continue
        ids, states, hs, table = r
        opt = hs[0]
        if opt == INF:
            continue
        games += 1
        for cname, on in CONFIGS.items():
            for k in ALL:
                setattr(ex1, k, k in on)
            try:
                v, bad = analyse(game, ref, table, ids, states, 4 * cap)
            except Exception:
                import traceback
                v, bad = "crash", [traceback.format_exc(limit=3)]
            if v is None:
                continue
            done[cname] += 1
            if v != opt:
                bad = ["P1 best plan in the pruned graph costs %s, optimum %s" % (v, opt)] + bad
            if bad:
                fails += 1
                print("seed %d profile %s config [%s] FAIL %s\n   game = %r" % (seed, profile, cname, "; ".join(bad), game), flush=True)
    for k in ALL:
        setattr(ex1, k, True)
    print("DONE prune %s seeds %d..%d: %d solvable games, %d failures, %d configurations, checks per configuration min %d, %.0f s"
          % (profile, seed0, seed0 + count - 1, games, fails, len(CONFIGS), min(done.values()), time.time() - t0), flush=True)


if __name__ == "__main__":
    main()
