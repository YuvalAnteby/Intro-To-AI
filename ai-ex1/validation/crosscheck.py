import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Games too large to enumerate: solve each with three configurations of ex1 and compare the plan costs.

  A  the submitted configuration
  B  same pruning, weaker heuristic (first-entry and merge terms off)
  C  same heuristic, every pruning rule off (all legal actions generated)

A legal plan of a lower cost found by B or C would prove A is not optimal (heuristic not admissible at this
size, or a pruning rule that cuts every optimal plan). Every plan is replayed with the official World.

usage: python crosscheck.py <first seed> <count> <profile> <seconds per solve> <total seconds>
"""
import contextlib, io, random, signal, sys, time
import search, ex1, ex1_check
from validate import random_game, PROFILES

PROFILES["G"] = (14, 4, 6, 4)
PROFILES["G2"] = (24, 4, 7, 5)
PRUNE = ["OPT_FOCUS", "OPT_TWINS", "OPT_FORCED", "OPT_ORDER", "OPT_COMP", "OPT_SYM", "OPT_DEAD", "OPT_UTURN",
         "OPT_FL", "OPT_FRESH", "OPT_BARREN"]


class Timeout(Exception):
    pass


def alarm(*_):
    raise Timeout()


def solve(game, config, limit):
    for k in PRUNE:
        setattr(ex1, k, config != "C")
    ex1.OPT_FIRST = config != "B"
    with contextlib.redirect_stdout(io.StringIO()):
        pr = ex1.create_logistics_problem(game)
    if config == "B":
        for r in pr.regions:
            r.merge_goals = set()
    signal.signal(signal.SIGALRM, alarm)
    signal.setitimer(signal.ITIMER_REAL, limit)
    try:
        res = search.astar_search(pr, pr.h_astar)
    except Timeout:
        return "timeout"
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    if res is None:
        return None
    node, _ = res
    w = ex1_check.World(game)
    for a in [str(x.action) for x in node.path()[::-1]][1:]:
        w.apply(a)          # raises on an illegal action
    assert w.solved()
    return w.cost


def main():
    seed0, count, profile, limit, budget = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], float(sys.argv[4]), float(sys.argv[5])
    t_end = time.time() + budget
    stats = dict(games=0, AB=0, AC=0, fail=0, A_timeout=0, unsolvable=0, maxcost=0)
    for seed in range(seed0, seed0 + count):
        if time.time() > t_end:
            break
        game = random_game(random.Random(seed), profile)
        try:
            a = solve(game, "A", limit)
            if a == "timeout":
                stats["A_timeout"] += 1
                continue
            stats["games"] += 1
            if a is None:
                stats["unsolvable"] += 1
            else:
                stats["maxcost"] = max(stats["maxcost"], a)
            for cfg in "BC":
                r = solve(game, cfg, limit)
                if r == "timeout":
                    continue
                stats["A" + cfg] += 1
                if r != a:
                    stats["fail"] += 1
                    print("seed %d FAIL: config A cost %r, config %s cost %r\n  game = %r" % (seed, a, cfg, r, game), flush=True)
        except Exception:
            import traceback
            stats["fail"] += 1
            print("seed %d CRASH %s\n  game = %r" % (seed, traceback.format_exc(limit=4), game), flush=True)
    print("DONE crosscheck %s from seed %d: %r" % (profile, seed0, stats), flush=True)


if __name__ == "__main__":
    main()
