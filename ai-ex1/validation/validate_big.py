import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Optimality check on larger random games (too large to enumerate completely).

Reference optimum: uniform-cost search over ALL legal actions of the reference model (validate.Ref), stopped at
the first goal. ex1 must return a legal plan of exactly that cost. Also checks h(start) <= optimum and, for
every state on ex1's returned path, h <= cost of the rest of the plan (the rest of an optimal plan is optimal).

usage: python validate_big.py <first seed> <count> [cap]
"""
import contextlib
import heapq
import io
import random
import sys
import time

import search
import ex1
import ex1_check
from validate import Ref, random_game, PROFILES

PROFILES["B"] = (12, 3, 4, 3)
PROFILES["C"] = (14, 3, 5, 4)


def ucs(ref, cap):
    start = ref.init
    best = {start: 0}
    heap = [(0, 0, start)]
    tick = 0
    done = set()
    while heap:
        d, _, s = heapq.heappop(heap)
        if s in done:
            continue
        done.add(s)
        if ref.is_goal(s):
            return d
        if len(done) > cap:
            return None
        for a, c, ns in ref.succ(s):
            nd = d + c
            if nd < best.get(ns, 1e18):
                best[ns] = nd
                tick += 1
                heapq.heappush(heap, (nd, tick, ns))
    return float("inf")


def main():
    seed0, count = int(sys.argv[1]), int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 250000
    profile = sys.argv[4] if len(sys.argv) > 4 else "B"
    stats = dict(ok=0, skip=0, unsolvable=0, FAIL=0, slow=0)
    worst_time = 0
    for seed in range(seed0, seed0 + count):
        game = random_game(random.Random(seed), profile)
        ref = Ref(game)
        # cheap filter: skip games ex1 itself declares disconnected (known crash, reported separately)
        opt = ucs(ref, cap)
        if opt is None:
            stats["skip"] += 1
            continue
        if opt == float("inf"):
            stats["unsolvable"] += 1
            continue
        fails = []
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                pr = ex1.create_logistics_problem(game)
            t0 = time.perf_counter()
            res = search.astar_search(pr, pr.h_astar)
            dt = time.perf_counter() - t0
            worst_time = max(worst_time, dt)
            if res is None:
                fails.append("no plan, optimum %d" % opt)
            else:
                node, expanded = res
                path = node.path()[::-1]
                plan = [str(x.action) for x in path][1:]
                world = ex1_check.World(game)
                for a in plan:
                    world.apply(a)
                if not world.solved():
                    fails.append("plan does not solve")
                elif world.cost != opt:
                    fails.append("cost %d, optimum %d" % (world.cost, opt))
                for x in path:
                    h = pr.h_astar(x)
                    if h > world.cost - x.path_cost:
                        fails.append("h=%d > remaining %d on the plan, state %r" % (h, world.cost - x.path_cost, x.state.s))
                        break
        except Exception:
            import traceback
            fails.append("crash: " + traceback.format_exc(limit=5))
        if fails:
            stats["FAIL"] += 1
            print("seed %d FAIL %s\n   game = %r" % (seed, "; ".join(fails), game), flush=True)
        else:
            stats["ok"] += 1
    print("DONE big %s seeds %d..%d cap %d: %r, slowest ex1 solve %.2f s" % (profile, seed0, seed0 + count - 1, cap, stats, worst_time), flush=True)


if __name__ == "__main__":
    main()
