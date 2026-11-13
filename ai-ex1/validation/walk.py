import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Admissibility probe on the REAL problems (too large for exact h*).

Take states s that ex1's own successor function reaches (random walks from the start, plus the states on the
optimal plan), and solve from s with the same A*. The plan found from s is a real, legal plan (it is replayed
with the official ex1_check.World after the walk prefix), so its cost is an upper bound on h*(s).
If h_astar(s) > that cost, h is provably not admissible at s.

usage: python walk.py <problem> <walks> <max walk length> <seconds budget> [seed]
"""
import contextlib
import io
import random
import sys
import time

import search
import ex1
import ex1_check


def find(name):
    for S in ex1_check.SETS.values():
        if name in S:
            return S[name]
    raise KeyError(name)


def make(game):
    with contextlib.redirect_stdout(io.StringIO()):
        return ex1.create_logistics_problem(game)


def solve_from(game, state):
    pr = make(game)
    pr.initial = ex1._State(pr, state.s)
    res = search.astar_search(pr, pr.h_astar)
    if res is None:
        return None
    node, _ = res
    return [str(x.action) for x in node.path()[::-1]][1:]


def main():
    name, walks, maxlen, budget = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
    game, opt = find(name)
    pr = make(game)
    t_end = time.time() + budget
    probes = []         # (prefix actions, state)
    # states on the optimal plan
    res = search.astar_search(make(game), pr.h_astar)
    node, _ = res
    path = node.path()[::-1]
    acts = [str(x.action) for x in path][1:]
    bad = 0
    for i, x in enumerate(path):
        h = pr.h_astar(x)
        if h > node.path_cost - x.path_cost:
            bad += 1
            print("%s VIOLATION on the optimal plan at step %d: h=%d, remaining cost %d" % (name, i, h, node.path_cost - x.path_cost))
    # random walks through ex1.successor
    for w in range(walks):
        st = pr.initial
        prefix = []
        length = rng.randint(1, maxlen)
        for _ in range(length):
            succ = pr.successor(st)
            if not succ:
                break
            a, st = rng.choice(succ)
            prefix.append(a)
        probes.append((prefix, st))
    checked = 0
    dead = 0
    worst_slack = None
    for prefix, st in probes:
        if time.time() > t_end:
            break
        h = pr.h_astar(search.Node(st))
        plan = solve_from(game, st)
        if plan is None:
            dead += 1       # a dead end of the pruned space (e.g. an empty truck that drove nowhere): nothing to compare
            continue
        world = ex1_check.World(game)
        for a in prefix:
            world.apply(a)
        c0 = world.cost
        for a in plan:
            world.apply(a)
        assert world.solved()
        cost = world.cost - c0
        checked += 1
        slack = cost - h
        if worst_slack is None or slack < worst_slack:
            worst_slack = slack
        if h > cost:
            bad += 1
            print("%s VIOLATION: h=%d but a legal plan of cost %d exists from state %r (after %d random actions)"
                  % (name, h, cost, st.s, len(prefix)))
    print("%s: optimum %s, plan states ok, %d/%d random states probed, %d pruned dead ends, violations %d, smallest (plan cost - h) = %s"
          % (name, opt, checked, len(probes), dead, bad, worst_slack), flush=True)


if __name__ == "__main__":
    main()
