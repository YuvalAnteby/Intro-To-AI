"""Focused heuristic regressions; run from the repository root."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import ex1
import ex1_check
import search
from util.validate import INF, Ref, from_world


def check_numeric_weights(capacity, weights, optimum, *, cycle=False):
    roads = {(i, (i + 1) % 6) for i in range(6)} if cycle else {(0, 1)}
    game = {
        "Locations": 6 if cycle else 2, "Roads": roads, "Ports": set(),
        "Trucks": {10: (0, capacity)}, "Ferries": {}, "Packages": weights,
    }
    problem = ex1.LogisticsProblem(game)
    h = problem.h_astar(search.Node(problem.initial))
    assert type(h) is int and 0 <= h <= optimum, (h, optimum)
    node, _ = search.astar_search(problem, problem.h_astar)
    world = ex1_check.World(game)
    for step in node.path()[::-1][1:]:
        world.apply(step.action)
    assert world.solved() and world.cost == node.path_cost == optimum
    assert problem.h_astar(node) == 0


def check_fractional_cargo():
    check_numeric_weights(1.3, {30: (0, 1, 3)}, 5, cycle=True)
    check_numeric_weights(1, {30: (0, 0.5, 1)}, 3)
    # The simulator rejects 0.1 + 0.2 at 0.3, but accepts 0.4 + 0.1 at 0.5.
    check_numeric_weights(0.3, {30: (0, 0.1, 1), 31: (0, 0.2, 1)}, 7)
    check_numeric_weights(0.5, {31: (0, 0.4, 1), 30: (0, 0.1, 1)}, 5)
    # A package already at its goal can be needed as ballast under the simulator rules.
    check_numeric_weights(1, {30: (1, 4, 0), 31: (0, -3, 0)}, 6)


def check_load_summation_order():
    large = 2**53
    game = {
        "Locations": 2, "Roads": {(0, 1)}, "Ports": set(), "Ferries": {},
        "Trucks": {10: (0, large + 2)},
        "Packages": {30: (0, large, 1), 31: (0, 1, 1), 33: (0, 0.0, 1),
                     32: (0, 1, 1), 34: (0, 2, 1)},
    }
    problem = ex1.LogisticsProblem(game)
    state = problem.initial
    world = ex1_check.World(game)
    ref = Ref(game)
    raw = ref.init
    # Sorting IDs before summing would reject the last LOAD accepted by the simulator.
    for pid in game["Packages"]:
        action = "LOAD{%d,10}" % pid
        world.apply(action)
        state = dict(problem.successor(state))[action]
        raw = {name: child for name, _, child in ref.succ(raw)}[action]


def check_arbitrary_layouts():
    game = {
        "Locations": 3, "Roads": {(0, 1)}, "Ports": set(), "Ferries": {},
        "Trucks": {10: (0, 1), 11: (2, 2)}, "Packages": {30: (0, 1, 1), 31: (0, 1, 1)},
    }
    ferry_game = {
        "Locations": 4, "Roads": {(0, 1), (1, 2), (2, 3)}, "Ports": {0, 2, 3},
        "Trucks": {10: (0, 1)}, "Ferries": {20: (2, (2, 3), 1)}, "Packages": {30: (0, 1, 3)},
    }
    for instance, world, expected in [
        (game, (0, 0, 0, 0), 5),       # Both packages fit the truck now at 0.
        (game, (0, 2, 2, 0), INF),     # One package is stranded.
        (ferry_game, (4, 0, 4), 5),    # Loaded truck aboard at a different initial dock.
    ]:
        problem = ex1.LogisticsProblem(instance)
        ref = Ref(instance)
        ref.init = world
        _, _, distances, _ = ref.explore()
        assert distances[0] == expected
        node = search.Node(ex1._State(problem, from_world(problem, world)))
        h = problem.h_astar(node)
        assert type(h) is int and 0 <= h <= expected, (world, h, expected)


def check_exclusive_cargo():
    game = {
        "Locations": 6,
        "Roads": {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)},
        "Ports": set(),
        "Trucks": {10: (0, 4)},
        "Ferries": {},
        "Packages": {30: (0, 3, 2), 31: (3, 3, 5)},
    }
    problem = ex1.LogisticsProblem(game)
    h = problem.h_astar(search.Node(problem.initial))
    # Each package needs two drives alone, plus its own load and unload.
    assert h >= 8, h
    result = search.astar_search(problem, problem.h_astar)
    assert result[0].path_cost == 9, result[0].path_cost


def check_whole_sails():
    game = {
        "Locations": 3, "Roads": set(), "Ports": {0, 1, 2},
        "Trucks": {10: (0, 1), 11: (0, 1)},
        "Ferries": {20: (0, (0, 1, 2), 2)},
        "Packages": {30: (0, 1, 1), 31: (0, 1, 2)},
    }
    problem = ex1.LogisticsProblem(game)
    assert problem.h_astar(search.Node(problem.initial)) == 14
    assert search.astar_search(problem, problem.h_astar)[0].path_cost == 14


def check_unserved_start_symmetry():
    game = {
        "Locations": 4, "Roads": set(), "Ports": {0, 1, 2, 3},
        "Trucks": {10: (2, 1)}, "Packages": {30: (2, 1, 3)},
        "Ferries": {20: (0, (2, 3), 1), 21: (1, (2, 3), 1)},
    }
    problem = ex1.LogisticsProblem(game)
    # After both ferries leave their different initial docks, their static graph edges still differ.
    a = (0, 2, 2, 3, 2)
    b = (0, 2, 3, 2, 2)
    assert problem._canon(a) != problem._canon(b)
    assert search.astar_search(problem, problem.h_astar)[0].path_cost == 10


def check_truck_endpoints():
    game = {
        "Locations": 4, "Roads": {(0, 1), (0, 2), (0, 3)}, "Ports": set(),
        "Trucks": {10: (0, 3)}, "Ferries": {},
        "Packages": {30: (0, 1, 1), 31: (0, 1, 2), 32: (0, 1, 3)},
    }
    problem = ex1.LogisticsProblem(game)
    assert problem.h_astar(search.Node(problem.initial)) == 11
    assert search.astar_search(problem, problem.h_astar)[0].path_cost == 11


def check_ferry_after_focused_drive():
    game = {
        "Locations": 3, "Roads": {(0, 1)}, "Ports": {1, 2},
        "Trucks": {10: (0, 1)}, "Ferries": {20: (2, (1, 2), 1)},
        "Packages": {30: (0, 1, 2)},
    }
    problem = ex1.LogisticsProblem(game)
    assert not any(a.startswith("SAIL") for a, _ in problem.successor(problem.initial))
    node, _ = search.astar_search(problem, problem.h_astar)
    assert node.path_cost == 11
    world = ex1_check.World(game)
    for step in node.path()[::-1][1:]:
        world.apply(step.action)
    assert world.solved()


def check_corridor_transfer():
    game = {
        "Locations": 3, "Roads": {(0, 1), (1, 2)}, "Ports": set(),
        "Trucks": {10: (0, 1), 11: (2, 1)}, "Ferries": {},
        "Packages": {30: (0, 1, 2), 31: (2, 1, 0)},
    }
    problem = ex1.LogisticsProblem(game)
    loaded = dict(problem.successor(problem.initial))["LOAD{30,10}"]
    middle = dict(problem.successor(loaded))["DRIVE{10,0,1}"]
    assert not any(a.startswith("UNLOAD") for a, _ in problem.successor(middle))
    assert search.astar_search(problem, problem.h_astar)[0].path_cost == 8


if __name__ == "__main__":
    check_fractional_cargo()
    check_load_summation_order()
    check_arbitrary_layouts()
    check_exclusive_cargo()
    check_whole_sails()
    check_unserved_start_symmetry()
    check_truck_endpoints()
    check_ferry_after_focused_drive()
    check_corridor_transfer()
    problem = ex1.LogisticsProblem(ex1_check.init_state_p2)
    assert search.astar_search(problem, problem.h_astar)[0].path_cost == 6
    print("heuristic regressions: PASS")
