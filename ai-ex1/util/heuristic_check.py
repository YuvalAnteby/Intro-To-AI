"""Focused heuristic regressions; run from the repository root."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import ex1
import ex1_check
import search


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
    check_exclusive_cargo()
    check_whole_sails()
    check_truck_endpoints()
    check_ferry_after_focused_drive()
    check_corridor_transfer()
    problem = ex1.LogisticsProblem(ex1_check.init_state_p2)
    assert search.astar_search(problem, problem.h_astar)[0].path_cost == 6
    print("heuristic regressions: PASS")
