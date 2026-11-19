import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Edge-case inputs: does ex1 crash, and is the answer right? (reference = validate.check_game)"""
import traceback
import unittest
import ex1
from ex1_check import IllegalAction, World
from validate import check_game
G = {
 "no packages": {"Locations": 3, "Roads": {(0,1),(1,2)}, "Ports": set(), "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {}},
 "all delivered already": {"Locations": 3, "Roads": {(0,1),(1,2)}, "Ports": set(), "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(2,3,2)}},
 "single location": {"Locations": 1, "Roads": set(), "Ports": set(), "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(0,3,0)}},
 "no trucks, delivered": {"Locations": 2, "Roads": {(0,1)}, "Ports": set(), "Trucks": {}, "Ferries": {}, "Packages": {30:(1,3,1)}},
 "no trucks, undelivered": {"Locations": 2, "Roads": {(0,1)}, "Ports": set(), "Trucks": {}, "Ferries": {}, "Packages": {30:(0,3,1)}},
 "too heavy package": {"Locations": 2, "Roads": {(0,1)}, "Ports": set(), "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(0,6,1)}},
 "road listed both ways": {"Locations": 3, "Roads": {(0,1),(1,0),(1,2)}, "Ports": set(), "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(0,3,2)}},
 "port without ferry": {"Locations": 3, "Roads": {(0,1),(1,2)}, "Ports": {0,2}, "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(0,3,2)}},
 "ferry docked outside its ports": {"Locations": 4, "Roads": {(0,1),(2,3)}, "Ports": {0,1,2}, "Trucks": {10:(0,5)}, "Ferries": {20:(0,(1,2),1)}, "Packages": {30:(0,3,3)}},
 "ferry ports as a set": {"Locations": 4, "Roads": {(0,1),(2,3)}, "Ports": {1,2}, "Trucks": {10:(0,5)}, "Ferries": {20:(1,{1,2},1)}, "Packages": {30:(0,3,3)}},
 "ferry ports as a list": {"Locations": 4, "Roads": {(0,1),(2,3)}, "Ports": {1,2}, "Trucks": {10:(0,5)}, "Ferries": {20:(1,[1,2],1)}, "Packages": {30:(0,3,3)}},
 "ferry of size 0": {"Locations": 4, "Roads": {(0,1),(2,3)}, "Ports": {1,2}, "Trucks": {10:(0,5)}, "Ferries": {20:(1,(1,2),0)}, "Packages": {30:(0,3,1)}},
 "ferry with one port": {"Locations": 3, "Roads": {(0,1),(1,2)}, "Ports": {1}, "Trucks": {10:(0,5)}, "Ferries": {20:(1,(1,),1)}, "Packages": {30:(0,3,2)}},
 "isolated start (unsolvable)": {"Locations": 3, "Roads": {(0,1)}, "Ports": set(), "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(2,3,0)}},
 "truck in another part, unused": {"Locations": 4, "Roads": {(0,1)}, "Ports": set(), "Trucks": {10:(0,5), 11:(3,5)}, "Ferries": {}, "Packages": {30:(0,3,1)}},
 "roads as lists": {"Locations": 3, "Roads": [[0,1],[1,2]], "Ports": [], "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(0,3,2)}},
 "zero weight package": {"Locations": 3, "Roads": {(0,1),(1,2)}, "Ports": set(), "Trucks": {10:(0,5)}, "Ferries": {}, "Packages": {30:(0,0,2), 31:(1,5,2)}},
 "two weightless packages on cycle": {"Locations": 3, "Roads": {(0,1),(1,2),(2,0)}, "Ports": set(), "Trucks": {10:(0,1)}, "Ferries": {}, "Packages": {30:(2,5,2), 31:(0,0,1), 32:(0,0,1)}},
}
for name, g in G.items():
    try:
        st, d = check_game(g)
        print("%-34s %s %s" % (name, st[:200], d if not st.startswith("FAIL") else ""))
    except Exception:
        print("%-34s CRASH %s" % (name, traceback.format_exc().strip().splitlines()[-1]))

try:
    import numpy as np
except ImportError:
    np = None


class NumericCapacityTests(unittest.TestCase):
    def test_integer_loads(self):
        capacities = [2048] if np is None else [2048, np.float16(2048)]
        for capacity in capacities:
            with self.subTest(capacity=capacity):
                game = {"Locations": 2, "Roads": {(0, 1)}, "Ports": set(), "Ferries": {},
                        "Trucks": {10: (0, capacity)}, "Packages": {30: (0, 1024, 1), 31: (0, 1025, 1)}}
                status, detail = check_game(game)
                self.assertEqual(status, "ok")
                # In some NumPy versions the comparison rounds the int load to 2048.
                self.assertEqual(detail[2], 5 if 2049 <= capacity else 7)

    @unittest.skipIf(np is None, "NumPy unavailable")
    def test_mixed_truck_capacities(self):
        weight, capacity = 1 + 2**-25, np.float32(1)
        game = {"Locations": 2, "Roads": {(0, 1)}, "Ports": set(), "Ferries": {},
                "Trucks": {10: (0, 1.0), 11: (0, capacity)}, "Packages": {30: (0, weight, 1)}}
        status, detail = check_game(game)
        self.assertEqual(status, "ok" if weight <= capacity else "unsolvable-ok")
        if status == "ok":
            self.assertEqual(detail[2], 3)

    @unittest.skipIf(np is None, "NumPy unavailable")
    def test_ferry_boarding(self):
        # Construct the frontier directly so thousands of trucks need just one successor call.
        for capacity, occupied, pending in [(2052, 2050, False), (2052, 2051, False), (0, 0, True)]:
            with self.subTest(capacity=capacity, occupied=occupied, pending=pending):
                game = {"Locations": 2, "Roads": set(), "Ports": {0, 1},
                        "Ferries": {20: (int(pending), (0, 1), np.float16(capacity))},
                        "Trucks": {100 + t: (0, 1) for t in range(occupied + 1)}, "Packages": {30: (0, 1, 1)}}
                problem = ex1.create_logistics_problem(game)
                world = World(game)
                state = list(problem.initial.s)
                if pending:
                    world.apply("SAIL{20,1,0}")
                    state[0], state[problem.IF] = problem.FE0, 0
                for t in range(occupied):
                    world.apply("BOARD{%d,20}" % (100 + t))
                    state[1 + t] = problem.n    # just boarded ferry zero
                action = "BOARD{%d,20}" % (100 + occupied)
                try:
                    world.apply(action)
                    legal = True
                except IllegalAction:
                    legal = False
                choices = dict(problem.successor(ex1._State(problem, tuple(state))))
                self.assertEqual(action in choices, legal)


if __name__ == "__main__":
    unittest.main()
