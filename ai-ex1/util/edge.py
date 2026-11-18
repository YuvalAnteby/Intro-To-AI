import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Edge-case inputs: does ex1 crash, and is the answer right? (reference = validate.check_game)"""
import traceback
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
