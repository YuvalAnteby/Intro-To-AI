# Assignment 1 (Trucks, Packages, Ferries): handoff notes

Written for whoever continues this work (a Claude Code session, or Yuval reading the code).
It records what the current `ex1.py` does, why each part is believed correct, what was measured,
what was tried and dropped, and what is still open.

## 1. Status

All 18 provided problems return an optimal plan through the official `ex1_check.py`
(limit 30 s each). Times below are from a 2-core cloud container and vary by about 20% between runs.
The grading machine is unknown, so treat the three slow ones as marginal.

| problem | time | expanded | | problem | time | expanded |
|---|---|---|---|---|---|---|
| p2 | 0.00 s | 15 | | y1 | 0.1 s | 1,506 |
| p1 | 0.01 s | 81 | | y2 | 3.4 s | 26,792 |
| p3 | 0.01 s | 78 | | **y3** | **16-19 s** | 88,162 |
| x1 | 0.5 s | 9,527 | | **y4** | **20 s** | 135,624 |
| x2 | 0.4 s | 3,289 | | y5 | 2.0 s | 25,021 |
| x3 | 0.04 s | 439 | | y6 | 2.7 s | 15,177 |
| x4 | 0.03 s | 148 | | **y7** | **18 s** | 136,714 |
| x5 | 0.02 s | 542 | | | | |
| x6 | 0.15 s | 1,474 | | | | |
| x7 | 0.05 s | 341 | | | | |
| x8 | 0.01 s | 157 | | | | |

For comparison, the first working version (plain successor, distance heuristic) solved 10 of 18.

## 2. Things you must do before submitting

1. Put your ID in `id = [...]` at the top of `ex1.py`.
2. Add the comment the course asks for about which LLMs were used and how.
3. Run `python ex1_check.py` on your own machine and look at the y3, y4, y7 times.
4. Read section 7 (risks). Two design decisions there are yours to make.

## 3. Files

Submitted: `ex1.py` only.

Local tools (not submitted):

| file | purpose |
|---|---|
| `validate.py` | The important one. Random small problems, exhaustive solution, checks plan optimality and h <= h* on every reachable state. |
| `bench.py` | All problems through the official checker, with expansions. |
| `run.py` | Same but in-process, with switches: `python run.py y4 y7 --set=OPT_TWINS=0`. |
| `prof.py` | cProfile of one problem. |
| `trace.py` | Optimal path with g, h, f per step. Shows where h is loose (f jumps). |
| `fhist.py` | Expansions per f layer. |
| `waste.py` | Which action types raise f on the paths to expanded nodes. |
| `hlab.py` | Slow, readable reference version of the cut heuristic. `validate.py --diff` compares it to the fast one. |
| `lab.py`, `gaps.py` | Older experiment drivers built around `hlab.py`. May need small fixes to run. |

## 4. State representation

A state is a `_State` object wrapping a flat tuple `s`:

```
s = (focus, truck_0..truck_T-1, ferry_0..ferry_F-1, package_0..package_P-1)
truck:   location l            standing at l
         n + 2f                aboard ferry f, boarded at the current port (may not disembark yet)
         n + 2f + 1            aboard ferry f, has sailed (may disembark)
ferry:   the port where it is docked
package: location l, or n + t  (inside truck t)
focus:   0, or a code meaning "truck t has just driven here from u" / "truck t has just loaded p"
```

Objects are indexed in sorted ID order. Everything static (roads, capacities, goals) lives on the problem.

`_State.__eq__/__hash__` compare a canonical key (`_canon`), so two states that differ only by renaming
interchangeable objects (same-capacity trucks, same-line ferries, same weight and goal packages) are one
state in `closed`. Each node still carries its own real tuple, so the action strings stay legal.

The heuristic ignores `focus` and the "boarded here" bit. It is a function of the world state only.

## 5. Successor pruning

Every rule has a switch `OPT_*` at the top of `ex1.py` so it can be turned off for testing.
"Effect" is roughly what turning the rule off costs on the hard problems.

| rule | switch | argument | effect |
|---|---|---|---|
| Never load a package lying at its goal | always | loading and unloading it again only adds cost | |
| A truck standing at the goal of a package it carries must unload it now | `OPT_FORCED` | any plan can be rewritten to unload here, it frees capacity and removes actions | ~10% |
| Twins: of identical objects in an identical situation only the lowest index acts | `OPT_TWINS` | renaming symmetry | mixed, big on y3 |
| Unload before load at a stop | `OPT_ORDER` | reorder within a stop | mixed |
| Focus: after DRIVE or LOAD of truck t the next action is again by t | `OPT_FOCUS`, `OPT_FL` | a DRIVE or LOAD of t commutes with later actions of other objects until t's next action, so it can be delayed to just before it | large (2-3x) |
| No immediate U-turn | `OPT_UTURN` | drive a-b then b-a with nothing in between is a no-op | ~30% |
| No BOARD then DISEMBARK without a SAIL | `OPT_FRESH` | no-op | ~10-20% |
| Empty truck does not cross a bridge to a side with no lying package and no docked ferry | `OPT_BARREN` | with focus, an empty truck drives uninterrupted until it loads or boards, and there it can do neither | helps y4 with the next rule, slightly hurts y3 |
| Dead ends: never enter a side of a bridge where no package starts or ends and no truck starts | `OPT_DEAD` | anything done inside can be done at the entrance for less | made y2 solvable (timeout to 3 s) |
| Dominated ports: never sail to an empty island if another port is served by all the same ferries | `OPT_DEAD` (`_dominated_ports`) | substitute that port for the island in every action | y4: 190k to 135k expansions |
| Symmetric states merged | `OPT_SYM` | see section 4 | y6: 5x, others mixed |
| Independent map components solved one after the other | `OPT_COMP` | actions in different components commute | y1: 100x |

About `OPT_COMP`: when the active component is finished, `_finish` resets its trucks and ferries in the
tuple to their initial positions. They never act again, so the plan stays legal, and it lets states merge.
See risk 7.3.

### Tried and removed

* **Focus on ferries** (after SAIL or BOARD the next action involving that ferry comes immediately, with
  a "dangling ferry" bit). Correct in testing, but it split states and made things slower
  (y7: 228k expansions with it, 137k without). Removed from the code.
* **Blocking a truck after UNLOAD / DISEMBARK** until something happens at its place. Same story.
* **Loading in increasing package index.** Removed when symmetric merging was added.

General lesson: any rule that adds bookkeeping bits to the state must prune more than it splits.
Measure with `run.py --set=...` before keeping one.

## 6. The heuristic

`h = (LOAD/UNLOAD still needed) + (movement bound per map component)`.

**Loads and unloads.** A lying, undelivered package needs 1 LOAD + 1 UNLOAD. A package in a truck needs
1 UNLOAD. These are disjoint from movement actions, so the two parts add.

**Movement.** Built on an auxiliary graph: a node per location and per ferry, a road edge per road, a
"port edge" (port, ferry) per served port. Class `_Region` handles one connected component.

1. **Road bridges.** Each bridge of the auxiliary graph is a cut. All transport between the two sides
   crosses it, and each DRIVE crosses exactly one road, so bounds for different bridges add.
   `g(v, a, b)` is the least number of crossings given the weight that must go each way, the number of
   "big" packages each way (heavier than half the largest truck, so no two share a truck), and the
   capacities of the trucks on each side. A truck already inside can leave once without first entering.
   This is what makes x8 exact (h0 = 44 = optimum).
2. **Port bridges** (a ferry line with no alternative). `port_cost` bounds BOARD + DISEMBARK + SAIL at
   the port, including return sails forced by ferry capacity and by where the ferry is docked now.
   A SAIL is split into a departure and an arrival of 1.5 each so both end ports can claim their half.
3. **Pieces.** Inside a 2-edge-connected part, a group of road-connected locations and everything
   hanging on it can only be left through its non-bridge port edges. Same `port_cost`.
4. **Fractions.** For what bridges do not cover (cycles of roads, rings of ferries): a truck of capacity
   C moving weight w pays at least w/C of every action on the package's way, and a ferry for k trucks
   shares a SAIL between k. Precomputed weighted distances `wd_road`, `wd_all`. Edges already counted
   by bridges cost 0 here, so nothing is counted twice. Combined with pieces by
   `max(pieces + road fractions, all fractions)`. Essential for x5 and y5.
5. **Merge bound** (`merge`). Packages with the same goal that are now in different places share the
   last stretch of their way (the chain). If y trucks cross the chain, the other K - y groups must be
   merged into them: 2 extra actions per package (UNLOAD + LOAD), or, for a lying group, a detour of
   the collecting truck over that group's private bridges. Take the cheapest y. Each bridge is used for
   one goal only. Made x4 exact and x6 20x faster.
6. **First entry** (`OPT_FIRST`). A side of a road bridge that needs transport and has no truck: the
   first truck to enter it arrives before any LOAD inside such sides, so it brings nothing destined
   there (sides that receive from outside are excluded), which is one crossing on top of what is needed
   once a truck is inside. Helps y3 by about 25%.

Values are cached twice: by raw state, and by a normalized key that drops the bookkeeping bits.
Sub-results (`g`, `port_cost`, merge per goal) are memoized.

h is not consistent. That is fine here: `graph_search` reopens a state reached with a lower g.

## 7. Risks and open items

### 7.1 Admissibility evidence (read this one)

The penalty for an inadmissible heuristic is 30 points, more than all three slow problems together.
What supports admissibility:

* `validate.py` builds the whole reachable state graph of a random small problem, computes exact h*
  for every state, and checks h <= h* everywhere, plus that A* returns a legal plan of optimal cost.
* It did catch a real bug during development (merge bound added to the wrong term), and later a second
  one (a shortcut for untouched components). Both fixed. So the test has teeth.
* Runs with no violation: 3,000 seeds on the cut + merge heuristic, then several runs of 300 to 1,500
  seeds on later versions. See `val_*.log`. About one third of seeds are unsolvable and skipped.

What it does not cover:

* Random problems are small: at most 7 locations, 3 trucks, 4 packages, 3 ferries. Bugs that need a
  larger structure would not show.
* Parts 5 and 6 above (merge, first entry) have the least rigorous arguments. They are sketched in the
  code comments, not proven line by line. Part 6 is not in the `hlab.py` reference at all.
* On the 18 real problems the only check is that the returned cost equals the known optimum. That
  proves the plan, not that h is admissible on every state.

If you want maximum safety for the hidden admissibility check, set `OPT_FIRST = False` and clear
`merge_goals`. Cost measured earlier: x4 and x6 get slower but still pass, y3 and y4 get roughly
25-60% slower and may cross 30 s.

### 7.2 Time margin

y3, y4, y7 take 16-20 s here. Python speed differs between machines by more than that margin.
About half the time is the heuristic, a quarter is successor generation, the rest is the framework.
The hidden set is scored by speed groups (under 5 s is likely the top group).

Ideas not yet tried, in order of expected value:

1. y7: `waste.py` shows most wasted work is f rising on DRIVE (+1, +2) and UNLOAD (+2). The bound
   around the two-truck ferry and the hub island is loose by 7 at the start (h0 = 53, optimum 60).
2. y4: h0 = 59 vs 71. The gap is the hub: three trucks share one port, and ferry return sails are
   under-counted when a ferry serves 5 ports.
3. y3: long chains (15 roads). Almost all the search is in the last three f layers.
4. Micro-optimisation of `move` and `_truck_standing` (they are the top two in the profile).

### 7.3 Things an AI code reviewer might question

* **Symmetric state equality** (`_State`). The assignment allows hashable classes with `__eq__` and
  `__hash__`, and this is a standard technique, but it means two different world states compare equal.
* **`_finish`** rewrites finished trucks back to their start positions in the tuple. The plan is
  unaffected, but the state then does not describe where those trucks really are. If you prefer strict
  states, set `OPT_COMP = False` and check y1 (it relied on this: 0.1 s with, about 12 s without in an
  older version).
* **Precomputation.** The constructor only computes things on the map (bridges, components, weighted
  distances). It never searches the state space. The distance computation is a plain relaxation loop,
  with no priority queue, to stay clearly inside "you may not write your own priority queue or search".

### 7.4 Smaller notes

* `import utils` is unused but came with the starter file.
* `create_logistics_problem` still has the starter's `print`.
* The file is about 1,500 lines. Most of it is the heuristic.

## 8. How to verify after any change

```
python validate.py 0 300            # plan optimality + h <= h* on random problems (about 1 minute)
python validate.py 0 300 --diff     # also: fast heuristic == reference (OPT_FIRST off in this mode)
python validate.py 90000 300 --big  # slightly larger random problems
python bench.py                     # all 18 through the official checker
```

Use a fresh seed range each time (first argument). A `FAIL` line prints the seed and the game dict,
and `random_game(random.Random(seed))` reproduces it.

## 9. Changes on 2026-11-13 (after an audit for hidden-test robustness)

Sections 1 to 8 describe the version before this date. What changed in `ex1.py`:

* `_crossings` (section 6, part 1) now computes the exact minimum in closed form. The old version stopped
  searching at 200 crossings and then returned a much smaller number. Results are identical on every input
  the old version handled, so the 18 problems expand the same number of states.
* A ferry that starts at a port it does not serve is handled (`gports`). Before, `h` could overestimate there.
* No division by zero for a ferry of capacity 0 or trucks of capacity 0.
* No crash when a package cannot reach its goal. The search returns no plan.
* `_port_cost` no longer enumerates subsets when more than 10 loaded trucks are aboard docked ferries.

New files: `ADMISSIBILITY_PROOF.md` (proof for the heuristic, revision 3) and `validation/` (the test tools,
see its README). The tool names in section 3 refer to an earlier session and are not in this folder.
Risk 7.1 is now covered by the proof and by `validation/`. Risk 7.2 (time on y3, y4, y7) is unchanged.
