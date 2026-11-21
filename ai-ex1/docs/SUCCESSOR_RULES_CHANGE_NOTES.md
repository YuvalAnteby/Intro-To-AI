# Successor rules A to D: delivered change and notes

Proof: `SUCCESSOR_RULES_PROOF.md`. This file records what changed, the points worth remembering, and the
implementation evidence. Evidence here is about the code, not a replacement for the proof.

## What changed in `ex1.py`

| Switch (default) | Rule | Where |
|---|---|---|
| `OPT_EMPTY_SAIL = True` | A. A ferry with nobody aboard sails only to a port where a truck that is not useless stands | ferry loop of `_successors` |
| `OPT_EFFCAP = True` | B. Truck classes by effective capacity (largest reachable load), ferry classes by usable truck slots | `_setup_rules` |
| `OPT_USELESS = True` | C. An empty standing truck that cannot carry any undelivered package of its component never acts | truck loop of `_successors` |
| `OPT_TOWARD = True` | D. An empty standing truck drives only along a shortest road path to a target | `_truck_standing`, `_target_mask` |

Changed or added methods: `LogisticsProblem.__init__` (one call to `_setup_rules` and a guard on `_por`),
`_setup_rules` (new), `_successors`, `_truck_standing`, `_target_mask` (new). An AST comparison with the
previous file shows `_Region`, `_Stubborn`, `_State`, `h_astar`, `_h`, `_bound`, `path_cost`, `goal_test`,
`successor`, the three canonicalization methods, `_sail`, `_finish`, `_build_regions`, `_build_fractions` and
`_fraction_table` unchanged. The AI-use header at the top of `ex1.py` now describes this work.

## Points to remember

1. **Same standard as before, in this configuration only.** All four rules meet the per-retained-state standard:
   from every state the search can generate, the pruned graph still reaches the goal as cheaply as the
   unrestricted world. They read only the current state, never the path to it. This holds with `OPT_HISTORY`,
   `OPT_CORRIDOR`, `OPT_BARREN` and `OPT_PARTIAL_ORDER` all off (proof, scope paragraph). The condition-(1)
   version turns history and corridor rules on, and then only `HISTORY_RULES_PROOF.md` applies.
2. **Rule D needs target kind T3** (ports that a currently empty ferry can sail to). Without it, Rules A and D
   together lose the solution even from the initial state. Proof §3.1 gives a three-location example, and the
   checker reproduces it (pruned ∞ against a world optimum of 17). Do not "simplify" T3 away.
3. **Partial-order pruning is ignored while any new rule is on.** Its proof assumes the old raw successor list.
   With all four new switches off (and, in the condition-(1) file, every history rule, H3 and the corridor rule
   off too), `OPT_PARTIAL_ORDER` behaves as before.
4. **Huge integers (revision 3).** Rule B used to shift a bitset by a package weight and mask it to the capacity,
   so a weight like 2^80 raised `OverflowError` in the constructor (found in Astra's recheck). `_best_load` now
   drops weights above the capacity, uses the bitset only for capacities up to 2^20, and otherwise keeps the subset
   sums in a set. If that set would pass 2^16 elements, Rule B is switched off for the instance. Proof: Lemma 7′.
   Checked against brute force on 3,000 random weight lists, and by multiplying every weight and capacity of 25
   instances by 10^7, which must not change the optimal cost (it does not). On those 25 the classes also scaled
   exactly, but that is not guaranteed in general: a scaled instance can pass the sparse limit and fall back to
   raw classes. Example (Astra): weights 2, 4, ..., 2^17 and capacities 2^17 and 2^17 + 1 in one component give
   both trucks c̄ = 2^17, and the same numbers times 16 reach 2^16 + 1 sums, so Rule B is off there. The fallback
   only merges fewer states, so optimality is kept either way.
5. **Integer cargo only.** The rules switch on only when weights and capacities are integers (`integer_cargo`),
   the same gate the existing exact-weight reductions use. Otherwise the old successor function runs unchanged.
6. **What Rule D's precomputation is.** One BFS per location on the road map (directed by the dead-direction
   restriction), done in the constructor. The assignment allows precomputing "distances on the road network".
   No state is searched outside the provided A*.
7. **Effective capacity is used for classes only.** Legality checks still use the real capacities, and the
   heuristic still uses the real capacities. Using effective capacities inside the heuristic would also be
   admissible and tighter (its proof only uses capacity as an upper bound on load), but that is a heuristic
   change and was left out on purpose.
8. **No speed-up is promised.** See the measurements below. Rules B and C may never fire on a given instance.
9. **Still open from the earlier discussion.** The biggest lever is not in this change. If the course staff
   confirm that pruning only needs one optimal plan from the initial state to survive (with any history kept in
   the state), the history-based rules (focus, U-turn, corridor, lazy sail with a pending ferry) become usable
   again. The TA's own "safe" canonical-order example already fails the strict per-state reading.

## Implementation evidence

`tools/validate_rules.py` has its own world model written from the assignment text (no code shared with
`ex1.py`). For each random instance and each of the 16 switch combinations it enumerates every raw state the
successor function can reach, checks that every generated action is legal, compares the pruned optimum with
the world optimum on each of those states (Dijkstra on both graphs), checks h ≤ world optimum on each of them,
and runs the real A* to check the returned plan's legality and cost.

| Run | Result |
|---|---|
| seeds 0 to 19 (first generator, before the ferry-heavy profile was added) | 304 ok, 16 skipped (graph too large), 0 failures, 548,624 states compared |
| seeds 100 to 299 | 3,168 ok, 32 skipped, 0 failures, 5,146,508 states compared |
| seeds 5000 to 5079, larger instances | 1,184 ok, 96 skipped, 0 failures, 1,635,344 states compared |

**The checker catches planted bugs.** Each bug was planted alone, with all four rules on, seeds 0 to 59:

| Planted bug | Seeds exposing it |
|---|---|
| Rule D without T3 | 5 of 60 (plus the §3.1 example) |
| Rule D without T1 | 32 of 60 |
| Rule C off by one (rests a truck whose capacity equals the lightest package) | 16 of 60 |
| Rule A requires the waiting truck to be empty | 13 of 60 |

**Rough speed on random medium instances** (`tools/compare_random.py --hard`, old file against new file, this
machine, Python 3.13, 60 s limit). Same cost on every solved instance. Typical effect 1.2x to 2x faster, two
instances slightly slower (more expansions through different tie-breaking), four instances timed out in both.
The supplied y cases have not been measured.

| seed | old | new |
|---|---|---|
| 2 | 3.46 s, 21,954 expanded | 2.73 s, 20,670 expanded |
| 3 | 0.74 s, 3,032 expanded | 0.76 s, 3,906 expanded |
| 9 | 1.44 s, 7,040 expanded | 0.81 s, 4,734 expanded |
| 11 | 2.73 s, 12,186 expanded | 1.25 s, 7,895 expanded |
| 12 | 5.56 s, 25,276 expanded | 3.86 s, 19,043 expanded |

## How to measure on planet

Put `tools/ablate_rules.py` beside `ex1.py`, `ex1_check.py`, `search.py` and `utils.py`:

```
python3 ablate_rules.py y3 y4 y7 --limit 120
```

It runs each case in a fresh process with all rules on, each rule off in turn, and all four off, and prints
time, expansions, cost and the checker's verdict. If one rule turns out to slow a case down, switch only that
one off. The proof covers every combination.
