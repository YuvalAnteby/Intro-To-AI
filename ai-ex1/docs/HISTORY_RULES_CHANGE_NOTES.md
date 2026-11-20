# History rules (condition 1): delivered change and notes

Proof: `HISTORY_RULES_PROOF.md`. This file records what changed, the points worth remembering, and the evidence.
The evidence is about the code. It is not a replacement for the proof.

## The reading this version relies on

Condition (1): at least one optimal plan from the initial state must survive the pruning, with any history kept
inside the hashable state. The assignment's Tips support it, and so does the TA's own example rule. The TA has not
answered the forum question yet. Under the stricter per-state reading (2) these rules are not valid, by design. The
strict version delivered earlier (rules A-D only) remains the fallback.

## What changed in ex1.py

| Switch (default) | Rule |
|---|---|
| `OPT_HISTORY = True` | master switch for H1-H4 |
| `OPT_FOCUS = True` | H1: after a DRIVE or LOAD of a truck, the next action is that truck's, or an empty sail to it |
| `OPT_UTURN = True` | H2: a truck in focus does not drive straight back (only with H1) |
| `OPT_FRESH = True` | H3: no DISEMBARK before the ferry has sailed |
| `OPT_NEEDBOARD = True` | H4: an empty sail is immediately followed by a BOARD onto that ferry (only with H1) |
| `OPT_CORRIDOR = True` | transfers only at anchors (re-derived in the proof, valid under condition 1 only) |

Rules A-D, the heuristic's values, `path_cost` and `goal_test` are unchanged. The history lives in the leading field
of the state tuple (always 0 before), it is part of the canonical key, and the heuristic cache ignores it.
New or changed methods: `_setup_rules`, `_prepare_rules` (new, factored out of `_successors`),
`_history_successors` (new), `_successors`, `_truck_standing`, `_canon`, `h_astar` (cache key only), `successor`
(bypasses incremental canonicalization when history is on). The AI-use header describes this work.

## Points to remember

1. **H1 carries an exception that must stay:** a truck in focus may have an empty ferry sail to it. Without it, a
   truck that drives to a port can never get its ferry. The checker found exactly this bug during development,
   in the "H1 on, H4 off" configuration. It is fixed and the proof describes the fixed behaviour.
2. **Merging equal-key states needs an argument under (1).** Under (2) it was trivially safe. Here the proof shows
   that all states sharing a key have the same pruned optimum (Lemma 4). The only index-based choice that needed
   care was the order of simultaneous forced unloads.
3. **Not valid under (2), on purpose.** The checker in `--mode1` reports how many reachable states lose their own
   optimum. Those counts are expected.
4. **The design was written from scratch** without the 16 November file. Rule ideas like focus and corridors are
   generic. The proof and the code are new.

## Evidence

`tools/validate_rules.py --mode1 --file ex1.py`: every reachable extended state of small random instances, legal
actions, h never above the world optimum, pruned optimum from the initial state equal to the world optimum, and the
real A* returning a legal plan of that cost. 14 switch configurations per instance.

| Run | Result |
|---|---|
| seeds 0 to 29 | 409 ok, 11 skipped, 0 failures |
| seeds 100 to 399 | 4,082 ok, 118 skipped, 0 failures, 7,790,933 states |
| seeds 6000 to 6079, larger | 944 ok, 176 skipped, 0 failures, 3,151,014 states |
| seeds 1000 to 1149, final code | 2,021 ok, 79 skipped, 0 failures, 2,713,827 states |

**Speed on this machine (Python 3.13, 40 s limit), strict file against this file.** Same cost wherever both finish.

y3-like chain maps (pure road trees, 50-66 locations, 3-4 trucks, 6-8 packages):

| seed | strict | condition 1 |
|---|---|---|
| 100 | timeout | 0.28 s, 2,890 expanded |
| 102 | 6.31 s, 34,284 | 0.10 s, 1,222 |
| 106 | 4.55 s, 24,723 | 0.06 s, 683 |
| 109 | timeout | 1.43 s, 13,600 |
| 110 | timeout | 0.26 s, 3,216 |
| 113 | timeout | 7.30 s, 63,573 |
| 115 | timeout | 0.96 s, 13,779 |

Ferry-heavy medium instances (3 islands, 2 ferries, 3-4 trucks, 5-7 packages), 24 seeds: typically 3x to 11x
faster, three instances solved that the strict file cannot (17-22 s), three still time out in both.

Switch ablation on two medium instances: focus gives most of the gain (about 4x fewer expansions on both). U-turn,
board-next and corridor each add up to about 1.7x, and fresh-board is about neutral.

## How to measure on planet

Put `tools/ablate_rules.py` beside `ex1.py`, `ex1_check.py`, `search.py` and `utils.py`:

```
python3 ablate_rules.py y3 y4 y7 --limit 60      history rules: all on, each off, all off
python3 ablate_rules.py y3 y4 y7 --rules         rules A-D: all on, each off, all off
```

Then run the full official checker: `python3 ex1_check.py`.
