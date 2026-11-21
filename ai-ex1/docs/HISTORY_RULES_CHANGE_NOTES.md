# History rules (condition 1): delivered change and notes

Revision 2, 2026-11-20: fixes the U-turn bug that Astra's audit found (point 1 below).
Revision 3, 2026-11-20: fixes the Rule B overflow on huge weights, and tightens the checker and the proofs after
Astra's recheck (points 8 and 9).

Proof: `HISTORY_RULES_PROOF.md`. This file records what changed, the points worth remembering, and the evidence.
The evidence is about the code. It is not a replacement for the proof.

## The reading this version relies on

Condition (1): at least one optimal plan from the initial state must survive the pruning, with any history kept
inside the hashable state. The strict version (rules A-D only) remains the fallback for the per-state reading (2).

The TA's forum answer states (2) in words ("from every state you keep, at least one optimal plan must still be
reachable"), but his own example rule only satisfies (1). Astra's recheck gives the cleanest instance, and it works
for the TA's rule too: road 0-1-2, capacity-one trucks 10 at 0 and 11 at 2, one unit package at 0 going to 1.
Keep the state after truck 11 drives from 2 to 1. Its world optimum is 3 (truck 10 loads, drives, unloads).

- Focus (H1) allows only truck 11 to act next, so the pruned optimum there is 4.
- The TA's rule "don't apply x right after y if they are independent and x has a lower index", with truck 10's
  actions indexed before truck 11's, prunes every action of truck 10 after that drive. Its pruned optimum there is
  also 4, while from the initial state it keeps the optimum 3. `tools/ta_rule_example.py` runs this.

What this shows, and no more: the TA's own example is valid only under (1), so (1) is a reading his example needs.
It does not show that the staff would accept H1. The two rules differ (right after truck 10's first LOAD, the TA's
order allows truck 11 to drive, and H1 forbids it). If the staff insist on (2) literally, both the TA's example and
this version fail it, and the strict file is the one to submit.

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

1. **H2 is a filter on one action, not on a position.** Revision 1 dropped every child in which the focus truck
   stood at prev. When a forced UNLOAD completes a component, `_finish` resets that component's trucks to their
   initial positions, and if the focus truck had started at prev, the UNLOAD was dropped too. Astra's audit gave
   two instances: two road components with no ferry, where the solver returned None on a solvable game, and a pair
   of states with the same key but different pruned optima (so merging was unsafe). Revision 2 drops only the
   action string `DRIVE{t,loc,prev}`. Both instances now pass, and the proof's Lemma 4 now treats the reset
   explicitly. Do not reintroduce a position test in any filter: no filter may read a truck's initial position.
2. **Why the checker missed it, and what changed there.** Its random games rarely had several components in which a
   truck finishes its component one road from its start. `validate_rules.py` now draws a quarter of its games from
   `split_game`: two independent sub-problems side by side (short roads from `small_game`, or ferry games),
   sometimes with an idle truck. Its child check also requires
   that every truck or ferry differing from the world successor belong to a component with no undelivered package,
   which is exactly what a `_finish` reset may change. On the revision-1 file the improved checker reports 40
   failures in seeds 0 to 59.
3. **H1 carries an exception that must stay:** a truck in focus may have an empty ferry sail to it. Without it, a
   truck that drives to a port can never get its ferry. The checker found exactly this bug during development,
   in the "H1 on, H4 off" configuration. It is fixed and the proof describes the fixed behaviour.
4. **Merging equal-key states needs an argument under (1).** Under (2) it was trivially safe. Here the proof shows
   that all states sharing a key have the same pruned optimum (Lemma 4). The index-based choices that need care
   are twin representatives, the order of simultaneous forced unloads, and the `_finish` reset.
5. **Not valid under (2), on purpose.** The checker in `--mode1` reports how many reachable states lose their own
   optimum. Those counts are expected.
6. **Older documents describe the file without history.** `ADMISSIBILITY_PROOF.md` §16 says `hcache` is keyed
   by the complete raw state. With history on, the key is the state with field 0 set to 0. h never reads field 0,
   and both aboard codes of H3 decode to the same ferry, so states that differ only there get the same h and reuse
   stays exact. `INCREMENTAL_CANONICALIZATION_PROOF.md` assumes field 0 is always 0 and no freshness bit.
   `successor` bypasses the incremental path whenever history or H3 is on, so that proof applies only with both
   off, which is the strict file.
7. **The design was written from scratch** without the 16 November file. Rule ideas like focus and corridors are
   generic. The proof and the code are new.
8. **Rule B and huge integers.** A package weight like 2^80 made the constructor raise `OverflowError` (the bitset
   was shifted by the weight). Now weights above the capacity are dropped, the bitset is used only up to capacity
   2^20, a set of sums above that, and Rule B switches itself off if the set would pass 2^16 sums. Proof:
   `SUCCESSOR_RULES_PROOF.md` Lemma 7′. Both theorems cover Rule B off.
9. **Checker, revision 3.** Without `--mode1` it now switches history, corridors, `OPT_BARREN` and
   `OPT_PARTIAL_ORDER` off in the file it checks, which is the configuration of the per-state theorem (before, it
   inherited the file's defaults). In both modes it now also checks that reachable states with the same canonical
   key have the same pruned optimum, which is Lemma 4 itself. On revision 1 that check fails directly on Astra's
   second instance.

## Evidence

`tools/validate_rules.py --mode1 --file ex1.py`: every reachable extended state of small random instances, legal
actions, children equal to the world successor up to a `_finish` reset, h never above the world optimum, pruned
optimum from the initial state equal to the world optimum, and the real A* returning a legal plan of that cost.
14 switch configurations per instance. Revision 3 adds the equal-key check (Lemma 4) in both modes:

| Run | Result |
|---|---|
| seeds 0 to 199 | 2,704 ok, 96 skipped, 0 failures, 3,469,038 states |
| seeds 2000 to 2049, larger | 611 ok, 89 skipped, 0 failures, 1,397,827 states |
| `tools/regress_cases.py` (Astra's two instances) | both ok, both fail on revision 1 |
| this file in per-state mode (history and corridor off), seeds 3000 to 3099 | 1,560 ok, 40 skipped, 0 failures |
| strict file, per-state check, seeds 3000 to 3119 (revision 2 checker) | 1,864 ok, 56 skipped, 0 failures |

Revision 2 (without the Rule B fix and the key check): seeds 0 to 299, 4,057 ok, 0 failures, and seeds 2000 to 2099
larger, 1,269 ok, 0 failures.

Revision 1's clean runs (seeds 0 to 29, 100 to 399, 1000 to 1149, 6000 to 6079) used the old checker, which could
not see the bug, and are superseded.

**Revision 1 against revision 2, same games.** 8 y3-like chain maps and 8 ferry-heavy medium games: identical
expansions on 15, one extra expansion on the 16th, same costs, same timeouts. The fix touches only the step that
completes a component, so the measurements below still apply.

**Speed on this machine (Python 3.13, 40 s limit), strict file against revision 1.** Same cost wherever both finish.

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

Then run the full official checker: `python3 ex1_check.py all`. To re-check the two regression instances:
`python3 regress_cases.py ex1.py` (needs `validate_rules.py` beside it).
