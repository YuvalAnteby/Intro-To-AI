# Validation tools for ex1.py (not submitted)

Run them from the `ai-ex1` folder. None of them shares code with `ex1.py`: the rules of the domain are
implemented again in `validate.py` (class `Ref`) from the assignment text.

| command | what it checks |
|---|---|
| `python util/validate.py 1000 700 S` | Small random games, whole state space enumerated, exact h*. Plan optimal, every generated action legal, `h <= h*` on every state, `h` a non-negative int, `goal_test` right. Arguments: first seed, number of games, profile. |
| `python util/validate.py 20000 700 X` | The same on inputs outside the assignment's wording (ferry starting at a port it does not serve, ferry for 0 trucks, truck of capacity 0). |
| `python util/validate_big.py 9000 250 150000` | Larger games: plan cost against a plain uniform-cost search. |
| `python util/crosscheck.py 1000 400 G 8 420` | Games too large to enumerate: the submitted configuration against a weaker heuristic and against no pruning. Profiles `G`, `G2`. Uses a timer signal, so Linux or macOS only. |
| `python util/walk.py x3 40 25 20` | A given problem: `h` against the cost of real plans from random reachable states. |
| `python util/prune_check.py 50000 300 S` | Pruning and state merging without the heuristic: the whole pruned graph against the exact solver, in 26 configurations of the switches (all rules, each alone, all but one). See [the pruning proof](../docs/PRUNING_PROOF.md), section 8. |
| `python util/mutate.py` | Checks the checker: injects a wrong effect in memory and counts how often `prune_check` notices. |
| `python util/edge.py` | Hand-written edge cases (empty input, unsolvable input, odd formats). |

Profiles of `validate.py`: `S` small, `M` medium, `L` long maps, `W` many packages, `R` roads only,
`H` many ferries, `X` out-of-wording inputs, `D` several independent parts of the map. A `FAIL` line prints the seed and the game.
Use fresh seed ranges for new evidence. The ranges above are the ones already run.
