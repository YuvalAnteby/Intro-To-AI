# Proof recheck of `ex1 (6).py`

For valid assignment instances with integer package weights and capacities, the heuristic is admissible. With the delivered switches, the supplied A* preserves an optimal plan from the initial state and detects unsolvable instances, assuming the search can run to completion. The defaults still violate the TA’s stronger requirement to preserve an optimal continuation from every retained state.

## The effective-capacity fix is correct

The only existing solver method whose executable logic changed from v5 is `_setup_rules`. It calls the new `_best_load` at line 1844. For a truck of capacity $c$, any package heavier than $c$ can be discarded from this calculation because all package weights are nonnegative. For the remaining weights, let $S_i$ be the attainable subset sums at most $c$ after processing $i$ packages. Then

$$
S_0=\{0\},\qquad
S_{i+1}=S_i\cup\{s+w_{i+1}\mid s\in S_i,\ s+w_{i+1}\le c\}.
$$

Every subset either includes the new package or omits it. By induction both the masked bitset and the sparse set implement this recurrence. An exact return therefore equals $\max S_m$. Every prospective legal truck load is itself a subset sum, so comparison with this maximum gives the same LOAD decision as comparison with the original capacity. Actual legality checks continue to use the original capacities.

If the sparse set exceeds $2^{16}$ elements, the helper returns `None`. Lines 1845–1855 discard the provisional results for **all** trucks and retain the original truck and ferry classes. The earlier symmetry proof covers those classes, and partial-order pruning stays off. Thus either branch preserves optimal cost. The old oversized bit shift is gone. The sparse limit bounds the number of stored sums. The space for each integer still depends on its bit length.

## Heuristic and initial-state optimality

Let $\pi(x)$ discard the history field and interpret both aboard codes as being on the same ferry. The heuristic ignores focus and pending-board history, and its movement bound decodes both aboard codes identically. Lemma 13 of the admissibility proof covers reuse of a regional value under every cache history. Every generated goal-reaching action sequence can be replayed in the physical world at the same cost. A completed-component reset is harmless because subsequent moves concern other components. Consequently

$$
0\le h(x)\le V_{\rm world}(\pi(x))\le V_{\rm pruned}(x).
$$

At a goal there are no pending package actions or movement terms, so $h=0$. The history proof’s Sections 4–6 supply the other half of the initial-state argument. An optimal physical plan can be reordered to obey focus, empty-ferry boarding and corridor handling. The forced unloads and canonical representatives preserve its cost. At the initial state the two optimal costs are therefore equal. The supplied graph search reopens any key reached at a smaller path cost. This proof requires admissibility and the equal remaining costs of merged representatives. It does not require consistency.

## The TA’s per-state criterion

Take the road 0–1–2. Trucks A and B start at 0 and 2 with capacity 1. A unit package starts at 0 with goal 1. The generator permits B to drive from 2 to 1 toward the package. From that retained state, A can LOAD, DRIVE and UNLOAD for cost **3**. Every completion requires all three operations, so 3 is optimal. Focus now forces B to act. Its only generated move is to drive to 0. B can then load, drive and unload, giving exactly **4**. From the initial state A’s three-action plan survives. This refutes the per-state theorem even though every location in the example is a corridor anchor.

To satisfy the literal per-state condition, set `OPT_HISTORY=False` and `OPT_CORRIDOR=False`, with `OPT_BARREN=False` and `OPT_PARTIAL_ORDER=False` as delivered. The successor proof covers Rules A–D in this combination. Effective capacities and occupancy reuse can stay enabled.

## Remaining corrections to the accompanying material

- **TA example.** With A’s actions indexed below B’s, the TA’s adjacent-order rule also blocks A’s LOAD immediately after B’s DRIVE. Those two actions genuinely commute. The same 3-versus-4 argument applies. It does not establish the claim on line 25 of the history change notes that any interpretation permitting the TA’s example must permit H1. Indeed, immediately after A’s initial LOAD the TA’s order allows B’s DRIVE, whereas H1 forbids it. In `ta_rule_example.py` line 34, different trucks alone are insufficient to establish independence. For instance, one truck’s UNLOAD can enable another’s LOAD of the same package.
- **Scaling.** Item 4 of the successor change notes overstates what is invariant. Uniformly scaling package weights and truck capacities preserves every LOAD decision and the world optimum. It can change the implemented symmetry classes. For weights $2,4,\ldots,2^{17}$ and capacities $2^{17},2^{17}+1$ in one component, both trucks have effective capacity $2^{17}$. Scaling all those numbers by 16 selects the sparse branch. There are $2^{16}+1$ feasible sums, so fallback keeps the two distinct raw capacities.
- **Cache wording.** Section 16 of the standalone admissibility proof still calls the outer cache key the complete raw tuple. Lines 2688–2689 of v6 zero the history field before lookup. Near line 2748 the source comment also claims identical regional values for some custody changes. Lemma 13 establishes the bound needed even if fresh evaluations select different cycle centers. Section 7 of the revised history proof gives the correct statement. The old incremental-canonicalization proof applies only with history and ferry freshness disabled. The default solver bypasses that code.

The revised validator compares remaining pruned costs across reachable states sharing a canonical key. Its per-state command-line mode now switches history and corridors off.

As a separate implementation cross-check, the two earlier U-turn regressions returned initial costs 6 and 3. The $2^{80}$-weight instance returned cost 3 under both the default and per-state settings. These checks make no claim about the 30-second benchmark.
