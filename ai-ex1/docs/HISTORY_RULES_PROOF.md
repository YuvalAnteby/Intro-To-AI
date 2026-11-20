# History rules H1 to H4 and the corridor rule: proofs under condition (1)

Status: 2026-11-20, implemented in `ex1_p1.py` (to become `ex1.py`). Written from first principles for this
version. It reuses the facts proved in `SUCCESSOR_RULES_PROOF.md` and the facts E1 to E3 listed there, and it
re-derives the corridor argument instead of citing it. No test result is used in any proof.

## 0. What is proved, and under which reading

**Condition (1).** Pruning is acceptable if at least one optimal plan from the *initial* state survives in the
pruned search graph, so that the supplied A* returns an optimal plan. This is the reading supported by the
assignment's Tips ("You are allowed to create only some of the successor, under the condition that your code
still provides an optimal solution to the problem") and by the TA's own example rule ("don't apply x right after y
if they are independent and x has a lower index"), which satisfies (1) but not the stronger per-state condition
(2). Under (2) the rules below are *not* valid, and the checker confirms that many reachable states lose their own
optimum. That is expected and harmless under (1).

**Theorem 1 (Section 8).** With the delivered switches, and with every combination listed in Section 8, the
supplied `astar_search` returns a plan whose cost is the optimal cost from the initial state.

**Unchanged.** `h` returns the same value as before for every world state. Its cache key now ignores the history
field, which `h` never reads. `path_cost`, `goal_test`, the search code and every legality test are unchanged.

## 1. The rules

| Rule | Switch | Effect |
|---|---|---|
| H1. Focus | `OPT_FOCUS` | After a DRIVE or LOAD of truck t, the next action is an action of t, or an empty SAIL of a ferry to t's location (which t then boards). |
| H2. No U-turn | `OPT_UTURN` (needs H1) | A truck in focus does not drive straight back to the location it just came from. |
| H3. Fresh board | `OPT_FRESH` | A truck that boarded a ferry does not disembark before that ferry has sailed. |
| H4. Board next | `OPT_NEEDBOARD` (needs H1) | After a SAIL of an empty ferry f, the next action is a BOARD onto f (by the focus truck, if the sail was made for it). |
| K. Corridors | `OPT_CORRIDOR` | A truck unloads only at an anchor. |

**Anchors** (`transfer_sites`): locations whose road degree is not 2, initial truck locations, initial package
locations, package goals, and every port of every ferry. A *corridor* is a maximal road path v_0, ..., v_L whose
interior vertices v_1, ..., v_{L-1} are not anchors. Interior vertices have exactly two road neighbours, are not
ports, hold no object initially, and are nobody's goal.

The existing rules stay as they are: never load a package lying at its goal, eager goal UNLOAD (forced unload),
dead sides and dominated ports, component order with the `_finish` write-back, twins and symmetric merging, and
Rules A to D of `SUCCESSOR_RULES_PROOF.md`. Strong stubborn sets stay off.

## 2. Extended states and the generator

An **extended state** is x = (w, η): a world state w (the tuple without its leading field) and a history code
η = `state[0]`:

| η | Meaning | Set by |
|---|---|---|
| 0 | no history | UNLOAD, BOARD, DISEMBARK, SAIL of a ferry with trucks aboard, forced UNLOAD, `_finish` |
| focus(t, prev) | truck t is in focus, its last drive came from prev (prev = none after a LOAD) | DRIVE of t (prev = origin), LOAD into t |
| need(f, t) | the next action must be a BOARD onto f, by t (t = none: by any truck at the dock) | empty SAIL of f, with H4 on |

With H4 off, an empty sail made for the focus truck leaves η unchanged, and an empty sail from η = 0 sets η = 0.

The generator has three branches:

- **η = need(f, t):** only BOARD(t', f) with t' = t (or any truck of the active component standing at f's dock
  if t = none), subject to f's capacity. Twins among empty trucks at the dock apply.
- **η = focus(t, prev):** only the actions `_truck_standing` produces for t (which include the forced UNLOAD of
  t alone, if t stands at the goal of a package it carries, and Rules D and K), minus the drive back to prev
  (H2), plus SAIL(f, d, loc(t)) for every empty, not disabled ferry f with capacity at least 1 that serves loc(t)
  and is docked elsewhere (ferry twins apply).
- **η = 0:** the generator of `SUCCESSOR_RULES_PROOF.md` (global forced UNLOAD, then everything else with Rules A
  to D, twins, component order), with K on UNLOADs, and with H3 removing every DISEMBARK of a truck whose aboard
  code says "boarded, not yet sailed" (even offset from n).

Every emitted action is world-legal (legality tests are unchanged). So every path of the pruned graph G is a legal
world plan of the same cost, and V_G(x) ≥ V(w) for every extended state x, where V is the world optimum.

## 3. Facts about optimal plans

Fix the initial state s0. A *plan* is a legal action sequence from s0 that reaches the goal. All facts below hold
for every optimal plan Π, because each describes a change that would make Π cheaper while keeping it legal.

- **F1 (no U-turn).** Π never has DRIVE(t, a, b) immediately followed by DRIVE(t, b, a). Deleting both leaves every
  other action reading exactly what it read, since only t's actions read t's position.
- **F2 (no fresh disembark).** Π never has BOARD(t, f) and later DISEMBARK(t, f) with no SAIL of f between them.
  Deleting both is legal: between them t only stands aboard, nothing reads its position, and every BOARD onto f in
  between sees occupancy one lower.
- **F3 (no trailing drives).** If truck t has a DRIVE, a later action of t that is not a DRIVE exists. Trailing
  drives can be deleted, and a trailing LOAD cannot exist because the package would end inside a truck.
- **F4 (useless trucks rest).** `SUCCESSOR_RULES_PROOF.md` Lemma 3, applied to the suffix after any prefix of Π
  (that suffix is optimal from its state).
- **F5 (shortest stretches).** A maximal block of consecutive DRIVE actions of one truck, with no other action in
  between, is a shortest path in G_go between its ends. Otherwise replace it by a shorter G_go path.
- **F6 (empty sails).** If ferry f sails while empty, the next action of f is a BOARD onto f. Proof as Lemma 4 of
  `SUCCESSOR_RULES_PROOF.md`: two consecutive empty sails merge into one (or both disappear), and a final empty
  sail can be deleted.

## 4. The starting plan π*

**Lemma 1.** There is an optimal plan π* from s0 with these properties:

- **(H)** every action is an H-action (no dead direction, no sail to a removed port, no action of a disabled
  ferry, no LOAD of a package lying at its goal),
- **(K)** every LOAD and every UNLOAD happens at an anchor,
- **(P4)** every SAIL of an empty ferry f is immediately followed by a BOARD onto f,
- **(P1)** every DRIVE or LOAD of a truck t is immediately followed either by an action of t, or by an empty
  SAIL(f, d, z) to t's current location z that is immediately followed by BOARD(t, f).

*Proof.* Build it in four steps. Each step keeps the cost and the properties of the earlier steps.

**Step 1 (H).** By E2 at s0 there is an optimal plan using H-actions only.

**Step 2 (K), the corridor argument.** Take a corridor v_0, ..., v_L with L ≥ 2 and edges e_i = {v_{i-1}, v_i}.
Let N_i be the number of DRIVE actions along e_i in the plan. For a threshold j in 1..L, the projection φ_j maps
v_1, ..., v_{j-1} to v_0 and v_j, ..., v_{L-1} to v_L. Apply it to every position of every truck:

- a DRIVE along e_i with i ≠ j joins two vertices with the same image and is deleted,
- a DRIVE along e_j becomes the L drives along the whole corridor in the same direction,
- LOAD and UNLOAD do not name a location, so they stay, and now happen at the image location.

The initial state is fixed by φ_j (no object starts inside). Colocations are preserved, so every LOAD and UNLOAD
stays legal with the same loads. No port is inside, so no ferry action changes. No goal is inside, so the final
state still satisfies the goal. The corridor drives now cost L·N_j, and the average of L·N_j over j is
Σ_i N_i, the old cost. Choose j minimizing L·N_j, preferring the smallest N_j on ties. If some edge of the
corridor has a dead direction, then its far side is a dead side that no truck starts in and no plan in H enters,
so that edge has N = 0 and is chosen, and no full traversal is created. Otherwise every full traversal uses
allowed directions. Corridors are edge-disjoint, so the projections can be applied one after another. The result
is optimal, still in H (goals and packages lying at goals are untouched), and every LOAD and UNLOAD happens at an
anchor.

**Step 3 (P4).** By F6, every empty sail of f is followed, among f's actions, by a BOARD onto f. Move the sail to
immediately before that BOARD. The actions it passes do not involve f, and only actions involving f read f's dock
(swap lemma, `SUCCESSOR_RULES_PROOF.md` Lemma 1). Cost, (H) and (K) are unchanged.

**Step 4 (P1).** For a truck t, a *run* is a maximal sequence of DRIVE and LOAD actions that are consecutive in
t's own action sequence. By F3 every run is followed, in t's sequence, by an action y of t that is UNLOAD or BOARD
(it cannot be DISEMBARK since t is standing). Move the run, keeping its order, to immediately before y, or, if y
is BOARD(t, f) and the action immediately before y is an empty SAIL of f, to immediately before that sail.

This is legal. A run's actions involve t and packages p loaded in the run. Every action of t between the run and y
belongs to the run. A package loaded in the run lies inside t until its next action, which is an UNLOAD by t at y
or later. So the actions the run passes share no object with it, and Lemma 1 of `SUCCESSOR_RULES_PROOF.md` lets
each run action move later past them. Runs of different trucks are attached to different actions, so they never
land inside each other, and a run placed before an empty sail leaves that sail immediately before its BOARD.
Positions where loads and unloads happen do not change, so (H), (K) and (P4) still hold. Now every run is
contiguous and ends right before y (or right before the sail that precedes y), which is (P1). ∎

## 5. Walking the generator along an optimal plan

Write a plan as Π = α·ρ, where the **prefix** α is a path the generator has emitted (from the initial extended
state x0 = (s0, 0)) and the **suffix** ρ is still to be emitted. Let x = (w, η) be the extended state the
generator reaches after α.

**Invariant J(α, ρ).** Π = α·ρ is an optimal plan from s0 with properties (H), (K) and (P1), and with (P4) for
every empty sail of Π, except that when H4 is off, an empty sail that is the last action of α need not be
immediately followed by a BOARD. (With H4 off, nothing after that sail relies on it: the sail was already
emitted, and if it was made for a focus truck t, the history stays focus(t, ·) and (P1) still requires
BOARD(t, f) next.)

J(empty, π*) holds by Lemma 1. Note that (P1) and (P4) are properties of the whole plan, so they also constrain
the first action of ρ through the last action of α. Note also that ρ is an optimal plan from w, because α is fixed
and Π is optimal.

**Lemma 2 (rewrite for a forced unload).** Assume J(α, ρ). Let truck t2 stand at the goal of a package p it
carries in w, and assume η is 0 or focus(t2, ·). Let ρ̂ be UNLOAD(p, t2) followed by ρ with every action involving
p deleted, and then with every run whose final action was deleted moved, as in Step 4, to just before its truck's
next UNLOAD or BOARD. Then J(α, ρ̂) holds, and ρ̂ starts with UNLOAD(p, t2).

*Proof.* UNLOAD(p, t2) is applicable in w. After it, p lies at its goal. The deleted actions are the remaining
LOADs and UNLOADs of p. Every other action stays legal: trucks that would have carried p carry less, and LOAD only
tests an upper bound on the load. The final state still has p at its goal. ρ contains at least one UNLOAD of p
(p is inside t2 in w), so the cost does not increase, and Π̂ = α·ρ̂ is optimal. Deleting an action of p from the
middle of a run keeps the run contiguous. Deleting a run's final UNLOAD(p, t3) leaves that run without its
terminal action. By F3 (Π̂ is optimal) t3 has a later UNLOAD or BOARD, and moving the run before it is legal for
the same reason as in Step 4. (H) and (K) hold (the new unload is at p's goal, an anchor, and nothing else changes
location). (P4) holds for every empty sail inside ρ̂ (no sail moves, and a run is placed before an empty sail
only for its own BOARD). At the boundary, if η = focus(t2, ·), the first action of ρ̂ is an action of t2, as (P1)
requires. If η = 0, the last action of α is not a DRIVE or LOAD, so (P1) asks nothing of the boundary, and it is
not an empty sail with H4 on (that would give η = need), so the exception in J covers the only sail the inserted
UNLOAD can separate from its BOARD. ∎

**Lemma 3 (step).** Assume J(α, ρ) with ρ non-empty. Then the generator emits, in x, an action a such that, after
replacing ρ by an equally good ρ' if necessary, ρ' = a·ρ'' and J(α·a, ρ'') holds.

*Proof.* By cases on η.

**Case need(f, t).** The last action of α is an empty SAIL of f. By (P4) the first action of ρ is a BOARD onto f,
by a truck standing at f's dock. If the sail followed a DRIVE or LOAD of t (that is exactly when the generator set
need(f, t) with t ≠ none), then (P1) says this BOARD is by t. The need branch emits it (the BOARD is legal, so the
capacity test passes). If t = none and the twin rule emits a different empty truck at the same dock, rename as in
Section 6.

**Case focus(t, prev).** The last action of α is a DRIVE or LOAD of t. By (P1), ρ starts with an action of t, or
with an empty SAIL(f, d, loc(t)) followed by BOARD(t, f).

- *Empty sail.* f is empty, not disabled (it acts, and Π uses H-actions), has capacity at least 1 (the BOARD after
  it is legal), serves loc(t) (H-action), and is docked elsewhere. The focus branch emits it, up to ferry twins. The
  new history is need(f, t) (or unchanged focus(t, prev) with H4 off), and (P1) gives the BOARD(t, f) that the new
  history asks for.
- *t stands at the goal of a package it carries.* The generator emits only the forced UNLOAD(p, t) for the first
  such p in t's cargo order. If ρ does not start with it, replace ρ by ρ̂ of Lemma 2 for this p.
- *Otherwise* the first action a of ρ is an action of t, and `_truck_standing` emits it, because it passes every
  filter there:
  - (K): a non-forced UNLOAD happens at an anchor.
  - LOAD: legal, so the capacity test passes, and package twins are handled in Section 6.
  - BOARD: legal, and ferry twins are handled in Section 6.
  - H2: if a is DRIVE(t, loc, prev), then α ends with DRIVE(t, prev, loc), contradicting F1.
  - Rule D, if t is empty and a is a DRIVE. In focus with t empty, t's last action was a DRIVE (a LOAD would have
    left t loaded, and an UNLOAD would have cleared the focus). By (P1), the rest of t's run is contiguous from the
    start of ρ up to its terminal action y at location z, possibly with one empty sail just before y. Nothing else
    happens between w and y. So in w: if y = LOAD(p, t), then p lies at z, is undelivered (H), and w_p ≤ c_t
    (t is empty), which is target kind T1. If y = BOARD(t, f) without a sail before it, f is docked at z with
    occupancy below k_f, kind T2. If an empty sail of f precedes y, f is empty in w and z ∈ `sail_to[f]`, kind T3.
    By F5 the drives from loc(t) to z form a shortest G_go path, so the first one satisfies
    d(m, z) = d(loc(t), z) − 1, as Rule D requires.

  The new history (focus(t, ·) after DRIVE or LOAD, 0 after UNLOAD or BOARD) agrees with (P1) for the rest of ρ.

**Case η = 0.** The last action of α is not a DRIVE or LOAD (or α is empty), so (P1) puts no constraint on the
first action of ρ.

- *Forced.* If a truck of the active component stands at the goal of a package it carries, the generator emits only
  its canonical forced UNLOAD u (first such truck, first such package). If ρ does not start with u, replace ρ by
  ρ̂ of Lemma 2 for u.
- *Component order.* Otherwise move all actions of the active component c* to the front of ρ, keeping their order.
  Actions of different components share no object, so this is legal (Lemma 1 of `SUCCESSOR_RULES_PROOF.md`). Runs
  stay contiguous because a run belongs to one component, and an empty sail and the BOARD after it belong to the
  same component. So J still holds.
- *The first action a of ρ is now emitted*, because it passes every filter of the η = 0 branch:
  - Rule C: a is not an action of a useless truck (F4).
  - Rule A: if a is an empty sail of f to X, (P4) says the next action is a BOARD onto f by a truck standing at X
    in w. That truck acts, so it is not useless (F4), and the BOARD is legal, so f's capacity is at least 1.
  - Rule D: if a is a DRIVE of an empty truck t, then a starts a run (η = 0), and by (P1) the run is contiguous up
    to its terminal. The argument of the focus case gives a target of kind T1, T2 or T3 in w, and F5 gives the
    shortest-path condition.
  - (K): a non-forced UNLOAD happens at an anchor.
  - H3: if a is DISEMBARK(t, f) while t's code says "boarded, not yet sailed", then Π contains BOARD(t, f) and this
    DISEMBARK with no SAIL of f between them, contradicting F2.
  - (H): Π uses H-actions only.
  - Twins: Section 6.

  The new history is focus(t, ·) after a DRIVE or LOAD, need(f, ·) after an empty sail with H4 on, and 0 otherwise.
  It agrees with (P1) and (P4) for the rest of ρ.

In every case J(α·a, ρ'') holds, because Π' = α·a·ρ'' is the (possibly rewritten) optimal plan with all four
properties. ∎

## 6. Twins, renamings and merged states

**Twins inside Lemma 3.** When the generator emits a twin representative instead of the first action a of ρ, there
is a renaming σ of interchangeable objects (`SUCCESSOR_RULES_PROOF.md` Lemma 7, with Rule B classes if on) that
fixes w and maps a to the representative. The objects swapped are empty trucks at the same position, packages of
the same class at the same place, or empty ferries at the same dock. The object named by η is never swapped: the
focus truck acts itself, and in need(f, ·) the ferry f is fixed. So σ also fixes η. Replace ρ by σ(ρ). It is legal
from w with the same cost and keeps (H), (K), (P1) and (P4), because σ preserves goals, weights, capacity classes,
served ports and positions, and maps runs to runs.

**Merged states.** `_canon` now returns the old key plus a description of η through the objects it names: for
focus(t, prev), the descriptor of t (position, class, cargo classes) and prev. For need(f, t), the class and dock
of f and the descriptor of t (or none). Ferry manifests also record each aboard truck's "sailed" bit when H3 is on.
Two extended states have equal keys exactly when a class-preserving renaming τ maps one to the other, history
included.

**Lemma 4.** V_G(τ(x)) = V_G(x) for every such renaming.

*Proof.* Every filter of the generator is defined through classes, positions and the renamed history, so the
emitted actions of τ(x) are the τ-images of those of x, up to two index-based choices. *Twin representatives:*
the images are twins of the representatives, so they lead to states with equal keys. *The forced UNLOAD:* the
generator picks the lowest truck index (and the first package in cargo order). Unloading moves no truck, so while
forced unloads are pending, no new ones appear, and the generator emits only forced unloads, one per step, until
none is pending. Forced unloads of different trucks are independent, and two unloads from the same truck commute,
since UNLOAD does not read the load. So whatever the order, the same set of unloads is executed, at the same cost,
ending in the same state with η = 0 (and with the same `_finish` write-back, which happens at the last delivery of
the component). By induction on the number of actions (V_G is finite or both sides are infinite), V_G is invariant
under τ. ∎

**A* with merging.** The supplied `graph_search` keeps one extended state per key, reopening it when it is reached
at a smaller g. By Lemma 4, all members of a key class have the same V_G. The usual A* argument then applies to
classes. Before the goal is popped, some open node lies on a path of cost V_G(x0) (if its class was closed with a
smaller or equal g, the closed member has the same V_G and its successors continue such a path). Consistency of h
is not needed.

## 7. Admissibility for the graph that is searched

For every extended state x = (w, η): h(x) = h(w) ≤ V(w) ≤ V_G(x). The first inequality is `ADMISSIBILITY_PROOF.md`
(h does not read η, and the cache key drops η). The second holds because every path of G is a legal world plan.
So h is admissible for G.

## 8. Main theorem and covered switch combinations

**Theorem 1.** With `OPT_FOCUS` on, and each of `OPT_UTURN`, `OPT_FRESH`, `OPT_NEEDBOARD`, `OPT_CORRIDOR`,
`OPT_EMPTY_SAIL`, `OPT_EFFCAP`, `OPT_USELESS` and `OPT_TOWARD` on or off, the supplied A* returns a plan of cost
V(s0).

*Proof.* By induction with Lemma 3, starting from J(empty, π*), the generator emits every action of an optimal plan
(possibly rewritten along the way), so V_G(x0) ≤ V(s0). With V_G ≥ V this gives V_G(x0) = V(s0). Sections 6 and 7
give an optimal search on G with merging. A switched-off rule only removes a filter, and every case of Lemma 3 shows
that the action is emitted with the filter present, so it is emitted without it too. With `OPT_UTURN` or
`OPT_NEEDBOARD` off, the corresponding history is simply not recorded. ∎

**Focus off.** With `OPT_FOCUS` off, η is always 0 (H2 and H4 need H1). Rules H3 and K and Rules A to D remain.
Use the invariant J without (P1) and (P4). The forced case is Lemma 2. Otherwise apply Lemma 6 of
`SUCCESSOR_RULES_PROOF.md` to ρ (optimal from w, H-actions only): it gives a free action x of ρ in the active
component that passes Rules A, C and D. Moving it to the front (Lemma 2 of that document) changes no location of
any load or unload, so (K) is kept. If x were a fresh DISEMBARK, Π would contradict F2. So x is emitted, and the
induction goes through.

**History off.** With `OPT_HISTORY` off and `OPT_CORRIDOR` off, the generator is the one of
`SUCCESSOR_RULES_PROOF.md`, which even satisfies condition (2).

## 9. Implementation correspondence

- `state[0]` holds η. Codes: 1 + t·(n+1) + prev (prev = n for none), and need_base + f·(T+1) + (t+1 or 0), with
  need_base = 1 + T·(n+1). Set in `_truck_standing` (DRIVE, LOAD), in `_history_successors` (empty sail for the
  focus truck) and in the ferry loop of `_successors` (empty sail from η = 0). Every other child gets 0, including
  `_finish`.
- `_history_successors` implements the need and focus branches of Section 2. `_successors` implements η = 0, with
  H3 in the DISEMBARK branch. BOARD stores the even "boarded, not yet sailed" code when H3 is on, and the unchanged
  `_sail` turns it odd.
- `_canon` appends the history description and, with H3, the sailed bit (Section 6). Incremental canonicalization
  is bypassed whenever history or H3 is on.
- `h_astar` drops η from its cache key. `_h`, `_bound` and everything below them are unchanged.
- `OPT_PARTIAL_ORDER` stays off (forced off by the new rules).

## 10. Implementation evidence (not part of the proof)

`tools/validate_rules.py --mode1` builds every extended state the generator can reach on small random instances,
checks that every action is legal, that h never exceeds the world optimum, that the pruned optimum from the initial
state equals the world optimum, and that the real A* returns a legal plan of that cost. Fourteen switch
configurations per instance: all rules on, each history rule off in turn, and all history off, each with Rules A
to D on and off.

| Run | Result |
|---|---|
| seeds 0 to 29 | 409 ok, 11 skipped (graph too large), 0 failures |
| seeds 100 to 399 | 4,082 ok, 118 skipped, 0 failures, 7,790,933 states checked |
| seeds 6000 to 6079, larger | 944 ok, 176 skipped, 0 failures, 3,151,014 states checked |
| seeds 1000 to 1149, final code | 2,021 ok, 79 skipped, 0 failures, 2,713,827 states checked |

During development the checker found one bug, before this document: with H1 on and H4 off, the empty-sail
exception of the focus branch was missing, so a truck that had driven to a port could never get its ferry. It is
fixed, and Section 2 describes the fixed behaviour.

## 11. Not claimed

- The per-state condition (2) is not claimed, and is false for these rules by design.
- No speed-up is claimed by the proof. Measurements are in the change notes.
