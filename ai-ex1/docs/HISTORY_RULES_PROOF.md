# History rules H1 to H4 and the corridor rule: proofs under condition (1)

Status: 2026-11-20, revision 3 (after Astra's audit and recheck, see Section 10). Implemented in `ex1.py`. Written from
first principles for this version. It reuses the facts proved in `SUCCESSOR_RULES_PROOF.md` and the facts E1 to E3 listed there, and it
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
supplied `astar_search` returns a plan whose cost is the optimal cost from the initial state when the instance is
solvable, and returns None when it is not. Preprocessing always completes: Rule B computes its classes exactly with
bounded memory, or switches itself off for the instance (`SUCCESSOR_RULES_PROOF.md` Section 10), and Rule B off is
one of the covered combinations.

**The physical state.** For an extended state x, π(x) is the world state obtained by dropping the history field and
reading both aboard codes of a truck (Section 2, H3) as "aboard ferry f". `h` is the same code as before, applied to
π(x): it normalizes the history field before its cache lookup and decodes both aboard codes to the same ferry. The
claim about h is admissibility (Section 7), not equal numbers across runs: the coarse regional cache of
`ADMISSIBILITY_PROOF.md` §16 can give different admissible values for the same state under different cache
histories. `path_cost`, `goal_test`, the search code and every legality test are unchanged.

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
ports, hold no object initially, and are nobody's goal. Walking from a non-anchor vertex in both directions through
non-anchor vertices ends at anchors or returns to the start. So every non-anchor vertex is interior to exactly one
corridor, possibly closed (v_0 = v_L, a road cycle through a single anchor), or lies on a road cycle with no anchor
at all. Such a cycle is a whole road component with no object, goal or port, so no truck ever enters it.

The existing rules stay as they are: never load a package lying at its goal, eager goal UNLOAD (forced unload),
dead sides and dominated ports, component order with the `_finish` write-back, twins and symmetric merging, and
Rules A to D of `SUCCESSOR_RULES_PROOF.md`. Strong stubborn sets stay off.

## 2. Extended states and the generator

An **extended state** is x = (w, η): the tuple w without its leading field and a history code η = `state[0]`.
With H3 on, an aboard code in w also carries the "boarded, not yet sailed" bit. The physical state π(x) of
Section 0 drops η and that bit. Below, "in w" means in π(x) whenever a physical fact is meant. The history codes:

| η | Meaning | Set by |
|---|---|---|
| 0 | no history | UNLOAD, BOARD, DISEMBARK, SAIL of a ferry with trucks aboard, forced UNLOAD, `_finish` |
| focus(t, prev) | truck t is in focus, its last drive came from prev (prev = none after a LOAD) | DRIVE of t (prev = origin), LOAD into t |
| need(f, t) | the next action must be a BOARD onto f, by t (t = none: by any truck at the dock) | empty SAIL of f, with H4 on |

With H4 off, an empty sail made for the focus truck leaves η unchanged, and an empty sail from η = 0 sets η = 0.

The generator has three branches:

- **η = need(f, t):** only BOARD(t', f) with t' = t (or any truck of the active component standing at f's dock
  if t = none), subject to f's capacity. Twins among empty trucks at the dock apply. Rule C is not applied in this
  branch, so a useless truck at the dock may also be offered a BOARD. That only adds successors.
- **η = focus(t, prev):** only the actions `_truck_standing` produces for t (which include the forced UNLOAD of
  t alone, if t stands at the goal of a package it carries, and Rules D and K), minus the single action
  DRIVE(t, loc(t), prev) (H2, identified by the action, not by the child's position: a forced UNLOAD that completes
  a component can also put t back at prev through the `_finish` reset), plus SAIL(f, d, loc(t)) for every empty,
  not disabled ferry f with 0 < k_f that serves loc(t) and is docked elsewhere (ferry twins apply). For integer
  ferry capacities 0 < k_f means k_f ≥ 1.
- **η = 0:** the generator of `SUCCESSOR_RULES_PROOF.md` (global forced UNLOAD, then everything else with Rules A
  to D, twins, component order), with K on UNLOADs, and with H3 removing every DISEMBARK of a truck whose aboard
  code says "boarded, not yet sailed" (even offset from n).

Every emitted action is world-legal (legality tests are unchanged). So every path of the pruned graph G is a legal
world plan of the same cost, and V_G(x) ≥ V(w) for every extended state x, where V is the world optimum.

## 3. Facts about optimal plans

Fix the initial state s0. A *plan* is a legal action sequence from s0 that reaches the goal. All facts below hold
for every optimal plan Π, because each describes a change that would make Π cheaper while keeping it legal.

- **F1 (no U-turn).** In Π, the action of t that follows DRIVE(t, a, b) in t's own sequence is never
  DRIVE(t, b, a). The actions between the two drives do not involve t, nor a package inside t (only t's own UNLOAD
  touches such a package), so by the swap lemma (`SUCCESSOR_RULES_PROOF.md` Lemma 1) the second drive can be moved
  next to the first. Deleting both then leaves every other action reading exactly what it read, since only t's
  actions read t's position, and the plan is cheaper.
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
allowed directions. A closed corridor (v_0 = v_L) is handled by the same projection: its interior goes to the
single anchor, and a drive along e_j becomes a closed walk of L drives. Its edges lie on a cycle, so none is a
bridge and none has a dead direction. Corridors are edge-disjoint, so the projections can be applied one after
another. The result
is optimal and every LOAD and UNLOAD happens at an anchor. It is still in H: drive directions were argued above and
no ferry action changed. One more case needs care. A transfer at an interior vertex can be projected onto an
endpoint that is the package's own goal, and the projected plan could then LOAD a package lying at its goal. In that
case delete that LOAD and every later action of that package. This is legal (trucks only carry less, and the
package already lies at its goal) and strictly cheaper, which contradicts the optimality of the projected plan. So
the projected plan contains no such LOAD.

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

**Invariant J(α, ρ).** Π = α·ρ is an optimal plan from s0, and:

- **(Hρ)** every action of ρ is an H-action,
- **(Kρ)** every LOAD and UNLOAD of ρ happens at an anchor,
- **(P1ρ)** every DRIVE or LOAD of a truck t in ρ is immediately followed, inside ρ, either by an action of t or by
  an empty SAIL of a ferry f to t's location that is immediately followed by BOARD(t, f),
- **(P4ρ)** every SAIL of an empty ferry f in ρ is immediately followed by a BOARD onto f,
- **(B)** the boundary condition for the history η reached after α:
  - η = focus(t, ·): ρ starts with an action of t, or with an empty SAIL(f, ·, loc(t)) immediately followed by
    BOARD(t, f),
  - η = need(f, t): ρ starts with BOARD(t, f), or, if t = none, with a BOARD onto f by a truck standing at f's dock,
  - η = 0: no condition.

All properties concern ρ and the boundary only. (Hρ), (Kρ), (P1ρ) and (P4ρ) talk about each action of ρ and the
one right after it, so they pass from ρ to any suffix of ρ. Each rewrite of ρ below re-establishes them explicitly.
J(empty, π*) holds by Lemma 1 (η = 0 at the start). ρ is an optimal plan from w, because α is fixed and Π is
optimal, and no DRIVE or LOAD is the last action of ρ (F3, and a final LOAD would leave a package in a truck).

**Lemma 2 (rewrite for a forced unload).** Assume J(α, ρ). Let truck t2 stand at the goal of a package p it
carries in w, and assume η is 0 or focus(t2, ·). Let ρ̂ be UNLOAD(p, t2) followed by ρ with every action involving
p deleted, and then with every run whose terminal UNLOAD was deleted moved, keeping its order, to immediately before
the next action of its truck (or, if that action is BOARD(t3, f) right after an empty SAIL of f, to immediately
before that sail). Then J(α, ρ̂) holds, and ρ̂ starts with UNLOAD(p, t2).

*Proof.* UNLOAD(p, t2) is applicable in w. After it, p lies at its goal. The deleted actions are the remaining
LOADs and UNLOADs of p. Every other action stays legal: trucks that would have carried p carry less, and LOAD only
tests an upper bound on the load. The final state still has p at its goal. ρ contains at least one UNLOAD of p
(p is inside t2 in w), so the cost does not increase, and Π̂ = α·ρ̂ is optimal.

Deleting a LOAD of p inside a run keeps the run contiguous and its terminal in place. Deleting a run's terminal
UNLOAD(p, t3) leaves that run without its terminal action. By F3 (Π̂ is optimal) t3 has a later action. If it is a
DRIVE or LOAD, it starts the next run of t3, which is contiguous up to its own terminal by (P1ρ), so the moved run
joins it. Otherwise it is an UNLOAD or BOARD (t3 is standing), and the moved run now ends right before it. The move
keeps t3's own order and passes only actions that involve neither t3 nor a package loaded in the run (such a package
stays inside t3 until a later UNLOAD by t3), so it is legal by the swap lemma, as in Step 4.

(Hρ) and (Kρ) hold (the new unload is at p's goal, an anchor, and nothing else changes location). (P1ρ) holds after
the runs are moved. (P4ρ) holds because no sail moves and a run is placed before an empty sail only for its own
BOARD. Boundary: if η = focus(t2, ·), ρ̂ starts with an action of t2, as (B) requires. If η = 0, (B) asks
nothing. ∎

**Lemma 3 (step).** Assume J(α, ρ) with ρ non-empty. Then the generator emits, in x, an action a such that, after
replacing ρ by an equally good ρ' if necessary, ρ' = a·ρ'' and J(α·a, ρ'') holds.

*Proof.* By cases on η.

**Case need(f, t).** By (B), ρ starts with BOARD(t, f), or with a BOARD onto f by a truck at the dock if t = none.
The need branch emits it (the BOARD is legal, so the capacity test passes). If t = none and the twin rule emits a
different empty truck at the same dock, rename as in Section 6.

**Case focus(t, prev).** By (B), ρ starts with an action of t, or with an empty SAIL(f, d, loc(t)) immediately
followed by BOARD(t, f). This history is set by a DRIVE or LOAD of t, and with H4 off it also survives an empty sail
emitted for t. In both cases t has not acted since that DRIVE or LOAD.

- *t stands at the goal of a package it carries.* The generator emits UNLOAD(p, t) for the first such p in t's cargo
  order (with the existing `OPT_FORCED` on, only that action of t) and no empty sail. If ρ does not start with it,
  replace ρ by ρ̂ of Lemma 2 for this p.
- *Empty sail, t not forced.* f is empty, not disabled (it acts, and ρ uses H-actions), has 0 < k_f (the BOARD after
  it is legal with occupancy 0), serves loc(t) (H-action), and is docked elsewhere. The focus branch emits it, up to
  ferry twins.
- *Otherwise* the first action a of ρ is an action of t, and `_truck_standing` emits it, because it passes every
  filter there:
  - (K): a non-forced UNLOAD happens at an anchor.
  - LOAD: legal, so the capacity test passes, and package twins are handled in Section 6.
  - BOARD: legal, and ferry twins are handled in Section 6.
  - H2 removes only the action DRIVE(t, loc(t), prev). If a is that DRIVE: prev ≠ none is set only by
    DRIVE(t, prev, loc(t)), and t has not acted since, so in t's own sequence in Π that drive is followed by a.
    This contradicts F1. Every other action of t, including a forced UNLOAD whose `_finish` reset puts t back at
    prev, passes H2.
  - Rule D, if t is empty and a is a DRIVE. Let y be the first action of t in ρ that is not a DRIVE. It exists
    (F3), and it is a LOAD or a BOARD, since t is empty and standing. By (P1ρ), every action of ρ before y is a
    DRIVE of t, except possibly one empty SAIL of a ferry f immediately before y, in which case y = BOARD(t, f).
    Nothing else happens between w and y. Let z be t's location at y. In w: if y = LOAD(p, t), then p lies at z, is
    undelivered (Hρ), and w_p ≤ c_t (t is empty), which is target kind T1. If y = BOARD(t, f) without a sail
    before it, f is docked at z with occupancy below k_f, kind T2. If an empty sail of f precedes y, f is empty in
    w and z ∈ `sail_to[f]`, kind T3. By F5 the drives from loc(t) to z form a shortest G_go path, so the first one
    satisfies d(m, z) = d(loc(t), z) − 1, as Rule D requires.

**Case η = 0.** (B) puts no constraint on the first action of ρ.

- *Forced.* If a truck of the active component stands at the goal of a package it carries, the generator emits only
  its canonical forced UNLOAD u (first such truck, first such package). If ρ does not start with u, replace ρ by
  ρ̂ of Lemma 2 for u.
- *Component order.* Otherwise move all actions of the active component c* to the front of ρ, keeping their order.
  Actions of different components share no object, so this is legal (Lemma 1 of `SUCCESSOR_RULES_PROOF.md`). Runs
  stay contiguous because a run belongs to one component, and an empty sail and the BOARD after it belong to the
  same component. So (P1ρ) and (P4ρ) still hold.
- *The first action a of ρ is now emitted*, because it passes every filter of the η = 0 branch:
  - Rule C: a is not an action of a useless truck (F4).
  - Rule A: if a is an empty sail of f to X, (P4ρ) says the next action is a BOARD onto f by a truck standing at X
    in w. That truck acts, so it is not useless (F4), and the BOARD is legal with occupancy 0, so 0 < k_f.
  - Rule D: if a is a DRIVE of an empty truck t, the argument of the focus case applies word for word (it only uses
    (P1ρ) from a onward), giving a target of kind T1, T2 or T3 in w and the shortest-path condition.
  - (K): a non-forced UNLOAD happens at an anchor.
  - H3: if a is DISEMBARK(t, f) while t's code says "boarded, not yet sailed", then Π contains BOARD(t, f) and this
    DISEMBARK with no SAIL of f between them, contradicting F2.
  - (H): Π uses H-actions only.
  - Twins: Section 6.

**The new boundary condition.** Write ρ' = a·ρ'' for the (possibly rewritten) suffix whose first action a was
emitted, and η' for the history of the child. (Hρ), (Kρ), (P1ρ) and (P4ρ) hold for ρ'' because they hold for ρ'
and concern each action and the one after it inside the suffix. For (B):

- a is a DRIVE or LOAD of t: η' = focus(t, ·), and (P1ρ) applied to a gives (B).
- a is an empty sail emitted for the focus truck t: (B) for η said ρ' = a·BOARD(t, f)···. With H4 on, η' =
  need(f, t), and ρ'' starts with BOARD(t, f). With H4 off, η' = focus(t, prev), and ρ'' starts with BOARD(t, f),
  an action of t.
- a is an empty sail emitted from η = 0: with H4 on, η' = need(f, none), and (P4ρ) gives a BOARD onto f by a truck
  at the dock. With H4 off, η' = 0.
- otherwise η' = 0.

So J(α·a, ρ'') holds. ∎

## 6. Twins, renamings and merged states

**Twins inside Lemma 3.** When the generator emits a twin representative instead of the first action a of ρ, there
is a renaming σ of interchangeable objects (`SUCCESSOR_RULES_PROOF.md` Lemma 7, with Rule B classes if on) that
fixes w and maps a to the representative. The objects swapped are empty trucks at the same position, packages of
the same class at the same place, or empty ferries at the same dock. The object named by η is never swapped: the
focus truck acts itself, and in need(f, ·) the ferry f is fixed. So σ also fixes η. Replace ρ by σ(ρ). It is legal
from w with the same cost and keeps (Hρ), (Kρ), (P1ρ), (P4ρ) and (B), because σ preserves goals, weights,
capacity classes, served ports and positions, and maps runs to runs.

**Merged states.** `_canon` now returns the old key plus a description of η through the objects it names: for
focus(t, prev), the descriptor of t (position, class, cargo classes) and prev. For need(f, t), the class and dock
of f and the descriptor of t (or none). Ferry manifests also record each aboard truck's "sailed" bit when H3 is on.
Two extended states have equal keys exactly when a class-preserving renaming τ maps one to the other, history
included.

**Lemma 4.** V_G(τ(x)) = V_G(x) for every such renaming.

*Proof.* Compare the successors the generator emits in x and in τ(x).

1. *Filters.* Every filter reads only classes (capacities through c̄, weights and goals through package classes,
   ferry classes), positions, the static anchors, the static map data, and the history, which τ maps along with
   the objects it names. No filter reads a truck's initial position. (H2 compares the action itself with
   DRIVE(t, loc(t), prev). The first version compared the child's position with prev and so read the initial
   position after a `_finish` reset. Section 10 records this bug.) So, apart from the choices in 2 and 3, the
   emitted actions in τ(x) are the τ-images of those in x.
2. *Twin representatives* are chosen by index. The τ-image of a representative is a twin of the representative
   chosen in τ(x), so both lead to states with equal keys.
3. *Forced unloads* are chosen by index. Let F be the set of pending forced unloads in x (trucks of the active
   component standing at the goal of a package they carry). Unloading moves no truck, so no new forced unload
   appears while F is executed. If η = 0 and F is non-empty, the generator emits one member of F, the child has
   η = 0, and so the generator keeps emitting members of F, one per step, until F is empty. If η = focus(t, ·) and t
   has a member of F, the generator emits it, the child has η = 0, and the same continues. Members of F commute
   (different trucks share no object, and two unloads from one truck commute because UNLOAD does not read the
   load). So in x and in τ(x) the same set of unloads, up to τ, is executed at the same cost, and the two final
   states are related by τ.
4. *The `_finish` reset* happens at the delivery that completes the active component, whatever the order. It puts
   every truck and ferry of that component at its own initial position. So the children of x and of τ(x) agree
   exactly on the finished component and are related by τ everywhere else. The renaming that is τ outside the
   finished component and the identity on it is again class-preserving, so the two children have equal keys.

So V_G(τ(x)) ≤ V_G(x) by induction on the number of actions of a cheapest G-path from x (a block of forced
unloads as in 3 counts as |F| actions, and both sides are infinite if one is). Applying this to τ⁻¹ gives the
other inequality. ∎

**A* with merging.** The supplied `graph_search` keeps one extended state per key, reopening it when it is reached
at a smaller g. By Lemma 4, all members of a key class have the same V_G. The usual A* argument then applies to
classes. Before the goal is popped, some open node lies on a path of cost V_G(x0) (if its class was closed with a
smaller or equal g, the closed member has the same V_G and its successors continue such a path). Consistency of h
is not needed.

## 7. Admissibility for the graph that is searched

For every reachable extended state x on which h is evaluated: 0 ≤ h(x) ≤ V(π(x)) ≤ V_G(x), and h = 0 at a goal.
The first inequality is Theorem 1 of `ADMISSIBILITY_PROOF.md` for the physical state π(x), including its Lemma 13,
which covers values reused from the regional cache under any cache history. The second holds because every path of
G is a legal world plan of the same cost: emitted actions are world-legal, and the `_finish` reset only moves
vehicles of a completed component, which no later action of an optimal completion needs. So h is admissible for G.

## 8. Main theorem and covered switch combinations

**Theorem 1.** With `OPT_FOCUS` on, and each of `OPT_UTURN`, `OPT_FRESH`, `OPT_NEEDBOARD`, `OPT_CORRIDOR`,
`OPT_EMPTY_SAIL`, `OPT_EFFCAP`, `OPT_USELESS` and `OPT_TOWARD` on or off, the supplied A* returns a plan of cost
V(s0) if the instance is solvable, and None if it is not.

*Proof.* If the instance is unsolvable, no path of G reaches a goal (every path is a legal world plan), and A*
exhausts the finite graph and returns None. Otherwise, by induction with Lemma 3, starting from J(empty, π*),
the generator emits every action of an optimal plan (possibly rewritten along the way), so V_G(x0) ≤ V(s0). With V_G ≥ V this gives V_G(x0) = V(s0). Sections 6 and 7
give an optimal search on G with merging. A switched-off rule only removes a filter, and every case of Lemma 3 shows
that the action is emitted with the filter present, so it is emitted without it too. With `OPT_NEEDBOARD` off, the
need history is not recorded. With `OPT_UTURN` off, the focus code still records prev, so keys are finer than
needed. That is harmless: no filter reads prev, and Lemma 4 holds for the finer keys because τ maps the history
together with the objects it names. ∎

**Focus off.** With `OPT_FOCUS` off, η is always 0 (H2 and H4 need H1). Rules H3 and K and Rules A to D remain.
Use the invariant J without (P1ρ), (P4ρ) and (B), which are not needed when η is always 0. The forced case is
Lemma 2. Otherwise apply Lemma 6 of `SUCCESSOR_RULES_PROOF.md` to ρ (optimal from w, H-actions only): it gives a free action x of ρ in the active
component that passes Rules A, C and D. Moving it to the front (Lemma 2 of that document) changes no location of
any load or unload, so (Kρ) is kept. If x were a fresh DISEMBARK, Π would contradict F2. So x is emitted, and the
induction goes through.

**History off.** With `OPT_HISTORY` off and `OPT_CORRIDOR` off (and `OPT_BARREN`, `OPT_PARTIAL_ORDER` off), the
generator is the one of `SUCCESSOR_RULES_PROOF.md`, which even satisfies condition (2).

**Partial-order pruning** is outside this proof. The constructor builds it only when Rules A to D, every history
rule, H3 and the corridor rule are all off.

## 9. Implementation correspondence

- `state[0]` holds η. Codes: 1 + t·(n+1) + prev (prev = n for none), and need_base + f·(T+1) + (t+1 or 0), with
  need_base = 1 + T·(n+1). Set in `_truck_standing` (DRIVE, LOAD), in `_history_successors` (empty sail for the
  focus truck) and in the ferry loop of `_successors` (empty sail from η = 0). Every other child gets 0, including
  `_finish`.
- `_history_successors` implements the need and focus branches of Section 2. H2 compares the action string
  with `DRIVE{t,loc,prev}`. `_successors` implements η = 0, with
  H3 in the DISEMBARK branch. BOARD stores the even "boarded, not yet sailed" code when H3 is on, and the unchanged
  `_sail` turns it odd.
- `_canon` appends the history description and, with H3, the sailed bit (Section 6). Incremental canonicalization
  is bypassed whenever history or H3 is on.
- `h_astar` drops η from its cache key. `_h`, `_bound` and everything below them are unchanged.
- `OPT_PARTIAL_ORDER` stays off (forced off by the new rules).

## 10. Implementation evidence (not part of the proof)

`tools/validate_rules.py --mode1` builds every extended state the generator can reach on small random instances,
checks that every action is legal and that every child equals the world successor except for vehicles of a
component with no undelivered package (the `_finish` reset), that h never exceeds the world optimum, that the pruned
optimum from the initial state equals the world optimum, and that the real A* returns a legal plan of that cost.
Fourteen switch configurations per instance: all rules on, each history rule off in turn, and all history off, each
with Rules A to D on and off. A quarter of the instances are two independent sub-problems side by side.

**Revision 3 (this document).** The checker now also requires equal pruned optima for reachable states with equal
canonical keys (Lemma 4 directly), and its per-state mode switches history and corridors off in the checked file.

| Run | Result |
|---|---|
| seeds 0 to 199 | 2,704 ok, 96 skipped, 0 failures, 3,469,038 states checked |
| seeds 2000 to 2049, larger | 611 ok, 89 skipped, 0 failures, 1,397,827 states checked |
| Astra's two instances (`tools/regress_cases.py`) | both ok (both fail on revision 1, the second at the key check) |
| this file, per-state mode (history and corridor off), seeds 3000 to 3099 | 1,560 ok, 40 skipped, 0 failures |
| Rule B with huge weights (Astra's 2^80 instance, 3,000 brute-force lists) | exact, no overflow |
| 25 instances with every weight and capacity times 10^7 | same optimal costs |

Revision 2 (same code apart from Rule B's overflow fix, checker without the key test): seeds 0 to 299, 4,057 ok,
0 failures, and seeds 2000 to 2099 larger, 1,269 ok, 0 failures.

**The bug in revision 1, found by Astra's audit.** H2 dropped every child in which the focus truck stood at prev.
A forced UNLOAD that completes a component triggers the `_finish` reset, which puts the component's trucks back at
their initial positions. If the focus truck had started at prev, the UNLOAD was dropped. On two road components with
no ferry the solver returned None on a solvable instance, and a second instance gave two states with the same key
and different pruned optima, so Lemma 4 was false for that code. The step that failed in the old Lemma 3 was "H2
removes only DRIVE(t, loc, prev)", which the code did not implement, and the old Lemma 4 never looked at the reset.
Revision 2 compares the action string (Section 9), and Lemma 4 now handles the reset in step 4.

**Why the checker missed it.** Its random instances rarely had several components in which a truck finishes its
component next to its start. The checker now draws a quarter of its instances as two independent sub-problems and
uses the stricter child check above. On the revision-1 file it reports 40 failures in seeds 0 to 59. Revision 1's
earlier clean runs (seeds 0 to 29, 100 to 399, 1000 to 1149, and 6000 to 6079 larger) used the old checker and are
superseded by the table above.

**An earlier bug, found by the checker during development:** with H1 on and H4 off, the empty-sail exception of the
focus branch was missing, so a truck that had driven to a port could never get its ferry. It was fixed before
revision 1.

## 11. Not claimed

- The per-state condition (2) is not claimed, and is false for these rules by design. Smallest example (Astra):
  road 0-1-2, capacity-one trucks at 0 and 2, one unit package at 0 going to 1. After the truck at 2 drives to 1,
  the world optimum is 3 but focus lets only that truck act, so the pruned optimum is 4. The TA's own example rule
  ("don't apply x right after y if they are independent and x has a lower index") also gives 4 at the same state
  when the first truck's actions are indexed first (`tools/ta_rule_example.py`). That places his example under (1)
  too. It is not an endorsement of H1, which is a different rule (right after the first truck's LOAD, his order
  lets the other truck drive, and H1 does not).
- No speed-up is claimed by the proof. Measurements are in the change notes.
