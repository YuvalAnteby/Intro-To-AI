# Successor rules A to D: definitions and proofs

Status: implemented on 2026-11-20 in `ex1.py` (switches on by default), as described in Section 10. Revision 2
(after Astra's audit): scope stated explicitly, ferry predicate 0 < k_f, component membership in Lemma 7.
Revision 3 (after Astra's recheck): Q restricted to component-respecting states, the gate and the ferry test stated
as the code has them, and Rule B computed exactly for any integer size (Lemma 7′ in Section 10).

**Scope of the per-state theorem.** Theorem 1 holds with `OPT_HISTORY`, `OPT_CORRIDOR`, `OPT_BARREN` and
`OPT_PARTIAL_ORDER` all off. With history or corridor rules on, only the initial-state statement of
`HISTORY_RULES_PROOF.md` holds, and the per-state statement is false by design.
No test result is used anywhere in the proofs. Implementation checks and measurements are in
`SUCCESSOR_RULES_CHANGE_NOTES.md`.

## 0. Summary

Four additions to the successor function, each behind its own switch:

| Rule | Proposed switch | What it changes |
|---|---|---|
| A. Lazy empty sails | `OPT_EMPTY_SAIL` | A ferry with no truck aboard may sail only to a port where a truck that is not useless is standing. |
| B. Effective capacities | `OPT_EFFCAP` | Trucks whose capacities allow exactly the same loads, and ferries whose capacities allow exactly the same boardings, get the same class. The twin rule and state merging then apply to more objects. No successor is removed directly. |
| C. Useless trucks rest | `OPT_USELESS` | No action is generated for an empty standing truck that cannot carry any undelivered package of its component. |
| D. Purposeful empty drives | `OPT_TOWARD` | An empty standing truck may drive only along the first edge of a shortest road path to a place where it could LOAD or BOARD in the current state, or to a port that a currently empty ferry could sail to. |

**What is proved (Theorem 1, Section 8).** For every state the search can generate, the cheapest goal-reaching
continuation inside the pruned graph costs exactly as much as the cheapest continuation in the unrestricted
world. This is the per-retained-state standard used in `PARTIAL_ORDER_PROOF.md` §1. It holds for every on/off
combination of the four switches, together with the existing rules exactly as they are now.

**What does not change.** `h_astar` and everything it calls, `path_cost`, `goal_test`, the canonical key
construction (only the class tags it reads change under Rule B), the forced-goal-UNLOAD branch, and the legality
checks (they keep using the real capacities).

**Scope.** The new rules are switched on only when `integer_cargo` holds (integer weights and capacities), the
same condition the existing code already uses for its exact-weight reductions. `OPT_PARTIAL_ORDER` is forced off
whenever any new rule is on, because its proof assumes the old list of raw successors.

## 1. Approaches considered

1. **State-based normal forms proved by delaying actions** (chosen). Each rule reads only the current physical
   state, so a retained state never inherits a restriction from the path that reached it. That is exactly what the
   per-state standard needs.
2. **History-based normal forms** (truck focus, U-turn ban, last-action ordering, pending ferry). By
   construction they restrict a state according to how it was reached, so they fail the per-state standard.
   Excluded.
3. **Strong stubborn sets.** Already implemented as `OPT_PARTIAL_ORDER` and measured slower. Not extended here.

## 2. Setting and facts reused from the existing proofs

### 2.1 States, actions, costs

The model is the one in `ADMISSIBILITY_PROOF.md` §1. For a state q:

- pos(t) is the location where truck t stands, or "aboard f",
- dock(f) is the port where ferry f is docked,
- pos(p) is the location where package p lies, or the truck that carries it,
- load(t) = Σ { w_p : pos(p) = t } and occ(f) = |{ t : pos(t) = aboard f }|.

Truck t has capacity c_t, ferry f has truck capacity k_f and served ports L_f, package p has weight w_p ≥ 1 and
goal g_p. A package is **delivered** if it lies at its goal, **undelivered** otherwise. SAIL costs 3, every
other action costs 1. V(q) is the cost of a cheapest legal goal-reaching continuation from q in the world (∞ if
none). A continuation π from q is **optimal** if its cost is V(q) < ∞.

### 2.2 The graph H and retained states

Following `PARTIAL_ORDER_PROOF.md` §3, H is the world transition graph without: LOAD of a package lying at its
goal, DRIVE in a direction (x, y) with y ∉ `adj_go[x]`, SAIL of f to a port outside `sail_to[f]`, and any action
of a disabled ferry (`fdead`). An **H-action** is a world-legal action that H keeps.

A state is **retained** if it is obtained from the initial state by H-actions, interleaved with the
completed-component write-back `_finish`. Every action the new generator emits is an H-action (Section 10), so
every state it produces is retained in this sense.

The existing proofs supply three facts. They depend only on invariants that hold in every retained state as
defined here (dead sides hold no truck and no package, removed islands stay empty).

- **E1** (`PRUNING_PROOF.md` §4, also `PARTIAL_ORDER_PROOF.md` §8). If a standing truck carries a package whose goal is its current location, then
  an UNLOAD of such a package starts an optimal continuation.
- **E2** (`PARTIAL_ORDER_PROOF.md` §9). For every retained state s with V(s) < ∞, some optimal continuation from
  s consists of H-actions only.
- **E3** (`PARTIAL_ORDER_PROOF.md` §9.5). The write-back `_finish` does not change V.

### 2.3 Components

Every truck, ferry, location and package belongs to one connected component of the auxiliary map graph
(locations, ferries, roads, port edges), written comp(·). Nothing ever leaves its component. Let c*(s) be the
lowest-ranked component that still has an undelivered package. The generator always emits the actions of c*(s)
that survive its filters (with `OPT_COMP` off it may emit others as well, which does no harm).

## 3. The rules

**Definition 1 (useless truck).** Truck t is *useless* in state s if it is standing, carries nothing, and every
undelivered package p with comp(p) = comp(t) has w_p > c_t.

**Definition 2 (Rule A).** Let ferry f have occ_s(f) = 0 and dock u. The action SAIL(f, u, X) is generated only
if 0 < k_f and some truck that is not useless in s is standing at X. (`integer_cargo` checks weights and truck
capacities, not ferry capacities, so the predicate is written as the code tests it. For an integer k_f it means
k_f ≥ 1.)

**Definition 3 (Rule B).** For truck t let W(t) be the set of all sums Σ_{p ∈ S} w_p over subsets S of the
packages of comp(t) (the empty sum 0 included), and let

  c̄_t = max { v ∈ W(t) : v ≤ c_t }.

For ferry f let N_f be the number of trucks in comp(f) and k̄_f = min(k_f, N_f). Under Rule B the truck class tag
`tcls[t]` becomes c̄_t, and the ferry class key becomes (L_f, `gports[f]`, `sail_to[f]`, `fdead[f]`, k̄_f). The
package classes are unchanged. Every legality check keeps the real c_t and k_f.

**Definition 4 (Rule C).** No action of a truck that is useless in s is generated in s.

**Definition 5 (targets and Rule D).** Let t be a truck standing empty in s at location l. Its *targets*
Tgt_s(t) are the locations z of comp(t) of these three kinds:

- **(T1)** z is where some undelivered package p lies in s, with w_p ≤ c_t.
- **(T2)** z = dock_s(f) for a ferry f of comp(t) that is not disabled and has occ_s(f) < k_f.
- **(T3)** z ∈ `sail_to[f]` for a ferry f of comp(t) that is not disabled and has occ_s(f) = 0 and 0 < k_f.

Let d(x, z) be the length of a shortest directed path from x to z in the road graph G_go whose edges are
x → y for y ∈ `adj_go[x]` (∞ if none). **Rule D:** for such a truck t at l, DRIVE(t, l, m) is generated only if
some z ∈ Tgt_s(t) has d(l, z) < ∞ and d(m, z) = d(l, z) − 1.

### 3.1 Why target kind (T3) is required

Without (T3), Rules A and D together are wrong, even from the initial state. Take locations 0, 1, 2, one road
{1, 2}, ports {0, 2}, one ferry f docked at 0 with L_f = {0, 2} and k_f = 1, one truck t at 1 with c_t = 1, and
one package p at 0 with weight 1 and goal 1. The only way to deliver p is: t drives to 2, f sails to 2, t boards,
f sails to 0, t disembarks, loads p, boards, f sails to 2, t disembarks, drives to 1, unloads (cost 17).

In the initial state, no truck stands at 2, so Rule A forbids the empty sail to 2. The only package lies at 0 and
the only dock is 0, neither reachable by road from 1, so without (T3) Rule D forbids t's drive. Nothing else is
applicable, so the pruned graph has no successor at all. With (T3), port 2 is a target of t (f is empty and
serves 2), t drives to 2, and then Rule A allows f to sail to 2. The proof below shows that (T3) is all that is
needed: in the case where the first useful move is "an empty truck drives toward a port that an empty ferry will
reach later", the drive is allowed by (T3).

## 4. Independence and swapping

**Definition 6.** The objects of an action are: DRIVE(t, x, y) → {t}, LOAD(p, t) and UNLOAD(p, t) → {p, t},
BOARD(t, f) and DISEMBARK(t, f) → {t, f}, SAIL(f, x, y) → {f}. Two actions are *independent* if their object sets
are disjoint.

**Lemma 1 (swap).** Let a, b be independent, let a be applicable in q and b applicable in a(q). Then b is
applicable in q, a is applicable in b(q), and a(b(q)) = b(a(q)).

*Proof.* What each action reads and writes, besides static data (roads, served ports, weights, capacities):

| Action | Writes | Reads |
|---|---|---|
| DRIVE(t, x, y) | pos(t) | pos(t) |
| LOAD(p, t) | pos(p) | pos(p), pos(t), load(t) |
| UNLOAD(p, t) | pos(p) | pos(p), pos(t) |
| BOARD(t, f) | pos(t) | pos(t), dock(f), occ(f) |
| SAIL(f, x, y) | dock(f) | dock(f) |
| DISEMBARK(t, f) | pos(t) | pos(t), dock(f) |

The physical place of a carried package or of a truck aboard a ferry is not a separate component. It is derived
from pos(t) and dock(f) and is read only through the entries above. load(t) changes only when some pos(q) changes
from t or to t, that is, through LOAD(q, t) or UNLOAD(q, t), and both have t among their objects. occ(f) changes
only through BOARD(·, f) or DISEMBARK(·, f), and both have f among their objects.

So everything b reads is either pos or dock of an object of b, or load or occ of a truck or ferry of b. Action a
writes only pos or dock of its own objects, which are not objects of b, and it cannot change load or occ of an
object of b, since that would require b's truck or ferry among a's objects. Hence b's applicability and b's
written values are the same in q and in a(q). The same holds with a and b exchanged. The two actions write
disjoint components, so both orders end in the same state. ∎

**Definition 7.** In a continuation π = a_1 … a_k, the action a_i is *free* if it is independent of every a_j
with j < i.

**Lemma 2 (moving a free action to the front).** If a_i is free in π, then π' = a_i a_1 … a_{i−1} a_{i+1} … a_k
is legal from the same state, is in the same state as π after the first i actions, and costs the same. In
particular π' is optimal if π is.

*Proof.* i − 1 swaps of adjacent independent actions, each allowed by Lemma 1. ∎

Objects of different components are distinct, so any two actions of different components are independent.

## 5. Properties of optimal continuations

In Sections 5 and 6, fix a retained non-goal state s with V(s) < ∞ and, by E2, an optimal continuation π from s
that consists of H-actions only. Every claim below says that π cannot look otherwise, because otherwise a legal
world continuation cheaper than V(s) would exist.

**Lemma 3 (useless trucks never act).** If t is useless in s, no action of π has t among its objects.

*Proof.* First, t never loads. As long as t is empty, LOAD(p, t) requires w_p ≤ c_t and requires p to lie where
t stands. Since π consists of H-actions, p is not lying at its goal at that moment. If p were delivered in s, it
would never move afterwards (an H-action never loads a package lying at its goal), so it would still lie at its
goal, a contradiction. So p is undelivered in s and lies in comp(t), hence w_p > c_t by uselessness, and the LOAD
is illegal. By induction along π, t stays empty, and so it never unloads either. Its actions in π are therefore
DRIVE, BOARD and DISEMBARK only.

Delete all of them. Among the remaining actions, nothing reads pos(t) (Lemma 1 table, t is not their object). The
only other effect of deleting t's actions is on occ(f) for ferries t would have boarded, which can only become
smaller, and BOARD needs occ(f) < k_f, so every remaining BOARD stays legal. SAIL does not test occupancy. t
carries no package, so every package ends where it ended before. The shorter continuation is legal, reaches the
goal, and is cheaper if t had any action. Since π is optimal, t had none. ∎

**Lemma 4 (empty ferries).** Let f be a ferry with occ_s(f) = 0. In π, the actions of f before its first BOARD
(all of them if there is none) are SAIL actions, and there is at most one. If there is one, call it σ_f. Then f
has a later BOARD, and the first action of f after σ_f is a BOARD.

*Proof.* Only BOARD(·, f) puts a truck aboard f, so f is empty until its first BOARD and no DISEMBARK(·, f) can
occur before it. Its earlier actions are therefore SAILs.

If f has at least one SAIL and no BOARD, delete all its SAILs. Only actions with f among their objects read
dock(f), and there are no others. The goal does not mention ferries. The result is legal and cheaper.

If f has at least two SAILs before its first BOARD, let the first two be S1 = SAIL(f, u, x) and
S2 = SAIL(f, x, y). Delete S1, and replace S2 by SAIL(f, u, y) if y ≠ u or delete it if y = u. Between S1 and S2
nothing reads dock(f). After the position of S2, dock(f) = y in both continuations. SAIL(f, u, y) is legal because
y ∈ L_f and y ≠ u. The result costs 3 or 6 less.

Both cases contradict optimality. So there is at most one SAIL before the first BOARD, a BOARD exists if a SAIL
does, and the first f-action after σ_f is that BOARD. ∎

**Lemma 5 (empty standing trucks).** Let t be standing and empty in s, at location l. Let E_t be the maximal
initial run of DRIVE actions in the sequence of t's actions in π. If E_t is not empty, then:

- **(a)** t has an action after E_t. Call the first one y_t. It is LOAD(p, t) or BOARD(t, f).
- **(b)** Let z be t's location at y_t. Then |E_t| = d(l, z), and the first action DRIVE(t, l, m) of E_t
  satisfies d(m, z) = d(l, z) − 1.

*Proof.* (a) If t had no action after E_t, delete E_t. Nothing else reads pos(t), and t carries nothing, so the
result is legal, reaches the goal and is cheaper. So y_t exists. By maximality it is not a DRIVE. During E_t, t
stays standing and empty, so y_t cannot be UNLOAD (nothing carried) or DISEMBARK (not aboard).

(b) E_t is a walk from l to z in G_go, since π uses only H-actions. Suppose |E_t| > d(l, z). Remove E_t and
insert a shortest G_go path from l to z immediately before y_t. Nothing other than t's own actions reads pos(t),
and t's only actions before y_t were E_t. Until the inserted drives, t stands at l, and the drives are legal road
moves. At y_t, t stands at z as before. Every other action reads exactly what it read before. The result is legal
and cheaper, a contradiction. So |E_t| = d(l, z).

The walk minus its first edge is a walk from m to z of length d(l, z) − 1, so d(m, z) ≤ d(l, z) − 1. The edge
l → m gives d(l, z) ≤ 1 + d(m, z). Hence d(m, z) = d(l, z) − 1. ∎

## 6. The main lemma

**Lemma 6.** π has a free action x such that:

1. the objects of x belong to c*(s), and x is an H-action,
2. x is not an action of a useless truck,
3. if x is a SAIL of a ferry f with occ_s(f) = 0, then x satisfies Rule A,
4. if x is a DRIVE of a truck standing empty in s, then x satisfies Rule D.

*Proof.* Write c* for c*(s). Let π_c be the subsequence of π formed by the actions whose objects belong to c*.
Define the **early set** D as the union of:

- E_t, for every truck t of c* that is standing and empty in s (Lemma 5),
- σ_f, for every ferry f of c* with occ_s(f) = 0 for which σ_f exists (Lemma 4).

Every member of D is a DRIVE or a SAIL. Component c* has an undelivered package, and every undelivered package is
unloaded at least once in π, so π_c contains an UNLOAD, which is not in D. Let y be the first action of π_c that
is not in D. Every action of π before y belongs to another component (and is independent of y) or belongs to D.

Properties 1 and 2 hold for every action of π_c: π consists of H-actions, and Lemma 3 says useless trucks have no
actions in π. So only properties 3 and 4 need care.

**Case 1: y is independent of every earlier member of D.** Then y is free. Take x = y.

- If y is a SAIL of a ferry f with occ_s(f) = 0: y ∉ D, so y is not σ_f, so by Lemma 4 y comes after f's first
  BOARD. That BOARD belongs to π_c, is not in D, and precedes y, which contradicts the choice of y. So this cannot
  happen, and property 3 holds vacuously.
- If y is a DRIVE of a truck t standing empty in s: y ∉ E_t, so y comes after t's first non-DRIVE action. That
  action belongs to π_c, is not in D, and precedes y, a contradiction again. So property 4 holds vacuously.

**Case 2: y shares an object with an earlier member d of D.**

- If d ∈ E_t, then t is an object of y. All actions of t before y belong to π_c and precede y, so they are in D,
  and the members of D that involve t are exactly the drives of E_t. So y is the first action of t after E_t,
  that is y = y_t, which by Lemma 5(a) is LOAD(p, t) or BOARD(t, f).
- If d = σ_f, then f is an object of y. The actions of f before y are in D, and the only member of D involving f
  is σ_f. So y is the first action of f after σ_f, which by Lemma 4 is a BOARD(t', f).

So y = LOAD(p, t) with E_t non-empty, or y = BOARD(t, f).

**Case 2a: y = LOAD(p, t), E_t non-empty.** Package p has no action before y, because such an action would be
a LOAD or UNLOAD of π_c before y, and those are never in D. So p lies at the same place in s as at y, which is z,
the location of t at y. Let x be the first action of E_t, a DRIVE(t, l, m). It is t's first action and its only
object is t, so x is free. Kind (T1) holds for z: p lies at z in s, it is undelivered (an H-action LOAD never
takes a package lying at its goal, and p has not moved since s), and w_p ≤ c_t because t is empty at y, its
earlier actions being drives. By Lemma 5(b), d(l, z) < ∞ and d(m, z) = d(l, z) − 1. So x satisfies Rule D.

**Case 2b: y = BOARD(t, f).** The actions before y that share an object with y are, for t, the drives of E_t
(any other earlier action of t would be outside D), and, for f, at most σ_f. By the case assumption at least one
of them exists. Let z be dock(f) at y, which is also t's location at y.

- *(i) E_t is non-empty.* Let x be the first action of E_t, which is free as in Case 2a. If σ_f precedes y, then
  occ_s(f) = 0, σ_f sails to z, z ∈ `sail_to[f]` (σ_f is an H-action), f is not disabled (it acts in π), and
  0 < k_f because y is legal with occ(f) = 0 at y. So z is of kind (T3). If σ_f does not precede y, then f has no
  action before y, so dock_s(f) = z and occ_s(f) = occ(f) at y < k_f, and f is not disabled. So z is of kind (T2).
  In both cases Lemma 5(b) gives d(m, z) = d(l, z) − 1, so x satisfies Rule D.
- *(ii) E_t is empty.* Then t has no action before y: if t is standing and empty in s, its first action is not a
  drive, and any earlier action would be outside D. If t is not standing and empty in s, it has no early actions
  at all, and any earlier action would again be outside D. So t stands in s where it stands at y, namely at z.
  Since some earlier member of D shares an object with y, σ_f precedes y, and by Lemma 4 y is f's first action
  after σ_f, so σ_f sails to z. Let x = σ_f. It is f's first action (Lemma 4) and its only object is f, so it is
  free. Rule A holds: occ_s(f) = 0, truck t stands at z in s and is not useless (it acts in π, Lemma 3), and
  0 < k_f because y is legal with occ(f) = 0.

In every case x is free and has properties 1 to 4. ∎

## 7. Rule B and the twin representatives

**Lemma 7 (effective capacities).** Let Q be the set of states in which every object lies in its initial
component, load(t) ∈ W(t) and load(t) ≤ c_t for every truck t. Then:

- **(a)** Q contains every retained state and is closed under legal actions and under `_finish`.
- **(b)** For q ∈ Q, truck t standing in q and package p lying where t stands, LOAD(p, t) is legal in q if and
  only if load_q(t) + w_p ≤ c̄_t.
- **(c)** For q ∈ Q, ferry f and truck t of comp(f) standing at dock_q(f), BOARD(t, f) is legal in q if and only
  if occ_q(f) < k̄_f.
- **(d)** Let τ be a bijection of the objects that maps every truck to a truck of the same component with equal
  c̄, every ferry to a ferry with the same Rule B class key, and every package to a package with the same weight
  and goal. Then for all q ∈ Q: τ(q) ∈ Q, an action a is a legal H-action in q if and only if τ(a) is a legal
  H-action in τ(q), τ(a(q)) = τ(a)(τ(q)), the costs of a and τ(a) are equal, and q is a goal if and only if τ(q)
  is. Hence V(τ(q)) = V(q), and τ maps optimal continuations from q to optimal continuations from τ(q).

*Proof.* Objects never leave their component (`ADMISSIBILITY_PROOF.md` Lemma 0(c)), so a package that a truck
can load lies at the truck's location and belongs to the truck's component. W(t) is built from exactly those
packages.

(a) Initially and after `_finish` the trucks concerned are empty (load 0 ∈ W). LOAD(p, t) adds w_p for a
package p that was lying, so not already in t, and that lies in comp(t). The new load is again a subset sum, and
it is ≤ c_t by legality. UNLOAD removes one summand. Other actions do not change loads.

(b) load_q(t) + w_p is a sum over a subset of the packages of comp(t), so it lies in W(t). If it is ≤ c_t, it
is ≤ c̄_t by the definition of c̄_t as a maximum. Conversely, c̄_t ≤ c_t.

(c) t is standing, so it is not aboard f, and every truck aboard f belongs to comp(f). Hence occ_q(f) ≤ N_f − 1.
If k_f ≥ N_f, both conditions hold. Otherwise k̄_f = k_f.

(d) The legality of an action depends on positions (which τ transports), on the roads and served ports (static
and preserved by τ, since τ keeps L_f), on the LOAD capacity test (which by (b) depends only on c̄, preserved),
on the BOARD occupancy test (which by (c) depends only on k̄, preserved), and on H's restrictions: dead road
directions are static, and `sail_to` and `fdead` are part of the ferry class key, and "lying at its goal" is
preserved because τ keeps goals. Effects are positional, so they commute with τ. SAIL maps to SAIL, so costs agree.
The goal condition is preserved because τ keeps goals. τ(q) ∈ Q because τ keeps weights and W depends only on
the component. ∎

**The renamings the search uses.**

- *Twin rule.* The generator lets only one representative act among (i) empty trucks with the same position code
  and the same class, (ii) packages with the same class at the same place, (iii) empty ferries with the same class
  at the same dock. Swapping two such objects, or performing two such swaps at once when an action has two
  non-representative objects (for example BOARD(t, f) with both t and f replaced), is a bijection τ of the kind in
  Lemma 7(d) with τ(s) = s: the swapped objects occupy identical places, and swapped trucks or ferries carry
  nothing. Trucks at the same position
  are in the same component. With Rule B off, the classes are the raw capacities and the existing twin argument
  (`PRUNING_PROOF.md` §5) applies unchanged.
- *State merging.* Two states with equal canonical keys are related by a bijection τ matching objects with equal
  descriptors. A truck's descriptor contains its position, which determines its component, so τ is of the kind in
  Lemma 7(d).

**Lemma 8 (representatives keep the new rules).** Let x be an action of Lemma 6 and τ a twin renaming (one or
two swaps, as above) with τ(s) = s. Then τ(x) also has properties 1 to 4 of Lemma 6.

*Proof.* Property 1: τ preserves components and, by Lemma 7(d), H-actions. For the others, note that for a truck
t and package p of comp(t), w_p ≤ c_t if and only if w_p ≤ c̄_t, because w_p alone is a subset sum.

- *Uselessness* depends on standing, emptiness, the component and the tests w_p ≤ c_t over the undelivered packages
  of the component. τ preserves positions of equivalent objects, emptiness, components, and the multiset of
  (weight, goal, place) of packages, so it preserves uselessness. Property 2 follows.
- *Rule A for ferry f* depends on occ_s(f) = 0, 0 < k_f, `sail_to[f]` and the set of places of non-useless
  standing trucks. A swapped ferry f' has the same class key, so the same `sail_to`, and 0 < k_f if and only if
  0 < k̄_f when comp(f) has a truck (which Rule A requires, the standing truck at X). Non-integer ferry capacities
  get a class of their own, so no swap involves them. The set of places is
  preserved by τ. Property 3 follows.
- *Rule D for truck t* depends on l, Tgt_s(t) and G_go. (T1) depends on the lying undelivered packages and the
  tests w_p ≤ c_t, preserved as shown above. (T2) and (T3) depend on ferries of comp(t). A swapped ferry has the
  same class key and the same dock and occupancy (both empty, same dock), and since comp(t) contains t,
  occ < k_f if and only if occ < k̄_f by Lemma 7(c), and 0 < k_f if and only if 0 < k̄_f. So Tgt_s(τ(t)) =
  Tgt_s(t), and τ(t) stands at l as t does. Property 4 follows. ∎

## 8. Main theorem

**Theorem 1.** Let G be the graph produced by the new successor function, with any subset of Rules A, B, C, D
switched on, `OPT_HISTORY = OPT_CORRIDOR = OPT_BARREN = False`, and `OPT_PARTIAL_ORDER` off. For every retained state s,
the cheapest goal-reaching continuation from s in G costs V(s).

*Proof.* Every action G emits is world-legal, so V_G(s) ≥ V(s). For the converse, use induction on V(s), which is
a non-negative integer or ∞. If V(s) = ∞ there is nothing to show. If V(s) = 0, s is a goal.

Let V(s) > 0. If some standing truck carries a package whose goal is its location, the generator emits only a
forced UNLOAD, and by E1 it starts an optimal continuation. Otherwise, take π and x from Lemma 6 and move x to the
front (Lemma 2), giving an optimal continuation π' that starts with x. Before the new filters, the generator emits
every H-action of c* that is legal in s, except those removed by the twin rule (`OPT_CORRIDOR` and `OPT_BARREN`
are off). Action x passes Rules A, C and D by Lemma 6. If the twin rule removes x, there is a twin renaming τ
with τ(s) = s that maps x to the emitted representative τ(x). By Lemma 7(d), τ(π') is an optimal continuation from s
that starts with τ(x), and by Lemma 8, τ(x) passes Rules A, C and D as well.

In both branches the generator emits an action a that starts an optimal continuation, so its child s' = a(s),
after `_finish` if a component completes, satisfies V(s') = V(s) − cost(a) < V(s) (E3 for the write-back). The
child is retained, so by induction V_G(s') = V(s'), and V_G(s) ≤ cost(a) + V_G(s') = V(s). ∎

## 9. A* returns an optimal plan

Unchanged from `PARTIAL_ORDER_PROOF.md` §10, with Theorem 1 in place of its Sections 7 to 9.

- `ADMISSIBILITY_PROOF.md` gives h(s) ≤ V(s) for every retained state, and Theorem 1 gives V(s) = V_G(s), so h is
  admissible for the search that actually runs.
- States with equal canonical keys are related by a bijection of Lemma 7(d), so they have equal V, and Theorem 1
  applies to each representative separately. Merging them in `closed` therefore loses no optimal path.
- The supplied `graph_search` reopens a state reached with a smaller g, so consistency of h is not needed.

## 10. Implementation plan and correspondence

All changes are in `ex1.py`. Each rule has its own switch, and all four are active only if `integer_cargo` holds.

**Constructor (static data only, computed on the map).**

- Rule B: c̄_t computed by `_best_load` (Lemma 7′ below), from the weights of comp(t)'s packages that are at most
  c_t. k̄_f from the number of trucks per component. `tcls` set to c̄. The ferry classes recomputed after `_build_regions`, so that
  `sail_to` and `fdead` exist, with the key of Definition 3.
- Rule D: for every location z, a breadth-first search over the reversed G_go edges gives d(·, z). For every
  location l and every neighbour m in `adj_go[l]`, a bit mask `toward[l][m]` over locations, with bit z set when
  d(l, z) < ∞ and d(m, z) = d(l, z) − 1. A bit mask `sailmask[f]` of `sail_to[f]`. This is a plain BFS on the road
  map, which the assignment explicitly allows ("distances on the road network").
- `_por` is not built when any new rule is on.

**`_successors` (per expansion).**

- Rule C: the minimum weight of the undelivered packages of each component. A standing empty truck whose capacity
  is below that minimum is skipped before the twin check (its twins are useless too, so no representative is lost).
- Rule A: a bit mask of the locations where a non-useless truck stands. For a ferry with `aboard_count[f] == 0`,
  a destination b is kept only if `0 < fcap[f]` and bit b is set.
- Rule D: a ferry mask with dock bits for (T2) and `sailmask` bits for (T3). For each distinct capacity among the
  empty standing trucks, a (T1) mask from the `lying` lists (which already exclude delivered packages when
  `integer_cargo` holds). Ferries and packages of other components need no filtering in the masks: `toward` has
  bits only for locations reachable by road, which lie in the truck's own component. A drive l → m of an empty
  truck is kept only if `toward[l][m] & (T1 | ferry mask)` is non-zero. This replaces the inactive `adj_far` loop.
- The forced-UNLOAD branch returns before any of this, unchanged.

**Lemma 7′ (Rule B is computed exactly, with bounded memory).** Let t have integer capacity c ≥ 0 below the total
weight of comp(t)'s packages, and let ws be the list of those weights. Then `_best_load(c, [w ∈ ws : w ≤ c])`
returns c̄_t = max{Σ_{p∈S} w_p : S ⊆ packages of comp(t), Σ_{p∈S} w_p ≤ c}, or None.

*Proof.* Weights are integers ≥ 0 (the gate). A set S containing a package with w_p > c has sum ≥ w_p > c, so the
feasible sets are exactly the feasible subsets of the reduced list w_1, ..., w_m. Let A_i be the set of subset sums
of w_1, ..., w_i that are at most c. Then A_0 = {0} and A_{i+1} = A_i ∪ {v + w_{i+1} : v ∈ A_i, v + w_{i+1} ≤ c},
because a sum of a subset of the first i + 1 weights is v or v + w_{i+1} for a subset sum v of the first i, and
v + w_{i+1} ≤ c implies v ≤ c, so v ∈ A_i. The dense branch (c ≤ 2^20) keeps A_i as the bits of an integer
masked to bits 0..c, and the sparse branch keeps A_i as a set. Both implement this recursion, and c̄_t = max A_m.
Memory is bounded: the dense integer has at most 2c + 1 ≤ 2^21 + 1 bits, and every shift is by a weight
w ≤ c ≤ 2^20. The sparse set grows by at most a factor 2 per weight before the size test, so it never holds more
than 2^17 sums, and the branch returns None once it has more than 2^16. Each stored sum is at most c, so the set
takes O(2^17 · log c) bits, linear in the length of the input number c (the old code needed about c bits). When it
returns None for some truck, the constructor switches Rule B off for the instance and keeps the raw classes
(`tcls` = capacities, `fcls` from the constructor). Partial-order pruning stays off, since `new_rules` was already
set. That is one of the combinations Theorem 1 covers. ∎

**Correspondence checks to make on the code once written:** every new filter only removes entries from the
existing list (no new action kinds and no change to any legality test). The masks use exactly the sets of
Definitions 1, 2 and 5. The heuristic, `path_cost`, `goal_test` and the canonicalizer bodies are byte-identical.

**Implementation evidence (not part of the proof).** `tools/validate_rules.py`, an independent exhaustive
solver on small random instances, compares the pruned optimum with the world optimum on every state the new
generator can reach, for all 16 switch combinations. Results are in `SUCCESSOR_RULES_CHANGE_NOTES.md`.

## 11. Not claimed

- No speed-up is claimed. Rule C may never fire on a given instance, Rule B helps only when capacities differ but
  allow the same loads, and A and D help in proportion to how many children are empty sails and empty drives.
- The rules are proved for integer package weights and integer truck capacities only, and the code keeps them off
  otherwise (`integer_cargo`). Ferry capacities are not part of that gate: a non-integer ferry capacity leaves the
  rules on, and that ferry gets a Rule B class of its own, so no ferry swap involves it. Rule A tests `0 < fcap[f]`,
  which for an integer slot count is the same as `fcap[f] >= 1`.
- The proof relies on E1 to E3 as proved in the existing documents.
