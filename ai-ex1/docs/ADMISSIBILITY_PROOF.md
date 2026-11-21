# Admissibility proof for the heuristic in `ex1.py`

Version of 2026-11-19. This document replaces the earlier admissibility notes. It is self-contained: every
quantity that `h_astar` adds is defined here and proved to be a lower bound, including the parts inherited
from the previous version, which were re-derived from the assignment's rules and not assumed. No test
result is used anywhere.

Revision of 2026-11-19: the cache argument now proves preservation of a lower bound without assuming
that a cache hit equals a fresh evaluation. The heuristic implementation is unchanged.

## 0. Results

**Theorem 1 (admissibility).** For every legal state s reachable from the initial state, or obtained by
the completed-region write-back described in Section 16, `h_astar` returns an integer h(s) with
0 ≤ h(s) ≤ h\*(s), where h\*(s) is the cost of a cheapest plan from s (∞ if there is none). At a goal
state h(s) = 0. This holds for every cache history built from such states of the same problem instance;
equality between the returned value and a fresh evaluation is not required.

**Proposition 2 (comparison of fresh evaluations with the previous version).** For every state s in the
scope of Theorem 1, every term of the fresh-evaluation formula below is at least the corresponding term
of the previous `ex1.py`, except the merge and first-entry term xfer. Thus h_fresh(s) ≥ h_old,fresh(s)
whenever the previous fresh value was decided by its flow term (Section 15). This comparison does not
assert equality between a cached value and a fresh value.

Neither result uses consistency, the successor function or its pruning. Theorem 1 bounds h by the
optimal cost of the unpruned world. Pruning only removes options, so the optimal cost inside the pruned
search graph is never smaller, and h is admissible for the search that `ex1.py` actually runs as well.

**The formula for a fresh evaluation.** Let h_fresh(s) be the value obtained by evaluating each region
at s, without reusing `reg.cache`. Then

```
h_fresh(s) = H(s) + Σ over regions R of  M_R(s)
M_R  = ⌈ T2 / 2 ⌉ + max( xfer, flow )
T2   = 2·Σ_{road bridges e} g_e  +  Σ_{port bridges e} c2_e  +  Alt
Alt  = max( piece2 + road2 + bal2 ,  frac2_all )      when the fractional tables are not all zero
     = piece2 + cyc2 + bal2                            otherwise
road2 = max( frac2_road , cyc2 )
```

Names ending in 2 are in doubled units (twice a cost), so that half-sails stay integral. H is Lemma 1,
g_e Lemma 2, c2_e and piece2 Lemma 5, bal2 Lemma 6, frac2_road and frac2_all Lemma 7, cyc2 Lemma 8,
flow Lemma 9, and xfer Lemmas 10 and 11.

A hit in the coarse, single-region `reg.cache` may reuse a cycle-center selection from another state
with the same key. Section 16 proves that this preserves the bound on the same action costs, so the
returned h(s) is admissible even when its equality to h_fresh(s) has not been established.

---

## 1. The model used in the proof

An instance has locations 0, …, n−1, roads (unordered pairs {x, y} with x ≠ y), trucks, ferries and
packages. Truck t has capacity c_t. Ferry f serves the port set L_f, carries at most k_f trucks and starts
docked at d_f. Package p has weight w_p and goal g_p. The supplied course-staff answer states w_p ≥ 1
and that every ferry starts at a port it serves; it does not explicitly state that weights are integers.
The core derivation below uses integer weights w_p ≥ 0 and integer capacities. Section 16 covers the
code's relaxation for other numeric inputs, so the admissibility conclusion does not require an
unconfirmed integrality assumption about the input weights or capacities.

A state says, for every truck, whether it stands at a location or is aboard one ferry, for every ferry, the
port where it is docked, and for every package, whether it lies at a location or is inside one truck.

The actions, exactly as in the assignment:

| action          | cost | precondition                                                           | effect                                      |
| --------------- | ---- | ---------------------------------------------------------------------- | ------------------------------------------- |
| DRIVE(t, x, y)  | 1    | t stands at x, {x, y} is a road                                        | t stands at y                               |
| LOAD(p, t)      | 1    | t stands where p lies, load(t) + w_p ≤ c_t                             | p is inside t                               |
| UNLOAD(p, t)    | 1    | p is inside t, t stands                                                | p lies at t's location                      |
| BOARD(t, f)     | 1    | t stands at the port where f is docked, fewer than k_f trucks aboard f | t is aboard f                               |
| SAIL(f, u, w)   | 3    | f is docked at u, w ∈ L_f, w ≠ u                                       | f is docked at w, trucks aboard stay aboard |
| DISEMBARK(t, f) | 1    | t is aboard f                                                          | t stands at f's dock                        |

load(t) is the total weight inside t. The goal: every package lies at its goal.

The search only gives `h_astar` states that are reachable from the initial state (the only exception, the
component write-back of the successor function, is covered in Section 16). Trucks start empty and only
LOAD adds weight, so in every such state load(t) ≤ c_t. Four facts are used repeatedly:

- **(M1)** A lying package does not move. A package inside a truck moves exactly with the truck.
- **(M2)** A package is loaded only at the location where it lies, by a truck t standing there, and then
  c_t ≥ load(t) + w_p ≥ w_p.
- **(M3)** LOAD and UNLOAD need the truck to stand, so nothing is loaded or unloaded aboard a ferry.
- **(M4)** SAIL costs 3, every other action costs 1.

**Proof strategy.** Fix a state s with h\*(s) < ∞ and an arbitrary plan π from s that reaches a goal. It
is enough to show cost(π) ≥ h(s).

---

## 2. The map graph, regions and cuts

Let D_f = L_f ∪ {d_f}. A ferry is always docked at a port of D_f.

**Map graph G** (code: `edges`, `gports`). Vertices: the locations and one vertex ν_f per ferry. Edges:
every road, and a _port edge_ {a, ν_f} for every ferry f and a ∈ D_f.

The _node_ of a truck is its location if it stands and ν_f if it is aboard f (code: `tnode`). The node of
a package is its location if it lies and the node of its truck otherwise (code: `site` in a bucket entry).

**Lemma 0.**
(a) DRIVE moves one truck along one road. BOARD(t, f) moves t from a to ν_f along {a, ν_f}, where a is
f's dock. DISEMBARK(t, f) moves t from ν_f to the dock a along {a, ν_f}. No other action changes the
node of any truck, in particular SAIL does not.
(b) The node of a package changes only while it is inside a truck whose node changes, along the same edge.
(c) Nothing ever leaves the connected component of G (the _region_) that contains it, and each action
involves the objects of one region only.

_Proof._ (a) and (b) are read off the table with (M1). For (c): nodes move along edges, a ferry's dock
stays in D_f, which lies in the component of ν_f, and LOAD and UNLOAD involve a truck and a package at the
same location. ∎

So cost(π) is the sum over regions of the cost of the actions of each region. If a package's node and goal
lie in different regions it can never be delivered and h\*(s) = ∞ (code: `dead`, then h = 0). From now
on fix one region R, with truck set T*R and C = max(1, max*{t ∈ T_R} c_t) (code: `cmax`). A package is
_big_ if 2·w_p > C (code: `pbig`). Two big packages are never in one truck together, because their total
weight exceeds C, which is at least every capacity in R.

**Cuts.** For a set X of vertices of G_R, δ(X) is the set of edges with exactly one end in X. An action
crosses δ(X) _outward_ if it moves a truck from X to outside X, _inward_ in the other direction. By
Lemma 0(a) such an action uses an edge of δ(X), and every action uses at most one edge.

---

## 3. Accounts

For the plan π and the region R define:

- A_H = the number of LOAD and UNLOAD actions,
- A_e, for every edge e of G_R, = the number of actions that move a truck along e (DRIVE for a road,
  BOARD or DISEMBARK for a port edge),
- for every SAIL(f, u, w): its _departure end_ (f, u) and its _arrival end_ (f, w), each worth 1.5. The
  end (f, x) _belongs to_ the port edge {x, ν_f}.

Then the cost of R's actions is exactly A_H + Σ_e A_e + 1.5·(number of sail ends) = A_H + Σ_e A_e + 3·S,
where S is the number of sails. The edges of G_R are of four kinds: road bridges and port bridges (the
bridges of G_R, code: `_bridges`, `isb`), and non-bridge roads and non-bridge port edges.

---

## 4. Handling (Lemma 1)

For a package p let h_p = 2 if p lies at a location other than g_p, h_p = 1 if p is inside a truck, and
h_p = 0 if p lies at g_p. p is _undelivered_ if h_p > 0 (code: the `bucket`). H(s) = Σ_p h_p (code:
`_bound`, `h += 2` and `h += 1`).

**Lemma 1.** (a) A*H ≥ Σ*{p in R} h_p.
(b) The handling excess ε_p = (#LOAD of p + #UNLOAD of p) − h_p is even and ε_p ≥ 0.
(c) If p is undelivered and ε_p = 0, then p stays inside a single truck from its first LOAD (or from s,
if p is inside a truck in s) until its final UNLOAD at g_p.

_Proof._ The LOADs and UNLOADs of p alternate (LOAD needs p lying, UNLOAD needs p inside). The sequence
starts with LOAD if p lies in s and with UNLOAD otherwise, and it ends with UNLOAD (or is empty) because p
lies at the end. A lying package away from its goal must move, so by (M1) it is loaded: LOAD … UNLOAD,
an even number ≥ 2. A package inside a truck must end lying: UNLOAD … UNLOAD, an odd number ≥ 1. A package
lying at its goal gives an even number ≥ 0. This is (b), and (a) follows because every LOAD and UNLOAD
concerns one package. For (c), ε_p = 0 leaves exactly one LOAD and one UNLOAD (or one UNLOAD), so p is
never taken out of its truck before the final UNLOAD. ∎

---

## 5. One cut (Lemma 2)

Fix a cut X of G*R. Let o and i be the numbers of outward and inward crossings of δ(X) in π, so that
o + i = Σ*{e ∈ δ(X)} A_e. The state s gives:

- T_in = trucks of R with node in X, T_out = the others. S_in(j) is the sum of the j largest capacities in
  T_in (S_in(0) = 0), and S_out is defined in the same way.
- O = undelivered packages with node in X and goal outside X, I = undelivered packages with node outside X
  and goal in X. W_O and W_I are their total weights, b_O and b_I their numbers of big packages.
- ℓ_in = the largest weight of a package that lies at a location of X other than its goal, or −1 if there
  is none. ℓ_out is the same outside X. κ(S) = the largest capacity in a set S of trucks, −1 if S = ∅.
- The _visit flags_: v_in = 1 if ℓ_in > κ(T_in), else 0, and v_out = 1 if ℓ_out > κ(T_out), else 0.

**Lemma 2.** (o, i) lies in Φ(X), the set of pairs of non-negative integers with

- (a) o ≥ max(b_O, ⌈W_O / C⌉) and i ≥ max(b_I, ⌈W_I / C⌉),
- (b) o − i ≤ |T_in| and i − o ≤ |T_out|,
- (c) if o ≥ i then W_O ≤ S_in(o − i) + i·C,
- (c′) if i ≥ o then W_I ≤ S_out(i − o) + o·C,
- (v) o ≥ v_out and i ≥ v_in.

_Proof._ **Alternation.** A crossing by a truck switches whether its node is in X. So the crossings of one
truck alternate in direction, starting outward if the truck is in T_in and inward otherwise. A truck of
T_in therefore has (#outward − #inward) ∈ {0, 1}, and a truck of T_out has it in {−1, 0}. Summing gives (b).

**Last exits.** Let p ∈ O. Its node starts in X and ends at g*p, outside X. By Lemma 0(b) every change of
p's node between X and the outside happens inside a truck while that truck crosses δ(X). These changes
alternate, so the last one is outward: call it the *last exit* of p. At that moment the truck's load
contains p and is at most its capacity, which is at most C. So the O-packages whose last exit is one given
crossing event weigh at most that truck's capacity and contain at most one big package. Let E be the set
of crossing events that are last exits of O-packages. Then W_O ≤ Σ*{ε ∈ E} cap(ε) ≤ |E|·C and b_O ≤ |E|,
so o ≥ |E| ≥ max(b_O, ⌈W_O/C⌉). With _first entries_ of I-packages (their first crossing, which is
inward) the same counting gives the second half of (a).

**(v).** Suppose v_out = 1. Take a package p that lies at x outside X, x ≠ g_p, with w_p = ℓ_out > κ(T_out).
p must move, so π loads it. Its first LOAD happens at x (p has not moved, by M1) and is done by a truck t
standing at x with c_t ≥ w_p (M2). So t ∉ T_out, that is t ∈ T_in. t starts in X and later stands at x,
outside X, so it crossed outward: o ≥ 1. The case v_in = 1 is symmetric.

**(c).** Assume o ≥ i. Call an outward crossing _initial_ if it is the first crossing of δ(X) by a truck
of T_in, and _repeated_ otherwise. By alternation, every repeated outward crossing of a truck is
immediately preceded, among that truck's crossings, by an inward crossing of the same truck, and different
repeated crossings have different predecessors. So #repeated ≤ i. Let j = #initial. Then j ≤ |T_in| and
j = o − #repeated ≥ o − i. The initial crossings are made by distinct trucks of T_in, so those in E carry
at most S_in(j) in total. The repeated ones in E carry at most (o − j)·C. Hence
W_O ≤ S_in(j) + (o − j)·C. The right side does not increase with j, because S_in(j+1) − S_in(j) ≤ C, and
j ≥ o − i, so W_O ≤ S_in(o − i) + i·C. (c′) is symmetric. ∎

For integers a, b ≥ 0 let **g(X, a, b) = min { o + i : (o, i) ∈ Φ(X), o ≥ a, i ≥ b }** and
g(X) = g(X, 0, 0). Whenever π is known to satisfy o ≥ a and i ≥ b, Lemma 2 gives
Σ\_{e ∈ δ(X)} A_e ≥ g(X, a, b).

**Monotonicity.** g(X, a, b) does not decrease when a, b, W_O, W_I, b_O, b_I, v_in or v_out grow, when a
truck is removed from T_in or T_out, or when a capacity is lowered, because each of these changes only
removes pairs from Φ(X). Conversely, adding a truck or raising a capacity can only lower g. In particular,
dropping the constraint (v) gives a smaller value g_0(X, a, b) ≤ g(X, a, b), which is also a valid lower
bound. This is what the previous version computed.

**Lemma 2′ (the closed form).** With cs and co the capacity lists of T_in and T_out sorted in decreasing
order, `_crossings(wo, wi, bo, bi, cs, co, a, b)` returns g_0(X, a, b), and `g(v, a, b)` returns
g(X, a, b) = g_0(X, max(a, v_out), max(b, v_in)).

_Proof._ Put A′ = max(a, b_O, ⌈W_O/C⌉) and B′ = max(b, b_I, ⌈W_I/C⌉) (the first two lines of the
code), and write d = o − i.
_Case d ≥ 0._ (b) requires d ≤ |T_in|. For fixed d the conditions on i are i ≥ B′, i + d ≥ A′ and, by
(c), i ≥ ⌈(W_O − S_in(d)) / C⌉. (c′) matters only for d = 0, where it says W_I ≤ o·C, which follows from
o = i ≥ B′ ≥ ⌈W_I/C⌉. The other half of (b) holds trivially. The cost is o + i = 2i + d, so the best i
is z = max(B′, A′ − d, ⌈(W_O − S_in(d))/C⌉), which is ≥ 0 because B′ ≥ 0. The first loop of the code
evaluates 2z + d for d = 0, …, |T_in| with ps = S_in(d).
_Case d < 0._ Symmetric with d′ = −d ∈ [1, |T_out|], the second loop.
Every admissible pair falls in one case and every evaluated pair is admissible, so the minimum of the two
loops is g_0(X, a, b). `g` merges the visit flags into a and b, which is exactly constraint (v). ∎

---

## 6. Bridge cuts and their values (Lemmas 3 and 4)

**Lemma 3 (additivity).** If cuts X*1, …, X_m have pairwise disjoint boundaries, then
Σ_j Σ*{e ∈ δ(X*j)} A_e ≤ Σ*{e ∈ ∪_j δ(X_j)} A_e. (Each A_e is counted once.)

**Bridge tree** (code: `cc`, `parent`, `tin`, `tout`). Contract the 2-edge-connected components of G_R.
The bridges join them into a tree, rooted at the component of the region's first vertex. For a non-root
component c let X_c be the union of the components in c's subtree. Its boundary is the single bridge e_c
from c to its parent. Distinct c give distinct edges, so Lemma 3 applies to the whole family. The code has
one _cut_ per non-root c, road bridges first (indices 0, …, R−1, `nroad` = R), then port bridges.

**Lemma 4 (cut values).** For every cut index i with component c*i and X = X*{c_i}, the value `cv[i]`
computed in `move` holds in separate bit fields W_O(X), W_I(X), b_O(X), b_I(X) and the set T_in(X) as a
bit mask over T_R. For a road cut it also holds the flags v_in(X) and v_out(X). The masks `vi` and `vo`
returned by `_visit_masks` have bit i equal to v_in(X) and v_out(X), for every cut.

_Proof._ In preorder the subtree of c is the interval (tin[c], tout[c]] of the 1-based array, so the
subtree sum is a difference of two prefix sums. For an undelivered package p with node x and goal g_p,
`_updates` adds, when cc[x] ≠ cc[g_p], the value out_p (w_p in the first field, the big bit in the third)
at cc[x], in_p (the second and fourth fields) at cc[g_p], and −(out_p + in_p) at their lowest common
ancestor λ. A subtree contains λ only if it contains both cc[x] and cc[g_p]. So the out field of the
subtree sum counts exactly the packages with node inside and goal outside, which is O(X), and the in field
is I(X). Each truck adds its own bit at the component of its node. Every field of a subtree sum lies
between 0 and its maximum (total weight, number of packages, or the truck mask), which is below 2^width
by the choice of WB and BB, so the packed integer decodes exactly.

Visit masks. `rmask[x]` has bit i set exactly when x ∈ X\_{c_i} (it is the set of cuts on the path from
the root), and ALL has every cut bit. Call a truck _capable_ for p if c_t ≥ w_p. For a lying undelivered
package p, `_visit_masks` forms cin = the union of `rmask` over the nodes of the trucks capable for p
(the cuts whose subtree holds a capable truck) and cout = the union of ALL ^ `rmask` over the same trucks
(the cuts whose other side holds one), and adds `rmask[site] & ~cin` to vi and `(ALL ^ rmask[site]) & ~cout`
to vo. So bit i of vi is set iff some lying undelivered package lies in X with no capable truck in T_in(X),
that is iff ℓ_in(X) > κ(T_in(X)), because a truck of a set S can carry p iff κ(S) ≥ w_p. This is v_in(X),
and bit i of vo is v_out(X) in the same way. `move` copies these bits into the flag fields of the road
cuts. ∎

So every road bridge e = e_c has A_e ≥ g(X_c) = `road0[cv]` (Lemmas 2, 2′, 4).

---

## 7. Port cuts (Lemma 5)

Two kinds of cuts have only port edges in their boundary.

- **Port bridge** {a, ν_f}: X is the side containing a (`cut_port` records whether this is the subtree
  side, and the code orients the fields accordingly).
- **Piece** q: take a maximal set Q of locations joined by non-bridge roads inside a 2-edge-connected
  component, such that some non-bridge port edge ends in Q. Remove the non-bridge port edges at Q, and let
  X_q be the component of what remains that contains Q (code: `pmask`).

**Structure facts.**
(P1) For a port bridge {a, ν_f}: ν_f ∉ X, and no other port of f lies in X, since a port a′ ∈ X would
close the cycle a … a′ ν_f a through the bridge.
(P2) For a piece q: δ(X_q) is exactly the set of removed edges, and their ferry vertices lie outside X_q.
A path that leaves Q without a removed edge uses a non-bridge road (and stays in Q by maximality) or a
bridge, and the far side of a bridge from Q meets the rest of G only through that bridge, so it cannot
contain a ferry vertex that is adjacent to Q by a removed edge (the bridge would lie on a cycle). Hence
X_q is Q plus the parts hanging from Q by bridges, and an edge {x, ν_f} with x ∈ X_q and ν_f ∉ X_q is a
removed edge with x ∈ Q.
(P3) Each port edge lies in the boundary of at most one port cut, because a port bridge is its own
boundary and a non-bridge port edge belongs to the piece of its location. Port-cut boundaries are disjoint
from all roads.

**Notation for a port cut X.** F_X = the ferries that have an edge in δ(X). For f ∈ F_X, P_f = the ports
of f in X. By P1 and P2 every edge of f at a port of P_f lies in δ(X). An outward crossing is a BOARD at a
port of P_f onto f ∈ F_X, and an inward crossing is a DISEMBARK from f ∈ F_X while f is docked at a port
of P_f. A _departure_ is a SAIL of some f ∈ F_X from a port of P_f to a port outside P_f, an _arrival_
is the reverse. An _incidence_ is a pair (sail, truck aboard during that sail). Further:

- K = the largest max(1, min(k_f, |T_R|)) over f ∈ F_X (code: `max(fk[f], 1)` for a port bridge,
  `piece_k` for a piece). At most K trucks are aboard a ferry of F_X at any time.
- m_O = max(⌈W_O/C⌉, b_O), m_I = max(⌈W_I/C⌉, b_I), ts = |T_in|, to = |T_out|.
- A ferry f ∈ F_X is _here_ if its dock is in P_f now. here and away count the ferries of F_X that are and
  are not here.
- T_dock = the trucks aboard a ferry of F_X that is here (they are in T_out), ndock = |T_dock|.
- W_n and b_n: weight and big count of the I-packages inside trucks of T_dock (_walk-in_ packages).
- A _cargo truck_ is a truck of T_dock that holds packages whose goal is outside X. cargo(t) is the weight
  and big count of those packages, cw and cb the totals over all cargo trucks, and cw(M), cb(M) the totals
  over a set M of cargo trucks. free = ndock − (number of cargo trucks).
- v_in and v_out as in Lemma 2, and v_arr = 1 if ℓ_in > κ(T_in ∪ T_dock), else 0.

**Lemma 5.** For the plan π:

- (a) boards := o ≥ max(m_O, m_I − to, v_out) and disembarks := i ≥ max(m_I, m_O − ts, v_in).
- (b) The number of departure incidences is at least each of: max(⌈(W_O + cw)/C⌉, b_O + cb), m_I − to,
  and v_out.
- (c) The number of arrival incidences is at least each of: max(⌈(W_I − W_n)/C⌉, b_I − b_n), need, and
  v_arr, where need = min over all sets M of cargo trucks of
  max(⌈(W_O + cw(M))/C⌉, b_O + cb(M)) − ts − free − |M|.
- (d) The number D_X of departures and the number A_X of arrivals satisfy D_X ≥ d0 and A_X ≥ a0, where d0
  is the largest of 0 and ⌈x/K⌉ over the bounds x of (b), and a0 likewise for (c).
- (e) D_X − A_X = here − (the number of ferries of F_X that are here at the end of π). Consequently
  D_X ≥ dep := max(d0, a0 − away) and A_X ≥ arr := max(a0, d0 − here).

_Proof._ (a) is Lemma 2 (a), (b) and (v) for X.

(b), first bound. Let p ∈ O, and let its last exit be the BOARD of a truck t at a port x ∈ P_f onto f.
p stays in t while t is aboard (M3), and p must be unloaded later, so t disembarks later. The first such
DISEMBARK is at a port outside X, otherwise p's node would enter X again after its last exit. f was docked
at x ∈ P_f at the BOARD and is docked outside P_f at that DISEMBARK, so in between f made a departure with
t, and p inside t, aboard. Assign p to the first such incidence. Now let q be inside a cargo truck t that
is aboard f (here), with goal outside X. If f makes a departure with t aboard before t's first DISEMBARK,
assign q to it. Otherwise t first disembarks at a port of P_f, so q enters X, and as for an O-package its
last exit is later followed by a departure incidence with q aboard. Assign q to that one. Every incidence
(σ, t) receives only packages that are inside t during σ, so at most C in weight and at most one big
package. Counting as in Lemma 2 gives the bound.

(b), second bound. Call an inward crossing _loaded_ if it is the first entry of some I-package. There are
at least m_I loaded crossings (same counting). Let τ1 < τ2 be consecutive loaded crossings of one truck t,
and let q be an I-package whose first entry is τ2. q was not inside t at τ1, since then q would have
entered at τ1. So q was loaded into t after τ1, at a location outside X, because q's node was outside X
until τ2. After τ1 t stood in X, and later it stood outside X. To get from X to a location outside X, t
boards some f ∈ F_X at a port of P_f and later disembarks outside X, so as in the first bound f departs
with t aboard in between. This gives a departure incidence of t inside (τ1, τ2), and the same argument
gives one before t's first loaded crossing when t ∈ T_in. So t has at most [t ∈ T_out] + (its departure
incidences) loaded crossings, and summing over the trucks gives m_I ≤ to + #(departure incidences).

(b), third bound. If v_out = 1, the proof of Lemma 2(v) shows that a truck of T_in must stand outside X
at some point, which needs a departure incidence as above.

(c), first bound. Let p ∈ I be no walk-in package, and let its first entry be the DISEMBARK of t from f at
a port of P_f. p was inside t from before t was aboard f, since nothing is loaded aboard (M3). If t had
boarded f at a port of P_f, p's node would have been in X before its first entry, which is impossible. So
either t boarded f at a port outside P_f, or t was aboard f in s while f was not here (if f were here,
t ∈ T_dock and p would be a walk-in package). Either way f's dock moves from outside P_f into P_f while
t is aboard: an arrival incidence with p aboard. Counting as before gives the bound.

(c), second bound. Call an outward crossing _loaded_ if it is the last exit of some package whose goal is
outside X. Let M be the set of cargo trucks that disembark into X before they have any arrival incidence
(M is determined by π). Every package whose node is in X at some moment and whose goal is outside X has a
last exit, and these packages include O and the cargo of the trucks in M, which enters X with them. So
there are at least max(⌈(W_O + cw(M))/C⌉, b_O + cb(M)) loaded exits. After a loaded exit, the next
DISEMBARK of that truck is outside X, as in (b). So before a later loaded exit the truck must enter X
again, by a DISEMBARK from a ferry docked in X, which it boarded outside X: an arrival incidence of that
truck. Before its first loaded exit a truck must also stand in X, which needs an arrival incidence unless
the truck is in T_in, or is in T_dock and walks in first (it is then one of the free trucks or a member of
M). Hence #(loaded exits) ≤ ts + free + |M| + #(arrival incidences), so the number of arrival incidences
is at least the bracket for this M, and therefore at least need. With more than ten cargo trucks the code
uses m_O − ts − ndock instead, which is at most the bracket for every M.

(c), third bound. If v_arr = 1, a lying package in X can only be loaded by a truck that is neither in X
nor aboard a ferry that is here (proof of Lemma 2(v)). To enter X that truck must disembark from a ferry
docked in X, which it boarded outside X or was aboard while that ferry was away: an arrival incidence.

(d) Each departure or arrival has at most K trucks aboard, so it accounts for at most K incidences.

(e) For f ∈ F_X let h_f(τ) = 1 if f's dock is in P_f at time τ and 0 otherwise. A sail of f lowers h_f by
one exactly when it is a departure and raises it by one exactly when it is an arrival. Summing over the
sails of π and over F_X gives D_X − A_X = here − Σ_f h_f(end), which lies between here − |F_X| = −away
and here. Hence D_X ≥ A_X − away ≥ a0 − away, and A_X ≥ D_X − here ≥ d0 − here. ∎

**What the code charges.** `_port_cost` computes boards, disemb, d0 (including the raise by `vout`), need
(including the raise by `varr`), mf, a0, dep and arr exactly as in (a) to (e), and returns
c2 = 2·(boards + disemb) + 3·(dep + arr) together with dep − arr. Every departure and every arrival of X
has its departure end or arrival end at a port of P_f, so that end belongs to an edge of δ(X) (P1, P2).
Therefore

2·Σ\_{e ∈ δ(X)} A_e + 3·(number of sail ends belonging to edges of δ(X)) ≥ c2.

`_ferry_bound` supplies the inputs. For a port bridge they come from `cv[i]` (Lemma 4), from `dmask` (the
trucks aboard f while f is docked at a, which is T_dock), from the walk-in and cargo sums over the
packages inside those trucks, and from here = [f is docked at a], away = 1 − here. Its visit flags are bit
i of the masks of Lemma 4, oriented to the port side: v_in is bit i of `vi` and v_out bit i of `vo` when X
is the subtree side, and the other way round otherwise. v_arr equals v_in when T_dock = ∅. Otherwise the
code tests whether some lying undelivered package of X is heavier than κ(T_in ∪ T_dock), which is
ℓ_in > κ(T_in ∪ T_dock) by the definition of ℓ_in. For a piece the inputs come from `pcross` (the pieces a
package must leave or enter), `tmq` (T_in), `dmq` (T_dock, disjoint from T_in by P2), the cargo per piece
and truck, and here and away over `piece_ferries[q]`, which is F_X by P2. Its flags `qvi` and `qvo` are
computed by the same rule as Lemma 4 with `pmask` in place of `rmask` (bit q of `pmask[x]` is set iff
x ∈ X_q), and v_arr as for a port bridge. A cut that the code skips has nothing to carry, no truck aboard a
ferry that is here and no visit flag, and it is charged 0, which is a valid lower bound.

---

## 8. Sails (Lemma 6)

The code forms _ferry groups_ (`ferry_group`): the ferries of each piece are put into one group, and
groups that share a ferry are merged. To a group Γ belong the port bridges of its ferries and the pieces
whose ferries lie in Γ.

**Lemma 6.** (a) Every sail of a ferry of Γ is a departure of at most one cut of Γ and an arrival of at
most one cut of Γ.
(b) Let S*Γ be the number of sails of Γ's ferries in π. Then S*Γ ≥ Σ dep*X and S*Γ ≥ Σ arr_X, summed over
the cuts X of Γ, and hence

6·S_Γ ≥ Σ_X 3·(dep_X + arr_X) + 3·| Σ_X (dep_X − arr_X) |.

_Proof._ (a) Fix a ferry f. The sets P*f of different cuts are disjoint: for a port bridge {a, ν_f} it is
{a}, for a piece it is the set of ports a of f such that {a, ν_f} is a non-bridge edge at that piece, a
port edge is either a bridge or not, and a non-bridge port edge lies at exactly one piece. A sail of f
from u to w is a departure of X exactly when u ∈ P_f(X) and w ∉ P_f(X), which happens for at most one X
(the one whose P_f contains u). Arrivals are symmetric. (b) By (a) and Lemma 5(e),
S*Γ ≥ Σ_X D_X ≥ Σ_X dep_X, and the same for arrivals. Finally 6·max(x, y) = 3(x + y) + 3|x − y|. ∎

The code adds dep − arr of every port cut to `balance[group]` and charges bal2 = 3·Σ_Γ |balance[Γ]|
(`sail_extra2`).

---

## 9. Fractional bounds (Lemma 7)

**(a) Per cycle block (new).** A _block_ B is the set of non-bridge roads of one 2-edge-connected
component of G_R (Section 10). Its _clusters_ are the connected components of G_R minus the edges of B
(code: `cl`). Γ_B is the multigraph on the clusters with one edge per edge of B (loops dropped), and
dist_B is the breadth-first distance in Γ_B. Γ_B is connected because G_R is. Let ℓ_R be the smallest
positive weight among all packages of R, delivered or not. For every package p of R let
cfw_p = C if w_p > 0 and w_p + ℓ_R > C, and cfw_p = w_p otherwise (code: `cfw`).

**Lemma 7a.** #(DRIVEs along edges of B) ≥ ⌈ Σ\_{p undelivered} cfw_p · dist_B(κ(node of p), κ(g_p)) / C ⌉,
where κ maps a vertex to its cluster.

_Proof._ _Load bound:_ if S is the set of packages inside one truck of R at one moment, then
Σ*{p ∈ S} cfw_p ≤ C. Indeed, if some p ∈ S has w_p > 0 and w_p + ℓ_R > C, every other q ∈ S has w_q = 0
(otherwise w_p + w_q ≥ w_p + ℓ_R > C ≥ capacity ≥ load), so the sum is C. Otherwise the sum is the load,
which is at most C. *Walk:* by Lemma 0(b), the node of p moves along edges of G_R, inside trucks, from its
current node to g_p. Mapped to clusters, an edge outside B keeps the cluster and an edge of B moves to an
adjacent cluster of Γ_B. So p crosses edges of B at least dist_B times, each time inside a truck that
performs a DRIVE along that edge. Summing over these DRIVEs d, with S_d the packages inside:
#DRIVE_B ≥ Σ_d Σ*{p ∈ S_d} cfw_p / C = Σ_p (cfw_p / C)·(number of B-crossings of p)
≥ Σ_p (cfw_p / C)·dist_B. #DRIVE_B is an integer, so the ceiling is allowed. ∎

**(b) Global tables (from the previous version).** Let T be the number of trucks, k′\_f = max(1, min(k_f, T)),
L the least common multiple of the k′\_f, C\* = max(1, largest capacity of all trucks), ℓ\* the smallest
positive weight of all packages, and fw_p = C\* if w_p > 0 and w_p + ℓ\* > C\*, else w_p
(code: `frac_weight`). The _fractional graph_ H has the locations and one vertex (f, a) per ferry f and
a ∈ D_f ("aboard f while it is docked at a"). Edge costs: a road costs 2L if it is not a bridge and 0 if
it is. A port edge {a, (f, a)} costs 2L if {a, ν_f} is not a bridge and 0 otherwise. A sail edge
(f, a)–(f, b), a ≠ b, costs h_f·[{a, ν_f} is not a bridge] + h_f·[{b, ν_f} is not a bridge] with
h_f = 3L / k′\_f. In the _roads-only_ variant port and sail edges cost 0. Then
wd_all[p][v] = fw_p · dist_H(v, g_p) and wd_road[p][v] is the same in the roads-only variant
(code: `_fraction_table`, with 0 for an unreachable goal). For a package the code reads its location, or
(f, dock) if it is aboard f. Let ψ_a and ψ_r be the sums over the undelivered packages, and
den = 2·C\*·L.

**Lemma 7b.** Let Q = 2·(#DRIVEs along non-bridge roads) + 2·(#BOARDs and DISEMBARKs along non-bridge
port edges) + 3·(number of sail ends belonging to non-bridge port edges), and Q_r = 2·(#DRIVEs along
non-bridge roads). Then Q ≥ ⌈2ψ_a / den⌉ = frac2_all and Q_r ≥ ⌈2ψ_r / den⌉ = frac2_road.

_Proof._ The trajectory of a package is a walk in H: it stays at its location while it lies or rides a
standing truck, a DRIVE moves it along a road, BOARD from a to (f, a), SAIL from (f, u) to (f, w), and
DISEMBARK from (f, w) to w. Its H-length is at least dist*H(start, g_p). Charge every action its share:
a DRIVE along a non-bridge road with load S charges Σ*{p ∈ S} fw_p·2L ≤ C\*·2L (the load bound of 7a with
C\* and ℓ\*), and a BOARD or DISEMBARK along a non-bridge port edge likewise at most C\*·2L. A SAIL of f
carries at most k′\_f trucks (BOARD respects k_f, and there are T trucks), each with Σ fw ≤ C\*, so at
each non-bridge end it charges at most k′\_f·C\*·h_f = 3L·C\*. Bridge edges cost nothing. Summing over all
actions, Σ_p fw_p·(H-length of p's walk) ≤ C\*·L·Q, so ψ_a ≤ C\*·L·Q, Q ≥ 2ψ_a/den, and Q is an integer.
The roads-only variant is the same computation restricted to roads. ∎

---

## 10. Cycle blocks (Lemma 8)

Take a block B with its clusters, Γ_B and dist_B as in Section 9 (code: `blocks`). For a cluster z let
ρ_z be the largest distance from z, and for 1 ≤ r ≤ ρ_z let X_r be the union of the clusters at distance
less than r from z.

**Lemma 8.**
(a) δ(X*r) consists of edges of B that join a cluster at distance r − 1 to a cluster at distance r. So
δ(X_r) ⊆ B, and the boundaries for different r are disjoint.
(b) #(DRIVEs along B) ≥ cyc_B := max( ⌈Σ_p cfw_p·dist_B / C⌉ , max_z Σ*{r=1}^{ρ_z} g(X_r) ).
(c) The sum of cyc_B over the blocks of R is at most the number of DRIVEs along non-bridge roads of R.

_Proof._ (a) An edge outside B joins two vertices of one cluster, so it never has exactly one end in X_r.
An edge of B joins clusters whose distances from z differ by at most one, and it lies in δ(X_r) exactly
when one end has distance less than r and the other at least r, that is, the distances are r − 1 and r.
(b) Lemma 2 for each X_r, Lemma 3 for the family, and Lemma 7a. (c) The blocks partition the non-bridge
roads of R. ∎

**The code.** `_block_bound` tries as centers the clusters where a package of `items` is now. By (b) any
set of centers gives a valid bound, so trying fewer centers can only lower the value, never break it. For
each center z and each r it evaluates the inputs of Lemma 2 for X_r. A
package whose cluster distances satisfy da < db belongs to O(X_r) exactly for da < r ≤ db, one with db < da
belongs to I(X_r) exactly for db < r ≤ da (difference arrays `wo`, `wi`, `bo`, `bi`). A truck is in
T_in(X_r) exactly when its cluster distance is less than r (`tm`). ℓ_in(X_r) is the largest lying weight
at distance less than r (`pre`), and ℓ_out(X_r) the largest at distance at least r (`suf`). The values are
packed in the road-cut layout and `road0[v]` returns g(X_r) (Lemma 2′). `items` keeps every package that
can influence a value, namely those that must change cluster and those that lie, since only these enter
O, I, ℓ_in and ℓ_out. cyc2 = 2·Σ_B cyc_B (`_cycle_bound`).

---

## 11. Truck flow (Lemma 9)

For a non-root component c let t*c be the number of trucks of R in X_c now, and k_c the number whose node
lies in X_c at the end of π. By alternation, o_c − i_c = t_c − k_c for the crossings of e_c. Also
0 ≤ k_c ≤ |T_R| and k_c ≥ Σ*{children d of c} k_d, because X_c contains the disjoint sets X_d.

For a road bridge let cost*c(k) = min{ o + i : (o, i) ∈ Φ(X_c), o − i = t_c − k }, so A*{e*c} ≥ cost_c(k_c).
For a port bridge with bounds (out, inn) on its crossings out of and into X_c (boards and disembarks of
Lemma 5, oriented, and (0, 0) for a skipped cut), let cost_c(k) = 2·max(inn, out − D) + D with
D = t_c − k. Given o − i = D, o ≥ out and i ≥ inn, the least o + i is reached at
i = max(inn, out − D, −D) = max(inn, out − D) because out ≥ 0, so again A*{e_c} ≥ cost_c(k_c).

**Lemma 9.** Σ*c A*{e*c} ≥ DP := min{ Σ_c cost_c(k_c) : 0 ≤ k_c ≤ |T_R|, k_c ≥ Σ*{children} k*d,
Σ*{children of the root} k_d ≤ |T_R| }. `_flow` returns flow = DP − Σ_c base_c, where base_c = g(X_c)
= `road0[cv]` for a road bridge and base_c = out + inn for a port bridge.

_Proof._ The actual numbers k_c are feasible, which gives the inequality. `_flow_cost` evaluates, for
k = 0, …, |T_R| and d = t_c − k, the same constraints as Lemma 2′ for that fixed d (including the visit
flags), so it returns cost_c(k) − min_k cost_c(k), and that minimum is g(X_c). `_port_flow_cost` returns
cost_c(k) − (out + inn), which is ≥ 0: if inn ≥ out − D the value is 2·inn + D − out − inn ≥ 0, otherwise
it is out − D − inn > 0. The dynamic program handles children before parents. `out_c[k]` is the least
total over c's subtree with k_c ≤ k, a non-increasing row. `dp[parent]` combines the children's rows by
min-plus convolution, and for non-increasing rows "sum equal to k" and "sum at most k" give the same
values. The root value at k = |T_R| is DP − Σ_c base_c. ∎

So flow ≤ Σ\_{bridges} (A_e − base_e).

---

## 12. First entry (Lemma 10)

A set Res of _reserved_ bridges is given by Lemma 11. A road bridge e = e*c is a *candidate* if it is not
reserved, some undelivered package of positive weight must cross e (equivalently W_O + W_I + b_O + b_I > 0
for X_c, since a big package has positive weight), and one side Y_e of e has no truck: Y_e = X_c if
T_in(X_c) = ∅, or the complement of X_c if T_out(X_c) = ∅. The code forms these sets as bit masks: the
crossing bridges of a package are `rmask[site] ^ rmask[goal]`, and the cuts whose subtree holds some truck,
or every truck, are the union and the intersection of the trucks' `rmask`. The proof below does not use the
crossing condition, which only limits the candidates. A set 𝒰 of
candidates is *closed* if no undelivered package whose node lies outside U = ∪*{e ∈ 𝒰} Y_e has its goal in
some Y_e with e ∈ 𝒰. For a package r with node in U let E(r) = { e ∈ 𝒰 : node of r ∈ Y_e }. For e ∈ 𝒰
let φ_e = 1 + g′\_e − base_e, where g′\_e is `_crossings` for the demands of Y_e with one extra truck of
capacity C on the Y_e side, all trucks of R on the other side and no visit flags (`_first_in`,
`_first_out`), and base_e is the value charged for e.

**Lemma 10.** Let 𝒰 be closed and suppose some undelivered package has its node in U. Then
Σ*{e ∈ 𝒰} (A_e − base_e) ≥ min*{r : node of r ∈ U} Σ\_{e ∈ E(r)} φ_e, for any base with A_e ≥ base_e. The
code uses the greatest closed set, obtained by removing sides that receive a package from outside until
nothing changes.

_Proof._ No truck has its node in U, so the packages with node in U lie at locations, and the undelivered
ones must be loaded in π. Let r be the one among them whose first LOAD comes first in π. Fix e ∈ E(r). r
lies at x ∈ Y_e and its first LOAD is done by a truck standing at x, so some truck enters Y_e before that
LOAD. Let τ be the first entry into Y_e (an entry is a crossing of e, the only edge of δ(Y_e)). At τ:
(1) no undelivered package with node in U has been loaded yet, since τ precedes r's first LOAD, so every
package of O(Y_e), which is undelivered with node in Y_e ⊆ U, still lies where it lay in s. (2) Every
package of I(Y_e) has its node in U, by closedness (outside U its goal could not be in Y_e), so it is an
undelivered package lying in U, it has not been loaded yet, and it is not inside the entering truck. The rest π′ of the plan, after τ, still has to carry all of
O(Y_e) out of Y_e and all of I(Y_e) into it, perhaps more, while exactly one truck, of capacity at most C,
is in Y_e and the others are outside. By Lemma 2 and monotonicity, π′ crosses e at least g′\_e times.
Adding the entry itself, A_e ≥ 1 + g′\_e, that is A_e − base_e ≥ φ_e. The bridges in E(r) are distinct and
A_e − base_e ≥ 0 for the other bridges of 𝒰, so summing and taking the minimum over the unknown r proves
the claim. _Greatest closed set:_ a side is removed only because a package outside the current union has
its goal in it. Such a package is outside the union of any closed set contained in the current set, so
that closed set does not contain the removed side. Hence the iteration never removes a side of a closed
set, and it stops at a closed set, which is therefore the greatest one. ∎

---

## 13. Merge (Lemma 11)

The code (`merge`, `_merge_struct`, `_merge_goal`) treats the goals g that have at least two packages in
increasing order, with a growing set Res of reserved bridges, initially empty. For one goal g:

- the undelivered packages with goal g form _groups_ by holder: those inside one truck, or those lying at
  one location. K is the number of groups.
- path(G) = the bridges that separate the node of group G from g (`rmask[site] ^ rmask[g]`).
- chain = ⋂_G path(G) minus Res. If the chain is empty the goal is skipped.
- twice = the bridges on at least two paths, and for a lying group priv(G) = path(G) minus twice minus Res.
- cost(G) = 2|G| for a carried group and min(2|G|, det(G)) for a lying group, where det(G) adds
  g(X_e, 1, 1) − base_e over the road bridges e ∈ priv(G) and max(0, 1 − boards_e) + max(0, 1 − disemb_e)
  over the charged port bridges e ∈ priv(G).
- for y = 1, …, K: V(y) = Σ*{road e ∈ chain} (g(X_e, y goalward) − base_e) + Σ*{charged port
  e ∈ chain} max(0, y − lb_e) + (the sum of the K − y smallest costs). Goalward means out of X_e if g ∉ X_e
  and into X_e otherwise, and lb_e is the charged bound for the goalward direction.
- merge_g = min_y V(y). If merge_g > 0, the chain and the private bridges of all lying groups are added to
  Res.

**Lemma 11.** Σ*{p with goal g} ε_p + Σ*{e ∈ chain ∪ ⋃*G priv(G)} (A_e − base_e) ≥ merge_g. Because the
bridges claimed for different goals are disjoint and their packages are different, the sum of merge_g over
all goals is at most Σ_p ε_p + Σ*{e ∈ Res} (A_e − base_e).

_Proof._ For e in the chain let N*e be the number of distinct crossing events at e that are the last
goalward crossing of some package of these groups. Every group crosses e goalward, so N_e ≥ 1. Let e\*
minimize N_e and put y = min(K, N*{e\*}).

_Chain._ Every chain bridge e has at least N_e ≥ y goalward crossings. For a road bridge Lemma 2 gives
A_e ≥ g(X_e, y goalward). For a charged port bridge, A_e is the number of boards plus disembarks, the
goalward count is at least max(y, lb_e) and the other count at least its charged bound, so
A_e − base_e ≥ max(0, y − lb_e).

_Paid groups._ Call a group G paid if every package of G has ε*p ≥ 2, so that Σ*{p ∈ G} ε_p ≥ 2|G| ≥ cost(G),
or if G lies and every bridge of priv(G) is crossed in both directions in π. In the second case the
excess on priv(G) is at least det(G) ≥ cost(G): a road bridge with o, i ≥ 1 gives A_e ≥ g(X_e, 1, 1) by
Lemma 2, and a charged port bridge as for the chain. A lying group with priv(G) = ∅ is paid with cost 0.

_At most y groups are unpaid when y < K._ An unpaid group G has a package p_G with ε = 0. By Lemma 1(c),
p_G stays in one truck τ_G from its first LOAD (or from s) until g, so its last goalward crossing at e\* is
made by τ_G. Map G to that event, and suppose two unpaid groups G ≠ G′ map to the same event, so
τ_G = τ_G′ = τ.

- Both carried: τ_G and τ_G′ are their holders in s, which differ for different groups. Contradiction.
- G carried, G′ lying: τ is at the node of G in s. For e ∈ priv(G′) let Y be the side of e containing the
  node of G′. Then g ∉ Y, and the node of G ∉ Y, since otherwise e ∈ path(G) and e ∈ twice. So τ starts
  outside Y, loads p_G′ inside Y and carries it to g outside Y, crossing e in both directions. This holds
  for every e ∈ priv(G′), so G′ is paid. Contradiction.
- Both lying: for e ∈ priv(G) and e′ ∈ priv(G′), the sides Y_e (containing the node of G) and Y_e′
  (containing the node of G′) are disjoint. Both are subtrees of the bridge tree rooted at g's component,
  so they are nested or disjoint, and Y_e ⊆ Y_e′ would put the node of G in Y_e′, so e′ ∈ path(G) and
  e′ ∈ twice, which is impossible (and symmetrically). So τ's node in s lies outside every private side of
  G or outside every private side of G′, say G′. As in the previous case τ then crosses every bridge of
  priv(G′) in both directions and G′ is paid. Contradiction.

So the unpaid groups map injectively into the N\_{e\*} = y events, and at least K − y groups are paid.

_Disjointness._ The handling excesses of different packages, the excess on the chain, and the excesses
on the private sets of different groups are separate quantities, since the chain lies inside twice and the
private sets avoid twice and each other. So the left side is at least the chain part for this y plus the
costs of the paid groups, which is at least V(y) ≥ merge_g. ∎

`_road_extra` returns xfer = Σ_g merge_g plus the first-entry term of Lemma 10 over the unreserved
bridges. By Lemmas 10 and 11, with disjoint resources,

xfer ≤ Σ*p ε_p + Σ*{bridges e} (A_e − base_e).

---

## 14. Proof of Theorem 1

First consider a fresh regional evaluation. Fix the region R and the plan π. The argument permits any
subset of cycle centers in each block (Lemma 8); it does not depend on the code's particular center
selection. Exact helper-cache reuse is justified in Section 16. In the notation of the code:

- base = Σ*{road bridges} g_e + Σ*{port bridges in pres} (boards*e + disemb_e). Since a processed port
  cut with c2 = 0 has boards = disemb = 0, T2 = 2·base + rest2 with
  rest2 = Σ*{processed port bridges} 3·(dep_e + arr_e) + Alt.
- extra = max(xfer, flow).

**(i) Handling.** A_H = Σ_p h_p + Σ_p ε_p (Lemma 1).

**(ii) Bridges.** Σ*{bridges} A_e = base + Σ*{bridges} (A_e − base_e), with every term A_e − base_e ≥ 0
(Lemmas 2, 4, 5).

**(iii) Extras.** Σ*p ε_p + Σ*{bridges} (A_e − base_e) ≥ extra. For xfer this is Section 13, and for flow
it is Lemma 9.

**(iv) Everything else.** Let N = Σ\_{non-bridge edges} A_e. Then 2·N + 6·S ≥ rest2:

- If Alt = piece2 + road2 + bal2: by Lemma 5 and P3 the non-bridge port edges carry at least the pieces'
  boards and disembarks. By Lemma 6, summed over the groups, the sails pay for all departure and arrival
  terms of port bridges and pieces together with bal2. By Lemma 7b and Lemma 8, the non-bridge roads pay
  for road2 = max(frac2_road, cyc2). These charges use different actions.
- If Alt = frac2_all: the port bridges' terms 3·(dep + arr) are paid by the sail ends belonging to the
  bridge port edges (Section 7), and Lemma 7b pays frac2_all from the non-bridge crossings and the sail
  ends belonging to non-bridge port edges. These are different ends.
- Without fractional tables, Alt = piece2 + cyc2 + bal2 is the first case with road2 = cyc2.

**Conclusion.** The cost of R's actions is A*H + Σ*{bridges} A_e + N + 3·S, so by (i) to (iv) it is at
least Σ_p h_p + base + extra + rest2 / 2. Every term except rest2 / 2 is an integer and the cost is an
integer, so the cost is at least Σ_p h_p + base + extra + ⌈rest2 / 2⌉ = Σ_p h_p + ⌈T2 / 2⌉ + extra. Summing
over the regions gives cost(π) ≥ h_fresh(s). Since π was arbitrary, h_fresh(s) ≤ h\*(s).

Every fresh regional value is an integer and nonnegative: T2 ≥ 0, flow ≥ 0, and
max(xfer, flow) ≥ 0. Lemma 13 in Section 16 proves that cache hits preserve the bound needed here,
including the separation from compulsory handling H(s). Consequently the returned h(s) also satisfies
0 ≤ h(s) ≤ h\*(s). At a goal state no package is undelivered, so H = 0, every bucket is empty, and
`_bound` returns 0. ∎

---

## 15. Proof of Proposition 2 (comparison with the previous version)

In this section h and h_old denote fresh evaluations, as specified in Proposition 2. They do not denote
values imported from another state through the coarse regional cache.

Write h = H + Σ_R ( ⌈rest2 / 2⌉ + max(base + xfer, base + flow) ), and the previous heuristic in the same
form with rest2_old, base_old, xfer_old and flow_old. Below, rest2 ≥ rest2_old and
base + flow ≥ base_old + flow_old are proved. Hence h(s) ≥ H + Σ_R (⌈rest2_old / 2⌉ + base_old + flow_old),
which is h_old(s) whenever the previous maximum was attained by flow_old. The merge and first-entry term is
computed by the same procedure on stronger inputs, but it is not comparable in general: raising the base
values can change whether a goal's merge bound is positive, and with that the set of bridges it reserves
and the candidates left to first entry. The version of this document dated earlier the same day added the
previous term as a further candidate to make the comparison unconditional. It was removed because that
second evaluation ran in almost every state and cost more time than it gained.

**rest2 ≥ rest2_old.** The new code processes every port bridge that the previous one processed (the old
skip condition is part of the new one) and possibly more. For a cut processed by both, the inputs differ
only by the visit flags, and `_port_cost` is non-decreasing in them: boards, disemb, d0 and need can only
grow, hence a0, dep and arr too. The term Σ*{port bridges} 3·(dep + arr) + piece2 + bal2 equals
Σ*{pieces} 2·(boards + disemb) + 6·Σ*Γ max(D*Γ, A*Γ), where D*Γ and A_Γ sum dep and arr over the group's
cuts, and every part of it can only grow (more pieces are active, each value is at least as large).
road2 = max(frac2_road, cyc2) is at least the old road term frac2_road, and frac2_all is unchanged. So
both alternatives of Alt, with the port-bridge sail terms added, are at least the old ones, and so is their
maximum. The ceiling is monotone.

**base + flow ≥ base_old + flow_old.** base + flow is the minimum DP of Lemma 9, and every cost_c(k) is
at least the old one (more constraints for road bridges, larger out and inn for port bridges). ∎

**Lemma 12 (first-entry selection).** On the same candidates and with the same reserved set, the
previous single pass (which classifies each package once, in index order, as inside or outside the current
union, and removes the goal sides of outside packages) ends with a set U_old ⊇ U\*, the greatest closed
set. If its result is positive, then U_old = U\* and both results are equal. So the new selection is never
below the old one on the same inputs.

_Proof._ Initially the set contains U\*. A side is removed only because a package outside the current
union, hence outside the union of U\*, has its goal in it, and by closedness that side is not in U\*. So
U_old ⊇ U\*. The old result is the minimum, over the packages listed as inside, of the sum over the sides
of U_old containing the package. If a listed package is no longer in U_old its sum is 0, and so is the
result. Otherwise every package outside U_old was processed as outside and removed its goal sides, so
U_old is closed, U_old ⊆ U\*, the two sets are equal, the listed packages are exactly those in U\*, and the
two results coincide. ∎

---

## 16. Implementation notes

**Cache obligation.** A cached value must remain a lower bound for the state in which it is reused.
Most helper caches store a value determined exactly by their key. For the coarse, single-region
`reg.cache`, a different argument is needed: reuse preserves admissibility even without establishing
equality to a fresh evaluation. All caches belong to one fixed problem instance.

**Keys used by the implementation.**

- `hcache`: the raw state tuple with its leading field set to 0 (`h_astar` normalizes it before the lookup,
  since the history field of the condition-(1) file is never read by h). Without history that field is always 0,
  so the key is the complete raw tuple. It stores an already obtained admissible answer for that state, which is
  admissible for every state sharing the key, because h reads nothing that differs between them. The unused `hcache2` attribute is initialized but is not read or written by `h_astar` or `_h`.
- `reg.cache`, one region: all truck nodes, all ferry docks, and, for every undelivered package, its ID
  and node. It also retains the holder when the package is aboard a ferry or has a goal in `merge_goals`.
  For multiple regions, `reg.sig(state)` instead retains the raw codes of that region's objects.
- `ferry_cache`: each truck's port-cut and piece memberships, each truck's ferry index `tfer`, all ferry
  docks, and each undelivered package's ID and memberships, retaining its holder when aboard a ferry.

**Capability observation.** Let s and s' share a coarse regional key, and let p lie at x in one state
and be carried by a standing truck t at x in the other. Since the carrying state is legal, c_t ≥ w_p
(or the corresponding inequality in the integer relaxation). The key fixes t's node and p's node, so
t is at x in both states. For any cut, including every cycle-ball cut, the side containing p therefore
contains a truck capable of carrying p. Making p lying cannot set a visit flag that was previously
false. Making it carried cannot remove a true visit flag caused by another package. If several packages
change custody, apply this observation to each of them; no intermediate state needs to be constructed.
Likewise p cannot force an arrival when its side already contains t. The same observation applies to
two states sharing `ferry_cache`'s key for all of its port cuts and pieces: their precise locations may
differ, but t and p remain on the same side of every relevant cut.

**Exact reuse in `ferry_cache`.** Package crossing demands, truck membership masks, ferry occupancy and
docks, and the per-truck walk-in and cargo sums are fixed by this key. The capability observation fixes
the visit and arrival flags even where lying/carried status is omitted. Thus every input to the port
bounds is the same, so the tuple `(port2, pres, piece2, sail_extra2)` is identical for states sharing
this key. Ordinary reuse is exact here.

**Why equality is not asserted for the coarse regional cache.** In `_cycle_bound`, a package is included
in `items` when `a != b or hol < 0`, where a and b are its current and goal clusters. `_block_bound`
chooses centers from the current clusters in `items`. Consequently, when a = b, changing a package from
lying to carried can remove an item and can change the selected set of centers. Its visit contribution
is redundant by the capability observation, but its presence as a possible center is a separate issue.
The earlier argument that all inputs, and therefore fresh values, must be identical did not account
for this selection rule. Equality is unnecessary for admissibility.

**Lemma 13 (safe regional cache reuse).** Let s and s' be legal states in the scope of Theorem 1 with
the same single-region cache key. If m is the regional value computed at s' and stored in `reg.cache`,
then for every solution plan π from s,

H_R(s) + m ≤ cost_R(π),

where H*R(s) = Σ*{p in R} h_p(s), and cost_R counts only actions of that region.

_Proof._ The key fixes all truck nodes, ferry docks, undelivered package IDs and package nodes. Hence
the demands W_O, W_I, b_O and b_I and the truck membership masks are identical for every fixed cut.
The capability observation also fixes its visit flags. It follows that the bridge values, port and
piece bounds, sailing balance, truck-flow bound and global fractional bounds are unchanged. The merge
groups are unchanged because the key retains holders for every merge goal. First-entry selection uses
package nodes and goals, truck membership, and the reserved bridges, which are likewise unchanged.
Thus xfer and flow are unchanged. These statements concern their values; some helper inputs, such as
an unneeded holder field, may still differ.

For a fixed cycle block B and any fixed center z, write

b*B(z; s) = Σ*{r=1}^{ρ*z} g(X_r; s),
f_B(s) = ⌈Σ*{p undelivered} cfw_p · dist_B(κ(node_p), κ(g_p)) / C⌉.

Every fixed-center value b_B(z; s) equals b_B(z; s'): its demands, truck masks and visit flags have just
been shown equal. Also f_B(s) = f_B(s') because nodes, goals and package IDs are fixed. A package omitted
from `items` has a = b and is carried, so its distance and cut demands are zero and it sets no visit
flag. If its custody changes under the shared key, its lying version still sets no visit flag by the
capability observation. Omitting it therefore affects neither these fixed-center values nor f_B.

Let Z'\_B be the centers actually selected when computing the stored value at s'. Lemmas 7a and 8 apply
to any set of centers, including Z'\_B when the current state is s. Therefore

max(f*B(s), max*{z in Z'\_B} b_B(z; s)) ≤ #(DRIVEs on B in π),

with the maximum over an empty set taken as 0. If `items` was empty, f_B is also 0, matching the code's
skipped block. This bound equals the block value used in m. Different blocks use disjoint road edges,
so their cached block values can still be added. In particular, this reuses exactly the non-bridge-road
cost account of Lemma 8; it does not charge compulsory handling or bridge costs.

All other regional terms are unchanged, so Section 14's accounting applies at s with these reused
cycle bounds. It gives H_R(s) + m ≤ cost_R(π). `_bound` recomputes H_R(s) from the current state, so it
does not accidentally reuse H_R(s') when the package custody changes. ∎

**Remaining caches and evaluation history.** The multiple-region `reg.cache` fixes the region's raw
state and therefore gives exact reuse. `road_extra_cache` (cut values, bucket and port bounds),
`cyc_cache` (block, truck clusters and complete `items`), `flow_cache` (cost pattern), and the scalar
memo tables are determined by their keys and immutable instance data. The same holds for `flow_steps`
and `flow_merges`, keyed by their input rows, and merge memoization, keyed by the goal, reserved bridges,
group descriptions, and relevant cut and port values. Visit masks are computed when the corresponding
calculation runs; a regional cache hit need not recompute them, because the argument above shows that
their relevant truth values are preserved.

Initially the caches are empty. On a miss, the bounds above justify the stored value. On a hit,
exact reuse or Lemma 13 justifies the value for the receiving state. Induction over evaluations therefore
establishes the invariant for every cache history. In particular `hcache` stores and reuses a valid
answer for its exact state, even if the earlier regional center selection depended on evaluation order.
This proves the cached part of Theorem 1 without asserting equality to h_fresh(s).

**The component write-back.** When the successor function finishes a region it writes that region's trucks
and ferries back to their initial positions. The region then has no undelivered package and contributes 0,
whatever those positions are. The consistency checks at the start of `_bound` can only return 0, which is
a valid lower bound.

**Degenerate inputs.**

- A region without trucks has C = 1 and κ = −1. Any package there that must move makes h\* = ∞.
- A capacity of 0, or a weight of 0, is covered: the proof uses w_p ≥ 0, and κ and the flags compare
  weights with capacities exactly.
- A ferry with k_f ≤ 0 can never be boarded, and K uses max(1, ·), an upper bound on the trucks aboard.
- With more than ten cargo trucks at one cut, the weaker bound m_O − ts − ndock is used (Lemma 5(c)).
- Non-integer weights or capacities: the code replaces every weight by 1 and every capacity by the number
  of packages. Every real load fits this relaxation, so Lemmas 2 to 11 hold for it, and the visit flags
  then fire only on a side without any truck, which is a true requirement.
- A ferry docked outside D_f cannot occur, and the code returns 0 for it.

---

## 17. What changed relative to the previous version

1. **Visit requirements (Lemma 2(v), Lemma 5).** A side that holds a lying package which no truck on that
   side can carry (none is big enough, or there is no truck) forces a crossing into it, and for port cuts
   also a disembark and, when no capable truck is aboard a ferry docked there, an arrival by sail. This is
   applied to road bridges, port bridges and pieces, and it also strengthens the flow, merge and
   first-entry terms that are built on the same crossing bound.
2. **Road cycles (Lemmas 7a and 8).** The previous version bounded the non-bridge roads only by fractions
   w/C of distances, which ignore the trip a truck makes to reach a package. Each 2-edge-connected
   component now contributes the larger of a ball-family cut bound and a per-cycle fractional bound, and
   the road part uses the larger of this and the old fractional road bound.
3. **First-entry selection (Lemmas 10 and 12).** The candidate set is reduced to the greatest closed set
   instead of by one order-dependent pass. On the same inputs it is never weaker, and it is independent of
   package order.

The parts inherited from the previous version (bridge and port bounds, cargo subsets, departures and
arrivals, balance, fractions, flow, merge, first entry) were re-derived above from the rules of the
assignment. The order dependence in item 3 was safe but could lose value. The separate gap in the
regional-cache explanation is addressed by Lemma 13; no change to the implemented heuristic is needed
for that argument.

**Revision after timing (same day).** A first version of these changes was slower on the course checker
than the previous heuristic. Four costs were removed without touching what is proved: the second
evaluation of merge and first entry that made the comparison of Section 15 unconditional, the visit flags
computed by a loop over every pair of lying package and cut (now a few whole-integer bit operations per
package, Lemma 4), a cache key that separated lying from carried packages and so recomputed every LOAD and
UNLOAD child (now the previous key, justified in Section 16), and ball families around every cluster of a
cycle block (now only around clusters where a relevant package is, Section 10).

**Proof correction (2026-11-19).** Section 16 now distinguishes exact helper-cache reuse from reuse of
an admissible cycle-center selection through the coarse regional cache. The theorem and formula
distinguish cached answers from fresh evaluations, and the comparison in Section 15 is stated for fresh
evaluations. The domain statement now accurately records the staff's w_p ≥ 1 clarification without
attributing an integer-weight guarantee to that answer. These are proof changes only; no test results
or changes to `ex1.py` are used.
