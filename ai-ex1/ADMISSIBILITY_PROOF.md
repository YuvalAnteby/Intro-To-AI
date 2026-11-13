# Admissibility proof for `h_astar` in `ex1.py`

Written against `ex1.py` with md5 `053cf25c14d86f3e977ea01bc2daa281` (1,580 lines).
If the heuristic code changes, the matching section here has to be rechecked.

Revision 2 (2026-11-13): three corrections after an external review, listed in section 12. The theorem is unchanged.

## 0. The claim

**Theorem.** Let a game satisfy

* **(A1)** every ferry starts docked at one of the ports it serves, and
* **(A2)** every ferry can carry at least one truck.

Then for every state `s`, `h(s) <= h*(s)`, where `h*(s)` is the cheapest total cost of any sequence of
legal actions that leads from `s` to a goal state. Also `h` is a non-negative integer and `h = 0` on goals.

`h*` ranges over **all** legal actions, not only the ones the pruned `successor` generates. Pruning can
only make the remaining cost larger, so this is at least as strong as anything a grader can measure.

(A1) and (A2) are properties of the input. All 18 given problems satisfy them. Section 9 says what
happens without them.

## 1. The model

Fix a state and any plan from it that delivers every package. All counts below ("the number of ...")
refer to this plan.

**Graph G.** Nodes: every location, and one node per ferry. Edges: a *road edge* per road, and a
*port edge* `(a, f)` for every port `a` that ferry `f` serves. The *node of a truck* is its location, or
the ferry it is aboard. The *node of a package* is its location, or the node of the truck that holds it.

* **F1.** DRIVE moves a truck along one road edge. BOARD and DISEMBARK of ferry `f` docked at `a` move a
  truck along the port edge `(a, f)` (this edge exists by A1, because a ferry is always docked at a port
  it serves). SAIL, LOAD and UNLOAD move no truck and no package in G.
* **F2.** A package changes node only while it is inside a truck that traverses an edge.
* **F3.** The weight inside a truck never exceeds its capacity, hence never exceeds `cmax`, the largest
  capacity among the trucks of the region (section 6 uses the largest capacity of the whole game instead,
  see there). A package is *big* if `2w > cmax`. Two big packages are never
  in one truck at the same time.
* **F4.** A *bridge* of G is an edge whose removal splits its region (connected component of G) into two
  *sides*. A truck or package changes side only by traversing the bridge, so the crossings of one truck
  alternate in direction.
* **F5.** A SAIL of `f` from `x` to `y` costs 3. Split it into a *departure half* that belongs to the
  pair `(x, f)` and an *arrival half* that belongs to `(y, f)`, 1.5 each.

**Additivity principle.** If several sets of actions (or half-sails) are pairwise disjoint and each has a
lower bound on its cost that holds for every plan, then the sum of the bounds is a lower bound on the
cost of the plan. Trucks, ferries and packages never leave their region, so different regions always
give disjoint sets.

## 2. What h is, and which actions each term claims

```
h = base + sum over regions [ ceil(T2 / 2) + xfer ]
T2 = 2 * sum(road bridges) + sum(port bridges) + 2 * first_entry + max(pieces + ceil(road fractions), ceil(all fractions))
```

`T2` is in doubled units (a DRIVE is 2, a half-sail is 3) so that everything stays an integer.

| term | code | actions it claims | proved in |
|---|---|---|---|
| base | `_bound` | one LOAD + one UNLOAD per lying undelivered package, one UNLOAD per package inside a truck | 3 |
| road bridge `e` | `g`, `_crossings` | DRIVEs over `e` | 4 |
| port bridge `(a,f)` | `port_cost` | BOARD / DISEMBARK of `f` at `a`, half-sails of the pair `(a,f)` | 5 |
| piece `q` | `port_cost` in `move` | BOARD / DISEMBARK over the non-bridge port edges of `q`, half-sails of those pairs | 5 |
| fractions | `wd_road`, `wd_all` | DRIVEs over non-bridge roads (and, in the second alternative, the same actions as the pieces) | 6 |
| first entry | `first_in`, `first_out` | DRIVEs over road bridges, beyond the road-bridge term, only on bridges merge does not use | 7 |
| merge | `merge`, `_merge_goal` | LOAD / UNLOAD beyond base, and crossings beyond the bridge terms on the bridges it marks `used` | 8 |

These sets are pairwise disjoint: different edges are different actions, bridge and non-bridge edges are
different edges, half-sails are indexed by (port, ferry) pairs that follow the same split, and the three
"beyond" terms are defined as the excess over the term they extend. Section 10 assembles them.

## 3. Base term

A lying undelivered package can only move inside a truck (F2), so it is loaded at least once and unloaded
at least once. A package inside a truck must end lying at its goal, so it is unloaded at least once.
These are different actions for different packages, and none is a movement action. ∎

## 4. Road bridges

For a road bridge `e` let S be one side ("inside") and let

* `wo`, `bo` = total weight and number of big packages that are inside now with goal outside,
* `wi`, `bi` = the same for packages outside now with goal inside,
* `cs` = capacities of the trucks inside now, `co` = of the trucks outside now.

The code obtains these from `cv[i]` (point masses on the bridge tree, prefix sums over the subtree).
A package inside and going inside contributes `out + inn - out - inn = 0`.

**Lemma 1 (crossing lemma).** Let `zo` and `zi` be the numbers of crossings of `e` out of S and into S.
Then

1. `zo >= bo` and `zi >= bi`,
2. there is `j <= min(|cs|, zo)` with `zo - j <= zi` and `(sum of the j largest of cs) + (zo - j) * cmax >= wo`,
3. the mirror statement of 2 for `zi`, `co`, `wi`.

*Proof.* (1) Every big package that has to go out is carried over `e` outward at least once, and by F3
one crossing carries at most one big package.
(2) Call an out-crossing *fresh* if it is the first crossing of `e` by that truck. A fresh out-crossing is
made by a truck that is inside now, and each truck makes at most one, so the `j` fresh out-crossings are
made by `j` different trucks of `cs`. By F4 every other out-crossing is directly preceded, for the same
truck, by an in-crossing, and different out-crossings get different in-crossings. So `zo - j <= zi`.
Every package that has to go out is in the truck during at least one out-crossing, so the loads of the
out-crossings add up to at least `wo`. The fresh ones carry at most the `j` largest capacities of `cs`
together, every other one at most `cmax`.
(3) Symmetric. ∎

`_crossings(wo, wi, bo, bi, cs, co, a, b)` returns the least `zo + zi` over all pairs with
`zo >= max(a, bo)`, `zi >= max(b, bi)` that satisfy 2 and 3 (or `a + b` if none below 200, which is
smaller). So:

Call a pair `(zo, zi)` *feasible for* `(cs, co)` if it satisfies 2 and 3 with these truck lists.

**Corollary 1.** If the pair `(zo, zi)` of the plan is feasible for some truck lists `(cs', co')` and
`zo >= a`, `zi >= b`, then `_crossings(wo, wi, bo, bi, cs', co', a, b) <= zo + zi`.
In particular (with the true truck lists, where Lemma 1 gives feasibility) the plan has at least
`g(v, a, b)` crossings of `e`, and at least `g(v, 0, 0)` DRIVEs over `e`.

*Proof.* The code returns either the least feasible total (at most `zo + zi`, because the pair of the plan
is one of the candidates) or, when no feasible total up to 200 exists, the fallback `a + b`, which is at
most `zo + zi` as well. ∎

**Remark (the cutoff).** Adding a truck to `cs` or `co`, or enlarging a capacity, only enlarges the set of
feasible pairs. The *returned value* is nevertheless not monotone, because of the fallback. Example:
`cmax = 2`, `wo = 201`, nothing else. With one truck inside the least total is 201, so the code returns 0.
With two trucks inside it returns 200. For the same reason a difference of two calls, such as
`g(v, y, 0) - g(v, 0, 0)`, can be negative (the example gives -98 for `y = 102`).
This proof therefore never uses monotonicity or the sign of a returned value. It uses only Corollary 1,
which holds for whatever the code returns. A negative difference makes `h` smaller, never larger.
Corollary 1 would also hold if the fallback were `max(a + b, 201)`, since then no feasible total up to
200 exists and the plan's own total is at least 201.

Different road bridges are different roads, so the bounds add. ∎

## 5. Ferries: `port_cost`

`port_cost` is used for two kinds of cuts.

* **Port bridge** `(a, f)`: E = {`(a, f)`}, S = the side that contains `a`.
* **Piece** `q` (a maximal set of locations joined by non-bridge roads, inside a 2-edge-connected part):
  E = the non-bridge port edges `(a, f)` with `a` in the piece, S = everything reachable from the piece
  without using E.

*E is exactly the set of edges between S and the rest.* For a port bridge this is the definition. For a
piece: a non-bridge edge has both ends in the same 2-edge-connected part, roads of that kind stay inside
the piece, and what hangs on the piece through bridges cannot reconnect to the rest. So S is the piece
plus what hangs on it through bridges, the ferry node of every edge of E lies outside S, and every edge
that leaves S is in E. The sets E of different pieces are disjoint, and none contains a bridge.

So a truck leaves S only by a BOARD over an edge of E ("out-crossing") and enters S only by a DISEMBARK
over an edge of E ("in-crossing"). Write P(f) for the ports `a` with `(a, f)` in E. Inputs of `port_cost`:

* `wo, bo` / `wi, bi`: weight and big packages that are in S with goal outside / outside S with goal in S,
* `wn, bn`: the part of `wi, bi` that is inside trucks aboard a ferry `f` docked at a port of P(f),
* `cargo`: for each truck aboard such a docked ferry, the weight and big count of its packages whose goal
  is outside S,
* `ts`: trucks in S, `to = ntrucks - ts`, `ndock`: trucks aboard ferries docked at their P ports,
* `k`: the largest capacity of the ferries of E, `here` / `away`: ferries of E docked at a P port / not.

Let `mo = max(ceil(wo/cmax), bo)` and `mi = max(ceil(wi/cmax), bi)`. An *incidence* is a pair
(sail event, truck aboard during it). A sail has at most `k` incidences.
Let D and A be the numbers of departures from, and arrivals at, P ports by the ferries of E.

**Lemma 2.** In every plan:

1. BOARDs over E `>= max(mo, mi - to)` and DISEMBARKs over E `>= max(mi, mo - ts)`.
2. `D >= d0` and `A >= a0`, with `d0`, `a0` as computed by `_port_cost`.
3. `D >= A - away` and `A >= D - here`.

So the cost of the BOARDs, DISEMBARKs and half-sails of E is at least
`boards + disemb + 1.5 * (max(d0, a0 - away) + max(a0, d0 - here))`, which is half of what the code returns.

*Proof of 1.* Call an out-crossing an *L-event* if it is the last out-crossing of some package that has to
go out. The packages that share an L-event are in one truck at one moment, so by F3 there are at least
`mo` L-events. Likewise there are at least `mi` *first-in events* (in-crossings that are the first
in-crossing of some package that has to go in). A first-in event is either the first crossing of its
truck (at most `to` events, one per truck that is outside now) or is preceded by an out-crossing of the
same truck, different events by different out-crossings (F4). So BOARDs `>= mi - to`. Symmetric for
DISEMBARKs. ∎

*Proof of 2, departures.* (i) Take an L-event: truck `t` boards `f` at `a` in P(f) carrying `p`, and `p`
never enters S again. `p` cannot be unloaded aboard, and if `t` disembarked at a port of P(f) then `p`
would enter S again. So `t` stays aboard until it disembarks at a port outside P(f), and the first sail
after the board is a departure from `a` with `t` aboard. Different L-events give different incidences
(for one truck they lie in disjoint stays aboard). So `D >= ceil(mo / k)`.

(ii) Cargo. A cargo package `q` is aboard `f` docked at `a` in P(f), with goal outside S. If `q` never
crosses E, it leaves the ferry node at a port outside P(f) having been aboard since now, so it is aboard
during a departure from `a`. Otherwise its last crossing is an out-crossing after which it never returns,
and (i) applies. So every package of `wo` and every cargo package is aboard during some departure from a
P port. Assign each to one such incidence. The packages of one incidence are in one truck at one moment,
so by F3 the number of incidences is at least `max(ceil((wo + cw)/cmax), bo + cb)`, and D is at least
that divided by `k`, rounded up. This is the first term of `d0` (with `cw = cb = 0` when there is no cargo).

(iii) At least `mi - to` first-in events are preceded by an out-crossing of the same truck `t`: `t` boards
at `a` in P(f) at time τ1 and at τ2 disembarks into S carrying `p`, for which this is the first entry
into S. At τ1 the truck is in S and `p` is not, so `p` is loaded into `t` between τ1 and τ2 at a location
outside S. To stand there, `t` must have left the ferry node at a port outside P(f), so `f` departed from
`a` with `t` aboard. Different events give different incidences. So `D >= ceil((mi - to) / k)`. ∎

*Proof of 2, arrivals.* (iv) Take a package `p` of `wi` that is not part of `wn`, and its first-in event:
`t` disembarks from `f'` at `a'` in P(f') carrying `p`. Before that `p` was never in S, and it is not now
aboard a ferry docked at a P port. So `t` took `p` aboard `f'` at a port outside P(f'), or is aboard `f'`
docked outside P(f') now, and stayed aboard until `a'`. The last sail before the disembark is an arrival
at `a'` with `t` aboard. There are at least `mf = max(ceil((wi - wn)/cmax), bi - bn)` such events, with
different incidences. So `A >= ceil(mf / k)`.

(v) Let M be the set of cargo trucks whose first crossing of E is a DISEMBARK that happens before any
arrival at a P port with that truck aboard (they "walk in"). Their whole cargo enters S with them, so each
of those packages later has a last out-crossing. Hence the number N of L-events (now for the packages of
`wo` and the cargo of M) is at least `max(ceil((wo + ew)/cmax), bo + eb)`, where `ew, eb` are the cargo
totals of M.
Fix a truck `t` and look at its L-events in order. After an L-event `t` leaves by ferry and disembarks
outside S (see (i)). Before its next L-event it must be in S again, so it enters S by a DISEMBARK after
boarding outside P, which needs an arrival at a P port with `t` aboard. Before its *first* L-event, `t`
also needs such an arrival, unless it is in S now (`ts` trucks) or it is aboard a docked ferry now and
walks in (at most `free + |M|` trucks, where `free = ndock - |cargo|`). So the number of arrival
incidences is at least `N - ts - free - |M|`, which is at least the minimum over all subsets that
`_port_cost` computes as `need` (and equals `mo - ts - ndock` when there is no cargo).
So `A >= ceil(need / k)`. ∎

*Proof of 3.* For one ferry of E, a sail from a P port to a non-P port is a departure only, the reverse
is an arrival only, a sail between two P ports is one of each, and other sails are neither. So
(departures - arrivals) of this ferry = [docked at a P port now] - [docked at a P port at the end], which
lies between `-(1 - here_f)` and `here_f`. Sum over the ferries of E. ∎

**Disjointness.** Different port bridges are different (port, ferry) pairs, the sets E of the pieces are
disjoint and contain no bridge, and half-sails follow the pairs (F5). So all port-bridge terms and all
piece terms add. A cut is skipped by the code when nothing has to cross it and no truck is aboard there,
which only drops a non-negative term.

## 6. Fractions

`_build_fractions` builds a graph H: the locations, plus a node "aboard `f` docked at `a`" for every port
edge. Edge lengths, in units of one action: non-bridge road 1, non-bridge port edge 1, sail of `f` from
`a` to `b`: `(1.5 / k_f)` for each of the two ends whose port edge is not a bridge. Everything that
sections 4 and 5 already charge to a bridge has length 0. `d_p` is the shortest length in H from where
`p` is to its goal (the relaxation loop computes exactly this, edges are symmetric).

In this section only, `cmax` is the largest truck capacity of the **whole game** (`max(self.tcap)` in
`_build_fractions`), not of the region. It is at least the capacity of every truck, so F3 holds with it.
Using the larger value only makes the bound smaller.

**Lemma 3.** The cost of the DRIVEs over non-bridge roads, the BOARDs and DISEMBARKs over non-bridge port
edges and the half-sails of non-bridge pairs is at least `sum over p of (w_p / cmax) * d_p`.

*Proof.* The way of `p` through the plan is a walk in H from its place to its goal, of length at least
`d_p`. Charge every step of the walk to the action that makes it, with weight `w_p / cmax`.
A DRIVE or BOARD or DISEMBARK over a non-bridge edge costs 1 and is charged `sum of w_p / cmax` over the
packages in that one truck, at most 1 by F3. A SAIL of `f` is charged, per non-bridge end,
`sum over the packages aboard of (w_p / cmax) * 1.5 / k_f`. At most `k_f` trucks are aboard, each with
weight at most `cmax`, so this is at most 1.5, the cost of that half-sail. No action is charged more than
the part of its cost that is listed in the lemma. ∎

With the roads-only table (`wd_road`) the same proof gives a bound on the non-bridge DRIVEs alone.

The code adds `max(pieces + ceil(road fractions), ceil(all fractions))`. Both alternatives are lower
bounds on the doubled cost of the same set of non-bridge actions: the first is the sum of two bounds on
disjoint subsets (piece terms from section 5, non-bridge DRIVEs), the second is Lemma 3. Each rounded
quantity is a bound on an integer (the doubled cost of a fixed set of actions and half-sails), so rounding
up is allowed. The maximum of two lower bounds on one quantity is a lower bound. ∎

## 7. First entry (`OPT_FIRST`)

Let Σ be the set of sides that survive in `cs` / `cc`: each X in Σ is a side of a road bridge `e_X` that
merge did not use, has no truck in it now, and some package has to cross `e_X`. Let U be their union.
The term `best` is the minimum, over the packages in the list `inside`, of `v(p)` = the sum of
`first_in` / `first_out` over the sides of Σ that contain `p`. Nothing is added unless `best > 0`.

Two facts follow from the code when `best > 0`:

* **(a)** every package in `inside` lies in U now. (A package in no side of Σ has `v = 0`.) Conversely
  every undelivered package that is in U now is in `inside`, because U only shrinks during the loop.
* **(b)** no undelivered package that is outside U now has its goal in a side of Σ. (By (a) those packages
  are exactly the ones the loop classified as outside, and each of them removed the sides that contain its
  goal.)

**Lemma 4.** If `best > 0`, the plan has at least `sum over Σ of g(v_X, 0, 0)  +  best` crossings of the
bridges of Σ.

*Proof.* Say that a package *has to go into X* if it is undelivered, outside X now, and has its goal in
X, and *has to go out of X* if it is undelivered, in X now, with its goal outside. These are exactly the
packages behind `wi, bi` and `wo, bo` of the bridge. Packages that already lie at their goal are in
neither set, whatever a plan does with them.

The sides of Σ have no truck, so every package that is in U now is lying. `inside` is not empty, and by
(a) its members are the undelivered packages in U. Let τ be the first moment at which an **undelivered**
package that is in U now is loaded, let `q` be that package and `x` its location. `q` has not moved before
τ, so `x` is where `q` is now, `q` is in `inside`, and `v(q) >= best`.

Before τ, no undelivered package that is in U now has been inside a truck.

Take a side X of Σ that contains `x`. The truck that loads `q` is in X at time τ and X has no truck now,
so there is a first crossing of `e_X` into X, at a time σ before τ, and no crossing of `e_X` happens
before σ. Consider a package that has to go into X. It is not outside U now, by (b). So it is in U now,
it is undelivered, and therefore it has not been inside any truck before τ. Hence the truck that crosses
at σ does not carry it. So after σ every package that has to go out of X is still in X, every package
that has to go into X is still outside X, and the crossing truck `t` is in X.

Apply Lemma 1 to the rest of the plan after σ, with the truck lists `([cap(t)], co without t)`: its pair
`(zo, zi)` of crossings of `e_X` is feasible for these lists. Enlarging the lists keeps a pair feasible,
so the pair is also feasible for `([cmax] + cs, co)`, the lists the code uses. By Corollary 1 the rest of
the plan has at least `_crossings(wo, wi, bo, bi, [cmax] + cs, co, 0, 0)` crossings of `e_X`.
Together with the crossing at σ: crossings of `e_X` `>= 1 + _crossings(...) = g(v_X,0,0) + first_in(v_X)`.
(This is an identity in the code's own values, so it holds whether or not a cutoff was hit.)

For the sides of Σ that do not contain `x`, Corollary 1 gives `g(v_X,0,0)`. Summing, the excess over the
road-bridge term is at least `v(q) >= best`. The mirror case (`first_out`, all trucks inside the subtree)
is the same statement with the two sides exchanged. ∎

The bridges of Σ are road bridges that merge did not mark, so this excess is disjoint from section 8.

## 8. Merge bound

Fix a goal `g` and the undelivered packages with this goal. A *group* is the set of those packages inside
one truck, or lying at one location. Let there be `K >= 2` groups. For a group, its *path* is the set of
bridges between its place and `g`. The *chain* C is the set of bridges on all K paths (not yet used).
A bridge is *private* to group `i` if it is on the path of `i` and of no other group (and not used).
For a private bridge `b` of `i` let `B_b` be the side of `b` that does not contain `g` (it contains the
place of `i`).

*Private sides are disjoint.* If `b` is private to `i` and `b'` to `j != i`, then `B_b` and `B_b'` are
two subtrees of the bridge tree pointing away from `g`, so they are nested or disjoint. Nested would put
the place of one group behind the private bridge of the other, making that bridge shared. So they are
disjoint. In the same way, the truck of a truck group is never inside a private side of another group.

Costs used by the code: `cost_i = 2 * |group i|` for a truck group, and
`cost_i = min(2 * |group i|, det_i)` for a lying group, where `det_i` is the sum over its private road
bridges of `g(v,1,1) - g(v,0,0)` and over its private port bridges of
`max(0, 1 - boards) + max(0, 1 - disemb)` (the bounds of section 5).

**Lemma 5.** Let E_g be the number of LOADs and UNLOADs of these packages beyond the base term, plus the
crossings of the private and chain bridges beyond the terms of sections 4 and 5. Then
`E_g >= min over y in 1..K of [ (sum of the K - y smallest costs) + (chain excess for y) ]`,
where the chain excess for `y` is `g(v, y, 0) - g(v, 0, 0)` (or `g(v, 0, y) - ...`) per chain road bridge
and `max(0, y - bound)` per chain port bridge, with the direction in which the packages cross.

*Proof.* For a chain bridge `e`, partition the packages by the crossing event of `e` that is their last
crossing toward `g`. Let `y_e` be the number of classes, let `e*` minimise it, and put `y = min(K, y_e*)`.

*Chain.* Every chain bridge has at least `y_e >= y` crossings toward `g`. By Corollary 1 it has at least
`g(v, y, 0)` crossings in total (road), or at least `y` BOARDs or DISEMBARKs of the right kind (port).
So the excess over what sections 4 and 5 counted is at least the chain excess for `y`. (Corollary 1 is
used for the call with `a = y`. The subtracted `g(v,0,0)` is the code's own value, the one section 4
counted, so this holds even when a cutoff makes the difference negative.)

*Merges.* If `y = K` nothing more is claimed. Let `y = y_e* < K`. Call group `i` *paid* if
(a) every package of the group is loaded or unloaded at least 2 times more than the base term counts, or
(b) the group is lying and every private bridge of it is crossed at least once in each direction.
A paid group contributes at least `max(0, cost_i)` to E_g: in case (a) `2 * |group|`, in case (b) at least
`det_i` by Corollary 1 with `a = b = 1` and by the BOARD and DISEMBARK bounds, and never less than 0,
because the actual crossings are at least the counted `g(v,0,0)`. Contributions of different groups
concern different packages and different bridges.

An unpaid group `i` has, by not-(a), a package `p_i` with fewer than 2 extra actions. The extra count of
a package is even (each extra LOAD comes with an extra UNLOAD), so it is 0: `p_i` is carried by one truck
`T_i` from where it is now all the way to `g` (the truck that holds it now, or the first truck that
loads it). Map the group to the class of `p_i` at `e*`.

This map is injective. Suppose unpaid groups `i != j` share a class. Then `T_i = T_j = T`, since a class
is one truck at one moment. Both cannot be truck groups (different trucks). If `j` is lying, `T` loads
`p_j` at the place of `j`, which lies in `B_b` for every private bridge `b` of `j`, and later brings it to
`g` outside `B_b`. If `T` starts outside all these `B_b`, it crosses every private bridge of `j` in both
directions, so `j` is paid by (b). So `T` starts inside some private side of `j`. If `i` is a truck group,
`T` starts at the place of `i`, which is in no private side of `j`. If `i` is lying, the same argument
puts the start of `T` inside a private side of `i`, and private sides of different groups are disjoint.
Contradiction in all cases.

So at most `y` groups are unpaid and at least `K - y` are paid. Their contributions are at least the sum
of the `K - y` smallest values of `max(0, cost_i)`, which is at least the sum of the `K - y` smallest
costs. ∎

Every bridge that the bound of one goal looks at is marked `used` and is skipped by later goals and by the
first-entry term, and different goals have different packages. So the merge bounds of the goals add, and
`xfer` is their sum.

## 9. What the assumptions are for

* **(A1)** If a ferry starts at a port it does not serve, a truck can BOARD there without a port edge, and
  F1 fails. This is the only input on which my tests found `h > h*` (13 against 9). It contradicts the
  assignment's definition of a ferry, and no given problem does it.
* **(A2)** With a ferry of capacity 0, `_port_cost` divides by zero. Not an admissibility issue, a crash.

## 10. Assembly

Let L be the cost of the LOADs and UNLOADs of the plan and M the cost of all other actions.

* `L >= base + (LOAD/UNLOAD part of xfer)` by sections 3 and 8.
* `M >= T2 / 2 + (crossing part of xfer)`: the road-bridge, port-bridge, first-entry and non-bridge terms
  are lower bounds on pairwise disjoint sets of movement actions and half-sails (table in section 2),
  the crossing part of `xfer` is an excess over the bridge terms on bridges no other excess uses, and the
  additivity principle applies. Regions add because they share nothing.

`L + M` is an integer and `base`, `xfer` are integers, so `L + M >= base + ceil(T2 / 2) + xfer = h`.
This holds for every plan, hence for the cheapest one: `h <= h*`.
On a goal state nothing is undelivered, so every term is 0.

`h` is an integer by construction. `h >= 0`: the only terms that can be negative are differences of two
`_crossings` values (`exo`, `exi`, `road11`, `first_in`, `first_out`), and only when a cutoff is hit.
Each of them subtracts `g(v,0,0)` of one road bridge and adds at least 0, each bridge enters at most one
such difference (`used` marks, disjoint private bridges, one side per bridge in section 7), and that
`g(v,0,0)` is itself part of `T2 / 2`. So the sum is at least `base >= 0`. ∎

## 11. What this proof does and does not establish

It proves that the **bound described here** is admissible. That `ex1.py` computes exactly this bound
(bit packing, bridge detection, prefix sums, caches and memo keys) is an implementation question, and the
evidence for it is the exhaustive test, not this text:

* 2,223 solvable random games, the whole reachable state space enumerated with an independent
  implementation of the rules, exact `h*` for every state: `h <= h*` on 16.5 million world states and on
  21.1 million successor-reachable states, zero violations.
* The cached values go through the same check, so a wrong memo key would show as a violation.
* On the real problems (p1, p3, x1..x8, y1): no violation on the states of the optimal plans or on about
  320 random reachable states.

Limits: the random games are small (at most 12 locations, 4 packages), and the proof was written by an
LLM and should be read by a human. Sections 7 and 8 are the ones worth reading most carefully.
Consistency of `h` is not claimed and not needed: `graph_search` in `search.py` re-expands a state that
is reached again with a lower cost.

This document is about the heuristic only. That the pruning rules of `successor` keep an optimal plan is
a separate claim. It is tested (plan cost equal to the true optimum on about 2,400 random games and on
the 18 given problems) and not proved here.

## 12. Corrections in revision 2

An external review of revision 1 found three inaccuracies in the text. None of them changes the theorem.

1. **Section 4 and 7.** Revision 1 said that the value of `_crossings` does not increase when a truck is
   added, and section 7 used that. Because of the 200 cutoff this is false for the returned value
   (example in section 4). Section 7 now uses only that the *set of feasible pairs* grows, together with
   Corollary 1, which holds for whatever the code returns. Revision 1 also said that all terms are
   non-negative. Section 10 now proves `h >= 0` without that.
2. **Section 6.** The fractions use the largest capacity of the whole game, not of the region. Safe, and
   now stated.
3. **Section 7.** Revision 1 defined τ as the first load of any package in U. A plan may first pick up a
   package that already lies at its goal inside U. τ is now the first load of an *undelivered* package in
   U, and "has to go into X" is defined on undelivered packages. No normal form of the plan is needed.

Optional code repair, not applied: in `_crossings`, return `max(a + b, 201)` instead of `a + b` after the
loop. That makes the returned value monotone and all differences non-negative. It changes nothing unless
a single road bridge needs more than 200 crossings.
