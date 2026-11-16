# Optimality proof for the search in `ex1.py`: pruning, state merging, and their combination with the heuristic

Written against `ex1.py` with md5 `6961c1fc5e9aee03ae67c387160edd5a`. Updated for the additional normal forms in section 10. Companion of `ADMISSIBILITY_PROOF.md` (cited as [H]), which proves `h <= h*`.

Status in one line: the original staged construction is extended by section 10. Section 9 lists the
pre-existing caveats; section 10 documents the current additional rules.

## 0. The claim

**Theorem P.** For every solvable game in which every ferry starts at a port it serves, `astar_search`
of `search.py`, run with `successor`, `goal_test` and `h_astar` of `ex1.py`, returns a legal plan of the
minimum possible cost C*.

The assumption on ferries is used in one place only (Lemma 5, symmetry of the static data). Inputs
without it are covered by tests, not by this proof (section 9).

Notation. *World rules* = the six actions of the assignment with all their preconditions. C* = the least
cost of a sequence of world-legal actions from the start to a goal. A *plan* is such a sequence.

## 1. The three graphs

* **G0**: all states, all world-legal actions.
* **G1**: what `_successors` generates with every switch on. Its rules, as the code implements them:

| # | rule | where |
|---|---|---|
| R1 | a package lying at its goal is never loaded | `lying` skips it |
| R2 | forced: if a standing truck holds a package whose goal is its location, its only action is to unload the lowest-numbered such package | `forced` in `_truck_standing` |
| R3 | twins: of several identical objects in the same situation only the lowest-numbered acts. (a) packages of one class in one truck, for UNLOAD, (b) packages of one class lying at one place, for LOAD, (c) empty trucks with the same capacity and the same position code, when no focus is set, (d) empty ferries of one class at one port, for BOARD, (e) the same, for SAIL | `seen`, `seen_t`, `seen_f` |
| R4 | order: directly after a LOAD the truck does not UNLOAD (except R2) | `kind != 2` |
| R5 | focus: after a DRIVE or LOAD of truck t the next action is by t, optionally preceded by an empty sail for boarding (section 10.3) | `kind` 1, 2 |
| R6 | no U-turn directly after a DRIVE | `back` |
| R7 | fresh: no DISEMBARK before the ferry has sailed since the BOARD | odd / even truck code |
| R8 | barren: an empty truck does not cross a road bridge to a side with no lying undelivered package and no docked usable ferry | `adj_far`, `useful` |
| R9 | dead: no DRIVE into `dead_drive`, no SAIL to `dead_sail` (bridge sides without marks, dominated ports), no use of `dead_ferry` | `adj_go`, `sail_to`, `fdead` |
| R10 | parts: only the objects of the lowest-ranked part of the map that still has an undelivered package act. When that part is finished its trucks and ferries are written back to their start positions (`_finish`) | `multi`, `rank` |

Additional current rules: global eager goal unloading, endpoint-only corridor transfers, and empty
sails immediately followed by BOARD. Their implementation and proof are in section 10.

* **G2** (used only in the original proof): G1 without R3, and with R2 relaxed to "its only action is to unload
  *some* such package". G1 is a subgraph of G2, and G2 is a subgraph of G0 on the essential state below.

A *class* is: trucks of equal capacity, packages of equal weight and goal, ferries with the same served
ports and capacity. `_State` treats two tuples as equal when `_canon` gives the same key.

**Essential state.** Erase from a tuple (i) the positions of trucks and ferries of parts ranked below the
active one, (ii) which package a "has just loaded" focus refers to. `_successors` reads neither: finished
objects are skipped by the `multi` test before anything is read from them, their codes never equal the
code of an active ferry, their bits never meet a `far` mask of the active part, and the loaded package of
a focus is not used (`back` is taken only from a DRIVE focus). So the *actions* available in a state, and
the essential state they lead to, depend on the essential state only. `_finish` changes nothing essential.
From here on "state" means essential state, and R10's write-back needs no further argument.

For a graph G let `V_G(s)` be the least cost of a path in G from `s` to a goal state.

## 2. What has to be shown

1. **Lemma 0** (soundness): every G1 path from the start is a plan.
2. **Lemma 4** (completeness): G2 contains a path from the start of cost C*.
3. **Lemma 6**: `V_G1 = V_G2` on every state.
4. **Lemma 5**: `V_G2` is the same for states that `_State` treats as equal.
5. **Lemma 7**: under 1 to 4 and `h <= V_G1`, A* with this closed list returns cost C*.

## 3. Lemma 0: only legal actions

By inspection of `_truck_standing`, `_sail` and `_successors`: DRIVE is generated for a truck whose code
is a location, along `adj_go`, a subset of the roads. LOAD for a package lying at the truck's location
whose weight fits the remaining capacity. UNLOAD for a package inside a standing truck. BOARD for a ferry
docked at the truck's location with fewer trucks aboard than its capacity. DISEMBARK for a truck aboard.
SAIL to a port in `sail_to`, a subset of the served ports, different from the current one. The new tuple
is the old one with exactly the effect of the action (plus the fresh bit, the focus, and the write-back
of R10, none of which is world state of an object that acts again). ∎

So `V_G1(s) >= h*(s)`, and with [H]: `h(s) <= h*(s) <= V_G1(s)` for every state.

## 4. Lemma 4: an optimal plan survives all rules

Start from any plan of cost C*. Each stage below turns a plan of cost C* into a plan of cost C* and
keeps what the earlier stages established.

### Stage 1: parts (R10)

Trucks, ferries and packages never leave their part of the map, and no precondition mentions an object
of another part. So actions of different parts commute. Reorder the plan part by part, in rank order.
A part without packages contributes nothing to an optimal plan. The stages below work inside one part
and keep the actions of a part contiguous, so R10 holds from here on.

### Stage 2: dead ends and dominated ports (R9)

*Bridge sides.* Mark the start locations of trucks and the start and goal locations of packages. A side
of a bridge of the map graph G of [H] is *dead* if it has no mark. The nodes in no dead side form the
*core* (the part of the bridge tree spanned by the marks). Every other node lies in a maximal dead side D
that hangs on the core by one bridge. Define a map ρ, the identity on the core, and on D:

* the bridge is a road `(x, y)` with `y` in D: ρ(D) = the location `x`,
* the bridge is a port edge `(u, f)` with the ferry `f` in D: ρ(D) = the location `u`,
* the bridge is a port edge `(u, f)` with the port `u` in D: ρ(D) = `z`, a port of `f` in the core. (It
  exists: `f` is in the core. If its 2-edge-connected part has another node, that part contains a port of
  `f`. Otherwise `f` lies between two marked sides, and the first node on the way to either is a port.)

Apply ρ to the whole plan: a truck in D counts as standing at ρ(D), a ferry docked at a dead port `u`
counts as docked at `z`. Actions that move nothing after the mapping are dropped (drives inside D, sails
between two ports that map to the same port, everything done with ferries inside D). LOAD and UNLOAD in D
happen at ρ(D). A ferry that *starts* at a dead port keeps its real position until its first sail: no
truck starts in a dead side and none can reach it before the ferry moves, so nothing happens there.

The result is a plan: every remaining action has the same objects and the same contents, trucks that
were together at a location of D are together at ρ(D), a sail between any two served ports is one action,
and the number of trucks aboard a core ferry is unchanged. No package starts or ends in D, so the final
state is the same. The cost does not grow. The new plan never enters a dead side, never sails to a dead
port, and never uses a dead ferry: exactly `dead_drive`, the bridge part of `dead_sail`, and `dead_ferry`.

*Dominated ports.* An island I (locations joined by roads) without marks and without a ferry docked at
the start is eliminated by the code if one port `z` outside I is served by every ferry that serves I
(`z` not eliminated before, not a dead port for these ferries). Replace I by `z` in the plan: a truck on
I stands at `z`, a ferry at a port of I is at `z`, sails that no longer move are dropped. By the same
reasons as above this is a plan of no greater cost. If the island of `z` is eliminated later, with
substitute `z'`, every ferry serving I serves `z`, hence serves that island, hence serves `z'`: the two
replacements compose, and since `gone` only grows the chain ends at a port that is never eliminated.

The second replacement adds no DRIVE and no use of a new ferry, and its new sails go to ports that are
not dead for the ferries involved (a ferry serving I and `z` cannot have `z` behind a dead bridge side
that excludes I). So after both, R9 holds.

**From here on no stage adds a DRIVE, BOARD or SAIL**, so R9 stays true.

### Stage 3: unload at the goal at once (R2, relaxed form)

Property F: *whenever a standing truck holds a package whose goal is its location, the truck's next
action is an UNLOAD of such a package.*

Take the earliest moment where F fails: truck `t` stands at the goal of `p`, holds `p`, and its next
action is something else. (It has a next action, because `p` must still be unloaded.) Insert
`UNLOAD(p, t)` before that action and delete every later LOAD and UNLOAD of `p`. The plan stays legal
(`p` lies at its goal from then on, trucks only get lighter), and at least one later UNLOAD of `p` was
deleted, so the cost does not grow. Nothing before this moment changed, and `p` is never in a truck
again. Repeat: at most one round per package.

F is a property of each truck's own sequence of actions (what it holds is decided by its own LOADs and
UNLOADs).

### Facts about any plan of cost C*

Each of the following patterns can be deleted from a plan, leaving a legal plan that is cheaper. So a
plan of cost C* contains none of them. They need no stage, and they hold after every later stage because
the cost stays C*.

* (a) LOAD of a package that lies at its goal: delete this LOAD and every later LOAD and UNLOAD of the
  package. This is R1.
* (b) Truck `t` loads `p` and later unloads `p` with no move of `t` in between: delete both. Nobody else
  can touch `p` in between.
* (c) `BOARD(t, f)` and the next `DISEMBARK(t, f)` with no sail of `f` in between: delete both. `t`
  stands at the port instead, and the ferry only has more room. This is R7.
* (d) `DRIVE(t, a, b)` directly followed by `DRIVE(t, b, a)`: delete both. This is R6, once R5 makes
  "the next action of t" and "the next action" the same thing.
* (e) A last action of a truck that is a DRIVE or a LOAD: delete it.
* (f) An empty truck that crosses a road bridge and comes back over it with only its own DRIVEs in
  between: delete the round trip.

### Stage 4: unloads before loads at every stop (prepares R4)

A *stop* of truck `t` is a maximal run, in `t`'s own sequence, of LOADs and UNLOADs with no move of `t`
between them. Let the stop occupy the time slots τ1 < ... < τm of the plan. Put the UNLOADs of the stop,
in their order, into the first slots and the LOADs, in their order, into the remaining ones.

The result is a plan:
* An UNLOAD moves to an earlier slot. Its package was in `t` before the stop (not loaded at this stop,
  by fact (b)), so it can be unloaded there. Other trucks only find the package available sooner.
* A LOAD moves to a later slot. In the old plan the package was inside `t` from its LOAD to the end of
  the stop (fact (b) again), so no other truck used it in between. Now it simply lies there longer.
* The weight in `t` is at most its weight before the stop while unloading, and at most its weight after
  the stop while loading. Both were legal.

Every truck's sequence keeps its moves, and the UNLOADs keep their order, so F still holds (the
goal-bound UNLOADs were first in the stop and still are). Do this for every stop.

### Stage 5: focus (R5)

**Claim.** A plan in which no truck ends with a DRIVE or LOAD can be reordered, without changing any
truck's own sequence, so that every DRIVE and LOAD of a truck is directly followed by an action of the
same truck.

*Commutation.* Let α be a DRIVE or LOAD of `t` and γ an action that does not involve `t`, directly after
α. Then γ, α is legal and gives the same state. For a DRIVE: no precondition of another object mentions
where a standing truck is, and `t` is standing before and after. For a LOAD of `p`: after α the package
is inside `t`, so γ does not touch it, and before α it lies still.

*Proof of the claim*, by induction on the length. Let β be the last action. If β is an UNLOAD or BOARD of
`t`, let α1..αk be the DRIVEs and LOADs of `t` that directly precede β in `t`'s own sequence (as many as
there are). Move them, in order, to just before β. The rest π' is a plan, and no truck ends it with a
DRIVE or LOAD: for `t` by the choice of α1, for the others because nothing changed. If β is a DISEMBARK
or SAIL, π' is the plan without β, and the truck of a DISEMBARK ends π' with its BOARD. By induction π'
can be reordered, and appending α1..αk β keeps the property. ∎

Apply the claim to each part's block (fact (e) gives the hypothesis). Stages 1 to 4 survive: the
multiset of actions is the same (R9, cost C*), parts stay contiguous (R10), and F and "unloads before
loads at every stop" are properties of each truck's own sequence.

### The result is a path in G2

Check every rule of G2 on the final plan π.

* R5: by stage 5. A SAIL or DISEMBARK, and an action of another truck, never directly follow a DRIVE or
  LOAD, which is exactly when the code offers them.
* R1, R7: facts (a), (c).
* R6: fact (d) with R5.
* R2 (relaxed): property F.
* R4: after a LOAD of `t` the next action is by `t` (R5). If it were an UNLOAD, both would be in one stop
  with a LOAD before an UNLOAD, against stage 4.
* R8: let an empty `t` cross a road bridge `e`. By R5 the plan continues with actions of `t` only, until
  `t` makes an UNLOAD or BOARD, and by fact (e) it does. `t` is empty, so until its first LOAD or BOARD
  it only drives, and nothing else in the world changes. By fact (f) it does not come back over `e` before
  that. So the first LOAD or BOARD happens on the far side of `e`: at a location where, already at the
  moment of the crossing, a package lay that is not at its goal (fact (a)), or a ferry was docked that is
  not dead (R9). That is the bit the code tests in `useful`.
* R9, R10: stages 2 and 1.

π has cost C* and every G2 path is a plan, so `V_G2(start) = C*`. ∎

## 5. Lemma 5: symmetry of G2

**Static data.** If every ferry starts at a served port, two ferries of one class have the same
neighbours in the map graph, so exchanging them is an automorphism of that graph that fixes all marks.
Hence `dead_ferry` and `dead_sail` treat them alike, and so does the dominated-port rule, which speaks
about "every ferry that serves the island". Trucks and packages carry no static pruning data beyond their
class and their part.

**From equal keys to a renaming.** If two states reachable from the start have the same `_canon` key,
there is a renaming σ of objects, preserving classes, with σ(s) = s'. The key is the multiset of standing
trucks (location, capacity, focus flag, classes held), the multiset of ferries (class, port, and for each
truck aboard: fresh bit, capacity, classes held) and the multiset of lying packages (location, class).
Matching equal entries gives σ on trucks, then on ferries with the trucks aboard, then on packages inside
matched trucks and at matched places. Matched objects are at the same place, so σ preserves the parts of
the map too.

**Equivariance.** Every rule of G2 is stated through positions, classes, the focus flag and static data
that is equal within a class. None mentions an object's number. So if `s -> u` is an edge of G2 with
action `a`, then `σ(s) -> σ(u)` is an edge with the renamed action and the same cost, and goals map to
goals. Hence `V_G2(σ(s)) = V_G2(s)`. ∎

## 6. Lemma 6: the lowest-number rules lose nothing (`V_G1 = V_G2`)

G1 is a subgraph of G2, so `V_G1 >= V_G2`. For the other direction take a cheapest G2 path from `s` and
look at its first edge that is not in G1. Only R3 or the "lowest-numbered" part of R2 can exclude it.

* **R3.** The path uses object `x` where G1 demands its twin `x0`. In each of the five cases (a) to (e)
  the two objects are interchangeable *in this state*: two packages of one class in the same truck or at
  the same place, two empty trucks with the same capacity and code and no focus set, two empty ferries of
  one class at one port. So the exchange τ of `x` and `x0` fixes the state. By equivariance, renaming the
  rest of the path by τ gives a G2 path from the same state, of the same cost, whose first edge uses `x0`.
* **R2.** Truck `t` unloads the goal-bound `q` where G1 demands the goal-bound `p`. In G2 every action of
  `t` is an UNLOAD of a goal-bound package until none is left, so the path contains `UNLOAD(p, t)` later,
  with only actions of other objects and such UNLOADs of `t` in between. Exchange the two UNLOADs. The
  states in between differ only in which of `p`, `q` is still inside `t`. No rule of another object reads
  that: `t` is non-empty either way, both packages have the same goal (same part, same count of
  undelivered packages), and a package lying at its goal is invisible to every rule. So the new sequence
  is a G2 path of the same cost, and it reaches the same state after the second UNLOAD.

In both cases the path is unchanged before the edge, and the edge is now in G1. Repeat with the next
offending edge, which lies further along. The path is finite, so this ends with a G1 path of the same
cost. ∎

With Lemma 4: `V_G1(start) = C*`. With Lemma 5: `V_G1` is the same for states that `_State` treats as
equal.

## 7. Lemma 7: A* with merged states

`graph_search` pops the node with the least `f = g + h`, returns it if it is a goal, and otherwise
expands it unless a node with an equal state (equal key) was expanded before with a cost not larger.
Write V for `V_G1`. Facts used: V is the same for equal states (section 6), `h <= V` (section 3),
V(s) = min over G1 edges of cost + V(next), costs are positive, and V = 0 exactly on goals.

**Invariant.** Until a goal is returned, the frontier contains a node `w` with `g(w) + V(w) <= C*`.

*Proof.* True at the start. Suppose it is true and the popped node is the only such `w`.
If `w` is expanded, the child along a cheapest continuation has `g + V = g(w) + V(w)`.
If `w` is skipped, a node `w'` with an equal state and `g(w') <= g(w)` was expanded earlier. Then
`g(w') + V(w') <= C*`, and its child `c` along a cheapest continuation was pushed with `g + V <= C*` and
`V(c) < V(w)`. If `c` is still in the frontier we are done. If not, `c` was popped earlier and was
expanded or skipped, and the same step applies to it. V strictly decreases along this chain, so it ends
at a node in the frontier, or at a popped node with V = 0, a goal, at which the search would already
have returned. ∎

So when a goal node `m` is popped, some frontier node `w` had `f(w) = g(w) + h(w) <= g(w) + V(w) <= C*`,
and `f(m) = g(m) <= f(w) <= C*`. Its path is a G1 path, hence a plan (Lemma 0), hence costs at least C*.
The pruned graph is finite and has a goal reachable from the start (Lemma 4 and 6), so a goal is popped.
The heuristic need not be consistent: the re-opening test `path_cost < closed[state]` is what the skip
rule above describes. ∎ Theorem P.

## 8. Targeted tests (support for the lemmas, with an independent exact solver)

`util/prune_check.py`. For each small random game the true optimum C* comes from the independent
implementation of the rules (`Ref`). Then, for a configuration of the switches, the *whole* pruned graph
is enumerated on raw tuples, without the heuristic, and V is computed for every state. Checked:

* P1: `V(start) = C*` (Lemmas 4 and 6 for that configuration),
* P2: V is equal for all states with the same `_canon` key (Lemma 5 and 6, tested directly on every state),
* P3: every edge is a legal action with the right effect (Lemma 0). The effect must equal the effect
  the independent rules give, with one permitted deviation computed by the checker itself, not taken from
  `ex1.py`: when an action delivers the last package of a part of the map, the trucks and ferries of
  exactly that part are back at their start positions.

26 configurations: all rules on, no rule, every rule alone (the rules that only exist together with focus
are added to focus one at a time), and all rules but one.

**Correction after review.** The first version of P3 accepted *any* difference in truck or ferry
positions as soon as the map had several parts, so it did not verify effects there. An external reviewer
showed this by injecting a wrong DRIVE effect that went unnoticed. P3 is now exact as described above, and
the same loose test in `validate.py` was fixed. `util/mutate.py` injects that fault: it is caught in
every game where a DRIVE is generated (155 of 155 with one part, 53 of 53 with several parts).

The review also exposed a coverage gap: the random profiles almost never produced a map with several
parts, so R10 was tested on very few games. Profile D (two or three independent maps side by side, some
with trucks and no packages) was added for it.

Results with the exact P3, fresh seeds, each game in all 26 configurations, **0 failures** of P1, P2, P3:

| profile | solvable games |
|---|---|
| S small | 231 |
| M medium | 61 |
| H many ferries | 68 |
| X inputs outside the assignment's wording | 183 |
| D several parts | 191 |

`validate.py` with the exact effect test (all rules on, plus `h <= h*` on every state): S 330, X 295,
D 224 solvable games, 0 failures.

The earlier campaign (1,440 games, 26 configurations, 0 failures) was run with the loose P3. Its P1 and
P2 results stand. Its P3 results count only for maps with one part.

A failure of P1 in the configuration "all rules" would be a real counterexample to Theorem P. A failure
in a partial configuration would show a rule that is only correct in combination with others. Neither
occurred, so no rule was weakened or removed.

## 9. What this proof does and does not establish

* Proved: Theorem P for the rules **as described in section 1**, under the stated assumption on ferries.
* By inspection plus tests: that `_successors` implements exactly these rules (P3 and the reading in
  section 1), and that `_canon` equality is the renaming equivalence of Lemma 5.
* **Not proved: inputs where a ferry starts at a port it does not serve.** Lemma 5's "static data" step
  fails to apply, so for these inputs the correctness of twins and state merging rests on tests only
  (profile X, including P2). Until that step is proved or the rules are switched off for such inputs,
  pruning correctness there is an open item, not a settled one.
* The proof was written by an LLM. The steps most worth a second reading: stage 2 (the map ρ and the
  ferry that starts at a dead port), stage 4, and the R2 case of Lemma 6.
* Not covered at all: running time.
## 10. Additional normal forms (2026-11-16)

This section extends Theorem P and the rule table in section 1. The admissible heuristic remains a
bound on unrestricted world completions; the rules here only reduce the graph searched for a plan.

### 10.1 Empty road corridors (`OPT_CORRIDOR`)

An anchor is a road vertex of degree other than two, an initial truck position, an initial package
position, a package goal, or a port in any ferry's `gports`. The interiors of paths between anchors are
empty degree-two road corridors. `_truck_standing` allows UNLOAD only at anchors. Deliveries are not
removed, since every goal is an anchor. Initially no package lies inside a corridor, and no UNLOAD can
put one there, so no interior LOAD is subsequently needed either.

To prove this preserves an optimum, fix any legal plan and one corridor of L unit road edges, numbered
0 through L. For each threshold j in 1..L, map vertices 0..j-1 to endpoint 0 and vertices j..L to endpoint
L. Leave the rest of the map fixed. Map every action's locations this way. Replace a DRIVE whose ends
map to the same endpoint by no action; replace a DRIVE crossing edge j by the L consecutive drives
along the corridor. LOAD/UNLOAD actions still have their original truck/package and capacities; their
colocations are preserved. No port, initial position, or goal moves. Expanded drives may pass other
objects without acting on them, which is legal. Thus each threshold gives a legal plan with all this
corridor's transfers at endpoints.

If the original plan traverses corridor edge j a total of N_j times, the transformed plan uses L*N_j
DRIVEs there. The average of these costs over the L thresholds is `sum_j N_j`, exactly the original
corridor driving cost. Some threshold therefore does not increase cost. Apply this independently to
all corridors. A cycle attached at only one anchor can be collapsed to that anchor; a component with
no anchor contains no initial truck or package and need not be visited.

Now apply the previous normalizations. They reorder existing transfers or remove actions; they do not
create an interior transfer. Thus at least one minimum-cost plan survives the combined rules.
This is a proof about total driving cost, and does not require equal truck capacities.

### 10.2 Eager goal unloading

With no truck focus active, if any truck can unload a package at its goal, the successor function now
chooses such an unload globally before other actions. Delivering it now cannot obstruct an action:
it frees truck capacity, and a package at its goal need never be loaded again. Move this unload ahead
of the intervening actions in the existing forced-unload argument. Only the active component is used.
Within a truck focus, `_truck_standing` still offers the forced unload; the focused empty-sail branch
also permits the additional legal choices discussed in section 10.3. No additional unloading history
is needed.

### 10.3 Empty sails immediately before boarding (`OPT_LAZYSAIL`)

Take an empty ferry's movements before its next BOARD. There can be no DISEMBARK in this interval.
Consecutive empty repositionings can be replaced by one sail from the ferry's current port directly to
that BOARD's port (or no sail if already there): a ferry can sail directly to every served destination.
If there is no later BOARD, delete those movements. Move the remaining empty sail immediately before
the BOARD. Intervening actions involve neither the empty ferry nor a truck aboard it, so delaying the
sail does not invalidate them. Its destination now has a standing truck ready to board.

The implementation retains exactly this form: an empty ferry may sail only to a currently standing
truck, and the resulting `FE0 + f` state permits only a BOARD on that ferry. Loaded-ferry sailing is
unchanged. The pending-ferry flag is part of `_canon`, including under ferry renaming; it cannot merge
with a state that has no pending BOARD.

There is an essential interaction with truck focus. A truck may have just driven to the port or loaded
there before the ferry arrives. The focused branch therefore allows the empty sail to that truck's
port, followed by the pending BOARD. For the focus proof, treat the consecutive empty-SAIL/BOARD pair
as the boarding truck's next operation. Other trucks' DRIVE/LOAD actions commute with it exactly as
with the original BOARD. This avoids requiring an anticipatory empty sail that this rule removes.

The implementation is intentionally more permissive than the witnessing normal form: the focused
branch may offer an empty sail despite a goal unload being available, and the pending state may board
any colocated truck, including one still carrying a goal package. The proof does not require every
generated plan to unload eagerly. Construct the witness by moving a goal unload before the empty
sail and BOARD; unloading frees capacity and leaves the truck at the same port, so both remain legal.
An unrelated truck's intervening DRIVE/LOAD commutes with that unload and can be delayed to its next
operation by the focus normalization. Then schedule the empty-sail/BOARD pair as above. Thus an eager
optimal witness remains available. The extra boarding choices are world-legal and cannot remove it
or produce a cost below the unrestricted world optimum. The old R2 description is subject to this
permissive pending-boarding exception.

For barren-road pruning, a road-bridge side containing a served destination port also contains that
ferry's graph node and every port it can currently occupy; otherwise another edge would cross the same
bridge cut. Its docked port therefore marks that side useful already. Delaying the empty sail does not
prevent an empty truck from approaching a needed boarding port across a road bridge.

Together, the corridor mapping, eager deliveries, and delayed empty-sail/BOARD pairs can be applied
before the existing focus/no-op/twin/component normalizations. They preserve at least one optimal plan.
The pre-existing caveat in section 9 about symmetry for unserved initial ferry ports remains unchanged.
