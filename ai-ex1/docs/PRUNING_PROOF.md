# Optimality proof for the search in `ex1.py`: pruning, state merging, and their combination with the heuristic

Written against the Git (LF) contents of `ex1.py` with md5 `5feb2f57385ffc13eba96fd5bb576ff6`. Companion of `ADMISSIBILITY_PROOF.md` (cited as [H]), which proves `h <= h*`.

Sections 1–10 prove the normal forms for nonnegative integer cargo. Section 11 treats other
weights under the simulator's LOAD rule.

## 0. The claim

**Theorem P.** For every solvable game in the domain of [H], section 0, `astar_search`
of `search.py`, run from the game's designated initial layout with `successor`, `goal_test` and
`h_astar` of `ex1.py`, returns a legal plan of the minimum possible cost C\*.

Sections 0.1–0.2 of [H] prove `h <= h*` by projecting real loads into an integer problem
and bounding the cost of every completion there.
Only the heuristic uses the relaxed truck loads. Successor legality is checked in the real world.

Notation. _World rules_ = the six actions of the assignment with all their preconditions. C* = the least
cost of a sequence of world-legal actions from the start to a goal. A *plan\* is such a sequence.

## 1. The three graphs

- **G0**: all states, all world-legal actions.
- **G1**: what `_successors` generates with every switch on. Its rules, as the code implements them:

| #   | rule                                                                                                                                                                                                                                                                                                                                                                         | where                         |
| --- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------- |
| R1  | a package lying at its goal is never loaded                                                                                                                                                                                                                                                                                                                                  | `lying` skips it              |
| R2  | forced: if a standing truck holds a package whose goal is its location, its only action is to unload the lowest-numbered such package                                                                                                                                                                                                                                        | `forced` in `_truck_standing` |
| R3  | twins: of several identical objects in the same situation only the lowest-numbered acts. (a) packages of one class in one truck, for UNLOAD, (b) packages of one class lying at one place, for LOAD, (c) empty trucks with the same capacity and the same position code, when no focus is set, (d) empty ferries of one class at one port, for BOARD, (e) the same, for SAIL | `seen`, `seen_t`, `seen_f`    |
| R4  | order: directly after a LOAD the truck does not UNLOAD (except R2)                                                                                                                                                                                                                                                                                                           | `kind != 2`                   |
| R5  | focus: after a DRIVE or LOAD of truck t the next action is by t, optionally preceded by an empty sail for boarding (section 10.3)                                                                                                                                                                                                                                            | `kind` 1, 2                   |
| R6  | no U-turn directly after a DRIVE                                                                                                                                                                                                                                                                                                                                             | `back`                        |
| R7  | fresh: no DISEMBARK before the ferry has sailed since the BOARD                                                                                                                                                                                                                                                                                                              | odd / even truck code         |
| R8  | barren: an empty truck does not cross a road bridge to a side with no lying undelivered package and no docked usable ferry                                                                                                                                                                                                                                                   | `adj_far`, `useful`           |
| R9  | dead: no DRIVE into `dead_drive`, no SAIL to `dead_sail` (bridge sides without marks, dominated ports), no use of `dead_ferry`                                                                                                                                                                                                                                               | `adj_go`, `sail_to`, `fdead`  |
| R10 | parts: only the objects of the lowest-ranked part of the map that still has an undelivered package act. When that part is finished its trucks and ferries are written back to their start positions (`_finish`)                                                                                                                                                              | `multi`, `rank`               |

Additional current rules: global eager goal unloading, endpoint-only corridor transfers, and empty
sails immediately followed by BOARD. Their implementation and proof are in section 10.

- **G2** (used only in the original proof): G1 without R3, and with R2 relaxed to "its only action is to unload
  _some_ such package". G1 is a subgraph of G2, and G2 is a subgraph of G0 on the essential state below.

A truck class has one effective capacity (floored for integer cargo). A package class has one weight
and goal, or one identity in section 11. A ferry class has one served-port set, one set of graph
neighbours including its initial dock, and one truck-slot count. `_State` treats two tuples as equal
when `_canon` gives the same key.

**Essential state.** Erase from a tuple (i) the positions of trucks and ferries of parts ranked below the
active one, (ii) which package a "has just loaded" focus refers to. `_successors` reads neither: finished
objects are skipped by the `multi` test before anything is read from them, their codes never equal the
code of an active ferry, their bits never meet a `far` mask of the active part, and the loaded package of
a focus is not used (`back` is taken only from a DRIVE focus). So the _actions_ available in a state, and
the essential state they lead to, depend on the essential state only. `_finish` changes nothing essential.
From here on "state" means essential state, and R10's write-back needs no further argument.

For a graph G let `V_G(s)` be the least cost of a path in G from `s` to a goal state.

## 2. What has to be shown

1. **Lemma 0** (soundness): every goal-reaching G1 path from the start is a plan.
2. **Lemma 4** (completeness): G2 contains a path from the start of cost C\*.
3. **Lemma 6**: `V_G1 = V_G2` on every state.
4. **Lemma 5**: `V_G2` is the same for states that `_State` treats as equal.
5. **Lemma 7**: under 1 to 4 and `h <= V_G1`, A* with this closed list returns cost C*.

## 3. Lemma 0: only legal actions

By inspection of `_truck_standing`, `_sail` and `_successors`: DRIVE is generated for a truck whose code
is a location, along `adj_go`, a subset of the roads. LOAD for a package lying at the truck's location
whose held-weight sum plus the new weight fits the capacity, as in section 11. UNLOAD for a package inside a standing truck. BOARD for a ferry
docked at the truck's location with fewer trucks aboard than its capacity. DISEMBARK for a truck aboard.
SAIL to a port in `sail_to`, a subset of the served ports, different from the current one. The new tuple
is the old one with exactly the effect of the action (plus the fresh bit, the focus, and the write-back
of R10, none of which is world state of an object that acts again). ∎

For any reachable search state, fix a world replay of its path. The unfinished regions have
the same positions and custody in both representations. A finished region has no pending
package and contributes zero to `_bound` regardless of the vehicle positions written by R10.
Thus the heuristic equals its value on the world replay even if an unserved dock makes the
reset tuple itself unreachable. Any goal-reaching continuation replays legally at the same cost.
Applying [H] to the reachable replay gives `h(s) <= h*(replay) <= V_G1(s)`.

## 4. Lemma 4: an optimal plan survives all rules

Start from any plan of cost C*. Each stage below turns a plan of cost C* into a plan of cost C\* and
keeps what the earlier stages established.

### Stage 1: parts (R10)

Trucks, ferries and packages never leave their part of the map, and no precondition mentions an object
of another part. So actions of different parts commute. Reorder the plan part by part, in rank order.
A part without packages contributes nothing to an optimal plan. The stages below work inside one part
and keep the actions of a part contiguous, so R10 holds from here on.

### Stage 2: dead ends and dominated ports (R9)

_Bridge sides._ Mark the start locations of trucks and the start and goal locations of packages. A side
of a bridge of the map graph G of [H] is _dead_ if it has no mark. The nodes in no dead side form the
_core_ (the part of the bridge tree spanned by the marks). Every other node lies in a maximal dead side D
that hangs on the core by one bridge. Define a map ρ, the identity on the core, and on D:

- the bridge is a road `(x, y)` with `y` in D: ρ(D) = the location `x`,
- the bridge is a port edge `(u, f)` with the ferry `f` in D: ρ(D) = the location `u`,
- the bridge is a port edge `(u, f)` with the port `u` in D: choose ρ(D) = `z`, a **served** port of
  `f` in the core. If `f` belongs to a nontrivial bridge component it has at least two neighbours
  in that component. Otherwise its unmarked singleton lies strictly between two marked sides and has
  at least two core neighbours. At most one neighbour is an unserved initial dock, so a served choice exists.

Apply ρ to the whole plan: a truck in D counts as standing at ρ(D), a ferry docked at a dead port `u`
counts as docked at `z`. Actions that move nothing after the mapping are dropped (drives inside D, sails
between two ports that map to the same port, everything done with ferries inside D). LOAD and UNLOAD in D
happen at ρ(D). A core ferry initially docked in D is the unique way for a truck to enter D.
Until that ferry first sails, no truck can board it there. For its first original sail use the
actual initial dock as source and the mapped target as destination, even if the two *mapped*
ports coincide. That destination is served, and this costs at most the one original sail.

The result is a plan: every remaining action has the same objects and the same contents, trucks that
were together at a location of D are together at ρ(D), a sail between any two served ports is one action,
and the number of trucks aboard a core ferry is unchanged. No package starts or ends in D, so all final
package goals are preserved. The cost does not grow. The new plan never enters a dead side, never sails to a dead
port, and never uses a dead ferry: exactly `dead_drive`, the bridge part of `dead_sail`, and `dead_ferry`.

_Dominated ports._ An island I (locations joined by roads) without marks and without a ferry docked at
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

Property F: _whenever a standing truck holds a package whose goal is its location, the truck's next
action is an UNLOAD of such a package._

Take the earliest moment where F fails: truck `t` stands at the goal of `p`, holds `p`, and its next
action is something else. (It has a next action, because `p` must still be unloaded.) Insert
`UNLOAD(p, t)` before that action and delete every later LOAD and UNLOAD of `p`. The plan stays legal
(`p` lies at its goal from then on, trucks only get lighter), and at least one later UNLOAD of `p` was
deleted, so the cost does not grow. Nothing before this moment changed, and `p` is never in a truck
again. Repeat: at most one round per package.

F is a property of each truck's own sequence of actions (what it holds is decided by its own LOADs and
UNLOADs).

### Facts about any plan of cost C\*

Each of the following patterns can be deleted from a plan, leaving a legal plan that is cheaper. So a
plan of cost C* contains none of them. They need no stage, and they hold after every later stage because
the cost stays C*.

- (a) LOAD of a package that lies at its goal: delete this LOAD and every later LOAD and UNLOAD of the
  package. This is R1.
- (b) Truck `t` loads `p` and later unloads `p` with no move of `t` in between: delete both. Nobody else
  can touch `p` in between.
- (c) `BOARD(t, f)` and the next `DISEMBARK(t, f)` with no sail of `f` in between: delete both. `t`
  stands at the port instead, and the ferry only has more room. This is R7.
- (d) `DRIVE(t, a, b)` directly followed by `DRIVE(t, b, a)`: delete both. This is R6, once R5 makes
  "the next action of t" and "the next action" the same thing.
- (e) A last action of a truck that is a DRIVE or a LOAD: delete it.
- (f) An empty truck that crosses a road bridge and comes back over it with only its own DRIVEs in
  between: delete the round trip.

### Stage 4: unloads before loads at every stop (prepares R4)

A _stop_ of truck `t` is a maximal run, in `t`'s own sequence, of LOADs and UNLOADs with no move of `t`
between them. Let the stop occupy the time slots τ1 < ... < τm of the plan. Put the UNLOADs of the stop,
in their order, into the first slots and the LOADs, in their order, into the remaining ones.

The result is a plan:

- An UNLOAD moves to an earlier slot. Its package was in `t` before the stop (not loaded at this stop,
  by fact (b)), so it can be unloaded there. Other trucks only find the package available sooner.
- A LOAD moves to a later slot. In the old plan the package was inside `t` from its LOAD to the end of
  the stop (fact (b) again), so no other truck used it in between. Now it simply lies there longer.
- The weight in `t` is at most its weight before the stop while unloading, and at most its weight after
  the stop while loading. Both were legal.

Every truck's sequence keeps its moves, and the UNLOADs keep their order, so F still holds (the
goal-bound UNLOADs were first in the stop and still are). Do this for every stop.

### Stage 5: focus (R5)

**Claim.** A plan in which no truck ends with a DRIVE or LOAD can be reordered, without changing any
truck's own sequence, so that every DRIVE and LOAD of a truck is directly followed by an action of the
same truck.

_Commutation._ Let α be a DRIVE or LOAD of `t` and γ an action that does not involve `t`, directly after
α. Then γ, α is legal and gives the same state. For a DRIVE: no precondition of another object mentions
where a standing truck is, and `t` is standing before and after. For a LOAD of `p`: after α the package
is inside `t`, so γ does not touch it, and before α it lies still.

_Proof of the claim_, by induction on the length. Let β be the last action. If β is an UNLOAD or BOARD of
`t`, let α1..αk be the DRIVEs and LOADs of `t` that directly precede β in `t`'s own sequence (as many as
there are). Move them, in order, to just before β. The rest π' is a plan, and no truck ends it with a
DRIVE or LOAD: for `t` by the choice of α1, for the others because nothing changed. If β is a DISEMBARK
or SAIL, π' is the plan without β, and the truck of a DISEMBARK ends π' with its BOARD. By induction π'
can be reordered, and appending α1..αk β keeps the property. ∎

Apply the claim to each part's block (fact (e) gives the hypothesis). Stages 1 to 4 survive: the
multiset of actions is the same (R9, cost C\*), parts stay contiguous (R10), and F and "unloads before
loads at every stop" are properties of each truck's own sequence.

### The result is a path in G2

Check every rule of G2 on the final plan π.

- R5: by stage 5. A SAIL or DISEMBARK, and an action of another truck, never directly follow a DRIVE or
  LOAD, which is exactly when the code offers them.
- R1, R7: facts (a), (c).
- R6: fact (d) with R5.
- R2 (relaxed): property F.
- R4: after a LOAD of `t` the next action is by `t` (R5). If it were an UNLOAD, both would be in one stop
  with a LOAD before an UNLOAD, against stage 4.
- R8: let an empty `t` cross a road bridge `e`. By R5 the plan continues with actions of `t` only, until
  `t` makes an UNLOAD or BOARD, and by fact (e) it does. `t` is empty, so until its first LOAD or BOARD
  it only drives, and nothing else in the world changes. By fact (f) it does not come back over `e` before
  that. So the first LOAD or BOARD happens on the far side of `e`: at a location where, already at the
  moment of the crossing, a package lay that is not at its goal (fact (a)), or a ferry was docked that is
  not dead (R9). That is the bit the code tests in `useful`.
- R9, R10: stages 2 and 1.

π has cost C* and every goal-reaching G2 path from the start is a plan, so `V_G2(start) = C*`. ∎

## 5. Lemma 5: symmetry of G2

**Static data.** The ferry class key includes both `fports` and `gports`. Two ferries of one class
have the same legal destinations and precisely the same neighbours in the map graph, including any
unserved initial dock. Exchanging their graph nodes is therefore an automorphism fixing all locations and marks.
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

- **R3.** The path uses object `x` where G1 demands its twin `x0`. In each of the five cases (a) to (e)
  the two objects are interchangeable _in this state_: two packages of one class in the same truck or at
  the same place, two empty trucks with the same capacity and code and no focus set, two empty ferries of
  one class at one port. So the exchange τ of `x` and `x0` fixes the state. By equivariance, renaming the
  rest of the path by τ gives a G2 path from the same state, of the same cost, whose first edge uses `x0`.
  A LOAD can require both a truck swap and a package swap. A BOARD can require both a truck swap and
  a ferry swap. The truck in the truck-twin rule is empty, the package twins lie together, and the
  ferry twins are empty at the same port. Swaps across these object types preserve each other's
  eligibility and fix the current state. Compose all required swaps before advancing to the next edge.
- **R2.** Truck `t` unloads the goal-bound `q` where G1 demands the goal-bound `p`. In G2 every action of
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

## 7. Lemma 7: A\* with merged states

`graph_search` pops the node with the least `f = g + h`, returns it if it is a goal, and otherwise
expands it unless a node with an equal state (equal key) was expanded before with a cost not larger.
Write V for `V_G1`. Facts used: V is the same for equal states (section 6), `h <= V` (section 3),
V(s) = min over G1 edges of cost + V(next), costs are positive, and V = 0 exactly on goals.

**Invariant.** Until a goal is returned, the frontier contains a node `w` with `g(w) + V(w) <= C*`.

_Proof._ True at the start. Suppose it is true and the popped node is the only such `w`.
If `w` is expanded, the child along a cheapest continuation has `g + V = g(w) + V(w)`.
If `w` is skipped, a node `w'` with an equal state and `g(w') <= g(w)` was expanded earlier. Then
`g(w') + V(w') <= C*`, and its child `c` along a cheapest continuation was pushed with `g + V <= C*` and
`V(c) < V(w)`. If `c` is still in the frontier we are done. If not, `c` was popped earlier and was
expanded or skipped, and the same step applies to it. V strictly decreases along this chain, so it ends
at a node in the frontier, or at a popped node with V = 0, a goal, at which the search would already
have returned. ∎

So when a goal node `m` is popped, some frontier node `w` had `f(w) = g(w) + h(w) <= g(w) + V(w) <= C*`,
and `f(m) = g(m) <= f(w) <= C*`. Its path is a G1 path, hence a plan (Lemma 0), hence costs at least C\*.
The pruned graph is finite and has a goal reachable from the start (Lemma 4 and 6), so a goal is popped.
The heuristic need not be consistent: the re-opening test `path_cost < closed[state]` is what the skip
rule above describes. ∎ Theorem P.

## 8. Targeted tests (support for the lemmas, with an independent exact solver)

`util/prune_check.py`. For each small random game the true optimum C* comes from the independent
implementation of the rules (`Ref`). Then, for a configuration of the switches, the *whole\* pruned graph
is enumerated on raw tuples, without the heuristic, and V is computed for every state. Checked:

- P1: `V(start) = C*` (Lemmas 4 and 6 for that configuration),
- P2: V is equal for all states with the same `_canon` key (Lemma 5 and 6, tested directly on every state),
- P3: every edge is a legal action with the right effect (Lemma 0). The effect must equal the effect
  the independent rules give, with one permitted deviation computed by the checker itself, not taken from
  `ex1.py`: when an action delivers the last package of a part of the map, the trucks and ferries of
  exactly that part are back at their start positions.

26 configurations: all rules on, no rule, every rule alone (the rules that only exist together with focus
are added to focus one at a time), and all rules but one.

**Correction after review.** The first version of P3 accepted _any_ difference in truck or ferry
positions as soon as the map had several parts, so it did not verify effects there. An external reviewer
showed this by injecting a wrong DRIVE effect that went unnoticed. P3 is now exact as described above, and
the same loose test in `validate.py` was fixed. `util/mutate.py` injects that fault: it is caught in
every game where a DRIVE is generated (155 of 155 with one part, 53 of 53 with several parts).

The review also exposed a coverage gap: the random profiles almost never produced a map with several
parts, so R10 was tested on very few games. Profile D (two or three independent maps side by side, some
with trucks and no packages) was added for it.

Results with the exact P3, fresh seeds, each game in all 26 configurations, **0 failures** of P1, P2, P3:

| profile                                   | solvable games |
| ----------------------------------------- | -------------- |
| S small                                   | 231            |
| M medium                                  | 61             |
| H many ferries                            | 68             |
| X inputs outside the assignment's wording | 183            |
| D several parts                           | 191            |

`validate.py` with the exact effect test (all rules on, plus `h <= h*` on every state): S 330, X 295,
D 224 solvable games, 0 failures.

The earlier campaign (1,440 games, 26 configurations, 0 failures) was run with the loose P3. Its P1 and
P2 results stand. Its P3 results count only for maps with one part.

A failure of P1 in the configuration "all rules" would be a real counterexample to Theorem P. A failure
in a partial configuration would show a rule that is only correct in combination with others. Neither
occurred, so no rule was weakened or removed.

## 9. What this proof does and does not establish

- Proved: Theorem P for the rules in sections 1, 10 and 11.
- By inspection plus tests: that `_successors` implements exactly these rules (P3 and the reading in
  section 1), and that `_canon` equality is the renaming equivalence of Lemma 5.
- The proof was written by an LLM. The steps most worth a second reading: stage 2 (the map ρ and the
  ferry that starts at a dead port), stage 4, and the R2 case of Lemma 6.
- Not covered at all: running time.

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

If the original plan traverses corridor edge j a total of N_j times, the transformed plan uses L\*N_j
DRIVEs there. The average of these costs over the L thresholds is `sum_j N_j`, exactly the original
corridor driving cost. Some threshold therefore does not increase cost. Apply this independently to
all corridors. A cycle attached at only one anchor can be collapsed to that anchor; a component with
no anchor contains no initial truck or package and need not be visited.

Now apply the previous normalizations. None of them creates a transfer at a corridor interior:

- Stage 2 moves the LOADs and UNLOADs of a dead side D to ρ(D), and those of a dominated island to its
  substitute port `z`. A port is an anchor. The remaining case is a road bridge `(x, y)` with `y` in D,
  where ρ(D) = `x` lies in the core. If `x` is marked or a port, it is an anchor. Otherwise look at the
  2-edge-connected part of `x`. If it has another node, `x` has at least two edges inside it, and they
  are roads because `x` is not a port. If it is `x` alone, then `x` is an unmarked node of the core, so it
  lies between two marked sides and has at least two bridges into the core, again roads. In both cases
  the road to `y` is a third one, so `x` has degree at least three and is an anchor.
- Stage 3 inserts UNLOADs only at goals, which are anchors.
- Stages 4 and 5, and the moves of sections 10.2 and 10.3, reorder actions without changing where any
  LOAD or UNLOAD happens.

Thus at least one minimum-cost plan survives the combined rules.
This is a proof about total driving cost, and does not require equal truck capacities.

### 10.2 Eager goal unloading

Call a truck _pending_ if it is standing, belongs to the active part, and holds a package whose goal is
its location. **The rule as the code implements it:** in a state with no focus, if some truck is pending,
the only successor is the UNLOAD of the lowest-numbered goal-bound package of the lowest-numbered pending
truck. Within a truck focus the forced-unload rule R2 applies as before. No additional history is needed.

_An optimal plan in this form exists._ After stage 3, the next action of a pending truck `t` is an UNLOAD
of a goal-bound package (property F). Such an UNLOAD commutes to the left past every action of another
object: no precondition reads what `t` holds, the package is not touched by anyone else, and a package
lying at its goal is invisible to every rule. So move it to directly after the action that made `t`
pending: its arrival (a DRIVE or a DISEMBARK), or its previous goal UNLOAD at the same stop. Do this
before stage 5. Stage 5 only moves DRIVEs and LOADs to the right, to just before a later action of the
same truck, so it never puts an action between an arrival and the UNLOAD that directly follows it.
In the resulting plan a truck becomes pending only by its own arrival and is no longer pending before any
other object acts. Hence at most one truck is pending at a time, and in every state of the plan with a
pending truck the next action is one of its goal UNLOADs. That is the relaxed form of the rule.

_The lowest-number choices lose nothing (extension of Lemma 6)._ Let G2 use the relaxed rule: with no
focus and some pending truck, the successors are the UNLOADs of goal-bound packages by pending trucks,
any of them. Take a cheapest G2 path whose next edge unloads `q` from `t'` where the code demands `p` from
`t`. Until no truck is pending, every edge of the path is such an UNLOAD, so `UNLOAD(p, t)` occurs later
with only goal UNLOADs in between. Exchange the two. The states in between differ only in which goal-bound
packages are already delivered. All of them belong to the active part, so the number of undelivered
packages of that part, and with it the moment the part is finished, is the same in both orders, and no
other rule reads a package lying at its goal. So the exchanged sequence is a G2 path of the same cost
that reaches the same state. This is the R2 case of Lemma 6 with two trucks in place of one, and the
relaxed rule is stated through positions and classes only, so Lemma 5 applies to it unchanged.

### 10.3 Empty sails immediately before boarding (`OPT_LAZYSAIL`)

Take an empty ferry's movements before its next BOARD. There can be no DISEMBARK in this interval.
Consecutive empty repositionings can be replaced by one sail from the ferry's current port directly to
that BOARD's port (or no sail if already there): a ferry can sail directly to every served destination.
If there is no later BOARD, delete those movements. Move the remaining empty sail immediately before
the BOARD. Intervening actions involve neither the empty ferry nor a truck aboard it, so delaying the
sail does not invalidate them. Its destination now has a standing truck ready to board.

**The rule as the code implements it.** Loaded-ferry sailing is unchanged. For an empty ferry `f`:

1. With no focus, `f` may sail to a port `b` only if some truck is standing at `b`.
2. With a truck focus on `t` (it has just driven or loaded), `f` may also sail to the location of `t`.
3. After either sail the state carries the flag `FE0 + f`, and its only successors are BOARDs onto `f` by
   a truck standing at the port of `f`.

The normal form proved above uses a narrower set of edges than these: the sail goes to the truck that
boards next, and that truck boards. The code generates more. In case 3 _any_ truck standing at the port
may board, not only the one the sail was meant for. In case 2 the sail is offered even when `t` has a
forced goal UNLOAD pending, and the twin rule R3(e) is not applied to it. In case 3 the twin rule R3(d)
is not applied. Every generated BOARD is legal because the ferry is empty, has capacity at least one,
and the truck stands at its port. The no-focus sail branch also permits a zero-capacity empty ferry
to sail to a waiting truck. That SAIL is world-legal and its pending state has no successors. Such a
branch has no path to a goal and adds no completion. Thus Lemma 0 still holds. Adding edges to a graph
that already contains a plan of cost C\* cannot remove that plan, so Lemma 4 still holds. The extra edges
are stated through positions and classes only, so they are equivariant and Lemmas 5 and 6 are unaffected.

The pending-ferry flag is part of `_canon`, including under ferry renaming, so a state with a pending
BOARD is never merged with a state without one. The heuristic ignores the flag.

There is an essential interaction with truck focus. A truck may have just driven to the port or loaded
there before the ferry arrives. The focused branch therefore allows the empty sail to that truck's
port, followed by the pending BOARD. For the focus proof, treat the consecutive empty-SAIL/BOARD pair
as the boarding truck's next operation. Other trucks' DRIVE/LOAD actions commute with it exactly as
with the original BOARD. This avoids requiring an anticipatory empty sail that this rule removes.

For barren-road pruning, a road-bridge side containing a served destination port also contains that
ferry's graph node and every port it can currently occupy; otherwise another edge would cross the same
bridge cut. Its docked port therefore marks that side useful already. Delaying the empty sail does not
prevent an empty truck from approaching a needed boarding port across a road bridge.

Together, the corridor mapping, eager deliveries, and delayed empty-sail/BOARD pairs can be applied
before the existing focus/no-op/twin/component normalizations. They preserve at least one optimal plan.

## 11. Legal loads with fractional or signed cargo

For nonnegative integer package weights, any integer load fits a truck of capacity C exactly when
it fits floor(C). Sections 1–10 apply directly. For every other weight list, `_successors` visits
packages in the original dictionary order when building each truck's cargo list. The LOAD comparison
computes `sum(held_weights) + new_weight <= original_capacity` using that same order and the same
Python operations as `World.load_of` and `World.load`. This matters at a floating-point boundary.
The integer surrogate loads from [H] do not participate in this test.

For this second case, take a cheapest real plan. Stage 1 reorders regions and can stop each region
as soon as all its packages are delivered, since other regions cannot use its objects. The corridor
and dead-side projections preserve the order and identity of every package handled by each truck.
Thus each projected LOAD sees the same held-package set and gives the same numerical test. The lazy
empty-sail transformation also preserves all holdings. Apply stage 5 to the resulting plan. Moving
a truck's DRIVE or LOAD past another object's independent action preserves its own sequence and
holdings, including at an empty-SAIL/BOARD pair. These transformations retain a plan of cost C*.

The code allows picking up a package lying at its goal, leaves goal unloading optional and permits an
UNLOAD directly after a LOAD (R1, R2, R4 and global eager unloading are disabled). No argument about
freeing weight or reordering loads at a stop is required. For R8 all lying packages, including
delivered ones, mark their side useful. The original first-LOAD-or-BOARD argument therefore also
covers fetching a signed package for its effect on capacity. The remaining movement rules follow
from the same cheaper round-trip deletions, which preserve holdings at every retained LOAD.

Every package has its own class here. Permuting equal-capacity trucks or equal-class ferries preserves
the identities, and hence the fixed summation order, of all packages in each corresponding truck.
The symmetry and lowest-number arguments of sections 5–6 apply with singleton package classes.
With the integer projection proof of [H], Lemma 7 then gives the optimal cost for this case as well. ∎
