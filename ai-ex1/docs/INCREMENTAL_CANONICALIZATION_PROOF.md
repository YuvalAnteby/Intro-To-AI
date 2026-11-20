# Incremental canonicalization: equivalence and optimality preservation

This proves the implementation added to **ex1.py**. The argument covers all generated states and all six action types; it does not rely on test cases or observed search results.

**Main result.** Every computed incremental key equals the key returned by the unchanged original canonicalizer on the same raw state. The raw successors, their order, action costs, goal predicate, and heuristic calculations remain unchanged. Therefore this optimization preserves the existing solver's state equivalence and optimal solution costs.

This is an equivalence proof for this change. It does not introduce new symmetry reductions or pruning, and it does not strengthen the separate correctness claims about pruning already present in the baseline.

## 1. Definitions and scope

Fix one problem instance. Let n, T, F and P be the numbers of locations, trucks, ferries and packages. The raw state is the unchanged tuple

\[
s=(0,\ \text{truck positions},\ \text{ferry docks},\ \text{package positions}).
\]

For a truck t, write x_t=s[1+t]. It is standing at location x_t when x_t<n. Otherwise it is aboard ferry

\[
f=\left\lfloor\frac{x_t-n}{2}\right\rfloor.
\]

Both legacy code n+2f and current code n+2f+1 have that same ferry membership in the original canonicalizer.

For a ferry f, write d_f=s[IF+f]. For a package p, write q_p=s[IP+p]. It is lying at location q_p when q_p<n, and is carried by truck q_p-n otherwise.

Let \(\tau_t,\phi_f,\pi_p\) be the existing truck, ferry and package class tags, and let N be the existing value of npcls. The implementation does not change these tags or how they are computed.

For a finite multiset M, let \(\sigma(M)\) be its elements arranged in ascending order as a tuple, retaining multiplicities. In multiset expressions below, a sorted tuple denotes its underlying multiset. Define

\[
C_t(s)=\sigma\{\!\{\pi_p:q_p=n+t\}\!\}
\]

(the cargo-class tuple of truck t),

\[
L(s)=\sigma\{\!\{q_pN+\pi_p:q_p<n\}\!\}
\]

(the lying-package tuple),

\[
S(s)=\sigma\{\!\{(x_t,\tau_t,C_t(s)):x_t<n\}\!\}
\]

(the standing-truck tuple),

\[
A_f(s)=\sigma\{\!\{(\tau_t,C_t(s)):
x_t\ge n,\ \lfloor(x_t-n)/2\rfloor=f\}\!\}
\]

(the manifest of ferry f), and

\[
D_f(s)=(\phi_f,d_f,A_f(s)),\qquad
B(s)=\sigma\{\!\{D_f(s):0\le f<F\}\!\}.
\]

The original function \_canon computes exactly

\[
K(s)=(S(s),B(s),L(s))
\]

when OPT_SYM is enabled. It includes packages lying at their goals and empty ferries. The new code includes both as well.

The extra metadata is

\[
M(s)=((C*0(s),\ldots,C*{T-1}(s)),
(D*0(s),\ldots,D*{F-1}(s))).
\]

Unlike B(s), the second vector in M(s) is indexed by actual ferry identity. The first vector is indexed by actual truck identity. These vectors make it possible to update the object named by an action even if several objects have equal canonical descriptors.

The proof assumes the same well-formed state encodings and comparable class tags as the original code. Problem data and switches are fixed for a run, and private keys/metadata are produced by the supplied methods rather than overwritten by external code. All tuples used as keys or metadata are immutable. The proof does not require package weights to be integers or at least 1; it uses the class tags the baseline already selected.

## 2. Invariant

When OPT_SYM is enabled, every \_State wrapper produced by the implementation satisfies:

1. Its raw tuple s is exactly the corresponding baseline raw tuple.
2. Its cached key k is absent, or \(k=K(s)\).
3. Its metadata parts is absent, or \(parts=M(s)\).

An absent key is computed by the unchanged original \_canon before hashing or equality comparison. Before an incremental child is constructed, successor ensures that its parent has both a correct key and correct metadata.

When symmetry is disabled, the incremental path is bypassed, and the original raw-tuple key is used.

## 3. Sorted-multiset update lemma

The helper \_canon_edit takes a sorted tuple, optionally removes one specified element, and optionally inserts one element.

Suppose \(u=\sigma(U)\). If an old element a is supplied, assume it occurs in U. If a new element b is supplied, there is no additional precondition. Then the helper returns

\[
\sigma\bigl((U\mathbin{\setminus_1}\{a\})\uplus\{b\}\bigr),
\]

omitting the removal or addition when its argument is absent. Here \(\setminus_1\) removes exactly one occurrence.

**Proof.** The helper copies the input tuple into a new list. The binary search finds the leftmost occurrence of a; the explicit equality check verifies that it exists. Deleting it removes exactly one occurrence, and the remaining list stays sorted. Ordered insertion adds b at a position that preserves sorted order. Conversion to a tuple changes neither its elements nor their multiplicities. The original tuple is never mutated.

If several objects have equal descriptors, deleting any one equal occurrence gives the same multiset. Object identity therefore does not need to be encoded in the sorted canonical key. Identity is retained separately in M(s). All actual elements are integers or tuples, so None unambiguously means that an edit is absent. \(\square\)

## 4. Metadata initialization lemma

For every well-formed raw state s, \_canon_parts(s) returns M(s).

**Proof.** Its package loop puts \(\pi_p\) into cargo[q_p-n] exactly when p is carried. Sorting each bucket therefore produces C_t(s) for each actual truck t.

Its truck loop places \((\tau_t,C_t(s))\) into the manifest of \(\lfloor(x_t-n)/2\rfloor\) exactly when x_t is an aboard code. Sorting each manifest produces A_f(s). Combining it with the unchanged ferry class and actual dock produces D_f(s), at index f. Empty buckets become empty tuples. These are precisely the two vectors defining M(s). \(\square\)

## 5. Successor generation and action annotations

The two raw successor generators retain every original action condition, capacity calculation, state assignment, pruning decision, append order and return. Their only additions are an optional changes list and one append to it immediately after each append to the raw result list.

| Raw append site     | Annotation                                |
| ------------------- | ----------------------------------------- |
| Forced UNLOAD       | ("unload", t, p), or None if \_finish ran |
| Other UNLOAD        | ("unload", t, p), or None if \_finish ran |
| LOAD                | ("load", t, p)                            |
| DRIVE with cargo    | ("drive", t, None)                        |
| DRIVE without cargo | ("drive", t, None)                        |
| BOARD               | ("board", t, f)                           |
| DISEMBARK           | ("disembark", t, f)                       |
| SAIL                | ("sail", f, None)                         |

The annotation uses internal object indices, directly from the action-generating loops. It is not inferred by parsing the action label.

Starting with two empty lists, each raw append has exactly one accompanying annotation append before the next raw append or return. Thus, by induction on executed append sites, the lists have the same length and corresponding order. Early returns preserve that property. successor also checks the lengths before pairing the lists.

For the two UNLOAD sites, the condition recording None is exactly the condition that called \_finish. That function changes only the newly constructed raw list; it does not change the condition's problem fields. Re-evaluating the condition therefore gives the same result.

The annotations do not affect action selection or mutate the raw state. Erasing these annotations and their optional argument recovers the original two generator functions.

## 6. Preservation by each ordinary action

Assume the parent invariant, and let s' be a child whose annotation is not None. Consequently, \_finish did not run. The key starts as K(s), and the metadata starts as M(s). We show that the edits produce K(s') and M(s').

### 6.1 DRIVE(t, a, b)

The truck is standing. Only x_t changes from a to b, apart from the leading field that \_canon ignores. No package changes its owner or lying location, and no ferry changes its dock or manifest.

Hence

\[
S(s')=\sigma\bigl(S(s)\setminus_1
\{(a,\tau_t,C_t(s))\}\uplus
\{(b,\tau_t,C_t(s))\}\bigr).
\]

The other key components and all metadata are unchanged. The drive branch makes exactly this replacement. The removed descriptor occurs because t is standing at a.

### 6.2 LOAD(p, t)

The truck is standing at a, and p is lying there. The raw change is \(q_p:a\mapsto n+t\). Thus

\[
C_t(s')=\sigma(C_t(s)\uplus\{\pi_p\}),\qquad
L(s')=\sigma(L(s)\setminus_1\{aN+\pi_p\}).
\]

The standing descriptor of t changes from
\((a,\tau_t,C_t(s))\) to \((a,\tau_t,C_t(s'))\).
All other truck cargo tuples are unchanged.

Since t is standing, no ferry manifest contains its cargo descriptor. Consequently every D_f is unchanged. The load branch performs precisely these edits and replaces cargo[t] in the identity-indexed vector. The removed lying token exists because p was lying at a.

### 6.3 UNLOAD(p, t), without component completion

The truck is standing at a and carries p. The raw change is \(q_p:n+t\mapsto a\). Therefore

\[
C_t(s')=\sigma(C_t(s)\setminus_1\{\pi_p\}),\qquad
L(s')=\sigma(L(s)\uplus\{aN+\pi_p\}).
\]

The standing descriptor of t is updated to use the new cargo tuple. No ferry descriptor changes. The unload branch performs exactly these edits and updates cargo[t]. The removed cargo class exists because t carries p.

This includes unloading at p's goal: the original canonicalizer still includes the resulting lying token, even though the action generator may omit that package from its active-package lists.

### 6.4 BOARD(t, f)

The standing truck t at a becomes aboard ferry f. Its cargo ownership does not change. Its old standing descriptor is removed, and its aboard descriptor is inserted into f's manifest:

\[
S(s')=\sigma(S(s)\setminus_1\{(a,\tau_t,C_t(s))\}),
\]

\[
A_f(s')=\sigma(A_f(s)\uplus\{(\tau_t,C_t(s))\}).
\]

The dock d_f is unchanged. Therefore D_f changes only in its manifest. Replace one occurrence of the old D_f in B(s) with the new D_f, and update the metadata entry at the actual ferry index f.

The board branch does exactly this. Cargo metadata and lying packages remain unchanged. Both removed descriptors exist: t is standing, and B contains one descriptor for every ferry.

### 6.5 DISEMBARK(t, f)

Truck t is aboard f and becomes standing at f's dock a. Its cargo ownership does not change. Therefore

\[
A_f(s')=\sigma(A_f(s)\setminus_1\{(\tau_t,C_t(s))\}),
\]

\[
S(s')=\sigma(S(s)\uplus\{(a,\tau_t,C_t(s))\}).
\]

Replace D_f in B and in the indexed metadata vector using the updated manifest. No package token or cargo tuple changes. These are exactly the disembark branch's operations. The removed aboard descriptor exists because t is aboard f.

### 6.6 SAIL(f, a, b)

The ferry's dock changes from a to b. Package ownership, truck standing/aboard membership and all ferry manifests stay the same. Thus only

\[
D_f(s)=(\phi_f,a,A_f(s))
\]

changes, to

\[
D_f(s')=(\phi_f,b,A_f(s)).
\]

The sail branch replaces that descriptor in B and at metadata index f.

The unchanged \_sail function may also normalize a legacy truck code n+2f to n+2f+1. Both codes are aboard codes with the same value of \(\lfloor(x_t-n)/2\rfloor=f\). This normalization changes none of the canonical descriptors, so no additional edit is needed.

### Consequence of the six cases

In every case, every requested removal is of an element that exists. The sorted-multiset lemma therefore applies, and the missing-descriptor guard cannot fire for a correctly annotated well-formed successor. Every changed descriptor is updated and every unchanged descriptor can be reused.

The updated identity-indexed vectors refer to the actual t or f, regardless of duplicate entries in the sorted key. All edits copy their lists before changing them and then store immutable tuples. Consequently constructing one child cannot corrupt the parent's metadata or another child's metadata.

## 7. Component completion and disabled switches

A component-completing UNLOAD can call \_finish, which resets several trucks and ferries to their initial positions. A single unload edit would be insufficient for that raw successor.

The annotation is therefore None. successor creates an ordinary \_State with no cached key and no metadata. Its next hash or equality operation computes the key with the unchanged original \_canon on the actual post-reset raw state. If it is expanded, successor initializes any missing key and metadata from that state before constructing incremental children.

Thus the fallback is correct regardless of how many objects \_finish reset. It also avoids making any new assumption about the correctness of the existing component reduction.

If OPT_INCREMENTAL_CANON is False, successor uses the original wrapper construction. If OPT_SYM is False, it also uses that path and \_canon returns the raw tuple as before. Neither disabled case performs an incremental edit.

## 8. Inductive correctness theorem

**Theorem.** Every state produced from the original initial state by any finite sequence of calls to successor satisfies the invariant in Section 2. In particular, whenever its key is materialized,

\[
\boxed{K*{\mathrm{incremental}}(s)=K*{\mathrm{original}}(s).}
\]

**Proof.** The initial state is constructed without a cached key or metadata. Its raw tuple is unchanged, so the invariant holds initially.

Suppose it holds for a parent. The annotated generator produces the same ordered raw successors as the baseline, by Section 5. If there are no children, there is nothing to prove.

Before an incremental child is built, any missing parent key is computed by the original \_canon, and any missing metadata is computed correctly by Section 4. For an ordinary child, the applicable case of Section 6 establishes both the exact key and the exact metadata. For a reset child, Section 7 establishes the invariant with absent caches. The disabled-switch cases use the original path.

Lazy hashing and equality only fill an absent key with the original \_canon; they therefore preserve the invariant as well. Induction proves the result at every finite depth and after every such cache fill. \(\square\)

## 9. State equality, heuristic and optimality

The implementations of **hash** and **eq** are unchanged. By Section 8, every key they inspect is exactly the original key. Therefore, for any two produced states s and t,

\[
s=_{\mathrm{new}}t
\iff K(s)=K(t)
\iff s=_{\mathrm{old}}t.
\]

Hashes also have the same values within the same Python hashing environment. Ordinary hash collisions remain harmless because equality is unchanged. The new metadata is not part of either hash or equality.

The following behavior is also unchanged:

- Every raw state has exactly the same ordered action/raw-successor list.
- Action labels are identical.
- path_cost adds 3 for SAIL and 1 for every other action, as before.
- goal_test reads the same raw package positions.
- All heuristic functions, precomputation and cache logic are unchanged and read the same raw state data. The new key/metadata helpers do not access or modify heuristic caches.

Consequently every raw goal-reaching action sequence in the baseline is available with exactly the same total cost in the updated code, and conversely. The state identifications used for duplicate detection are also identical. If G is the baseline's retained search graph and G' the updated graph, this correspondence preserves goals and edge costs, so

\[
\boxed{\operatorname{OptCost}(G')=\operatorname{OptCost}(G).}
\]

This is true also when no solution exists, taking both optimal costs to be infinity. The corresponding graph after the existing canonical state identifications is unchanged as well.

For an unchanged search algorithm using the problem's state equality, hash, successors, costs, goals and heuristic interface, this change introduces no new reason to discard a cheaper solution. Given the same sequence of heuristic calls, the same heuristic values and cache updates result. The existing admissibility argument therefore remains applicable; no consistency assumption is added by this optimization.

Precisely: **if the baseline search and its existing reductions return an optimal solution, incremental canonicalization preserves that guarantee.** The proof establishes equivalence of this optimization, rather than independently proving every old pruning rule or the external search implementation.

## 10. Expected work reduction and its limits

The original canonicalizer scans all packages and trucks and sorts all key components for each new key. The incremental path reuses unchanged components:

| Action               | Key components edited                            | Indexed metadata copied |
| -------------------- | ------------------------------------------------ | ----------------------- |
| DRIVE                | Standing trucks                                  | None                    |
| LOAD / UNLOAD        | One cargo tuple, standing trucks, lying packages | Truck-cargo vector      |
| BOARD / DISEMBARK    | Standing trucks, one ferry manifest, ferries     | Ferry vector            |
| SAIL                 | Ferries                                          | Ferry vector            |
| Component completion | Original full computation                        | Rebuilt if expanded     |

This does **not** make every update constant time. Sorted tuple edits copy a list and a tuple, insertion/deletion can shift elements, and comparisons of nested descriptors may inspect cargo tuples. LOAD/UNLOAD can still copy a lying-package tuple proportional to P. Raw-state copying and hashing of nested canonical tuples remain unchanged.

The extra indexed vectors consume memory, although unchanged cargo tuples, manifests and key components are shared. Incremental keys are constructed during successor generation; the original code could defer a key for a child that was never hashed or compared. Initial and reset-state metadata also has an initialization cost.

Thus this is a plausible performance improvement, particularly when many siblings share most of a large state. It is not a proof of a speedup or of being the fastest available optimization.

## 11. Code audit and runtime comparison

The following static checks were performed:

- Python syntax compilation, without executing the module or a solver.
- All 44 original function bodies outside the four modified functions are source-identical, including every heuristic method, \_canon, **hash**, **eq**, \_finish, \_sail, goal_test and path_cost.
- Removing only metadata appends and their optional argument makes the two modified raw successor generators identical to the baseline at the abstract syntax tree level.
- Each of the eight raw-result append sites has exactly one immediately following annotation append.
- Original module-level executable statements are retained; the additions are the standard-library bisect import and the new switch.

These checks support the code-to-proof correspondence. They are not the proof by themselves. No problem-instance tests, solver runs or timing benchmarks were used to establish correctness.

The updated file defaults to:

```python
OPT_INCREMENTAL_CANON = True
```

To compare canonicalization strategies, set it to False before creating the problem, then run the same checker command, inputs and time limit in a fresh process. False selects the original canonicalizer for child keys. The wrapper's extra metadata field and inactive annotation checks remain, so this switch compares the two strategies within the updated file; the untouched original file is the exact baseline for a whole-file timing comparison.

SHA-256 of the untouched baseline file:

```text
551aefbdf1481f4b3bdc09252dd0f4587dcf1e9ddffd47f1c925c9141255b865
```

SHA-256 of the updated file:

```text
068ed471c7eed92272d82707355d615a8d857fe0cdca10a09ac6fa446572db90
```
