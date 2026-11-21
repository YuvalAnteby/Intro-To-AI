# State-hash caching, occupancy reuse and incremental canonicalization: combined correctness proof

This proves the three optimizations in **ex1 (3).py**, individually and together: lazy state-hash caching, occupancy reuse and optional incremental canonicalization. It covers every generated state, all six action types, and all eight combinations of the optimization switches. It does not rely on test cases or observed search results. The current defaults enable occupancy reuse and hash caching, with incremental canonicalization disabled.

**Main result.** Reused occupancy equals the original scan, incremental keys equal the original canonicalizer, and cached state hashes equal the original hash results. All three optimizations preserve the ordered raw successors and full-key equality relation. Action costs, goals and heuristic calculations remain unchanged, so the baseline's optimal solution costs are preserved.

This is an equivalence proof relative to the original code before these optimizations. They introduce no new symmetry reductions or pruning. The proof does not strengthen separate correctness claims about pruning already present in that baseline.

## 1. Definitions and scope

**Scope in later versions.** This proof assumes that the leading field of every state is 0 and that aboard codes
carry no freshness bit, as in ex1 (3).py. In the condition-(1) file, `successor` bypasses incremental key
generation whenever the history rules or H3 are on, which is the default. So this proof applies to that file only
with both off, and in the strict file it applies as written. In both files `OPT_INCREMENTAL_CANON` is off by
default anyway, so the delivered solvers never run that code.

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
4. Its cached hash kh is absent, or its key is present and kh equals hash(k), as formalized in Section 7.2.

An absent key is computed by the unchanged original \_canon before hashing or equality comparison. Before an incremental child is constructed, successor ensures that its parent has both a correct key and correct metadata.

There is also an expansion-local invariant: after the existing count-building loop and throughout child generation, aboard_count[f] equals the actual occupancy O_f(s) of the parent state, as defined in Section 5.1. This vector is not stored in a child. Whenever metadata is present, its ferry manifest has the same number of entries, counting duplicates.

When symmetry is disabled, the incremental path is bypassed, and the original raw-tuple key is used. Occupancy reuse remains valid independently of symmetry.

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

## 5. Occupancy reuse, successor generation and annotations

There are two implementations of the BOARD occupancy calculation:

- **Scan:** for each candidate ferry, scan every truck and count its two possible aboard codes.
- **Reuse:** read that ferry's entry from the count vector already constructed once by \_successors.

The switch OPT_OCCUPANCY_REUSE selects which value is passed to \_truck_standing. Both calls from \_successors pass the same vector for the same parent state, or None when the switch is disabled. A direct call without the optional vector retains the scan.

### 5.1 Definition and membership identity

For a well-formed raw state s, define the occupancy of ferry f by

\[
O*f(s)=\sum*{t=0}^{T-1}
\mathbf{1}\{x_t=n+2f\ \lor\ x_t=n+2f+1\}.
\]

Each truck contributes at most one unit. Occupancy counts trucks, including empty trucks; it does not sum package weights or count distinct truck classes.

For every integer truck code x and valid ferry index f,

\[
x=n+2f\ \lor\ x=n+2f+1
\quad\Longleftrightarrow\quad
x\ge n\ \land\
\left\lfloor\frac{x-n}{2}\right\rfloor=f.
\tag{1}
\]

**Proof.** The forward direction follows by substituting either code. For the reverse direction, let y=x-n be a nonnegative integer. The floor condition says \(2f\le y<2f+2\). Its only integer possibilities are y=2f and y=2f+1. A standing code x<n satisfies neither side. \(\square\)

### 5.2 Correctness of the once-per-expansion count

The existing loop initializes aboard_count to F zeros and visits every truck slot. For each code x_t at least n, it increments the entry \((x_t-n)\mathbin{>>}1\).

After processing r trucks, the loop invariant is

\[
aboard_count[f]=
\sum\_{t=0}^{r-1}
\mathbf{1}\{x_t\ge n\ \land\
\lfloor(x_t-n)/2\rfloor=f\}
\quad\text{for every }f.
\]

It holds initially because the sum is empty and every entry is zero. A standing truck changes no entry. An aboard truck adds one to exactly its own ferry's entry, extending the corresponding sums by the correct indicators. Thus it holds after r+1 trucks.

At termination r=T. For nonnegative integers, shifting right one bit equals division by 2 rounded down. Equation (1) therefore gives

\[
\boxed{aboard_count[f]=O_f(s)\quad\text{for every }f.}
\tag{2}
\]

This loop includes all trucks, exactly as the old scan does. It does not filter out inactive components, duplicate truck classes or empty trucks. Both aboard encodings are counted.

### 5.3 The vector cannot become stale during generation

The parent raw state s is an immutable tuple. Each successor is constructed as a separate list and then converted to a tuple. \_finish modifies only a successor list; \_sail likewise starts with its own list copy.

After the count-building loop, no code in this expansion changes aboard_count or its alias board_occupancy. The count vector is a local variable. It is neither stored in a \_State nor attached to the problem object, and it is not passed into incremental key construction. A BOARD or DISEMBARK child is an alternative outcome from the same parent; generating it does not update the parent's count vector.

Consequently Equation (2) remains true at every BOARD check in this expansion. On expansion of a child, \_successors computes a fresh vector from that child's actual raw tuple, including any component-reset positions.

When a forced UNLOAD returns early, or a dead/goal state has no children, no later BOARD check needs the vector. With F=0, no ferry entry is accessed.

### 5.4 Equivalence of every BOARD decision

For a fixed candidate ferry f, the old loop computes cnt by adding one for precisely the terms in O_f(s). The new branch assigns cnt=aboard_count[f]. By Equation (2), these integers are equal.

The two uses of cnt are unchanged:

1. The capacity condition remains exactly cnt < self.fcap[f].
2. The empty-ferry symmetry condition remains exactly cnt == 0 and OPT_TWINS.

Thus every capacity decision and every decision to enter empty-ferry symmetry handling is identical. No rounding or replacement of ferry capacity is performed. This remains true for any capacity supported by the baseline comparison, and does not depend on package-weight integrality.

For the symmetry loop, consider ferries in their unchanged iteration order. Its seen set is initially the same. Assuming it is the same before a candidate, the unchanged docking/dead-ferry checks and the equal cnt give the same branch decisions. If the set is consulted or updated, the unchanged ferry-class key is the same. Therefore the set remains the same, and exactly the same BOARD child and annotation are appended or skipped. Induction over the ferry loop proves equality of its entire ordered output.

The scan's other local variables, c and t2, are only used inside that scan. Replacing it with the equal cnt does not affect a later calculation.

### 5.5 Equivalence of the complete raw successor list

LOAD, UNLOAD, DRIVE, DISEMBARK, SAIL and component-reset construction are unchanged. Section 5.4 proves equivalence of BOARD output, including symmetry decisions and its order.

The outer truck loop, forced-unload selection, component selection, package-load sums and their summation order, and ferry loop are also unchanged. The ferry loop continues to use the same already-existing aboard_count vector for its empty-ferry decisions.

Hence, for every well-formed parent s,

\[
\boxed{R*{\mathrm{reuse}}(s)=R*{\mathrm{scan}}(s),}
\tag{3}
\]

where R is the **ordered list of action labels and raw successor tuples**, not merely a set. If an annotation list is requested, it receives exactly the same ordered entries in both modes. Problem fields written during generation, such as \_rank, \_last and \_useful, also receive the same values.

If the reuse flag is disabled, the optional argument is None and the retained original scan is used. Both branches have therefore been covered. The optional argument's internal contract is that a non-None vector equals O(st); every caller in this implementation satisfies that contract.

### 5.6 Compatibility with canonical metadata

From the definition of the manifest A_f(s), it contains one descriptor per actual truck aboard f. Sorting retains duplicate descriptors. Therefore

\[
O_f(s)=|A_f(s)|.
\]

If parent.parts is present and satisfies the metadata invariant, this also gives

\[
\boxed{aboard_count[f]
=\operatorname{len}(parent.parts[1][f][2]).}
\tag{4}
\]

The ferry index f here refers to the identity-indexed metadata vector, not position f in the sorted canonical ferry tuple. This distinction matters for interchangeable ferries.

Equation (4) proves that occupancy and incremental metadata describe the same physical membership. The code computes occupancy from the raw state, so it does not depend on metadata being available.

The mathematical effects on occupancy agree with the key updates in Section 6:

| Action                    | Occupancy in the child, before any component reset |
| ------------------------- | -------------------------------------------------- |
| LOAD, UNLOAD, DRIVE, SAIL | Unchanged                                          |
| BOARD(t, f)               | \(O_f+1\); all other entries unchanged             |
| DISEMBARK(t, f)           | \(O_f-1\); all other entries unchanged             |
| Component completion      | Defined by the actual post-reset raw state         |

These are properties of child states, not instructions to mutate the parent's vector. Fresh counting when the child is expanded establishes the correct values in every row.

### 5.7 Canonicalization annotations

The generators retain their original action conditions, capacity comparisons, state assignments, pruning decisions, append order and returns. Occupancy reuse changes only how the same integer cnt is obtained, as proved above. Incremental canonicalization adds an optional changes list and one append to it immediately after each append to the raw result list.

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

The annotation uses internal object indices directly from the action-generating loops, rather than parsing the action label.

Starting with two empty lists, each raw append has exactly one accompanying annotation append before the next raw append or return. Induction on executed append sites proves that the lists have the same length and corresponding order. Early returns preserve that property. successor also checks the lengths before pairing the lists.

For the two UNLOAD sites, the condition recording None is exactly the condition that called \_finish. That function changes only the newly constructed raw list, not the condition's problem fields. Re-evaluating the condition therefore gives the same result.

Neither occupancy reuse nor annotation bookkeeping mutates the parent state or adds a pruning decision. Replacing the occupancy lookup by its equal retained scan, then erasing annotations and their optional arguments, recovers the original two generator functions.

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

## 7. Component completion, lazy hash caching and disabled switches

A component-completing UNLOAD can call \_finish, which resets several trucks and ferries to their initial positions. A single unload edit would be insufficient for that raw successor.

The annotation is therefore None. successor creates an ordinary \_State with no cached key, no metadata and kh=None. Its next hash or equality operation computes the key with the unchanged original \_canon on the actual post-reset raw state. If it is expanded, successor initializes any missing key and metadata from that state before constructing incremental children.

Thus the fallback is correct regardless of how many objects \_finish reset. It also avoids making any new assumption about the correctness of the existing component reduction.

If OPT_INCREMENTAL_CANON is False, successor uses the original wrapper construction. If OPT_SYM is False, it also uses that path and \_canon returns the raw tuple as before. Neither disabled case performs an incremental edit.

### 7.1 The key is stable for the lifetime of a state

Let

\[
\kappa(s)=
\begin{cases}
K(s),&\text{if symmetry is enabled},\\
s,&\text{otherwise},
\end{cases}
\qquad
\Phi(s)=\operatorname{hash}(\kappa(s)).
\]

Here hash is Python's ordinary built-in hash operation in the current interpreter. It is not a new digest or an approximation.

For this implementation, raw states are tuples of integer positions/codes. Canonical keys contain only tuples and integer class tags/positions. Truck classes are integer capacities when integer_cargo is true, and integer truck indices otherwise. Ferry/package classes are integer indices. Thus the entire key is composed of immutable values.

After construction, no method changes a wrapper's raw tuple. A missing k can be filled by \_canon; an incremental child can receive its already-correct key at construction. Subsequent methods do not replace a present key or mutate its contents. Filling parts does not alter the key. Problem data and switches are fixed during a run, as assumed in Section 1.

Therefore the key's value and its hash remain fixed for the lifetime of a state. This uses Python's hash contract for immutable hashable values, documented in the [data model](https://docs.python.org/3/reference/datamodel.html#object.__hash__) and [glossary](https://docs.python.org/3/glossary.html#term-hashable).

### 7.2 The hash-cache invariant

The extra field kh satisfies

\[
kh=\mathrm{None}
\quad\text{or}\quad
\bigl(k\ne\mathrm{None}\ \land\ k=\kappa(s)\ \land\ kh=\Phi(s)\bigr).
\tag{H}
\]

Every \_State constructor sets kh to None, including constructors given a correct incremental key. It does not hash the key during construction, so states never hashed incur no hash-computation work. It does not inherit a parent's cached integer.

The only other assignment to kh occurs in **hash**, immediately after value=hash(self.k). No action generator, occupancy calculation, heuristic method, equality comparison or component-reset operation writes kh.

### 7.3 Exactness of every hash call

Assume the key invariant and (H) at entry to **hash**. If k is missing, the unchanged initialization first sets it to \_canon(s), hence to \(\kappa(s)\).

There are three branches:

1. **Hash caching disabled.** The method returns hash(self.k), exactly as before. It does not use kh.
2. **Hash caching enabled, kh absent.** The method computes \(value=\operatorname{hash}(k)=\Phi(s)\), stores that exact integer in kh, then returns it. This establishes (H).
3. **Hash caching enabled, kh present.** By (H), kh already equals \(\Phi(s)\). By Section 7.1, the key and its hash have not changed. The method returns that same integer without recomputing hash(k).

Thus, for every call,

\[
\boxed{hash*{\mathrm{cached}}(s)=hash*{\mathrm{original}}(s)=\Phi(s).}
\tag{6}
\]

The method tests value is None, not the truth value of value. Every integer hash, including zero and negative values, is consequently a valid cached result. It stores the already-normalized result of Python's built-in hash rather than implementing hash arithmetic itself.

An equality call before the first hash may materialize k, leaving kh absent; the next hash then uses branch 2. An equality call after hashing leaves the present key unchanged. Filling incremental metadata likewise cannot invalidate kh. These operations all preserve (H).

### 7.4 Hash collisions do not merge states

The **eq** implementation remains unchanged and compares full keys. The cached integer is not used as a substitute for a key.

For any two produced states s and t,

\[
s=t\iff\kappa(s)=\kappa(t).
\]

Equal keys have equal hashes by Python's hash contract. The reverse implication is neither assumed nor used: distinct keys may collide, and they are still distinguished by the original full-key equality comparison.

Consequently hash-based dictionary/set lookup has the same hash values and equality decisions as before. The proof does not require a collision-free hash function.

### 7.5 Compatibility with occupancy and incremental canonicalization

Occupancy reuse reads the raw state and an expansion-local count vector. It never reads or writes kh. Hash caching reads the canonical key and kh. It never reads or writes occupancy. Neither method changes raw state data.

Incremental canonicalization produces the same key \(\kappa(s)\) proved in Section 6. Giving that key to a new wrapper still initializes its kh to None; the first hash therefore computes the child's exact hash.

A component-reset child likewise starts with absent key, metadata and hash cache. It obtains its key and occupancy from its actual post-reset raw tuple. A parent's cached hash is never carried into a modified child.

Thus all interfaces between the optimizations preserve their invariants, including when incremental canonicalization is disabled, as in the current default configuration.

## 8. Joint inductive correctness theorem

**Theorem.** Fix a problem instance and all existing pruning/symmetry switches. For any fixed combination of the three optimization switches, every finite sequence of state generation, equality and hashing operations satisfies:

1. Each expansion returns exactly the original ordered list of actions and raw child tuples.
2. A materialized key equals \(\kappa(s)\).
3. Incremental metadata, when present, equals M(s).
4. During child generation after the count-building loop, the local occupancy vector equals O(s) for the current parent.
5. The hash-cache invariant (H) holds, and every hash call returns \(\Phi(s)\).

In particular, with occupancy reuse and hash caching enabled and incremental canonicalization disabled,

\[
\boxed{
R*{\mathrm{new}}(s)=R*{\mathrm{original}}(s),\quad
\kappa*{\mathrm{new}}(s)=\kappa*{\mathrm{original}}(s),\quad
hash*{\mathrm{new}}(s)=hash*{\mathrm{original}}(s).
}
\tag{7}
\]

The same result holds for all eight combinations of the three optimization switches. With symmetry disabled, \(\kappa(s)\) is the original raw-tuple key.

**Proof.** The initial raw tuple is unchanged. The initial wrapper has no cached key, metadata or hash. All stored-state invariants therefore hold initially.

Suppose they hold before an expansion. If counting is reached, Section 5.2 establishes the occupancy invariant directly from the parent raw tuple. Section 5.3 preserves it throughout the expansion. Sections 5.4–5.5 then give the same ordered raw children and annotations as without occupancy reuse. If generation returns earlier with no children, equality of the output holds immediately.

When incremental canonicalization is enabled, successor obtains any missing parent key from \_canon and any missing metadata from the correct \_canon_parts. The action cases in Section 6 establish the correct child keys and metadata. Component completion uses the fallback in Section 7. When incremental canonicalization is disabled, the children use the original lazy key construction. In all cases, every new child initializes kh to None, establishing (H) for that child.

The occupancy vector is not stored in children. When a child is later expanded, its count invariant is established afresh from its own raw tuple.

If the next operation is equality, the unchanged method fills missing keys with \_canon and compares the exact keys. It does not change a present key or any cached hash. If the next operation is hashing, Section 7.3 proves that it returns \(\Phi(s)\) and preserves (H), whether caching is enabled or disabled. Filling metadata does not change any key or hash.

Induction over the operation sequence proves all five claims. The disabled occupancy branch is the retained scan; the disabled incremental branch is the original lazy key path; the disabled hash-cache branch returns hash(k) directly. Hence the reasoning covers every switch combination, rather than assuming that the optimizations cannot interact. \(\square\)

## 9. State equality, heuristic and optimality

The implementation of **eq** is unchanged, and Section 7.3 proves that **hash** returns the same integer as before. By Section 8, every key they inspect is exactly the original key. Therefore, for any two produced states s and t,

\[
s=_{\mathrm{new}}t
\iff \kappa(s)=\kappa(t)
\iff s=_{\mathrm{old}}t.
\]

Hashes also have the same values within the same Python hashing environment. Ordinary hash collisions remain harmless because equality is unchanged. The metadata is not part of the key or equality. The cached hash is not used for equality either: colliding keys are still compared in full. The occupancy vector is not part of a stored state at all.

The following behavior is also unchanged:

- Every raw state has exactly the same ordered action/raw-successor list.
- Action labels are identical.
- path_cost adds 3 for SAIL and 1 for every other action, as before.
- goal_test reads the same raw package positions.
- All heuristic functions, precomputation and cache logic are unchanged and read the same raw state data. Neither occupancy reuse, the key/metadata helpers nor the state-hash cache accesses or modifies heuristic caches.

Consequently every raw goal-reaching action sequence in the baseline is available with exactly the same total cost in the updated code, and conversely. The state identifications used for duplicate detection are also identical. If G is the baseline's retained search graph and G' the updated graph, this correspondence preserves goals and edge costs, so

\[
\boxed{\operatorname{OptCost}(G')=\operatorname{OptCost}(G).}
\]

This is true also when no solution exists, taking both optimal costs to be infinity. The corresponding graph after the existing canonical state identifications is unchanged as well.

For an unchanged search algorithm using the problem's state equality, hash, successors, costs, goals and heuristic interface, this change introduces no new reason to discard a cheaper solution. Given the same sequence of heuristic calls, the same heuristic values and cache updates result. The existing admissibility argument therefore remains applicable; no consistency assumption is added by this optimization.

Precisely: **if the baseline search and its existing reductions return an optimal solution, state-hash caching, occupancy reuse and incremental canonicalization, separately or together, preserve that guarantee.** The joint proof establishes equivalence of these optimizations, rather than independently proving every old pruning rule or the external search implementation.

## 10. Expected work reduction and its limits

### 10.1 Lazy state-hash caching

The previous \_State already cached its canonical tuple k, but called hash(k) on every request for the wrapper's hash. The new field caches the resulting integer only when a hash is first requested. It does not eagerly build or hash a key when a child is generated.

Suppose a particular state's hash is requested m times, with m at least 1, and the underlying runtime does not already cache the tuple hash. Let C(s) be the cost of hashing its key. Ignoring the common initial key-construction cost, the hash work changes from approximately

\[
m\,C(s)
\quad\text{to}\quad
C(s)+O(m).
\]

With fixed-size integer operations, hashing the nested key can inspect a number of entries proportional to T+F+P. Each later wrapper-cache hit takes a fixed number of attribute reads and branches, independent of key size.

This is a reduction in repeated hash work, not a measured speedup of the whole search. A state hashed only once gains no avoided hash computation. The extra attribute and branch overhead remain, and each wrapper has one extra slot plus a cached integer after its first hash.

**Runtime version matters.** CPython 3.14 added a cached hash to tuple objects themselves, as recorded under gh-131525 in the [official changelog](https://docs.python.org/3.14/whatsnew/changelog.html). On that runtime, repeated hash(k) is already cheap, so this additional wrapper cache may be redundant or slower. The older behavior and the implementation change are discussed in [CPython issue 131525](https://github.com/python/cpython/issues/131525). No speedup is asserted without measuring the user's actual runtime.

### 10.2 Occupancy reuse

Let Q(s) be the number of candidate truck/ferry pairs that reach the occupancy calculation during this expansion, after the unchanged docking/dead-ferry checks. Since there are at most T trucks and F ferries, \(Q(s)\le TF\).

The existing once-per-expansion pass already costs O(T+F), including initialization, in both modes. The old BOARD calculations additionally inspect exactly \(TQ(s)\) truck slots. Reuse replaces those scans with \(Q(s)\) indexed reads.

Under the usual constant-time integer/indexing model, this changes the occupancy-related work from

\[
O(T+F+TQ(s))
\quad\text{to}\quad
O(T+F+Q(s)).
\]

For this part alone, the worst-case upper bounds become \(O(T+F+T^2F)\) versus \(O(T+F+TF)\). This does not claim those worst cases arise on every instance, or that the whole successor function has those bounds: raw-state copying and other work remain.

The count vector already existed for empty-ferry symmetry handling. Reusing it adds only local references and an optional argument; it adds no persistent per-state occupancy data. Actual elapsed-time savings depend on how many BOARD candidates reach this calculation. Instances with few such candidates may show little benefit.

### 10.3 Incremental canonicalization

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

For the hash-cache change, the following static checks passed:

- Python syntax compilation, without executing the module or running a solver.
- Relative to the preceding occupancy-plus-incremental version, exactly two function bodies changed: \_State.**init** and \_State.**hash**. The other 49 are source-identical.
- The entire LogisticsProblem, \_Region and \_Memo classes are source-identical to that version. This includes every heuristic, occupancy calculation, action generator, canonicalization helper, goal check, action cost and component-reset method.
- The constructor adds only kh=None, and \_State gains one slot named kh. No hash is computed at construction.
- The cache-disabled branch retains the original key initialization and hash(k) return expression.
- The cache-enabled branch stores and returns exactly hash(k), with None as the only missing-value sentinel.
- Writes to kh occur only at construction and after that exact hash computation.
- The module-level configuration changes are OPT_INCREMENTAL_CANON=False and the new OPT_HASH_CACHE=True; occupancy reuse remains enabled.

The earlier static checks for occupancy reuse and incremental canonicalization remain applicable to their unchanged methods. Their mathematical proofs are included above.

These checks establish correspondence between the edit and the proof's code paths. They do not replace the universal mathematical argument. No problem-instance tests, solver runs or timing benchmarks were used as proof, and no timing results for the new hash cache are claimed.

Current defaults follow the user's choice to keep incremental canonicalization off:

```python
OPT_INCREMENTAL_CANON = False
OPT_OCCUPANCY_REUSE = True
OPT_HASH_CACHE = True
```

To isolate the new optimization, keep the first two settings fixed and compare OPT_HASH_CACHE=True with OPT_HASH_CACHE=False in fresh processes, using the same checker command, inputs and time limit. Record the Python version as well because CPython 3.14 already performs tuple-hash caching internally.

The proof covers all eight on/off combinations. Turning symmetry off bypasses incremental canonicalization, while occupancy reuse and hash caching remain semantically valid.

The disabled paths retain added slots and inactive bookkeeping checks. They compare strategies within this file; the untouched original file is the exact baseline for a whole-file timing comparison. The correctness theorem concerns identical solution semantics, not identical time-limit outcomes or memory consumption.

SHA-256 of the original file, before these optimizations:

```text
551aefbdf1481f4b3bdc09252dd0f4587dcf1e9ddffd47f1c925c9141255b865
```

SHA-256 of the incremental-only version:

```text
068ed471c7eed92272d82707355d615a8d857fe0cdca10a09ac6fa446572db90
```

SHA-256 of the preceding version with occupancy reuse and incremental canonicalization available:

```text
44662919d7aa8742003ac3602d133136f7901442de82e8f784f602c192cd6637
```

SHA-256 of the current version with lazy state-hash caching:

```text
e6ceb74db92e799a6b964a9e5c035990dd590b5f0a118242d79117fa07d6c29d
```
