# Chapter 4 — Canonization Algorithms

[← Ch 3: Hash-Consing Caches](03-hash-consing-caches.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: The E-Graph →](05-egraph.md)


## Why Canonization Matters

When two e-classes merge, parent nodes that reference the absorbed
class must update their children to point to the survivor. But for
operators with algebraic properties, simply replacing child ids is
not enough; the canonical form must be restored.

Consider a commutative `eq` node stored as `(eq e3 e7)` with the
invariant `child₀ ≤ child₁`. If `e7` merges into `e2`, the node
becomes `(eq e3 e2)`, violating the sort invariant. The cache would
fail to detect that `(eq e2 e3)` already exists, missing a congruence.

Each operator kind has its own canonization strategy, expressed via
two traits: `FixedCanon` for fixed-arity nodes and `VarCanon` for
variable-arity nodes. The strategy is a type parameter on the cache,
so the compiler monomorphizes, with no dynamic dispatch.

## `PlainCanon` — Ordered Children

For plain operators: children are stored in declaration order.
Canonization applies `find()` to each child in place, with no
reordering. This strategy covers Plain0 through Plain3, PlainN, and
A nodes. (`OrderedCanon` is the variable-arity form, used by PlainN
and Seq.) A nodes carry an additional *build-time* normal form on top
of this; see "A-Only Operators" below.

## `CCanon` — Commutative Pair

For binary commutative operators: children are stored sorted by id.
After applying `find()`, the pair is re-sorted.

```
Before merge: (eq e3 e7)  stored as (eq 3 7)  ✓ sorted
After find:   (eq e3 e2)  → re-sort → (eq 2 3)
```

If re-sorting produces a different content hash, the old cache entry
is removed and a new one is inserted. If the new hash collides with
an existing node, that's a congruence.

## `MSetCanon` — Multiset Canonization

For AC operators: children are `(id, multiplicity)` pairs stored
sorted by id. Canonization:

1. Apply `find()` to each id.
2. If two entries now have the same canonical id, merge their
   multiplicities (sum them).
3. Re-sort by canonical id.
4. Apply the op's algebraic laws (`CanonMode`): drop the identity (unit) class
   if the op declares one (the unit is resolved through `find` at canonize time, so a
   summand that merged into the unit's class later still drops), then the count clamp
   (nilpotent: counts mod n, zeroed summands removed). `SetCanon`'s dedup IS the
   idempotent clamp; nilpotent ops are stored MSet precisely because dedup would destroy
   the parity the mod-n clamp needs (see `ac-algebraic-properties.md`).

   When a merge makes a class equal to an op's unit class, `rebuild_congruence` also
   recanonizes every parent in the merged class's use list (not only the absorbed side's
   parents, which are the only ones recanonization normally visits). Reason: parents on
   the surviving side have unchanged child representatives, so nothing re-visits them,
   but the unit-drop rule now applies to their children. This is deliberately not solved
   by forcing the unit's class to be the union survivor: (1) canonical forms must be
   independent of the choice of representative (`ac-congruence-completeness.md` §6c):
   any behavior conditioned on which element survives a union is order-dependent and
   therefore not canonical; (2) a class may be the unit of one op and an ordinary
   operand of another, so a single per-class survivor cannot encode per-op unit status.
   Both union argument orders are covered by `identity_late_merge_mset.egg` and
   `identity_late_merge_direction.egg`.
4. The span may shrink (fewer distinct elements after merging).

```
Before: (add {e3:2, e5:1, e7:1})
Merge e5 into e3:
  find(e3)=e3, find(e5)=e3, find(e7)=e7
  → merge: {e3:2, e3:1, e7:1} → {e3:3, e7:1}
After:  (add {e3:3, e7:1})
```

The e-graph owns reusable `Vec` scratch buffers and clears/reuses them across
nodes. A node visit does not deliberately create a fresh scratch vector, but a
buffer may allocate when a larger input exceeds its retained capacity. The
caller reads the buffer length after canonization to determine the new span.

## `SetCanon` — Set Canonization

For ACI operators: children are deduplicated ids, stored in sorted order.
Canonization:

1. Apply `find()` to each id.
2. Sort.
3. Remove duplicates (since `x ∪ x = x`).
4. The span may shrink.

```
Before: (or {e3, e5, e7})
Merge e5 into e3:
  find(e3)=e3, find(e5)=e3, find(e7)=e7
  → sort+dedup: {e3, e3, e7} → {e3, e7}
After:  (or {e3, e7})
```

## A-Only Operators — Flattening and Singleton Collapse

Every A-only sequence spelling uses an order-preserving `Seq`, but `AssocDir`
controls which nested same-op children are part of that sequence:
`:assoc-left` flattens the first-child spine, `:assoc-right` flattens the
last-child spine, and bare `:assoc` flattens every nested same-op child. Two
laws follow, and both run in `EGraph::add`, including when a rewrite RHS builds
a term:

1. **Flatten the selected spine.** A selected child whose class is an
   `op`-sequence is spliced into the parent's sequence, at the child's position,
   to a fixpoint (`flatten_seq_children`). For `:assoc-left`,
   `op(op(a,b),c)` and `op(a,b,c)` are one node while `op(a,op(b,c))`
   retains its grouped right child. `:assoc-right` is the mirror image.
   Bare `:assoc` makes both nestings and `op(a,b,c)` one node. Every mode
   preserves order.
2. **Collapse the singleton.** A one-element sequence is its element, so `add`
   returns that child's class instead of minting a node: the same degenerate-arity
   resolution the MSet and Set arms perform, and the reason a program does not have
   to state `(rewrite (op x) x)` for itself. There is no empty case: an A-only
   operator has no identity (see below), so the empty sequence names nothing.
   Sortcheck rejects a zero-argument A application, and `add` panics if one
   reaches it.

### Which child is spliced

Direction chooses the candidates: the first child for `Left`, the last for
`Right`, and every child for `Both`. For each candidate, `pure_seq_node`
splices it iff **every** member of its class is an `op` `Seq` node, choosing
the class's **least node id** when several spellings exist.

Both halves answer the representative trap (`ac-congruence-completeness.md`
§6c): a test keyed on `find(child)` flattens or not depending on which node the
union-find happened to make representative, so it is a function of merge history
rather than of e-graph state, and the resulting normal form is not canonical.
Current class membership plus the least fixed node id are independent of which
member the union-find selected as representative (node ids are assigned at
creation and never renumbered). Every spelling of a child therefore selects the
same sequence in that e-graph state, and the parents land in one class. This is
not an invariance claim across different node-insertion orders.

AC's `atomic` bit cannot serve as the predicate here. `register_if_fresh` sets
it on every class whose op has no completion column, which includes every `Seq`
class, so for A-only operators it is constantly true. Purity plays the same
role: a class holding only `op`-sequences has no standalone atom form, so
spelling it out is forced, and a class that also holds an atom is left alone.
That case is not hypothetical: once a rule proves `gmul(b, inv(b)) = I`, the
identity's class holds a `Seq` node, and splicing it into every later sequence
would rewrite uphill and grow terms without bound.

### `:identity` on an A-only operator

Rejected at registration, and this is the spec's answer, not an omission.
`OpKind::A` carries no identity field, and the property-tag resolver
(`sortcheck.rs`) rejects `:identity` (along with `:idempotent`, `:nilpotent`
and `:inverse`) on an operator that is not also `:comm`. The unit-drop law and
the empty-monomial degeneracy it enables are therefore MSet/Set-only, and the A
arm of `add` has no unit to resolve.

### Recanonization

Nothing changes on the recanonize path: `OrderedCanon` applies `find()` and
preserves both order and arity, so a `Seq` node's canonical form after a merge
is the same node with canonical children, and `degeneracy_merge` has no `Seq`
case to answer. Re-flattening is not possible there in any event:
`recanonize_node` rewrites children into the node's existing span, which can
shrink but not grow.

The build-only placement matches the AC counterpart's current design
(`ac-congruence-completeness.md` §6c). For A-only the placement leaves a
gap: if a class stored as a `Seq` child later
merges with a pure `op`-sequence class, the parent is not re-flattened, so
`op(x,d)` and `op(a,b,d)` stay distinct after `x = op(a,b)` is proved. A-only
inter-reduction (`a_round`) closes some such contiguous-subsequence cases when
completion is enabled. Plain mode does not run that pass, and even completion
mode does not claim a complete decision procedure for arbitrary ground
associative equations.

### What flattening erases

`ac-congruence-completeness.md` §2 states the trade for AC: flattening erases
the intermediate sub-term, so a rule written against the nested shape has
nothing to match. A-only operators inherit that trade along the selected
spine. After a left-associative `op(op(a,b),c)` flattens, no node spells the
intermediate `op(a,b)` *as a child*, so a binary pattern `(op ?x ?y)` no longer
matches the three-element term: it is an exact pattern against a sequence of a
different length. The unselected side remains explicitly grouped. Patterns
over A operators are written with rest variables (`(op ..p ?x ..s)`), which
is what makes an interior position expressible at all;
`egraph/tests/egg/bench/calc.native.egg` is the worked example.

The erasure is of the *occurrence*, not of the class. Flattening rewrites the
child list of the node being built and nothing else: the spliced class keeps its
node, its use-list and its membership, stays hash-consed, and stays reachable
through `find`. This is the same statement as §6c's "the inlined class does not
disappear".

### Proof mode

Both laws are silent under `PROOFS`. Flattening changes which node `add` builds,
and the singleton collapse returns an existing class rather than merging two;
neither records a justification, because neither is an inference: they are the
definition of the operator's canonical form, in the same sense as the MSet
unit-drop and the MSet/Set degeneracy resolution, which are equally silent. An
explanation therefore never contains a re-association step, and a term's proof is
a proof about its normal form.

## Congruence Detection

After re-canonization, the cache is re-probed with the new canonical
children. If a *different* existing node has the same canonical
children, this is a congruence: the two nodes must be merged.

```
Before merge: (f a b) and (f a c) are distinct.
After merge(b, c): both canonize to (f a find(b)).
→ Congruence collision: merge the two f-nodes.
```

Congruence collisions are added to the rebuild worklist.
Cascading congruence is the mechanism by which the e-graph maintains
the congruence closure invariant (drain the worklist, unioning collided
e-classes and collecting new collisons until none subsist).

## Summary

| Kind | Children | Canonical form | Merge behavior |
|------|----------|---------------|----------------|
| Plain | `[c₀, ..., cₙ]` | Order preserved | Update in place |
| SPair (was C) | `[c₀, c₁]` | Sorted pair | Re-sort |
| Seq (theory: A) | `[c₀, ..., cₙ]` | Directionally flattened sequence, order preserved | Update in place (flatten + singleton collapse are build-time) |
| MSet (theory: AC) | `[(id, mult), ...]` | Sorted by id | Merge multiplicities + clamp + unit-drop |
| Set (theory: ACI) | `[id, ...]` | Sorted, unique | Deduplicate + unit-drop |

---
[← Ch 3: Hash-Consing Caches](03-hash-consing-caches.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: The E-Graph →](05-egraph.md)
