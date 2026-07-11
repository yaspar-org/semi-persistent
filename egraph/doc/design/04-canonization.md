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
A nodes.

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
4. Apply the op's algebraic laws (`CanonMode`, 2026-07): drop the identity (unit) class
   if the op declares one — the unit is resolved through `find` at canonize time, so a
   summand that merged into the unit's class later still drops — then the count clamp
   (nilpotent: counts mod n, zeroed summands removed). `SetCanon`'s dedup IS the
   idempotent clamp; nilpotent ops are stored MSet precisely because dedup would destroy
   the parity the mod-n clamp needs (see `ac-algebraic-properties.md`).

   When a merge makes a class equal to an op's unit class, `rebuild_congruence` also
   recanonizes every parent in the merged class's use list (not only the absorbed side's
   parents, which are the only ones recanonization normally visits). Reason: parents on
   the surviving side have unchanged child representatives, so nothing re-visits them,
   but the unit-drop rule now applies to their children. This is deliberately not solved
   by forcing the unit's class to be the union survivor: (1) canonical forms must be
   independent of the choice of representative (`ac-congruence-completeness.md` §6c) —
   any behavior conditioned on which element survives a union is order-dependent and
   therefore not canonical; (2) a class may be the unit of one op and an ordinary
   operand of another, so a single per-class survivor cannot encode per-op unit status;
   (3) overriding union-by-rank was implemented, measured slower (16% on the divergent
   benchmark), and removed (`ac-completion-performance.md` §5.6). Both union argument
   orders are covered by `identity_late_merge_mset.egg` and
   `identity_late_merge_direction.egg`.
4. The span may shrink (fewer distinct elements after merging).

```
Before: (add {e3:2, e5:1, e7:1})
Merge e5 into e3:
  find(e3)=e3, find(e5)=e3, find(e7)=e7
  → merge: {e3:2, e3:1, e7:1} → {e3:3, e7:1}
After:  (add {e3:3, e7:1})
```

The canonization buffer is allocated once and reused across all nodes
in a rebuild pass, with no per-node allocation. The caller reads the
buffer length after canonization to determine the new span.

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
| Seq (was A) | `[c₀, ..., cₙ]` | Order preserved | Update in place |
| MSet (theory: AC) | `[(id, mult), ...]` | Sorted by id | Merge multiplicities + clamp + unit-drop |
| Set (theory: ACI) | `[id, ...]` | Sorted, unique | Deduplicate + unit-drop |

---
[← Ch 3: Hash-Consing Caches](03-hash-consing-caches.md) · [Table of Contents](00-table-of-contents.md) · [Ch 5: The E-Graph →](05-egraph.md)
