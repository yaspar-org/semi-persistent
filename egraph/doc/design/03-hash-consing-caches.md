# Chapter 3 — Hash-Consing Caches

[← Ch 2: E-Classes and Union-Find](02-classes-and-union-find.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: Canonization →](04-canonization.md)


## The Structural Sharing Invariant

Hash-consing ensures structural sharing: two nodes that start with
different children can, after merges, converge to the same structure
(same operator, same e-classes as children). When that happens, the
hash-consing cache detects the collision and the two nodes' respective
e-classes are merged. This is congruence closure.

The challenge is that "same canonical children" is a moving target.
When two classes merge, a node's canonical children change, and the
cache must be updated. This is the re-canonization problem, handled
by rebuild (Chapter 5). This chapter focuses on the cache structure
itself.

## Cache Partitioning

Caches are partitioned by arity and kind. This is not just for type
safety; it also improves cache locality. Binary nodes (the vast majority
in most e-graphs) are packed together in 16-byte structs. Variadic
nodes with their pool spans live separately. Literal nodes with their
value ids are in their own cache.

| Cache | Node type | Key |
|-------|-----------|-----|
| `FixedArityCache<.., 0>` | `FixedArityNode<G, 0>` | `(op)` |
| `FixedArityCache<.., 1>` | `FixedArityNode<G, 1>` | `(op, c₀)` |
| `FixedArityCache<.., 2>` | `FixedArityNode<G, 2>` | `(op, c₀, c₁)` |
| `FixedArityCache<.., 3>` | `FixedArityNode<G, 3>` | `(op, c₀, c₁, c₂)` |
| `FixedArityCache<.., 2>` (C) | `FixedArityNode<G, 2>` | `(op, min, max)` |
| `VariableArityCache` | `VariableArityNode<G>` | `(op, pool[start..end])` |
| `LitCache` | `LitNode<G, V>` | `(op, lit_val_id)` |

## `FixedArityCache`

```rust
pub struct FixedArityCache<G, O, L, const K: usize, const TRACK: bool, const PROOFS: bool> {
    nodes: VecI<FixedArityNode<G, O, K>, L, TRACK>,
    index: HashMap<StoredKey, G, PassthroughBuildHasher>,
}
```

The `nodes` vector stores the actual node data, indexed by a typed
local id `L`. The `index` HashMap maps content hashes to global ids
for O(1) lookup.

### Passthrough Hasher

Cache lookups use a `PassthroughHasher` that treats the pre-computed
content hash as the final hash value. This avoids double-hashing:
the content hash is computed once from `(op, children)` using a fast
hash function, then used directly as the `HashMap` key.

```rust
struct PassthroughHasher(u64);
impl Hasher for PassthroughHasher {
    fn write_u64(&mut self, i: u64) { self.0 = i; }
    fn finish(&self) -> u64 { self.0 }
}
```

### `probe_or_insert(op, children, global_id) → InsertResult`

1. Canonize children (for C: sort the pair).
2. Compute content hash from `(op, canonical_children)`.
3. Probe index: if found, return `InsertResult::Existing(global_id)`.
4. Otherwise, allocate node, insert into index, return
   `InsertResult::Fresh(local_id)`.

### `recanonize_node(local_id, find, collisions)`

During rebuild:
1. Read current children.
2. Apply `find()` to each child.
3. If unchanged → done.
4. If changed: remove old entry from index, update children in node,
   compute new content hash, probe index.
5. If new hash collides with an existing node: congruence. Report
   `(this_global_id, existing_global_id)` to collision list.
6. Otherwise, insert new entry into index.

### `rebuild_index()`

After `restore()`, the `HashMap` index may be stale (it is a derived
structure, not semi-persistent). `rebuild_index()` reconstructs it by
scanning all surviving nodes. This is O(n) but only happens on
backtrack, not on every saturation iteration.

## `VariableArityCache`

Same structure but children are stored in a shared pool:

```rust
pub struct VariableArityCache<G, O, C, L, const TRACK: bool, const PROOFS: bool> {
    nodes: VecI<VariableArityNode<G, O>, L, TRACK>,
    pool: VecI<C, ...>,
    index: HashMap<StoredKey, G, PassthroughBuildHasher>,
}
```

Content hash includes all pool elements in the span. For AC nodes,
children are `(id, multiplicity)` pairs sorted by id. For ACI nodes,
children are deduplicated ids sorted.

On re-canonization, each child in the span is updated via `find()`.
For AC: if two children merge to the same id, their multiplicities
are summed and the span may shrink. For ACI: duplicates are removed
and the span may shrink.

## `LitCache`

```rust
pub struct LitCache<G, O, V, L, const TRACK: bool> {
    nodes: VecI<LitNode<G, O, V>, L, TRACK>,
    index: HashMap<StoredKey, G, PassthroughBuildHasher>,
}
```

Key is `(op, lit_val_id)`. Literal nodes have no e-node children, so
`recanonize_node` is a no-op. `LitCache` also lacks the `PROOFS`
parameter; there is no history bit to manage.

## Source of Truth vs Derived

The node vectors and children pools are the source of truth: they
are semi-persistent and rolled back on backtrack. The `HashMap` index
is derived, rebuilt from the source of truth after backtrack. This separation is deliberate: the index is high-churn
(every rebuild touches it), and making it semi-persistent would add
overhead for no benefit since it can be reconstructed in O(n).

---
[← Ch 2: E-Classes and Union-Find](02-classes-and-union-find.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: Canonization →](04-canonization.md)
