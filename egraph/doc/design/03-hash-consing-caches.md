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

Caches are partitioned by arity and kind. Besides enforcing typed routing, this
packs equal-layout nodes together rather than mixing fixed nodes, pool spans,
and literal payloads in one arena. With the current flags field and 31-bit ids,
a fixed binary node is 20 bytes, as pinned by a layout test. Variadic nodes with
their pool spans live separately. Literal nodes with their value ids are in
their own cache.

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
    index: hashbrown::HashMap<StoredKey<L>, (), PassthroughBuildHasher>,
}
```

The `nodes` vector stores the actual node data, indexed by a typed
local id `L`. Each index entry stores a 32-bit content fingerprint and
the local id; a raw-entry probe confirms the operator and full children in
the node arena before returning its global id. Lookup is expected O(1), subject
to the hash table's usual assumptions.

### Passthrough Hasher

Cache lookups fold the precomputed 64-bit content hash to a 32-bit
fingerprint, spread that fingerprint across the 64 bits consumed by
`hashbrown`, and use a `PassthroughHasher` to avoid hashing it again.
Fingerprint collisions are harmless because probes compare full content.

```rust
struct PassthroughHasher(u64);
impl Hasher for PassthroughHasher {
    fn write_u64(&mut self, i: u64) { self.0 = i; }
    fn finish(&self) -> u64 { self.0 }
}
```

### `probe_or_insert(op, children, global_id) → InsertResult`

1. Receive already canonical children (the `NodeStore` dispatch sorts an
   `SPair`; rebuild invokes the selected canonizer).
2. Compute content hash from `(op, canonical_children)`.
3. Probe index and confirm full content: if found, return
   `InsertResult::Hit { global_id }`.
4. Otherwise, allocate node, insert into index, return
   `InsertResult::Inserted { local_id }`.

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

### `restore(token)`

The `HashMap` index is derived, not semi-persistent, so restoring the
node arena leaves it stale in two ways: it still holds entries for the
suffix nodes the restore deletes, and entries for pre-mark nodes that
were recanonized under the mark point at rewritten keys. `restore`
repairs it in O(suffix + dirty) expected hash-table operations when that
work is small, and rebuilds it in O(n) expected hash-table operations
otherwise. Here `dirty` is the recorded pre-mark recanonization segment,
not the e-graph's semi-naive touched log.

Each `mark` pushes a `CacheFrame { saved_len, dirty_start,
dirty_overflow }`. `saved_len` splits the arena: ids below it keep
their entries, ids at or above it are the suffix to delete.
`dirty_start` cuts a shared `dirty` list into per-frame segments;
`recanonize_node` appends the local id of every pre-mark node whose
key it rewrites. Once a frame already holds more than `saved_len /
REBUILD_RATIO` entries, the next attempted record sets
`dirty_overflow` instead of appending. Thus the implementation can retain
up to `floor(saved_len / REBUILD_RATIO) + 1` entries before overflow;
the ratio test already rejects incremental repair at that point.
Overflow forces the rebuild path because the dirty segment is then
incomplete and incremental repair would leave rewritten keys in the index.

`restore` proceeds in this order:

1. Assert every `Vec` token in the cache token is restorable
   (`is_valid_token`), before any mutation. The deletions in step 3
   are not undoable, so an invalid token must refuse while index and
   arena still agree.
2. Decide the path: incremental iff `dirty_overflow` is unset and
   `REBUILD_RATIO * (suffix + dirty) <= saved_len`.
3. Incremental: delete the index entries for the suffix
   `[saved_len..live_len)` and for the frame's dirty segment, reading
   keys from the still-live arena; restore the arena; re-insert the
   dirty nodes under their restored keys.
   Rebuild: restore the arena, then reconstruct the whole index by
   scanning the surviving nodes.
4. Truncate `dirty` to `dirty_start` and `frames` to the token's
   frame, then `debug_assert!(index_matches_rebuild())`.

`REBUILD_RATIO` is 4. The source comment records the heuristic model:
deletion and insertion are treated as roughly comparable and dirty entries
must be deleted and reinserted. This is a policy threshold, not a benchmarked
or architecture-independent break-even theorem.

## `VariableArityCache`

Same structure but children are stored in a shared pool:

```rust
pub struct VariableArityCache<G, O, C, L, const TRACK: bool, const PROOFS: bool> {
    nodes: VecI<VariableArityNode<G, O>, L, TRACK>,
    children: VecI<C, usize, TRACK>,
    index: hashbrown::HashMap<StoredKey<L>, (), PassthroughBuildHasher>,
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
    index: hashbrown::HashMap<StoredKey<L>, (), PassthroughBuildHasher>,
}
```

Key is `(op, lit_val_id)`. Literal nodes have no e-node children, so
`recanonize_node` is a no-op. `LitCache` also lacks the `PROOFS`
parameter; there is no history bit to manage.

## Source of Truth vs Derived

The node vectors and children pools are the source of truth: they
are semi-persistent and rolled back on backtrack. The `HashMap` index
is derived, repaired in O(suffix + dirty) expected hash-table operations or
reconstructed in O(n) expected operations from the source of truth after
backtrack (see `restore` above). This
separation is deliberate: the index is high-churn (every rebuild
touches it), and making it semi-persistent would add capture bookkeeping to
the forward path. The repair-on-backtrack scheme avoids those tracked writes;
its net performance effect is a benchmark question.

The same pattern covers the literal store (Chapter 13): its
value-to-id `HashMap` is derived from a semi-persistent interning log,
and its restore validates the log token before removing the suffix
entries from the index, for the same reason as step 1 above.

---
[← Ch 2: E-Classes and Union-Find](02-classes-and-union-find.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: Canonization →](04-canonization.md)
