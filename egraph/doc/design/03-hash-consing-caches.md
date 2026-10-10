# Chapter 3 — Hash-Consing Caches

[← Ch 2: E-Classes and Union-Find](02-classes-and-union-find.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: The E-Graph →](04-egraph.md)

## The Structural Sharing Invariant

Hash-consing ensures structural sharing: two nodes that start with
different children can, after merges, converge to the same structure
(same operator, same e-classes as children). When that happens, the
hash-consing cache detects the collision and the two nodes' respective
e-classes are merged. This is congruence closure.

The challenge is that "same canonical children" is a moving target.
When two classes merge, a node's canonical children change, and the
cache must be updated. This is the re-canonization problem, handled
by rebuild (Chapter 4). This chapter focuses on the cache structure
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
| `LitCache` | `LitNode<G, V>` | `(op, lit)` |

## `FixedArityCache`

```rust
pub struct FixedArityCache<G, O, L, const K: usize, const TRACK: bool, const PROOFS: bool,
                           P = HotFirst> {
    nodes: Vec<FixedArityNode<G, O, K>, L, <P as TaggedFamily<..>>::Store, TRACK>,
    index: hashbrown::HashMap<FpKey, HintSlot<L>, PassthroughBuildHasher>,
    spill: Vec<HintBucket<L>>,
    history: Option<VecI<..>>,     // recanonicalization history, under PROOFS
    frames: Vec<CacheFrame>,
}
```

The `nodes` vector stores the actual node data, indexed by a typed
local id `L`. The `index` is a hint index: it maps a 32-bit content fingerprint to
the local ids that held content with that fingerprint at some point. A `HintSlot` with
its tag clear holds a single local id; with the tag set it indexes a `spill` bucket
listing several. A probe confirms the operator and full children of every candidate
in the node arena before returning its global id. Lookup is expected O(1), subject
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

### `probe_or_insert(global_id, op, children) → InsertResult`

1. Receive already canonical children (the `NodeStore` dispatch sorts an
   `SPair`; rebuild invokes the selected canonizer).
2. Compute content hash from `(op, canonical_children)`.
3. Probe index and confirm full content: if found, return
   `InsertResult::Hit { global_id }`.
4. Otherwise, allocate node, insert into index, return
   `InsertResult::Inserted { local_id }`.

### `recanonize_node(local_id, find, collisions, touched)`

During rebuild:
1. Read current children.
2. Apply `find()` to each child.
3. If unchanged → done.
4. If changed: update children in node, push the node onto `touched`, and
   compute the new fingerprint. The hint for the old content stays in its bucket.
5. Probe the hints for the new content, excluding this node. A hit is a congruence:
   report `(this_global_id, existing_global_id)` to the collision list and flag this
   node `FLAG_CONGRUENT_DUP`.
6. If there was no collision and the node does not carry `FLAG_CONGRUENT_DUP`, push a
   hint for the new content. A flagged node gets no hint, so a probe never returns
   one and every collision's survivor is unflagged.

### `reset_frame(depth)` (formerly `restore(token)`)

The hint index is derived state and takes no part in the semi-persistence protocol:
a restore does no index work. Rolling the node arena back revalidates the hints for
the old content and invalidates those for content written under the mark, because a
probe checks every candidate against the arena. This is what removed the re-key
repair from the restore path (commit `2e19432`, 2026-09-09). It also keeps a cluster of
congruent duplicates, many nodes with one content after merges, to one bucket instead
of a long same-hash probe chain.

Since 2026-09-18 the caches carry no tokens: the e-graph's single `History` owns them,
and a cache sees only the structural protocol — `push_frame`, `reset_frame(depth)`,
`restore_frame(depth)`, `pop_frame`, `frame_depth` — driven through the forwarding view
`EGraphMembers`. `CacheFrame` is a unit struct, so the frame stack only counts the open
frames. The group has already validated the token and the members' lockstep before any
member is touched, and `reset_frame` is called only with a depth below the live one.

`reset_frame` resets the node arena and, under `PROOFS`, the history column to the
frame at `depth`, and truncates `frames` to `depth + 1` under semantics B, since the
checkpoint's frame stays open; the fused `restore_frame` truncates exactly to `depth`.
Then `debug_assert!(index_is_complete())` checks that a probe finds the content of every
live node.

`REBUILD_RATIO` (4) and `restore_incrementally` remain in `caches.rs` as dead code with
their test, kept as the policy for a future append-only index; the hint index has no
rebuild path.

## `VariableArityCache`

Same structure but children are stored in a shared pool:

```rust
pub struct VariableArityCache<G, O, C, L, const TRACK: bool, const PROOFS: bool, P = HotFirst> {
    nodes: Vec<VariableArityNode<G, O>, L, <P as ..>::Store, TRACK>,
    children: Vec<C, usize, <P as ..>::Store, TRACK>,
    index: hashbrown::HashMap<FpKey, HintSlot<L>, PassthroughBuildHasher>,
    spill: Vec<HintBucket<L>>,
    history_nodes, history_children,   // under PROOFS
    frames: Vec<CacheFrame>,
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
pub struct LitCache<G, O, V, L, const TRACK: bool, P = HotFirst> {
    nodes: Vec<LitNode<G, O, V>, L, <P as ..>::Store, TRACK>,
    index: hashbrown::HashMap<FpKey, HintSlot<L>, PassthroughBuildHasher>,
    spill: Vec<HintBucket<L>>,
    frames: Vec<CacheFrame>,
}
```

Key is `(op, lit)`. Literal nodes have no e-node children, so `LitCache` has no
`recanonize_node`: `NodeStore::recanonize_node` returns `Normal::Node` for a literal
node without touching the cache. `LitCache` also lacks the `PROOFS`
parameter; there is no history bit to manage.

## Source of Truth vs Derived

The node vectors and children pools are the source of truth: they
are semi-persistent and rolled back on backtrack. The hint index
is derived: a restore leaves it untouched, and probes validate its entries
against the restored arena (see `reset_frame` above). This
separation is deliberate: the index is high-churn (every rebuild
touches it), and making it semi-persistent would add capture bookkeeping to
the forward path.

The literal store (Chapter 10) does not follow this pattern. It is an
`SpUniqueMap` (`literal.rs`), whose log of canonical keys and values is the source of
truth and whose index belongs to the verified map; it takes no token, and its frame
operations are driven by the `History` like every other member.

---
[← Ch 2: E-Classes and Union-Find](02-classes-and-union-find.md) · [Table of Contents](00-table-of-contents.md) · [Ch 4: The E-Graph →](04-egraph.md)
