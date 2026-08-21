# Chapter 6 — Index Construction

[← Ch 5: The E-Graph](05-egraph.md) · [Table of Contents](00-table-of-contents.md) · [Ch 7: Leapfrog Triejoin →](07-leapfrog.md)


## Why Indices?

Pattern matching in an e-graph is a relational join problem. A pattern
like `(Mul (Num x) (Num y))` asks: "find all Mul nodes whose children
are Num nodes." Answering this efficiently requires sorted indices that
the leapfrog join (Chapter 7) can seek into.

The indices are derived structures, not semi-persistent, rebuilt
from scratch each saturation iteration. Rebuilding from scratch is deliberate:
merges change canonical representatives, invalidating all index entries.
Let `N` be indexed nodes, `E` child occurrences, `K` occupied keys, `B` the
largest logical key bound requested, and `H` the retained span-table length.
Stream construction is O(N + E). With sufficiently large recycled arenas, the
four stamped builds are O(N + E + K). Growing an arena adds
O(max(0, B - H)); a fresh build therefore includes O(B). Generation-stamp
exhaustion exceptionally clears O(H) entries. The fan-out pass visits occupied
buckets and their entries. The result has sorted buckets with no tombstones or
readable stale entries.

## `IndexStore`

```rust
pub struct IndexStore<Cfg: EGraphConfig> {
    pub by_op: DenseSpanMap<Cfg::G>,
    pub by_repr: DenseSpanMap<Cfg::G>,
    pub by_child_pos: DenseSpanMap<Cfg::G>,
    pub by_contains: DenseSpanMap<Cfg::G>,
    pub child_pos_stride: usize,
    pub repr: Vec<Cfg::G>,   // build-time representative of each node
    pub op: Vec<Cfg::O>,     // build-time operator of each node
    pub fanouts: FanOuts<Cfg::O>,
}
```

Each family is a `DenseSpanMap` from `containers-verus`: one flat pool holding
every value and a span table saying where each key's run starts and how long it
is (`containers-verus/doc/design/15-dense-span-map.md`). Every key is a dense
integer, so a probe is an array index into the span table and a slice of the
pool, not a hash and a pointer chase into a per-key `Vec`. The container's
`refines()` states that key `k`'s slice is the order-preserving filter of the
build stream down to `k`, which is the property that makes the two-pass counting
build substitutable for the per-key push it replaced.

No index family hashes anything. `FanOuts` still uses ordinary maps for
per-operator aggregate statistics; this chapter makes no fixed performance
claim for their hasher.

Four index families, each answering a different query:

| Index | Key | Answers | Example |
|-------|-----|---------|---------|
| `by_op` | `OpId` | "all nodes with this op" | all Add nodes |
| `by_repr` | canonical `G` | "all nodes in this e-class" | all nodes equivalent to e5 |
| `by_child_pos` | `pos * stride + canonical G` | "parent nodes with this child at this position" | nodes whose child 0 is e3 |
| `by_contains` | canonical `G` | "variadic parent nodes containing this child anywhere" | A/AC/ACI/PlainN nodes containing e3 |

All index keys annotated "canonical" must be post-rebuild representative
ids. This invariant holds because indices are built after rebuild.

`by_contains` is populated for all variadic node kinds: `A`, `AC`,
`ACI`, and `PlainN` (arity > 3). It is NOT limited to AC/ACI; any
node whose children are stored in the pool gets containment indexing.

## The composite `by_child_pos` key

`by_child_pos` is keyed by a `(position, class)` pair, and the pair is flattened
into one integer by `DenseSpanMap::composite_key` as `pos * stride + class`,
where `stride` is the node bound the index was built at.
`lemma_composite_key_injective` establishes that the flattening is injective for
a class below the stride, so a parent filed at one position never appears in
another position's bucket. `IndexStore::nodes_by_child_pos` returns the empty
slice for a class at or above the stride and for a position deeper than any node
in this build has, which is what the hash map returned for a key it had never
inserted.

The layout is position-major rather than class-major for two reasons. One
pattern position's keys are then one contiguous run of the span table. And the
key is computable as each child is visited: the stride is known before the walk,
whereas the deepest position is only known after it.

The logical key bound is the largest composite key encountered plus one, which
can be proportional to the node bound times the deepest indexed position.
`SpanArena` uses generation stamps and occupied-key tracking, so a build writes
only occupied entries, but arena capacity can retain a previously reached high
key. A workload combining a large id space with high-arity variadic nodes can
therefore have a large retained span table; splitting the key space remains a
possible response if Criterion and memory measurements show this case matters.

## Cursors

The cursor over a bucket slice is `SortedVecCursor` from `containers-verus`,
re-exported here. It exposes three operations:

```rust
seek(target: G)    // galloping search: O(log(d + 1)) for advance distance d
key() → Option<G>  // current element
step()             // advance position: O(1)
```

The `seek` operation is what makes leapfrog join efficient: instead of
scanning linearly, it gallops from the current position and bisects the
resulting bounded window in the contiguous slice.

### Why bulk-rebuilt flat arrays?

The implementation uses bulk-rebuilt flat arrays. A `BPlusTreeSet`
alternative exists in the codebase, but it is not wired into `IndexStore`.
Any statement that one is faster must come from the maintained Criterion
benchmark at the revision and workload being evaluated; older isolated
timings are not retained as a design invariant.

The right choice depends in part on how large the delta is between
iterations. Large deltas can favor bulk rebuild; sufficiently small deltas can
make incremental maintenance attractive. Saturation does not guarantee either
trajectory. A future optimization could switch representations dynamically,
but for now every family is bulk-rebuilt. The `BPlusTreeSet` implementation
exists in the codebase (`bplus.rs`).

## Build

```
build(eg):
    stride = eg.node_count()
    for each e-node id in 0..eg.node_count():
        if subsumed: skip
        let repr = eg.class_repr(id)
        stream[by_op].push((eg.node_op(id), id))
        stream[by_repr].push((repr, id))
        for (pos, child) in eg.children(id):
            stream[by_child_pos].push((pos * stride + eg.class_repr(child), id))
        if node is A, AC, ACI, or PlainN:
            for child in eg.variadic_children(id):
                stream[by_contains].push((eg.class_repr(child), id))  // deduped per node
    for each family: DenseSpanMap::try_build_in(arena, stream, largest key + 1)
```

Ids are visited in ascending order, so each family's stream is ascending in its
value, and `lemma_view_sorted` carries that order into every bucket: the bucket
is the stream's order-preserving filter. No per-bucket sort runs, and no
per-bucket `dedup`, because a node is filed under any one key at most once. A
debug assertion re-checks strict ascent per bucket.

The streams are owned by an `IndexScratch`, so the tens of megabytes they occupy
are faulted in once rather than per round.

## The span arena

`IndexScratch` owns the **span arenas**. A plain `DenseSpanMap::try_build`
initializes a table through its key bound. `try_build_in` instead reuses an
arena with generation stamps and an occupied-key list, so the current build
writes the keys its stream occupies rather than clearing the whole logical key
space.

`try_build_in` takes a caller-owned `SpanArena` that outlives the map. The arena
holds the span table, the list of keys the current build occupied, and a
generation stamp. A normal build bumps the stamp and writes only the keys its
stream carries, so a key an earlier build wrote carries an older stamp and
`get` returns the empty slice for it. It does not clear the retained table.
Table growth writes the missing slots, and `u64` stamp exhaustion performs one
full clear before restarting at generation 1.

The arenas are held in two sets of four, because semi-naive keeps the full index
and the round's delta alive at the same time and a family's key space is stable
across rounds. `IndexStore::recycle_into` hands a store's four arenas back to the
scratch; a caller that does not call it loses the reuse and stays correct,
because the next build allocates a fresh arena.

The scratch is owned by the `Interpreter`, not by the saturation call. `(run 1)`
is a single round, so a scratch allocated per call would be dropped before it was
ever reused, and the E6 incremental cycle is twenty `(run 1)`s over one base.
Reuse across calls, and across `(push)` and `(pop)`, needs no invalidation from
the caller: the stamp is what makes an earlier call's content unreadable, and
that is stated in `build_in`'s postcondition rather than assumed.
`egraph/tests/index_arena_reuse.rs` checks the consumer gets it, on a second
build whose key space is smaller than the first's so the stale keys are in range.

`measure_fanouts` also consumes the occupied-key list through
`for_each_occupied`; it no longer scans `0..len()`. A stamped span is wider
than an unstamped span and each probe checks the generation, while sparse
rebuilds avoid full-table clearing. The net tradeoff is workload-dependent and
must be evaluated with Criterion confidence intervals and memory counters.

## `IndexStats`

```rust
pub struct IndexStats<O> {
    pub op_card: HashMap<O, usize>,
    pub fanouts: FanOuts<O>,
    pub atom_card: HashMap<usize, usize>,  // per-atom override (semi-naive)
}
```

`op_card` records each occupied `by_op` cardinality. The scheduler (Chapter 8)
uses that, measured access-path fan-outs, and optional sampling to estimate
candidate counts, then chooses the lowest estimate. `atom_card` overrides
`op_card` per query atom; it is empty for naive matching and filled per
semi-naive flavor, where two atoms sharing an op can have different driver-scan
sizes because they read different index slices (Chapter 18).

## Delta Index for Semi-Naive Evaluation

`IndexStore::build_delta(eg, touched)` builds the same four families
restricted to the `touched` node set. During semi-naive saturation that log
contains fresh nodes, recanonicalized nodes, and members of an absorbed class
whose class assignment changed even when their node representation did not; it
may contain duplicates, which `build_delta` removes. Semi-naive evaluation
pairs a full index with a delta index in a `VariantIndex`, which selects, per
query atom, whether that atom scans the full index, the delta, or
`full ∖ delta`. See Chapter 18.

---
[← Ch 5: The E-Graph](05-egraph.md) · [Table of Contents](00-table-of-contents.md) · [Ch 7: Leapfrog Triejoin →](07-leapfrog.md)
