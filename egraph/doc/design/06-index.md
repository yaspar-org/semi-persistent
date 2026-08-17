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
Rebuilding is O(n) where n is the total number of e-nodes, and it
produces perfectly sorted arrays with no tombstones or stale entries.

## `IndexStore`

```rust
pub struct IndexStore<Cfg: EGraphConfig> {
    pub by_op: DenseSpanMap<Cfg::G>,
    pub by_repr: DenseSpanMap<Cfg::G>,
    pub by_child_pos: DenseSpanMap<Cfg::G>,
    pub by_contains: DenseSpanMap<Cfg::G>,
    pub child_pos_stride: usize,
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

No family hashes anything. `doc/perf-results/E3-index-hasher.md` measured
foldhash against SipHash on these maps at 4.5-10% end to end; that result now
applies only to the per-operator statistics maps `FanOuts` carries.

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

The span table's length is the largest key the stream carried plus one, so the
`by_child_pos` table is proportional to the node bound times the deepest arity in
the graph. On the comparison corpus the deepest arity is 2 for both
`math-microbenchmark` encodings and 20 for `addac-n20.native`, whose graph is 77
nodes. A program that combines a large id space with a high-arity variadic
operator would allocate a span table proportional to their product; the family
stays correct, the memory is the cost. Splitting the key space is the fix if a
workload is measured to hit it.

## Cursors

The cursor over a bucket slice is `SortedVecCursor` from `containers-verus`,
re-exported here. It exposes three operations:

```rust
seek(target: G)    // galloping search on the slice: O(log n)
key() → Option<G>  // current element
step()             // advance position: O(1)
```

The `seek` operation is what makes leapfrog join efficient: instead of
scanning linearly, it jumps directly to the next candidate via binary
search on a contiguous slice.

### Why bulk-rebuilt flat arrays?

We benchmarked two strategies: incrementally maintained `BPlusTreeSet`s
(a cache-line-aligned B+ tree with O(log n) insert and linked-leaf
iteration) versus bulk-rebuilt sorted `Vec`s. The flat array won:
binary search on a contiguous slice has better cache behavior than
tree traversal, and the bulk sort amortizes well.

The right choice depends on how large the delta is between iterations.
Early in saturation, deltas are large (many new nodes per iteration),
favoring bulk rebuild. Later, deltas shrink and incremental
maintenance could win. A future optimization could switch
representations dynamically, but for now every family is bulk-rebuilt.
The `BPlusTreeSet` implementation exists in the
codebase (`bplus.rs`) but is not currently wired into the index.

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

## The span arena, and why the build is not proportional to the key space

`IndexScratch` also owns the **span arenas**, and they are the reason a build
costs what its stream costs rather than what its key space costs. A
`DenseSpanMap` built by `try_build` allocates a span table of one entry per key
and writes all of it, which is `O(num_keys)` whether or not the keys occur. That
term dominated: `comparison/span-table-sparsity.md` measures `by_child_pos` at
S = 1e6 addressing 801 008 values with 2 003 967 keys, and the build spending
40.6 ms per round writing 77 MB of span table for a 3.2 MB pool. On a semi-naive
delta the ratio is the whole cost, because the delta's stream is a few thousand
values over the same key space.

`try_build_in` takes a caller-owned `SpanArena` that outlives the map. The arena
holds the span table, the list of keys the current build occupied, and a
generation stamp. A build bumps the stamp and writes only the keys its stream
carries, so a key an earlier build wrote carries an older stamp and `get`
returns the empty slice for it. Nothing is cleared. Work is proportional to the
stream and the keys it occupies.

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

**The fan-out pass still scans the key space.** `measure_fanouts` needs every
occupied key, the arena maintains exactly that list, and the list is
`pub(crate)`: there is no exported iterator, so `index.rs` walks `0..len()` and
skips the empty buckets. At S = 1e6 that is 7.69 ms of a 32.64 ms index build,
and it is the largest single term left in the build. Exporting the occupancy list
is a `containers-verus` change and the next reduction available.

**A stamped span is 24 bytes against 16, and the probe path pays for it.**
Matching measures 5% slower, reproducibly, because a probe reads a span table
1.5 times wider and compares the stamp before returning the slice. The round
total falls anyway, 170.5 ms to 151.2 ms at S = 1e6. A workload whose rounds are
dominated by probing rather than by building would come out the other way; which
one applies to a given workload is a measurement, and `run-span-table.py --wall`
is how to take it.

## `IndexStats`

```rust
pub struct IndexStats<O> {
    pub op_card: HashMap<O, usize>,
    pub atom_card: HashMap<usize, usize>,  // per-atom override (semi-naive)
}
```

Cardinality of each `by_op` entry. Used by the scheduler (Chapter 8)
to estimate query plan costs: the scheduler picks the atom with the
smallest cardinality first. `atom_card` overrides `op_card` per query
atom; it is empty for naive matching and filled per semi-naive flavor,
where two atoms sharing an op can have different driver-scan sizes
because they read different index slices (Chapter 18).

## Delta Index for Semi-Naive Evaluation

`IndexStore::build_delta(eg, touched)` builds the same four families
restricted to the `touched` node set (the nodes whose canonical form
changed this round, logged on the e-graph). Semi-naive evaluation pairs
a full index with a delta index in a `VariantIndex`, which selects—per
query atom—whether that atom scans the full index, the delta, or
`full ∖ delta`. See Chapter 18.

---
[← Ch 5: The E-Graph](05-egraph.md) · [Table of Contents](00-table-of-contents.md) · [Ch 7: Leapfrog Triejoin →](07-leapfrog.md)
