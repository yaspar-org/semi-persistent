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
    pub by_op: HashMap<Cfg::O, SortedVec<Cfg::G>>,
    pub by_repr: HashMap<Cfg::G, SortedVec<Cfg::G>>,
    pub by_child_pos: HashMap<(Cfg::G, u32), SortedVec<Cfg::G>>,
    pub by_contains: HashMap<Cfg::G, SortedVec<Cfg::G>>,
}
```

Four index families, each answering a different query:

| Index | Key | Answers | Example |
|-------|-----|---------|---------|
| `by_op` | `OpId` | "all nodes with this op" | all Add nodes |
| `by_repr` | canonical `G` | "all nodes in this e-class" | all nodes equivalent to e5 |
| `by_child_pos` | `(canonical G, pos)` | "parent nodes with this child at this position" | nodes whose child 0 is e3 |
| `by_contains` | canonical `G` | "variadic parent nodes containing this child anywhere" | A/AC/ACI/PlainN nodes containing e3 |

All index keys annotated "canonical" must be post-rebuild representative
ids. This invariant holds because indices are built after rebuild.

`by_contains` is populated for all variadic node kinds: `A`, `AC`,
`ACI`, and `PlainN` (arity > 3). It is NOT limited to AC/ACI; any
node whose children are stored in the pool gets containment indexing.

## `SortedVec` and Cursors

Values in each index are stored in a `SortedVec<G>`, a densely packed
and sorted `Vec<G>`. The entire index is bulk-rebuilt each iteration:
entries are collected into unsorted `Vec`s, then `sort_unstable` +
`dedup` produces the final sorted arrays. The cursor over a
`SortedVec` exposes three operations:

```rust
seek(target: G)    // partition_point on the slice: O(log n)
key() → Option<G>  // current element
step()             // advance position: O(1)
```

The `seek` operation is what makes leapfrog join efficient: instead of
scanning linearly, it jumps directly to the next candidate via binary
search on a contiguous slice.

### Why Bulk-Rebuilt Sorted Vecs?

We benchmarked two strategies: incrementally maintained `BPlusTreeSet`s
(a cache-line-aligned B+ tree with O(log n) insert and linked-leaf
iteration) versus bulk-rebuilt sorted `Vec`s. The sorted `Vec` won:
binary search on a contiguous slice has better cache behavior than
tree traversal, and the bulk sort amortizes well.

The right choice depends on how large the delta is between iterations.
Early in saturation, deltas are large (many new nodes per iteration),
favoring bulk rebuild. Later, deltas shrink and incremental
maintenance could win. A future optimization could switch
representations dynamically, but for now bulk-rebuilt sorted `Vec`s
are used uniformly. The `BPlusTreeSet` implementation exists in the
codebase (`bplus.rs`) but is not currently wired into the index.

## Build

```
build(eg):
    for each e-node id in 0..eg.node_count():
        if subsumed: skip
        let repr = eg.class_repr(id)
        by_op[eg.node_op(id)].push(id)
        by_repr[repr].push(id)
        for (pos, child) in eg.children(id):
            by_child_pos[(eg.class_repr(child), pos)].push(id)
        if node is A, AC, ACI, or PlainN:
            for child in eg.variadic_children(id):
                by_contains[eg.class_repr(child)].push(id)  // deduped per node
    sort all SortedVecs
```

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

`IndexStore::build_delta(eg, touched)` builds the same four maps
restricted to the `touched` node set (the nodes whose canonical form
changed this round, logged on the e-graph). Semi-naive evaluation pairs
a full index with a delta index in a `VariantIndex`, which selects—per
query atom—whether that atom scans the full index, the delta, or
`full ∖ delta`. See Chapter 18.

---
[← Ch 5: The E-Graph](05-egraph.md) · [Table of Contents](00-table-of-contents.md) · [Ch 7: Leapfrog Triejoin →](07-leapfrog.md)
