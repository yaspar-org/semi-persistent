# Semi-Persistent Containers — Design Documents

Semi-persistent data structures with O(1) snapshots and O(k) restoration.
Building blocks for applications that need fast state snapshots and
backtracking — e-graph engines, SAT solvers, constraint propagators,
game-tree searchers, and similar systems.

All containers are built on top of a single core primitive: the
semi-persistent vector (Chapter 2), which uses a diff-log protocol
to record mutations and replay them in reverse on restore.

## Chapters

1. **[Dense Identifiers and the `Tagged` Trait](01-dense-ids-and-tagged.md)**
   How 31-bit ids steal a tag bit for inline capture tracking.
   `DenseId`, `Tagged`, `Opt<T>`, `BoolTagged`. Bit-stealing vs bool-pair.

2. **[Semi-Persistent Vectors](02-semi-persistent-vectors.md)**
   The core primitive. O(1) snapshot, O(k) restore. `InlineStore` vs
   `ParallelStore`. The diff-log protocol. Compile-time elision via
   `const TRACK: bool`.

3. **[`AppendOnlyVec`](03-append-only-vec.md)**
   Push-only vector. Restore = truncate. Useful for interned data,
   string pools, and arena-allocated nodes.

4. **[`Map`](04-map.md)**
   Semi-persistent hash map backed by `AppendOnlyVec` + transient
   `HashMap`. Useful for small registries and symbol tables.

5. **[`ListArena` — Intrusive Linked Lists](05-list-arena.md)**
   Arena of singly-linked list nodes. O(1) prepend, O(n) splice.
   Useful for adjacency lists and dependency tracking.

6. **[`SparseSet` — O(1) Membership](06-sparse-set.md)**
   Three-vector sparse set with O(1) add/remove/contains, stable
   id recycling, and full semi-persistence.

7. **[`BPlusTreeSet` — Arena-Backed B+ Tree](07-bplus-tree.md)**
   Cache-line-aligned B+ tree set with O(log n) insert, O(log n)
   seek, and O(1) step via linked leaves. Semi-persistent via
   a tag bit stolen from the node header.
