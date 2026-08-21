# Semi-Persistent Containers: Design Documents

Semi-persistent data structures with memory-cheap snapshots: O(1) frame
metadata per open mark plus sparse diffs, rather than a copy of the values.
Fork history also grows by O(1) per restore. For `b` fork-history links walked
during token validation, `k` replayed diffs, `r` regrown cells, `q` discarded
live values whose destructors run, `p` surviving-parent diffs, and `w`
materialized bitmap words, vector restore is O(b+k+r+q+p) for inline capture
and O(b+k+r+q+p+w) for parallel capture. This crate is the unverified reference
implementation: the engine links the verified counterpart
(`containers-verus`, aliased as `semi-persistent-containers`), and this
crate serves as the differential-conformance oracle and performance
baseline (`containers-conformance`). The design applies to applications
that need fast state snapshots and backtracking: e-graph engines, SAT
solvers, constraint propagators, game-tree searchers, and similar
systems.

Semi-persistent source-of-truth state is composed from the vector primitives
in Chapters 2 and 3. Containers may also maintain transient acceleration
structures, such as `Map`'s `HashMap`, which are rebuilt from that state after
restore.

## Chapters

1. **[Dense Identifiers and the `Tagged` Trait](01-dense-ids-and-tagged.md)**
   How 31-bit ids steal a tag bit for inline capture tracking.
   `DenseId`, `Tagged`, `Opt<T>`, `BoolTagged`. Bit-stealing vs bool-pair.

2. **[Semi-Persistent Vectors](02-semi-persistent-vectors.md)**
   The core primitive. Sparse-diff snapshots (memory ∝ changes, not a copy),
   backend-specific mark/restore costs. `InlineStore` vs `ParallelStore`. The diff-log protocol.
   Compile-time elision via `const TRACK: bool`.

3. **[`AppendOnlyVec`](03-append-only-vec.md)**
   Push-only vector. Restore = truncate. Useful for interned data,
   string pools, and arena-allocated nodes.

4. **[`Map`](04-map.md)**
   Semi-persistent hash map backed by `AppendOnlyVec` + transient
   `HashMap`. Useful for small registries and symbol tables.

5. **[`ListArena`, Intrusive Linked Lists](05-list-arena.md)**
   Arena of singly-linked list nodes with cached heads and tails. Amortized
   O(1) prepend, append, and splice.
   Useful for adjacency lists and dependency tracking.

6. **[`SparseSet`, O(1) Membership](06-sparse-set.md)**
   Three-vector sparse set with amortized O(1) add and O(1) remove/contains,
   IDs stable while live and recycled after removal, and full
   semi-persistence.

7. **[`BPlusTreeSet`, Arena-Backed B+ Tree](07-bplus-tree.md)**
   Packed, layout-parameterized B+ tree set for 31- and 63-bit dense IDs.
   Supports logarithmic insertion and seek, linked-leaf iteration, bulk
   construction, selectable in-node search, and semi-persistent restore.
