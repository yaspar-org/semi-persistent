# Chapter 2 — E-Classes and Union-Find

[← Ch 1: Node Storage](01-node-storage.md) · [Table of Contents](00-table-of-contents.md) · [Ch 3: Hash-Consing Caches →](03-hash-consing-caches.md)


## The Problem

An e-graph maintains equivalence classes of terms. When two terms are
proved equal, their classes merge. The engine needs:

1. Fast find: given any e-node, determine its canonical representative.
   This happens on every child lookup during matching, so it must be O(1).
2. Fast merge: union two classes. This happens on every rewrite firing.
3. Parent tracking: when classes merge, all parent nodes that reference
   the absorbed class must be re-canonized. The engine needs to find those
   parents efficiently.
4. Semi-persistence: push/pop must snapshot and restore the entire
   equivalence relation.
5. Optional proofs: when enabled, record *why* each merge happened so
   the engine can explain any equality.

The engine splits these responsibilities between two structures: `UnionFind`
handles find/merge/proofs, and `EClasses` adds parent tracking and
representative enumeration.

## Union-Find

The e-graph's `UnionFind` is a type alias over the verified kernel in
`containers-verus`, instantiated with `Justification` as the proof payload:

```rust
// egraph/src/union_find.rs
pub type UnionFind<T, const TRACK: bool = true, const PROOFS: bool = false> =
    crate::containers::union_find::UnionFind<T, Justification<T>, TRACK, PROOFS>;

// containers-verus/src/union_find.rs
pub struct UnionFind<T: DenseId, J, const TRACK: bool = true, const PROOFS: bool = false> {
    parent: SpVec<T, T::Index, InlineStore<T, T::Index>, TRACK>,
    rank: SpVec<u8, T::Index, InlineStore<u8, T::Index>, TRACK>,  // max rank = ⌊log₂(n)⌋ ≤ 63, so u8 suffices
    parent_proof: Option<SpVec<T, T::Index, InlineStore<T, T::Index>, TRACK>>,
    justification: Option<SpVec<J, T::Index, InlineStore<J, T::Index>, TRACK>>,
    // ghost state (root map, path-length measure, snapshot archives) elided
}
```

### Dual Parent Pointers

The union-find maintains two parent vectors when `PROOFS = true`:

- `parent`: path-compressed. Used by `find()` for O(α(n))
  lookups. Path compression destroys the original merge tree: after
  `find(a)`, every node on the path from `a` to the root points
  directly to the root.
- `parent_proof`: uncompressed. Preserves the original merge tree
  so the proof system can walk from any node to the root, collecting
  justifications along the way. Never modified by `find()`.

When `PROOFS = false`, `parent_proof` and `justification` are `None`
and never allocated. Zero overhead.

### `find(x) → T`

Path compression: walks parent pointers to the root, then flattens
the path so all nodes point directly to the root. O(α(n)) amortized.

Each path compression write is captured by the diff log (the parent
vector is semi-persistent). This means `restore()` undoes path
compressions too, so the union-find returns to its exact pre-mark state.

### `find_const(x) → T`

Same traversal but without path compression (no mutation). Used during
read-only phases like index construction and rebuild's child
canonization. O(log n) worst case.

### `union(a, b) → Option<(T, T)>`

Union-by-rank: attaches the shorter tree under the taller one.
The rank of a root is an upper bound on the tree's height, and it
only increments when two equal-rank trees merge, so the maximum rank
is ⌊log₂(n)⌋. Even with 2^63 elements the rank cannot exceed 63,
which is why `u8` is the right type: it saves 3 bytes per element
compared to `u32` while being more than large enough.
Returns `Some((survivor, absorbed))` if the two were in different
classes, `None` if already equivalent.

```
Before: find(a)=rₐ, find(b)=r_b, rank(rₐ)=2, rank(r_b)=1
After:  parent[r_b] = rₐ  (shorter under taller)
        parent_proof[r_b] = rₐ  (if PROOFS)
        justification[r_b] = just  (if PROOFS)
```

### Semi-Persistence

All vectors (`parent`, `rank`, `parent_proof`, `justification`)
are semi-persistent. `mark()`/`restore()` snapshots and undoes all
union operations and path compressions.

## `EClasses` — E-Class Membership and Parent Tracking

The e-graph's `EClasses` is a type alias over the verified aggregate in
`containers-verus`:

```rust
// egraph/src/classes.rs
pub type EClasses<T, L, N, const TRACK: bool, const PROOFS: bool> =
    containers::eclasses::EClasses<T, L, N, Justification<T>, TRACK, PROOFS>;

// containers-verus/src/eclasses.rs
pub struct EClasses<T: DenseId, L: DenseId, N: DenseId, J, const TRACK: bool, const PROOFS: bool> {
    entries: CircularList<Opt<T::Index>, T, TRACK>,   // class rings
    reprs: SparseSet<ClassData<L, T>, T::Index, ..., TRACK>,  // per-class data, keyed by repr id
    uf: UnionFind<T, J, TRACK, PROOFS>,
    uses: ListArena<T, L, N, TRACK>,                  // per-class parent lists
    min_pool: SpVec<Opt<T>, usize, ParallelStore<Opt<T>, usize>, TRACK>,  // min-monomial pool
    min_width: usize,                                 // pool row width; 0 until set_min_width
}

pub struct ClassData<L: DenseId, T: DenseId> {
    pub use_list: L,
    pub min_row: Option<T::Index>,
    pub atomic: bool,
    pub size: T::Index,   // member-node count, feeds --union-by size/sum
}
```

`T` is the global e-node id type, `L` is the use-list id type, `N`
is the use-list node id type. There is no sort parameter; sort
information lives in the `OpRegistry`, not in `EClasses`.

### `reprs: SparseSet`

The `reprs` sparse set supports direct enumeration of all current
e-class representatives. Each entry stores a `ClassData`; its
`use_list` field is the head of the class's parent use-list. When
classes merge, the absorbed
class's representative is removed from the set. This avoids scanning
all entries to find roots.

### Use-Lists

Each e-class maintains a singly-linked list of parent nodes, i.e.
nodes that have this class as a child. These lists are stored in a
`semi_persistent::containers::ListArena` (from the `semi-persistent-containers` crate) owned by `EClasses`.

When a new node `(f a b)` is added to the e-graph, it is appended to
the use-lists of both `a` and `b`. When two classes merge, the
absorbed class's use-list is traversed during rebuild to find all
parent nodes that need re-canonization. After processing, the
remaining entries are spliced into the survivor's use-list via O(1)
`ListArena::splice`.

### `add_singleton() → T`

Creates a new e-class with a single member:
1. Allocate a union-find entry (self-loop).
2. Create an `EClassEntry` with an empty use-list.
3. Insert the representative into the `reprs` sparse set.

### `merge(a, b) → Option<MergeInfo>`

1. `uf.union(find(a), find(b))` → `(survivor, absorbed)`.
2. Read the absorbed class's `UseListId` from `reprs`.
3. Remove the absorbed representative from `reprs`.
4. Return `MergeInfo { survivor, absorbed_uses }` for the rebuild
   worklist. Rebuild is not triggered here; it happens lazily at the
start of each saturation iteration or explicitly via `rebuild()`.

---
[← Ch 1: Node Storage](01-node-storage.md) · [Table of Contents](00-table-of-contents.md) · [Ch 3: Hash-Consing Caches →](03-hash-consing-caches.md)

## Merge survivor policy (`--union-by`)

Union-by-rank chooses survivors for tree balance, blind to what a merge costs
downstream: the absorbed side's parents recanonicalize, and under semi-naive
evaluation the absorbed side's member nodes enter the touched log (the
class-growth delta). `--union-by {rank,size,uses,sum}` selects the criterion:
`rank` is the default; `size` absorbs the smaller class by member
count, making the touched-log pushes amortized O(n log n) (a node is absorbed
at most log n times); `uses` absorbs the side with the shorter use-list,
bounding recanonization the same way; `sum` adds the two counters and bounds
both. The counters are verified: the use-list header's cached length was
already tied to the model by `wf` (`cache_len`), and the class member count is
a `ClassData` field whose accuracy clause (W7: stored size equals the ring
length, at every method boundary and in every archived frame) is part of
`eg_model_wf`. Both counters are `Index`-typed, so their width follows the id
configuration.

Survivor choice is semantically free (every class property the engine reads
is merge-folded, §9a), so all four policies produce identical check outcomes,
measured across the comparison corpus. Node counts are identical on
path-independent programs and move only within the documented
order-sensitivity class (budget-capped, goal-stopped, or
scaffolding-path-dependent runs; methodology section 4). Measured on
math-microbenchmark's rules encoding under semi-naive, the class-growth delta
cost drops from 1.69 s under `rank` to 0.60 s under `size`/`uses`/`sum`.
