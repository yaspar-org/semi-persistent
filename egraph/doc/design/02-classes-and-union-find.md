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

```rust
pub struct UnionFind<T: DenseId, const TRACK: bool, const PROOFS: bool> {
    parent_fast: VecI<T, T::Index, TRACK>,
    rank: VecI<u8, T::Index, TRACK>,  // max rank = ⌊log₂(n)⌋ ≤ 63, so u8 suffices
    parent_proof: Option<VecI<T, T::Index, TRACK>>,
    justification: Option<VecI<Justification<T>, T::Index, TRACK>>,
}
```

### Dual Parent Pointers

The union-find maintains two parent vectors when `PROOFS = true`:

- `parent_fast`: path-compressed. Used by `find()` for O(α(n))
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
After:  parent_fast[r_b] = rₐ  (shorter under taller)
        parent_proof[r_b] = rₐ  (if PROOFS)
        justification[r_b] = just  (if PROOFS)
```

### Semi-Persistence

All vectors (`parent_fast`, `rank`, `parent_proof`, `justification`)
are semi-persistent. `mark()`/`restore()` snapshots and undoes all
union operations and path compressions.

## `EClasses` — E-Class Membership and Parent Tracking

```rust
pub struct EClasses<T: DenseId, L: DenseId, N: DenseId, const TRACK: bool, const PROOFS: bool> {
    entries: VecI<EClassEntry<T>, T::Index, TRACK>,
    reprs: SparseSet<L, T::Index, ...>,
    uf: UnionFind<T, TRACK, PROOFS>,
    uses: ListArena<T, L, N, TRACK>,
}
```

`T` is the global e-node id type, `L` is the use-list id type, `N`
is the use-list node id type. There is no sort parameter; sort
information lives in the `OpRegistry`, not in `EClasses`.

### `reprs: SparseSet`

The `reprs` sparse set supports direct enumeration of all current
e-class representatives. Each entry stores a `UseListId`, the head
of the class's parent use-list. When classes merge, the absorbed
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
