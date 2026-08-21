# Chapter 6: `SparseSet`, O(1) Membership with Live-Stable IDs

[← Ch 5: ListArena](05-list-arena.md) · [Table of Contents](00-table-of-contents.md) · [Ch 7: BPlusTreeSet →](07-bplus-tree.md)

A sparse set provides amortized O(1) add, O(1) remove and contains, and O(N)
iteration (apart from the cost of cloning or comparing `T` where an operation
requires it).
An ID remains attached to its value while that entry is live; after removal,
the stale ID is rejected by `contains` and may be recycled for a later value.
It uses three parallel vectors:

```rust
pub struct SparseSet<T, Idx, S, const TRACK: bool> {
    dense:   Vec<T, Idx, S, TRACK>,     // packed payload values
    sparse:  VecI<Idx, Idx, TRACK>,     // id → position in dense
    indices: VecI<Idx, Idx, TRACK>,     // position → id (inverse of sparse)
}
```

## How It Works

The `dense` vector holds values packed with no gaps. The `sparse`
vector maps each id to its position in `dense`. The `indices` vector
is the inverse: it maps each position back to its id.

```
After add(A), add(B), add(C):

  sparse:  [0, 1, 2]     id → pos
  indices: [0, 1, 2]     pos → id
  dense:   [A, B, C]     packed values

  id=0 → sparse[0]=0 → dense[0]=A  ✓
  id=1 → sparse[1]=1 → dense[1]=B  ✓
  id=2 → sparse[2]=2 → dense[2]=C  ✓
```

## Remove: Swap-with-Last

Removing id=1 (value B) swaps it with the last element:

```
Before remove(1):
  sparse:  [0, 1, 2]     indices: [0, 1, 2]     dense: [A, B, C]

After remove(1):
  sparse:  [0, _, 1]     indices: [0, 2, 1]     dense: [A, C]
                                        ↑ recycled slot
  1. last_pos=2, last_id=indices[2]=2
  2. dense[1] = dense[2] = C           (swap value)
  3. indices[1] = 2                     (position 1 now holds id 2)
  4. sparse[2] = 1                      (id 2 is now at position 1)
  5. pop dense                          (shrink by 1)
```

## Contains: Cross-Check

`contains(id)` verifies the sparse→dense→indices round-trip:

```
contains(id):
    pos = sparse[id]
    return pos < dense.len() && indices[pos] == id
```

This catches stale ids: if id was removed, `sparse[id]` still holds
the old position, but `indices[pos]` now points to a different id.

## ID Recycling

When `add()` is called and the dense vector is shorter than the
sparse vector, a previously-removed id is recycled:

```
add(D) after remove(1):
  pos = dense.len() = 2
  recycled_id = indices[2] = 1         (slot 2 in indices still holds old id 1)
  sparse[1] = 2                        (id 1 now at position 2)
  dense.push(D)

  Result: id=1 is reused for value D
```

## Semi-Persistence

All three vectors are semi-persistent. `mark()`/`restore()` snapshots
and restores the entire set. The swap-with-last removal is fully
reversible because the diff log captures the old values of `dense`,
`sparse`, and `indices` before each mutation. Useful for tracking
active elements in a pool with O(1) membership queries and full
backtracking support.

---
[← Ch 5: ListArena](05-list-arena.md) · [Table of Contents](00-table-of-contents.md) · [Ch 7: BPlusTreeSet →](07-bplus-tree.md)
