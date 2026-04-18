# Chapter 7 — Leapfrog Triejoin

[← Ch 6: Index Construction](06-index.md) · [Table of Contents](00-table-of-contents.md) · [Ch 8: Query Compilation →](08-query-compilation.md)


## The Join Problem

Pattern matching in an e-graph is a multi-way join. The pattern
`(f (g x) (h x))` produces three constraints:

1. `by_op(f)` — all f-nodes
2. `by_child_pos(class_of_g_node, 0)` — parents with this child at pos 0
3. `by_child_pos(class_of_h_node, 1)` — parents with this child at pos 1

The answer is the intersection of these sorted sets. A naive nested
loop is O(n²) for a 2-way join. Leapfrog triejoin computes the
intersection in worst-case optimal time.

## The Algorithm

Leapfrog maintains a vector of sorted iterators (cursors), all
seeking to agree on the same key.

```rust
pub struct LeapfrogJoin<'a, G: DenseId> {
    iters: Vec<SortedVecIter<'a, G>>,
}
```

### Initialization

Sort iterators by their current key. Seek all iterators to the
maximum of their initial keys. If any iterator is exhausted, the
join is empty.

### Finding the Next Match

Instead of checking every element, the algorithm uses `seek` to
skip directly to the next candidate.

```
Iterators (sorted by current key):
  A: [2, 5, 8, 12, 15]   cursor at 2
  B: [3, 5, 9, 12, 20]   cursor at 3
  C: [1, 5, 7, 12, 18]   cursor at 5

Round 1: max = 5 (from C)
  A.seek(5) → 5    B.seek(5) → 5    C already at 5
  All agree on 5 → MATCH

Round 2: advance past 5
  A.step() → 8     (now lagging)
  max = 8
  B.seek(8) → 9    C.seek(8) → 12
  max = 12
  A.seek(12) → 12  B.seek(12) → 12  C already at 12
  All agree on 12 → MATCH
```

Each `seek` is O(log n) via binary search on the `SortedVec` data.
The total work is proportional to the output size times
log n, which is worst-case optimal for the AGM bound on join output.

### Usage in Pattern Matching

Each `Join` step in the query plan creates a `LeapfrogJoin` over
the relevant index iterators:

```
Join { target: n0, lookups: [ByOp(Add), ByChildPos(e3, 0)] }
```

This intersects `by_op[Add]` with `by_child_pos[(e3, 0)]`, yielding
Add nodes whose first child is in class e3. For each result, `n0` is
bound and execution continues to the next step.

---
[← Ch 6: Index Construction](06-index.md) · [Table of Contents](00-table-of-contents.md) · [Ch 8: Query Compilation →](08-query-compilation.md)
