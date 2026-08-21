# Chapter 7 — Leapfrog Triejoin

[← Ch 6: Index Construction](06-index.md) · [Table of Contents](00-table-of-contents.md) · [Ch 8: Query Compilation →](08-query-compilation.md)


## The Join Problem

Pattern matching in an e-graph is a multi-way join. The pattern
`(f (g x) (h x))` produces three constraints:

1. `by_op(f)`: all f-nodes
2. `by_child_pos(class_of_g_node, 0)`: parents with this child at pos 0
3. `by_child_pos(class_of_h_node, 1)`: parents with this child at pos 1

The answer is the intersection of these sorted sets. A naive nested
loop can be O(n²) for a 2-way join. The leapfrog step computes a
one-dimensional sorted intersection with monotone seeks. This is the
worst-case-optimal intersection primitive used by the matcher; the full query
also includes scheduling, e-class re-joins, variadic decomposition, guards, and
backtracking, so this chapter does not assign the whole matcher the AGM bound.

## The Algorithm

Leapfrog maintains a vector of sorted iterators (cursors), all
seeking to agree on the same key.

```rust
pub struct LeapfrogJoin<C: SortedCursor> {
    iters: CursorVec<C>,  // SmallVec<[C; 4]>
    p: usize,
    at_end: bool,
}
```

Generic over the cursor, not tied to `SortedVec`: the same join drives a
`SortedVecCursor`, a `BPlusCursor`, or a `Difference` combinator.

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

Each `seek` **gallops**: it doubles an offset from the cursor's current position
until it lands on or past the target, then bisects the bounded window that
doubling produced. Cost is O(log(*d* + 1)) in the distance actually advanced
rather than O(log *n*) in the list length, with the
zero-distance/current-key case handled directly. Total work also depends on
failed candidate alignments and cursor advancement, not only on output size.
Galloping changes the seek cost; it does not turn the surrounding
decomposition/backtracking engine into a worst-case-optimal general join.

Alternatives include full bisection and beginning the gallop at an estimated
stride derived from remaining cursor lengths. The implementation currently
starts at one. Relative performance depends on bucket lengths and the advance
distribution; it is a benchmark question, not a correctness property. Current
comparisons must use the maintained Criterion benchmark and its confidence
intervals rather than the historical point estimates formerly recorded here.

The seek is verified, and it is the verified code that runs: `index.rs`
re-exports `containers-verus`'s `SortedVecCursor` rather than defining one, so
the proof (it lands on the first key ≥ the target and skips no present key, for
every list and every target) covers what ships. Re-exporting the verified cursor
does not itself establish a performance result; use the conformance Criterion
benchmark for that
([containers-verus Ch. 12](../../../containers-verus/doc/design/12-sorted-vec-cursor.md) §7a).
`SortedCursor for SortedVecCursor` is therefore implemented in that crate, not
here; `leapfrog.rs` carries no cursor impl of its own.

### Measuring the seek distribution

`leapfrog::seek_stats` records, for every seek the push-based matcher issues, the
distance it advanced against the run remaining in front of it. It is behind the
`seek-stats` feature and prints under `EGRAPH_SEEK=1`; with the feature off its
cursor wrapper is a type alias for `SortedVecCursor`, so the statistics wrapper
is absent from that path. The two histograms record distance and remaining
length; they support, but do not replace, end-to-end Criterion measurements of
candidate search policies.

### Usage in Pattern Matching

Each `Join` step in the query plan creates a `LeapfrogJoin` over
the relevant index iterators:

```
Join { target: n0, lookups: [ByOp(Add), ByChildPos(e3, 0)] }
```

This intersects `by_op[Add]` with `by_child_pos[(e3, 0)]`, yielding
Add nodes whose first child is in class e3. For each result, `n0` is
bound and execution continues to the next step.

## The `Difference` Combinator

`LeapfrogJoin` is generic over any `SortedCursor`. Semi-naive
evaluation (Chapter 18) exploits this with `Difference<A, B>`, a
two-cursor combinator that is *itself* a `SortedCursor`: it yields the
keys of `A` (a full-index cursor) that are absent from `B` (the
delta-index cursor), i.e. `full ∖ delta`. Because it satisfies the
same monotonic-forward seek contract, it drops into a `LeapfrogJoin`
anywhere a base cursor would, with no change to the join algorithm.

---
[← Ch 6: Index Construction](06-index.md) · [Table of Contents](00-table-of-contents.md) · [Ch 8: Query Compilation →](08-query-compilation.md)
