# Chapter 7 — Leapfrog Triejoin

[← Ch 6: Index Construction](06-index.md) · [Table of Contents](00-table-of-contents.md) · [Ch 8: Query Compilation →](08-query-compilation.md)


## The Join Problem

Pattern matching in an e-graph is a multi-way join. The pattern
`(f (g x) (h x))` produces three constraints:

1. `by_op(f)`: all f-nodes
2. `by_child_pos(class_of_g_node, 0)`: parents with this child at pos 0
3. `by_child_pos(class_of_h_node, 1)`: parents with this child at pos 1

The answer is the intersection of these sorted sets. A naive nested
loop is O(n²) for a 2-way join. Leapfrog triejoin computes the
intersection in worst-case optimal time.

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
doubling produced. Cost is O(log *d*) in the distance actually advanced rather
than O(log *n*) in the list length, and since *d* ≤ *n* it is never
asymptotically worse. That matters because leapfrog's seeks are overwhelmingly
short (a majority advance by at most one element), so a full binary search
paid 5-8 probes to move one position
(`doc/perf-results/E7-galloping-seek.md`). The total work is proportional to the
output size times log *n*, which is worst-case optimal for the AGM bound on join
output; galloping improves the constant, not that bound.

That choice was re-measured on the index's arena layout, together
with the one alternative the join has enough information to compute: starting the
ladder at an estimated stride rather than at 1, since the expected advance
distance is the ratio of the two intersecting cursors' remaining lengths and is
available in O(1) at seek time. Both alternatives lose
(`doc/perf-results/E18-seek-strategy.md`). Bisection does not win a single point
of a sweep over bucket-sized spans, from 64 to 262 144 keys and advance distances
1 to 1024; its best showing is 3.5% behind galloping and its worst is 32x behind.
A perfect stride estimate would be worth 9 to 14%, but only for advances between
4 and 64, and it *loses* 19 to 44% past 256, because the hinted ladder stops on
its first probe and hands the bisection a window twice as wide as the one plain
doubling produces. An estimate 8x too large costs 6.4x at *d* = 1, which is where
30% to 95% of seeks are. The measured advance distribution is bimodal, so no
per-cursor scalar can serve it, and a prototype starting the ladder at the
cursor's running mean advance ran 0.4 to 1.4% slower end to end than its own
control.

The seek is verified, and it is the verified code that runs: `index.rs`
re-exports `containers-verus`'s `SortedVecCursor` rather than defining one, so
the proof (it lands on the first key ≥ the target and skips no present key, for
every list and every target) covers what ships. Re-exporting the verified cursor
is performance-neutral end-to-end
([containers-verus Ch. 12](../../../containers-verus/doc/design/12-sorted-vec-cursor.md) §7a).
`SortedCursor for SortedVecCursor` is therefore implemented in that crate, not
here; `leapfrog.rs` carries no cursor impl of its own.

### Measuring the seek distribution

`leapfrog::seek_stats` records, for every seek the push-based matcher issues, the
distance it advanced against the run remaining in front of it. It is behind the
`seek-stats` feature and prints under `EGRAPH_SEEK=1`; with the feature off its
cursor wrapper is a type alias for `SortedVecCursor`, so nothing is added to the
shipped path (measured at −0.31% to +0.28% on `math-microbenchmark`, both
encodings, both strategies). The two histograms it keeps are enough to price any
search whose cost is a function of the distance and the remaining length, which
is what settled the comparison above without a run per candidate.

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
