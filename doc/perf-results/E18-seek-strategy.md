<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E18 — seek strategy: galloping, bisection, stride-hinted galloping — **galloping held, hinting rejected**

**Verdict: galloping stays, unchanged. Bisecting the remaining run never wins
anywhere in the region the workloads occupy, and starting the gallop's ladder at
an estimated stride costs 0.4 to 1.4% end to end against its own control. Only
the instrumentation and the sweep land.**

E7 chose galloping over bisection and measured it on one hot 1M-element array.
Two things have changed since. The index buckets are contiguous spans in a
shared arena (R2, `19b4b8c`), which changes the constants a cache-resident
1M-element array reported. And a further question E7 did not ask has an O(1)
answer available at seek time: the expected advance distance is the ratio of the
two intersecting cursors' remaining lengths, so the ladder could start at that
estimate instead of at 1. Chapter 20 puts the leapfrog seek at 5.2% of the
profile after `790ba05`, which bounds what either answer can be worth. This
experiment measures both.

## What the seek costs, as a function of what

Galloping probes at offsets 1, 3, 7, ... from the cursor until it passes the
target, then bisects the window the last doubling bounded: about
`2·⌊log₂ d⌋ + 2` comparisons for an advance of *d*. Bisecting the remaining run
of *rem* keys costs `⌈log₂ rem⌉ + 1`. The two cross at `d² ≈ rem`. A
stride-hinted gallop that starts at exactly the right offset costs
`⌊log₂ d⌋ + 2`, which is the floor for any strategy in this family.

Which of the three is cheapest is therefore a property of the joint
distribution of *d* and *rem*, not of the algorithm, so the distribution was
measured first.

## The distribution

`leapfrog::seek_stats` records `(⌊log₂ d⌋, ⌊log₂ rem⌋)` for every seek the
push-based matcher issues, behind the `seek-stats` feature and `EGRAPH_SEEK=1`.
It wraps `ematch.rs`'s `cursor_of` and `cursor_in`, which are the only two places
that engine opens an index bucket. With the feature off the wrapper is a type
alias for `SortedVecCursor` and the call sites compile to the same code; the
measurement below confirms that.

Counts are exact and deterministic, so a single run per program suffices.

| program | seeks | *d* = 0 | *d* ≤ 1 | median log₂*d* | mean log₂*rem* |
|---|---|---|---|---|---|
| `math-microbenchmark.rules`, naive | 675 013 | 0.0% | 38.0% | 1 | 10.14 |
| `math-microbenchmark.rules`, semi-naive | 2 638 008 | 24.0% | 85.4% | 0 | 6.30 |
| `math-microbenchmark.native`, naive | 54 567 | 0.0% | 30.1% | 1 | 8.71 |
| `math-microbenchmark.native`, semi-naive | 658 520 | 33.7% | 95.2% | 0 | 9.61 |
| `math-add-ac.rules`, naive | 28 858 | 0.0% | 9.4% | 5 | 9.67 |
| `addac-n20.rules`, naive | 46 676 | 0.0% | 1.7% | 1 | 9.84 |

**The distribution is bimodal, and that is the finding that decides the
experiment.** Between 30% and 95% of seeks advance by at most one element, and
the rest spread almost flat from `2^2` out to `2^12`: on
`math-microbenchmark.rules` naive, every bucket from log₂*d* = 2 to 10 holds
between 3.2% and 5.5% of seeks. There is no concentration for a per-cursor
constant to sit on. The advance distance is not a quantity with a useful mean;
it is a spike at 0 plus a heavy flat tail.

The remaining run is large where the advance is small: mean log₂*rem* is 6.3 to
10.1, so a bisection would pay 7 to 11 comparisons to move one position. That is
the same reading E7 took, and it survives the move to arena spans.

Applying the three cost models above to these counts gives comparisons per seek:

| program | galloping | bisection | hinted, perfect estimate |
|---|---|---|---|
| `math-microbenchmark.rules`, naive | 7.99 | 12.14 | 5.00 |
| `math-microbenchmark.rules`, semi-naive | 3.09 | 6.78 | 2.43 |
| `math-microbenchmark.native`, naive | 8.28 | 10.71 | 5.14 |
| `math-microbenchmark.native`, semi-naive | 2.15 | 8.01 | 1.90 |
| `math-add-ac.rules`, naive | 11.61 | 11.67 | 6.80 |
| `addac-n20.rules`, naive | 8.08 | 11.84 | 5.04 |

Bisection loses on every program, by 0.5% on the closest and by 3.7x on the
furthest. A perfect stride estimate would remove 12% to 41% of the comparisons.
The rest of the experiment is about whether that 41% is reachable and whether
comparisons are what the time is made of.

## The crossover, measured on the arena layout

`benches/seek_microbench.rs::seek_strategy_sweep` prices the three searches
against each other over 32 MB of ids, seeking inside one bucket-sized span at a
time and cycling spans. That is the layout the index has: a seek's working set is
its span, and consecutive joins touch spans scattered through a pool far larger
than the last-level cache. Benchmarking on a single hot array instead hands
galloping a locality advantage it does not have in the engine, which is the
constant this comparison turns on.

Times are criterion medians for 4096 seeks, in µs. `hinted/exact` is an oracle:
its hint *is* the advance distance, so it bounds what any estimator can pay for.
`hinted/over` and `hinted/under` are the same oracle wrong by 8x in each
direction.

| span | *d* | galloping | bisection | hinted/exact | hinted/over | hinted/under |
|---|---|---|---|---|---|---|
| 64 | 1 | **7.90** | 83.99 | 7.98 | 57.66 | 8.17 |
| 64 | 4 | 52.84 | 88.04 | **47.01** | 81.14 | 52.96 |
| 64 | 16 | 78.04 | 90.49 | **71.23** | 92.03 | 76.80 |
| 1 024 | 1 | **7.80** | 123.65 | 7.90 | 53.02 | 8.08 |
| 1 024 | 4 | 51.30 | 135.28 | **45.20** | 73.99 | 51.76 |
| 1 024 | 16 | 78.01 | 139.25 | **71.15** | 110.28 | 76.35 |
| 1 024 | 64 | 107.60 | 152.84 | **97.29** | 144.90 | 101.97 |
| 1 024 | 256 | 165.52 | 217.85 | 226.16 | 218.52 | **143.73** |
| 16 384 | 1 | **7.50** | 187.78 | 7.48 | 48.05 | 7.59 |
| 16 384 | 4 | 41.34 | 176.62 | **35.76** | 73.19 | 41.51 |
| 16 384 | 16 | 70.64 | 183.64 | **67.71** | 108.29 | 71.59 |
| 16 384 | 64 | 107.49 | 209.23 | **97.26** | 142.11 | 101.97 |
| 16 384 | 256 | 139.58 | 354.90 | 200.34 | 179.50 | **130.48** |
| 16 384 | 1 024 | 395.18 | 408.86 | 531.91 | **346.59** | 420.49 |
| 262 144 | 1 | **7.47** | 241.09 | 7.50 | 47.94 | 7.32 |
| 262 144 | 4 | 41.38 | 244.42 | **35.43** | 73.03 | 41.35 |
| 262 144 | 16 | 72.28 | 248.31 | 68.24 | 99.11 | **65.82** |
| 262 144 | 64 | 107.36 | 323.28 | **97.19** | 166.95 | 101.84 |
| 262 144 | 256 | 160.63 | 427.50 | 191.15 | 191.52 | **131.70** |
| 262 144 | 1 024 | 411.09 | 752.20 | 552.39 | **302.81** | 405.48 |

**Bisection does not win a single point of this table.** Its best showing is
`span = 16 384, d = 1 024`, where it is 3.5% slower than galloping; at
`d ≤ 16` it is 1.16x to 32x slower. The workloads sit at `d ≤ 1` for 30% to 95%
of seeks and at `rem` between `2^6` and `2^16`, which is the region where
galloping wins by 10x to 32x. Chapter 7's claim that galloping is the right
default survives the arena layout with a wider margin than E7 recorded, because
a bisection over a span now misses in a pool that no longer fits in cache while
the ladder's first probes stay on the cursor's own cache line.

**The oracle hint is worth 9 to 14%, and only for `4 ≤ d ≤ 64`.** At `d ≥ 256`
it *loses* 19 to 44%, which is not what the comparison count predicts and is
worth stating because it constrains the whole family: with the hint equal to the
distance, the ladder stops on its first probe and hands the bisection a window of
width *d*, where plain galloping's ladder overshoots by at most 2x and hands it a
window of width *d*/2. The hinted search trades `log₂ d` sequential, prefetchable
ladder probes for one additional random-access bisection probe, and past
`d = 256` that trade is a loss. A stride hint can only pay in a band, and it pays
at most 14% inside it.

**Overestimating is 6.4x to 7.3x worse at `d = 1`.** That is the asymmetry that
settles the design: the penalty for a hint that is 8x too large falls exactly on
the case that is 30% to 95% of the workload, while the reward for a correct hint
is 14% in a band that holds a few percent of it.

## The estimator, measured rather than assumed

The remaining question is how accurate `n/m` would be. Rather than plumb the
plan-time ratio through the join, `seek_stats` records the *running mean advance
of the cursor itself*, which is the same quantity estimated online and strictly
better informed: `n/m` predicts that mean from two lengths, this observes it. If
the observed mean does not predict the next advance, no ratio rule does.

| program | \|error\| ≤ 1 octave | hint ≥ 8·*d* | hint ≤ *d*/8 | of the *d* ≤ 1 seeks, hint ≥ 8 |
|---|---|---|---|---|
| `math-microbenchmark.rules`, naive | 40.2% | 40.8% | 8.2% | 39.0% |
| `math-microbenchmark.rules`, semi-naive | 86.7% | 8.4% | 2.0% | 2.3% |
| `math-microbenchmark.native`, naive | 40.6% | 34.8% | 15.2% | 33.1% |
| `math-microbenchmark.native`, semi-naive | 94.3% | 3.6% | 1.5% | 2.3% |
| `math-add-ac.rules`, naive | 24.4% | 42.2% | 13.8% | 99.5% |
| `addac-n20.rules`, naive | 8.6% | 66.9% | 10.4% | 99.1% |

On the naive strategy, which is the shipped default, the estimator is within one
octave on 8.6% to 40.6% of seeks and overshoots by 8x or more on 34.8% to 66.9%.
Worse, the overshoot concentrates where it costs most: on
`math-microbenchmark.rules` naive, 39.0% of the `d ≤ 1` seeks would start their
ladder at 8 or beyond, so 14.8% of all seeks would pay the 6.4x to 7.3x penalty
the table above measures. The semi-naive numbers look accurate only because 85%
to 95% of their seeks do not move at all, and those return at the early check
whatever the hint is.

The bimodality is the cause. A per-cursor scalar can be 1 or it can be 256; the
distribution demands both.

## End to end

Two prototypes, both replacing the cursor with a local seek over the bucket
slice so the candidate could be measured without touching the verified one.
`local` is the production gallop transcribed, which isolates the cost of the
reimplementation and its bookkeeping from the cost of the hint; `hinted` is the
same code starting its ladder at the running mean. Neither is committed.
`math-microbenchmark`, both encodings, both strategies, medians of seven,
`MALLOC_MMAP_THRESHOLD_=65536`:

| program | base | local | hinted | hint vs local |
|---|---|---|---|---|
| rules, naive | 527.1 ms | 529.8 ms | 535.5 ms | **+1.08%** |
| rules, semi-naive | 551.1 ms | 560.4 ms | 568.1 ms | **+1.37%** |
| native, naive | 461.1 ms | 466.0 ms | 464.8 ms | −0.26% |
| native, semi-naive | 432.0 ms | 438.0 ms | 439.9 ms | +0.43% |

**The hint loses on three of the four configurations and is inside the spread on
the fourth.** That is what the comparison model and the crossover table
predicted, and the agreement is the reason to stop here rather than sweep hint
formulas: the estimator is wrong in the direction that costs 7x, on the case that
is most of the workload.

The instrumentation itself is free when its feature is off. Same protocol,
against the same base binary:

| program | base | branch, `seek-stats` off | change |
|---|---|---|---|
| rules, naive | 526.4 ms | 527.9 ms | +0.28% |
| rules, semi-naive | 551.9 ms | 550.2 ms | −0.31% |
| native, naive | 463.9 ms | 464.2 ms | +0.07% |
| native, semi-naive | 432.7 ms | 432.6 ms | −0.01% |

The `base` and `local` columns are worth reading too, with one confound stated:
the verified cursor is 0.51% to 1.68% faster than a local transcription of the
same algorithm, and the transcription also maintains the two counters the hint
needs, so the comparison charges the bookkeeping to the local side. It bounds
rather than isolates: whatever the verified seek costs against a hand-written
one, it is under 1.7%, and the sign is against the hand-written one.

## Conditions

The 32 programs under `comparison/` that print statistics produce identical
counts under all three binaries: nodes, classes, iterations, and match steps, on
both strategies, 64 comparisons. Seeks find the same elements whatever the
search, so this is the condition that catches a search that does not. The
programs were pinned from `f05787c` rather than read from the working tree,
because a concurrent session was editing `comparison/`.

`egraph/tests/seek_strategy.rs` checks the three searches against
`SortedVecCursor` itself: same landing position from every starting position, for
every target, at every hint from 1 to 64 and at three oversized hints including
`usize::MAX / 2`. The oversized case is the one an `n/m` estimator produces
whenever `m` is 1, and it is correct because the hint moves where the ladder
starts, not the invariant it maintains: `data[lo] < target`, established by the
early check.

`cargo test --release -p semi-persistent-egraph` passes with no failures, as do
the operator-restriction comparisons on the hub shape, the heterogeneous-shape
scheduling comparisons, and the adaptive-policy threshold, including the three
timing comparisons that run only under `--ignored`. `cargo clippy --release
--all-targets --all-features -- -D warnings` and `cargo fmt --all --check` are
clean on every file this experiment touches; both flag `tests/au_deceptive.rs`,
which does so at `f05787c` as well and is a concurrent session's file.

All three were run against a copy of the tree with the concurrent session's
in-flight changes reset to `f05787c`, because that session's `au/census.rs` did
not compile while this was measured. Everything reported here is therefore this
change against `f05787c`, with no other working-tree edit in it.

## What would revive stride hinting

A workload measured to have a *unimodal* advance-distance distribution, with the
mass between `d = 4` and `d = 64` where the oracle pays 9 to 14%. That is the
band, and the crossover table gives its edges. None of the six programs
instrumented here is that shape. Four put 30% to 95% of seeks at `d ≤ 1` and
spread the rest almost flat to `2^12`; `addac-n20.rules` naive concentrates 64.5%
at `d ∈ {2, 3}` but still sends 22% past `d = 64`; `math-add-ac.rules` naive is
flat from `d = 1` to `2^9` with no bucket above 16%. A single scalar cannot serve
a distribution with mass at both ends, which is what the estimator table
measures.

A second opening, narrower: at `d ≥ 1024` a hint pays even when it is 8x too
large (`hinted/over` is 0.74x to 0.88x galloping there), because one probe at
offset 8192 plus a bisection of that window is shorter than eleven doublings and
a bisection of the last one. A rule that raised the ladder's start only for
cursors already observed to be making long advances would land there. It is not worth building against a distribution
where `d ≥ 1024` is under 2% of seeks, but it is the shape of the rule that would
work if one appeared.

Bisection needs no revival condition: it lost every point of the crossover table.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
# the distribution
cargo build --release --features seek-stats
EGRAPH_SEEK=1 ../target/release/semi-persistent \
  ../comparison/math-microbenchmark.rules.egg --types machine --use-naive \
  | grep '^SEEK_'
# the crossover table
cargo bench --bench seek_microbench -- seek_strategy
# the correctness conditions
cargo test --release --test seek_strategy
```
