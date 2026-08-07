<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E7 — galloping seek in `SortedVecCursor` (B2) — **accepted**

**Verdict: accepted. 4-6% end-to-end on the join-heavy rows, 70-97% on the seek
itself, and no shape regresses — including the two designed to break it.**

`SortedVecCursor::seek` ran `partition_point` over the whole remaining slice. It
now gallops: double an offset from the cursor until it lands on or past the
target, then bisect the bounded window. Cost goes from O(log *rem*) to
O(log *d*) in the distance actually advanced.

## The premise, measured first

B2's payoff depends entirely on the stride distribution, so that was instrumented
before any code was written — a temporary histogram in `seek` over the real
saturation workloads:

| workload | seeks | *d* = 0 | *d* ≤ 1 | *d* ≤ 3 | median log₂*d* | mean log₂(remaining) |
|---|---|---|---|---|---|---|
| `plain7/naive` |  55 721 |  0.0% |  7.9% | 20.6% | 7 | 11.0 |
| `plain7/semi`  |  50 871 | 30.6% | 43.3% | 50.4% | 2 |  9.2 |
| `ac6/naive`    |  15 369 |  0.0% | 56.4% | 83.8% | 1 |  4.7 |
| `ac6/semi`     |   8 341 | 24.7% | 67.2% | 86.0% | 1 |  3.0 |
| `ac10/naive`   | 333 921 |  0.0% | 64.9% | 85.1% | 1 |  7.9 |
| `ac10/semi`    | 218 602 |  0.5% | 64.8% | 86.2% | 1 |  7.1 |

Two things fall out. **The strides are short** — on the AC rows a majority of
seeks advance by at most one element and ~85% by at most three, while the slice
being searched averages 2^4.7 to 2^7.9 elements, so binary search was paying 5-8
probes to move one position. And **a quarter to a third of semi-naive seeks do not
move at all** (*d* = 0), because the `Difference` combinator seeks both sides to
the same key; those now cost a single compare and an early return.

`plain7/naive` is the exception with median log₂*d* = 7, and it is the row that
gains least below — consistent, and the reason the sweep in the next section
matters.

Note the plan's framing ("full-slice `partition_point` per seek") was already half
addressed: the old code sliced from `self.pos` first, so it was O(log *rem*), not
O(log *n*). The remaining gap is *rem* vs *d*, which is what this closes.

## Stride sweep — the acceptance condition

E7's condition was that short strides improve **without long jumps regressing past
the random baseline**. `benches/seek_microbench.rs` only drives stride-1 seeks, so
`seek_stride_sweep` was added to it: a 1M-key set, 4096 seeks per row, fixed
strides plus a uniform-random reference and an adversarial short-step/long-jump
alternation.

| shape | binary search | galloping | change |
|---|---|---|---|
| `stride/1`    | 213.1 µs |   6.6 µs | **−96.9%** |
| `stride/4`    | 214.0 µs |  39.4 µs | **−81.6%** |
| `stride/16`   | 220.1 µs |  64.2 µs | **−70.8%** |
| `stride/64`   | 372.4 µs |  87.3 µs | **−76.6%** |
| `stride/256`  | 722.8 µs | 177.5 µs | **−75.4%** |
| `stride/1024` | 228.0 µs |  61.5 µs | **−73.0%** |
| `random`      | 665.3 µs | 197.6 µs | **−70.3%** |
| `adversarial` | 583.5 µs |  99.7 µs | **−82.9%** |

The condition is met with room to spare: **nothing regresses, and the two shapes
that were supposed to expose the downside improve by 70% and 83%.**

That is a stronger result than the plan expected, and the mechanism is why the
`adversarial` row was included as a check rather than assumed: a gallop overshoots
its target by at most a factor of two, so the bisection that follows searches a
window no wider than the distance covered. A long jump therefore costs
2·log *d* rather than log *rem*, and since *d* ≤ *rem* always, the gallop is never
asymptotically worse — it can only lose by a constant, and here it does not lose
at all because the ladder's early probes are sequential and cache-friendly where
binary search's first probes are not.

The original `seek_microbench` rows (all stride-1, against `E7-before`):
−93.0% at n = 1k, −95.8% at 100k, −96.5% at 1M. The gain grows with n, as it
should: binary search's cost grows with the slice and galloping's does not.

## End-to-end numbers

`saturate_bench` against `E7-before` (= `2bbf57b`), three runs:

| bench | change | absolute after |
|---|---|---|
| `saturate/plain7/naive` | −2.3% to +0.4% | 13.2 ms |
| `saturate/plain7/semi`  | **−3.9 to −4.2%** |  7.4 ms |
| `saturate/ac6/naive`    | **−2.0 to −2.5%** |  2.37 ms |
| `saturate/ac6/semi`     | −0.8 to −1.2% |  1.25 ms |
| `saturate/ac10/naive`   | **−4.3 to −4.7%** | 78.2 ms |
| `saturate/ac10/semi`    | **−3.9 to −4.6%** | 50.0 ms |
| `saturate/accompl32`    | −1.1% to +2.3% | 1.49 ms |
| `saturate/accompl64`    | +0.3% to +2.8% | 4.95 ms |

The row-by-row pattern tracks the histogram, which is what makes this credible
rather than coincidental: `ac10` has the most seeks (334k) and the shortest strides
and gains most; `plain7/naive` has median log₂*d* = 7 and gains nothing; `plain7/semi`
has 30.6% zero-distance seeks and gains 4%.

Standalone confirmation per protocol item 7, min of 40/200 reps:

| | baseline | galloping | |
|---|---|---|---|
| `ac10/naive` | 79.8004 ms | 75.0903 ms | **−5.9%** |
| `ac6/semi`   |  1.2109 ms |  1.1953 ms | −1.3% |
| `accompl64`  |  4.7259 ms |  4.7310 ms | +0.1% |
| `accompl32`  |  1.4435 ms |  1.4383 ms | −0.4% |

**The completion rows' criterion +2 to +2.8% is an artifact.** Standalone they are
flat (+0.1%, −0.4%) — the same pattern E6 hit on the same two rows, and the reason
protocol item 7 exists. Checksums are identical throughout (`ac10` 41920, `ac6`
17400, `accompl64` 127200, `accompl32` 63200).

## Correctness

`cargo test --workspace --release`: 81 test binaries, 0 failures. `cargo fmt --all
--check` and `cargo clippy --release --all-targets` clean.

`seek` already had direct coverage — `leapfrog::tests::difference::basic_seek` and
`seek_matches_filter` (a proptest comparing seek against a filter), plus
`index::tests::seek_and_step` — and the whole join layer sits on top of it, so
582 lib tests exercise it indirectly. Mutation-checked to confirm that coverage
actually gates the new code:

| mutation | result |
|---|---|
| gallop condition `<` → `<=` | **29 tests fail** |
| `hi = lo + step` → `lo + step / 2` | **48 tests fail** |
| early-return guard `<` → `<=` | **9 tests fail** |

One rewrite that looked like an off-by-one — bisecting `data[lo..hi]` instead of
`data[lo + 1..hi]` — left every test passing, and that is correct rather than a
coverage gap: `data[lo] < target` holds by the loop invariant, so
`partition_point` over the wider window returns at least 1 and both forms give the
same index. The shipped form is the narrower one because it makes the invariant
visible at the call.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench seek_microbench -- --save-baseline E7-before   # at 2bbf57b
cargo bench --bench saturate_bench  -- --save-baseline E7-before
# apply the change, then
cargo bench --bench seek_microbench -- --baseline E7-before
cargo bench --bench saturate_bench  -- --baseline E7-before
cargo run --release --example acsite -- 10 40
cargo run --release --example complsite
```
