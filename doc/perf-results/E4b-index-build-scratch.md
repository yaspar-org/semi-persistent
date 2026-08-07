<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E4b — index build allocations (A5) — **rejected, both halves**

A5 was two independent changes to `IndexStore::build_from`. Measured separately,
neither survives:

- **A5a — hoist the per-node `seen` scratch `Vec`.** No effect outside the noise
  band. Rejected.
- **A5b — build the maps as `SortedVec` and sort in place, so `finalize` stops
  rehashing every key.** A consistent 6-8% *regression* on the completion
  workload, reproduced outside criterion. Rejected.

This file is also the one that caught a measurement error affecting the rows
below — see "What criterion was reporting".

## A5a — hoist `seen`

`build_from`'s variadic branch allocated `let mut seen = Vec::new()` per node to
deduplicate that node's children. Hoisted above the loop and `clear()`ed per node.

Criterion, three runs against `E5-before` (= `3c19b48`), reported `ac6/naive`
−5.1%, `ac6/semi` −4.3%, `ac10/semi` −4.1%. The standalone site says otherwise:

| | baseline | A5a | A5a repeats | verdict |
|---|---|---|---|---|
| `ac6/naive`  |  2.619 ms |  2.628 ms | 2.607, 2.614, 2.625 | inside band |
| `ac6/semi`   |  1.352 ms |  1.329 ms | — | inside band |
| `ac10/naive` | 89.29 ms  | 88.03 ms  | 89.49, 88.40, 88.68 | inside band |

A5a's own spread is 2.607-2.628 ms on `ac6` (±0.4%) and 88.0-89.5 ms on `ac10`
(±0.8%). The baseline readings sit inside both. There is no effect to accept.

The mechanism agrees. `allocprobe`, baseline → A5a:

| workload | allocations before | after | removed |
|---|---|---|---|
| `plain7/naive` | 148 111 | 148 111 | 0 |
| `ac6/naive`    |  49 224 |  48 944 | 0.6% |
| `ac10/naive`   | 1 702 889 | 1 699 028 | 0.2% |

`plain7` removes *nothing*, because the branch is only taken for variadic nodes
and `plain7` has none — every node is `f/2`. On the AC rows it removes 0.2-0.6%.
A change that eliminates half a percent of allocations cannot produce 5%.

## A5b — build as `SortedVec`, sort in place

`finalize` consumed each `FastMap<K, Vec<G>>` with `into_iter().collect()` to
produce `FastMap<K, SortedVec<G>>` — rehashing every key to change the value
type. The change built the maps as the final type and sorted the buckets in
place through `values_mut()`, which needs a hand-written `Default` for
`SortedVec` (the derive would demand `G: Default`).

It works and it removes the rehash. It is also slower:

| | baseline | A5b | delta |
|---|---|---|---|
| `accompl64` standalone (`complsite`) | 4.766 ms | 5.151 ms | **+8.1%** |
| `accompl64` criterion | — | — | +5.7% |
| `accompl32` criterion | — | — | +2.6% |

Reproduced outside criterion, so it is not layout. It is also not explained by
anything the change touches, and three hypotheses were tested and eliminated:

1. **Load factor.** `into_iter().collect()` right-sizes the table; sorting in
   place leaves whatever incremental growth produced, and `schedule.rs` iterates
   `by_op` every round. Checked by printing `len()` against `capacity()` for all
   four maps after a build: load factors are *identical* between the two versions
   (`by_op` 60.7%, `by_repr` 71.2%, `by_child_pos` 59.8%, `by_contains` 58.9% at
   `accompl64`, and the same at `accompl32`), because `collect()` from a
   `HashMap` iterator uses its size hint and lands on the same capacity class.
   Eliminated.
2. **Allocation count.** A5b removes 4 allocations per build (the four
   `collect()` tables) — `accompl64` 7972 → 7968. Not a mechanism for 8%.
3. **Build cost.** `IndexStore::build` timed alone, min of 2000: `accompl64`
   70.4 µs baseline → **67.7 µs** under A5b. The changed code got 4% *faster*
   while the workload got 8% slower.

So the regression is downstream of the build, in code A5b does not modify — the
`SortedVec` value type is now written through a different path, which changes the
resulting `Vec`s' allocation addresses and hence the layout every later join
probe reads. That is a layout effect, but a *durable* one rather than a
run-to-run artifact: it reproduces across rebuilds and outside criterion.

Either way the accept/reject decision does not depend on explaining it. A5b's
upside was removing a rehash worth 4% of an operation that is not the
bottleneck, and its downside is a reproducible 8% on a shipped workload.

## What criterion was reporting

The AC rows moved −4% to −5% for A5a alone, −4% for A5b alone, and −4% for both
together. Three changes cannot each cause the same 4% and then not compound. What
they share is not code but the fact that a rebuild happened, and — the part
protocol item 6 did not previously cover — **a criterion delta on an AC row can
be an artifact of that size, not just the ±1% the README currently claims.**

E1's completion regression established the check for the completion path and
`examples/complsite.rs` as the tool. There was no equivalent for the AC-rewrite
path, which is why this went unnoticed until an experiment produced a win too
large for its mechanism. `examples/acsite.rs` is added here to close that gap:
same shape as `complsite`, for `ac_rules` at either width under either driver.

**E3's AC numbers were re-verified through it** rather than left standing on
criterion alone. They hold: `ac6/semi` 1.411 ms (pre-E3) → 1.342 ms (post-E3),
−4.9%, against a recorded criterion figure of −4.5 to −6.2%; `ac6/naive` −2.1%
against a recorded −0.9 to −1.4%. E3's mechanism argument (the semi-naive rows
gaining twice the naive rows) is what made it credible, and the standalone site
now confirms it independently. E1 and E2's accepted rows were confirmed by
allocation counts of 16-23%, orders of magnitude above this artifact.

## Correctness

Both halves passed `cargo test --workspace --release` (81 test binaries, 0
failures) before being timed. Neither is retained, so nothing here ships.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo run --release --example acsite               # ac6/naive
cargo run --release --example acsite -- 6 200 semi # ac6/semi
cargo run --release --example acsite -- 10 40      # ac10/naive
cargo run --release --example complsite            # accompl64
```
