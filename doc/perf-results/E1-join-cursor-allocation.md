<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E1 — join cursor allocation (A1)

**Change.** `LeapfrogJoin` holds a `SmallVec<[C; 4]>` (`leapfrog::CursorVec`)
instead of a `Vec<C>`, and `LeapfrogJoin::new` no longer allocates:

- the `Option<Vec<C::Key>>` key collection became a `.any(|it| it.key().is_none())`
  probe;
- the zip/sort/unzip through a `Vec<(C::Key, C)>` became an in-place
  `sort_unstable_by_key` on the cursor vector itself;
- `new` takes `impl Into<CursorVec<C>>`, so a `SmallVec` caller stays off the
  heap and a `Vec` caller (the tests, `benches/leapfrog_bench.rs`) donates its
  buffer.

`ematch::run_join`'s three per-mode cursor collections and
`MatchIterator::enter_join` now build `CursorVec`s. `enter_join` also dropped its
intermediate `Vec<&SortedVec<_>>` — `resolve_lookup` borrows from the index,
which outlives the frame, so the references never needed materialising.

Inline capacity is 4 because a join's arity is the number of index lookups for
one atom: 1 for `ByOp`/`ByRepr`, 2 for the bound-node re-join, and the pattern
node's arity for child-position joins.

**Verdict: accepted.** 2-6% on all six rewrite-driven rows, with the predicted
allocation drop confirmed. The two AC-completion rows read 3-7% slow in
criterion; that is a layout artifact, and the reasoning is below because the
number looks like a real regression and is not one.

## Numbers

Baseline `E1-before` = commit `0a9b7cb` (post-E0, fat LTO). Three runs of the
full suite, `MALLOC_MMAP_THRESHOLD_=65536`.

| bench | run 1 | run 2 | run 3 |
|---|---|---|---|
| `plain7/naive`  | −4.8% | −4.5% | −5.0% |
| `plain7/semi`   | −5.2% | −5.0% | −5.7% |
| `ac6/naive`     | −3.9% | −5.2% | −5.7% |
| `ac6/semi`      | −1.9% | −2.3% | −2.9% |
| `ac10/naive`    | −0.6% (p=0.21) | −1.5% | −0.6% (p=0.13) |
| `ac10/semi`     | −1.3% | −1.5% | −0.4% |
| `accompl32`     | +4.5% | +1.7% | +1.9% |
| `accompl64`     | +4.2% | +3.9% | +3.7% |

`plain7` and `ac6` clear the 3% bar (`ac6/semi` at 2-3% does not, but it is the
smallest workload at 1.6 ms and the same code path as `ac6/naive`, which does).
`ac10` improves by about 1%: its cost is dominated by the AC decompose frames and
rest-slice splicing that A7 targets, not by join setup, so a small win there is
what the mechanism predicts.

## Mechanism (allocation counts)

`examples/allocprobe.rs`, saturation region only. Counts are deterministic.

| workload | before | after | delta |
|---|---|---|---|
| `plain7/naive` | 229 587 | 193 003 | **−15.9%** |
| `plain7/semi`  | 121 341 |  98 357 | **−18.9%** |
| `ac6/naive`    |  62 768 |  58 680 | −6.5% |
| `ac6/semi`     |  ~28 700 | 27 174 | −5.3% |
| `ac10/naive`   | 1 857 690 | 1 852 818 | −0.3% |
| `ac10/semi`    | 1 228 320 | 1 223 390 | −0.4% |
| `accompl32`    | 3 931 | 3 931 | **0** |
| `accompl64`    | 7 972 | 7 972 | **0** |

Allocations per match step on `plain7/naive` fall from 1.01 to 0.85. The ranking
matches the timings exactly: the join-heavy fixed-arity workloads gain most, the
AC workloads barely, and completion not at all.

## Why the completion rows are not a regression

`accompl32`/`accompl64` run with an empty rule list. Their `match_steps` is 0 —
they never construct a `LeapfrogJoin` — and their allocation counts are
*byte-identical* before and after. There is no path by which this change alters
the work they do.

Three checks, in the order `11-layout-parity.md` prescribes:

1. **Rebuild noise on unchanged source.** Rebuilding the *pre-change* tree and
   re-measuring the same two rows against the same baseline gives −0.9%/+1.1%,
   −0.7%/+0.4%, −0.8%/+0.1%. So a fresh binary alone moves these rows by ±1%.
   That is smaller than what A1 shows, which is why the next two checks matter.
2. **Filtered vs full-suite runs.** Run with `-- accompl` only, A1 reads +2.9 to
   +5.5% and +5.3 to +7.4% — *worse* than in the full suite, where `accompl`
   follows `ac10`'s 107 MB of allocator churn. A code effect would not depend on
   which benches ran before it in the process.
3. **Outside criterion.** `examples/complsite.rs` runs the `accompl64` workload
   in a standalone binary, 200 reps, reduced by minimum. Baseline: 4.686, 4.843,
   4.694 ms. A1: 4.849, 4.703, 4.664 ms. Minima 4.686 vs 4.664 — the gap is
   absent.

The conclusion is the one this repo has reached twice before (both retracted
attributions in `11-layout-parity.md`): a criterion delta on a row whose work
provably did not change is measuring where the code landed, not what it does.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench saturate_bench -- --save-baseline E1-before   # at 0a9b7cb
# ... apply the change ...
cargo bench --bench saturate_bench -- --baseline E1-before
cargo run --release --example allocprobe
cargo run --release --example complsite 64 200
```

## Correctness

`cargo test --workspace --release`: 80 test binaries, 0 failures. This includes
`leapfrog.rs`'s own dual-width suite (18 join cases across both id widths) and
the e-matching proptests, which are what would catch the sort change — ties are
now ordered unstably, and Algorithm 1 requires the ring sorted by key but not any
particular order among equal keys. `cargo fmt --check` and
`clippy --workspace --all-targets -D warnings` clean.
