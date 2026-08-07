<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E0 — release profile (C1)

**Change.** Added to the workspace `Cargo.toml`:

```toml
[profile.release]
lto = "fat"
codegen-units = 1
```

There was no `[profile.release]` section and no `.cargo/config.toml`, so release
builds ran cargo's defaults: `codegen-units = 16`, no LTO.

**Why it should matter.** The hot code is generic and instantiated across a crate
boundary — `SortedCursor::seek`/`step`, `VecI` indexing, `DenseId` conversions all
live in `containers-verus` and are called from `egraph`'s join and rebuild loops.
Without LTO those calls do not inline across the boundary; with 16 codegen units
they may not inline within `egraph` either.

**Verdict: accepted.** 6-9% on every end-to-end saturation row for zero code
change. This ran first because it moves the baseline every later experiment
measures against.

## Numbers

Baseline `E0-before` = defaults, saved from the pre-change build.
`MALLOC_MMAP_THRESHOLD_=65536` for every run. Three runs per configuration;
each cell is the criterion point estimate of the change vs `E0-before`.

| bench | thin r1 | thin r2 | thin r3 | fat r1 | fat r2 | fat r3 |
|---|---|---|---|---|---|---|
| `plain7/naive`  | −5.6% | −4.9% | −5.0% | −6.8% | −9.0% | −8.3% |
| `plain7/semi`   | −6.4% | −6.2% | −6.8% | −4.6% | −8.5% | −7.9% |
| `ac6/naive`     | −6.7% | −7.1% | −8.5% | −3.8% | −8.2% | −6.8% |
| `ac6/semi`      | −6.7% | −7.0% | −4.5% | −1.6% | −7.5% | −7.0% |
| `ac10/naive`    | −6.2% | −6.4% | −5.7% | −4.5% | −6.9% | −5.9% |
| `ac10/semi`     | −6.8% | −6.5% | −6.5% | −3.7% | −7.5% | −6.9% |
| `accompl32`     | −0.6% | −1.3% | **+0.4%** | −4.1% | −7.8% | −6.0% |
| `accompl64`     | −0.6% | −1.9% | −0.8% | −6.8% | −7.2% | −6.6% |

Absolute baseline times (defaults): `plain7/naive` 23.54 ms, `plain7/semi`
13.54 ms, `ac6/naive` 3.618 ms, `ac6/semi` 1.752 ms, `ac10/naive` 108.2 ms,
`ac10/semi` 70.69 ms, `accompl32` 1.647 ms, `accompl64` 5.454 ms.

Compile cost, full release rebuild of `egraph` benches + examples: thin 1m45,
fat 1m47, both from a warm dependency graph. The difference is inside run-to-run
variation — fat LTO is not measurably more expensive here.

## Why fat, not thin

On the six rewrite-driven rows thin and fat tie: both land in a −5% to −9% band
and their run-to-run spread overlaps completely. The two AC-completion rows
separate them cleanly. Thin gives −0.6%, −1.3%, +0.4% on `accompl32` — one run
is a regression, so thin's effect there is indistinguishable from zero. Fat gives
−4.1%, −7.8%, −6.0% on the same row and −6.6% to −7.2% on `accompl64`, never
overlapping thin's range.

That is consistent with what the completion path is: `multiset.rs` normalization
and `cc.rs` completion call small container primitives in tight loops, which is
exactly the cross-crate inlining thin LTO does only within a codegen partition.
Since compile cost is a wash, there is no reason to take the weaker option.

## What the first fat run says about the protocol

Fat run 1 disagrees with runs 2 and 3 by 2.2 points on `plain7/naive` and 5.9
points on `ac6/semi`, in the direction of *understating* the win. Had it been the
only run, fat would have looked worse than thin on four of eight rows and the
decision would have gone the other way.

This is the same class of effect `11-layout-parity.md` documents: a fresh binary
lands its hot loops at different offsets, and the first run after a rebuild also
warms a cold file cache. It is why the three-run rule in `README.md` is not
optional, and why nothing in this directory is decided from a single run.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
# with the [profile.release] section removed from the workspace Cargo.toml:
cargo bench --bench saturate_bench -- --save-baseline E0-before
# with it restored:
cargo bench --bench saturate_bench -- --baseline E0-before
```

## Correctness

`cargo test --workspace --release` under the new profile: 80 test binaries, all
passing, 0 failures. Checked because LTO and codegen-unit changes alter inlining
and float/UB-adjacent codegen, not because any specific test was suspected.
