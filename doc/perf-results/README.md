<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Performance experiments

One file per experiment: what was changed, what was measured, and whether it was
kept. A rejected experiment gets a file too — the number is the useful part, and
without it the next person re-runs the same idea.

## Method

Every experiment is measured on `egraph/benches/saturate_bench.rs` (end-to-end
saturation) unless its file says otherwise. Microbenchmarks decide only
questions that are genuinely local, and never on their own — a cursor that seeks
10% faster in isolation has to show up in a saturation number to count.

Protocol, in order:

1. **Correctness first.** `cargo test --workspace --release` green before any
   timing run. A faster wrong answer is not a result.
2. **Baseline the same bench ids you will compare**, via criterion's
   `--save-baseline`. Compare the *same id across two runs*, never two arms of
   one group: `containers-verus/doc/design/11-layout-parity.md` records the
   second-registered arm reading ~18% slow purely for being second.
3. **`MALLOC_MMAP_THRESHOLD_=65536`** exported for every run. Without it, an arm
   that runs after a large allocator churn inherits a fragmented `brk` heap and
   reads systematically slow; this collapses the spread to within 3.5%.
4. **At least three runs** before believing a delta. E0's first fat-LTO run
   disagreed with its next two by 3 points on one row and by 5 on another — a
   single run cannot distinguish a code effect from a layout effect.
5. **Confirm the mechanism, not just the time.** If the claim is "this removes
   allocations", `egraph/examples/allocprobe.rs` must show the count drop.
   Allocation counts are deterministic; wall-clock on this machine is not.
6. **Before attributing a delta to code, rule out layout.** Rebuilding
   *unchanged* source moves a row by up to ±1% here (measured in E1). Where a
   criterion delta is larger than that but the mechanism does not explain it —
   worst of all, where the row's work provably did not change — reproduce it in
   a standalone single-site binary (`egraph/examples/complsite.rs` is the one
   for the completion path) before recording it. E1's apparent 4% completion
   regression vanished at this step.

## Machine and toolchain

| | |
|---|---|
| toolchain | 1.94.0 (pinned in `rust-toolchain.toml`) |
| cores | 64 |
| CPU frequency governor | not exposed (no `cpufreq` sysfs); frequency is not pinnable here |
| load during runs | < 1.0 (1-minute average), no other user sessions |

The absent governor control is why the three-run rule matters more here than the
protocol in the plan assumed.

## Results

| exp | change | outcome |
|-----|--------|---------|
| [E0](E0-release-profile.md) | `[profile.release]`: `lto = "fat"`, `codegen-units = 1` | **accepted** — 6-9% end-to-end, zero code change |
| [E1](E1-join-cursor-allocation.md) | `SmallVec` cursor vector; allocation-free `LeapfrogJoin::new` | **accepted** — 2-6% on join-driven rows, 16-19% fewer allocations |
| [E2](E2-match-recycling.md) | `MatchPool`: recycle match buffers across queries instead of cloning nine `Vec`s per match | **accepted** — 22-33% on rewrite rows, 60% fewer bytes allocated |
