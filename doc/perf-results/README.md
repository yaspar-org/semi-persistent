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
7. **A win too large for its mechanism is a measurement error.** E4b's two halves
   each read −4 to −5% on the AC rows in criterion, and so did both together —
   three changes cannot each cause the same 4% and then fail to compound. The
   standalone site put all three inside the noise band. The rule that follows:
   before recording an AC-row delta, reproduce it through
   `egraph/examples/acsite.rs`, and check the delta against what the mechanism
   can pay for (an allocation count, a probe count). E1/E2's accepted rows had
   16-23% allocation reductions behind them; E4b's had 0.2%.
8. **A dense table is not automatically cheaper than a map.** E4a replaced maps
   with `Vec`s indexed by class id and gained 22-29%; E11b did the same thing for
   a table of `Term` and lost 31-75%, because `vec![None; n]` of a large non-`Copy`
   type allocates, zeroes and drop-scans every slot even when almost none are
   written. The dense form wins when slots are word-sized and densely written, and
   an initially-empty map wins when they are large and sparse. Which one applies is
   a measurement, not an inference from E4a.

9. **Decompose the cost before accepting the stated mechanism.** A plan names the
   mechanism it noticed, which need not be the one that dominates. C4 was written
   up as "the rule scan restarts from index 0 after every rewrite"; splitting the
   count showed restarts were 23% of the tests and the final *failing* scan was
   77%, so the proposed fix addressed the minority — and was unsound anyway.
   Indexing, which shrinks every scan instead of skipping some, took 30-47%.
   Before implementing a stated fix, count the sub-parts of the thing it targets;
   if the fix does not address the largest, look for the one that does.

10. **Confirm the site is on the path before optimizing it, and confirm the
    counter fires before trusting a zero.** A7 named the AC decompose *frames*,
    which sit in a second matcher engine (`MatchIterator`) that nothing outside
    `ematch.rs`'s own tests constructs — real code, zero executions in any
    benchmark. The cost was one level away, in the recursive engine everything
    actually uses. Symmetrically, a probe that reads zero is only evidence once
    it has been shown to be capable of reading non-zero: the first two zeros here
    were an atomic read from the wrong test binary and a reporter that ran before
    the tests it summarized. Drive the site deliberately, see the counter move,
    *then* believe the zeros.

`examples/` holds the standalone sites protocol items 6 and 7 require:
`complsite.rs` (completion), `acsite.rs` (AC rewrite, either width and driver),
`allocprobe.rs` (allocation counts), `extractprobe.rs` (extraction structure and
fixpoint pass counts).

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
| [E3](E3-index-hasher.md) | foldhash instead of SipHash for the dense-id index maps | **accepted** — 4.5-10%, twice the gain on semi-naive as on naive; AC rows re-verified standalone |
| [E4a](E4-extract-dense-tables.md) | dense-id `Vec`s instead of maps for the extraction cost tables | **accepted** — 22-29% where the fixpoint dominates; DAG rows unaffected (they are 99.97% `reconstruct`) |
| [E4b](E4b-index-build-scratch.md) | hoist `build_from`'s scratch `Vec`; stop `finalize` rehashing every key | **rejected, both halves** — the hoist is inside the noise band (0.2% of allocations); the in-place `finalize` regresses completion 8% |
| [E7](E7-galloping-seek.md) | galloping instead of full-remainder binary search in `SortedVecCursor::seek` | **accepted** — 4-6% end-to-end, 70-97% on the seek, no shape regresses |
| [E6](E6-rhs-instantiation-allocation.md) | `SmallVec` child and prim-arg lists in `apply::eval`, inline capacity swept | **accepted** — 5-11% on every rewrite row, 37-82% fewer allocations |
| [E11a](E11a-reconstruct-redundant-clone.md) | `reconstruct` deep-cloned each child term then dropped the original | **accepted** — 91-98% on every extraction row; removes an O(depth²) term |
| [E11b](E11b-reconstruct-memo.md) | memoize `reconstruct` per class, so a shared class is built once | **rejected** — a memo hit still deep-copies the subterm, so it trades a graph walk for a copy of the same size; 4 variants, all regress the tree rows |
| [E13](E13-rule-lhs-index.md) | index the AC rule table by LHS-minimum class, so a normalize step tests only the rules a present class could match | **accepted** — 30-47% on the completion rows, 80-85% fewer subset tests, both rising with problem size |
| [E14](E14-decompose-child-buffers.md) | recycle the `ExpandA`/`DecomposeAC`/`DecomposeACI` child buffers through `MatchPool` instead of allocating one per match step | **accepted** — 13.5% on `ac10`, 6-7% on `ac6`, 30-41% fewer allocations; the site A7 actually named is dead code |
| [E8](E8-union-find-compression.md) | path-compression policy: on-the-fly vs systematic sweep vs threshold | **closed on its gate** — mean hops 0.000-0.433, deepest chain 2; nothing to compress |
| [E5](E5-bplus-search-kind.md) | `Branchless` as the B+tree search default | **closed** — `BPlusTreeSet` is not instantiated outside benches; the sweep splits on node size anyway |
| [E12](E12-worklist-fixpoint.md) | worklist instead of full rescan in the extraction fixpoint | **closed unimplemented** — the fixpoint converges in 2 passes on every workload |
