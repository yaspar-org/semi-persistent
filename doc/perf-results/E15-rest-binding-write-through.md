<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E15: write rest bindings through to the match pools (D1): **accepted**

**Verdict: accepted. −21.5% / −17.5% on ac10, −12.5% / −9.6% on ac6,
reproducing within 0.5 points across two comparison runs; 42% fewer
allocations on ac10 with identical node counts on every workload.**

At every leaf of the AC assignment search that carries a rest variable, the
recursive matcher built the residual binding as a fresh `Vec` (a
zero-size-hint `collect` through a filter, so a 4/8/16 growth walk at the
measured mean residual of 9.9) and passed it to `push_mset`, which copied it
into `Match::mset_pool`, the destination it could have been written to
directly. `doc/perf-dps.md` (D1) sized the site at 221 388 bindings per
allocprobe run, one level below the child buffers E14 recycled.

The change is two methods and two call sites: `Match::push_mset_residual`
filters the residual straight onto the pool tail and records the span from
the tail length; `push_set_residual` is the ACI counterpart (zero executions on
these workloads, fixed for symmetry). The temporary, its growth walk, and
the copy are gone; a warm pool makes the binding allocation-free.

## Numbers

`saturate_bench`, criterion baseline `pre-e15`, two comparison runs:

| benchmark | change (mid, run 1 / run 2) |
|---|---|
| ac10/naive | −21.5% / −21.4% |
| ac10/semi | −17.5% / −17.5% |
| ac6/naive | −12.1% / −12.5% |
| ac6/semi | −9.6% / −9.6% |
| accompl32 / accompl64 | −2.3% / −1.6% and −1.6% / −1.2% |
| plain7/naive | −23.5% / −23.7%, interval ±8 points |
| plain7/semi | −4.7% / −5.1% |

The AC improvements are mechanism-backed: allocprobe fell from 644 597 to
373 499 allocations on ac10/naive (−42%) and 18 659 to 12 615 on ac6/naive
(−32%), node counts unchanged everywhere (behavioral checksum). The E14
calibration (30-41% allocation cut bought 13.5%) predicted low double
digits; the larger realized win is consistent with the removed allocations
sitting on the search's leaf path rather than its interior.

The plain7 changes are NOT attributable to this mechanism (plain joins
execute zero rest bindings) and plain7/naive's interval is sixteen times
wider than the ac ones. Read them as code-placement movement of the kind
`containers-verus/doc/design/11-layout-parity.md` documents, not as part of
this experiment's claim.

## What remains

Post-E15 allocprobe: ac10/naive 1.36 allocations per step (was 2.34), ac6
0.91-1.03, plain unchanged at 0.12-0.15. The next allocator in the AC
comparisons is unattributed; re-probe before proposing (perf-dps.md D5's
discipline).
