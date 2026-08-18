<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Destination-passing analysis: temporary allocations on the hot paths (through E17)

Where the hot paths still build a temporary and copy it into its real
destination, and what writing through to the destination buys. Findings from
instrumented runs of `examples/allocprobe` on this revision (egraph-wf, after
the verified-aggregate swap); each proposed change carries the experiment
that decides it, per the E-series protocol; outcomes are folded in where
they exist (D1 landed as E15, and the flat match store as E17, per the
closing section).

## The measured envelope

`allocprobe`, this revision:

| workload | allocs | allocs per step |
|---|---|---|
| plain7/naive | 26 711 | 0.12 |
| plain7/semi | 17 183 | 0.15 |
| ac6/naive | 18 659 | 1.35 |
| ac10/naive | 644 597 | 2.34 |
| ac10/semi | 403 229 | 2.21 |
| accompl32 / accompl64 | 3 956 / 8 001 | one-time, ~12.6 per node |

The plain joins are at their floor (0.12 per step is the index build plus
match spill, both already scratch-recycled by E2/E4b). The AC matcher still
allocates about 2.3 times per e-matching step. That residue is where
destination passing applies.

## D1. Rest-binding temporaries in the AC assignment search: the headline

`ematch.rs`, `decompose_ac_elem` and `decompose_aci_elem` (the LIVE recursive
engine, one level below the child buffers E14 recycled): at every leaf of the
sub-multiset assignment search that carries a rest variable, the matcher
builds the residual binding as a fresh `Vec` and hands it to
`env.push_mset(rv, &remaining)`, which copies it into `Match`'s `mset_pool`
and records a span:

```rust
let remaining: Vec<Cfg::C> = residual.iter()
    .filter(|&&(_, m)| m > zero)
    .map(|&(g, m)| Cfg::mset_child_with_mult(g, m))
    .collect();
env.push_mset(rv, &remaining);
```

The pool IS the destination; the temporary exists only because `push_mset`
takes a slice. `collect` through a `filter` starts from a zero size hint, so
each binding pays the 4/8/16 doubling walk.

Instrumented on this revision (counters at both sites, one allocprobe run):
**221 388 rest bindings, mean residual 9.9 elements, all on the multiset
site** (the set-variant site fired zero times on these workloads but has the
identical shape). At three growth allocations per binding that is ~660k
allocations across the run, which accounts for the bulk of what the ac
workloads still allocate: the ac10 pair alone is 1.05M.

**Change (landed as E15; the record is
`doc/perf-results/E15-rest-binding-write-through.md`, ac10 allocations
−21.5%, wall −17.5%)**: `Match::push_mset_filtered(rv, residual)` writes the
filter/map directly onto the tail of `mset_pool` and records the span from
the tail length, with `push_set_filtered(rv, residual, used)` as the
set-variant counterpart. Zero allocations per binding once the pool is warm, which
is the same mechanism `push_mset` itself already relies on. The temporary,
its growth walk, and the copy all disappear.

**Experiment (E15)**: criterion baseline on `saturate_bench` before/after,
identical-checksum assertion, allocprobe delta. Expected: ac10 allocation
count falls by roughly 60%; wall-clock by single digits to low double digits
on the ac comparisons, using E14 as the calibration point (its 30-41%
allocation cut bought 13.5%). Cost to try: low, one API on `Match` plus two
call sites.

## D2. Fallback if D1's API is rejected: size the collect

`Vec::with_capacity(residual.len())` at the same two sites removes the
growth walk (one allocation per binding instead of ~3) without touching the
`Match` API. Strictly dominated by D1; listed because it is a two-line
change with maybe half the win.

## D3. Proof-forest re-rooting allocates per justified merge

`egraph/src/classes.rs::reroot_proof`: every `merge_justified` builds
`vec![x]` and grows it along the proof path, then drops it. The destination
fix is a reusable scratch (`path: Vec<T>` beside the proof columns, or a
`ProofBuf` loan, which is the pattern `explain` already uses). Unmeasured:
every benchmark runs `PROOFS=false`, so the first step is an allocprobe
variant with proofs on. Do not ship without that number, but the mechanism
is the same one D1 removes.

## D4. Cold-engine step clones (hygiene only)

The frame-machine matcher (`MatchIterator`) clones each step's `elems` and
`children` plan vectors per executed step. E14 established no production
path and no benchmark reaches this engine (lib tests only). Fix for
cleanliness when touching that file; no experiment justified.

## D5. Completion-path allocations: instrument before proposing

`accompl32/64` allocate ~12.6 times per node with zero e-matching steps, all
in the one-time completion pass. Nothing is known about the distribution
yet; the multiset normalizers were already checked sound (caller-owned
ping-pong buffers). Next probe target, not a proposal.

## D6. Non-allocation constant factor: four root walks per directed merge

The adapter's `merge_directed` runs `prefer_a_by_uses` (two `find_const`
walks) and the kernel's merge then re-finds both arguments (two `find`
walks). A kernel entry taking already-canonical roots would halve the walks;
after full path compression the walks are one or two hops, so this is a
micro item. Measure on `saturate_bench` only; discard on anything under a
point.

## D1 and the match store: landed

D1 landed as E15 (ac10 −21.5%/−17.5%). The attribution follow-up reopened
E16's flat store for the RESULTS role and landed as E17 (every
match-emitting workload double-digit down, ac10 allocations and peak
memory −64%). Post-E17 the allocator residue is 0.08-0.58 per step across
the rewrite workloads; no attributed step-proportional class remains.

## D7. Ring-cell shrink: discarded without an experiment

Shrinking the class-ring cell from 12 to 8 bytes (bit-stealing `Opt<T>`
payload instead of the `BoolTagged` key word) was nominated on a
walk-density mechanism. `iter_class` has zero non-test consumers in the
e-graph: rings are read one cell at a time (`repr_id`) and written by
`splice`, so the mechanism has no workload and the change would buy only
4 bytes per node of footprint against a full kernel payload refactor and a
deliberate break of the layout-parity pins. Revisit only if a ring-walking
consumer appears.

## S1, closed by the swap

The A-list's path-compression study ran itself during the verified-
aggregate swap: path halving measured 3-5% slower than production's
two-pass full compression on merge-heavy saturation, and the kernel now
implements full compression, verified. No further study is warranted.

## Already destination-passing (the floor this analysis stands on)

`canon.rs` normalizers (caller-owned ping-pong buffers), `seq_children`/
`mset_children`/`set_children` (append into a caller buffer, recycled by
E14), `explain` (caller-owned `ProofBuf`), match results (E2's recycling),
RHS instantiation (E6), index-build scratch (E4b), join cursors (E1's
inline `SmallVec`). The pools-and-spans design in `Match` is itself the
destination-passing idiom; D1 closes the one gap where a temporary is still
built beside its destination and copied in.
