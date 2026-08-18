<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E6: allocation in RHS instantiation (A6): **accepted**

**Verdict: accepted. 5-11% on every rewrite row, backed by an 82% allocation
reduction on `plain7` and 37% on `ac10`.**

`apply::eval` allocated a fresh `Vec` for every node it instantiated:

- `RhsOp::App`: `let mut children = Vec::new()`, one per node built, per applied
  match.
- `RhsOp::PrimApp`: `raw_vals: Vec<L>` and `refs: Vec<&L>`, two more per
  primitive call.

All three are now `SmallVec`. `eval_arg` recurses, so `children` is one live
buffer per recursion level; the plan flagged that as needing a per-depth scratch
stack or a bump arena, but a `SmallVec` handles it without either: each level's
inline storage lives in its own stack frame, which is exactly the per-depth scratch
the plan described, obtained for free.

## Allocation counts

`examples/allocprobe.rs`, per protocol item 5:

| workload | before | after | removed |
|---|---|---|---|
| `plain7/naive` | 148 111 | 26 711 | **−82.0%** |
| `plain7/semi`  |  75 159 | 17 182 | **−77.1%** |
| `ac6/naive`    |  49 224 | 29 352 | **−40.4%** |
| `ac6/semi`     |  23 564 | 14 732 | **−37.5%** |
| `ac10/naive`   | 1 702 889 | 1 070 299 | **−37.1%** |
| `ac10/semi`    | 1 098 261 |   682 741 | **−37.8%** |
| `accompl32`    |   3 931 |  3 931 | 0 |
| `accompl64`    |   7 972 |  7 972 | 0 |

`plain7` drops from 0.65 to 0.12 allocations per match step. The completion rows
are unchanged **by construction**: `accompl*` runs with no rules, so `eval` is
never called on that path. See "The completion rows" below: this matters for
reading the timing table.

## Inline capacity

Not inherited from `leapfrog::CursorVec`'s 4. A cursor vector holds one entry per
query atom; a child list holds one per child, and the AC rules splice a rest
variable (`(add (mul y x) ..r)`), so a list is as long as the matched node's arity.
Swept on `examples/acsite.rs` (min of 40 reps) and `allocprobe`:

| inline capacity | `ac10/naive` | allocations |
|---|---|---|
|  4 | 84.86 ms | 1 199 399 |
|  8 | 82.52 ms | — |
| **16** | **79.69 ms** | **1 070 299** |
| 32 | 79.60 ms | — |

16 is the knee (32 buys 0.1% for twice the stack) and it is worth 6% over the
naive choice of 4. Confirmed at the macro level: cap 4 gave −4.6 to −5.9% on the
AC rows where cap 16 gives −9.3 to −11.7%, with the `plain7` rows unchanged between
them (a larger frame costs nothing there because those lists are 2 children).

## Numbers

`saturate_bench` against `E6-before` (= `1c7e826`), three runs at cap 4 and two at
cap 16. Cap 16 shipped; its range across both runs:

| bench | change | absolute after |
|---|---|---|
| `saturate/plain7/naive` | **−7.1 to −7.8%** | 13.2 ms |
| `saturate/plain7/semi`  | **−5.5 to −6.2%** |  7.7 ms |
| `saturate/ac6/naive`    | **−9.5 to −10.8%** |  2.43 ms |
| `saturate/ac6/semi`     | **−9.0 to −10.0%** |  1.26 ms |
| `saturate/ac10/naive`   | **−9.3 to −11.3%** | 82.1 ms |
| `saturate/ac10/semi`    | **−10.6 to −11.3%** | 51.7 ms |
| `saturate/accompl32`    | −1.8 to −3.3% | 1.52 ms |
| `saturate/accompl64`    | −2.9 to −3.7% | 4.90 ms |

All `p = 0.00`. Standalone confirmation per protocol item 7, min of 200 reps:

| | baseline | A6 (cap 4) | A6 (cap 16) |
|---|---|---|---|
| `ac6/naive` | 2.6209 ms | 2.4431 ms (−6.8%) | 2.3897 ms (**−8.8%**) |
| `ac6/semi`  | 1.3359 ms | 1.2533 ms (−6.2%) | 1.2295 ms (**−8.0%**) |
| `accompl64` | 4.7011 ms | 4.7332 ms (+0.7%) | — |

Identical checksums (`ac6` 17400, `accompl64` 127200), so the rewrites produce the
same e-graph.

## The completion rows

Criterion reports −1.8 to −3.7% on `accompl32`/`accompl64`, and **that is an
artifact, not a result.** Those workloads run with `cc = true` and no rules, so
`apply::eval` is never reached: allocprobe confirms their counts are byte-identical
before and after. `complsite.rs` puts `accompl64` at 4.7332 ms against a 4.7011 ms
baseline, i.e. +0.7%, inside the band E4b measured for that site.

This is protocol item 7 working in the accepting direction rather than the
rejecting one: the rows whose mechanism is present (−37% to −82% allocations) show
5-11% and reproduce standalone, and the rows whose mechanism is provably absent
show a criterion delta that the standalone site does not confirm. Had the AC rows
been the only evidence, the same ±3% doubt would apply to them too.

## Correctness

`cargo test --workspace --release`: 81 test binaries, 0 failures. `cargo fmt --all
--check` and `cargo clippy --release --all-targets` clean.

The type change is the gate here: `eval_arg` takes `&mut ChildVec<Cfg>` instead of
`&mut Vec<Cfg::G>`, so any caller that assumed `Vec` fails to compile rather than
silently mis-behaving, and `eg.add(*o, &children)` still receives a slice through
`Deref`. Behaviour is identical by construction (`SmallVec` has the same
`push`/`extend_from_slice` semantics), which the unchanged checksums confirm
empirically.

## Not done

`RhsArg::SeqComp`/`SetComp`/`MsetComp` each call `m.seq_slice(..).to_vec()` to
copy the source out of the match before iterating, because the loop body needs
`&mut Match` to bind the comprehension variable. That is one allocation per
comprehension evaluation, and removing it needs the borrow split (index into the
match, or lend the pool out) rather than a container swap. None of the benchmark
workloads use comprehensions, so there is no measurement to justify it here; left
for a workload that exercises them.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench saturate_bench -- --save-baseline E6-before   # at 1c7e826
cargo bench --bench saturate_bench -- --baseline E6-before
cargo run --release --example allocprobe
cargo run --release --example acsite -- 10 40
```
