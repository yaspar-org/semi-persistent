// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Nested-mark benchmark: DEEP live frame stacks with writes retained at
//! every level, restoring to various ancestors. This is the workload the
//! depth-zero mark-churn bench cannot see — it exposes whether mark's
//! prepare cost scales with the TOP frame's diffs (production, and verus
//! after the parent-suffix fix) or the WHOLE retained history.
//!
//! Each timed iteration builds `DEPTH` nested frames, writing
//! `WRITES_PER_FRAME` cells at each level (so the diff log retains
//! DEPTH*WRITES entries across live strata), then either marks once more
//! (measuring prepare over a full history) or restores to an ancestor.

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

const N: usize = 100_000;
const WRITES_PER_FRAME: usize = 64;

// Build a stack of `depth` frames, WRITES_PER_FRAME distinct writes each,
// then mark once more — the final mark's prepare_mark sees a diff log with
// depth*WRITES retained entries but should clear only the top frame's.
macro_rules! nested_body {
    ($v:expr, $mark:path, $never:expr, $set:ident, $depth:expr) => {{
        let mut x: u64 = 0x9E3779B97F4A7C15;
        let mut toks = Vec::new();
        for _ in 0..$depth {
            toks.push($mark(&mut $v, $never));
            for _ in 0..WRITES_PER_FRAME {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let idx = (x % N as u64) as u32;
                $v.$set(idx, x);
            }
        }
        // The measured op: one more mark over the deep retained history.
        let final_tok = $mark(&mut $v, $never);
        black_box(&final_tok);
        // Restore all the way out (cost not the focus; keeps state bounded).
        $v.restore(toks[0]);
        black_box($v.len())
    }};
}

fn bench_nested_mark(c: &mut Criterion) {
    let mut g = c.benchmark_group("nested_mark/vecp_deep_history");
    for &depth in &[2usize, 8, 32] {
        g.bench_with_input(BenchmarkId::new("prod", depth), &depth, |b, &depth| {
            b.iter_batched_ref(
                || {
                    let mut v: prod::VecP<u64, u32, true> = prod::VecP::new();
                    for i in 0..N {
                        v.push(i as u64);
                    }
                    v
                },
                |v| nested_body!(*v, prod::VecP::mark, prod::ShrinkPolicy::Never, set, depth),
                BatchSize::LargeInput,
            )
        });
        g.bench_with_input(BenchmarkId::new("verus", depth), &depth, |b, &depth| {
            type V = verus::VecP<u64, u32, true>;
            b.iter_batched_ref(
                || {
                    let mut v: V = V::new();
                    for i in 0..N {
                        v.push(i as u64);
                    }
                    v
                },
                |v| nested_body!(*v, V::mark, verus::ShrinkPolicy::Never, set_index, depth),
                BatchSize::LargeInput,
            )
        });
    }
    g.finish();
}

criterion_group!(benches, bench_nested_mark);
criterion_main!(benches);
