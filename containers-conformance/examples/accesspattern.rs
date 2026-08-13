// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Sequential vs random `set` access: why `perf_gate`'s `mark_set_restore` row
//! read parity while the egraph's `mark/bitset` row reads +12.8%.
//!
//! The two benches differ in exactly one dimension. `perf_gate` picks each index
//! with an xorshift (RANDOM over 100k u64s = 800 KB, far past L2), so every
//! `set` is a cache miss and the miss latency dominates any per-op instruction
//! difference. The egraph's `bench_mark` walks `0..n/2` (SEQUENTIAL), so the
//! hardware prefetcher hides the memory cost and per-op work is visible.
//!
//! If that is the explanation, the same workload should show a much larger verus
//! delta under sequential access than under random access. Both impls go through
//! one call site; arms interleaved and min-reduced.
//!
//! Run: `cargo run --release --example accesspattern -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

type VProd = prod::VecP<u32, usize>;
type VVerus = verus::vec::Vec<u32, usize, verus::parallel_store::ParallelStore<u32, usize>, true>;

const N: usize = 100_000;

macro_rules! arm {
    ($ty:ty, $policy:expr, $random:expr) => {{
        let mut v = <$ty>::new();
        for i in 0..N {
            v.try_push((i as u32) & 0x7FFF_FFFF).expect("push");
        }
        // Criterion reuses one vec across iterations, so time a steady-state
        // mark/set/restore cycle on an already-materialized capture bitmap.
        let t = std::time::Instant::now();
        let tok = v.try_mark($policy).expect("mark");
        if $random {
            let mut x: u64 = 0x9E3779B97F4A7C15;
            for _ in 0..(N / 2) {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                v.set((x % N as u64) as usize, (x as u32) & 0x7FFF_FFFF);
            }
        } else {
            for i in 0..(N / 2) {
                v.set(i, (i as u32 + 999) & 0x7FFF_FFFF);
            }
        }
        v.try_restore(tok).expect("restore");
        let us = t.elapsed().as_nanos() as f64 / 1000.0;
        black_box(v.len());
        us
    }};
}

fn time(which: usize, random: bool) -> f64 {
    let mut best = f64::MAX;
    for s in 0..30 {
        let us = if which == 0 {
            arm!(VProd, prod::ShrinkPolicy::Never, random)
        } else {
            arm!(VVerus, verus::vec::ShrinkPolicy::Never, random)
        };
        if s >= 8 {
            best = best.min(us);
        }
    }
    best
}

fn main() {
    for (name, random) in [("sequential sets", false), ("random sets", true)] {
        let (mut p, mut v) = (f64::MAX, f64::MAX);
        for r in 0..2 {
            if r == 0 {
                p = p.min(time(0, random));
                v = v.min(time(1, random));
            } else {
                v = v.min(time(1, random));
                p = p.min(time(0, random));
            }
        }
        println!(
            "{name:<18} prod {p:>9.2} us   verus {v:>9.2} us   {:+.1}%",
            (v / p - 1.0) * 100.0
        );
    }
}
