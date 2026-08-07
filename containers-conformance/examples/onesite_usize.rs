// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Confound-free probe of the egraph's exact `mark`/`set`/`restore` shape.
//!
//! `egraph/benches/vec_bench.rs::bench_mark` reads a stable +12.8% verus-slower
//! across n = 1k..1M after the PR-2 swap. That is NOT the layout artifact
//! documented in `doc/design/11-layout-parity.md` (a layout delta cannot track n
//! over three decades), so it needs a single-call-site confirmation.
//!
//! The one type difference from the gated `perf_gate` row: the egraph
//! instantiates `VecP<u32, usize>` — a **usize** index — where `perf_gate` uses
//! `u32`. This probe runs the egraph's body on both index widths, selecting the
//! impl at RUNTIME so both arms share one call site.
//!
//! Run: `cargo run --release --example onesite_usize -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

type VProdU = prod::VecP<u32, usize>;
type VProd32 = prod::VecP<u32, u32>;
type VVerusU = verus::vec::Vec<u32, usize, verus::parallel_store::ParallelStore<u32, usize>, true>;
type VVerus32 = verus::vec::Vec<u32, u32, verus::parallel_store::ParallelStore<u32, u32>, true>;

const N: usize = 100_000;

/// The egraph's timed body: mark, dirty half the cells, restore.
macro_rules! churn {
    ($v:expr, $policy:expr, $idx:ty) => {{
        let v = $v;
        let t = v.mark($policy);
        for i in 0..(N / 2) {
            v.set((i % N) as $idx, (i as u32 + 999) & 0x7FFF_FFFF);
        }
        v.restore(t);
        v.len()
    }};
}

fn time(which: usize) -> f64 {
    let mut best = f64::MAX;
    for s in 0..40 {
        let us = match which {
            0 => {
                let mut v = VProdU::new();
                for i in 0..N {
                    v.push((i as u32) & 0x7FFF_FFFF);
                }
                let t = std::time::Instant::now();
                black_box(churn!(&mut v, prod::ShrinkPolicy::Never, usize));
                t.elapsed().as_nanos() as f64 / 1000.0
            }
            1 => {
                let mut v = VVerusU::new();
                for i in 0..N {
                    v.push((i as u32) & 0x7FFF_FFFF);
                }
                let t = std::time::Instant::now();
                black_box(churn!(&mut v, verus::vec::ShrinkPolicy::Never, usize));
                t.elapsed().as_nanos() as f64 / 1000.0
            }
            2 => {
                let mut v = VProd32::new();
                for i in 0..N {
                    v.push((i as u32) & 0x7FFF_FFFF);
                }
                let t = std::time::Instant::now();
                black_box(churn!(&mut v, prod::ShrinkPolicy::Never, u32));
                t.elapsed().as_nanos() as f64 / 1000.0
            }
            _ => {
                let mut v = VVerus32::new();
                for i in 0..N {
                    v.push((i as u32) & 0x7FFF_FFFF);
                }
                let t = std::time::Instant::now();
                black_box(churn!(&mut v, verus::vec::ShrinkPolicy::Never, u32));
                t.elapsed().as_nanos() as f64 / 1000.0
            }
        };
        if s >= 10 {
            best = best.min(us);
        }
    }
    best
}

fn main() {
    // Interleave so neither arm is systematically second on a warmed heap.
    let (mut pu, mut vu, mut p32, mut v32) = (f64::MAX, f64::MAX, f64::MAX, f64::MAX);
    for r in 0..2 {
        if r == 0 {
            pu = pu.min(time(0));
            vu = vu.min(time(1));
            p32 = p32.min(time(2));
            v32 = v32.min(time(3));
        } else {
            v32 = v32.min(time(3));
            p32 = p32.min(time(2));
            vu = vu.min(time(1));
            pu = pu.min(time(0));
        }
    }
    println!(
        "index=usize  prod {pu:.2} us  verus {vu:.2} us  {:+.1}%",
        (vu / pu - 1.0) * 100.0
    );
    println!(
        "index=u32    prod {p32:.2} us  verus {v32:.2} us  {:+.1}%",
        (v32 / p32 - 1.0) * 100.0
    );
}
