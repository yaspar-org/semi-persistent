// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Which phase owns the egraph `mark/bitset` +12.8%?
//!
//! `egraph/benches/vec_bench.rs::bench_mark` times `mark` + `n/2` sequential
//! `set`s + `restore` as one unit. That row is verus-slower by a stable
//! +12.8% across n = 1k..1M, which cannot be the layout artifact of
//! `doc/design/11-layout-parity.md` (layout deltas do not track n over three
//! decades). This probe splits the unit into its three phases so the cost lands
//! on a specific code path instead of a guess.
//!
//! Each phase is timed separately with the other two as untimed setup, both
//! impls through one call site, interleaved, min-reduced.
//!
//! Run: `cargo run --release --example phasesplit -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

type VProd = prod::VecP<u32, usize>;
type VVerus = verus::vec::Vec<u32, usize, verus::parallel_store::ParallelStore<u32, usize>, true>;

const N: usize = 100_000;

/// Phase selector.
#[derive(Copy, Clone, PartialEq)]
enum Ph {
    Mark,
    Sets,
    Restore,
}

macro_rules! arm {
    ($ty:ty, $policy:expr, $ph:expr) => {{
        let mut v = <$ty>::new();
        for i in 0..N {
            v.try_push((i as u32) & 0x7FFF_FFFF).expect("push");
        }
        // Warm the bitmap the way the criterion bench does: it reuses ONE vec
        // across all iterations, so every iteration after the first sees an
        // already-materialized capture bitmap.
        let t0 = v.try_mark($policy).expect("mark");
        for i in 0..(N / 2) {
            v.set(i, (i as u32 + 999) & 0x7FFF_FFFF);
        }
        v.try_restore(t0).expect("restore");

        let us;
        match $ph {
            Ph::Mark => {
                let t = std::time::Instant::now();
                let tok = v.try_mark($policy).expect("mark");
                us = t.elapsed().as_nanos() as f64 / 1000.0;
                black_box(&tok);
                v.try_restore(tok).expect("restore");
            }
            Ph::Sets => {
                let tok = v.try_mark($policy).expect("mark");
                let t = std::time::Instant::now();
                for i in 0..(N / 2) {
                    v.set(i, (i as u32 + 999) & 0x7FFF_FFFF);
                }
                us = t.elapsed().as_nanos() as f64 / 1000.0;
                v.try_restore(tok).expect("restore");
            }
            Ph::Restore => {
                let tok = v.try_mark($policy).expect("mark");
                for i in 0..(N / 2) {
                    v.set(i, (i as u32 + 999) & 0x7FFF_FFFF);
                }
                let t = std::time::Instant::now();
                v.try_restore(tok).expect("restore");
                us = t.elapsed().as_nanos() as f64 / 1000.0;
            }
        }
        black_box(v.len());
        us
    }};
}

fn time(which: usize, ph: Ph) -> f64 {
    let mut best = f64::MAX;
    for s in 0..30 {
        let us = if which == 0 {
            arm!(VProd, prod::ShrinkPolicy::Never, ph)
        } else {
            arm!(VVerus, verus::vec::ShrinkPolicy::Never, ph)
        };
        if s >= 8 {
            best = best.min(us);
        }
    }
    best
}

fn main() {
    for (name, ph) in [
        ("mark", Ph::Mark),
        ("sets (n/2 sequential)", Ph::Sets),
        ("restore", Ph::Restore),
    ] {
        let (mut p, mut v) = (f64::MAX, f64::MAX);
        for r in 0..2 {
            if r == 0 {
                p = p.min(time(0, ph));
                v = v.min(time(1, ph));
            } else {
                v = v.min(time(1, ph));
                p = p.min(time(0, ph));
            }
        }
        println!(
            "{name:<24} prod {p:>9.2} us   verus {v:>9.2} us   {:+.1}%",
            (v / p - 1.0) * 100.0
        );
    }
}
