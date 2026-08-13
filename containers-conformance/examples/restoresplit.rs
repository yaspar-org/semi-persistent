// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Which restore sub-step owns the residual +30%?
//!
//! After `CaptureBits::set_true` regained production's `#[inline(always)]`,
//! `examples/phasesplit` reads sets at −32% (verus faster) but restore at a
//! stable +30% (verus slower). `restore` does: `resize_default` → replay
//! (`restore_entry` per surviving diff) → `finish_restore`. Verus does strictly
//! LESS bitmap work than production here (one `zero_all` in `begin_restore` vs
//! production's zero in both `prepare_mark` and `finish_restore`), so the cost
//! is not the algorithm and needs isolating.
//!
//! The discriminator: `restore` cost scales with the number of surviving diffs
//! (the replay) and, separately, with the materialized word count (the zero
//! passes). Vary the dirty fraction to separate them — a per-diff cost tracks
//! the fraction; a per-word cost is flat in it.
//!
//! Run: `cargo run --release --example restoresplit -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

type VProd = prod::VecP<u32, usize>;
type VVerus = verus::vec::Vec<u32, usize, verus::parallel_store::ParallelStore<u32, usize>, true>;

const N: usize = 100_000;

macro_rules! arm {
    ($ty:ty, $policy:expr, $dirty:expr) => {{
        let mut v = <$ty>::new();
        for i in 0..N {
            v.try_push((i as u32) & 0x7FFF_FFFF).expect("push");
        }
        // Steady state: bitmap already materialized, as in criterion's reuse.
        let t0 = v.try_mark($policy).expect("mark");
        for i in 0..$dirty {
            v.set(i, (i as u32) & 0x7FFF_FFFF);
        }
        v.try_restore(t0).expect("restore");

        let tok = v.try_mark($policy).expect("mark");
        for i in 0..$dirty {
            v.set(i, (i as u32 + 999) & 0x7FFF_FFFF);
        }
        let t = std::time::Instant::now();
        v.try_restore(tok).expect("restore");
        let us = t.elapsed().as_nanos() as f64 / 1000.0;
        black_box(v.len());
        us
    }};
}

fn time(which: usize, dirty: usize) -> f64 {
    let mut best = f64::MAX;
    for s in 0..30 {
        let us = match (which, dirty) {
            (0, d) if d == N / 100 => arm!(VProd, prod::ShrinkPolicy::Never, N / 100),
            (1, d) if d == N / 100 => arm!(VVerus, verus::vec::ShrinkPolicy::Never, N / 100),
            (0, d) if d == N / 10 => arm!(VProd, prod::ShrinkPolicy::Never, N / 10),
            (1, d) if d == N / 10 => arm!(VVerus, verus::vec::ShrinkPolicy::Never, N / 10),
            (0, _) => arm!(VProd, prod::ShrinkPolicy::Never, N / 2),
            (_, _) => arm!(VVerus, verus::vec::ShrinkPolicy::Never, N / 2),
        };
        if s >= 8 {
            best = best.min(us);
        }
    }
    best
}

fn main() {
    for (name, dirty) in [
        ("1% dirty (1k diffs)", N / 100),
        ("10% dirty (10k diffs)", N / 10),
        ("50% dirty (50k diffs)", N / 2),
    ] {
        let (mut p, mut v) = (f64::MAX, f64::MAX);
        for r in 0..2 {
            if r == 0 {
                p = p.min(time(0, dirty));
                v = v.min(time(1, dirty));
            } else {
                v = v.min(time(1, dirty));
                p = p.min(time(0, dirty));
            }
        }
        println!(
            "restore {name:<24} prod {p:>9.2} us   verus {v:>9.2} us   {:+.1}%",
            (v / p - 1.0) * 100.0
        );
    }
}
