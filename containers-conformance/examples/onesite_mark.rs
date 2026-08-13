// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Confound-free prod-vs-verus comparison for `vec/mark_set_restore`.
//!
//! The `retained_containers` bench registers `prod` then `verus` in one group,
//! the same positional layout that made `micro/push_only_untracked` read +40%
//! when the code was byte-identical (see `examples/onesite.rs` and
//! `doc/design/11-layout-parity.md`). `vec/mark_set_restore` reads anywhere from
//! −1.8% to +19.9% across runs while three hand-timed harnesses call it parity;
//! that spread is the positional signature.
//!
//! This probe removes the confound: the implementation is selected at runtime,
//! so both arms go through one call site in one binary, and each is timed both
//! first and last with the best time kept.
//!
//! Run: `cargo run --release --example onesite_mark -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

type VV = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, true>;
const VEC_N: usize = 100_000;
const VEC_TOUCHES: usize = 50_000;

// The mark/set/restore body, identical modulo the crate's `ShrinkPolicy` path.
macro_rules! churn {
    ($v:expr, $policy:expr) => {{
        let v = $v;
        let tok = v.try_mark($policy).expect("mark");
        let mut x: u64 = 0x9E3779B97F4A7C15;
        for _ in 0..VEC_TOUCHES {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let idx = (x % VEC_N as u64) as u32;
            v.set(idx, x);
        }
        v.try_restore(tok).expect("restore");
        v.len() as usize
    }};
}

// Matches criterion's `iter_batched_ref`: the vec build is SETUP (untimed);
// only one mark/set/restore churn is timed, on a freshly built vec each sample.
fn time(w: usize) -> f64 {
    let mut best = f64::MAX;
    // A few warm iterations first, then timed samples.
    for s in 0..70 {
        if w == 0 {
            let mut v: prod::VecP<u64, u32, true> = prod::VecP::new();
            for i in 0..VEC_N {
                v.try_push(i as u64).expect("push");
            }
            let t = std::time::Instant::now();
            black_box(churn!(&mut v, prod::ShrinkPolicy::Never));
            let us = t.elapsed().as_nanos() as f64 / 1000.0;
            if s >= 20 {
                best = best.min(us);
            }
        } else {
            let mut v: VV = VV::new();
            for i in 0..VEC_N {
                v.try_push(i as u64).expect("push: within index word");
            }
            let t = std::time::Instant::now();
            black_box(churn!(&mut v, verus::vec::ShrinkPolicy::Never));
            let us = t.elapsed().as_nanos() as f64 / 1000.0;
            if s >= 20 {
                best = best.min(us);
            }
        }
    }
    best
}

fn main() {
    let p1 = time(0);
    let v1 = time(1);
    let v2 = time(1);
    let p2 = time(0);
    let p = p1.min(p2);
    let v = v1.min(v2);
    println!(
        "prod {p:.2} us   verus {v:.2} us   {:+.1}%",
        (v / p - 1.0) * 100.0
    );
    println!("  (prod first={p1:.2} last={p2:.2} | verus first={v1:.2} last={v2:.2})");
}
