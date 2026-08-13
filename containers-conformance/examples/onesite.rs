//! Confound-free prod-vs-verus push comparison.
//!
//! `benches/micro_untracked.rs`'s `push_only_untracked` group cannot be trusted
//! between its two arms: it is contaminated by benchmark position (~+18% to
//! whichever arm runs second, a glibc heap-reuse effect) and by hot-loop cache
//! line alignment (~+18% when the 8-instruction loop straddles a 64-byte
//! boundary). See that file's header and `doc/design/11-layout-parity.md`.
//!
//! This probe removes both. The implementation is selected at *runtime*, so
//! both arms are reached through one identical call site in one binary at one
//! code offset, and each is timed both first and last with the best time taken.
//! Any residual difference is the implementation and nothing else.
//!
//! Expected: within ~0.5%. As of the ContainerId allocator alignment it reads
//! +0.1%, order-independent.
//!
//! Run with `cargo run --release --example onesite -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;
type VV = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;
const N: usize = 100_000;

#[inline(never)]
fn run(which: usize) -> u32 {
    if which == 0 {
        let mut v: prod::VecP<u64, u32, false> = prod::VecP::new();
        for i in 0..N {
            v.try_push(i as u64).expect("push");
        }
        v.len()
    } else {
        let mut v: VV = VV::new();
        for i in 0..N {
            v.try_push(i as u64).expect("push: within index word");
        }
        v.len()
    }
}
fn time(w: usize) -> f64 {
    for _ in 0..200 {
        black_box(run(w));
    }
    let mut best = f64::MAX;
    for _ in 0..5 {
        let t = std::time::Instant::now();
        for _ in 0..1000 {
            black_box(run(w));
        }
        best = best.min(t.elapsed().as_nanos() as f64 / 1000.0 / 1000.0);
    }
    best
}
fn main() {
    // alternate which runs first across the two orders
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
