//! Show that the prod-vs-verus push gap is code alignment, not implementation.
//!
//! Shifts the text section by `PAD` nop bytes and re-times both impls at the
//! same process position. If a reported gap were real it would survive the
//! shift; if it is alignment, it moves. Measured across PAD = 0, 16, 32, 48,
//! 64, 80: both arms stay within 0.1% of each other at ~56.5 µs every time.
//!
//! Companion to `onesite.rs`; background in the header of
//! `benches/micro_untracked.rs` and `doc/design/11-layout-parity.md`.
//!
//! Run with:
//! ```text
//! for p in 0 16 32 48 64 80; do
//!   PAD=$p cargo run --release --example alignprobe -p containers-conformance
//! done
//! ```
//! `PAD` is threaded through `build.rs` (default 0, so a plain `cargo build`
//! compiles fine), and `rerun-if-env-changed=PAD` rebuilds on each value.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;
type VV = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;
const N: usize = 100_000;

// PAD nops shift everything after them in the text section. `ALIGNPROBE_PAD`
// is set by build.rs from the `PAD` env var (default 0).
core::arch::global_asm!(concat!(
    ".text\n.globl __pad_start\n__pad_start:\n.rept ",
    env!("ALIGNPROBE_PAD"),
    "\nnop\n.endr\n"
));

#[inline(never)]
fn prod_loop() -> u32 {
    let mut v: prod::VecP<u64, u32, false> = prod::VecP::new();
    for i in 0..N {
        v.push(i as u64);
    }
    v.len()
}
#[inline(never)]
fn verus_loop() -> u32 {
    let mut v: VV = VV::new();
    for i in 0..N {
        v.try_push(i as u64).expect("push: within index word");
    }
    v.len()
}
fn time(f: fn() -> u32) -> f64 {
    for _ in 0..200 {
        black_box(f());
    } // warm
    let t = std::time::Instant::now();
    for _ in 0..2000 {
        black_box(f());
    }
    t.elapsed().as_nanos() as f64 / 2000.0 / 1000.0
}
fn main() {
    // interleave to neutralize any drift
    let (mut p, mut v) = (f64::MAX, f64::MAX);
    for _ in 0..3 {
        p = p.min(time(prod_loop));
        v = v.min(time(verus_loop));
    }
    println!(
        "PAD={:>4}  prod {p:>7.2} us  verus {v:>7.2} us  {:+.1}%",
        env!("ALIGNPROBE_PAD"),
        (v / p - 1.0) * 100.0
    );
}
