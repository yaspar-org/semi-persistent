// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Micro-decomposition of the untracked vec gap: push-only and pop-only,
//! prod vs verus, to attribute the residual overhead.
//!
//! # `push_only_untracked` numbers here are NOT comparable between the two arms
//!
//! This group reports a ~+18% verus penalty that is entirely measurement
//! artifact. Do not act on it; see `examples/onesite.rs` for the sound
//! comparison (+0.1%, order-independent) and `doc/design/11-layout-parity.md`
//! for the full bisection. Two confounds, each worth ~+18% on its own:
//!
//! 1. **Position in the process.** Whichever arm is registered *second* pays
//!    it. Registering the same `prod` closure four times reads 57.9, 68.5,
//!    68.8, 68.8 µs — the penalty tracks slot, not code. Cause is glibc's
//!    `brk`-heap reuse state after a prior arm has grown and freed 2 MiB:
//!    forcing every large allocation to `mmap`
//!    (`MALLOC_MMAP_THRESHOLD_=65536`) collapses the spread to within 3.5%.
//! 2. **Code alignment of the hot loop.** Identical verus source measures
//!    57.5 µs in one bench binary and 70.2 in another, both in isolated
//!    processes, differing only in where the 8-instruction push loop lands
//!    modulo 64 (offset 21, contained → fast; offset 56, straddling a cache
//!    line → slow). Padding the text section through six layouts
//!    (`examples/alignprobe.rs`) holds both arms within 0.1% of each other.
//!
//! Both arms compile to byte-identical code: the same 8-instruction push loop,
//! the same shared `RawVec::grow_one` symbol, a 42-instruction `drop_in_place`
//! differing only in jump targets, and the same 16 allocations totalling the
//! same 2,097,120 bytes. `warm_heap`-style pre-warming does *not* fix it — the
//! state that matters is per-arena and not reachable from the benchmark.
//!
//! Kept as-is rather than "fixed" because the artifact is worth having on
//! record: it is the reason two earlier attributions of this gap (to Verus
//! codegen around the length overflow check, then to the `ContainerId`
//! allocator) were both wrong.
use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

const N: usize = 100_000;

fn bench_push_only(c: &mut Criterion) {
    let mut g = c.benchmark_group("micro/push_only_untracked");
    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut v: prod::VecP<u64, u32, false> = prod::VecP::new();
            for i in 0..N {
                v.push(i as u64);
            }
            black_box(v.len())
        })
    });
    g.bench_function("verus", |b| {
        type V = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;
        b.iter(|| {
            let mut v: V = V::new();
            for i in 0..N {
                v.push(i as u64);
            }
            black_box(v.len())
        })
    });
    g.finish();
}

fn bench_pop_only(c: &mut Criterion) {
    let mut g = c.benchmark_group("micro/pop_only_untracked");
    g.bench_function("prod", |b| {
        b.iter_batched_ref(
            || {
                let mut v: prod::VecP<u64, u32, false> = prod::VecP::new();
                for i in 0..N {
                    v.push(i as u64);
                }
                v
            },
            |v| {
                let mut acc = 0u64;
                while let Some(x) = v.pop() {
                    acc = acc.wrapping_add(x);
                }
                black_box(acc)
            },
            BatchSize::LargeInput,
        )
    });
    g.bench_function("verus", |b| {
        type V = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;
        b.iter_batched_ref(
            || {
                let mut v: V = V::new();
                for i in 0..N {
                    v.push(i as u64);
                }
                v
            },
            |v| {
                let mut acc = 0u64;
                while let Some(x) = v.pop() {
                    acc = acc.wrapping_add(x);
                }
                black_box(acc)
            },
            BatchSize::LargeInput,
        )
    });
    g.finish();
}

criterion_group!(benches, bench_push_only, bench_pop_only);
criterion_main!(benches);
