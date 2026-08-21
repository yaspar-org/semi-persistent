// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Tracked-vector benches shaped like the e-graph's saturation loop:
//! FREQUENT marks, FEW writes per mark, over VecI (InlineStore — union-find
//! parent/rank, caches, classes) and VecP, with a size sweep. This is the
//! workload distinguishes an O(len)-per-mark store from one that clears only
//! slots named by the previous frame's diffs. At fixed writes per mark, scaling
//! with `n` exposes an unintended whole-vector sweep.

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

const MARKS: usize = 200; // marks per timed iteration
const WRITES_PER_MARK: usize = 8; // few writes between marks (e-graph shape)

fn bench_veci_mark_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("tracked_veci/mark_churn");
    for &n in &[1_000usize, 100_000, 1_000_000] {
        g.bench_with_input(BenchmarkId::new("prod", n), &n, |b, &n| {
            b.iter_batched_ref(
                || {
                    let mut v: prod::VecI<u32, u32, true> = prod::VecI::new();
                    for i in 0..n {
                        v.push((i as u32) & 0x7FFF_FFFF);
                    }
                    v
                },
                |v| {
                    let mut x: u64 = 0x2545F491;
                    for _ in 0..MARKS {
                        let tok = v.mark(prod::ShrinkPolicy::Never);
                        for _ in 0..WRITES_PER_MARK {
                            x ^= x << 13;
                            x ^= x >> 7;
                            x ^= x << 17;
                            let idx = (x % n as u64) as u32;
                            v.set(idx, (x as u32) & 0x7FFF_FFFF);
                        }
                        v.restore(tok);
                    }
                    black_box(v.len());
                },
                BatchSize::LargeInput,
            )
        });
        g.bench_with_input(BenchmarkId::new("verus", n), &n, |b, &n| {
            type V = verus::VecI<u32, u32, true>;
            b.iter_batched_ref(
                || {
                    let mut v: V = V::new();
                    for i in 0..n {
                        v.try_push((i as u32) & 0x7FFF_FFFF)
                            .expect("push: within index word");
                    }
                    v
                },
                |v| {
                    let mut x: u64 = 0x2545F491;
                    for _ in 0..MARKS {
                        let tok = v
                            .try_mark(verus::ShrinkPolicy::Never)
                            .expect("mark: depth bounded by this harness");
                        for _ in 0..WRITES_PER_MARK {
                            x ^= x << 13;
                            x ^= x >> 7;
                            x ^= x << 17;
                            let idx = (x % n as u64) as u32;
                            v.set_index(idx, (x as u32) & 0x7FFF_FFFF);
                        }
                        v.try_restore(tok).expect("restore: own token");
                    }
                    black_box(v.len());
                },
                BatchSize::LargeInput,
            )
        });
    }
    g.finish();
}

fn bench_vecp_mark_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("tracked_vecp/mark_churn");
    for &n in &[1_000usize, 1_000_000] {
        g.bench_with_input(BenchmarkId::new("prod", n), &n, |b, &n| {
            b.iter_batched_ref(
                || {
                    let mut v: prod::VecP<u64, u32, true> = prod::VecP::new();
                    for i in 0..n {
                        v.push(i as u64);
                    }
                    v
                },
                |v| {
                    let mut x: u64 = 0x2545F492;
                    for _ in 0..MARKS {
                        let tok = v.mark(prod::ShrinkPolicy::Never);
                        for _ in 0..WRITES_PER_MARK {
                            x ^= x << 13;
                            x ^= x >> 7;
                            x ^= x << 17;
                            let idx = (x % n as u64) as u32;
                            v.set(idx, x);
                        }
                        v.restore(tok);
                    }
                    black_box(v.len());
                },
                BatchSize::LargeInput,
            )
        });
        g.bench_with_input(BenchmarkId::new("verus", n), &n, |b, &n| {
            type V = verus::VecP<u64, u32, true>;
            b.iter_batched_ref(
                || {
                    let mut v: V = V::new();
                    for i in 0..n {
                        v.try_push(i as u64).expect("push: within index word");
                    }
                    v
                },
                |v| {
                    let mut x: u64 = 0x2545F492;
                    for _ in 0..MARKS {
                        let tok = v
                            .try_mark(verus::ShrinkPolicy::Never)
                            .expect("mark: depth bounded by this harness");
                        for _ in 0..WRITES_PER_MARK {
                            x ^= x << 13;
                            x ^= x >> 7;
                            x ^= x << 17;
                            let idx = (x % n as u64) as u32;
                            v.set_index(idx, x);
                        }
                        v.try_restore(tok).expect("restore: own token");
                    }
                    black_box(v.len());
                },
                BatchSize::LargeInput,
            )
        });
    }
    g.finish();
}

criterion_group!(benches, bench_veci_mark_churn, bench_vecp_mark_churn);
criterion_main!(benches);
