// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Aggregate-level comparison of the retained former-production `EClasses`
//! and the verified kernel used by the engine. The workloads isolate the
//! merge/find/mark-restore operations from e-matching and instantiation.
//!
//! Criterion samples both implementations in the same executable. Historical
//! revision-to-revision comparison can additionally use baselines:
//!
//! ```text
//! cargo bench -p containers-conformance --bench eclasses_bench -- --save-baseline before
//! # ... apply the change ...
//! cargo bench -p containers-conformance --bench eclasses_bench -- --baseline before
//! ```
//!
use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use semi_persistent_containers as retained;
use semi_persistent_containers_verus as verified;
use std::hint::black_box;

retained::define_id31! { pub struct RetainedE / StoredRetainedE, "re"; }
retained::define_id31! { pub struct RetainedK / StoredRetainedK, "rk"; }
retained::define_id31! { pub struct RetainedL / StoredRetainedL, "rl"; }
retained::define_id31! { pub struct RetainedN / StoredRetainedN, "rn"; }
verified::define_id31! { pub struct VerifiedE / StoredVerifiedE, "ve"; }
verified::define_id31! { pub struct VerifiedK / StoredVerifiedK, "vk"; }
verified::define_id31! { pub struct VerifiedL / StoredVerifiedL, "vl"; }
verified::define_id31! { pub struct VerifiedN / StoredVerifiedN, "vn"; }

type RetainedEC = retained::eclasses::EClasses<
    RetainedE,
    RetainedK,
    RetainedL,
    RetainedN,
    retained::union_find::NoJust,
    true,
    false,
>;
type VerifiedEC = verified::eclasses::EClasses<
    VerifiedE,
    VerifiedK,
    VerifiedL,
    VerifiedN,
    verified::union_find::NoJust,
    true,
    false,
>;

const N: usize = 4096;
const FIND_PASSES: usize = 64;

/// Fresh retained aggregate with `N` singleton classes and one use each.
fn build_retained() -> (RetainedEC, Vec<RetainedE>) {
    let mut ec = RetainedEC::new();
    let mut ids = Vec::with_capacity(N);
    for i in 0..N {
        let id = <RetainedE as retained::DenseId>::from_usize(i);
        let key = ec.add_singleton(id);
        ec.add_use(key, id);
        ids.push(id);
    }
    (ec, ids)
}

/// Fresh verified aggregate with the same classes and uses.
fn build_verified() -> (VerifiedEC, Vec<VerifiedE>) {
    let mut ec = VerifiedEC::new();
    let mut ids = Vec::with_capacity(N);
    for _ in 0..N {
        let (id, key) = ec.try_add_singleton();
        ec.add_use(key, id);
        ids.push(id);
    }
    (ec, ids)
}

fn bench_merge_cascade(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses/merge_cascade");
    g.throughput(Throughput::Elements(N as u64));

    g.bench_function(BenchmarkId::new("retained", N), |b| {
        b.iter_batched(
            build_retained,
            |(mut ec, ids)| {
                let mut stride = 1;
                while stride < N {
                    let mut i = 0;
                    while i + stride < N {
                        if let Some(mi) = ec.merge(ids[i], ids[i + stride]) {
                            let sk = ec.repr_id(mi.survivor).unwrap();
                            ec.splice_uses(ec.use_list_id(sk), mi.absorbed_uses);
                        }
                        i += stride * 2;
                    }
                    stride *= 2;
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function(BenchmarkId::new("verified", N), |b| {
        b.iter_batched(
            build_verified,
            |(mut ec, ids)| {
                let mut stride = 1;
                while stride < N {
                    let mut i = 0;
                    while i + stride < N {
                        if let Some(mi) = ec.merge(ids[i], ids[i + stride]) {
                            let sk = ec.repr_id(mi.survivor).unwrap();
                            ec.splice_uses(ec.use_list_id(sk), mi.absorbed_uses);
                        }
                        i += stride * 2;
                    }
                    stride *= 2;
                }
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

fn merged_retained() -> (RetainedEC, Vec<RetainedE>) {
    let (mut ec, ids) = build_retained();
    for i in 1..N {
        ec.merge(ids[0], ids[i]);
    }
    (ec, ids)
}

fn merged_verified() -> (VerifiedEC, Vec<VerifiedE>) {
    let (mut ec, ids) = build_verified();
    for i in 1..N {
        ec.merge(ids[0], ids[i]);
    }
    (ec, ids)
}

fn bench_find_sweep(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses/find_sweep");
    g.throughput(Throughput::Elements((N * FIND_PASSES) as u64));

    g.bench_function(BenchmarkId::new("retained", N), |b| {
        let (ec, ids) = merged_retained();
        b.iter(|| {
            let mut acc = 0usize;
            for _ in 0..FIND_PASSES {
                for &id in &ids {
                    acc ^= black_box(retained::DenseId::to_usize(ec.find_const(id)));
                }
            }
            black_box(acc)
        })
    });

    g.bench_function(BenchmarkId::new("verified", N), |b| {
        let (ec, ids) = merged_verified();
        b.iter(|| {
            let mut acc = 0usize;
            for _ in 0..FIND_PASSES {
                for &id in &ids {
                    acc ^= black_box(verified::DenseId::to_usize(ec.find_const(id)));
                }
            }
            black_box(acc)
        })
    });

    g.finish();
}

fn bench_mark_merge_restore(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses/mark_merge_restore");
    g.throughput(Throughput::Elements(255));

    g.bench_function(BenchmarkId::new("retained", N), |b| {
        b.iter_batched(
            build_retained,
            |(mut ec, ids)| {
                let tok = ec.mark(retained::ShrinkPolicy::Never);
                for i in 1..256 {
                    ec.merge(ids[0], ids[i]);
                }
                ec.restore(tok);
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function(BenchmarkId::new("verified", N), |b| {
        b.iter_batched(
            build_verified,
            |(mut ec, ids)| {
                let tok = ec.mark(verified::ShrinkPolicy::Never);
                for i in 1..256 {
                    ec.merge(ids[0], ids[i]);
                }
                ec.try_restore(tok).expect("own token");
                black_box(ec.num_classes())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

criterion_group!(
    benches,
    bench_merge_cascade,
    bench_find_sweep,
    bench_mark_merge_restore,
);
criterion_main!(benches);
