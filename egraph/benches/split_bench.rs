// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_containers::bplus::{BPlusTreeSet, BinarySearch, Layout64};
use semi_persistent_egraph::id::ENodeId;
use std::collections::BTreeSet;

// ---------------------------------------------------------------------------
// Microbenchmark: split-only (small working set, L1-resident)
// ---------------------------------------------------------------------------

fn bench_split_only(c: &mut Criterion) {
    let mut group = c.benchmark_group("split_only");

    // Insert 15 keys into an empty tree — forces exactly 1 leaf split.
    group.bench_function("bplus_one_split", |b| {
        b.iter(|| {
            let mut t = BPlusTreeSet::<ENodeId, Layout64, BinarySearch, false>::new();
            for i in 0..15u32 {
                t.insert(ENodeId::new(i));
            }
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("btreeset_one_split", |b| {
        b.iter(|| {
            let mut t = BTreeSet::new();
            for i in 0..15u32 {
                t.insert(ENodeId::new(i));
            }
            std::hint::black_box(t.len());
        });
    });

    // Insert 1000 keys — forces ~70 leaf splits, entire tree fits in L1 (4.5KB).
    group.bench_function("bplus_1k_l1_resident", |b| {
        b.iter(|| {
            let mut t = BPlusTreeSet::<ENodeId, Layout64, BinarySearch, false>::new();
            for i in 0..1000u32 {
                t.insert(ENodeId::new(i));
            }
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("btreeset_1k_l1_resident", |b| {
        b.iter(|| {
            let mut t = BTreeSet::new();
            for i in 0..1000u32 {
                t.insert(ENodeId::new(i));
            }
            std::hint::black_box(t.len());
        });
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Clustered inserts (insert-near-last pattern)
// ---------------------------------------------------------------------------

fn bench_clustered(c: &mut Criterion) {
    let mut group = c.benchmark_group("clustered_insert");

    // 10 clusters of 1000 elements each, sorted within cluster.
    // Pattern: [0..1000, 10000..11000, 20000..21000, ...]
    // Simulates inserting nodes from the same e-class (spatially local).
    let mut data = Vec::new();
    for cluster in 0..10 {
        for i in 0..1000u32 {
            data.push(cluster * 10000 + i);
        }
    }

    group.bench_function("bplus", |b| {
        b.iter(|| {
            let mut t = BPlusTreeSet::<ENodeId, Layout64, BinarySearch, false>::new();
            for &k in &data {
                t.insert(ENodeId::new(k));
            }
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("btreeset", |b| {
        b.iter(|| {
            let mut t = BTreeSet::new();
            for &k in &data {
                t.insert(k);
            }
            std::hint::black_box(t.len());
        });
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Bulk-loading fill factor (sorted input)
// ---------------------------------------------------------------------------

fn bench_sorted_input(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorted_input_100k");
    let data: Vec<u32> = (0..100_000).collect();
    let data_ids: Vec<ENodeId> = data.iter().map(|&x| ENodeId::new(x)).collect();

    group.bench_function("bplus_insert", |b| {
        b.iter(|| {
            let mut t = BPlusTreeSet::<ENodeId, Layout64, BinarySearch, false>::new();
            for &k in &data {
                t.insert(ENodeId::new(k));
            }
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("bplus_from_sorted", |b| {
        b.iter(|| {
            let t = BPlusTreeSet::<ENodeId, Layout64, BinarySearch, false>::from_sorted(&data_ids);
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("btreeset", |b| {
        b.iter(|| {
            let t: BTreeSet<u32> = data.iter().copied().collect();
            std::hint::black_box(t.len());
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_split_only,
    bench_clustered,
    bench_sorted_input
);
criterion_main!(benches);
