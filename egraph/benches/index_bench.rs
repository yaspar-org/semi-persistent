// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_containers::bplus::BPlusTreeSet;
use std::collections::{BTreeSet, HashSet};

const N: usize = 10_000_000;

/// Generate N unique random-ish u32 values via a simple LCG.
fn make_random_set() -> Vec<u32> {
    let mut set = HashSet::with_capacity(N);
    let mut x: u64 = 0xDEAD_BEEF;
    while set.len() < N {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        set.insert((x >> 33) as u32);
    }
    set.into_iter().collect()
}

fn bench_10m(c: &mut Criterion) {
    let random_keys = make_random_set();

    // Pre-build sorted vec (not timed).
    let mut sorted = random_keys.clone();
    sorted.sort_unstable();

    // Pre-build BTreeSet (not timed).
    let btree: BTreeSet<u32> = random_keys.iter().copied().collect();

    // Pre-build B+Tree from sorted (not timed).
    let bplus_bulk = BPlusTreeSet::<false>::from_sorted(&sorted);

    // Pre-build B+Tree via insert (not timed).
    let mut bplus_inc = BPlusTreeSet::<false>::new();
    for &k in &random_keys {
        bplus_inc.insert(k);
    }

    // --- Build benchmarks ---
    let mut group = c.benchmark_group("build_10m");
    group.sample_size(10);

    group.bench_function("sorted_vec", |b| {
        b.iter(|| {
            let mut v = random_keys.clone();
            v.sort_unstable();
            std::hint::black_box(v.len());
        });
    });

    group.bench_function("bplus_bulk", |b| {
        b.iter(|| {
            let mut v = random_keys.clone();
            v.sort_unstable();
            let t = BPlusTreeSet::<false>::from_sorted(&v);
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("bplus_insert", |b| {
        b.iter(|| {
            let mut t = BPlusTreeSet::<false>::new();
            for &k in &random_keys {
                t.insert(k);
            }
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("btreeset", |b| {
        b.iter(|| {
            let t: BTreeSet<u32> = random_keys.iter().copied().collect();
            std::hint::black_box(t.len());
        });
    });

    group.finish();

    // --- Iteration benchmarks ---
    let mut group = c.benchmark_group("iter_10m");
    group.sample_size(10);

    group.bench_function("sorted_vec", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &v in &sorted {
                sum = sum.wrapping_add(v as u64);
            }
            std::hint::black_box(sum);
        });
    });

    group.bench_function("bplus_bulk", |b| {
        b.iter(|| {
            let mut cur = bplus_bulk.cursor();
            cur.seek_first();
            let mut sum = 0u64;
            while let Some(k) = cur.key() {
                sum = sum.wrapping_add(k as u64);
                cur.step();
            }
            std::hint::black_box(sum);
        });
    });

    group.bench_function("bplus_insert", |b| {
        b.iter(|| {
            let mut cur = bplus_inc.cursor();
            cur.seek_first();
            let mut sum = 0u64;
            while let Some(k) = cur.key() {
                sum = sum.wrapping_add(k as u64);
                cur.step();
            }
            std::hint::black_box(sum);
        });
    });

    group.bench_function("btreeset", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &v in &btree {
                sum = sum.wrapping_add(v as u64);
            }
            std::hint::black_box(sum);
        });
    });

    group.finish();

    // --- Seek benchmarks (10k seeks into 10M) ---
    let seeks: Vec<u32> = sorted.iter().step_by(1000).copied().collect(); // ~10k seeks

    let mut group = c.benchmark_group("seek_10m");

    group.bench_function("sorted_vec", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &target in &seeks {
                let pos = sorted.partition_point(|&k| k < target);
                if pos < sorted.len() {
                    sum = sum.wrapping_add(sorted[pos] as u64);
                }
            }
            std::hint::black_box(sum);
        });
    });

    group.bench_function("bplus", |b| {
        b.iter(|| {
            let mut cur = bplus_bulk.cursor();
            let mut sum = 0u64;
            for &target in &seeks {
                cur.seek(target);
                if let Some(k) = cur.key() {
                    sum = sum.wrapping_add(k as u64);
                }
            }
            std::hint::black_box(sum);
        });
    });

    group.bench_function("btreeset", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &target in &seeks {
                if let Some(&k) = btree.range(target..).next() {
                    sum = sum.wrapping_add(k as u64);
                }
            }
            std::hint::black_box(sum);
        });
    });

    group.finish();
}

fn bench_monotonic_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("monotonic_insert_10m");
    group.sample_size(10);
    let n = 10_000_000u32;

    group.bench_function("bplus", |b| {
        b.iter(|| {
            let mut t = BPlusTreeSet::<false>::new();
            for i in 0..n {
                t.insert(i);
            }
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("btreeset", |b| {
        b.iter(|| {
            let mut t = BTreeSet::new();
            for i in 0..n {
                t.insert(i);
            }
            std::hint::black_box(t.len());
        });
    });

    group.bench_function("vec_push_only", |b| {
        b.iter(|| {
            let mut v = Vec::with_capacity(n as usize);
            for i in 0..n {
                v.push(i);
            }
            std::hint::black_box(v.len());
        });
    });

    group.finish();
}

criterion_group!(benches, bench_10m, bench_monotonic_insert);
criterion_main!(benches);
