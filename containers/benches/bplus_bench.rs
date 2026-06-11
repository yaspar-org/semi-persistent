// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! B+Tree parameterization microbenchmarks.
//!
//! Sweeps node size ({64, 128, 256, 512} byte) × search kind ({BinarySearch,
//! Branchless}) × key width ({u32, u64}) across three workloads:
//!
//! - `build`:   bulk `from_sorted` of 1M sorted keys.
//! - `insert`:  per-key `insert` of 1M random keys.
//! - `seek`:    10K monotonically-increasing seeks into a 1M-key tree.
//!
//! u32 layouts exist at {64, 128, 256} byte sizes; u64 layouts at {128, 256,
//! 512} byte sizes (u64 needs a larger node to match u32's fanout).
//!
//! `std::collections::BTreeSet` is included as a baseline.
use std::collections::{BTreeSet, HashSet};

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers::{
    BPlusTreeSet, BinarySearch, Branchless, DenseId, Layout64U32, Layout128U32, Layout128U64,
    Layout256U32, Layout256U64, Layout512U64, NodeLayout, SearchKind,
};

semi_persistent_containers::define_id31! {
    pub struct BenchId31 / StoredBenchId31, "b";
}
semi_persistent_containers::define_id63! {
    pub struct BenchId63 / StoredBenchId63, "b64";
}

const N: usize = 1_000_000;
const SEEK_COUNT: usize = 10_000;

fn make_random_keys(n: usize) -> Vec<u32> {
    let mut set = HashSet::with_capacity(n);
    let mut x: u64 = 0xDEAD_BEEF;
    while set.len() < n {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        set.insert(((x >> 33) as u32) & 0x7FFF_FFFF);
    }
    set.into_iter().collect()
}

fn label<L: NodeLayout, S: SearchKind>(key_width: &str) -> String {
    let search = if std::any::type_name::<S>().ends_with("BinarySearch") {
        "bin"
    } else {
        "br"
    };
    format!("bplus{}_{}_{}", L::NODE_SIZE, key_width, search)
}

fn bench_combo<K, L, S>(c: &mut Criterion, key_width: &str, sorted: &[K], random: &[K], seeks: &[K])
where
    K: DenseId + 'static,
    L: NodeLayout<Word = <K as DenseId>::Index>,
    S: SearchKind,
{
    let name = label::<L, S>(key_width);
    let tree: BPlusTreeSet<K, L, S, false> = BPlusTreeSet::<K, L, S, false>::from_sorted(sorted);

    c.bench_with_input(
        BenchmarkId::new("build_from_sorted_1m", &name),
        &(),
        |b, _| {
            b.iter(|| {
                let t = BPlusTreeSet::<K, L, S, false>::from_sorted(sorted);
                std::hint::black_box(t.len());
            });
        },
    );

    c.bench_with_input(BenchmarkId::new("insert_random_1m", &name), &(), |b, _| {
        b.iter(|| {
            let mut t = BPlusTreeSet::<K, L, S, false>::new();
            for &k in random {
                t.insert(k);
            }
            std::hint::black_box(t.len());
        });
    });

    c.bench_with_input(
        BenchmarkId::new("seek_monotonic_10k", &name),
        &(),
        |b, _| {
            b.iter(|| {
                let mut cur = tree.cursor();
                let mut sum = 0usize;
                for &target in seeks {
                    cur.seek(target);
                    if let Some(k) = cur.key() {
                        sum = sum.wrapping_add(k.to_usize());
                    }
                }
                std::hint::black_box(sum);
            });
        },
    );
}

fn bench_btreeset(c: &mut Criterion, sorted: &[u32], random: &[u32], seeks: &[u32]) {
    let tree: BTreeSet<u32> = sorted.iter().copied().collect();

    c.bench_function("build_from_sorted_1m/btreeset", |b| {
        b.iter(|| {
            let t: BTreeSet<u32> = sorted.iter().copied().collect();
            std::hint::black_box(t.len());
        });
    });
    c.bench_function("insert_random_1m/btreeset", |b| {
        b.iter(|| {
            let mut t = BTreeSet::new();
            for &k in random {
                t.insert(k);
            }
            std::hint::black_box(t.len());
        });
    });
    c.bench_function("seek_monotonic_10k/btreeset", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &target in seeks {
                if let Some(&k) = tree.range(target..).next() {
                    sum = sum.wrapping_add(k as u64);
                }
            }
            std::hint::black_box(sum);
        });
    });
}

fn bench_all(c: &mut Criterion) {
    let raw = make_random_keys(N);
    let mut sorted = raw.clone();
    sorted.sort_unstable();
    let seeks_u32: Vec<u32> = sorted.iter().step_by(N / SEEK_COUNT).copied().collect();

    // 31-bit keys.
    let sorted31: Vec<BenchId31> = sorted.iter().map(|&x| BenchId31::new(x)).collect();
    let random31: Vec<BenchId31> = raw.iter().map(|&x| BenchId31::new(x)).collect();
    let seeks31: Vec<BenchId31> = seeks_u32.iter().map(|&x| BenchId31::new(x)).collect();

    bench_combo::<BenchId31, Layout64U32, BinarySearch>(c, "u32", &sorted31, &random31, &seeks31);
    bench_combo::<BenchId31, Layout64U32, Branchless>(c, "u32", &sorted31, &random31, &seeks31);
    bench_combo::<BenchId31, Layout128U32, BinarySearch>(c, "u32", &sorted31, &random31, &seeks31);
    bench_combo::<BenchId31, Layout256U32, BinarySearch>(c, "u32", &sorted31, &random31, &seeks31);

    // 63-bit keys (same values widened).
    let sorted63: Vec<BenchId63> = sorted.iter().map(|&x| BenchId63::new(x as u64)).collect();
    let random63: Vec<BenchId63> = raw.iter().map(|&x| BenchId63::new(x as u64)).collect();
    let seeks63: Vec<BenchId63> = seeks_u32
        .iter()
        .map(|&x| BenchId63::new(x as u64))
        .collect();

    bench_combo::<BenchId63, Layout128U64, BinarySearch>(c, "u64", &sorted63, &random63, &seeks63);
    bench_combo::<BenchId63, Layout256U64, BinarySearch>(c, "u64", &sorted63, &random63, &seeks63);
    bench_combo::<BenchId63, Layout512U64, BinarySearch>(c, "u64", &sorted63, &random63, &seeks63);
    bench_combo::<BenchId63, Layout512U64, Branchless>(c, "u64", &sorted63, &random63, &seeks63);

    bench_btreeset(c, &sorted, &raw, &seeks_u32);
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = bench_all
}
criterion_main!(benches);
