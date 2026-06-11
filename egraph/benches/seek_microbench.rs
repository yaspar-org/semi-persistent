// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Isolates the single `seek()` cost difference between `SortedVecCursor`
//! and `BPlusCursor` on the workload shape that leapfrog actually produces:
//! many small-skip forward seeks into a large sorted set.
//!
//! Two B+tree build paths are benchmarked:
//!
//! - `bplus_bulk`: built via `from_sorted`, so arena order matches
//!   traversal order — best-case cache locality.
//! - `bplus_incremental`: built via randomly-ordered `insert` calls,
//!   producing an arena where leaves and internal nodes are interleaved
//!   in allocation order. This models the real e-matching index which
//!   grows one node at a time as new e-nodes are canonicalized.
//!
//! Setup: one sorted set of N keys. Drive a cursor through N seeks that
//! each advance by exactly 1 position. At this small-skip pattern,
//! binary search pays log N per seek while the B+tree fast path stays
//! inside the current leaf.
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers::{
    SortedCursor,
    bplus::{BPlusTreeSet, BinarySearch, Layout256},
};
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::index::SortedVec;

type Tree = BPlusTreeSet<ENodeId, Layout256, BinarySearch, false>;

/// Fisher-Yates shuffle seeded deterministically so benchmark runs are stable.
fn shuffled(mut v: Vec<u32>, seed: u64) -> Vec<u32> {
    let mut s = seed;
    for i in (1..v.len()).rev() {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let j = (s >> 33) as usize % (i + 1);
        v.swap(i, j);
    }
    v
}

fn seek_microbench(c: &mut Criterion) {
    let mut group = c.benchmark_group("seek_microbench");
    group.sample_size(20);

    for &n in &[1_000usize, 100_000, 1_000_000] {
        // Keys: 0, 10, 20, ... (step 10 so seek targets can fall between).
        let data: Vec<u32> = (0..n as u32).map(|i| i * 10).collect();

        let svec = SortedVec::<ENodeId> {
            data: data.iter().map(|&x| ENodeId::new(x)).collect(),
        };

        // Bulk-built tree: arena in traversal order.
        let data_ids: Vec<ENodeId> = data.iter().map(|&x| ENodeId::new(x)).collect();
        let tree_bulk = Tree::from_sorted(&data_ids);

        // Incrementally-built tree: same final contents, but inserted in
        // random order. Each `insert` allocates new leaves and splits
        // internal nodes on demand, so the arena ends up with leaves and
        // internals interleaved. Descending from root will chase pointers
        // to arbitrary arena slots — every node load is a cold cache line.
        let mut tree_inc = Tree::new();
        for &k in &shuffled(data.clone(), 0xA5A5_DEADBEEF) {
            tree_inc.insert(ENodeId::new(k));
        }
        // Sanity: same contents, same cursor behavior.
        assert_eq!(tree_bulk.len(), tree_inc.len());

        let targets: Vec<u32> = (0..n as u32).map(|i| i * 10).collect();

        group.bench_with_input(BenchmarkId::new("sortedvec", n), &(), |b, _| {
            b.iter(|| {
                let mut cur = svec.iter();
                for &t in &targets {
                    <_ as SortedCursor>::seek(&mut cur, ENodeId::new(t));
                }
                std::hint::black_box(cur.key());
            });
        });

        group.bench_with_input(BenchmarkId::new("bplus_bulk", n), &(), |b, _| {
            b.iter(|| {
                let mut cur = tree_bulk.cursor();
                cur.seek_first();
                for &t in &targets {
                    <_ as SortedCursor>::seek(&mut cur, ENodeId::new(t));
                }
                std::hint::black_box(cur.key());
            });
        });

        group.bench_with_input(BenchmarkId::new("bplus_incremental", n), &(), |b, _| {
            b.iter(|| {
                let mut cur = tree_inc.cursor();
                cur.seek_first();
                for &t in &targets {
                    <_ as SortedCursor>::seek(&mut cur, ENodeId::new(t));
                }
                std::hint::black_box(cur.key());
            });
        });
    }

    group.finish();
}

criterion_group!(benches, seek_microbench);
criterion_main!(benches);
