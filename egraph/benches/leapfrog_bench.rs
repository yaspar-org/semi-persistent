// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Leapfrog-triejoin microbenchmark.
//!
//! Drives the real `LeapfrogJoin` — which is generic over any
//! `SortedCursor` — with both `SortedVecCursor<ENodeId>` and `BPlusCursor`
//! as the cursor type. No intermediate adapters: `SortedCursor` is
//! implemented directly on both cursors.
//!
//! `ENodeId` is `#[repr(transparent)] u32`, so `SortedVec<ENodeId>` and
//! `BPlusTreeSet` store the same bytes per key; the comparison is
//! apples-to-apples.
//!
//! Workload: k-way intersection of large pre-built sorted sets with
//! controlled selectivity (fraction of probes that hit across *all* k
//! sets). Mirrors e-matching's access pattern.
use std::collections::HashSet;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers::bplus::{BPlusTreeSet, BinarySearch, Layout256};
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::index::{SortedVec, SortedVecCursor};
use semi_persistent_egraph::leapfrog::LeapfrogJoin;

type Tree = BPlusTreeSet<ENodeId, Layout256, BinarySearch, false>;

/// Generate `k` sorted sets of size `n`, each containing the same
/// `hits = n * hit_frac` shared keys plus `n - hits` private keys drawn
/// from a per-set disjoint range. All keys fit in 31 bits to match
/// `ENodeId`.
fn gen_sets(k: usize, n: usize, hit_frac: f64, seed: u64) -> Vec<Vec<u32>> {
    let hits = (n as f64 * hit_frac) as usize;
    let private_per_set = n - hits;

    let mut lcg = seed;
    let mut next_u32 = || {
        lcg = lcg
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((lcg >> 33) as u32) & 0x7FFF_FFFF
    };

    let shared_range: u32 = (hits as u32).saturating_mul(4).clamp(1, 0x0FFF_FFFF);
    let mut shared: HashSet<u32> = HashSet::with_capacity(hits);
    while shared.len() < hits {
        shared.insert(next_u32() % shared_range);
    }
    let shared_vec: Vec<u32> = shared.iter().copied().collect();

    let mut out = Vec::with_capacity(k);
    for i in 0..k {
        let base: u32 = shared_range + (i as u32 + 1).wrapping_mul(0x0200_0000);
        let window: u32 = (private_per_set as u32 * 4).clamp(1, 0x00FF_FFFF);
        let mut private: HashSet<u32> = HashSet::with_capacity(private_per_set);
        while private.len() < private_per_set {
            private.insert((base + next_u32() % window) & 0x7FFF_FFFF);
        }
        let mut all: Vec<u32> = shared_vec.iter().copied().chain(private).collect();
        all.sort_unstable();
        all.dedup();
        out.push(all);
    }
    out
}

// Drivers share the same `LeapfrogJoin::<C>::new(...)` call with
// different C. Both collect matches into a Vec<u32> for equivalence
// checking.

fn run_sortedvec(sets: &[SortedVec<ENodeId>]) -> Vec<u32> {
    let iters: Vec<SortedVecCursor<'_, ENodeId>> = sets.iter().map(|s| s.iter()).collect();
    let mut join = LeapfrogJoin::new(iters);
    let mut out = Vec::new();
    while join.is_valid() {
        out.push(join.key().raw());
        join.next();
    }
    out
}

fn run_bplus(trees: &[Tree]) -> Vec<u32> {
    let iters: Vec<_> = trees
        .iter()
        .map(|t| {
            let mut c = t.cursor();
            c.seek_first();
            c
        })
        .collect();
    let mut join = LeapfrogJoin::new(iters);
    let mut out = Vec::new();
    while join.is_valid() {
        out.push(join.key().raw());
        join.next();
    }
    out
}

fn bench_leapfrog(c: &mut Criterion) {
    let mut group = c.benchmark_group("leapfrog");
    group.sample_size(10);

    for &(k, n, hit_frac) in &[
        (2usize, 100_000usize, 0.01f64),
        (2, 100_000, 0.5),
        (3, 100_000, 0.01),
        (3, 100_000, 0.1),
        (5, 100_000, 0.01),
        (3, 1_000_000, 0.001),
    ] {
        let raw = gen_sets(k, n, hit_frac, 0xC0FFEE);

        let svecs: Vec<SortedVec<ENodeId>> = raw
            .iter()
            .map(|v| SortedVec {
                data: v.iter().map(|&x| ENodeId::new(x)).collect(),
            })
            .collect();
        let trees: Vec<Tree> = raw
            .iter()
            .map(|v| {
                let ids: Vec<ENodeId> = v.iter().map(|&x| ENodeId::new(x)).collect();
                Tree::from_sorted(&ids)
            })
            .collect();

        // Functional equivalence check — both backends must yield the same
        // match sequence in the same order.
        let expect = run_sortedvec(&svecs);
        let got = run_bplus(&trees);
        assert_eq!(
            got,
            expect,
            "leapfrog backends disagree at k={k} n={n} hit={hit_frac}: \
             sortedvec produced {} matches, bplus produced {}",
            expect.len(),
            got.len(),
        );

        let id = format!("k{k}_n{n}_hit{hit_frac}");
        group.bench_with_input(BenchmarkId::new("sortedvec", &id), &(), |b, _| {
            b.iter(|| std::hint::black_box(run_sortedvec(&svecs)));
        });
        group.bench_with_input(BenchmarkId::new("bplus256_bin", &id), &(), |b, _| {
            b.iter(|| std::hint::black_box(run_bplus(&trees)));
        });
    }

    group.finish();
}

criterion_group!(benches, bench_leapfrog);
criterion_main!(benches);
