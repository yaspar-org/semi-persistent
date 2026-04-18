// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_egraph::DenseId;
use semi_persistent_egraph::containers::VecI;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::lca::{LcaTable, LcaTableCompact};

/// Build a random tree of `n` nodes. Node 0 is root.
/// Each node i > 0 gets a random parent in 0..i.
fn random_tree(n: usize, seed: u64) -> VecI<ENodeId, u32, false> {
    let mut pp = VecI::<ENodeId, u32, false>::new();
    pp.push(ENodeId::new(0)); // root
    let mut rng = seed;
    for i in 1..n {
        // xorshift64
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        let parent = (rng as usize) % i;
        pp.push(ENodeId::new(parent as u32));
    }
    pp
}

/// Generate `count` random query pairs in 0..n.
fn random_queries(n: usize, count: usize, seed: u64) -> Vec<(ENodeId, ENodeId)> {
    let mut rng = seed;
    let mut queries = Vec::with_capacity(count);
    for _ in 0..count {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        let a = (rng as usize) % n;
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        let b = (rng as usize) % n;
        queries.push((ENodeId::from_usize(a), ENodeId::from_usize(b)));
    }
    queries
}

fn bench_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("lca_build");
    for &n in &[1_000, 10_000, 100_000] {
        let pp = random_tree(n, 42);
        group.bench_with_input(BenchmarkId::new("full", n), &n, |b, &n| {
            b.iter(|| LcaTable::build(&pp, n));
        });
        group.bench_with_input(BenchmarkId::new("compact", n), &n, |b, &n| {
            b.iter(|| LcaTableCompact::build(&pp, n));
        });
    }
    group.finish();
}

fn bench_query(c: &mut Criterion) {
    let mut group = c.benchmark_group("lca_query");
    let num_queries = 10_000;
    for &n in &[1_000, 10_000, 100_000] {
        let pp = random_tree(n, 42);
        let queries = random_queries(n, num_queries, 123);

        let table_full = LcaTable::build(&pp, n);
        group.bench_with_input(BenchmarkId::new("full", n), &n, |b, _| {
            b.iter(|| {
                for &(a, q_b) in &queries {
                    std::hint::black_box(table_full.lca(a, q_b));
                }
            });
        });

        let table_compact = LcaTableCompact::build(&pp, n);
        group.bench_with_input(BenchmarkId::new("compact", n), &n, |b, _| {
            b.iter(|| {
                for &(a, q_b) in &queries {
                    std::hint::black_box(table_compact.lca(a, q_b));
                }
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_build, bench_query);
criterion_main!(benches);
