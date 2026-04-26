// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Benchmarks across memo strategies and dedup modes.
//!
//! Two groups, both on a balanced Add(Lit) tree of varying depth:
//!
//! - `fold`: cost to fold an already-built store.
//!     • dense   — default memo strategy
//!     • sparse  — hashmap-backed, O(reachable) memo
//!     • none    — no memo, stack-based (incorrect on DAGs)
//!
//! - `build`: cost to construct a tree with lots of structural redundancy,
//!   comparing plain push vs hash-consed push (`new_dedup`). All leaves are
//!   `Lit(1)`; with dedup the whole tree collapses to d+1 unique nodes.

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use semi_persistent_traversals::{Dense, Sparse, memo};
use semi_persistent_traversals_derive::rec_family;
use std::hint::black_box;

rec_family! {
    family Lang => LangStore;
    enum Stmt { Noop, Print(Expr) }
    enum Expr { Lit(i64), Add(Expr, Expr) }
}

// ---------------------------------------------------------------------------
// Builder — balanced Add tree of depth d, all leaves Lit(1)
// ---------------------------------------------------------------------------

fn build(s: &mut LangStore, depth: u32) -> ExprId {
    if depth == 0 {
        s.push_expr(ExprNode::Lit(1))
    } else {
        let l = build(s, depth - 1);
        let r = build(s, depth - 1);
        s.push_expr(ExprNode::Add(l, r))
    }
}

// ---------------------------------------------------------------------------
// Fold under a given strategy M
// ---------------------------------------------------------------------------

fn fold_with<M: semi_persistent_traversals::MemoStrategy>(s: &LangStore, root: LangStoreRoot) -> i64 {
    let r = s.with_strategy::<M>().fold(
        root,
        |_: StmtNodeMapped<i64>| 0i64,
        |expr: ExprNodeMapped<i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
        },
    );
    match r {
        LangStoreFoldResult::Expr(v) => v,
        LangStoreFoldResult::Stmt(v) => v,
    }
}

// ---------------------------------------------------------------------------
// Fold benchmarks
// ---------------------------------------------------------------------------

fn bench_fold(c: &mut Criterion) {
    let mut group = c.benchmark_group("fold");

    for depth in [10u32, 14, 18] {
        let node_count: usize = (1usize << (depth + 1)) - 1;
        group.throughput(Throughput::Elements(node_count as u64));

        let mut s = LangStore::new();
        let root = LangStoreRoot::Expr(build(&mut s, depth));

        group.bench_with_input(BenchmarkId::new("dense", depth), &depth, |b, _| {
            b.iter(|| black_box(fold_with::<Dense>(black_box(&s), black_box(root))))
        });

        group.bench_with_input(BenchmarkId::new("sparse", depth), &depth, |b, _| {
            b.iter(|| black_box(fold_with::<Sparse>(black_box(&s), black_box(root))))
        });

        group.bench_with_input(BenchmarkId::new("none", depth), &depth, |b, _| {
            b.iter(|| black_box(fold_with::<memo::None>(black_box(&s), black_box(root))))
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Build benchmarks: plain vs hash-consed construction
// ---------------------------------------------------------------------------

fn bench_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("build");

    for depth in [10u32, 14, 18] {
        let push_calls: usize = (1usize << (depth + 1)) - 1;
        group.throughput(Throughput::Elements(push_calls as u64));

        group.bench_with_input(BenchmarkId::new("plain", depth), &depth, |b, &d| {
            b.iter(|| {
                let mut s = LangStore::new();
                black_box(build(&mut s, d));
                black_box(s);
            })
        });

        group.bench_with_input(BenchmarkId::new("dedup", depth), &depth, |b, &d| {
            b.iter(|| {
                let mut s = LangStore::new_dedup();
                black_box(build(&mut s, d));
                black_box(s);
            })
        });
    }
    group.finish();
}

criterion_group!(benches, bench_fold, bench_build);
criterion_main!(benches);
