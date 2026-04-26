// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Benchmarks across storage layouts and strategies.
//!
//! Two groups:
//!
//! - `fold`: cost to fold an already-built AST.
//!     • single_arena       — Arena<Lang<usize, usize>>, dense memo
//!     • partitioned_dense  — LangStore, dense memo
//!     • partitioned_sparse — LangStore, sparse (hashmap) memo
//!
//! - `build`: cost to construct an AST with lots of structural redundancy,
//!   comparing plain push vs hash-consed push. The input is a balanced Add
//!   tree where every leaf is Lit(1); with dedup, the whole tree collapses
//!   to d+1 unique nodes.
//!     • single_plain  — Arena<Lang<_,_>>::new().push
//!     • single_dedup  — HcArena<Lang<_,_>>::new_dedup().push
//!     • partitioned_plain — LangStore::new().push_*
//!     • partitioned_dedup — LangStore::new_dedup().push_*

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use semi_persistent_traversals::{Arena, Dense, HcArena, Id, Sparse};
use semi_persistent_traversals_derive::{partition, rec_family};
use std::hint::black_box;

// ---------------------------------------------------------------------------
// Shared family (used by both layouts via the two macros)
// ---------------------------------------------------------------------------

rec_family! {
    family Lang;
    enum Stmt { Noop, Print(Expr) }
    enum Expr { Lit(i64), Add(Expr, Expr) }
}

partition! {
    family LangP => LangStore;
    enum Stmt { Noop, Print(Expr) }
    enum Expr { Lit(i64), Add(Expr, Expr) }
}

// ---------------------------------------------------------------------------
// Builders — balanced Add tree of depth d, all leaves Lit(1)
// ---------------------------------------------------------------------------

fn build_single<const DEDUP: bool>(a: &mut Arena<Lang<usize, usize>, DEDUP>, depth: u32) -> Id
where
    Lang<usize, usize>: Clone + semi_persistent_traversals::Functor<usize, Mapped<usize> = Lang<usize, usize>> + Eq + std::hash::Hash + semi_persistent_traversals::HasVariadic,
{
    if depth == 0 {
        a.push(Expr::Lit(1).into())
    } else {
        let l = build_single(a, depth - 1);
        let r = build_single(a, depth - 1);
        a.push(Expr::Add(l.0, r.0).into())
    }
}

fn build_partitioned(s: &mut LangStore, depth: u32) -> ExprId {
    if depth == 0 {
        s.push_expr(ExprNode::Lit(1))
    } else {
        let l = build_partitioned(s, depth - 1);
        let r = build_partitioned(s, depth - 1);
        s.push_expr(ExprNode::Add(l, r))
    }
}

// ---------------------------------------------------------------------------
// Fold closures
// ---------------------------------------------------------------------------

fn fold_single(a: &Arena<Lang<usize, usize>>, root: Id) -> i64 {
    a.fold(root, |node: Lang<i64, i64>| {
        node.dispatch(
            |_| 0,
            |expr| match expr {
                Expr::Lit(n) => n,
                Expr::Add(l, r) => l + r,
            },
        )
    })
}

fn fold_partitioned_dense(s: &LangStore, root: LangStoreRoot) -> i64 {
    let r = s.with_strategy::<Dense>().fold(
        root,
        |_: StmtNodeMapped<i64>| 0i64,
        |expr: ExprNodeMapped<i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
        },
    );
    match r { LangStoreFoldResult::Expr(v) => v, LangStoreFoldResult::Stmt(v) => v }
}

fn fold_partitioned_sparse(s: &LangStore, root: LangStoreRoot) -> i64 {
    let r = s.with_strategy::<Sparse>().fold(
        root,
        |_: StmtNodeMapped<i64>| 0i64,
        |expr: ExprNodeMapped<i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
        },
    );
    match r { LangStoreFoldResult::Expr(v) => v, LangStoreFoldResult::Stmt(v) => v }
}

// ---------------------------------------------------------------------------
// Fold benchmarks
// ---------------------------------------------------------------------------

fn bench_fold(c: &mut Criterion) {
    let mut group = c.benchmark_group("fold");

    for depth in [10u32, 14, 18] {
        let node_count: usize = (1usize << (depth + 1)) - 1;
        group.throughput(Throughput::Elements(node_count as u64));

        let mut single = Arena::<Lang<usize, usize>>::new();
        let single_root = build_single(&mut single, depth);

        let mut part = LangStore::new();
        let part_root = LangStoreRoot::Expr(build_partitioned(&mut part, depth));

        group.bench_with_input(BenchmarkId::new("single_arena", depth), &depth, |b, _| {
            b.iter(|| black_box(fold_single(black_box(&single), black_box(single_root))))
        });

        group.bench_with_input(BenchmarkId::new("partitioned_dense", depth), &depth, |b, _| {
            b.iter(|| black_box(fold_partitioned_dense(black_box(&part), black_box(part_root))))
        });

        group.bench_with_input(BenchmarkId::new("partitioned_sparse", depth), &depth, |b, _| {
            b.iter(|| black_box(fold_partitioned_sparse(black_box(&part), black_box(part_root))))
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
        // Work units = number of push_* calls the builder makes (2^(d+1) - 1).
        let push_calls: usize = (1usize << (depth + 1)) - 1;
        group.throughput(Throughput::Elements(push_calls as u64));

        group.bench_with_input(BenchmarkId::new("single_plain", depth), &depth, |b, &d| {
            b.iter(|| {
                let mut a = Arena::<Lang<usize, usize>>::new();
                black_box(build_single(&mut a, d));
                black_box(a);
            })
        });

        group.bench_with_input(BenchmarkId::new("single_dedup", depth), &depth, |b, &d| {
            b.iter(|| {
                let mut a: HcArena<Lang<usize, usize>> = HcArena::new_dedup();
                black_box(build_single(&mut a, d));
                black_box(a);
            })
        });

        group.bench_with_input(BenchmarkId::new("partitioned_plain", depth), &depth, |b, &d| {
            b.iter(|| {
                let mut s = LangStore::new();
                black_box(build_partitioned(&mut s, d));
                black_box(s);
            })
        });

        group.bench_with_input(BenchmarkId::new("partitioned_dedup", depth), &depth, |b, &d| {
            b.iter(|| {
                let mut s = LangStore::new_dedup();
                black_box(build_partitioned(&mut s, d));
                black_box(s);
            })
        });
    }
    group.finish();
}

criterion_group!(benches, bench_fold, bench_build);
criterion_main!(benches);
