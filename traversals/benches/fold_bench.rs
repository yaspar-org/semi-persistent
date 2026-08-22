// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Benchmarks across memo strategies and dedup modes.
//!
//! Four groups:
//!
//! - `fold`: cost to fold an already-built store.
//!   • dense   — default memo strategy
//!   • sparse  — hashmap-backed, O(reachable) memo
//!   • none    — no memo, stack-based (incorrect on DAGs)
//!
//! - `build`: cost to construct a tree with lots of structural redundancy,
//!   comparing plain push vs hash-consed push (`new_dedup`). All leaves are
//!   `Lit(1)`; with dedup the whole tree collapses to d+1 unique nodes.
//!
//! - `focused_fold`: cost to fold a 2,047-node subtree in a store with
//!   1,000,000 nodes, comparing dense and sparse memo allocation.
//!
//! - `variadic_build`: cost of 256 pool-backed smart-constructor calls
//!   for short inline-sized and wider child slices, split into plain
//!   insertion, dedup hits, and dedup misses.

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use semi_persistent_traversals::{Dense, Sparse, memo};
use semi_persistent_traversals_derive::rec_family;
use std::hint::black_box;

rec_family! {
    family Lang => LangStore;
    enum Stmt { Noop, Print(Expr) }
    enum Expr { Lit(i64), Add(Expr, Expr) }
}

rec_family! {
    #[smart_constructors]
    family VariadicLang => VariadicLangStore;
    enum BenchRoot { Program(Variadic<BenchExpr>) }
    enum BenchExpr { Lit(u64), Sum(Variadic<BenchExpr>) }
}

// ---------------------------------------------------------------------------
// Builder — balanced Add tree of depth d, all leaves Lit(1)
// ---------------------------------------------------------------------------

fn build<const DEDUP: bool>(s: &mut LangStore<DEDUP>, depth: u32) -> ExprId {
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

fn fold_with<M: semi_persistent_traversals::MemoStrategy>(
    s: &LangStore,
    root: LangStoreRoot,
) -> i64 {
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

// ---------------------------------------------------------------------------
// Variadic smart-constructor benchmarks
// ---------------------------------------------------------------------------

const VARIADIC_PUSHES: usize = 256;

fn setup_variadic_plain(arity: usize) -> (VariadicLangStore, Vec<BenchExprId>) {
    let mut store = VariadicLangStore::new();
    let children = (0..arity).map(|value| store.lit(value as u64)).collect();
    (store, children)
}

fn setup_variadic_dedup(arity: usize) -> (VariadicLangStore<true>, Vec<BenchExprId>) {
    let mut store = VariadicLangStore::new_dedup();
    let children: Vec<_> = (0..arity).map(|value| store.lit(value as u64)).collect();
    store.sum(&children);
    (store, children)
}

fn setup_variadic_dedup_misses(arity: usize) -> (VariadicLangStore<true>, Vec<Vec<BenchExprId>>) {
    let mut store = VariadicLangStore::new_dedup();
    let leaves: Vec<_> = (0..(VARIADIC_PUSHES + arity))
        .map(|value| store.lit(value as u64))
        .collect();
    let candidates = (0..VARIADIC_PUSHES)
        .map(|offset| leaves[offset..offset + arity].to_vec())
        .collect();
    (store, candidates)
}

fn bench_variadic_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("variadic_build");
    group.throughput(Throughput::Elements(VARIADIC_PUSHES as u64));

    for arity in [4usize, 16] {
        group.bench_with_input(BenchmarkId::new("plain", arity), &arity, |b, &arity| {
            b.iter_batched(
                || setup_variadic_plain(arity),
                |(mut store, children)| {
                    for _ in 0..VARIADIC_PUSHES {
                        black_box(store.sum(black_box(&children)));
                    }
                    black_box(store);
                },
                BatchSize::SmallInput,
            );
        });

        group.bench_with_input(BenchmarkId::new("dedup_hit", arity), &arity, |b, &arity| {
            b.iter_batched(
                || setup_variadic_dedup(arity),
                |(mut store, children)| {
                    for _ in 0..VARIADIC_PUSHES {
                        black_box(store.sum(black_box(&children)));
                    }
                    black_box(store);
                },
                BatchSize::SmallInput,
            );
        });

        group.bench_with_input(
            BenchmarkId::new("dedup_miss", arity),
            &arity,
            |b, &arity| {
                b.iter_batched(
                    || setup_variadic_dedup_misses(arity),
                    |(mut store, candidates)| {
                        for children in candidates {
                            black_box(store.sum(black_box(&children)));
                        }
                        black_box(store);
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Focused fold: small reachable subtree in a much larger store
// ---------------------------------------------------------------------------

fn bench_focused_fold(c: &mut Criterion) {
    const STORE_NODES: usize = 1_000_000;
    const SUBTREE_DEPTH: u32 = 10;
    const SUBTREE_NODES: usize = (1usize << (SUBTREE_DEPTH + 1)) - 1;

    let mut store = LangStore::new();
    for value in 0..(STORE_NODES - SUBTREE_NODES) {
        store.push_expr(ExprNode::Lit(value as i64));
    }
    let root = LangStoreRoot::Expr(build(&mut store, SUBTREE_DEPTH));
    assert_eq!(store.len_expr(), STORE_NODES);

    let mut group = c.benchmark_group("focused_fold");
    group.throughput(Throughput::Elements(SUBTREE_NODES as u64));
    group.bench_function("dense", |b| {
        b.iter(|| black_box(fold_with::<Dense>(black_box(&store), black_box(root))))
    });
    group.bench_function("sparse", |b| {
        b.iter(|| black_box(fold_with::<Sparse>(black_box(&store), black_box(root))))
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_fold,
    bench_build,
    bench_variadic_build,
    bench_focused_fold
);
criterion_main!(benches);
