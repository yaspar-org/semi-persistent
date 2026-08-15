// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Extraction benchmark: `extract::extract_best` end to end.
//!
//! `saturate_bench.rs` never calls extraction, so the experiments that touch
//! `extract.rs` (A4 dense-id vectors, C2 reconstruct memoization, C3 worklist
//! fixpoint) have nothing to be measured against without this.
//!
//! Three workload shapes, because the experiments pull in different directions
//! and a change that helps one can hurt another:
//!
//! - **`tree`** — a left-deep chain, every class reached once. The control:
//!   memoization has nothing to save here, so this is where C2 would show a
//!   regression if its bookkeeping cost more than it saved.
//! - **`dag`** — `x_{i+1} = f(x_i, x_i)`, so class `i` is reachable by `2^(d-i)`
//!   paths. `reconstruct` has no memo, so it rebuilds each one: this is
//!   exponential in depth and is the worst case C2 exists to fix. Depth is kept
//!   to 16 for that reason — at 30 the baseline does not finish.
//! - **`wide`** — many small classes with alternatives, to exercise the
//!   `extract_best` fixpoint (A4, C3) rather than `reconstruct`.
//!
//! Compare the same bench id across two runs, never two arms of one group; see
//! the note in `saturate_bench.rs`.

use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::extract::extract_best;
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

/// Left-deep chain of `depth` applications over distinct leaves.
fn tree(depth: usize) -> (EG, ENodeId) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let f = eg.ops().id_by_name("f").unwrap();
    let leaves: Vec<OpId> = (0..=depth)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let mut acc = eg.add(leaves[0], &[]);
    for &c in &leaves[1..] {
        let leaf = eg.add(c, &[]);
        acc = eg.add(f, &[acc, leaf]);
    }
    eg.rebuild();
    (eg, acc)
}

/// `x_0 = c`, `x_{i+1} = f(x_i, x_i)`. Only `depth + 1` classes, but the root's
/// term has `2^depth` leaves — the shared-subterm case.
fn dag(depth: usize) -> (EG, ENodeId) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let c = eg.register_op0("c", e);
    let f = eg.ops().id_by_name("f").unwrap();
    let mut acc = eg.add(c, &[]);
    for _ in 0..depth {
        acc = eg.add(f, &[acc, acc]);
    }
    eg.rebuild();
    (eg, acc)
}

/// `width` independent two-argument nodes over shared leaves, all merged into
/// one class, so `extract_best` must compare `width` alternatives per pass.
fn wide(width: usize) -> (EG, ENodeId) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    eg.register_op2("g", e, e, e);
    let f = eg.ops().id_by_name("f").unwrap();
    let g = eg.ops().id_by_name("g").unwrap();
    let leaves: Vec<ENodeId> = (0..width)
        .map(|i| {
            let op = eg.register_op0(&format!("c{i}"), e);
            eg.add(op, &[])
        })
        .collect();
    // A chain of `g` nodes gives the alternatives different costs, so the
    // fixpoint actually has to propagate improvements rather than settle in one
    // pass.
    let mut chain = leaves[0];
    for &l in &leaves[1..] {
        chain = eg.add(g, &[chain, l]);
    }
    let root = eg.add(f, &[leaves[0], chain]);
    for &l in &leaves[1..] {
        let alt = eg.add(f, &[l, chain]);
        eg.merge(root, alt);
    }
    eg.rebuild();
    (eg, root)
}

fn bench_extract(c: &mut Criterion) {
    for (id, depth) in [("tree20", 20usize), ("tree200", 200)] {
        let (eg, root) = tree(depth);
        let mut group = c.benchmark_group(format!("extract/{id}"));
        group.bench_function("run", |b| {
            b.iter(|| std::hint::black_box(extract_best(&eg, root).is_ok()));
        });
        group.finish();
    }
    // Depth 16 is ~65k leaves in the reconstructed term and ~150 ms per
    // iteration; every further step doubles both. Depth 18 was tried and
    // rejected — its per-sample spread was 683 ms to 1.12 s, because a term
    // that large makes each iteration's allocate-and-drop dominate. 16 keeps
    // the exponential visible with a spread small enough to measure against.
    for (id, depth) in [("dag12", 12usize), ("dag16", 16)] {
        let (eg, root) = dag(depth);
        let mut group = c.benchmark_group(format!("extract/{id}"));
        group.sample_size(20);
        group.bench_function("run", |b| {
            b.iter(|| std::hint::black_box(extract_best(&eg, root).is_ok()));
        });
        group.finish();
    }
    for (id, width) in [("wide32", 32usize), ("wide128", 128)] {
        let (eg, root) = wide(width);
        let mut group = c.benchmark_group(format!("extract/{id}"));
        group.sample_size(20);
        group.bench_function("run", |b| {
            b.iter(|| std::hint::black_box(extract_best(&eg, root).is_ok()));
        });
        group.finish();
    }
}

criterion_group!(benches, bench_extract);
criterion_main!(benches);
