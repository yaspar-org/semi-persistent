// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `MatchPool` (per-match slots, nine vectors each) against `MatchSet` (flat
//! stride-packed storage, shared pools) from the CONSUMER's side: populate a
//! query's worth of matches, then read them the way `apply` does — per match,
//! every node and mult binding plus a walk of the multiset rest slice.
//!
//! Both structures are kept warm across iterations (`clear`, not drop), which
//! is the production discipline for the pool and the intended one for the
//! set. Separate bench ids per structure; the same second-arm code-placement
//! caveat as everywhere else (`saturate_bench`'s module doc) applies to
//! cross-arm reading, so treat the pool-vs-set gap as the signal and the
//! absolute times as machine-local.

use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_egraph::ematch::{Match, MatchPool, MatchSet};
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::multiplicity::MultiplicityLike;
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::MatchShape;
use std::hint::black_box;

type Cfg = DefaultConfig;

const NODE_VARS: usize = 4;
const MULT_VARS: usize = 2;
const REST_LEN: usize = 10;

fn shape() -> MatchShape {
    let mut s = MatchShape::default();
    for i in 0..NODE_VARS {
        s.intern_var(&format!("x{i}")).unwrap();
    }
    for i in 0..MULT_VARS {
        s.intern_mult(&format!("m{i}")).unwrap();
    }
    s.intern_mset("rest").unwrap();
    s
}

fn id(n: usize) -> ENodeId {
    ENodeId::new(n as u32)
}

/// One in-progress env, bound the way the matcher leaves it: every node and
/// mult var set, the rest var holding `REST_LEN` packed children.
fn env_for(shape: &MatchShape, j: usize) -> Match<Cfg> {
    let mut env = Match::new(shape);
    for (k, v) in shape.var_ids().enumerate() {
        env.set(v, id(j * NODE_VARS + k));
    }
    for v in shape.mult_var_ids() {
        env.set_mult(
            v,
            <Cfg as semi_persistent_egraph::config::EGraphConfig>::M::ONE,
        );
    }
    let rv = shape.mset_var_ids().next().unwrap();
    let rest: Vec<_> = (0..REST_LEN)
        .map(|k| {
            <Cfg as semi_persistent_egraph::config::EGraphConfig>::mset_child_with_mult(
                id(j + k),
                <Cfg as semi_persistent_egraph::config::EGraphConfig>::M::ONE,
            )
        })
        .collect();
    env.push_mset(rv, &rest);
    env
}

/// The pool arm reads through `clone_match`-free row reconstruction is not
/// available on `&MatchPool`; post-E17 the pool IS set-backed, so this arm
/// measures the pooled store (loan buffers included) against the bare set.
fn consume_pool(pool: &mut MatchPool<Cfg>, shape: &MatchShape) -> u64 {
    let rv = shape.mset_var_ids().next().unwrap();
    let mut acc = 0u64;
    for j in 0..pool.len() {
        let row = pool.row_mut(j);
        use semi_persistent_egraph::ematch::MatchView;
        for v in shape.var_ids() {
            acc ^= MatchView::get(&row, v).to_usize() as u64;
        }
        for c in MatchView::mset_slice(&row, rv) {
            acc = acc.wrapping_add(black_box(*c).a.to_usize() as u64);
        }
    }
    acc
}

fn consume_set(set: &MatchSet<Cfg>, shape: &MatchShape) -> u64 {
    let rv = shape.mset_var_ids().next().unwrap();
    let mut acc = 0u64;
    for j in 0..set.len() {
        for v in shape.var_ids() {
            acc ^= set.get_node(v, j).to_usize() as u64;
        }
        for c in set.mset_slice(rv, j) {
            acc = acc.wrapping_add(black_box(*c).a.to_usize() as u64);
        }
    }
    acc
}

fn bench(c: &mut Criterion) {
    let shape = shape();
    for &m_count in &[1024usize, 16384] {
        // pre-built envs: population cost measured is the STORE's, not the
        // matcher's.
        let envs: Vec<Match<Cfg>> = (0..m_count).map(|j| env_for(&shape, j)).collect();

        let mut g = c.benchmark_group(format!("matchset/{m_count}"));

        g.bench_function("pool/populate", |b| {
            let mut pool: MatchPool<Cfg> = MatchPool::new();
            pool.reshape(&shape);
            b.iter(|| {
                pool.clear();
                for e in &envs {
                    pool.push(e);
                }
                black_box(pool.len())
            })
        });
        g.bench_function("set/populate", |b| {
            let mut set: MatchSet<Cfg> = MatchSet::new(&shape);
            b.iter(|| {
                set.clear();
                for e in &envs {
                    set.push(e);
                }
                black_box(set.len())
            })
        });

        let mut pool: MatchPool<Cfg> = MatchPool::new();
        pool.reshape(&shape);
        for e in &envs {
            pool.push(e);
        }
        let mut set: MatchSet<Cfg> = MatchSet::new(&shape);
        for e in &envs {
            set.push(e);
        }
        g.bench_function("pool/consume", |b| {
            b.iter(|| black_box(consume_pool(&mut pool, &shape)))
        });
        g.bench_function("set/consume", |b| {
            b.iter(|| black_box(consume_set(&set, &shape)))
        });

        g.finish();
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
