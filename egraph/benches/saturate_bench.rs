// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! End-to-end saturation macro-benchmark.
//!
//! The existing benches are all microbenchmarks over one container or one
//! cursor. This one times the whole driver loop — index rebuild, scheduling,
//! e-matching, RHS instantiation, congruence rebuild — so a change to any of
//! those is visible where it matters. This is the primary end-to-end suite for
//! evaluating saturation performance changes.
//!
//! **How to compare two revisions.** Save a baseline, change the code, compare:
//!
//! ```text
//! cargo bench --bench saturate_bench -- --save-baseline before
//! # ... apply the change ...
//! cargo bench --bench saturate_bench -- --baseline before
//! ```
//!
//! This is deliberately *not* an A/B pair of arms inside one group. Two arms in
//! one criterion group measure heap position and code layout as much as they
//! measure code: same-binary controls made the second-registered arm read ~18%
//! slow purely for being second. Comparing
//! the *same* bench id across two runs holds registration order, predecessor
//! allocations, and call site fixed, so the only difference is the code.
//!
//! Companion: `examples/allocprobe.rs` runs these same workloads under a
//! counting global allocator and prints allocation counts. Counts are
//! deterministic where wall-clock is not, so they confirm that a change which
//! was *supposed* to remove allocations actually did.

use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::apply::{PreparedRule, compile_rewrite};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::registry::RuleRegistry;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::saturate::{saturate, saturate_semi};
use semi_persistent_egraph::surface_ast::{SurfaceCommand, SurfacePattern};

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type Rule = PreparedRule<OpId, SortId, NiraLitVal>;

// ---------------------------------------------------------------------------
// Workload construction
// ---------------------------------------------------------------------------

fn pat(src: &str) -> SurfacePattern {
    let mut p = semi_persistent_egraph::parser::parse_patterns(src).unwrap();
    assert_eq!(p.len(), 1, "expected one pattern in {src:?}");
    p.remove(0)
}

fn rhs_of(src: &str) -> semi_persistent_egraph::ast::RhsTerm {
    let wrapped = format!("(rewrite x {src})");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&wrapped).unwrap();
    match cmds.into_iter().next().unwrap() {
        SurfaceCommand::Rewrite { rhs, .. } => rhs,
        _ => unreachable!("wrapped source is a rewrite"),
    }
}

fn mk(eg: &EG, rr: &mut RuleRegistry<false>, lhs: &str, rhs: &str) -> Rule {
    compile_rewrite(
        "bench",
        lhs,
        rhs,
        &pat(lhs),
        &rhs_of(rhs),
        &[],
        false,
        eg.ops(),
        eg.sorts(),
        rr,
        &NiraModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .expect("bench rule must compile")
}

/// **Plain workload.** Commutativity + associativity of one binary op over a
/// left-deep chain of `leaves` distinct constants. Every node is fixed-arity,
/// so this is the `by_op` / `by_child_pos` join path with no AC machinery: the
/// baseline for A1 (join cursor allocation), A2 (match cloning), A3 (index
/// hashing), A6 (RHS instantiation), and B2 (cursor seek).
///
/// At `leaves = 7` this reaches ~3.2k nodes and ~227k match steps over 8
/// rounds — enough rounds that per-round index rebuild cost is represented,
/// and enough matches that per-match cost dominates per-round cost.
fn plain(leaves: usize) -> (EG, Vec<Rule>) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let consts: Vec<OpId> = (0..leaves)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let f = eg.ops().id_by_name("f").unwrap();
    let mut acc = eg.add(consts[0], &[]);
    for &c in &consts[1..] {
        let leaf = eg.add(c, &[]);
        acc = eg.add(f, &[acc, leaf]);
    }
    eg.rebuild();

    let mut rr = RuleRegistry::<false>::new();
    let rules = vec![
        mk(&eg, &mut rr, "(f a b)", "(f b a)"),
        mk(&eg, &mut rr, "(f (f a b) c)", "(f a (f b c))"),
    ];
    (eg, rules)
}

/// **AC workload.** A wide multiset (`add` of `width` distinct `mul` nodes)
/// matched by a two-element sub-multiset pattern with a rest variable. Each
/// match binds a rest slice of width `width - 2`, so this drives the AC
/// decompose frames (A7) and the `seq_pool`/`mset_pool` span machinery that
/// makes `Match` expensive to clone (A2).
///
/// Growth is steep — `width` 6/10/14 gives ~14k/276k/3.3M match steps at four
/// rounds — so the two sizes below are the useful window: one fast enough for
/// a full criterion sample, one large enough that constant factors show.
fn ac_rules(width: usize) -> (EG, Vec<Rule>) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_mset("add", e, e);
    eg.register_op2("mul", e, e, e);
    let consts: Vec<OpId> = (0..=width)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let add = eg.ops().id_by_name("add").unwrap();
    let mul = eg.ops().id_by_name("mul").unwrap();
    let ids: Vec<ENodeId> = consts.iter().map(|&c| eg.add(c, &[])).collect();
    let muls: Vec<ENodeId> = (0..width)
        .map(|i| eg.add(mul, &[ids[i], ids[i + 1]]))
        .collect();
    eg.add(add, &muls);
    eg.rebuild();

    let mut rr = RuleRegistry::<false>::new();
    let rules = vec![
        mk(
            &eg,
            &mut rr,
            "(add (mul x y) (mul z w) ..r)",
            "(add (mul y x) (mul w z) ..r)",
        ),
        mk(&eg, &mut rr, "(add (mul x y) ..r)", "(add (mul y x) ..r)"),
    ];
    (eg, rules)
}

/// **AC-completion workload** (`cc = true`, no rewrite rules). `pairs`
/// overlapping two-element sums, each equated to a constant. Adjacent sums
/// share an element but neither contains the other, so each adjacent pair is a
/// §4b superposition candidate: the work is entirely `multiset.rs`
/// normalization and `cc.rs` completion, which is what C4 and B3 touch and
/// what nothing else in the bench suite covers.
fn ac_completion(pairs: usize) -> EG {
    let mut eg = EG::from_model(&NiraModel);
    eg.set_cc(true);
    let e = eg.intern_sort("E");
    eg.register_mset("add", e, e);
    let consts: Vec<OpId> = (0..pairs + 3)
        .map(|i| eg.register_op0(&format!("c{i}"), e))
        .collect();
    let add = eg.ops().id_by_name("add").unwrap();
    let ids: Vec<ENodeId> = consts.iter().map(|&c| eg.add(c, &[])).collect();
    for i in 0..pairs {
        let s = eg.add(add, &[ids[i], ids[i + 1]]);
        eg.merge(s, ids[i + 2]);
    }
    // The reducts whose equality completion must derive.
    for i in 0..pairs.saturating_sub(1) {
        eg.add(add, &[ids[i + 2], ids[i + 1]]);
    }
    eg.rebuild();
    eg
}

// ---------------------------------------------------------------------------
// The measured region
// ---------------------------------------------------------------------------

/// Which driver to time. `Naive` rediscovers every match each round; `Semi`
/// runs the k-variant delta decomposition. Both are shipped and both are
/// measured: a change can help one and hurt the other (semi-naive runs k
/// variants per rule, so per-query setup cost is multiplied).
#[derive(Copy, Clone)]
enum Driver {
    Naive,
    Semi,
}

/// Run one saturation to completion and return a value derived from the result,
/// so nothing can be optimized away.
#[inline]
fn run(driver: Driver, eg: &mut EG, rules: &[Rule], limit: usize) -> usize {
    let g = GlobalCtx::<SortId, ENodeId>::new();
    let r = match driver {
        Driver::Naive => saturate(rules, eg, &NiraModel, limit, &g),
        Driver::Semi => saturate_semi(rules, eg, &NiraModel, limit, &g),
    };
    // Fold both the result and the final graph size into the returned value:
    // a change that silently stops saturating would otherwise look like a win.
    r.iterations + eg.node_count() + usize::from(r.saturated)
}

/// Register one `(workload, driver)` pair.
///
/// The setup closure — building the e-graph and compiling the rules — runs
/// outside the timed region via `iter_batched`, so only saturation is timed.
/// `PerIteration` rather than `SmallInput` because these inputs are up to
/// hundreds of thousands of nodes; batching them would measure the allocator's
/// response to holding a batch alive as much as the saturation itself.
fn bench_sat<F>(c: &mut Criterion, id: &str, samples: usize, limit: usize, build: F)
where
    F: Fn() -> (EG, Vec<Rule>),
{
    for (suffix, driver) in [("naive", Driver::Naive), ("semi", Driver::Semi)] {
        let mut group = c.benchmark_group(format!("saturate/{id}/{suffix}"));
        group.sample_size(samples);
        group.bench_function("run", |b| {
            b.iter_batched(
                &build,
                |(mut eg, rules)| std::hint::black_box(run(driver, &mut eg, &rules, limit)),
                criterion::BatchSize::PerIteration,
            );
        });
        group.finish();
    }
}

fn bench_plain(c: &mut Criterion) {
    // ~3.2k nodes, 8 rounds, 227k (naive) / 112k (semi) match steps.
    bench_sat(c, "plain7", 50, 8, || plain(7));
}

fn bench_ac(c: &mut Criterion) {
    // ~83 nodes, 4 rounds, 14k (naive) / 7k (semi) match steps: fast enough
    // for a full sample, so small regressions are resolvable.
    bench_sat(c, "ac6", 50, 4, || ac_rules(6));
    // ~1k nodes, 4 rounds, 276k (naive) / 183k (semi) match steps: large
    // enough that per-match constant factors dominate per-round setup.
    bench_sat(c, "ac10", 10, 4, || ac_rules(10));
}

fn bench_ac_completion(c: &mut Criterion) {
    // Completion runs inside `rebuild`, so one saturation round suffices to
    // drive it to fixpoint; the rule list is empty by construction.
    for pairs in [32usize, 64] {
        let mut group = c.benchmark_group(format!("saturate/accompl{pairs}"));
        group.sample_size(20);
        group.bench_function("run", |b| {
            b.iter_batched(
                || ac_completion(pairs),
                |mut eg| {
                    std::hint::black_box(run(Driver::Naive, &mut eg, &[], 1));
                },
                criterion::BatchSize::PerIteration,
            );
        });
        group.finish();
    }
}

criterion_group!(benches, bench_plain, bench_ac, bench_ac_completion);
criterion_main!(benches);
