// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The workload that separates a mean fan-out from a sampled one (design
//! chapter 20, S5).
//!
//! **The shape.** `(d v) (pr v z) (alt v w)`: a cheap driver `d` over `leaves`
//! distinct classes, and two candidates for the second join, both keyed on the
//! class `v` that `d` binds.
//!
//! `pr` is the selective one. It has a node over each of the first `hits`
//! leaves and nothing over the rest, so a probe from `d` returns one node on
//! `hits`/`leaves` of the bindings and nothing on the others. It also has
//! `distractors` nodes hanging off one hub class that `d` never points at.
//! Those never take part in a match, but they are what the round's size-biased
//! mean of the `by_child_pos` path measures: the mean is the bucket a probe
//! lands in weighted by bucket size, and the hub bucket outweighs every leaf
//! bucket together. So the mean prices `pr`'s probe at roughly `distractors`
//! where its true value from this driver is under one.
//!
//! `alt` is the unselective one, and honestly priced: `fan` nodes over each
//! leaf that `pr` does not cover, one node over each leaf it does.
//!
//! The mean therefore orders `d`, `alt`, `pr` — it takes `alt`'s 64 over `pr`'s
//! 4 000 — and walks `fan` `alt` nodes on every binding that has no match at
//! all. Sampling reads the true joint distribution off the driver's own nodes,
//! prices `pr` under one, and orders `d`, `pr`, `alt`.
//!
//! The measurement is match steps: load-independent, so it holds in every build
//! profile, following the S4 gate in `ematch_runtime_schedule`.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::ematch::{
    match_steps, reset_match_steps, run_query, set_match_step_counting,
};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::index::{IndexSampler, IndexStore, VariantIndex};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::{GlobalCtx, ResolvedQuery};
use semi_persistent_egraph::schedule::{
    IndexStats, QueryPlan, SamplerConfig, Step, reset_sample_tally, sample_tally,
    schedule_with_stats_sampled, set_sampled_selectivity,
};
use std::time::Instant;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type RQ = ResolvedQuery<OpId, SortId, NiraLitVal>;
type Plan = QueryPlan<OpId, u32, NiraLitVal>;

// ---------------------------------------------------------------------------
// The shape
// ---------------------------------------------------------------------------

/// Build the anti-correlated shape and compile its query.
///
/// Returns the e-graph, the resolved query, and the number of matches the shape
/// admits (`hits`, one per covered leaf, each with its single `alt` node).
fn s5_shape(leaves: usize, hits: usize, fan: usize, distractors: usize) -> (EG, RQ, usize) {
    assert!(hits < leaves);
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op0("leaf", e);
    eg.register_op1("s", e, e);
    eg.register_op1("d", e, e);
    eg.register_op2("pr", e, e, e);
    eg.register_op2("alt", e, e, e);
    let s = eg.ops().id_by_name("s").unwrap();
    let d = eg.ops().id_by_name("d").unwrap();
    let pr = eg.ops().id_by_name("pr").unwrap();
    let alt = eg.ops().id_by_name("alt").unwrap();

    // Distinct classes, as one `s` chain: cheaper than registering thousands of
    // nullary operators. The first `leaves` of them carry the shape; the rest
    // are second children, which the query leaves free.
    let fillers = distractors.max(fan).max(1);
    let mut cls: Vec<ENodeId> = Vec::with_capacity(leaves + fillers + 2);
    cls.push(eg.add(eg.ops().id_by_name("leaf").unwrap(), &[]));
    for i in 1..leaves + fillers + 2 {
        let prev = cls[i - 1];
        cls.push(eg.add(s, &[prev]));
    }
    let hub = cls[leaves];
    let filler = &cls[leaves + 1..];

    for (i, &c) in cls.iter().take(leaves).enumerate() {
        eg.add(d, &[c]);
        if i < hits {
            eg.add(pr, &[c, filler[0]]);
            eg.add(alt, &[c, filler[0]]);
        } else {
            for &w in &filler[..fan] {
                eg.add(alt, &[c, w]);
            }
        }
    }
    // The hub: `pr` nodes the driver can never reach, which set the mean.
    for &z in &filler[..distractors] {
        eg.add(pr, &[hub, z]);
    }
    eg.rebuild();

    let pats = semi_persistent_egraph::parser::parse_patterns("(d v) (pr v z) (alt v w)").unwrap();
    let fq = semi_persistent_egraph::sortcheck::flatten_surface(&pats, eg.ops()).unwrap();
    let rq = semi_persistent_egraph::resolve::resolve(
        &fq,
        eg.ops(),
        eg.sorts(),
        &NiraModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .unwrap();
    (eg, rq, hits)
}

/// Schedule the query from the round's statistics — the same input the
/// saturation driver gives the scheduler — with sampling on or off.
fn plan_with(eg: &EG, rq: &RQ, cfg: Option<SamplerConfig>) -> Plan {
    let index = IndexStore::build(eg);
    let vindex = VariantIndex::naive(&index);
    let sampler = IndexSampler::new(eg, vindex);
    let stats = IndexStats::from_index(&index);
    set_sampled_selectivity(cfg);
    let plan = schedule_with_stats_sampled(rq, &stats, &sampler);
    set_sampled_selectivity(None);
    plan
}

/// The atom order the plan commits to, one entry per join.
fn order(plan: &Plan) -> Vec<usize> {
    plan.steps
        .iter()
        .filter_map(|s| match s {
            Step::Join { atom_id, .. } => Some(*atom_id),
            _ => None,
        })
        .collect()
}

/// Run the plan; return its match count and match steps.
fn run(eg: &EG, plan: &Plan) -> (usize, u64) {
    let full = IndexStore::build(eg);
    let vindex = VariantIndex::naive(&full);
    let globals = GlobalCtx::<SortId, ENodeId>::new();
    set_match_step_counting(true);
    reset_match_steps();
    let matches = run_query(plan, eg, &vindex, &globals).len();
    (matches, match_steps())
}

// ---------------------------------------------------------------------------
// The gate
// ---------------------------------------------------------------------------

/// `leaves / hits` is `k`, so the emitter stride resolves the selective side
/// exactly: one of the 32 drawn driver nodes points at a covered leaf, which is
/// the true fraction and not a rounding of it. The order the test asserts holds
/// well away from that point — the sampled price of `pr` is under one wherever
/// the draw finds at most a few covered leaves — but the estimate is worth
/// stating at a ratio where it is exact.
const LEAVES: usize = 1024;
const HITS: usize = 32;
const FAN: usize = 64;
const DISTRACTORS: usize = 4096;

/// Sampling picks the selective probe and costs under a third of the mean's
/// match steps on the anti-correlated shape.
///
/// The mean's order walks `fan` `alt` nodes on each of the `leaves - hits`
/// bindings that cannot match; the sampled order opens the empty `pr` bucket
/// first and stops. Stated at 3x against a measured 86x so that it fails on a
/// regression rather than on noise; timing-free, so it holds in every profile.
#[test]
fn sampled_selectivity_cuts_steps_on_the_anticorrelated_shape() {
    let (eg, rq, expect) = s5_shape(LEAVES, HITS, FAN, DISTRACTORS);
    let off = plan_with(&eg, &rq, None);
    let on = plan_with(&eg, &rq, Some(SamplerConfig::default()));

    assert_eq!(
        order(&off),
        vec![0, 2, 1],
        "the mean must drive from `d` and take `alt` second"
    );
    assert_eq!(
        order(&on),
        vec![0, 1, 2],
        "sampling must drive from `d` and take `pr` second"
    );

    let (m_off, steps_off) = run(&eg, &off);
    let (m_on, steps_on) = run(&eg, &on);
    assert_eq!(
        (m_off, m_on),
        (expect, expect),
        "the two orders must agree on the match set"
    );
    println!("steps: mean {steps_off}, sampled {steps_on}");
    assert!(
        steps_on * 3 < steps_off,
        "expected sampled selectivity to cost under a third of the mean's \
         steps, measured {steps_on} against {steps_off}"
    );
}

/// The match set is the same under both estimators across the shape's
/// parameters, including the ones the step gate does not run at. Sampling
/// changes the plan's atom order and nothing else, and an order is a
/// permutation of the same conjunction against the same index snapshot.
#[test]
fn both_estimators_agree_on_the_match_set() {
    for (leaves, hits, fan, distractors) in [
        (256usize, 8usize, 16usize, 512usize),
        (128, 64, 4, 0),
        (64, 1, 32, 64),
        (512, 16, 1, 8192),
    ] {
        let (eg, rq, expect) = s5_shape(leaves, hits, fan, distractors);
        let off = plan_with(&eg, &rq, None);
        let on = plan_with(&eg, &rq, Some(SamplerConfig::default()));
        let (m_off, _) = run(&eg, &off);
        let (m_on, _) = run(&eg, &on);
        assert_eq!(
            (m_off, m_on),
            (expect, expect),
            "leaves={leaves} hits={hits} fan={fan} distractors={distractors}"
        );
    }
}

/// The bootstrap guard rejects a draw whose mean is decided by a few of its
/// entries, and the plan falls back to the mean model.
///
/// At `hits = 1` exactly one of the 32 drawn driver nodes points at a covered
/// leaf, so the resampled means scatter as widely as the estimate itself: the
/// coefficient of variation is about 1, and a threshold under that rejects it.
/// The same draw at the default threshold is accepted, which is what makes this
/// a statement about the guard rather than about the draw.
#[test]
fn the_bootstrap_guard_rejects_a_draw_one_sample_decides() {
    let (eg, rq, _) = s5_shape(LEAVES, 1, FAN, DISTRACTORS);
    let strict = SamplerConfig {
        k: 32,
        bootstrap: 200,
        cv_threshold: 0.5,
    };
    let loose = SamplerConfig {
        cv_threshold: 4.0,
        ..strict
    };
    reset_sample_tally();
    assert_eq!(
        order(&plan_with(&eg, &rq, Some(strict))),
        order(&plan_with(&eg, &rq, None)),
        "a rejected estimate must leave the mean's order"
    );
    let (taken, rejected) = sample_tally();
    assert!(
        rejected > 0 && rejected <= taken,
        "the guard must have fired: {rejected} of {taken}"
    );

    reset_sample_tally();
    assert_eq!(
        order(&plan_with(&eg, &rq, Some(loose))),
        vec![0, 1, 2],
        "the same draw under a loose threshold must keep the sampled order"
    );
    assert_eq!(
        sample_tally().1,
        0,
        "a loose threshold must reject nothing on the same draw"
    );
}

// ---------------------------------------------------------------------------
// Benchmark: the tables recorded in design chapter 20, S5
// ---------------------------------------------------------------------------

/// Print steps under both estimators as the unselective side's fan-out grows,
/// and the plan-time cost of one sampled estimate. Ignored by default.
///
/// `cargo test --release -p semi-persistent-egraph --test ematch_sampled_selectivity -- \
///  --ignored --nocapture sweep`
#[test]
#[ignore = "sweep: regenerates the chapter 20 S5 tables"]
fn sweep() {
    println!(
        "{:>7} {:>6} {:>12} {:>12} {:>8} {:>10}",
        "leaves", "fan", "steps mean", "steps smpl", "ratio", "matches"
    );
    for fan in [1usize, 4, 16, 64, 256] {
        let (eg, rq, expect) = s5_shape(LEAVES, HITS, fan, DISTRACTORS);
        let off = plan_with(&eg, &rq, None);
        let on = plan_with(&eg, &rq, Some(SamplerConfig::default()));
        let (m_off, s_off) = run(&eg, &off);
        let (m_on, s_on) = run(&eg, &on);
        assert_eq!((m_off, m_on), (expect, expect));
        println!(
            "{LEAVES:>7} {fan:>6} {s_off:>12} {s_on:>12} {:>8.2} {m_off:>10}",
            s_off as f64 / s_on.max(1) as f64
        );
    }

    println!("\n{:>4} {:>14} {:>14}", "k", "plan mean us", "plan smpl us");
    let (eg, rq, _) = s5_shape(LEAVES, HITS, FAN, DISTRACTORS);
    let index = IndexStore::build(&eg);
    let vindex = VariantIndex::naive(&index);
    let sampler = IndexSampler::new(&eg, vindex);
    let stats = IndexStats::from_index(&index);
    for k in [8usize, 32, 128] {
        let mut cols = Vec::new();
        for cfg in [
            None,
            Some(SamplerConfig {
                k,
                ..SamplerConfig::default()
            }),
        ] {
            set_sampled_selectivity(cfg);
            let mut samples = Vec::new();
            for _ in 0..201 {
                let t = Instant::now();
                let p: Plan = schedule_with_stats_sampled(&rq, &stats, &sampler);
                samples.push(t.elapsed().as_secs_f64() * 1e6);
                std::hint::black_box(p);
            }
            samples.sort_by(f64::total_cmp);
            cols.push(samples[samples.len() / 2]);
        }
        set_sampled_selectivity(None);
        println!("{k:>4} {:>14.3} {:>14.3}", cols[0], cols[1]);
    }
}
