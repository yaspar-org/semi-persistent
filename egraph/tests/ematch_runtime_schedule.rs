// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A workload that separates plan-time atom ordering from per-binding atom
//! ordering (design chapter 20).
//!
//! **The shape.** `(f x y)` together with two probe atoms, `(p w x)` over the
//! first child and `(q y v)` over the second. The `f` atom is the cheapest
//! relation, so both schedulers drive from it and both bind the pair `(x, y)`
//! first; what is left is a two-atom choice made once the pair is in hand. Each
//! `f` node has exactly one of its two children populated: half have `fan`
//! `p`-parents over `x` and no `q`-parents over `y`, half the reverse. Whichever
//! atom a plan-time order puts second is therefore the empty one on half the
//! bindings and the full one on the other half, and no single order is right
//! twice.
//!
//! `p` reads `x` at position 1 and `q` reads `y` at position 0, neither of which
//! is where `f` puts them, so each probe bucket holds probe nodes only and its
//! length is the number this file varies.
//!
//! The tests use match steps, a deterministic measure of candidate work that is
//! independent of host load and build timing.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::ematch::{
    match_steps, reset_match_steps, run_query_scheduled, set_match_step_counting,
    set_runtime_scheduling,
};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::index::{IndexStore, VariantIndex};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::{GlobalCtx, ResolvedQuery};
use semi_persistent_egraph::schedule::{IndexStats, QueryPlan, Step, schedule_with_stats};

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type RQ = ResolvedQuery<OpId, SortId, NiraLitVal>;
type Plan = QueryPlan<OpId, u32, NiraLitVal>;

/// The query, in both compiled forms the matcher needs.
struct Query {
    rq: RQ,
    plan: Plan,
}

// ---------------------------------------------------------------------------
// The shape
// ---------------------------------------------------------------------------

/// Build the heterogeneous shape: `pairs` `f` nodes whose probe buckets are
/// populated on alternating sides with `fan` parents each, plus `matched` pairs
/// populated on both sides with one parent each so the query has a match set to
/// compare.
///
/// Returns the e-graph, the compiled query, and the number of matches the shape
/// admits (one per `matched` pair).
fn heterogeneous_shape(pairs: usize, fan: usize, matched: usize) -> (EG, Query, usize) {
    assert!(matched <= pairs);
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op0("leaf", e);
    eg.register_op1("s", e, e);
    eg.register_op2("f", e, e, e);
    eg.register_op2("p", e, e, e);
    eg.register_op2("q", e, e, e);
    let s = eg.ops().id_by_name("s").unwrap();
    let f = eg.ops().id_by_name("f").unwrap();
    let p = eg.ops().id_by_name("p").unwrap();
    let q = eg.ops().id_by_name("q").unwrap();

    // Distinct classes to hang the shape off, as one `s` chain: cheaper than
    // registering thousands of nullary operators.
    let needed = 2 * pairs + fan + 2;
    let mut leaves: Vec<ENodeId> = Vec::with_capacity(needed);
    leaves.push(eg.add(eg.ops().id_by_name("leaf").unwrap(), &[]));
    for i in 1..needed {
        let prev = leaves[i - 1];
        leaves.push(eg.add(s, &[prev]));
    }
    let filler = &leaves[2 * pairs..];

    for i in 0..pairs {
        let (x, y) = (leaves[2 * i], leaves[2 * i + 1]);
        eg.add(f, &[x, y]);
        if i < matched {
            // Both sides populated: this pair is where the matches come from.
            eg.add(p, &[filler[0], x]);
            eg.add(q, &[y, filler[0]]);
        } else if i % 2 == 0 {
            for &w in &filler[..fan] {
                eg.add(p, &[w, x]);
            }
        } else {
            for &v in &filler[..fan] {
                eg.add(q, &[y, v]);
            }
        }
    }
    eg.rebuild();

    let query = compile(&eg);
    (eg, query, matched)
}

/// Compile `(f x y) (p w x) (q y v)` against `eg`'s registries and schedule it
/// from the round's measured statistics — the same input the saturation driver
/// gives the scheduler.
fn compile(eg: &EG) -> Query {
    let pats = semi_persistent_egraph::parser::parse_patterns("(f x y) (p w x) (q y v)").unwrap();
    let fq = semi_persistent_egraph::sortcheck::flatten_surface(&pats, eg.ops()).unwrap();
    let rq = semi_persistent_egraph::resolve::resolve(
        &fq,
        eg.ops(),
        eg.sorts(),
        &NiraModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .unwrap();
    let index = IndexStore::build(eg);
    let plan = schedule_with_stats(&rq, &IndexStats::from_index(&index));
    Query { rq, plan }
}

/// The atom order the plan commits to, one entry per join.
fn static_order(plan: &Plan) -> Vec<usize> {
    let joins: Vec<usize> = plan
        .steps
        .iter()
        .filter_map(|s| match s {
            Step::Join { atom_id, .. } => Some(*atom_id),
            _ => None,
        })
        .collect();
    assert_eq!(
        joins.len(),
        3,
        "expected one join per atom, plan was {:?}",
        plan.steps
    );
    joins
}

/// The plan must be the one the gates exist to beat: drive from the `f` atom,
/// then commit to one of the two probe atoms for every binding. Asserted rather
/// than assumed, so a scheduler change that stops producing the shape fails here
/// instead of silently checking a different plan.
fn assert_static_order(plan: &Plan) {
    let joins = static_order(plan);
    assert_eq!(
        joins[0], 0,
        "the plan must drive from the `f` atom: {joins:?}"
    );
    assert!(
        joins[1] == 1 || joins[1] == 2,
        "the plan's second join must be one of the two probe atoms: {joins:?}"
    );
}

/// Run the query with the flag as given; return its match count and match steps.
fn run(runtime: bool, eg: &EG, query: &Query) -> (usize, u64) {
    let full = IndexStore::build(eg);
    let vindex = VariantIndex::naive(&full);
    let globals = GlobalCtx::<SortId, ENodeId>::new();
    set_match_step_counting(true);
    set_runtime_scheduling(runtime);
    reset_match_steps();
    let matches = run_query_scheduled(&query.rq, &query.plan, eg, &vindex, &globals).len();
    let steps = match_steps();
    set_runtime_scheduling(false);
    (matches, steps)
}

/// The default fan-out of the populated side. Large enough that walking it on
/// the bindings where it is the wrong choice dominates the run, small enough
/// that the shape builds in milliseconds.
const FAN: usize = 64;

/// Per-binding scheduling costs less than a tenth of the plan-time order's match
/// steps on the heterogeneous shape. A plan-time
/// order walks `fan` probe nodes on half the bindings and finds each one's
/// partner bucket empty, where the per-binding order opens the empty bucket
/// first and stops. The assertion leaves a wide margin below the workload's
/// structural fan-out ratio.
#[test]
fn runtime_scheduling_cuts_steps_on_the_heterogeneous_shape() {
    let (eg, query, expect) = heterogeneous_shape(1024, FAN, 8);
    assert_static_order(&query.plan);

    let (m_off, steps_off) = run(false, &eg, &query);
    let (m_on, steps_on) = run(true, &eg, &query);
    assert_eq!(
        (m_off, m_on),
        (expect, expect),
        "the two orders must agree on the match set"
    );
    println!("steps: plan-time {steps_off}, per-binding {steps_on}");
    assert!(
        steps_on * 10 < steps_off,
        "expected per-binding scheduling to cost under a tenth of the \
         plan-time order's steps, measured {steps_on} against {steps_off}"
    );
}

/// The match set is the same under both orders across the shape's parameters,
/// including the ones the step gate does not run at.
#[test]
fn both_orders_agree_on_the_match_set() {
    for (pairs, fan, matched) in [(64usize, 8usize, 64usize), (256, 32, 16), (16, 128, 0)] {
        let (eg, query, expect) = heterogeneous_shape(pairs, fan, matched);
        let (m_off, _) = run(false, &eg, &query);
        let (m_on, _) = run(true, &eg, &query);
        assert_eq!(
            (m_off, m_on),
            (expect, expect),
            "pairs={pairs} fan={fan} matched={matched}"
        );
    }
}
