// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Adversarial shapes for the operator-restriction policy in `ematch::run_join`.
//!
//! A join whose atom carries both a `ByOp` lookup and a bound-child lookup can
//! apply the operator restriction as a leapfrog operand or as a per-candidate
//! `op[id]` test, and the two costs cross over. This file builds the shape that
//! separates them and checks semantic agreement across both sides of the
//! adaptive decision rule.
//!
//! **The shape.** `hubs` classes of a unary operator `hub`, each the position-0
//! child of `m` parents spread over eight operators `f0..f7`, of which `isect`
//! are under `f0`; `by_op[f0]` is brought up to `n` with filler nodes whose
//! position-0 child is not a hub. The join under test therefore intersects a
//! bucket of `m` with a relation of `n`, which are the two lengths the policy
//! reads, and the intersection is a third parameter independent of both.
//!
//! Hub-parent and filler nodes are interleaved in allocation order by a fixed
//! shuffle, because a relation packed into one id range is the case a leapfrog
//! seek clears in a single step and no real e-graph produces it.
//!
//! `hubs * m` is held constant while bucket and relation sizes vary.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::ematch::{OpFilterPolicy, run_query, set_op_filter_policy};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::index::{IndexStore, VariantIndex};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::schedule::{IndexStats, QueryPlan, Step, schedule_with_stats};

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type Plan = QueryPlan<OpId, u32, NiraLitVal>;

/// Operators the hub's parents are spread over.
const OPS: usize = 8;

/// The policy is process-wide, so tests that pin it take turns.
static POLICY_PIN: std::sync::Mutex<()> = std::sync::Mutex::new(());

// ---------------------------------------------------------------------------
// The shape
// ---------------------------------------------------------------------------

/// Which of the two mechanisms a run is pinned to.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Mode {
    /// `ByOp` stays a leapfrog operand.
    Leapfrog,
    /// `ByOp` is demoted to a per-candidate operator test.
    Filter,
    /// The shipped rule decides per binding.
    Adaptive,
}

impl Mode {
    fn pin(self) {
        set_op_filter_policy(match self {
            Mode::Leapfrog => OpFilterPolicy::AlwaysLeapfrog,
            Mode::Filter => OpFilterPolicy::AlwaysFilter,
            Mode::Adaptive => OpFilterPolicy::Adaptive,
        });
    }
}

/// Build the hub shape: `hubs` hub classes with `m` parents each, against an
/// `f0` relation of exactly `n` nodes, `min(m, n / hubs)` of which sit in each
/// hub's bucket.
///
/// Returns the e-graph, the plan for `(f0 (hub z) y)` whose join is the one
/// under test, and the number of matches the shape admits.
fn hub_shape(hubs: usize, m: usize, n: usize, isect: usize) -> (EG, Plan, usize) {
    assert!(isect <= m && hubs * isect <= n);
    let fillers = n - hubs * isect;
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op0("leaf", e);
    eg.register_op1("s", e, e);
    eg.register_op1("hub", e, e);
    for k in 0..OPS {
        eg.register_op2(&format!("f{k}"), e, e, e);
    }
    let s = eg.ops().id_by_name("s").unwrap();
    let hub_op = eg.ops().id_by_name("hub").unwrap();
    let fs: Vec<OpId> = (0..OPS)
        .map(|k| eg.ops().id_by_name(&format!("f{k}")).unwrap())
        .collect();

    // Distinct classes to hang parents off, as one `s` chain: cheaper than
    // registering a quarter of a million nullary operators.
    let leaves_needed = (hubs * m).max(fillers + 2) + hubs + 2;
    let mut leaves: Vec<ENodeId> = Vec::with_capacity(leaves_needed);
    leaves.push(eg.add(eg.ops().id_by_name("leaf").unwrap(), &[]));
    for i in 1..leaves_needed {
        let prev = leaves[i - 1];
        leaves.push(eg.add(s, &[prev]));
    }
    let hub_ids: Vec<ENodeId> = (0..hubs).map(|i| eg.add(hub_op, &[leaves[i]])).collect();

    // The two node populations, interleaved in allocation order. `true` places
    // the next hub parent, `false` the next filler `f0`.
    let mut kinds = vec![true; hubs * m];
    kinds.extend(std::iter::repeat_n(false, fillers));
    let mut rng: u64 = 0x2545_F491_4F6C_DD1D;
    for i in (1..kinds.len()).rev() {
        rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        kinds.swap(i, (rng >> 33) as usize % (i + 1));
    }

    let mut hp = 0usize;
    let mut fill = 0usize;
    for &hub_parent in &kinds {
        if hub_parent {
            let (h, j) = (hp / m, hp % m);
            // Spread the `f0` parents through the bucket instead of packing
            // them at its front, which is the leapfrog seek's best case.
            let is_f0 = isect > 0 && j * isect / m != (j + 1) * isect / m;
            let op = if is_f0 { fs[0] } else { fs[1 + j % (OPS - 1)] };
            eg.add(op, &[hub_ids[h], leaves[hp]]);
            hp += 1;
        } else {
            eg.add(fs[0], &[leaves[fill], leaves[fill + 1]]);
            fill += 1;
        }
    }
    eg.rebuild();

    let plan = plan_for(&eg);
    (eg, plan, hubs * isect)
}

/// Compile and schedule `(f0 (hub z) y)` against `eg`'s registries, with the
/// `hub` atom pinned as the driver.
///
/// The `op_card` override keeps the plan shape fixed while the test varies the
/// executor's bucket and relation sizes. Planner selection is tested separately.
fn plan_for(eg: &EG) -> Plan {
    let pats = semi_persistent_egraph::parser::parse_patterns("(f0 (hub z) y)").unwrap();
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
    let mut stats = IndexStats::from_index(&index);
    stats.op_card.insert(eg.ops().id_by_name("hub").unwrap(), 1);
    schedule_with_stats(&rq, &stats)
}

/// The plan must place the join this file exists to measure: a step whose
/// lookups are `ByOp` together with a bound-child lookup. Asserted rather than
/// assumed, so a scheduler change that stops producing the shape fails here
/// instead of silently measuring something else.
fn assert_join_under_test(plan: &Plan) {
    let joins: Vec<&Step<OpId, u32, NiraLitVal>> = plan
        .steps
        .iter()
        .filter(|s| match s {
            Step::Join { lookups, .. } => {
                lookups.len() > 1
                    && lookups.iter().any(|l| {
                        matches!(
                            l,
                            semi_persistent_egraph::schedule::IndexLookup::ByOp { .. }
                        )
                    })
                    && lookups.iter().any(|l| {
                        matches!(
                            l,
                            semi_persistent_egraph::schedule::IndexLookup::ByChildPos { .. }
                        )
                    })
            }
            _ => false,
        })
        .collect();
    assert_eq!(
        joins.len(),
        1,
        "expected exactly one ByOp-plus-bound-child join, plan was {:?}",
        plan.steps
    );
}

/// Run the query once and return the match count, with `mode` pinned.
fn run(mode: Mode, eg: &EG, plan: &Plan) -> usize {
    mode.pin();
    let full = IndexStore::build(eg);
    let vindex = VariantIndex::naive(&full);
    run_query(plan, eg, &vindex, &GlobalCtx::<SortId, ENodeId>::new()).len()
}

/// Both mechanisms return the same match set on the hub shape at scales that
/// fall on both sides of the rule. Timing-free, so it holds in debug too; the
/// decision-rule assertions live in `ematch`'s unit tests, where the
/// per-join probe is visible.
#[test]
fn both_mechanisms_agree_on_the_hub_shape() {
    let _pin = POLICY_PIN.lock().unwrap_or_else(|e| e.into_inner());
    for (hubs, m, n, isect) in [
        (512usize, 16usize, 8192usize, 3usize),
        (1, 8192, 5, 5),
        (4, 2048, 8192, 2048),
    ] {
        let (eg, plan, expect) = hub_shape(hubs, m, n, isect);
        assert_join_under_test(&plan);
        let f = run(Mode::Filter, &eg, &plan);
        let l = run(Mode::Leapfrog, &eg, &plan);
        let a = run(Mode::Adaptive, &eg, &plan);
        assert_eq!(
            (f, l, a),
            (expect, expect, expect),
            "hubs={hubs} m={m} n={n}"
        );
    }
    set_op_filter_policy(OpFilterPolicy::Adaptive);
}
