// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Adversarial shapes for the operator-restriction policy in `ematch::run_join`.
//!
//! A join whose atom carries both a `ByOp` lookup and a bound-child lookup can
//! apply the operator restriction as a leapfrog operand or as a per-candidate
//! `op[id]` test, and the two costs cross over. This file builds the shape that
//! separates them and holds the policy to the better of the two at both
//! extremes.
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
//! `hubs * m` is held at 262 144 throughout, so the filter's cost per query is
//! the same 262 144 `op[id]` loads in every case measured and only the leapfrog
//! column moves. `sweep` prints the tables that
//! `ematch::OP_FILTER_RELATION_PER_CANDIDATE` records.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::ematch::{OpFilterPolicy, run_query, set_op_filter_policy};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::index::{IndexStore, VariantIndex};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::schedule::{IndexStats, QueryPlan, Step, schedule_with_stats};
use std::time::Instant;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type Plan = QueryPlan<OpId, u32, NiraLitVal>;

/// Hub-parent nodes in total, held fixed as `m` varies.
const HUB_PARENTS: usize = 262_144;
/// Operators the hub's parents are spread over.
const OPS: usize = 8;

/// The policy is process-wide, so the tests that pin it take turns. Held for
/// the whole of a test rather than around each `pin`, because a run's timing is
/// only interpretable if nothing else in the binary is running.
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
/// The pin is one `op_card` override, and it is what makes the sweep a
/// measurement of the executor rather than of the planner: the plan shape has
/// to be the same in every cell for the two mechanisms' costs to be comparable
/// across them, and the planner would otherwise reorder the atoms as `n` falls
/// below the hub relation. Which plan the cost model picks on a given e-graph is
/// a separate question, settled in chapter 20.
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

/// Median wall time of `reps` runs of the query, index build excluded.
fn time(mode: Mode, eg: &EG, plan: &Plan, reps: usize) -> (f64, usize) {
    mode.pin();
    let full = IndexStore::build(eg);
    let vindex = VariantIndex::naive(&full);
    let globals = GlobalCtx::<SortId, ENodeId>::new();
    let mut samples = Vec::with_capacity(reps);
    let mut matches = 0;
    for _ in 0..reps {
        let t = Instant::now();
        matches = run_query(plan, eg, &vindex, &globals).len();
        samples.push(t.elapsed().as_secs_f64() * 1e3);
    }
    samples.sort_by(f64::total_cmp);
    (samples[reps / 2], matches)
}

// ---------------------------------------------------------------------------
// Sweep: regenerates the tables recorded on `OP_FILTER_RELATION_PER_CANDIDATE`
// ---------------------------------------------------------------------------

/// Print median wall per query for both mechanisms over `m` x intersection
/// Print median wall per query for both mechanisms over the `(m, n)` grid.
/// Ignored by default: fifteen shapes of up to a million nodes each.
///
/// `cargo test --release -p semi-persistent-egraph --test ematch_op_filter -- \
///  --ignored --nocapture sweep`
#[test]
#[ignore = "sweep: minutes, regenerates the crossover table"]
fn sweep() {
    let _pin = POLICY_PIN.lock().unwrap_or_else(|e| e.into_inner());

    // Table 1, bucket size against relation size, with an empty intersection
    // so that no match-construction work is in either column and the two
    // mechanisms are all that separates them.
    println!("bucket size x relation size (empty intersection)");
    header();
    for m in [1usize, 2, 4, 8, 16, 32, 64, 128, 4096, 262_144] {
        let hubs = (HUB_PARENTS / m).max(1);
        for n in [2621usize, 16_384, 53_710, 131_072, 262_144] {
            row(hubs, m, n, 0);
        }
    }

    // Table 2, bucket size against intersection density, the two axes the
    // shape was built for. `n` is the whole hub-parent population scaled by the
    // density, and the intersection is as large as that `n` allows.
    println!("\nbucket size x intersection density");
    header();
    for m in [16usize, 256, 4096, 65_536, 262_144] {
        let hubs = (HUB_PARENTS / m).max(1);
        for (num, den) in [(1usize, 1usize), (1, 100), (1, 10_000)] {
            let n = (HUB_PARENTS * num / den).max(1);
            row(hubs, m, n, m.min(n / hubs));
        }
    }
    set_op_filter_policy(OpFilterPolicy::Adaptive);
}

fn header() {
    println!(
        "{:>8} {:>6} {:>9} {:>7} {:>10} {:>11} {:>8} {:>9}",
        "m", "hubs", "n", "isect", "filter ms", "leapfrog ms", "lf/filt", "matches"
    );
}

fn row(hubs: usize, m: usize, n: usize, isect: usize) {
    let (eg, plan, expect) = hub_shape(hubs, m, n, isect);
    assert_join_under_test(&plan);
    let reps = if m >= 65_536 { 9 } else { 15 };
    let (t_filter, n1) = time(Mode::Filter, &eg, &plan, reps);
    let (t_leap, n2) = time(Mode::Leapfrog, &eg, &plan, reps);
    assert_eq!(
        (n1, n2),
        (expect, expect),
        "the two mechanisms must agree on the match set"
    );
    println!(
        "{m:>8} {hubs:>6} {n:>9} {isect:>7} {t_filter:>10.3} {t_leap:>11.3} {:>8.3} {n1:>9}",
        t_leap / t_filter
    );
}

// ---------------------------------------------------------------------------
// Regression gate (b): timing, release codegen only
// ---------------------------------------------------------------------------

/// The shipped policy is within 1.2x of the better mechanism at both extremes.
///
/// This is what pins the rule: make it unconditional demotion (the policy this
/// replaced) and the hub extreme fails; make it unconditional leapfrog and the
/// tiny-bucket extreme fails.
///
/// Release-only, following `containers-conformance`'s binary-search canary: the
/// bands are codegen properties, and an unoptimized or instrumented build turns
/// the `op[id]` test and the cursor seek into call boundaries that move the two
/// costs by different factors. The decision half of the gate
/// (`ematch::tests::op_restriction_*`) runs in every profile.
#[test]
fn adaptive_policy_is_within_1_2x_of_the_better_mechanism() {
    let _pin = POLICY_PIN.lock().unwrap_or_else(|e| e.into_inner());
    if cfg!(debug_assertions) {
        eprintln!("skipped: timing canary is calibrated for release codegen only");
        return;
    }
    // Many tiny buckets against a relation two orders larger: the
    // math-microbenchmark shape, where m loads beat m gallops.
    check_extreme("tiny buckets", 16_384, 16, HUB_PARENTS, 16, Mode::Filter);
    // One hub with a quarter of a million parents and a 26-node relation: the
    // shape the unconditional demotion loses on.
    check_extreme("hub", 1, HUB_PARENTS, 26, 26, Mode::Leapfrog);
    set_op_filter_policy(OpFilterPolicy::Adaptive);
}

fn check_extreme(what: &str, hubs: usize, m: usize, n: usize, isect: usize, expected_better: Mode) {
    let (eg, plan, expect) = hub_shape(hubs, m, n, isect);
    assert_join_under_test(&plan);
    let reps = if m >= 65_536 { 9 } else { 15 };
    let (t_filter, n_f) = time(Mode::Filter, &eg, &plan, reps);
    let (t_leap, n_l) = time(Mode::Leapfrog, &eg, &plan, reps);
    let (t_adapt, n_a) = time(Mode::Adaptive, &eg, &plan, reps);
    assert_eq!(
        (n_f, n_l, n_a),
        (expect, expect, expect),
        "{what}: match sets must agree"
    );

    let (better_t, better) = if t_filter <= t_leap {
        (t_filter, Mode::Filter)
    } else {
        (t_leap, Mode::Leapfrog)
    };
    println!(
        "{what}: filter {t_filter:.3} ms, leapfrog {t_leap:.3} ms, \
         adaptive {t_adapt:.3} ms, ratio {:.3}",
        t_adapt / better_t
    );
    assert_eq!(
        better, expected_better,
        "{what}: expected {expected_better:?} to be the better mechanism, \
         measured filter {t_filter:.3} ms against leapfrog {t_leap:.3} ms"
    );
    assert!(
        t_adapt <= 1.2 * better_t,
        "{what}: adaptive {t_adapt:.3} ms is more than 1.2x the better \
         mechanism's {better_t:.3} ms ({better:?})"
    );
}

// ---------------------------------------------------------------------------
// Completeness at scale, every profile
// ---------------------------------------------------------------------------

/// Both mechanisms return the same match set on the hub shape at scales that
/// fall on both sides of the rule. Timing-free, so it holds in debug too; the
/// moderate-scale decision gate lives in `ematch`'s unit tests, where the
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
