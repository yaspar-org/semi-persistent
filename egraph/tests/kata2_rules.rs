// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ramp-up kata 2: saturating vs diverging rules, `--union-by` survivors,
//! and the compiled plan for §2's `Ite` rewrite.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::UnionBy;
use semi_persistent_egraph::id::{OpId, SortId};
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::lit_model::LitModel;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::registry::{OpRegistry, SortRegistry};
use semi_persistent_egraph::resolve::{GlobalCtx, resolve};
use semi_persistent_egraph::saturate::SaturationStrategy;
use semi_persistent_egraph::schedule::{
    IndexLookup, IndexStats, QueryPlan, Step, schedule_with_stats,
};
use semi_persistent_egraph::sortcheck::flatten_surface;

type Interp = Interpreter<DefaultConfig, BignumLit, BignumModel, true, false>;
type EG = EGraph<DefaultConfig, BignumLit, true, false>;

fn run(src: &str) -> Interp {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src).expect("parse");
    let mut interp = Interp::new(BignumModel);
    interp.set_strategy(SaturationStrategy::Naive);
    let mut globals = GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sortcheck");
    interp.run_checked(&checked).expect("run");
    interp
}

fn egg(name: &str) -> String {
    let path = format!("{}/tests/egg/{name}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"))
}

#[test]
fn saturating_ruleset_reaches_a_fixpoint() {
    let interp = run(&egg("kata2_saturates.egg"));
    let sat = interp.last_sat().expect("run recorded a result");
    assert!(
        sat.saturated,
        "dbl should finish before the iteration bound"
    );
    assert!(
        sat.iterations < 10,
        "expected an early fixpoint, got {} iterations",
        sat.iterations
    );
}

#[test]
fn diverging_ruleset_hits_the_bound() {
    let interp = run(&egg("kata2_diverges.egg"));
    let sat = interp.last_sat().expect("run recorded a result");
    assert!(
        !sat.saturated,
        "up x → up (s x) still has work after 5 rounds"
    );
    assert_eq!(sat.iterations, 5);
}

/// `--union-by size` keeps the bigger class; `--union-by uses` keeps the
/// class with more parents. Same `union`, different survivor. The asserted
/// equality is unchanged: both sides share a representative either way.
#[test]
fn union_by_size_and_uses_pick_different_survivors() {
    let size = merge_large_against_used(UnionBy::Size);
    let uses = merge_large_against_used(UnionBy::Uses);
    assert_eq!(
        size.survivor, size.large,
        "size should keep the 3-member class"
    );
    assert_eq!(
        uses.survivor, uses.used,
        "uses should keep the class with the parent"
    );
    assert_ne!(
        size.survivor, uses.survivor,
        "the two policies must disagree on who survives"
    );
    assert_eq!(
        size.eg.find_const(size.large),
        size.eg.find_const(size.used)
    );
    assert_eq!(
        uses.eg.find_const(uses.large),
        uses.eg.find_const(uses.used)
    );
}

struct MergeShot {
    eg: EG,
    large: semi_persistent_egraph::ENodeId,
    used: semi_persistent_egraph::ENodeId,
    survivor: semi_persistent_egraph::ENodeId,
}

fn merge_large_against_used(policy: UnionBy) -> MergeShot {
    let mut eg = EG::from_model(&BignumModel);
    eg.set_union_by(policy);
    let s = eg.intern_sort("S");
    let a = eg.register_op0("a", s);
    let b = eg.register_op0("b", s);
    let c = eg.register_op0("c", s);
    let d = eg.register_op0("d", s);
    let f = eg.register_op1("f", s, s);

    let large = eg.add(a, &[]);
    let used = eg.add(b, &[]);
    let extra1 = eg.add(c, &[]);
    let extra2 = eg.add(d, &[]);
    eg.merge(large, extra1);
    eg.merge(large, extra2);
    eg.add(f, &[used]);

    let (survivor, _absorbed) = eg
        .merge(large, used)
        .expect("the two classes were still distinct");
    MergeShot {
        eg,
        large,
        used,
        survivor,
    }
}

/// The plan `EGRAPH_DUMP_PLAN=1` would print for `(Ite (True) x y)`.
///
/// Step 0 scans `Ite`. Steps 1–3 read the three children (condition, then,
/// else). Step 4 re-joins the condition class against `True`, because the
/// class representative need not be the `True` node — after `(union c (True))`
/// it is often still `Lt`.
#[test]
fn section2_ite_plan_rejoins_true_in_the_condition_class() {
    let model = NiraModel;
    let mut sorts: SortRegistry<SortId, false> = SortRegistry::new();
    let sort_names: Vec<&str> = model.sorts().iter().map(|s| s.name).collect();
    sorts.register_builtins(&sort_names);
    let b = sorts.intern("B");
    let i = sorts.intern("I");
    let mut ops: OpRegistry<OpId, SortId, false> = OpRegistry::new();
    ops.register_builtins(&model, &sorts);
    ops.register("True", &[], b);
    ops.register("Lt", &[i, i], b);
    ops.register("Ite", &[b, i, i], i);

    let pats = semi_persistent_egraph::parser::parse_patterns("(Ite (True) x y)").expect("pattern");
    let fq = flatten_surface(&pats, &ops).expect("flatten");
    let rq = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new()).expect("resolve");
    let true_op = ops.id_by_name("True").unwrap();
    let ite_op = ops.id_by_name("Ite").unwrap();
    // Same cardinality story as design chapter 8: Ite is rare, True is common,
    // so the scheduler drives from Ite. That is the plan `EGRAPH_DUMP_PLAN`
    // prints for §2 after the program has built `t` and `(True)`.
    let mut stats = IndexStats::new();
    stats.op_card.insert(ite_op, 1);
    stats.op_card.insert(true_op, 4);
    let plan: QueryPlan<OpId, u32, NiraLitVal> = schedule_with_stats(&rq, &stats);

    assert!(
        matches!(
            &plan.steps[0],
            Step::Join { lookups, .. }
                if lookups.iter().any(|l| matches!(l, IndexLookup::ByOp { op } if *op == ite_op))
        ),
        "step 0 should scan Ite, got {:?}",
        plan.steps[0]
    );
    let extracts: Vec<u32> = plan
        .steps
        .iter()
        .filter_map(|s| match s {
            Step::ExtractChild { pos, .. } => Some(*pos),
            _ => None,
        })
        .collect();
    assert_eq!(extracts, vec![0, 1, 2], "Ite has three children");

    let rejoin = plan.steps.iter().any(|s| {
        matches!(
            s,
            Step::Join { lookups, .. }
                if lookups.iter().any(|l| matches!(l, IndexLookup::ByOp { op } if *op == true_op))
                && lookups.iter().any(|l| matches!(l, IndexLookup::ByRepr { .. }))
        )
    });
    assert!(
        rejoin,
        "expected ByRepr ∩ ByOp(True) so a non-True representative still matches; steps: {:?}",
        plan.steps
    );
}
