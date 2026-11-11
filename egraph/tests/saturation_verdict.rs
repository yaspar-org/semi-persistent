// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The saturation verdict under eager completion. A run is saturated only when its rules
//! changed nothing and the completion inside each rebuild reached its fixpoint: a
//! completion stopped on a budget leaves AC-entailed equalities out of the graph, and a
//! rule round that adds nothing to such a graph has not reached a fixpoint of the theory.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::interpret::{AcMode, Interpreter};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::node_types::FLAG_AC_COLLAPSED;
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::saturate::SaturationStrategy;
use semi_persistent_egraph::sortcheck::sortcheck_program;
use semi_persistent_egraph::{CompletionOutcome, DEFAULT_COMPLETION_NODE_BUDGET};

/// Run `source` under eager completion with a node budget of 0 and return the run's
/// saturation flag, the completion outcome the run left, and whether one more rebuild
/// with the default budget adds nodes to the graph the run ended on.
fn eager_run_with_zero_budget(
    source: &str,
    strategy: SaturationStrategy,
) -> (bool, Option<CompletionOutcome>, bool) {
    let commands = parse_program_v2(source).expect("program parses");
    let mut interp =
        Interpreter::<DefaultConfig, MachineLit, MachineModel, true, false>::new(MachineModel);
    interp.set_strategy(strategy);
    interp.set_ac_mode(AcMode::Eager);
    interp.eg.set_completion_node_budget(0);
    let mut globals = GlobalCtx::new();
    let checked = sortcheck_program(commands, &mut interp.eg, &interp.model, &mut globals)
        .expect("program sortchecks");
    interp.run_checked(&checked).expect("program runs");
    let sat = interp.last_sat().expect("the program has a run").saturated;
    let outcome = interp.eg.completion_outcome();
    let before = interp.eg.node_count();
    interp
        .eg
        .set_completion_node_budget(DEFAULT_COMPLETION_NODE_BUDGET);
    interp.eg.rebuild();
    (sat, outcome, interp.eg.node_count() > before)
}

/// The rule of this program never fires, so its one round changes nothing. Completion
/// of the chain `a_i + b = a_(i+1)` superposes neighbouring equations and mints nodes
/// over several rounds; a node budget of 0 stops every rebuild after its first minting
/// round, so the run's rebuild ends on `AbortedGrowthLimit` with completion unfinished
/// (a rebuild with the default budget still adds nodes). The run must not report
/// saturation.
#[test]
fn eager_run_stopped_on_node_budget_is_not_saturated() {
    let source = r#"
        (sort E)
        (function Add (E) E :assoc-comm)
        (function a0 () E)
        (function a1 () E)
        (function a2 () E)
        (function a3 () E)
        (function a4 () E)
        (function a5 () E)
        (function b () E)
        (function F (E) E)
        (union (Add (a0) (b)) (a1))
        (union (Add (a1) (b)) (a2))
        (union (Add (a2) (b)) (a3))
        (union (Add (a3) (b)) (a4))
        (union (Add (a4) (b)) (a5))
        (rewrite (F (F x)) x)
        (run 1)
    "#;
    for strategy in [SaturationStrategy::Naive, SaturationStrategy::SemiNaive] {
        let (saturated, outcome, unfinished) = eager_run_with_zero_budget(source, strategy);
        assert!(
            matches!(outcome, Some(CompletionOutcome::AbortedGrowthLimit { .. })),
            "{strategy:?}: the fixture must stop completion on the node budget, got {outcome:?}"
        );
        assert!(
            unfinished,
            "{strategy:?}: the fixture must leave completion work for a later rebuild"
        );
        assert!(
            !saturated,
            "{strategy:?}: a run whose completion stopped on {outcome:?} reported saturated"
        );
    }
}

/// A completion round whose only effect is retiring a node. After `Add(a, b) = d` is
/// closed, the class of `Add(a, b, c)` is joined to `Add(c, d)` by hand, so the round
/// finds the normal form `{c, d}` of `{a, b, c}` already in the class: the merge is a
/// no-op and the round only collapses the node `Add(a, b, c)`. That round changed the
/// active rule set, so it is not the fixpoint round: another round follows it, and the
/// reported `Converged` counts more than the one round.
#[test]
fn completion_round_that_only_retires_a_node_is_not_the_fixpoint() {
    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
    eg.set_cc(true);
    let s = eg.intern_sort("E");
    let a_op = eg.register_op0("a", s);
    let b_op = eg.register_op0("b", s);
    let c_op = eg.register_op0("c", s);
    let d_op = eg.register_op0("d", s);
    let add = eg.register_mset("add", s, s);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let s_ab = eg.add(add, &[a, b]);
    eg.merge(s_ab, d);
    eg.rebuild();
    assert!(
        matches!(
            eg.completion_outcome(),
            Some(CompletionOutcome::Converged { .. })
        ),
        "setup: {:?}",
        eg.completion_outcome()
    );
    let s_abc = eg.add(add, &[a, b, c]);
    let s_cd = eg.add(add, &[c, d]);
    eg.merge(s_abc, s_cd);
    let collapsed =
        |eg: &EGraph31<NiraLitVal, false, false>| eg.node_flags(s_abc) & FLAG_AC_COLLAPSED != 0;
    assert!(!collapsed(&eg), "setup: add(a, b, c) is not yet collapsed");
    let nodes = eg.node_count();
    eg.rebuild();
    assert!(collapsed(&eg), "the rebuild collapses add(a, b, c)");
    assert_eq!(eg.node_count(), nodes, "the rebuild mints no node");
    match eg.completion_outcome() {
        Some(CompletionOutcome::Converged { rounds }) => assert!(
            rounds > 1,
            "the round that collapsed add(a, b, c) reported the fixpoint (Converged after \
             {rounds} round)"
        ),
        other => panic!("expected Converged, got {other:?}"),
    }
}
