// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Regression coverage for Set/ACI completion-basis diagnostics and the
//! representation-agnostic `CcSnapshot`.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::cc::CcSnapshot;
use semi_persistent_egraph::interpret::{AcMode, InterpError, Interpreter};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::sortcheck_program;

fn set_fixture() -> (
    EGraph31<NiraLitVal, false, false>,
    semi_persistent_egraph::ENodeId,
) {
    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
    let sort = eg.intern_sort("E");
    let and = eg.register_set("and", sort, sort);
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let ab = eg.add(and, &[a, b]);
    (eg, ab)
}

#[test]
fn basis_report_counts_set_completion_nodes() {
    // ac_invariants must scan both completion partitions.
    let (eg, ab) = set_fixture();

    let report = eg.cc_basis_report();
    assert!(
        report.n_ac_nodes >= 1,
        "Set/ACI node {ab:?} must be included in completion-basis diagnostics \
         (regression: an MSet-only scan would let CHECK_AC_BASIS pass vacuously)"
    );
}

#[test]
fn cc_snapshot_counts_set_completion_nodes_if_kept() {
    // CcSnapshot must be representation-agnostic.
    let (eg, ab) = set_fixture();

    let snap = CcSnapshot::build(&eg);
    assert_eq!(
        snap.completion_nodes(),
        &[ab],
        "CcSnapshot must agree with completion_node_ids semantics for Set/ACI \
         (regression: it was once MSet-only)"
    );
}

#[test]
fn lazy_disequality_is_inconclusive_when_completion_hits_its_budget() {
    let source = r#"
        (sort E)
        (function Add (E) E :assoc-comm)
        (function a () E)
        (function b () E)
        (function c () E)
        (function d () E)
        (function e () E)
        (union (Add (a) (b)) (c))
        (union (Add (b) (d)) (e))
        (check (!= (a) (b)))
    "#;
    let commands = parse_program_v2(source).expect("program parses");
    let mut interp =
        Interpreter::<DefaultConfig, MachineLit, MachineModel, true, false>::new(MachineModel);
    interp.set_ac_mode(AcMode::Lazy);
    interp.eg.set_completion_node_budget(0);
    let mut globals = GlobalCtx::new();
    let checked = sortcheck_program(commands, &mut interp.eg, &interp.model, &mut globals)
        .expect("program sortchecks");

    match interp.run_checked(&checked) {
        Err(InterpError::CheckFailed(message)) => {
            assert!(
                message.contains("inconclusive"),
                "budget exhaustion must not become a disequality verdict: {message}"
            );
        }
        other => panic!("expected an inconclusive failed check, got {other:?}"),
    }
}
