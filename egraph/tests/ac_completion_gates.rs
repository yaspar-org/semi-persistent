// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Regression coverage for Set/ACI completion-basis diagnostics and the
//! representation-agnostic `CcSnapshot`.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::cc::CcSnapshot;
use semi_persistent_egraph::literal::NiraLitVal;

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
