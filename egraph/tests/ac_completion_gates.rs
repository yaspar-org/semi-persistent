// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Gates for known AC/ACI completion gaps.
//!
//! These are intentionally `#[ignore]`: they encode behavior the next implementation
//! iteration should make true, while keeping the normal suite green until the feature lands.
//! Run with:
//!   cargo test -p semi-persistent-egraph --test ac_completion_gates -- --ignored

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
#[ignore = "GATE: CHECK_AC_BASIS/ac_invariants must count Set/ACI completion nodes, not only MSet"]
fn basis_report_counts_set_completion_nodes() {
    let (eg, ab) = set_fixture();

    let report = eg.cc_basis_report();
    assert!(
        report.n_ac_nodes >= 1,
        "Set/ACI node {ab:?} must be included in completion-basis diagnostics; \
         today ac_invariants.rs scans only NodeRef::MSet, so CHECK_AC_BASIS can pass vacuously"
    );
}

#[test]
#[ignore = "GATE: delete CcSnapshot or make it representation-agnostic for Set/ACI"]
fn cc_snapshot_counts_set_completion_nodes_if_kept() {
    let (eg, ab) = set_fixture();

    let snap = CcSnapshot::build(&eg);
    assert_eq!(
        snap.completion_nodes(),
        &[ab],
        "CcSnapshot is stale/MSet-only; if retained, it must agree with current completion_node_ids semantics for Set/ACI"
    );
}
