// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Regression gates for formerly-known AC/ACI completion gaps.
//!
//! These started life as intentionally-`#[ignore]`d witnesses of missing Set/ACI coverage
//! in the basis diagnostics and `CcSnapshot`. Both gaps were closed (2026-07-10:
//! Set-aware basis diagnostics; representation-agnostic `CcSnapshot`), so the gates were
//! flipped and now run in the normal suite as ordinary regressions.

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
    // GATE (flipped 2026-07-10): ac_invariants scans both completion partitions now.
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
    // GATE (flipped 2026-07-10): CcSnapshot is representation-agnostic — kept, not deleted.
    let (eg, ab) = set_fixture();

    let snap = CcSnapshot::build(&eg);
    assert_eq!(
        snap.completion_nodes(),
        &[ab],
        "CcSnapshot must agree with completion_node_ids semantics for Set/ACI \
         (regression: it was once MSet-only)"
    );
}
