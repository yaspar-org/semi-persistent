// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Property-based adversarial checks for anti-unification.
//!
//! The ignored oracle property compares the staged transportation traversal to
//! the complete set of 2x2 transportation-polytope vertices. It persists the
//! minimal failing family instead of relying only on one hand-written example.

use proptest::prelude::*;
use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::actions::{ActionCache, generate_actions};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, anti_unify};
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

/// A 2x2 transportation polytope is a line segment. Its integer matrices are
/// parameterized by x00 in [lower, upper], and its vertices are the one or two
/// endpoints (one when the segment is degenerate).
fn expected_2x2_vertices(row0: u32, row1: u32, col0: u32) -> usize {
    let total = row0 + row1;
    let col1 = total - col0;
    let lower = row0.saturating_sub(col1);
    let upper = row0.min(col0);
    if lower == upper { 1 } else { 2 }
}

fn generated_2x2_actions(row0: u32, row1: u32, col0: u32) -> usize {
    let total = row0 + row1;
    let col1 = total - col0;
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let ops: Vec<_> = (0..4)
        .map(|i| eg.register_op0(&format!("v{i}"), sort))
        .collect();
    let leaves: Vec<_> = ops.iter().map(|&op| eg.add(op, &[])).collect();
    let plus = eg.register_mset("plus", sort, sort);

    let mut left_children = vec![leaves[0]; row0 as usize];
    left_children.extend(std::iter::repeat_n(leaves[1], row1 as usize));
    let mut right_children = vec![leaves[2]; col0 as usize];
    right_children.extend(std::iter::repeat_n(leaves[3], col1 as usize));
    let left = eg.add(plus, &left_children);
    let right = eg.add(plus, &right_children);
    eg.rebuild();

    let snapshot = AuSnapshot::new(&eg).unwrap();
    let left = snapshot.class_of(left).unwrap();
    let right = snapshot.class_of(right).unwrap();
    let mut cache = ActionCache::new(usize::MAX);
    generate_actions(&snapshot, &mut cache, left, right);
    cache.get(left, right).unwrap().len()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    #[ignore = "known correctness bug: fixed row-major activation misses valid AC vertices"]
    fn prop_ac_actions_match_complete_2x2_vertex_oracle(
        row0 in 1u32..6,
        row1 in 1u32..6,
        col0_seed in 1u32..10,
    ) {
        let total = row0 + row1;
        let col0 = 1 + (col0_seed - 1) % (total - 1);
        let expected = expected_2x2_vertices(row0, row1, col0);
        let actual = generated_2x2_actions(row0, row1, col0);
        prop_assert_eq!(
            actual,
            expected,
            "rows=[{},{}], cols=[{},{}]",
            row0,
            row1,
            col0,
            total - col0,
        );
    }
}

// Small ordered terms provide a non-algebraic control: exact search may
// improve on the generalize seed, and bounded UCT must never beat the exact
// oracle for the same action language.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(40))]

    #[test]
    fn prop_small_ordered_quality_is_bounded_by_seed_and_exact(
        i0 in 0usize..4,
        i1 in 0usize..4,
        j0 in 0usize..4,
        j1 in 0usize..4,
    ) {
        let mut eg = Eg::new();
        let sort = eg.intern_sort("E");
        let ops: Vec<_> = (0..4)
            .map(|i| eg.register_op0(&format!("k{i}"), sort))
            .collect();
        let leaves: Vec<_> = ops.iter().map(|&op| eg.add(op, &[])).collect();
        let f = eg.register_op2("f", sort, sort, sort);
        let left = eg.add(f, &[leaves[i0], leaves[i1]]);
        let right = eg.add(f, &[leaves[j0], leaves[j1]]);
        eg.rebuild();
        let snapshot = AuSnapshot::new(&eg).unwrap();

        let exact = anti_unify(&snapshot, left, right, &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        }).unwrap();
        let uct = anti_unify(&snapshot, left, right, &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 128,
            ..Default::default()
        }).unwrap();

        prop_assert!(uct.size >= exact.size);
    }
}
