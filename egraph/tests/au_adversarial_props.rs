// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Property-based adversarial checks for anti-unification.
//!
//! The matrix-count property checks the bounded enumeration (used only as a
//! test oracle; production paths use min-cost transport) against the full
//! integer-point count of the 2x2 transportation polytope.

use proptest::prelude::*;
use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::actions::{ActionCache, generate_actions};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

/// A 2x2 transportation polytope is a line segment. Its integer matrices are
/// parameterized by x00 in [lower, upper]; the complete enumeration emits one
/// action per integer point (upper - lower + 1), not just the two endpoints.
fn expected_2x2_matrices(row0: u32, row1: u32, col0: u32) -> usize {
    let total = row0 + row1;
    let col1 = total - col0;
    let lower = row0.saturating_sub(col1);
    let upper = row0.min(col0);
    (upper - lower + 1) as usize
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
    fn prop_ac_actions_match_complete_2x2_matrix_oracle(
        row0 in 1u32..6,
        row1 in 1u32..6,
        col0_seed in 1u32..10,
    ) {
        let total = row0 + row1;
        let col0 = 1 + (col0_seed - 1) % (total - 1);
        let expected = expected_2x2_matrices(row0, row1, col0);
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

// Small ordered terms provide a non-algebraic control: both algorithms must
// stay within the shared generalize action, bounded UCT must never beat Exact,
// certified UCT must equal Exact, and every returned projection is concrete.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(40))]

    #[test]
    fn prop_small_ordered_quality_is_bounded_and_projection_valid(
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

        // Recorded scalar baseline from the pre-change initializer for these
        // fixed ordered fixtures. This intentionally records only expected
        // quality; it does not reconstruct or expose a syntactic zipper.
        let recorded_baseline_size = 1
            + if i0 == j0 { 1 } else { 2 }
            + if i1 == j1 { 1 } else { 2 };
        let exact = anti_unify(&snapshot, left, right, &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        }).unwrap();
        let uct = anti_unify(&snapshot, left, right, &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 128,
            ..Default::default()
        }).unwrap();

        prop_assert!(exact.size <= recorded_baseline_size);
        prop_assert!(uct.size >= exact.size);
        prop_assert!(uct.size <= recorded_baseline_size);
        if uct.completion == Completion::Exact {
            prop_assert_eq!(
                uct.pool.quality(uct.term_id),
                exact.pool.quality(exact.term_id)
            );
        }

        for mut result in [exact, uct] {
            let left_projection = result.pool.project(result.term_id, 0);
            let right_projection = result.pool.project(result.term_id, 1);
            prop_assert!(!result.pool.has_variants(left_projection));
            prop_assert!(!result.pool.has_variants(right_projection));
        }
    }
}
