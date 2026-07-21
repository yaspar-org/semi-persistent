// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Diagnostic fixtures for anti-unifier quality metrics.
//!
//! These tests deliberately do not reimplement search. They pin the mathematical
//! relationship between:
//! * raw anti-unifier size;
//! * the linear compression ratio;
//! * the current Python proof-of-concept reward (`mcts.py`, `AUNode::ucb1_value`);
//! * the original e-class NCR intent; and
//! * Rust's approved `(size, variant_mass)` tie-break.
//!
//! They also expose why normalization constants must be shared by all actions of
//! one OR node: action-local constants can reverse the underlying size ordering.

use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, anti_unify};
use semi_persistent_egraph::au::terms::{TermOp, TermPool};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::{DenseId, EGraph31};

const X_TARGET: f64 = 0.8;
const EPS: f64 = 1e-12;

fn assert_close(actual: f64, expected: f64) {
    assert!(
        (actual - expected).abs() <= EPS,
        "actual={actual}, expected={expected}"
    );
}

/// Negative-exponential map from the original quality proposal.
fn unbounded_exp_normalize(value: f64, scale: f64, x_target: f64) -> f64 {
    if value <= 0.0 {
        return 0.0;
    }
    if scale <= 0.0 {
        return 1.0;
    }
    let decay = -(1.0 - x_target).ln() / scale;
    1.0 - (-decay * value).exp()
}

fn linear_compression_ratio(au_size: u32, left_best: u32, right_best: u32) -> f64 {
    let min_repr = left_best.min(right_best) as f64;
    let max_repr = left_best.max(right_best) as f64;
    (au_size as f64 - min_repr) / max_repr
}

/// Current Python proof-of-concept behavior:
///
/// `cr = (reward - min(left, right)) / max(left, right)`
/// `ncr = unbounded_exp_normalize(cr, 1.0, 0.8)`
///
/// Algebraically this normalizes `size - min` with scale `max`, not `max - min`.
fn python_ncr(au_size: f64, left_best: f64, right_best: f64) -> f64 {
    let min_repr = left_best.min(right_best);
    let max_repr = left_best.max(right_best);
    let cr = (au_size - min_repr) / max_repr;
    unbounded_exp_normalize(cr, 1.0, X_TARGET)
}

/// Original e-class NCR intent supplied with this review:
/// adjusted = size - min_repr; scale = max_repr - min_repr.
fn intended_eclass_ncr(au_size: f64, left_best: f64, right_best: f64) -> f64 {
    let min_repr = left_best.min(right_best);
    let max_repr = left_best.max(right_best);
    unbounded_exp_normalize(au_size - min_repr, max_repr - min_repr, X_TARGET)
}

/// Formula currently used by Rust selection once its caller supplies bounds.
fn rust_selection_ncr(value: f64, min_size: f64, max_size: f64) -> f64 {
    let local_cr = (value - min_size) / max_size;
    unbounded_exp_normalize(local_cr, 1.0, X_TARGET)
}

#[test]
fn fixed_pair_size_and_compression_metrics_have_identical_strict_rankings() {
    // For one e-class pair with left_best != right_best, every metric below is
    // a strictly increasing function of au_size. Therefore they choose exactly
    // the same minimum-size anti-unifier; normalization changes calibration,
    // not the argmin.
    let (left_best, right_best) = (5_u32, 10_u32);
    for a in 5_u32..=30 {
        for b in 5_u32..=30 {
            let size_order = a.cmp(&b);
            let linear_order = linear_compression_ratio(a, left_best, right_best)
                .partial_cmp(&linear_compression_ratio(b, left_best, right_best))
                .unwrap();
            let python_order = python_ncr(a as f64, left_best as f64, right_best as f64)
                .partial_cmp(&python_ncr(b as f64, left_best as f64, right_best as f64))
                .unwrap();
            let intended_order = intended_eclass_ncr(a as f64, left_best as f64, right_best as f64)
                .partial_cmp(&intended_eclass_ncr(
                    b as f64,
                    left_best as f64,
                    right_best as f64,
                ))
                .unwrap();

            assert_eq!(linear_order, size_order);
            assert_eq!(python_order, size_order);
            assert_eq!(intended_order, size_order);
        }
    }
}

#[test]
fn original_intent_and_python_pin_different_reference_points() {
    let (left_best, right_best) = (5.0, 10.0);

    // Both agree on perfect compression.
    assert_close(intended_eclass_ncr(5.0, left_best, right_best), 0.0);
    assert_close(python_ncr(5.0, left_best, right_best), 0.0);

    // Original intent maps size=max_repr exactly to x_target.
    assert_close(intended_eclass_ncr(10.0, left_best, right_best), X_TARGET);

    // Python uses max_repr itself as scale, so the same point is below x_target.
    let python_at_max = python_ncr(10.0, left_best, right_best);
    assert!(python_at_max > 0.0 && python_at_max < X_TARGET);

    // Both remain bounded and monotone above the reference point.
    let intended_large = intended_eclass_ncr(100.0, left_best, right_best);
    let python_large = python_ncr(100.0, left_best, right_best);
    assert!(intended_large > X_TARGET && intended_large < 1.0);
    assert!(python_large > X_TARGET && python_large < 1.0);
}

#[test]
fn equal_representative_sizes_are_a_real_semantic_difference() {
    let left_best = 5.0;
    let right_best = 5.0;

    // Original intent has zero scale. By its stated fallback, every non-perfect
    // candidate saturates at 1 and distinct non-perfect sizes become tied.
    assert_close(intended_eclass_ncr(5.0, left_best, right_best), 0.0);
    assert_close(intended_eclass_ncr(6.0, left_best, right_best), 1.0);
    assert_close(intended_eclass_ncr(20.0, left_best, right_best), 1.0);

    // Python's max-based scale retains strict size ordering in the same case.
    let python_6 = python_ncr(6.0, left_best, right_best);
    let python_20 = python_ncr(20.0, left_best, right_best);
    assert!(python_6 < python_20 && python_20 < 1.0);
}

#[test]
fn action_local_normalization_constants_can_reverse_size_preference() {
    // Both actions belong to one hypothetical parent OR node. The first has the
    // better expected size, so every parent-pair compression metric prefers it.
    let better_size = 10.0;
    let worse_size = 12.0;
    assert!(python_ncr(better_size, 5.0, 10.0) < python_ncr(worse_size, 5.0, 10.0));
    assert!(
        intended_eclass_ncr(better_size, 5.0, 10.0) < intended_eclass_ncr(worse_size, 5.0, 10.0)
    );

    // If each action instead receives unrelated child-derived bounds, the Rust
    // selection formula can prefer the larger expected term. This is why all
    // actions at an OR node must be normalized against that OR node's same
    // `(left_best_size, right_best_size)` basis.
    let better_with_bad_local_bounds = rust_selection_ncr(better_size, 2.0, 2.0);
    let worse_with_favorable_local_bounds = rust_selection_ncr(worse_size, 11.0, 11.0);
    assert!(worse_with_favorable_local_bounds < better_with_bad_local_bounds);
}

#[test]
fn compression_metrics_cannot_break_equal_size_ties_but_variant_mass_can() {
    let mut pool = TermPool::<OpId, ENodeId>::new();
    let f = OpId::from_usize(0);
    let x = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
    let y = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
    let fy = pool.intern(TermOp::EGraph(f), &[y]);

    let bare = pool.intern(TermOp::Variants, &[x, fy]);
    let variants_xy = pool.intern(TermOp::Variants, &[x, y]);
    let factored = pool.intern(TermOp::EGraph(f), &[variants_xy]);

    assert_eq!(pool.size(bare), 3);
    assert_eq!(pool.size(factored), 3);

    // Every compression metric based only on size ties these candidates.
    assert_close(python_ncr(3.0, 1.0, 2.0), python_ncr(3.0, 1.0, 2.0));
    assert_close(
        intended_eclass_ncr(3.0, 1.0, 2.0),
        intended_eclass_ncr(3.0, 1.0, 2.0),
    );

    // Approved secondary objective: preserve more backbone at equal size.
    assert_eq!(pool.variant_mass(bare), 3);
    assert_eq!(pool.variant_mass(factored), 2);
    assert!(pool.quality(factored) < pool.quality(bare));
}

#[test]
fn exact_and_uct_apply_the_approved_equal_size_backbone_tie_break() {
    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
    let sort = eg.intern_sort("S");
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let f_op = eg.register_op1("f", sort, sort);

    let x = eg.add(x_op, &[]);
    let fx = eg.add(f_op, &[x]);
    let y = eg.add(y_op, &[]);
    let fy = eg.add(f_op, &[y]);
    eg.merge(x, fx); // left class contains both x and f(x)
    eg.rebuild();

    let snapshot = AuSnapshot::new(&eg).unwrap();

    for algorithm in [AuAlgorithm::Exact, AuAlgorithm::Uct] {
        let result = anti_unify(
            &snapshot,
            x,
            fy,
            &AuConfig {
                algorithm,
                playouts: 1_000,
                ..Default::default()
            },
        )
        .unwrap();

        assert_eq!(result.size, 3, "{algorithm:?}");
        assert_eq!(result.pool.variant_mass(result.term_id), 2, "{algorithm:?}");
        assert_eq!(*result.pool.op(result.term_id), TermOp::EGraph(f_op));
    }
}

#[test]
fn raw_size_is_not_comparable_across_different_eclass_pairs() {
    // Across independent AU problems, a smaller absolute term can represent much
    // worse compression. Raw size prefers B (7 < 8), while either normalized
    // metric prefers A relative to each problem's own representatives.
    let candidate_a = (8.0, 5.0, 10.0); // size, left_best, right_best
    let candidate_b = (7.0, 1.0, 2.0);
    assert!(candidate_b.0 < candidate_a.0);
    assert!(
        python_ncr(candidate_a.0, candidate_a.1, candidate_a.2)
            < python_ncr(candidate_b.0, candidate_b.1, candidate_b.2)
    );
    assert!(
        intended_eclass_ncr(candidate_a.0, candidate_a.1, candidate_a.2)
            < intended_eclass_ncr(candidate_b.0, candidate_b.1, candidate_b.2)
    );
}

#[test]
fn projection_relative_compression_can_disagree_with_minimum_total_size() {
    // This is NOT the current Python metric: Python fixes the baseline to the
    // optimal representatives of the e-class pair. It captures an alternative
    // interpretation of "best compression": compare each AU with the concrete
    // representatives that its own projections produce.
    fn projection_relative_cr(au_size: f64, left_projection: f64, right_projection: f64) -> f64 {
        let min_projection = left_projection.min(right_projection);
        let max_projection = left_projection.max(right_projection);
        (au_size - min_projection) / max_projection
    }

    // A chooses larger representatives but factors them very effectively.
    let candidate_a = (12.0, 10.0, 10.0);
    // B is absolutely smaller but preserves less of its chosen inputs as backbone.
    let candidate_b = (8.0, 5.0, 7.0);

    assert!(candidate_b.0 < candidate_a.0, "minimum size chooses B");
    assert!(
        projection_relative_cr(candidate_a.0, candidate_a.1, candidate_a.2)
            < projection_relative_cr(candidate_b.0, candidate_b.1, candidate_b.2),
        "projection-relative compression chooses A"
    );
}

#[test]
fn python_scale_maps_the_bare_variants_no_compression_point_to_x_target() {
    let (left_best, right_best) = (5.0, 10.0);
    // Variants itself is free, but both concrete arms count toward AU size.
    let bare_variants_size = left_best + right_best;

    // This is exactly CR=1 under the term-level definition.
    assert_close(
        linear_compression_ratio(
            bare_variants_size as u32,
            left_best as u32,
            right_best as u32,
        ),
        1.0,
    );
    assert_close(
        python_ncr(bare_variants_size, left_best, right_best),
        X_TARGET,
    );

    // The original max-min scale reaches x_target much earlier, at size=max,
    // and therefore rates the true no-sharing result as worse than x_target.
    assert!(intended_eclass_ncr(bare_variants_size, left_best, right_best) > X_TARGET);
}
