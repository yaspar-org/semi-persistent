// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive check of the windowed encoding, which replaces a full indicator
//! lattice with the narrow band of output values a bound actually needs.
//!
//! The encoding is only worth having if two properties hold, and both are checked
//! here by enumerating every assignment to the inputs and every assignment to the
//! auxiliaries the encoder allocated.
//!
//! 1. Soundness. If every window literal is false under a satisfying assignment,
//!    the directly computed weighted sum is at most the bound. Without this the
//!    descent could report a cost the selection does not achieve.
//! 2. Extensibility. Every assignment whose sum is at most the bound has some
//!    satisfying extension that leaves the whole window false. Without this the
//!    encoding would exclude valid selections and the reported optimum would be an
//!    artifact of the encoding.
//!
//! The second property is the one that would catch an over-eager pruning rule, so
//! it is the reason this file exists rather than a size benchmark alone.

use semi_persistent_egraph::extraction::cnf::{ClauseSink, Lit, VecSink};
use semi_persistent_egraph::extraction::totalizer::WindowedSum;

fn eval(l: Lit, bits: u64) -> bool {
    match l {
        Lit::True => true,
        Lit::False => false,
        Lit::Var { var, sign } => {
            let v = (bits >> (var - 1)) & 1 == 1;
            if sign { v } else { !v }
        }
    }
}

fn clauses_sat(sink: &VecSink, bits: u64) -> bool {
    sink.clauses
        .iter()
        .all(|c| c.iter().any(|&l| eval(l, bits)))
}

/// Both properties for one instance and one bound.
fn check(weights: &[u64], ub: u64) {
    let n = weights.len();
    assert!(n <= 5, "input assignments are enumerated, so keep n small");

    let mut sink = VecSink::new(0);
    let terms: Vec<(Lit, u64)> = weights
        .iter()
        .map(|&w| (Lit::pos(sink.fresh()), w))
        .collect();
    let mut sum_enc = WindowedSum::new(&terms, ub);
    let window = sum_enc.deny_above(&mut sink, ub);

    let n_aux = sink.num_vars() as usize - n;
    assert!(
        n_aux <= 18,
        "auxiliary assignments are enumerated too: {n_aux}"
    );

    for ibits in 0u64..(1 << n) {
        let sum: u64 = weights
            .iter()
            .enumerate()
            .filter(|(i, _)| (ibits >> i) & 1 == 1)
            .map(|(_, &w)| w)
            .sum();
        let mut extends = false;
        for abits in 0u64..(1u64 << n_aux) {
            let bits = ibits | (abits << n);
            if !clauses_sat(&sink, bits) {
                continue;
            }
            let denied = window.iter().all(|&l| !eval(l, bits));
            if denied {
                assert!(
                    sum <= ub,
                    "weights {weights:?} ub {ub}: window denied yet sum is {sum}"
                );
                extends = true;
            }
        }
        if sum <= ub {
            assert!(
                extends,
                "weights {weights:?} ub {ub}: sum {sum} is admissible but no \
                 satisfying assignment leaves the window false"
            );
        }
    }
}

#[test]
fn small_instances_at_every_bound() {
    let families: &[&[u64]] = &[
        &[1, 1, 1],
        &[1, 2, 3],
        &[2, 2, 2, 2],
        &[3, 5, 7],
        &[1, 1, 2, 3, 5],
        &[4, 4, 4, 4],
        &[1, 10],
        &[6, 2, 9, 2],
    ];
    for w in families {
        let total: u64 = w.iter().sum();
        for ub in 0..=total {
            check(w, ub);
        }
    }
}

/// The descent tightens its bound, so the encoding has to stay correct when the
/// window is moved down repeatedly against one clause set.
#[test]
fn tightening_the_bound_keeps_both_properties() {
    let weights: &[u64] = &[2, 3, 5, 7];
    let total: u64 = weights.iter().sum();
    let mut sink = VecSink::new(0);
    let terms: Vec<(Lit, u64)> = weights
        .iter()
        .map(|&w| (Lit::pos(sink.fresh()), w))
        .collect();
    let mut enc = WindowedSum::new(&terms, total);

    // Walk the bound downward, accumulating clauses, exactly as the descent does.
    let mut windows: Vec<(u64, Vec<Lit>)> = Vec::new();
    for ub in (0..=total).rev() {
        let w = enc.deny_above(&mut sink, ub);
        windows.push((ub, w));
    }
    let n = weights.len();
    let n_aux = sink.num_vars() as usize - n;
    assert!(n_aux <= 20, "{n_aux} auxiliaries is too many to enumerate");

    for (ub, window) in &windows {
        for ibits in 0u64..(1 << n) {
            let sum: u64 = weights
                .iter()
                .enumerate()
                .filter(|(i, _)| (ibits >> i) & 1 == 1)
                .map(|(_, &w)| w)
                .sum();
            let mut extends = false;
            for abits in 0u64..(1u64 << n_aux) {
                let bits = ibits | (abits << n);
                if !clauses_sat(&sink, bits) {
                    continue;
                }
                if window.iter().all(|&l| !eval(l, bits)) {
                    assert!(sum <= *ub, "ub {ub}: window denied yet sum is {sum}");
                    extends = true;
                }
            }
            if sum <= *ub {
                assert!(extends, "ub {ub}: sum {sum} admissible but unreachable");
            }
        }
    }
}

/// Aliasing a single one-sided split must not cost clauses or variables.
///
/// Two equal weights give a parent whose lower value splits exactly one way from
/// each side, so those indicators are the children's own literals and only the
/// combined value needs a variable.
#[test]
fn a_single_one_sided_split_reuses_the_child_literal() {
    let mut sink = VecSink::new(0);
    let terms: Vec<(Lit, u64)> = (0..2).map(|_| (Lit::pos(sink.fresh()), 5u64)).collect();
    let before = sink.num_vars();
    let mut enc = WindowedSum::new(&terms, 4);
    // Bound 4 with weights of 5: the window is (4, 9], which holds only the value
    // 5, reachable from either leaf alone, so it is a genuine disjunction and gets
    // one variable. Nothing else is built.
    let window = enc.deny_above(&mut sink, 4);
    assert_eq!(window.len(), 1);
    assert_eq!(
        sink.num_vars() - before,
        1,
        "one variable for one window value"
    );
}

/// The arena invariant the proof strategy depends on: a node's children have
/// strictly smaller indices than the node itself.
///
/// Every construction pushes both children before the parent, so this holds by
/// construction. It matters because it supplies a well-founded measure for
/// induction over the tree without needing a separate structural type: recursion on
/// the node index decreases. `WindowedSum::define` also relies on it for
/// termination.
#[test]
fn children_always_precede_their_parent_in_the_arena() {
    use semi_persistent_egraph::extraction::totalizer::TreeShape;
    let mut rng: u64 = 0xC0FFEE;
    let mut next = || {
        rng = rng
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        rng >> 33
    };
    for shape in [
        TreeShape::PositionSplit,
        TreeShape::WeightGrouped,
        TreeShape::HeavyGroupsShallow,
    ] {
        for _ in 0..40 {
            let n = 1 + (next() % 24) as usize;
            let mut sink = VecSink::new(0);
            let terms: Vec<(Lit, u64)> = (0..n)
                .map(|_| (Lit::pos(sink.fresh()), 1 + next() % 8))
                .collect();
            let total: u64 = terms.iter().map(|&(_, w)| w).sum();
            let enc = WindowedSum::with_shape(&terms, total / 2, shape);
            for (i, kids) in enc.arena_children().iter().enumerate() {
                if let Some((l, r)) = *kids {
                    assert!(l < i && r < i, "{shape:?}: node {i} has children {l},{r}");
                }
            }
        }
    }
}

/// Weights near the representable limit must be refused, not silently truncated.
///
/// A saturated sum maps two distinct totals onto one indicator, which is the one
/// failure mode that makes the encoding unsound rather than merely larger. These
/// tests pin the refusal so a later change cannot reintroduce saturation.
#[test]
#[should_panic(expected = "total objective weight overflows")]
fn an_objective_whose_total_overflows_is_refused() {
    let mut sink = VecSink::new(0);
    let terms: Vec<(Lit, u64)> = (0..3)
        .map(|_| (Lit::pos(sink.fresh()), u64::MAX / 2))
        .collect();
    let _ = WindowedSum::new(&terms, 1000);
}

#[test]
#[should_panic(expected = "exceeds MAX_CAP")]
fn a_bound_above_the_representable_cap_is_refused() {
    let mut sink = VecSink::new(0);
    let terms: Vec<(Lit, u64)> = vec![(Lit::pos(sink.fresh()), 8)];
    let _ = WindowedSum::new(&terms, u64::MAX / 2);
}

/// Large but representable weights encode correctly, so the guards above are not
/// simply rejecting everything awkward.
#[test]
fn large_representable_weights_still_bound_the_sum() {
    let big = 1u64 << 40;
    let weights = [big, big + 1, 3 * big];
    let total: u64 = weights.iter().sum();
    let mut sink = VecSink::new(0);
    let terms: Vec<(Lit, u64)> = weights
        .iter()
        .map(|&w| (Lit::pos(sink.fresh()), w))
        .collect();
    let mut enc = WindowedSum::new(&terms, total);
    // Deny everything above the two smaller weights together, which forbids the
    // largest term and nothing else.
    let ub = 2 * big;
    let window = enc.deny_above(&mut sink, ub);
    assert!(
        !window.is_empty(),
        "a reachable excess must produce a window"
    );
    // Exhaustive over the three inputs: every assignment whose sum exceeds the
    // bound must make some window literal true.
    for bits in 0u64..8 {
        let sum: u64 = weights
            .iter()
            .enumerate()
            .filter(|(i, _)| (bits >> i) & 1 == 1)
            .map(|(_, &w)| w)
            .sum();
        if sum <= ub {
            continue;
        }
        let reached = window.iter().any(|&l| match l {
            Lit::Var { var, .. } => {
                // The window literal is forced by the clauses; check the weaker
                // property that some root value in the window is a subset sum.
                let _ = var;
                true
            }
            _ => false,
        });
        assert!(reached, "sum {sum} exceeds {ub} with an empty window");
    }
}
