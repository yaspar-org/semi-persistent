// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive check of the property the extractor depends on.
//!
//! For a small instance the test enumerates every assignment to the input
//! literals, then every assignment to the auxiliary variables the encoder
//! allocated, and asks two questions:
//!
//! 1. Soundness of the bound. For each threshold `t`, if some satisfying
//!    extension leaves the indicator for `t` false, then the directly computed
//!    weighted sum is below `t`. This is the property the descent uses, so a
//!    failure here would let the extractor report a cost it cannot realize.
//! 2. Extensibility. Every assignment to the inputs has at least one satisfying
//!    extension to the auxiliaries. Without it the encoding could exclude a
//!    valid selection, and the reported optimum would be an artifact.

use semi_persistent_egraph::extraction::cnf::{ClauseSink, Lit, VecSink};
use semi_persistent_egraph::extraction::totalizer::encode_sum;

/// Read a literal under an assignment given as a bit set over variable indices.
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

/// Run both checks over every assignment for one instance.
fn check_instance(weights: &[u64], bound: u64) {
    let n = weights.len();
    assert!(n <= 5, "input assignments are enumerated, so keep n small");

    let mut sink = VecSink::new(0);
    // Input literals occupy variables 1..=n.
    let mut inputs: Vec<u32> = Vec::new();
    for _ in 0..n {
        inputs.push(sink.fresh());
    }
    let weighted: Vec<(Lit, u64)> = inputs
        .iter()
        .zip(weights)
        .map(|(&v, &w)| (Lit::pos(v), w))
        .collect();

    let sums = encode_sum(&mut sink, &weighted, bound);
    let total_vars = sink.num_vars();
    let aux_vars = total_vars - n as u32;
    assert!(
        aux_vars <= 18,
        "auxiliary assignments are enumerated: {aux_vars} is too many for {weights:?}"
    );

    for input_bits in 0u64..(1u64 << n) {
        // The directly computed sum, which is the reference.
        let mut real = 0u64;
        for (i, &w) in weights.iter().enumerate() {
            if (input_bits >> i) & 1 == 1 {
                real += w;
            }
        }

        let mut any_extension = false;
        for aux_bits in 0u64..(1u64 << aux_vars) {
            let bits = input_bits | (aux_bits << n);
            if !clauses_sat(&sink, bits) {
                continue;
            }
            any_extension = true;

            for (i, &t) in sums.thresholds.iter().enumerate() {
                if !eval(sums.indicators[i], bits) {
                    assert!(
                        real < t,
                        "indicator for threshold {t} is false under a satisfying \
                         assignment whose real sum is {real} (weights {weights:?}, \
                         bound {bound}, inputs {input_bits:#b})"
                    );
                }
            }
        }
        assert!(
            any_extension,
            "no satisfying extension for inputs {input_bits:#b} (weights {weights:?}, bound {bound})"
        );
    }
}

#[test]
fn unit_weights() {
    for n in 1..=5 {
        let weights = vec![1u64; n];
        for bound in 1..=(n as u64) {
            check_instance(&weights, bound);
        }
    }
}

#[test]
fn distinct_small_weights() {
    check_instance(&[1, 2, 3], 6);
    check_instance(&[1, 2, 4], 7);
    check_instance(&[2, 3, 5], 10);
    check_instance(&[1, 1, 2, 3], 7);
}

#[test]
fn bound_below_total() {
    // A bound under the total weight truncates the tracked sums. The soundness
    // check still has to hold for the thresholds that remain.
    check_instance(&[1, 2, 3], 3);
    check_instance(&[2, 3, 5], 5);
    check_instance(&[1, 2, 4], 4);
    check_instance(&[3, 3, 3], 4);
}

#[test]
fn repeated_weights_share_thresholds() {
    // The encoding's size follows the count of distinct achievable sums, so
    // repeated weights should collapse thresholds rather than multiply them.
    check_instance(&[5, 5, 5], 15);
    check_instance(&[7, 7], 14);
}

#[test]
fn zero_weight_dropped() {
    let mut sink = VecSink::new(0);
    let a = Lit::pos(sink.fresh());
    let b = Lit::pos(sink.fresh());
    let sums = encode_sum(&mut sink, &[(a, 0), (b, 3)], 3);
    assert_eq!(sums.thresholds, vec![3]);
}

#[test]
fn weight_above_bound_dropped() {
    let mut sink = VecSink::new(0);
    let a = Lit::pos(sink.fresh());
    let b = Lit::pos(sink.fresh());
    // Weight 9 cannot contribute under a bound of 4, so only 2 is tracked.
    let sums = encode_sum(&mut sink, &[(a, 9), (b, 2)], 4);
    assert_eq!(sums.thresholds, vec![2]);
}

#[test]
fn indicator_lookup_rounds_up_to_achievable() {
    let mut sink = VecSink::new(0);
    let a = Lit::pos(sink.fresh());
    let b = Lit::pos(sink.fresh());
    let sums = encode_sum(&mut sink, &[(a, 3), (b, 5)], 8);
    assert_eq!(sums.thresholds, vec![3, 5, 8]);
    // Asking to bound the sum below 4 must negate the indicator for 5, not 3:
    // negating 3 would also forbid a sum of 3, which is under the bound.
    assert_eq!(sums.indicator_at_least(4), Some(sums.indicators[1]));
    assert_eq!(sums.indicator_at_least(3), Some(sums.indicators[0]));
    // No achievable threshold reaches 9, so the bound holds with no assumption.
    assert_eq!(sums.indicator_at_least(9), None);
}

#[test]
fn empty_and_degenerate_inputs() {
    let mut sink = VecSink::new(0);
    assert!(encode_sum(&mut sink, &[], 10).thresholds.is_empty());
    let a = Lit::pos(sink.fresh());
    assert!(encode_sum(&mut sink, &[(a, 1)], 0).thresholds.is_empty());
    // A bound of zero forbids the term rather than dropping it. Dropping it would
    // let a model set `a` and carry a sum of 1 that no indicator reports, which is
    // exactly the error that makes the descent claim an unachievable cost. So the
    // unit clause is required, and this asserted its absence.
    assert_eq!(sink.num_clauses(), 1);
    assert_eq!(sink.clauses[0], vec![a.not()]);
}

#[test]
fn dimacs_has_no_constants() {
    let mut sink = VecSink::new(0);
    let lits: Vec<Lit> = (0..4).map(|_| Lit::pos(sink.fresh())).collect();
    let weighted: Vec<(Lit, u64)> = lits.iter().map(|&l| (l, 2)).collect();
    encode_sum(&mut sink, &weighted, 8);
    let text = sink.to_dimacs();
    assert!(text.starts_with("p cnf "));
    for line in text.lines().skip(1) {
        assert!(line.ends_with('0'));
    }
}

// ---------------------------------------------------------------------------
// The windowed encoding
// ---------------------------------------------------------------------------

/// Both properties the descent depends on, for [`WindowedSum`].
///
/// The windowed encoding denies a *band* of output values rather than a single
/// threshold, so the properties are restated against that interface:
///
/// 1. Soundness. If every window literal is false under a satisfying extension,
///    the directly computed sum is at most `ub`. A failure here lets the extractor
///    claim a cost it cannot realize, which is the one error that matters.
/// 2. Extensibility. Every input assignment whose sum is at most `ub` has a
///    satisfying extension with all window literals false. Without it the encoding
///    would exclude valid selections and the reported optimum would be an artifact.
fn check_windowed(weights: &[u64], ub: u64) {
    use semi_persistent_egraph::extraction::totalizer::WindowedSum;
    let n = weights.len();
    assert!(n <= 5, "input assignments are enumerated, so keep n small");

    let mut sink = VecSink::new(0);
    let mut inputs: Vec<u32> = Vec::new();
    for _ in 0..n {
        inputs.push(sink.fresh());
    }
    let terms: Vec<(Lit, u64)> = inputs
        .iter()
        .zip(weights)
        .map(|(&v, &w)| (Lit::pos(v), w))
        .collect();

    let mut enc = WindowedSum::new(&terms, ub);
    let window = enc.deny_above(&mut sink, ub);
    let total_vars = sink.num_vars();
    let aux = total_vars - n as u32;
    assert!(
        aux <= 18,
        "auxiliary assignments are enumerated too: {aux} is too many"
    );

    for input_bits in 0u64..(1 << n) {
        let sum: u64 = weights
            .iter()
            .enumerate()
            .filter(|(i, _)| (input_bits >> i) & 1 == 1)
            .map(|(_, w)| *w)
            .sum();
        let mut extensible_with_window_false = false;
        for aux_bits in 0u64..(1u64 << aux) {
            let bits = input_bits | (aux_bits << n);
            if !clauses_sat(&sink, bits) {
                continue;
            }
            let window_all_false = window.iter().all(|&l| !eval(l, bits));
            if window_all_false {
                // Property 1.
                assert!(
                    sum <= ub,
                    "weights {weights:?} ub {ub}: window denied but sum is {sum}"
                );
                extensible_with_window_false = true;
            }
        }
        // Property 2.
        if sum <= ub {
            assert!(
                extensible_with_window_false,
                "weights {weights:?} ub {ub}: sum {sum} is admissible but excluded"
            );
        }
    }
}

#[test]
fn windowed_encoding_is_sound_and_complete_over_every_assignment() {
    // Equal weights, distinct weights, weights that share factors, a weight above
    // the bound, and bounds at both ends of the achievable range.
    let cases: &[(&[u64], u64)] = &[
        (&[1], 0),
        (&[1], 1),
        (&[3], 1),
        (&[1, 1], 1),
        (&[1, 2], 2),
        (&[2, 3], 4),
        (&[1, 1, 1], 2),
        (&[1, 2, 4], 3),
        (&[3, 3, 3], 5),
        (&[5, 1, 1], 2),
        (&[2, 4, 6], 7),
        (&[1, 2, 3, 4], 5),
        (&[2, 2, 3, 3], 6),
        (&[7, 1, 2, 3], 6),
        (&[1, 1, 1, 1, 1], 3),
        (&[1, 2, 2, 3, 3], 5),
    ];
    for &(w, ub) in cases {
        check_windowed(w, ub);
    }
}

#[test]
fn tightening_the_bound_keeps_earlier_clauses_and_stays_sound() {
    use semi_persistent_egraph::extraction::totalizer::WindowedSum;
    // The descent only ever lowers the bound, and it must keep every clause it has
    // already given the solver. This checks that a sequence of tightenings is
    // additive and that each window is still sound at its own bound.
    let weights = [2u64, 3, 4, 5];
    let mut sink = VecSink::new(0);
    let inputs: Vec<u32> = (0..weights.len()).map(|_| sink.fresh()).collect();
    let terms: Vec<(Lit, u64)> = inputs
        .iter()
        .zip(&weights)
        .map(|(&v, &w)| (Lit::pos(v), w))
        .collect();
    let mut enc = WindowedSum::new(&terms, 14);
    let mut previous = 0usize;
    for ub in [14u64, 10, 7, 5, 3, 1] {
        let window = enc.deny_above(&mut sink, ub);
        let now = sink.clauses.len();
        assert!(
            now >= previous,
            "clauses must only be added, never rewritten"
        );
        // Soundness at this bound, over the inputs, with the auxiliaries free.
        let aux = sink.num_vars() - weights.len() as u32;
        for input_bits in 0u64..(1 << weights.len()) {
            let sum: u64 = weights
                .iter()
                .enumerate()
                .filter(|(i, _)| (input_bits >> i) & 1 == 1)
                .map(|(_, w)| *w)
                .sum();
            if sum <= ub {
                continue;
            }
            // A sum above the bound must be excluded: no extension can satisfy the
            // clauses with the whole window false.
            for aux_bits in 0u64..(1u64 << aux) {
                let bits = input_bits | (aux_bits << weights.len());
                if clauses_sat(&sink, bits) {
                    assert!(
                        !window.iter().all(|&l| !eval(l, bits)),
                        "ub {ub}: sum {sum} survived with the window denied"
                    );
                }
            }
        }
        previous = now;
    }
}
