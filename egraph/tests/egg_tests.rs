// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! File-based integration tests for the interpreter.
//!
//! Each `.egg` file in `tests/egg/` is run through the interpreter. The first six lines may
//! carry directive comments. The three feature directives mirror the CLI verbs (use / derive
//! / check), so a test file is self-contained, no env var needed:
//!   ;; EXPECT: ok|check-failed|parse-error|sort-error|error|panic   outcome (default: ok)
//!   ;; TYPES: machine                                     type group (default: bignum)
//!   ;; EVAL: naive|semi|both                              eval algorithm (default: both)
//!   ;; DERIVE_AC_EQS: on                                  derive all AC consequences (default off)
//!   ;; CHECK_AC_BASIS: on                                 enable + assert the reduced-basis
//!                                                         invariants post-run (default off)
//!
//! EVAL `both` runs the file under naive AND semi-naive, asserting the same EXPECT outcome
//! (the historical default cross-check). DERIVE_AC_EQS renames the old AC_COMPLETE directive.
//! CHECK_AC_BASIS turns on `set_basis_checks` and, after a successful run, asserts the active
//! AC rule set is fully reduced (`min_monomial` minimal, Kapur-reduced); it needs DERIVE_AC_EQS to
//! have anything to check.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::*;
use semi_persistent_egraph::saturate::SaturationStrategy;

/// Directives parsed from a `.egg` file's first six lines.
struct Directives {
    expect: String,
    types: String,
    /// The eval strategies to run under (one each for naive/semi, both for `both`).
    evals: Vec<SaturationStrategy>,
    derive_ac_eqs: bool,
    check_ac_basis: bool,
}

fn parse_directives(src: &str) -> Directives {
    let mut d = Directives {
        expect: "ok".to_string(),
        types: "bignum".to_string(),
        evals: vec![SaturationStrategy::Naive, SaturationStrategy::SemiNaive],
        derive_ac_eqs: false,
        check_ac_basis: false,
    };
    for line in src.lines().take(6) {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix(";; EXPECT:") {
            d.expect = rest.trim().to_string();
        }
        if let Some(rest) = line.strip_prefix(";; TYPES:") {
            d.types = rest.trim().to_string();
        }
        if let Some(rest) = line.strip_prefix(";; EVAL:") {
            d.evals = match rest.trim() {
                "naive" => vec![SaturationStrategy::Naive],
                "semi" | "semi-naive" => vec![SaturationStrategy::SemiNaive],
                "both" => vec![SaturationStrategy::Naive, SaturationStrategy::SemiNaive],
                other => panic!("unknown EVAL directive: {other} (expected naive|semi|both)"),
            };
        }
        if let Some(rest) = line.strip_prefix(";; DERIVE_AC_EQS:") {
            d.derive_ac_eqs = rest.trim() == "on";
        }
        if let Some(rest) = line.strip_prefix(";; CHECK_AC_BASIS:") {
            d.check_ac_basis = rest.trim() == "on";
        }
    }
    d
}

fn run_egg_file(path: &str, strategy: SaturationStrategy, d: &Directives) -> (String, Vec<String>) {
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));

    let groups: Vec<TypeGroup> = d
        .types
        .split(',')
        .map(|s| TypeGroup::parse(s.trim()).unwrap_or_else(|| panic!("unknown type group: {s}")))
        .collect();
    let choice = choose_litval(&groups);

    let result = match choice {
        LitValChoice::Machine => {
            run_with::<MachineLit, MachineModel>(&src, MachineModel, strategy, d)
        }
        LitValChoice::Bignum => run_with::<BignumLit, BignumModel>(&src, BignumModel, strategy, d),
        LitValChoice::All => run_with::<AllLit, AllModel>(&src, AllModel, strategy, d),
    };

    (d.expect.clone(), result)
}

fn run_with<
    L: semi_persistent_egraph::literal::LitVal,
    M: semi_persistent_egraph::lit_model::LitModel<Value = L>,
>(
    src: &str,
    model: M,
    strategy: SaturationStrategy,
    d: &Directives,
) -> Vec<String> {
    let surface_cmds = match semi_persistent_egraph::parser::parse_program_v2(src) {
        Ok(c) => c,
        Err(e) => return vec![format!("parse-error: {e}")],
    };
    let mut interp =
        Interpreter::<semi_persistent_egraph::nodes::DefaultConfig, L, M, true, false>::new(model);
    interp.set_strategy(strategy);
    interp.set_cc(d.derive_ac_eqs);
    interp.set_basis_checks(d.check_ac_basis);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = match semi_persistent_egraph::sortcheck::sortcheck_program(
        surface_cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    ) {
        Ok(c) => c,
        Err(e) => return vec![format!("sort-error: {e}")],
    };
    match interp.run_checked(&checked) {
        Ok(()) => {
            // CHECK_AC_BASIS: after a clean run, assert the active AC rule set is fully
            // reduced (every used min_monomial is the true minimum; no rule LHS reducible by the
            // others). This turns the diagnostic checkers into a real test assertion.
            if d.check_ac_basis {
                let report = interp.eg.cc_basis_report();
                let (nonmin, _) = interp.eg.cc_min_used_nonminimal();
                let (lhs_red, _rhs_red) = interp.eg.cc_not_kapur_reduced();
                let (axiom_nonjoin, axiom_offenders) = interp.eg.cc_axiom_cps_nonjoinable();
                assert_eq!(
                    nonmin,
                    0,
                    "CHECK_AC_BASIS: {nonmin} rules use a non-minimal min_monomial (active_rules={})",
                    report.rules.len()
                );
                assert_eq!(
                    lhs_red,
                    0,
                    "CHECK_AC_BASIS: {lhs_red} rules have a Kapur-reducible LHS (active_rules={})",
                    report.rules.len()
                );
                assert_eq!(
                    axiom_nonjoin,
                    0,
                    "CHECK_AC_BASIS: {axiom_nonjoin} per-rule axiom critical pairs are not joinable \
                     (Kapur Lemma 4.1(ii)/4.2(ii); active_rules={}; offenders (node, op): {axiom_offenders:?})",
                    report.rules.len()
                );
            }
            vec![format!("ok: {} nodes", interp.eg.len())]
        }
        Err(e) => vec![format!("error: {e}")],
    }
}

fn check(path: &str) {
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
    let directives = parse_directives(&src);
    for strategy in directives.evals.iter().copied() {
        let (expect, results) = run_egg_file(path, strategy, &directives);
        let output = results.join("\n");
        match expect.as_str() {
            "ok" => assert!(
                output.starts_with("ok"),
                "{path} [{strategy:?}]: expected ok, got: {output}"
            ),
            "check-failed" => assert!(
                output.contains("check failed"),
                "{path} [{strategy:?}]: expected check-failed, got: {output}"
            ),
            "parse-error" => assert!(
                output.contains("parse-error"),
                "{path} [{strategy:?}]: expected parse-error, got: {output}"
            ),
            "error" => assert!(
                output.starts_with("error"),
                "{path} [{strategy:?}]: expected error, got: {output}"
            ),
            "sort-error" => assert!(
                output.starts_with("sort-error"),
                "{path} [{strategy:?}]: expected sort-error, got: {output}"
            ),
            other => panic!("{path}: unknown EXPECT directive: {other}"),
        }
    }
}

fn check_panic(path: &str) {
    let src = std::fs::read_to_string(path).unwrap();
    let directives = parse_directives(&src);
    for strategy in directives.evals.iter().copied() {
        let src = src.clone();
        let cc = directives.derive_ac_eqs;
        let basis_checks = directives.check_ac_basis;
        let result = std::panic::catch_unwind(move || {
            let surface_cmds = semi_persistent_egraph::parser::parse_program_v2(&src).unwrap();
            let mut interp = Interpreter::<
                semi_persistent_egraph::nodes::DefaultConfig,
                MachineLit,
                MachineModel,
                true,
                false,
            >::new(MachineModel);
            interp.set_strategy(strategy);
            interp.set_cc(cc);
            interp.set_basis_checks(basis_checks);
            let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
            let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
                surface_cmds,
                &mut interp.eg,
                &interp.model,
                &mut globals,
            )
            .unwrap();
            let _ = interp.run_checked(&checked);
        });
        assert!(
            result.is_err(),
            "{path} [{strategy:?}]: expected panic but succeeded"
        );
    }
}

macro_rules! egg_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            check(concat!("tests/egg/", $file));
        }
    };
    ($name:ident, $file:expr, panic) => {
        #[test]
        fn $name() {
            check_panic(concat!("tests/egg/", $file));
        }
    };
    // Known-failing reproducer: runs only under `--ignored`. `$why` documents the open bug.
    ($name:ident, $file:expr, ignore = $why:expr) => {
        #[test]
        #[ignore = $why]
        fn $name() {
            check(concat!("tests/egg/", $file));
        }
    };
}

// ── Arithmetic: checked (default) ──
egg_test!(checked_add_ok, "checked_add_ok.egg");
egg_test!(checked_overflow, "checked_overflow.egg", panic);

// ── Arithmetic: wrapping ──
egg_test!(wrapping_add, "wrapping_add.egg");

// ── Arithmetic: saturating ──
egg_test!(saturating_add, "saturating_add.egg");

// ── i64 comprehensive ──
egg_test!(i64_all_ops, "i64_all_ops.egg");
egg_test!(i64_wrapping_saturating, "i64_wrapping_saturating.egg");

// ── u64 comprehensive ──
egg_test!(u64_all_ops, "u64_all_ops.egg");

// ── f64 comprehensive ──
egg_test!(f64_arith, "f64_arith.egg");
egg_test!(f64_all_ops, "f64_all_ops.egg");

// ── Bignum comprehensive ──
egg_test!(bignum_arith, "bignum_arith.egg");
egg_test!(bignum_all_ops, "bignum_all_ops.egg");

// ── String comprehensive ──
egg_test!(string_ops, "string_ops.egg");
egg_test!(string_all_ops, "string_all_ops.egg");

// ── Comparisons and if ──
egg_test!(cmp_and_if, "cmp_and_if.egg");

// ── Bool ops ──
egg_test!(bool_ops, "bool_ops.egg");

// ── Check failures ──
egg_test!(check_neq, "check_neq.egg");

// ── Parse errors ──
egg_test!(parse_error, "parse_error.egg");

// ── Push/pop ──
egg_test!(push_pop, "push_pop.egg");

// ── Rewrites ──
egg_test!(rewrite_commute, "rewrite_commute.egg");
egg_test!(rewrite_constant_fold, "rewrite_constant_fold.egg");

// ── Subsumption ──
egg_test!(subsume, "subsume.egg");

// ── Globals in patterns ──
egg_test!(globals_in_patterns, "globals_in_patterns.egg");

// ── Extraction ──
egg_test!(extract_basic, "extract_basic.egg");
egg_test!(extract_aci, "extract_aci.egg");

// ── Deep multi-level constant folding ──
egg_test!(deep_constant_fold, "deep_constant_fold.egg");

// ── AC multiplicity semantics ──
egg_test!(ac_mult_exact, "ac_mult_exact.egg");
egg_test!(ac_mult_constraint, "ac_mult_constraint.egg");
egg_test!(ac_mult_nonlinear, "ac_mult_nonlinear.egg");

// ── AC build-side flattening (WF_flat) ──
egg_test!(ac_flatten_build, "ac_flatten_build.egg");
// Set (ACI) ops flatten at build too — the MSet-only gate was a bug (2026-07-10).
egg_test!(set_flatten_build, "set_flatten_build.egg");

// ── AC congruence completeness (superposition + inter-reduction) ──
egg_test!(ac_complete_containment, "ac_complete_containment.egg");
egg_test!(ac_complete_superposition, "ac_complete_superposition.egg");
egg_test!(ac_complete_cancel, "ac_complete_cancel.egg");
// Regression for the leapfrog_join target-clear bug: a rule with two same-op AC atoms +
// rest-vars (the bound-node ByRepr re-join cleared a target bound upstream). Completion off.
egg_test!(ac_two_same_op_atoms, "ac_two_same_op_atoms.egg");
// Same scenario under AC completion (which surfaced the bug by creating more add nodes).
egg_test!(ac_complete_nested_match, "ac_complete_nested_match.egg");
// Composable property tags (multi-AC/ACI plan Facet A): `:assoc :comm` reproduces the
// `:assoc-comm` alias behavior, and invalid tag combinations are rejected at registration.
egg_test!(alg_tags_composable_ac, "alg_tags_composable_ac.egg");
// Multiple AC (MSet) symbols complete independently (multi-AC/ACI plan, step 4).
egg_test!(ac_complete_multi_mset, "ac_complete_multi_mset.egg");
// ACI (Set) completion: the §4b superposition under an idempotent op (step 5).
egg_test!(aci_complete_superposition, "aci_complete_superposition.egg");
egg_test!(aci_complete_multi, "aci_complete_multi.egg");
// Identity (unit drop) on MSet and ACI ops (multi-AC/ACI plan, property 1).
egg_test!(identity_mset, "identity_mset.egg");
egg_test!(identity_aci, "identity_aci.egg");
// Identity unit-drop on the RECANONIZE path: a summand class merging into the unit's
// class after the node is built (Kapur Lemma 4.3; Kapur-conformance fix W2 (spec §3 table)). The first two are
// canonization facts (completion off); the third checks a unit-dropped rule still
// superposes (completion on).
egg_test!(identity_late_merge_mset, "identity_late_merge_mset.egg");
egg_test!(identity_late_merge_aci, "identity_late_merge_aci.egg");
egg_test!(identity_late_merge_cc, "identity_late_merge_cc.egg");
// Adversarial coverage batch (adversarial analysis §B): behaviors that were correct but
// unpinned. cross_op_unit_isolation is a SOUNDNESS guard (per-op unit-drop); the push/pop
// pair pins semi-persistence of the unit merge; the direction twin pins the became-a-unit
// sweep against rank-dependent survivor choice.
egg_test!(cross_op_unit_isolation, "cross_op_unit_isolation.egg");
egg_test!(
    identity_late_merge_direction,
    "identity_late_merge_direction.egg"
);
egg_test!(nilpotent_unit_then_clamp, "nilpotent_unit_then_clamp.egg");
egg_test!(push_pop_unit_merge_in, "push_pop_unit_merge_in.egg");
egg_test!(push_pop_unit_merge_out, "push_pop_unit_merge_out.egg");
egg_test!(
    alg_tags_reject_idem_nilpotent,
    "alg_tags_reject_idem_nilpotent.egg"
);
egg_test!(
    alg_tags_reject_idem_needs_ac,
    "alg_tags_reject_idem_needs_ac.egg"
);
// Idempotent + inverse is rejected: an idempotent group is trivial, so `not` is not an
// `and`-inverse (it is xor-with-true). See design doc "Inverse is a group inverse, not a
// complement".
egg_test!(
    alg_tags_reject_idem_inverse,
    "alg_tags_reject_idem_inverse.egg"
);
// :cancellative is an AC-only inference tag: on an A-only, C-only, or plain op it would
// be stored nowhere and silently ignored, so registration rejects it.
egg_test!(
    alg_tags_reject_cancellative_assoc_only,
    "alg_tags_reject_cancellative_assoc_only.egg"
);
egg_test!(
    alg_tags_reject_cancellative_comm_only,
    "alg_tags_reject_cancellative_comm_only.egg"
);
egg_test!(
    alg_tags_reject_cancellative_plain,
    "alg_tags_reject_cancellative_plain.egg"
);
// Nilpotent (XOR) completion: mod-n cancellation, empty→unit, stored MSet (multi-AC/ACI plan,
// property 2).
egg_test!(nilpotent_xor, "nilpotent_xor.egg");
egg_test!(
    nilpotent_xor_superposition,
    "nilpotent_xor_superposition.egg"
);
// Per-rule AXIOM critical pairs (Kapur §4 Lemmas 4.1(ii), 4.2(ii)/4.5; Kapur-conformance
// fix W3, spec §3 table): superpositions of a rule with the op's own
// idempotency/nilpotency axiom, which the count clamp alone cannot derive.
egg_test!(aci_rule_axiom_cp, "aci_rule_axiom_cp.egg");
egg_test!(nilpotent_rule_axiom_cp, "nilpotent_rule_axiom_cp.egg");
egg_test!(nilpotent3_rule_axiom_cp, "nilpotent3_rule_axiom_cp.egg");
// Adversarial axiom-pair edges: singleton LHS whose second reduct empties to the unit,
// and the general n−m arm with summand multiplicity m > 1.
egg_test!(
    nilpotent3_singleton_lhs_axiom,
    "nilpotent3_singleton_lhs_axiom.egg"
);
egg_test!(nilpotent3_mult2_axiom_cp, "nilpotent3_mult2_axiom_cp.egg");
// Soundness: xor(a,a) is never a (the old Set-dedup bug). check is expected to fail.
egg_test!(nilpotent_no_dedup, "nilpotent_no_dedup.egg");
// Canonization establishes the clamp / identity-drop / degeneracy normal form with completion
// OFF (build AND recanonize paths): xor(a,a)=e, and(a,a)=a, add(a,e)=a, etc. Guards the
// architecture fix that moved these out of the completion pass and into canonization.
egg_test!(canonize_clamp_no_cc, "canonize_clamp_no_cc.egg");

// ── Former known-failing reproducers, now live (fixed by the Kapur-conformance series) ──
// BUG 1 (identity unit-drop on recanonize) was fixed by Kapur-conformance fix W2 (spec §3 table) (`CanonMode`
// carries the unit class; the became-a-unit sweep revisits the surviving side's parents).
egg_test!(identity_recanon_set, "identity_recanon_set.egg");
egg_test!(identity_recanon_mset, "identity_recanon_mset.egg");
// BUG 2 (Kapur §4 semantic-property axiom critical pairs, idempotent 4.1(ii) and nilpotent
// 4.2(ii)) was fixed by Kapur-conformance fix W3 (spec §3 table); the general order-n arm covers the order-3 gate.
egg_test!(idem_semantic_cp, "idem_semantic_cp.egg");
egg_test!(nilpotent_semantic_cp, "nilpotent_semantic_cp.egg");
egg_test!(nilpotent3_semantic_cp, "nilpotent3_semantic_cp.egg");
// GATES flipped 2026-07-10: `:cancellative` drives the Kapur §5 cancel-closure
// inferences (rule cancel-close + cancelative disjoint superposition; the no-identity
// §5.2(iii)(b) per-constant case remains a documented gap), and `:inverse` drives
// inverse-pair cancellation at build and in the completion round.
egg_test!(cancellative_cancel, "cancellative_cancel.egg");
egg_test!(group_inverse_cancel, "group_inverse_cancel.egg");
// The paper's own cancelative examples: SC2 (§5.2, needs the per-constant closure) and
// Example 4 / SC3 (§5.3, cancelative disjoint superposition); plus the group facet on the
// §5b virtual-sum scenario (no user rule) and build-time multiplicity handling.
egg_test!(cancellative_sc2, "cancellative_sc2.egg");
egg_test!(
    cancellative_disjoint_superposition,
    "cancellative_disjoint_superposition.egg"
);
egg_test!(group_inverse_virtual_sum, "group_inverse_virtual_sum.egg");
egg_test!(group_inverse_multiplicity, "group_inverse_multiplicity.egg");
// Inline check/extract rebuilds after building fresh terms so AC consequences fire.
egg_test!(ac_inline_check_after_run, "ac_inline_check_after_run.egg");
// Nilpotent order validation: invalid orders produce a parse-error, not a panic.
egg_test!(
    nilpotent_order_zero_rejected,
    "nilpotent_order_zero_rejected.egg"
);
egg_test!(
    nilpotent_order_256_rejected,
    "nilpotent_order_256_rejected.egg"
);
egg_test!(nilpotent_order_255_ok, "nilpotent_order_255_ok.egg");
// Zero-child variadic applications: the empty monomial is meaningful only for an op with
// a declared identity (it is the unit); otherwise it is rejected at sortcheck.
egg_test!(
    zero_arity_mset_without_identity_rejected,
    "zero_arity_mset_without_identity_rejected.egg"
);
egg_test!(
    zero_arity_set_without_identity_rejected,
    "zero_arity_set_without_identity_rejected.egg"
);
egg_test!(
    zero_arity_with_identity_is_unit,
    "zero_arity_with_identity_is_unit.egg"
);
