// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! File-based integration tests for the interpreter.
//!
//! Each `.egg` file in `tests/egg/` is run through the interpreter. The first six lines may
//! carry directive comments. The feature directives mirror the CLI flags, so a test file is
//! self-contained, no env var needed:
//!   ;; EXPECT: ok|check-failed|parse-error|sort-error|error|panic   outcome (default: ok)
//!   ;; TYPES: machine                                     type group (default: bignum)
//!   ;; EVAL: naive|semi|both                              eval algorithm (default: both)
//!   ;; DERIVE_AC_EQS: on                                  eager AC completion (default off)
//!   ;; LAZY_AC_EQS: on                                    lazy AC completion at checks (default off)
//!   ;; UNION_BY: rank|size|uses|sum                       merge survivor policy (default rank)
//!   ;; CHECK_AC_BASIS: on                                 enable + assert the reduced-basis
//!                                                         invariants post-run (default off)
//!
//! EVAL `both` runs the file under naive AND semi-naive, asserting the same EXPECT outcome.
//! CHECK_AC_BASIS turns on `set_basis_checks` and, after a successful run, asserts the active
//! checks: `min_monomial` minimality and the implemented Kapur-reduced left-side conditions.
//! The report also diagnoses reducible right sides, but this harness does not reject them.
//! It needs DERIVE_AC_EQS to have anything to check.

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
    lazy_ac_eqs: bool,
    check_ac_basis: bool,
    union_by: semi_persistent_egraph::UnionBy,
}

fn parse_directives(src: &str) -> Directives {
    let mut d = Directives {
        expect: "ok".to_string(),
        types: "bignum".to_string(),
        evals: vec![SaturationStrategy::Naive, SaturationStrategy::SemiNaive],
        derive_ac_eqs: false,
        lazy_ac_eqs: false,
        check_ac_basis: false,
        union_by: semi_persistent_egraph::UnionBy::Rank,
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
        if let Some(rest) = line.strip_prefix(";; LAZY_AC_EQS:") {
            d.lazy_ac_eqs = rest.trim() == "on";
        }
        if let Some(rest) = line.strip_prefix(";; CHECK_AC_BASIS:") {
            d.check_ac_basis = rest.trim() == "on";
        }
        if let Some(rest) = line.strip_prefix(";; UNION_BY:") {
            use semi_persistent_egraph::UnionBy;
            d.union_by = match rest.trim() {
                "rank" => UnionBy::Rank,
                "size" => UnionBy::Size,
                "uses" => UnionBy::Uses,
                "sum" => UnionBy::Sum,
                other => panic!("unknown UNION_BY directive: {other}"),
            };
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
    if d.lazy_ac_eqs {
        interp.set_ac_mode(semi_persistent_egraph::interpret::AcMode::Lazy);
    }
    interp.set_union_by(d.union_by);
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
            // CHECK_AC_BASIS: after a clean run, assert the selected finite-state properties:
            // every used min_monomial is the true minimum, no rule LHS is reducible by the
            // others, and semantic-axiom critical pairs join. The diagnostic also computes
            // RHS reducibility, but this fixture gate deliberately does not assert it and
            // therefore does not establish a fully Kapur-reduced rule set.
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
    // Every file runs under both atom-scheduling modes as well as under both
    // evaluation strategies. The scheduling flag may not change what a program
    // computes, only the order in which matches are found (design chapter 20),
    // and a whole-program outcome over a hundred and seven files is the
    // broadest statement of that available.
    for runtime in [false, true] {
        semi_persistent_egraph::ematch::set_runtime_scheduling(runtime);
        for strategy in directives.evals.iter().copied() {
            let (expect, results) = run_egg_file(path, strategy, &directives);
            let output = results.join("\n");
            let at = format!("{path} [{strategy:?}, runtime_scheduling={runtime}]");
            match expect.as_str() {
                "ok" => assert!(output.starts_with("ok"), "{at}: expected ok, got: {output}"),
                "check-failed" => assert!(
                    output.contains("check failed"),
                    "{at}: expected check-failed, got: {output}"
                ),
                "parse-error" => assert!(
                    output.contains("parse-error"),
                    "{at}: expected parse-error, got: {output}"
                ),
                "error" => assert!(
                    output.starts_with("error"),
                    "{at}: expected error, got: {output}"
                ),
                "sort-error" => assert!(
                    output.starts_with("sort-error"),
                    "{at}: expected sort-error, got: {output}"
                ),
                other => panic!("{path}: unknown EXPECT directive: {other}"),
            }
        }
    }
    semi_persistent_egraph::ematch::set_runtime_scheduling(false);
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
    // Unsupported-behavior fixture: runs only under `--ignored`; `$why` states the limitation.
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

// ── Ground literals in patterns ──
// A literal written inside a pattern resolves to an `RAtom::Lit`, which used to compile
// to a `Step::Join` with no index lookup; that join yields nothing, so every rule holding
// one was dead. The first seven files all failed before the fix and cover the positions a
// literal can occupy; the eighth is the boundary, and passed before it too.
egg_test!(lit_pattern_ground, "lit_pattern_ground.egg");
egg_test!(lit_pattern_depth2, "lit_pattern_depth2.egg");
egg_test!(lit_pattern_when_guard, "lit_pattern_when_guard.egg");
egg_test!(lit_pattern_multi_body, "lit_pattern_multi_body.egg");
egg_test!(lit_pattern_string, "lit_pattern_string.egg");
egg_test!(lit_pattern_bignum, "lit_pattern_bignum.egg");
egg_test!(lit_pattern_rhs, "lit_pattern_rhs.egg");
egg_test!(
    lit_pattern_term_paths_unaffected,
    "lit_pattern_term_paths_unaffected.egg"
);

// ── Subsumption ──
egg_test!(subsume, "subsume.egg");

// ── Globals in patterns ──
egg_test!(globals_in_patterns, "globals_in_patterns.egg");

// ── Extraction ──
egg_test!(extract_basic, "extract_basic.egg");
egg_test!(extract_aci, "extract_aci.egg");

// ── Constructors (`(constructor …)`, `:cost`, `:unextractable`) ──
// A constructor is a function for congruence and matching; the difference is extraction.
egg_test!(constructor_congruence, "constructor_congruence.egg");
egg_test!(constructor_cost, "constructor_cost.egg");
// A class whose every node is `:unextractable` is an extract error naming the class.
egg_test!(constructor_unextractable, "constructor_unextractable.egg");
egg_test!(
    constructor_unextractable_alternative,
    "constructor_unextractable_alternative.egg"
);
egg_test!(
    datatype_variants_are_constructors,
    "datatype_variants_are_constructors.egg"
);

// ── Rulesets, run goals, birewrite, stats ──
egg_test!(ruleset_scoping, "ruleset_scoping.egg");
egg_test!(birewrite_both_directions, "birewrite_both_directions.egg");
egg_test!(run_until_goal, "run_until_goal.egg");
egg_test!(print_size_and_stats, "print_size_and_stats.egg");

// ── Deep multi-level constant folding ──
egg_test!(deep_constant_fold, "deep_constant_fold.egg");

// ── AC multiplicity semantics ──
egg_test!(ac_mult_exact, "ac_mult_exact.egg");
egg_test!(
    ac_multiplicity_variant_gap,
    "ac_multiplicity_variant_gap.egg"
);
egg_test!(ac_multiplicity_variant, "ac_multiplicity_variant.egg");
egg_test!(ac_lazy_entailment, "ac_lazy_entailment.egg");
egg_test!(ac_lazy_neq_derived, "ac_lazy_neq_derived.egg");
egg_test!(ac_lazy_alternation, "ac_lazy_alternation.egg");
egg_test!(semi_recanon_parent_delta, "semi_recanon_parent_delta.egg");
egg_test!(
    semi_merge_membership_delta,
    "semi_merge_membership_delta.egg"
);
egg_test!(rhs_mult_expr, "rhs_mult_expr.egg");
egg_test!(rhs_mult_expr_underflow, "rhs_mult_expr_underflow.egg");
egg_test!(rhs_comprehensions, "rhs_comprehensions.egg");
egg_test!(
    rhs_comprehension_filter_reject_node,
    "rhs_comprehension_filter_reject_node.egg"
);
egg_test!(a_interreduction_gap, "a_interreduction_gap.egg");
egg_test!(a_interreduction_eager, "a_interreduction_eager.egg");
egg_test!(a_interreduction_lazy, "a_interreduction_lazy.egg");
egg_test!(rbig_mult_lift, "rbig_mult_lift.egg");
egg_test!(rbig_pow_conformance, "rbig_pow_conformance.egg");
egg_test!(ac_mult_constraint, "ac_mult_constraint.egg");
egg_test!(ac_mult_nonlinear, "ac_mult_nonlinear.egg");

// ── AC build-side flattening (WF_flat) ──
egg_test!(ac_flatten_build, "ac_flatten_build.egg");
// Set (ACI) ops flatten at build too.
egg_test!(set_flatten_build, "set_flatten_build.egg");

// ── A-only (Seq) build-side normal form ──
// Associative-but-not-commutative ops flatten to a sequence (order preserved) and
// collapse a one-element sequence to its element, per
// `ac-algebraic-properties.md`'s A row and `04-canonization.md`. These two files
// pin both behaviors; the AC/ACI counterparts above pin the multiset forms.
egg_test!(a_flatten_build, "a_flatten_build.egg");
egg_test!(a_singleton_collapse, "a_singleton_collapse.egg");

// ── A-only matching: a fixed child an earlier atom already bound ──
// A variadic expansion checks such a child against each window and leaves it bound.
// A cleanup that clears every local child instead unbinds a variable an enclosing
// step owns: the next window rebinds it (the rule fires on positions the constraint
// excluded) and a later re-join reads it as unbound and panics.
// `ematch.rs`'s `expand_a_checks_a_prebound_fixed_child` and its two decomposition
// counterparts assert the match set directly.
egg_test!(a_prebound_fixed_child, "a_prebound_fixed_child.egg");
egg_test!(a_matrix_kron_fusion, "a_matrix_kron_fusion.egg");

// ── AC congruence completeness (superposition + inter-reduction) ──
egg_test!(ac_complete_containment, "ac_complete_containment.egg");
egg_test!(ac_complete_superposition, "ac_complete_superposition.egg");
egg_test!(ac_complete_cancel, "ac_complete_cancel.egg");
// Regression for the leapfrog_join target-clear bug: a rule with two same-op AC atoms +
// rest-vars (the bound-node ByRepr re-join cleared a target bound upstream). Completion off.
egg_test!(ac_two_same_op_atoms, "ac_two_same_op_atoms.egg");
// Same scenario under AC completion (which surfaced the bug by creating more add nodes).
egg_test!(ac_complete_nested_match, "ac_complete_nested_match.egg");
// Composable property tags: `:assoc :comm` reproduces the
// `:assoc-comm` alias behavior, and invalid tag combinations are rejected at registration.
egg_test!(alg_tags_composable_ac, "alg_tags_composable_ac.egg");
// Multiple AC (MSet) symbols complete independently.
egg_test!(ac_complete_multi_mset, "ac_complete_multi_mset.egg");
// ACI (Set) completion: the §4b superposition under an idempotent op.
egg_test!(aci_complete_superposition, "aci_complete_superposition.egg");
egg_test!(aci_complete_multi, "aci_complete_multi.egg");
// Identity (unit drop) on MSet and ACI ops.
egg_test!(identity_mset, "identity_mset.egg");
egg_test!(identity_aci, "identity_aci.egg");
// Identity unit-drop on the RECANONIZE path: a summand class merging into the unit's
// class after the node is built (Kapur Lemma 4.3). The first two are
// canonization facts (completion off); the third checks a unit-dropped rule still
// superposes (completion on).
egg_test!(identity_late_merge_mset, "identity_late_merge_mset.egg");
egg_test!(identity_late_merge_aci, "identity_late_merge_aci.egg");
egg_test!(identity_late_merge_cc, "identity_late_merge_cc.egg");
// Boundary coverage: cross_op_unit_isolation is a soundness guard for per-op
// unit dropping; the push/pop pair checks semi-persistence of the unit merge;
// the direction counterpart checks the became-a-unit sweep against
// rank-dependent survivor choice.
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
// Algebraic canonization must preserve sorts. Associative singleton collapse returns its
// only child's class, so A/AC operators are closed over one sort. Commutative sorting can
// exchange argument positions, so both argument sorts must match (the return may differ).
egg_test!(
    alg_tags_reject_a_sort_mismatch,
    "alg_tags_reject_a_sort_mismatch.egg"
);
egg_test!(
    alg_tags_reject_ac_sort_mismatch,
    "alg_tags_reject_ac_sort_mismatch.egg"
);
egg_test!(
    alg_tags_reject_comm_sort_mismatch,
    "alg_tags_reject_comm_sort_mismatch.egg"
);
egg_test!(
    alg_tags_comm_distinct_return_sort,
    "alg_tags_comm_distinct_return_sort.egg"
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
// Nilpotent (XOR) completion: mod-n cancellation, empty-to-unit, stored MSet.
egg_test!(nilpotent_xor, "nilpotent_xor.egg");
egg_test!(
    nilpotent_xor_superposition,
    "nilpotent_xor_superposition.egg"
);
// Per-rule axiom critical pairs (Kapur §4 Lemmas 4.1(ii), 4.2(ii)/4.5):
// superpositions of a rule with the op's own
// idempotency/nilpotency axiom, which the count clamp alone cannot derive.
egg_test!(aci_rule_axiom_cp, "aci_rule_axiom_cp.egg");
egg_test!(nilpotent_rule_axiom_cp, "nilpotent_rule_axiom_cp.egg");
egg_test!(nilpotent3_rule_axiom_cp, "nilpotent3_rule_axiom_cp.egg");
// Axiom-pair boundary cases: singleton LHS whose second reduct empties to the unit,
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
// invariant that these operations belong to canonization rather than completion.
egg_test!(canonize_clamp_no_cc, "canonize_clamp_no_cc.egg");

// Unit recanonization: `CanonMode` carries the unit class, and the
// became-a-unit sweep revisits the surviving side's parents.
egg_test!(identity_recanon_set, "identity_recanon_set.egg");
egg_test!(identity_recanon_mset, "identity_recanon_mset.egg");
// Kapur §4 semantic-property axiom critical pairs: idempotent 4.1(ii),
// nilpotent 4.2(ii), and the general-order arm at order 3.
egg_test!(idem_semantic_cp, "idem_semantic_cp.egg");
egg_test!(nilpotent_semantic_cp, "nilpotent_semantic_cp.egg");
egg_test!(nilpotent3_semantic_cp, "nilpotent3_semantic_cp.egg");
// `:cancellative` drives the Kapur §5 cancel-closure inferences (rule cancel-close,
// cancelative disjoint superposition, and the no-identity §5.2(iii)(b) per-constant
// case). Focused coverage for constants introduced after an earlier completion
// fixpoint remains future work. `:inverse` drives inverse-pair cancellation at build
// and in the completion round.
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
// Root-binding pattern form `(= v pat)`: `v` names the e-class `pat` matched. Repeating
// the name across conjuncts joins them on that class, which is what a guard on an
// equality between two derived terms needs; the negative counterpart in each file has the same
// terms present in distinct classes and asserts the rule does not fire.
egg_test!(root_binding_bind_and_use, "root_binding_bind_and_use.egg");
egg_test!(root_binding_shared_root, "root_binding_shared_root.egg");
egg_test!(root_binding_nonlinear, "root_binding_nonlinear.egg");
egg_test!(root_binding_when_global, "root_binding_when_global.egg");
egg_test!(root_binding_rewrite_lhs, "root_binding_rewrite_lhs.egg");
egg_test!(root_binding_reject_arity, "root_binding_reject_arity.egg");
// A shared root whose merge happens mid-run: the enabling event changes no node's tuple,
// so the rule has to be matched against the whole graph every round. Runs under both
// evaluation strategies, which is what makes it the regression test.
egg_test!(
    root_binding_merge_during_run,
    "root_binding_merge_during_run.egg"
);
// Primitive predicates in `:when`: a guard is evaluated over the literal values the
// patterns bound, not matched against the e-graph. Each positive file carries its
// soundness counterpart, a term the guard is false for, and asserts the rule did not fire.
egg_test!(when_prim_predicate, "when_prim_predicate.egg");
egg_test!(
    when_prim_predicate_two_vars,
    "when_prim_predicate_two_vars.egg"
);
egg_test!(when_prim_predicate_nested, "when_prim_predicate_nested.egg");
egg_test!(
    when_prim_predicate_reject_non_bool,
    "when_prim_predicate_reject_non_bool.egg"
);
egg_test!(
    when_prim_predicate_reject_unbound,
    "when_prim_predicate_reject_unbound.egg"
);
egg_test!(
    when_prim_predicate_reject_in_lhs,
    "when_prim_predicate_reject_in_lhs.egg"
);

egg_test!(eq_global_only_atom, "eq_global_only_atom.egg");

// The README's autoformalization example is executable documentation. Its
// `checkau` commands guard the documented size-42 bound before domain
// saturation, the size-8/9 identity-padding examples, and the size-35
// Exact/UCT bounds afterward.
#[test]
fn readme_au_policy_divergence() {
    check("examples/au_policy_divergence.egg");
}

// ── Cross-engine benchmark corpus (`tests/egg/bench/`) ──
//
// The same programs `scripts/egglog-compare/compare.py` times against egglog and
// `benches/corpus.rs` times in process. Registered here because they carry
// `(check ...)` commands: their correctness is a test, their timing is not.

egg_test!(
    bench_acgen_native,
    "bench/acgen.native.egg",
    ignore = "slow: 32 s under both strategies; run with --ignored"
);
egg_test!(
    bench_acgen_rules,
    "bench/acgen.rules.egg",
    ignore = "slow: 32 s under both strategies; run with --ignored"
);
egg_test!(bench_array_rules, "bench/array.rules.egg");
egg_test!(bench_bdd_native, "bench/bdd.native.egg");
egg_test!(bench_bdd_rules, "bench/bdd.rules.egg");
egg_test!(bench_calc_native, "bench/calc.native.egg");
egg_test!(bench_calc_rules, "bench/calc.rules.egg");
egg_test!(bench_combinators_rules, "bench/combinators.rules.egg");
egg_test!(bench_eqsat_basic_native, "bench/eqsat-basic.native.egg");
egg_test!(bench_eqsat_basic_rules, "bench/eqsat-basic.rules.egg");
egg_test!(bench_eqsolve_native, "bench/eqsolve.native.egg");
egg_test!(bench_eqsolve_rules, "bench/eqsolve.rules.egg");
egg_test!(bench_herbie_native, "bench/herbie.native.egg");
egg_test!(bench_herbie_rules, "bench/herbie.rules.egg");
egg_test!(bench_integer_math_native, "bench/integer_math.native.egg");
egg_test!(bench_integer_math_rules, "bench/integer_math.rules.egg");
egg_test!(bench_intersection_rules, "bench/intersection.rules.egg");
egg_test!(bench_knapsack_rules, "bench/knapsack.rules.egg");
egg_test!(
    bench_levenshtein_distance_rules,
    "bench/levenshtein-distance.rules.egg"
);
egg_test!(bench_math_add_ac_native, "bench/math-add-ac.native.egg");
egg_test!(bench_math_add_ac_rules, "bench/math-add-ac.rules.egg");
egg_test!(
    bench_math_microbenchmark_native,
    "bench/math-microbenchmark.native.egg"
);
egg_test!(
    bench_math_microbenchmark_rules,
    "bench/math-microbenchmark.rules.egg"
);
egg_test!(bench_matrix_native_a, "bench/matrix.native-A.egg");
egg_test!(bench_matrix_native, "bench/matrix.native.egg");
egg_test!(bench_matrix_rules, "bench/matrix.rules.egg");
egg_test!(bench_resolution_native, "bench/resolution.native.egg");
egg_test!(bench_resolution_rules, "bench/resolution.rules.egg");
egg_test!(bench_subsume_rules, "bench/subsume.rules.egg");
egg_test!(bench_typecheck_rules, "bench/typecheck.rules.egg");
egg_test!(bench_until_native, "bench/until.native.egg");
egg_test!(bench_until_rules, "bench/until.rules.egg");
