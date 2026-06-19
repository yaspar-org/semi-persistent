// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! File-based integration tests for the interpreter.
//!
//! Each `.egg` file in `tests/egg/` is run through the interpreter.
//! The first line may contain a directive comment:
//!   ;; EXPECT: ok              — program should succeed
//!   ;; EXPECT: check-failed    — a (check ...) should fail
//!   ;; EXPECT: parse-error     — parsing should fail
//!   ;; EXPECT: error           — any runtime error
//!   ;; EXPECT: panic           — should panic (overflow etc.)
//!   ;; TYPES: machine          — type group (default: bignum)
//!
//! If no EXPECT directive, defaults to "ok".

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::*;
use semi_persistent_egraph::saturate::SaturationStrategy;

/// Every `.egg` test runs under both saturation strategies; semi-naive must
/// reach the same outcome (EXPECT directive) as naive.
const STRATEGIES: [SaturationStrategy; 2] =
    [SaturationStrategy::Naive, SaturationStrategy::SemiNaive];

fn run_egg_file(path: &str, strategy: SaturationStrategy) -> (String, Vec<String>) {
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));

    let mut expect = "ok".to_string();
    let mut types = "bignum".to_string();
    let mut ac_complete = false;
    for line in src.lines().take(6) {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix(";; EXPECT:") {
            expect = rest.trim().to_string();
        }
        if let Some(rest) = line.strip_prefix(";; TYPES:") {
            types = rest.trim().to_string();
        }
        if let Some(rest) = line.strip_prefix(";; AC_COMPLETE:") {
            ac_complete = rest.trim() == "on";
        }
    }

    let groups: Vec<TypeGroup> = types
        .split(',')
        .map(|s| TypeGroup::parse(s.trim()).unwrap_or_else(|| panic!("unknown type group: {s}")))
        .collect();
    let choice = choose_litval(&groups);

    let result = match choice {
        LitValChoice::Machine => {
            run_with::<MachineLit, MachineModel>(&src, MachineModel, strategy, ac_complete)
        }
        LitValChoice::Bignum => {
            run_with::<BignumLit, BignumModel>(&src, BignumModel, strategy, ac_complete)
        }
        LitValChoice::All => run_with::<AllLit, AllModel>(&src, AllModel, strategy, ac_complete),
    };

    (expect, result)
}

fn run_with<
    L: semi_persistent_egraph::literal::LitVal,
    M: semi_persistent_egraph::lit_model::LitModel<Value = L>,
>(
    src: &str,
    model: M,
    strategy: SaturationStrategy,
    ac_complete: bool,
) -> Vec<String> {
    let surface_cmds = match semi_persistent_egraph::parser::parse_program_v2(src) {
        Ok(c) => c,
        Err(e) => return vec![format!("parse-error: {e}")],
    };
    let mut interp =
        Interpreter::<semi_persistent_egraph::nodes::DefaultConfig, L, M, true, false>::new(model);
    interp.set_strategy(strategy);
    interp.set_ac_complete(ac_complete);
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
        Ok(()) => vec![format!("ok: {} nodes", interp.eg.len())],
        Err(e) => vec![format!("error: {e}")],
    }
}

fn check(path: &str) {
    for strategy in STRATEGIES {
        let (expect, results) = run_egg_file(path, strategy);
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
            other => panic!("{path}: unknown EXPECT directive: {other}"),
        }
    }
}

fn check_panic(path: &str) {
    let src = std::fs::read_to_string(path).unwrap();
    let ac_complete = src
        .lines()
        .take(6)
        .any(|l| l.trim().strip_prefix(";; AC_COMPLETE:").is_some_and(|r| r.trim() == "on"));
    for strategy in STRATEGIES {
        let src = src.clone();
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
            interp.set_ac_complete(ac_complete);
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

// ── AC congruence completeness (superposition + inter-reduction) ──
egg_test!(ac_complete_containment, "ac_complete_containment.egg");
egg_test!(ac_complete_superposition, "ac_complete_superposition.egg");
egg_test!(ac_complete_cancel, "ac_complete_cancel.egg");
// Pins the nested-same-op flattening blocker: completion ON + no flattening panics
// the matcher. Flips to a normal `egg_test!` (EXPECT: ok) once flattening lands.
egg_test!(ac_complete_nested_match, "ac_complete_nested_match.egg", panic);
