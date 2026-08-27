// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Anti-unification is optimal relative to the equality relation the e-graph holds, not
//! relative to the AC theory (design ch. 19 §2.8). This file pins the consequence under
//! all three AC congruence modes.
//!
//! The fixture is the containment gap of `ac-congruence-completeness.md` §4a, wrapped in
//! one common unary operator so the anti-unifier has a backbone and the only candidate
//! disagreement is the AC-equal pair:
//!
//! ```text
//! (union (add a b) c)     ; add is :assoc :comm
//! (union (add a b d) n)   ; AC entails n = add(c, d)
//! antiunify (g n) (g (add c d))
//! ```
//!
//! Expected sizes, and why each matters:
//!
//! | mode  | size | meaning                                                          |
//! | ----- | ---- | ---------------------------------------------------------------- |
//! | plain | 5    | `(g (Variants n (add c d)))` — a reported difference the theory does not have |
//! | eager | 2    | `(g n)` — the AC optimum                                          |
//! | lazy  | 5    | identical to plain: lazy does nothing for the solver              |
//!
//! `checkau :max_size` bounds from above only, so each size is pinned by a bracket: the
//! bound that must pass and the bound one lower that must fail. A regression that made
//! plain mode reach 2, or eager mode stop reaching it, breaks a bracket in one direction
//! or the other.
//!
//! The lazy row is the one worth guarding. It is not an implementation accident that a
//! future change might silently improve; it follows from the transaction lifecycle, where
//! only `CheckEq`/`CheckNeq` keep the transaction open and every other command restores
//! the graph before running. If lazy mode ever starts reaching size 2, either that
//! lifecycle changed or the solver acquired its own completion path, and both are facts
//! §2.8 asserts are not true.

use semi_persistent_egraph::interpret::{AcMode, Interpreter};
use semi_persistent_egraph::model::{BignumLit, BignumModel};

/// The §4a containment fixture. `max_size` is the bound the trailing `checkau` asserts.
fn program(max_size: u32) -> String {
    format!(
        "(sort E)\n\
         (function add (E) E :assoc :comm)\n\
         (function g (E) E)\n\
         (function a () E)\n\
         (function b () E)\n\
         (function c () E)\n\
         (function d () E)\n\
         (function n () E)\n\
         (union (add a b) c)\n\
         (union (add a b d) n)\n\
         (let l (g n))\n\
         (let r (g (add c d)))\n\
         (checkau l r :max_size {max_size} :algorithm exact)\n"
    )
}

/// Run the fixture under one AC mode and report whether the `checkau` bound held.
/// Parse and sort errors panic rather than returning `false`, so a typo in the fixture
/// cannot be mistaken for the bound failing.
fn au_within(mode: AcMode, max_size: u32) -> bool {
    let src = program(max_size);
    let surface = semi_persistent_egraph::parser::parse_program_v2(&src)
        .unwrap_or_else(|e| panic!("fixture does not parse: {e}"));
    let mut interp = Interpreter::<
        semi_persistent_egraph::nodes::DefaultConfig,
        BignumLit,
        BignumModel,
        true,
        false,
    >::new(BignumModel);
    interp.set_ac_mode(mode);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        surface,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .unwrap_or_else(|e| panic!("fixture does not sort-check: {e}"));
    interp.run_checked(&checked).is_ok()
}

/// Pin an exact size: the bound holds, and the next bound down does not.
fn assert_exact_size(mode: AcMode, size: u32, label: &str) {
    assert!(
        au_within(mode, size),
        "{label}: anti-unifier exceeds size {size}, expected it to reach exactly {size}"
    );
    assert!(
        !au_within(mode, size - 1),
        "{label}: anti-unifier reached size {} or less, expected exactly {size}",
        size - 1
    );
}

/// Plain congruence closure leaves the §4a equality underived, so the solver reports a
/// `Variants` node at a position where the AC theory has no disagreement.
#[test]
fn plain_mode_over_reports_disagreement() {
    assert_exact_size(AcMode::Off, 5, "plain");
}

/// Eager completion derives the equality before the snapshot is taken, so the two sides
/// are one class and the anti-unifier is the shared term.
#[test]
fn eager_completion_reaches_the_ac_optimum() {
    assert_exact_size(AcMode::Eager, 2, "eager");
}

/// Lazy completion is triggered by equality checks only. `checkau` is not one, so the
/// transaction is closed and the graph restored before the solver snapshots it, and the
/// result is the plain one. See ch. 19 §2.8 for why adapting the goal-directed search to
/// a solver with one OR node per reachable class pair is not a local change.
#[test]
fn lazy_completion_does_not_help_the_solver() {
    assert_exact_size(AcMode::Lazy, 5, "lazy");
}

/// The three modes are not three points on one speed axis: plain and lazy hand the solver
/// the same relation, and only eager changes the answer. Asserting the relationship
/// directly means a regression that shifted every mode by the same amount still fails.
#[test]
fn lazy_agrees_with_plain_and_both_differ_from_eager() {
    assert!(!au_within(AcMode::Off, 4), "plain reached size 4");
    assert!(!au_within(AcMode::Lazy, 4), "lazy reached size 4");
    assert!(au_within(AcMode::Eager, 4), "eager failed to reach size 4");
}
