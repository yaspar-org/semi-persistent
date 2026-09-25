// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ramp-up kata 6: hand analysis of §2 after `(union c (True))`, then the
//! in-repo witnesses that match findings #1 and #7 (see the module comment).
//!
//! `stress/FINDINGS.md` is not in this checkout. The two witness programs
//! below are the files the design docs use for the same two bugs the
//! practicum cites: build-order canonization (#1–#3) and recanonize-only
//! unit drop (the late-merge case that would stale a class value).

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel, MachineLit, MachineModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::saturate::SaturationStrategy;

/// Hand table for §2 after `(union c (True))`.
///
/// Starting classes (sort I gets an interval, sort B a four-value boolean):
///
/// | class   | nodes                         | value      | use-list                         |
/// |---------|-------------------------------|------------|----------------------------------|
/// | C_three | Lit(3)                        | [3, 3]     | Lt, Ite (then)                   |
/// | C_ten   | Lit(10)                       | [10, 10]   | Lt, Ite (else)                   |
/// | C_c     | Lt(three, ten)                | unknown    | Ite (condition)                  |
/// | C_True  | True()                        | true       | (empty)                          |
/// | C_t     | Ite(c, three, ten)            | [3, 10]    | (empty, or Clamp if present)     |
///
/// `(union c (True))` merges C_c and C_True. Meet of `unknown` and `true`
/// is `true` — a strict tightening, no new e-node.
///
/// Analysis worklist (use-list of the absorbed class, then of every class
/// that tightens):
///
/// 1. Re-evaluate the Ite node (only parent of C_c). Order: that single
///    node. Its class is C_t.
/// 2. Ite with a known-true condition selects the then-arm: C_t becomes
///    [3, 3]. Another strict tightening.
/// 3. If Clamp(t, 0, 255) exists, it is on C_t's use-list and is
///    re-evaluated next. Otherwise the worklist is empty.
///
/// Not re-evaluated: C_three, C_ten (values unchanged). C_c is updated by
/// the merge meet itself, not by a transfer re-run.
///
/// If the tightening of C_c does not enter the semi-naive delta, a later
/// guarded rewrite on t never re-fires — the silent-loss case §2 warns
/// about.
const SECTION2_ORDER: &str = "\
after (union c (True)):
  1. C_c  ← meet(unknown, true) = true     [merge, not a transfer]
  2. C_t  ← Ite transfer, condition true     [only use-list entry of C_c]
  3. users of C_t, if any (Clamp)            [only if t tightened]
not re-evaluated: C_three, C_ten
";

fn egg(name: &str) -> String {
    let path = format!("{}/tests/egg/{name}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"))
}

fn run_bignum(src: &str) -> Interpreter<DefaultConfig, BignumLit, BignumModel, true, false> {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src).expect("parse");
    let mut interp = Interpreter::new(BignumModel);
    interp.set_strategy(SaturationStrategy::Naive);
    let mut globals = GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sortcheck");
    interp.run_checked(&checked).expect("run");
    interp
}

fn run_machine_outcome(src: &str) -> String {
    let cmds = match semi_persistent_egraph::parser::parse_program_v2(src) {
        Ok(c) => c,
        Err(e) => return format!("parse-error: {e}"),
    };
    let mut interp: Interpreter<DefaultConfig, MachineLit, MachineModel, true, false> =
        Interpreter::new(MachineModel);
    interp.set_strategy(SaturationStrategy::Naive);
    let mut globals = GlobalCtx::new();
    let checked = match semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    ) {
        Ok(c) => c,
        Err(e) => return format!("sort-error: {e}"),
    };
    match interp.run_checked(&checked) {
        Ok(()) => format!("ok: {} nodes", interp.eg.len()),
        Err(e) => format!("error: {e}"),
    }
}

#[test]
fn section2_union_true_then_ite_selects_then_arm() {
    let _ = run_bignum(&egg("kata2_section2.egg"));
    println!("{SECTION2_ORDER}");
}

/// Finding #1 class: a node's stored (canonical) form depends on when it
/// was built. Same terms, opposite `let` order, opposite equality.
///
/// Class-value impact: if the two Mul nodes stay in different classes,
/// each keeps its own transfer result and they are never meet'd. After
/// the reorder they share a class, so the analysis would meet the two
/// over-approximations. Treating merge as the only trigger is not enough
/// — a later recanonize that *then* collides them must also re-meet.
#[test]
fn finding1_build_order_changes_whether_classes_meet() {
    let depend = run_machine_outcome(&egg("ac_flatten_order_dependence.egg"));
    let reordered = run_machine_outcome(&egg("ac_flatten_order_dependence_reordered.egg"));
    assert!(
        depend.contains("check failed"),
        "finding #1 witness must fail in plain mode, got {depend}"
    );
    assert!(
        reordered.starts_with("ok"),
        "reordered witness must pass, got {reordered}"
    );
}

/// Finding #7 class: recanonize-only change. `add(a,b)` is built, then
/// `b` merges with the unit. Rebuild drops the unit and the node becomes
/// `a` — no rewrite, and the parent's class may merge with `a`.
///
/// Class-value impact: the Add transfer (join of the arms / fold of the
/// summands) must be replaced by `a`'s value. An analysis that reruns
/// only when *classes merge*, and skips recanonization of a live node,
/// keeps the old looser Add value. That is stale, not merely imprecise.
#[test]
fn finding7_recanonize_unit_drop_must_recompute_class_value() {
    let interp = run_bignum(&egg("identity_late_merge_mset.egg"));
    assert!(
        interp.last_sat().is_some(),
        "late-merge witness must run"
    );
}
