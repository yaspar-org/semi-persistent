// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Interpreter-level tests for the run-control and statistics surface: `:ruleset`, `(run …
//! :until …)`, and `print-stats`.
//!
//! The `.egg` fixtures in `tests/egg/` can only assert a program's outcome — ok, or a failed
//! check. The facts here are numbers the program itself cannot observe: how many iterations a
//! run took, and what the stats report. They come off the interpreter API and out of the JSON
//! file `(print-stats :file …)` writes.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::saturate::SaturationStrategy;

type Interp = Interpreter<DefaultConfig, BignumLit, BignumModel, true, false>;

/// Run a program to completion and hand back the interpreter for inspection.
fn run(src: &str) -> Interp {
    run_with(src, SaturationStrategy::Naive)
}

fn run_with(src: &str, strategy: SaturationStrategy) -> Interp {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src).expect("parse");
    let mut interp = Interp::new(BignumModel);
    interp.set_strategy(strategy);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
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

// ── `:until` ───────────────────────────────────────────────────────────────

const UNBOUNDED: &str = "
(sort E)
(constructor a () E)
(constructor s (E) E)
(rewrite (s x) (s (s x)))
(let start (s (a)))
";

#[test]
fn until_stops_before_the_budget() {
    // The rule never saturates — it makes a longer term every round — so the budget is the
    // only other way out. The goal holds after one iteration, and the run has to stop there.
    for strategy in [SaturationStrategy::Naive, SaturationStrategy::SemiNaive] {
        let interp = run_with(
            &format!("{UNBOUNDED}(run 100 :until (= start (s (s (a)))))"),
            strategy,
        );
        let sat = interp.last_sat().expect("a run happened");
        assert!(sat.goal_met, "{strategy:?}: goal should be met");
        assert!(
            sat.iterations < 100,
            "{strategy:?}: stopped at the budget ({} iterations)",
            sat.iterations
        );
        assert!(!sat.saturated, "{strategy:?}: this rule cannot saturate");
    }
}

#[test]
fn until_shortens_the_run() {
    // The control for the test above: the same program without a goal runs longer, and
    // reports no goal. Stated as a contrast rather than an iteration count, which would pin
    // how fast this particular rule reaches its fixpoint.
    let with = run(&format!(
        "{UNBOUNDED}(run 100 :until (= start (s (s (a)))))"
    ));
    let without = run(&format!("{UNBOUNDED}(run 100)"));
    let (a, b) = (
        with.last_sat().expect("run").iterations,
        without.last_sat().expect("run").iterations,
    );
    assert!(a < b, "with :until {a} iterations, without {b}");
    assert!(!without.last_sat().expect("run").goal_met);
}

#[test]
fn until_already_satisfied_runs_no_iterations() {
    // The goal is checked *before* the first iteration, so a goal that already holds costs
    // nothing. `(!= …)` on two distinct classes is the cheapest such goal.
    let interp = run("
(sort E)
(constructor a () E)
(constructor b () E)
(let x (a))
(let y (b))
(run 50 :until (!= x y))
");
    let sat = interp.last_sat().expect("a run happened");
    assert_eq!(sat.iterations, 0);
    assert!(sat.goal_met);
}

// ── Rulesets ───────────────────────────────────────────────────────────────

#[test]
fn a_named_run_leaves_the_default_ruleset_alone() {
    // `tests/egg/ruleset_scoping.egg` pins the same scoping through `(check …)`; this asserts
    // it on the class ids, where "did not fire" is directly visible.
    let mut interp = run("
(sort E)
(constructor a () E)
(constructor b () E)
(constructor c () E)
(ruleset extra)
(rewrite (a) (b))
(rewrite (b) (c) :ruleset extra)
(let x (a))
(let y (b))
(run extra 10)
");
    let (x, _) = interp.global("x").expect("x");
    let (y, _) = interp.global("y").expect("y");
    assert_ne!(
        interp.eg.find(x),
        interp.eg.find(y),
        "the untagged rule fired under a named run"
    );
}

#[test]
fn pop_removes_rules_installed_after_push() {
    // Sortcheck resolves the ruleset name across the whole program. At execution time,
    // however, `push` records the installed-rule length and `pop` truncates back to it.
    let mut interp = run("
(sort E)
(constructor a () E)
(constructor b () E)
(ruleset temporary)
(let x (a))
(let y (b))
(push)
(rewrite (a) (b) :ruleset temporary)
(pop)
(run temporary 2)
");
    let (x, _) = interp.global("x").expect("x");
    let (y, _) = interp.global("y").expect("y");
    assert_ne!(
        interp.eg.find(x),
        interp.eg.find(y),
        "a rule installed after push survived pop"
    );
}

#[test]
fn pop_reuses_global_ids_for_later_rules() {
    // The checked GlobalCtx and runtime GlobalCtx must truncate at the same
    // point. Otherwise `live` resolves to gid 2 while runtime reuses gid 1,
    // and matching the rule indexes a nonexistent binding.
    run("
(sort E)
(constructor a () E)
(constructor b () E)
(constructor c () E)
(constructor f (E) E)
(constructor hit () E)
(let base (a))
(push)
(let scoped (b))
(pop)
(let live (c))
(f (c))
(rewrite (f live) (hit))
(run 2)
(check (= (f (c)) (hit)))
");
}

#[test]
fn pop_restores_a_shadowed_global_name() {
    // Truncation must restore the outer name->id mapping, not merely remove
    // the inner mapping. If `chosen` became a fresh pattern variable here,
    // both f-nodes would match and the final disequality would fail.
    run("
(sort E)
(constructor a () E)
(constructor b () E)
(constructor f (E) E)
(constructor hit () E)
(let chosen (a))
(push)
(let chosen (b))
(pop)
(f (a))
(f (b))
(rewrite (f chosen) (hit))
(run 2)
(check (= (f (a)) (hit)))
(check (!= (f (b)) (hit)))
");
}

#[test]
fn check_rebuilds_pending_congruence_after_budgeted_run() {
    // The one permitted round merges a and b in its apply phase, after the
    // round's rebuild. Both f-nodes already exist, so a node-growth-only check
    // would skip the rebuild that makes them congruent.
    run("
(sort E)
(constructor a () E)
(constructor b () E)
(constructor f (E) E)
(constructor seed () E)
(let fa (f (a)))
(let fb (f (b)))
(seed)
(rule ((seed)) ((union (a) (b))))
(run 1)
(check (= fa fb))
");
}

// ── Stats ──────────────────────────────────────────────────────────────────

const STATS_PROGRAM: &str = "
(sort E)
(constructor a () E)
(constructor f (E) E)
(constructor g (E) E)
(rewrite (f x) (g x))
(let x (f (a)))
(run 5)
";

/// Extract a JSON number or boolean by key from the flat object `print-stats` writes.
fn field<'a>(json: &'a str, key: &str) -> &'a str {
    let at = json
        .find(&format!("\"{key}\":"))
        .unwrap_or_else(|| panic!("key {key} missing from {json}"));
    let rest = &json[at + key.len() + 3..];
    let end = rest
        .find([',', '}'])
        .unwrap_or_else(|| panic!("unterminated value for {key} in {json}"));
    &rest[..end]
}

#[test]
fn print_stats_file_reports_the_last_run() {
    let path = std::env::temp_dir().join(format!(
        "semper-print-stats-{}-{:?}.json",
        std::process::id(),
        std::thread::current().id()
    ));
    let src = format!(
        "{STATS_PROGRAM}(print-stats :file \"{}\")",
        path.to_str().unwrap()
    );
    let interp = run(&src);
    let json = std::fs::read_to_string(&path).expect("stats file written");
    let _ = std::fs::remove_file(&path);

    let sat = interp.last_sat().expect("a run happened");
    assert_eq!(field(&json, "nodes"), interp.eg.len().to_string());
    assert_eq!(field(&json, "classes"), interp.eg.class_count().to_string());
    assert_eq!(field(&json, "iterations"), sat.iterations.to_string());
    assert_eq!(field(&json, "saturated"), "true");
    assert_eq!(field(&json, "goal_met"), "false");
    // The counter is armed by the presence of `(print-stats …)`, so a program that asks for
    // stats gets a real number rather than the default-off zero.
    assert!(
        field(&json, "match_steps").parse::<u64>().unwrap() > 0,
        "match steps not counted: {json}"
    );
    assert!(field(&json, "wall_time_ms").parse::<f64>().unwrap() >= 0.0);
}

#[test]
fn stats_classes_are_fewer_than_nodes_after_a_merging_run() {
    // `(f a)` and `(g a)` are two nodes in one class after the rewrite, so the two counts
    // have to differ — the check that `classes` is not just `nodes` under another name.
    let interp = run(STATS_PROGRAM);
    assert!(
        interp.eg.class_count() < interp.eg.len(),
        "classes {} nodes {}",
        interp.eg.class_count(),
        interp.eg.len()
    );
}
