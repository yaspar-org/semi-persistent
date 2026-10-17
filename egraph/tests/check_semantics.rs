// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `check` and `prove` (doc/goal-egglog-check.md).
//!
//! `prove` is the build-and-compare check: it builds its terms, rebuilds, and compares
//! classes. `check` is egglog's: a conjunctive query over the current e-graph that
//! succeeds when it has a match, and builds nothing.

use semi_persistent_egraph::interpret::{AcMode, Interpreter};
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::sortcheck_program;

type Interp = Interpreter<DefaultConfig, BignumLit, BignumModel, true, false>;

fn run(src: &str) -> Result<Interp, String> {
    run_in(src, AcMode::Off)
}

fn run_with(src: &str, strategy: semi_persistent_egraph::saturate::SaturationStrategy) -> Interp {
    let surface = parse_program_v2(src).unwrap();
    let mut interp = Interp::new(BignumModel);
    interp.set_strategy(strategy);
    let mut globals = GlobalCtx::new();
    let checked = sortcheck_program(surface, &mut interp.eg, &interp.model, &mut globals).unwrap();
    interp.run_checked(&checked).unwrap();
    interp
}

fn run_in(src: &str, mode: AcMode) -> Result<Interp, String> {
    let surface = parse_program_v2(src).map_err(|e| e.to_string())?;
    let mut interp = Interp::new(BignumModel);
    interp.set_ac_mode(mode);
    let mut globals = GlobalCtx::new();
    let checked = sortcheck_program(surface, &mut interp.eg, &interp.model, &mut globals)
        .map_err(|e| e.to_string())?;
    interp.run_checked(&checked).map_err(|e| e.to_string())?;
    Ok(interp)
}

const DECLS: &str = "
(sort E)
(function f (E) E)
(function a () E)
(function b () E)
(function c () E)
(union (a) (b))
";

#[test]
fn prove_builds_terms_and_closes_under_congruence() {
    // Neither `(f (a))` nor `(f (b))` exists before the command; `prove` builds both, and
    // congruence joins them because `(a)` and `(b)` are one class.
    run(&format!("{DECLS}(prove (= (f (a)) (f (b))))")).expect("equal by congruence");
    run(&format!("{DECLS}(prove (!= (f (a)) (f (c))))")).expect("distinct");
}

#[test]
fn prove_fails_on_the_wrong_relation() {
    let e = run(&format!("{DECLS}(prove (= (f (a)) (f (c))))"))
        .err()
        .expect("not equal");
    assert!(e.contains("terms are not equal"), "{e}");
    let e = run(&format!("{DECLS}(prove (!= (a) (b)))"))
        .err()
        .expect("equal");
    assert!(e.contains("terms are equal"), "{e}");
}

#[test]
fn prove_of_one_term_builds_it() {
    let interp = run(&format!("{DECLS}(prove (f (c)))")).expect("builds");
    assert!(interp.eg.node_count() >= 4, "the term was built");
}

const UNBOUNDED: &str = "
(sort N)
(constructor z () N)
(constructor s (N) N)
(rewrite (s x) (s (s x)))
(let start (s (z)))
";

#[test]
fn until_with_facts_stops_the_run_as_goal_does() {
    // `:goal` builds `(s (s (z)))` and waits for it to join `start`; `:until` waits for a
    // match of the same equality, which needs the term to exist and join. One rewrite
    // round gives both.
    for strategy in [
        semi_persistent_egraph::saturate::SaturationStrategy::Naive,
        semi_persistent_egraph::saturate::SaturationStrategy::SemiNaive,
    ] {
        let until = run_with(
            &format!("{UNBOUNDED}(run 100 :until (= start (s (s (z)))))"),
            strategy,
        );
        let goal = run_with(
            &format!("{UNBOUNDED}(run 100 :goal (= start (s (s (z)))))"),
            strategy,
        );
        let (u, g) = (until.last_sat().unwrap(), goal.last_sat().unwrap());
        assert!(u.goal_met && g.goal_met, "{strategy:?}");
        assert_eq!(u.iterations, g.iterations, "{strategy:?}");
        assert!(u.iterations < 100, "{strategy:?}");
    }
}

#[test]
fn until_with_variables_stops_at_the_first_match() {
    let i = run(&format!(
        "{UNBOUNDED}(run 100 :until (= start (s (s (s (s x))))))"
    ))
    .unwrap();
    let sat = i.last_sat().unwrap();
    assert!(sat.goal_met && sat.iterations < 100, "{sat:?}");
    // A goal that never holds: the run ends at its fixpoint or its budget, and reports
    // the goal unmet.
    let i = run(&format!("{UNBOUNDED}(run 5 :until (= start (z)))")).unwrap();
    let sat = i.last_sat().unwrap();
    assert!(
        !sat.goal_met && (sat.saturated || sat.iterations == 5),
        "{sat:?}"
    );
}

// ── `check`: egglog's query ─────────────────────────────────────────────────

#[test]
fn check_compares_terms_that_exist() {
    run(&format!(
        "{DECLS}(let x (f (a)))\n(let y (f (b)))\n(check (= x y))"
    ))
    .unwrap();
    run(&format!(
        "{DECLS}(let x (f (a)))\n(let y (f (b)))\n(check (= (f (a)) (f (b))))"
    ))
    .unwrap();
    let e = run(&format!(
        "{DECLS}(let x (f (a)))\n(let y (f (c)))\n(check (= x y))"
    ))
    .err()
    .expect("different classes");
    assert!(e.contains("no match for (= x y)"), "{e}");
}

#[test]
fn check_does_not_build_its_terms() {
    // `prove` builds `(f (a))` and `(f (b))` and joins them by congruence; `check` looks
    // them up, finds neither, and fails, as egglog's does.
    run(&format!("{DECLS}(prove (= (f (a)) (f (b))))")).unwrap();
    let e = run(&format!("{DECLS}(check (= (f (a)) (f (b))))"))
        .err()
        .expect("not built");
    assert!(e.contains("no match"), "{e}");
    let e = run(&format!("{DECLS}(check (f (c)))"))
        .err()
        .expect("not built");
    assert!(e.contains("no match for (f (c))"), "{e}");
    let before = run(DECLS).unwrap().eg.node_count();
    let after = run(&format!("{DECLS}(check (a))")).unwrap().eg.node_count();
    assert_eq!(before, after, "a check adds no node");
}

#[test]
fn check_variables_are_existential() {
    let base = format!("{DECLS}(let t (f (a)))\n");
    run(&format!("{base}(check (= e (f x)))")).unwrap();
    run(&format!("{base}(check (= t (f x)))")).unwrap();
    run(&format!("{base}(check (= t (f x)) (= x (b)))")).unwrap();
    let e = run(&format!("{base}(check (= t (f x)) (= x (c)))"))
        .err()
        .expect("no join");
    assert!(e.contains("no match"), "{e}");
    // A variable is scoped to its check: the next check may reuse the name freely.
    run(&format!("{base}(check (= e (f x)))\n(check (= e (a)))")).unwrap();
}

#[test]
fn check_names_follow_rule_bodies() {
    // A bare name of an operator or sort is not a variable: egglog reports the same as
    // shadowing, and here it also catches a nullary term written without parentheses.
    let e = run(&format!("{DECLS}(check (= e (f a)))"))
        .err()
        .expect("operator");
    assert!(e.contains("`a` names an operator"), "{e}");
    let e = run(&format!("{DECLS}(check (= E (f (a))))"))
        .err()
        .expect("sort");
    assert!(e.contains("`E` names a sort"), "{e}");
}

#[test]
fn a_variable_used_once_is_reported() {
    let base = format!("{DECLS}(let t (f (a)))\n");
    let i = run(&format!("{base}(check (f x))")).unwrap();
    assert!(
        i.warnings().iter().any(|w| w.contains("`x` occurs once")),
        "{:?}",
        i.warnings()
    );
    let i = run(&format!("{base}(check (f _x))")).unwrap();
    assert!(i.warnings().is_empty(), "{:?}", i.warnings());
    // The bare side of a top-level `(= e p)` names the class and is not reported.
    let i = run(&format!("{base}(check (= e (f (a))))")).unwrap();
    assert!(i.warnings().is_empty(), "{:?}", i.warnings());
}

const LAZY: &str = "
(sort E)
(function add (E) E :assoc :comm)
(function a () E)
(function b () E)
(function c () E)
(function d () E)
(function n () E)
(union (add a b) c)
(union (add a b d) n)
(let t (add c d))
";

#[test]
fn lazy_ac_completes_where_a_check_needs_it() {
    // `(add c d)` and `n` join only through AC completion: `a + b = c` rewrites
    // `a + b + d`, the class of `n`, to `c + d`. Lazy mode keeps the stored graph
    // uncompleted, so each check below has to run completion to see it.
    run_in(&format!("{LAZY}(prove (= n t))"), AcMode::Lazy).unwrap();
    run_in(&format!("{LAZY}(check (= (n) t))"), AcMode::Lazy).unwrap();
    run_in(&format!("{LAZY}(check (= (n) (add (c) x)))"), AcMode::Lazy).unwrap();
    // Without completion the classes stay apart.
    run_in(&format!("{LAZY}(check (= (n) t))"), AcMode::Off)
        .err()
        .expect("apart without completion");
}

#[test]
fn a_lazy_check_leaves_the_graph_as_it_was() {
    let i = run_in(
        &format!("{LAZY}(check (= (n) t))\n(print-size)"),
        AcMode::Lazy,
    )
    .unwrap();
    let plain = run_in(&format!("{LAZY}(print-size)"), AcMode::Lazy).unwrap();
    assert_eq!(i.eg.node_count(), plain.eg.node_count());
}

// ── `(!= p q)` on e-class sorts ─────────────────────────────────────────────

#[test]
fn neq_compares_classes_in_checks() {
    let base = format!("{DECLS}(let t (f (a)))\n(let u (f (c)))\n");
    run(&format!("{base}(check (!= t u))")).unwrap();
    run(&format!("{base}(check (!= (f (a)) (f (c))))")).unwrap();
    let e = run(&format!("{base}(check (!= (a) (b)))"))
        .err()
        .expect("joined");
    assert!(e.contains("no match"), "{e}");
    // Two variables bound by patterns: some pair of `f` nodes in different classes.
    run(&format!("{base}(check (= x (f p)) (= y (f q)) (!= x y))")).unwrap();
    let e = run(&format!(
        "{DECLS}(let t (f (a)))\n(check (= x (f p)) (= y (f q)) (!= x y))"
    ))
    .err()
    .expect("only one f class");
    assert!(e.contains("no match"), "{e}");
}

#[test]
fn neq_in_a_rule_body_filters_matches() {
    // The rule marks pairs of distinct `f` classes; with `(a)` and `(b)` joined, only
    // the pair over `(a)` and `(c)` qualifies.
    let src = format!(
        "{DECLS}(function g (E E) E)\n(let t (f (a)))\n(let t2 (f (b)))\n(let u (f (c)))\n\
         (rule ((= x (f p)) (= y (f q)) (!= x y)) ((g x y)))\n(run 1)\n\
         (prove (= (g t u) (g t u)))\n(check (g t u))\n(check (g u t))"
    );
    run(&src).unwrap();
    let e = run(&format!(
        "{DECLS}(function g (E E) E)\n(let t (f (a)))\n(let t2 (f (b)))\n\
         (rule ((= x (f p)) (= y (f q)) (!= x y)) ((g x y)))\n(run 1)\n(check (g t t2))"
    ))
    .err()
    .expect("t and t2 are one class");
    assert!(e.contains("no match"), "{e}");
}

#[test]
fn bare_neq_is_class_disequality_beside_literal_guards() {
    // `IBig::!=` compares literal values; the bare `!=` compares classes.
    let src = "
(sort E)
(function n (IBig) E)
(let one (n 1))
(let two (n 2))
(union (n 3) one)
";
    run(&format!("{src}(check (= x (n v)) (= y (n w)) (!= x y))")).unwrap();
    run(&format!(
        "{src}(check (= x (n v)) (= y (n w)) (IBig::!= v w) (!= x y))"
    ))
    .unwrap();
    // `(n 1)` and `(n 3)` hold different values in one class: the guard keeps the pair,
    // the class disequality drops it.
    run(&format!(
        "{src}(check (= one (n v)) (= one (n w)) (IBig::!= v w))"
    ))
    .unwrap();
    let e = run(&format!(
        "{src}(check (= one (n v)) (= one (n w)) (IBig::!= v w) (!= v w))"
    ))
    .err()
    .expect("v and w are literal values here");
    assert!(e.contains("literal value variable"), "{e}");
}

// ── `:count`, `:min`, `:none` ───────────────────────────────────────────────

#[test]
fn counts_are_distinct_assignments_of_named_variables() {
    // `(f (a))` and `(f (b))` are one class (congruence); `(f (c))` another.
    let base = format!("{DECLS}(let t (f (a)))\n(let t2 (f (b)))\n(let u (f (c)))\n");
    run(&format!("{base}(check (= e (f x)) :count 2)")).unwrap();
    // `x` is (a)=(b) or (c): two assignments of `x`, though three `f` nodes.
    run(&format!("{base}(check (f x) :count 2)")).unwrap();
    run(&format!("{base}(check (f x) :min 1)")).unwrap();
    run(&format!("{base}(check (= e (f (c))) (= e (f (a))) :none)")).unwrap();
    let e = run(&format!("{base}(check (= e (f x)) :count 3)"))
        .err()
        .expect("two");
    assert!(e.contains("2 matches for (= e (f x)), expected 3"), "{e}");
    let e = run(&format!("{base}(check (f x) :none)"))
        .err()
        .expect("some");
    assert!(e.contains("expected none"), "{e}");
    let e = run(&format!("{base}(check (f x) :min 3)"))
        .err()
        .expect("two");
    assert!(e.contains("expected at least 3"), "{e}");
}

#[test]
fn lazy_counts_wait_for_the_fixpoint() {
    // Completion joins `n` and `t`: one class, so `:count 1` holds only after it.
    run_in(
        &format!("{LAZY}(check (= y (add (c) (d))) (= y (n)) :count 1)"),
        AcMode::Lazy,
    )
    .unwrap();
    run_in(
        &format!("{LAZY}(check (= y (add (c) (d))) (= y (n)) :none)"),
        AcMode::Off,
    )
    .unwrap();
    run_in(
        &format!("{LAZY}(check (= y (add (c) (d))) (= y (n)) :none)"),
        AcMode::Lazy,
    )
    .err()
    .expect("completion joins them");
}

// ── `query` ─────────────────────────────────────────────────────────────────

fn binary_stdout(name: &str, src: &str, args: &[&str]) -> String {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::write(&path, src).unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_semi-persistent"))
        .arg(&path)
        .args(args)
        .output()
        .expect("run the binary");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn query_prints_matches_in_content_order() {
    let src = format!(
        "{DECLS}(let u (f (c)))\n(let t (f (a)))\n(query (= e (f x)))\n(query (f x) :limit 1)\n\
         (query (= e (f (c))) (= e (f (a))))"
    );
    let out = binary_stdout("query_order.egg", &src, &[]);
    // Two classes of `f` nodes; the order is by content colour, so it is the same for
    // any order of the lets.
    let swapped = src.replace(
        "(let u (f (c)))\n(let t (f (a)))",
        "(let t (f (a)))\n(let u (f (c)))",
    );
    let out2 = binary_stdout("query_order_swapped.egg", &swapped, &[]);
    let lines = |o: &str| -> Vec<String> {
        o.lines()
            .filter(|l| l.starts_with("query") || l.starts_with("  "))
            .map(str::to_owned)
            .collect()
    };
    assert_eq!(lines(&out), lines(&out2), "{out}\n---\n{out2}");
    assert!(out.contains("query (= e (f x)): 2 matches"), "{out}");
    assert!(
        out.contains("query (f x) :limit 1: 2 matches") || out.contains("query (f x): 2 matches"),
        "{out}"
    );
    assert!(out.contains("  ... 1 more"), "{out}");
    assert!(
        out.contains("query (= e (f (c))) (= e (f (a))): 0 matches"),
        "{out}"
    );
    assert!(out.contains("x = (c)") || out.contains("x = (a)"), "{out}");
}

// ── egglog conformance ──────────────────────────────────────────────────────
//
// egglog's tests that check with query variables, ported. egglog's function tables
// become unions with a constant class, and `(fail (check q))` becomes `(check q :none)`.

#[test]
fn egglog_fail_wrong_assertion() {
    // egglog tests/fail_wrong_assertion.egg, second half: `(set (g 1 2) 3)` and
    // `(set (g 2 3) 3)` put both terms in the class of 3.
    let src = "
(sort E)
(function g (IBig IBig) E)
(function three () E)
(union (g 1 2) (three))
(union (g 2 3) (three))
(check (= (g 1 2) (g 2 3)))
(check (!= (g 1 2) (g 2 3)) :none)
(check (= (g 0 2) (g 2 3)) :none)
(check (= x (g 1 2)))
(check (= x (g 1 3)) :none)
(check (= x (g 1 2)) (= y (g 2 3)) (= x y))
(check (= x (g 0 0)) (= y (g 1 1)) (= x y) :none)
";
    run(src).unwrap();
}

#[test]
fn egglog_repro_small_rebuild_fail_term_encoding() {
    // egglog tests/repro-small-rebuild-fail-term-encoding.egg: the variable `l` binds
    // the location under `Prog` in the class the union made.
    let src = "
(sort Loc)
(sort Exp)
(sort Stmt)
(function L (IBig) Loc)
(function Const (IBig) Exp)
(function Prog (Loc) Stmt)
(function Ass (IBig Exp) Stmt)
(union (Prog (L 0)) (Ass 120 (Const 10)))
(check (= (Prog l) (Ass 120 (Const 10))))
(check (= (Prog l) (Ass 121 (Const 10))) :none)
";
    run(src).unwrap();
}

#[test]
fn query_output_is_restored_by_pop() {
    let base = format!("{DECLS}(let t (f (a)))\n(let u (f (c)))\n");
    let out = binary_stdout(
        "query_pop.egg",
        &format!(
            "{base}(query (= e (f x)))\n(push)\n(let v (f (f (c))))\n(query (= e (f x)))\n(pop)\n(query (= e (f x)))"
        ),
        &[],
    );
    let blocks: Vec<&str> = out.split("query (= e (f x)): ").skip(1).collect();
    assert_eq!(blocks.len(), 3, "{out}");
    assert!(blocks[1].starts_with("3 matches"), "{out}");
    let first: Vec<&str> = blocks[0].lines().collect();
    let last: Vec<&str> = blocks[2].lines().take(first.len()).collect();
    assert_eq!(first, last, "{out}");
}

#[test]
fn a_lazy_check_stopped_by_a_budget_is_inconclusive() {
    // A lazy check alternates rule rounds with completion until its condition is decided.
    // `:none` holds before any round, but the rule would add a `g` node, so the answer is
    // only known at the fixpoint. With no rounds allowed, the check reports that it could
    // not decide rather than passing or failing; with the default it fails outright.
    let src = "
(sort E)
(function f (E) E)
(function g (E) E)
(function a () E)
(let t (f (a)))
(rewrite (f x) (g x))
(check (g x) :none)
";
    let decide = |rounds: Option<usize>| -> Result<(), String> {
        let surface = parse_program_v2(src).unwrap();
        let mut interp = Interp::new(BignumModel);
        interp.set_ac_mode(AcMode::Lazy);
        if let Some(r) = rounds {
            interp.set_lazy_ac_rounds(r);
        }
        let mut globals = GlobalCtx::new();
        let checked =
            sortcheck_program(surface, &mut interp.eg, &interp.model, &mut globals).unwrap();
        interp.run_checked(&checked).map_err(|e| e.to_string())
    };
    let e = decide(Some(0)).expect_err("no round to decide in");
    assert!(e.contains("inconclusive"), "{e}");
    let e = decide(None).expect_err("the rule adds a match");
    assert!(
        e.contains("1 match for (g x)") && !e.contains("inconclusive"),
        "{e}"
    );
}
