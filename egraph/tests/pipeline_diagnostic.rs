// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! One-off diagnostic test: exercises every construct through the full pipeline,
//! printing intermediate forms at each stage.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::sortcheck_program;

fn run(label: &str, src: &str) {
    println!("\n{}", "=".repeat(72));
    println!("  {label}");
    println!("{}", "=".repeat(72));
    println!("{src}");

    // 1. Parse
    let surface_cmds = parse_program_v2(src).unwrap();
    println!("--- PARSED ({} commands) ---", surface_cmds.len());
    for (i, cmd) in surface_cmds.iter().enumerate() {
        println!("  [{i}] {cmd:?}");
    }

    // 2. Sortcheck + resolve
    let mut interp =
        Interpreter::<DefaultConfig, BignumLit, BignumModel, true, false>::new(BignumModel);
    let mut globals = GlobalCtx::new();
    let checked =
        sortcheck_program(surface_cmds, &mut interp.eg, &interp.model, &mut globals).unwrap();
    println!("\n--- CHECKED ({} commands) ---", checked.len());
    for (i, cmd) in checked.iter().enumerate() {
        println!("  [{i}] {cmd:?}");
    }

    // 3. Execute
    println!("\n--- EXECUTING ---");
    match interp.run_checked(&checked) {
        Ok(()) => println!("  e-graph: {} nodes", interp.eg.len()),
        Err(e) => panic!("  EXECUTION FAILED in '{label}': {e}"),
    }
    println!("  OK");
}

#[test]
fn full_pipeline_diagnostic() {
    run(
        "Plain: datatype + constant folding + commutativity",
        r#"
(datatype Math (Num IBig) (Add Math Math) (Mul Math Math))
(rewrite (Add (Num x) (Num y)) (Num (IBig::+ x y)))
(rewrite (Mul (Num x) (Num y)) (Num (IBig::* x y)))
(rewrite (Add a b) (Add b a))
(rewrite (Mul a b) (Mul b a))
(let e (Mul (Num 3) (Add (Num 4) (Num 5))))
(run 10)
(check (= e (Num 27)))
"#,
    );

    run(
        "Commutative: Eq(A,B) = Eq(B,A)",
        r#"
(sort S)
(function Eq (S S) S :comm)
(function A () S)
(function B () S)
(Eq (A) (B))
(check (= (Eq (A) (B)) (Eq (B) (A))))
"#,
    );

    run(
        "Assoc: prefix+suffix rest rewrite",
        r#"
(sort S)
(function F (S) S)
(function A () S)
(function B () S)
(function C () S)
(function Cat (S) S :assoc)
(rewrite (Cat ..pre (A) (B) ..suf) (Cat ..pre (F (A)) ..suf))
(let s (Cat (A) (B) (C)))
(run 10)
(check (= s (Cat (F (A)) (C))))
"#,
    );

    run(
        "AC: sub-multiset match with rest",
        r#"
(sort S)
(function G (S) S)
(function A () S)
(function B () S)
(function Plus (S) S :assoc-comm)
(rewrite (Plus x:1 ..rest) (Plus (G x) ..rest))
(let q (Plus (A) (B)))
(run 1)
"#,
    );

    run(
        "ACI: double negation elimination",
        r#"
(sort S)
(function Neg (S) S)
(function A () S)
(function B () S)
(function Or (S) S :assoc-comm-idem)
(rewrite (Neg (Neg x)) x)
(let p (Or (Neg (Neg (A))) (B)))
(run 10)
(check (= (Neg (Neg (A))) (A)))
"#,
    );

    run(
        "Literals: IBig constant folding",
        r#"
(datatype Math (Num IBig) (Add Math Math))
(rewrite (Add (Num x) (Num y)) (Num (IBig::+ x y)))
(rewrite (Add a b) (Add b a))
(let x (Add (Num 3) (Num 5)))
(run 10)
(check (= x (Num 8)))
"#,
    );

    run(
        "Push/pop: scoped computation",
        r#"
(datatype M (N IBig) (P M M))
(rewrite (P (N x) (N y)) (N (IBig::+ x y)))
(push)
(let a (P (N 1) (N 2)))
(run 10)
(check (= a (N 3)))
(pop)
(let b (P (N 10) (N 20)))
(run 10)
(check (= b (N 30)))
"#,
    );

    run(
        "Rule: transitive closure via datalog insert",
        r#"
(sort N)
(function Edge (N N) N)
(function Path (N N) N)
(function X () N)
(function Y () N)
(function Z () N)
(Edge (X) (Y))
(Edge (Y) (Z))
(rule ((Edge x y) (Edge y z)) ((Path x z)))
(run 10)
(check (Path (X) (Z)))
"#,
    );

    run(
        "Subsume: subsumed node excluded from future matches",
        r#"
(datatype E (T1 IBig IBig) (T2 IBig IBig) (T3 IBig IBig))
(rewrite (T1 x y) (T2 x y) :subsume)
(rewrite (T2 x y) (T3 x y))
(let a (T1 1 2))
(run 10)
(check (= a (T3 1 2)))
"#,
    );

    run(
        "Extract: optimal term extraction",
        r#"
(datatype Expr (EA) (EB) (EF Expr Expr) (EG Expr))
(let x (EF (EG (EA)) (EB)))
(rewrite (EG (EA)) (EB))
(run 10)
(extract x)
(check (= (EG (EA)) (EB)))
"#,
    );

    run(
        "Globals: let-bound names in patterns",
        r#"
(datatype E (V IBig) (Pair E E))
(let a (V 1))
(let b (V 2))
(rewrite (Pair a x) (Pair b x))
(let t (Pair a b))
(run 10)
(check (= t (Pair (V 2) (V 2))))
"#,
    );

    run(
        "AC exact: match entire multiset",
        r#"
(sort S)
(function A () S)
(function B () S)
(function H (S S) S)
(function Plus (S) S :assoc-comm)
(rewrite (Plus x y) (H x y))
(let q (Plus (A) (B)))
(run 1)
(check (= q (H (A) (B))))
"#,
    );

    run(
        "ACI exact: match entire set",
        r#"
(sort S)
(function A () S)
(function B () S)
(function H (S S) S)
(function Or (S) S :assoc-comm-idem)
(rewrite (Or x y) (H x y))
(let q (Or (A) (B)))
(run 1)
(check (= q (H (A) (B))))
"#,
    );

    run(
        "AC rest-only: capture entire multiset",
        r#"
(sort S)
(function A () S)
(function B () S)
(function W (S) S)
(function Plus (S) S :assoc-comm)
(rewrite (Plus ..rest) (W (Plus ..rest)))
(let q (Plus (A) (B)))
(run 1)
"#,
    );

    run(
        "ACI rest-only: capture entire set",
        r#"
(sort S)
(function A () S)
(function B () S)
(function W (S) S)
(function Or (S) S :assoc-comm-idem)
(rewrite (Or ..rest) (W (Or ..rest)))
(let q (Or (A) (B)))
(run 1)
"#,
    );

    run(
        "A exact: match exact sequence",
        r#"
(sort S)
(function A () S)
(function B () S)
(function H (S S) S)
(function Cat (S) S :assoc)
(rewrite (Cat x y) (H x y))
(let q (Cat (A) (B)))
(run 1)
(check (= q (H (A) (B))))
"#,
    );

    run(
        "CheckNeq: terms not equal",
        r#"
(datatype M (N IBig))
(let a (N 1))
(let b (N 2))
(check (!= a b))
"#,
    );

    println!("\n\n=== ALL PIPELINE DIAGNOSTICS PASSED ===\n");
}
