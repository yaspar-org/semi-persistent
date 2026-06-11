// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! End-to-end wiring test: the interpreter can run a program under the
//! semi-naive strategy, and `(check …)` assertions that pass under naive
//! also pass under semi-naive. Exercises `Interpreter::set_strategy` →
//! `(run …)` dispatch → `EGraph::saturate_semi`.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::saturate::SaturationStrategy;

/// Parse, sort-check, and run a program under the given strategy. Returns
/// `Ok(())` iff every `(check …)` in the program passed.
fn run(src: &str, strategy: SaturationStrategy) -> Result<(), String> {
    let cmds =
        semi_persistent_egraph::parser::parse_program_v2(src).map_err(|e| format!("parse: {e}"))?;
    let mut interp =
        Interpreter::<DefaultConfig, BignumLit, BignumModel, true, false>::new(BignumModel);
    interp.set_strategy(strategy);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .map_err(|e| format!("sort: {e}"))?;
    interp
        .run_checked(&checked)
        .map_err(|e| format!("run: {e}"))
}

const PROGRAMS: &[&str] = &[
    // commutativity closes the equality
    "(datatype Math (Num IBig) (Add Math Math))\n\
     (rewrite (Add a b) (Add b a))\n\
     (let e (Add (Num 1) (Num 2)))\n\
     (run 10)\n\
     (check (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))",
    // two-level constant folding (needs multi-round delta propagation)
    "(datatype Math (Num IBig) (Add Math Math) (Mul Math Math))\n\
     (rewrite (Add (Num x) (Num y)) (Num (IBig::+ x y)))\n\
     (rewrite (Mul (Num x) (Num y)) (Num (IBig::* x y)))\n\
     (rewrite (Add a b) (Add b a))\n\
     (rewrite (Mul a b) (Mul b a))\n\
     (let e (Mul (Num 3) (Add (Num 4) (Num 5))))\n\
     (run 10)\n\
     (check (= e (Num 27)))",
];

#[test]
fn semi_naive_runs_programs_like_naive() {
    for (i, src) in PROGRAMS.iter().enumerate() {
        let naive = run(src, SaturationStrategy::Naive);
        let semi = run(src, SaturationStrategy::SemiNaive);
        assert!(naive.is_ok(), "program {i}: naive failed: {naive:?}");
        assert!(
            semi.is_ok(),
            "program {i}: semi-naive failed where naive succeeded: {semi:?}"
        );
    }
}
