// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! F5-EqSat sweep (goal F5.1): an equality-saturation workload driven round
//! by round with a mark per rewrite round, so sealed frames are per-round
//! scale, under `SEMPER_COMPRESS=auto` + `SEMPER_SHADOW=<file>`. The rewrite
//! system is the classic growth-heavy set (commutativity + associativity +
//! distributivity + constant folding) over generated arithmetic expressions;
//! each instance grows to a node budget, restores mid-run once (the
//! backtracking-EqSat shape, exercising the branch cut), and regrows.
//! Run explicitly:
//!
//!   SEMPER_COMPRESS=auto SEMPER_SHADOW=/tmp/shadow_f5.csv \
//!     cargo test --release --test f5_eqsat_sweep -- --ignored --nocapture

use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::sortcheck_program;

/// Deterministic expression generator (no RNG: seeds vary the shape).
fn gen_expr(depth: usize, seed: u64) -> String {
    if depth == 0 {
        return format!("(Num {})", (seed % 7) + 1);
    }
    let s1 = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let s2 = s1
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let op = if s1.is_multiple_of(3) { "Mul" } else { "Add" };
    format!(
        "({op} {} {})",
        gen_expr(depth - 1, s1),
        gen_expr(depth - 1, s2)
    )
}

#[test]
#[ignore = "measurement sweep; run with --ignored --nocapture and SEMPER_SHADOW set"]
fn eqsat_sweep_marks_per_round() {
    const INSTANCES: u64 = 200;
    const MAX_ROUNDS: usize = 24;
    const NODE_BUDGET: usize = 40_000;

    let mut total_frames = 0usize;
    for inst in 0..INSTANCES {
        let expr = gen_expr(4, inst.wrapping_mul(0x9e3779b97f4a7c15) + 1);
        let setup = format!(
            r#"
(datatype Math (Num IBig) (Add Math Math) (Mul Math Math))
(rewrite (Add (Num x) (Num y)) (Num (IBig::+ x y)))
(rewrite (Mul (Num x) (Num y)) (Num (IBig::* x y)))
(rewrite (Add a b) (Add b a))
(rewrite (Mul a b) (Mul b a))
(rewrite (Add (Add a b) c) (Add a (Add b c)))
(rewrite (Mul (Mul a b) c) (Mul a (Mul b c)))
(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))
(let e {expr})
"#
        );
        let mut interp =
            Interpreter::<DefaultConfig, BignumLit, BignumModel, true, false>::new(BignumModel);
        let mut globals = GlobalCtx::new();
        let checked = sortcheck_program(
            parse_program_v2(&setup).unwrap(),
            &mut interp.eg,
            &interp.model,
            &mut globals,
        )
        .unwrap();
        interp.run_checked(&checked).expect("setup");
        let step = sortcheck_program(
            parse_program_v2("(run 1)").unwrap(),
            &mut interp.eg,
            &interp.model,
            &mut globals,
        )
        .unwrap();

        // Grow with a mark per rewrite round; keep a mid-run token and
        // restore once (the backtracking shape), then regrow.
        let mut mid = None;
        for round in 0..MAX_ROUNDS {
            let tok = interp.eg.mark(ShrinkPolicy::Never);
            total_frames += 1;
            if round == MAX_ROUNDS / 3 {
                mid = Some(tok);
            }
            interp.run_checked(&step).expect("round");
            if interp.eg.len() > NODE_BUDGET {
                break;
            }
        }
        if let Some(tok) = mid.take() {
            interp.eg.restore(tok);
            // Regrow a few rounds on the new branch.
            for _ in 0..4 {
                let _ = interp.eg.mark(ShrinkPolicy::Never);
                total_frames += 1;
                interp.run_checked(&step).expect("regrow round");
                if interp.eg.len() > NODE_BUDGET {
                    break;
                }
            }
        }
        if inst % 10 == 0 {
            println!(
                "instance {inst}: {} nodes, {total_frames} marks so far",
                interp.eg.len()
            );
        }
    }
    println!("total marks (frames per column): {total_frames}");
    assert!(
        total_frames >= 1000,
        "the sweep must log at least 1000 frames per hot column, got {total_frames}"
    );
}
