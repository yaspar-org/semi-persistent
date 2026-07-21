// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! End-to-end AU tests through the production parser, sort checker, rewrite
//! scheduler, and interpreter. Unlike `au_corpus_runner`, these tests register
//! real rewrites and require saturation to improve the asserted AU bound.

use semi_persistent_egraph::containers::DenseId;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::GlobalCtx;

type Interp = Interpreter<DefaultConfig, BignumLit, BignumModel, true, false>;

fn run_program(source: &str) -> Result<Interp, String> {
    let commands = semi_persistent_egraph::parser::parse_program_v2(source)
        .map_err(|error| format!("parse: {error}"))?;
    let mut interpreter = Interp::new(BignumModel);
    let mut globals = GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        commands,
        &mut interpreter.eg,
        &interpreter.model,
        &mut globals,
    )
    .map_err(|error| format!("sort: {error}"))?;
    interpreter
        .run_checked(&checked)
        .map_err(|error| format!("run: {error}"))?;
    Ok(interpreter)
}

#[test]
fn rewrite_saturation_strictly_improves_the_checked_au_bound() {
    let source = r#"
        (sort E)
        (function a () E)
        (function f (E) E)
        (function g (E) E)
        (let left (f (a)))
        (let right (g (a)))

        ; Before saturation only the bare Variants result of size four exists.
        (checkau left right :max_size 4 :algorithm exact)

        ; This rewrite merges the two roots. The post-run size-two bound would
        ; fail if `run` were replaced by repeated no-op rebuilds.
        (rewrite (g x) (f x))
        (run 3)
        (checkau left right :max_size 2 :algorithm exact)
    "#;

    let mut interpreter = run_program(source).unwrap();
    let (left, _) = interpreter.global("left").unwrap();
    let (right, _) = interpreter.global("right").unwrap();
    assert_eq!(
        interpreter.eg.find_const(left),
        interpreter.eg.find_const(right)
    );
    let saturation = interpreter
        .last_sat()
        .expect("the program contains a real run");
    assert!(saturation.iterations > 0);
}

#[test]
fn rewrite_created_cycles_remain_finite_for_exact_au() {
    let source = r#"
        (sort E)
        (function a () E)
        (function b () E)
        (function f (E) E)
        (let left (f (a)))
        (let right (f (b)))

        ; Each rewrite merge leaves an f-node whose child is its own class.
        ; The original leaves remain finite representatives.
        (rewrite (f x) x)
        (run 4)
        (checkau left right :max_size 2 :algorithm exact)
    "#;

    let mut interpreter = run_program(source).unwrap();
    let (left, _) = interpreter.global("left").unwrap();
    let (right, _) = interpreter.global("right").unwrap();
    assert_ne!(
        interpreter.eg.find_const(left),
        interpreter.eg.find_const(right)
    );
    assert!(interpreter.last_sat().is_some());
}

#[test]
fn algebraic_tag_surface_exercises_ac_aci_unit_nilpotent_and_inverse_with_au() {
    let source = r#"
        (sort E)
        (function zero () E)
        (function a () E)
        (function b () E)
        (function c () E)
        (function neg (E) E)
        (function plus (E) E :assoc :comm :identity (zero) :cancellative :inverse neg)
        (function xor (E) E :assoc :comm :nilpotent 2 :identity (zero))
        (function join (E) E :assoc :comm :idempotent :identity (zero))

        (let group_left (plus (a) (neg (b))))
        (let group_right (plus (a) (neg (c))))
        (let xor_left (xor (a) (b)))
        (let xor_right (xor (a) (c)))
        (let join_left (join (a) (b) (c)))
        (let join_right (join (a) (b)))

        (checkau group_left group_right :max_size 6 :algorithm exact)
        (checkau xor_left xor_right :max_size 5 :algorithm exact)
        (checkau join_left join_right :max_size 6 :algorithm exact)
    "#;

    run_program(source).unwrap();
}

#[test]
fn exact_and_uct_algorithms_are_accepted() {
    let source = r#"
        (sort E)
        (function a () E)
        (function b () E)
        (antiunify (a) (b) :algorithm exact :playouts 0)
        (checkau (a) (b) :max_size 2 :algorithm uct :playouts 0)
    "#;
    run_program(source).expect("exact and uct must both be accepted");
}

#[test]
fn syntactic_algorithm_is_rejected_with_supported_values() {
    let source = r#"
        (sort E)
        (function a () E)
        (function b () E)
        (antiunify (a) (b) :algorithm syntactic :playouts 0)
    "#;
    let error = match run_program(source) {
        Ok(_) => panic!("syntactic algorithm should be rejected"),
        Err(error) => error,
    };
    assert_eq!(
        error,
        "run: check failed: unknown AU algorithm 'syntactic' (expected exact or uct)"
    );
}

#[test]
fn unknown_checkau_algorithm_names_only_supported_values() {
    let source = r#"
        (sort E)
        (function a () E)
        (function b () E)
        (checkau (a) (b) :max_size 2 :algorithm exat :playouts 0)
    "#;
    let error = match run_program(source) {
        Ok(_) => panic!("unknown algorithm should be rejected"),
        Err(error) => error,
    };
    assert_eq!(
        error,
        "run: check failed: unknown AU algorithm 'exat' (expected exact or uct)"
    );
}

#[test]
fn overflowing_checkau_max_size_is_rejected_during_parsing() {
    let source = r#"
        (sort E)
        (function a () E)
        (checkau (a) (a) :max_size 4294967296 :algorithm exact)
    "#;
    let error = semi_persistent_egraph::parser::parse_program_v2(source)
        .expect_err("u32 overflow should be a parse error");
    assert!(error.to_string().contains("max_size"));
}

#[test]
fn contradictory_idempotent_cancellative_tag_set_is_rejected() {
    let source = r#"
        (sort E)
        (function e () E)
        (function a () E)
        (function meet (E) E :assoc :comm :idempotent :identity (e) :cancellative)
        (antiunify (a) (e) :algorithm exact)
    "#;

    let commands = semi_persistent_egraph::parser::parse_program_v2(source).unwrap();
    let mut interpreter = Interp::new(BignumModel);
    let mut globals = GlobalCtx::new();
    let error = semi_persistent_egraph::sortcheck::sortcheck_program(
        commands,
        &mut interpreter.eg,
        &interpreter.model,
        &mut globals,
    )
    .expect_err("an idempotent cancellative monoid is trivial and should be rejected");
    assert!(error.to_string().contains("idempotent"));
}

#[test]
fn rewritten_globals_are_real_egraph_classes_not_custom_corpus_terms() {
    let source = r#"
        (sort E)
        (function p () E)
        (function q () E)
        (function wrap (E) E)
        (let double (wrap (wrap (p))))
        (let plain (p))
        (let other (q))
        (rewrite (wrap (wrap x)) x)
        (run 3)
        (checkau double plain :max_size 1 :algorithm exact)
        (checkau double other :max_size 2 :algorithm exact)
    "#;
    let mut interpreter = run_program(source).unwrap();
    let (double, _) = interpreter.global("double").unwrap();
    let (plain, _) = interpreter.global("plain").unwrap();
    assert_eq!(
        interpreter.eg.find_const(double),
        interpreter.eg.find_const(plain)
    );
    // Dense-id access in this end-to-end test also proves the production graph,
    // rather than the corpus runner's private s-expression tree, was exercised.
    assert!(interpreter.eg.find_const(double).to_usize() < interpreter.eg.len());
}
