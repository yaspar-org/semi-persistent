// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance programs for the saturation engine of abstract values.
//!
//! The task is `doc/future/abstract-engine-task.md`. Each `.egg` file in
//! `tests/egg/abs-engine/` states one target behaviour of that document's §10.
//! The programs use syntax that the parser does not accept yet, so the test is
//! ignored until the engine lands. The PR that implements the engine removes the
//! `#[ignore]`.
//!
//! Directives, in a file's first eight lines (the subset of `egg_tests.rs`):
//!   ;; EXPECT: ok|check-failed|parse-error|sort-error|error   outcome (default: ok)
//!   ;; EVAL: naive|semi|both                              eval algorithm (default: both)
//!   ;; MESSAGE: text                                      the outcome's message contains `text`
//!
//! `egg_tests.rs` lists its files one by one and never walks this directory.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::saturate::SaturationStrategy;

const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/egg/abs-engine");

struct Directives {
    expect: String,
    evals: Vec<SaturationStrategy>,
    message: Option<String>,
}

fn parse_directives(src: &str) -> Directives {
    let mut d = Directives {
        expect: "ok".to_string(),
        evals: vec![SaturationStrategy::Naive, SaturationStrategy::SemiNaive],
        message: None,
    };
    for line in src.lines().take(8) {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix(";; EXPECT:") {
            d.expect = rest.trim().to_string();
        }
        if let Some(rest) = line.strip_prefix(";; MESSAGE:") {
            d.message = Some(rest.trim().to_string());
        }
        if let Some(rest) = line.strip_prefix(";; EVAL:") {
            d.evals = match rest.trim() {
                "naive" => vec![SaturationStrategy::Naive],
                "semi" | "semi-naive" => vec![SaturationStrategy::SemiNaive],
                "both" => vec![SaturationStrategy::Naive, SaturationStrategy::SemiNaive],
                other => panic!("unknown EVAL directive: {other} (expected naive|semi|both)"),
            };
        }
    }
    d
}

/// One run of a program: `ok: …`, or the stage that stopped it and its message.
fn run(src: &str, strategy: SaturationStrategy) -> String {
    let surface_cmds = match semi_persistent_egraph::parser::parse_program_v2(src) {
        Ok(c) => c,
        Err(e) => return format!("parse-error: {e}"),
    };
    let mut interp = Interpreter::<
        semi_persistent_egraph::nodes::DefaultConfig,
        BignumLit,
        BignumModel,
        true,
        false,
    >::new(BignumModel);
    interp.set_strategy(strategy);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = match semi_persistent_egraph::sortcheck::sortcheck_program(
        surface_cmds,
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

fn check(path: &std::path::Path) {
    let src = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let d = parse_directives(&src);
    for strategy in d.evals.iter().copied() {
        let output = run(&src, strategy);
        let at = format!("{} [{strategy:?}]", path.display());
        let ok = match d.expect.as_str() {
            "ok" => output.starts_with("ok"),
            "check-failed" => output.contains("check failed"),
            "parse-error" => output.starts_with("parse-error"),
            "sort-error" => output.starts_with("sort-error"),
            "error" => output.starts_with("error"),
            other => panic!("{at}: unknown EXPECT directive: {other}"),
        };
        assert!(ok, "{at}: expected {}, got: {output}", d.expect);
        if let Some(m) = &d.message {
            assert!(
                output.contains(m.as_str()),
                "{at}: expected the message to contain {m:?}, got: {output}"
            );
        }
    }
}

/// Every program in the directory, so a program added there cannot miss its run.
#[test]
#[ignore = "abs-saturation-engine: not implemented yet"]
fn abs_engine_programs() {
    let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(DIR)
        .unwrap_or_else(|e| panic!("cannot read {DIR}: {e}"))
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "egg"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "{DIR} holds no .egg files");
    for path in &files {
        check(path);
    }
}
