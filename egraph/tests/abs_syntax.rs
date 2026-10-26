// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance tests for the surface syntax of abstract domains (branch `abs-surface-syntax`).
//!
//! Every `.egg` program in `tests/egg/abs/` runs through parse, sortcheck and the
//! interpreter, under naive and semi-naive evaluation. The directives follow
//! `egg_tests.rs` (`;; EXPECT: ok|sort-error|parse-error|error|check-failed`,
//! `;; MESSAGE: text`, `;; WARNING: text|none`, all in the first eight lines), with one
//! difference: a `;; WARNING: text` line asks for exactly one warning containing `text`,
//! because the interim semantics raise the not-active warning once per program.
//!
//! The task is specified in `doc/future/abstract-syntax-task.md`. The test is ignored
//! until that branch implements it; `cargo test --test abs_syntax -- --ignored` runs it.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::saturate::SaturationStrategy;

/// The directory of the acceptance programs, relative to the crate root.
const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/egg/abs");

struct Directives {
    expect: String,
    message: Option<String>,
    /// `Some(vec![])` for `WARNING: none`.
    warnings: Option<Vec<String>>,
}

fn parse_directives(src: &str) -> Directives {
    let mut d = Directives {
        expect: "ok".to_string(),
        message: None,
        warnings: None,
    };
    for line in src.lines().take(8) {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix(";; EXPECT:") {
            d.expect = rest.trim().to_string();
        }
        if let Some(rest) = line.strip_prefix(";; MESSAGE:") {
            d.message = Some(rest.trim().to_string());
        }
        if let Some(rest) = line.strip_prefix(";; WARNING:") {
            let ws = d.warnings.get_or_insert_with(Vec::new);
            if rest.trim() != "none" {
                ws.push(rest.trim().to_string());
            }
        }
    }
    d
}

/// Runs `src` once and returns the outcome line, as `egg_tests.rs` spells it.
fn run(src: &str, strategy: SaturationStrategy, d: &Directives, at: &str) -> String {
    let surface = match semi_persistent_egraph::parser::parse_program_v2(src) {
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
        surface,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    ) {
        Ok(c) => c,
        Err(e) => return format!("sort-error: {e}"),
    };
    match interp.run_checked(&checked) {
        Ok(()) => {
            if let Some(want) = &d.warnings {
                let got = interp.warnings();
                if want.is_empty() {
                    assert!(got.is_empty(), "{at}: WARNING: none, but got {got:?}");
                }
                for w in want {
                    let n = got.iter().filter(|g| g.contains(w.as_str())).count();
                    assert_eq!(n, 1, "{at}: want one warning with {w:?}, got {got:?}");
                }
            }
            format!("ok: {} nodes", interp.eg.len())
        }
        Err(e) => format!("error: {e}"),
    }
}

fn check(path: &std::path::Path) {
    let src = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let d = parse_directives(&src);
    for strategy in [SaturationStrategy::Naive, SaturationStrategy::SemiNaive] {
        let at = format!("{} [{strategy:?}]", path.display());
        let output = run(&src, strategy, &d, &at);
        let prefix = match d.expect.as_str() {
            "ok" => "ok",
            "sort-error" => "sort-error",
            "parse-error" => "parse-error",
            "error" => "error",
            "check-failed" => "error",
            other => panic!("{at}: unknown EXPECT directive: {other}"),
        };
        assert!(
            output.starts_with(prefix),
            "{at}: expected {}, got: {output}",
            d.expect
        );
        if d.expect == "check-failed" {
            assert!(output.contains("check failed"), "{at}: got: {output}");
        }
        if let Some(m) = &d.message {
            assert!(
                output.contains(m.as_str()),
                "{at}: expected the message to contain {m:?}, got: {output}"
            );
        }
    }
}

#[test]
#[ignore = "abs-surface-syntax: not implemented yet"]
fn abs_surface_syntax_acceptance() {
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
