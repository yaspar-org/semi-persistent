// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance fixtures against the Lean e-matching model.
//!
//! Every `.egg` file under `tests/egg/conform/` was written by `semper-conform`
//! (`proofs/lean/Conform`), which builds a small e-graph, matches one pattern with
//! the model's reference interpreter and checks the matches it found (`check-eq`)
//! and a sample of the candidates it rejected (`check-neq`). The directory is
//! scanned: a file needs no registration. `tests/egg/conform/README.md` names the
//! seed and the regeneration command; the Lean workflow regenerates the sample
//! and fails when a committed file differs.
//!
//! The runner is the one of `egg_tests.rs`, reduced to the directives these files
//! use (`;; EXPECT: ok`, `;; TYPES: machine`): every file runs under both
//! evaluation strategies and both atom-scheduling modes.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::*;
use semi_persistent_egraph::saturate::SaturationStrategy;

const DIR: &str = "tests/egg/conform";

fn run_source(src: &str, strategy: SaturationStrategy) -> String {
    let surface_cmds = match semi_persistent_egraph::parser::parse_program_v2(src) {
        Ok(c) => c,
        Err(e) => return format!("parse-error: {e}"),
    };
    let mut interp = Interpreter::<
        semi_persistent_egraph::nodes::DefaultConfig,
        MachineLit,
        MachineModel,
        true,
        false,
    >::new(MachineModel);
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

/// The two directives a conformance file carries, read from its first eight lines.
fn directives(src: &str) -> (String, String) {
    let mut expect = "ok".to_string();
    let mut types = "bignum".to_string();
    for line in src.lines().take(8) {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix(";; EXPECT:") {
            expect = rest.trim().to_string();
        }
        if let Some(rest) = line.strip_prefix(";; TYPES:") {
            types = rest.trim().to_string();
        }
    }
    (expect, types)
}

#[test]
fn conform_fixtures_agree_with_the_model() {
    let mut paths: Vec<_> = std::fs::read_dir(DIR)
        .unwrap_or_else(|e| panic!("cannot read {DIR}: {e}"))
        .map(|e| e.expect("directory entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "egg"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "{DIR} holds no .egg file");
    let mut failures = Vec::new();
    for path in &paths {
        let src = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        let (expect, types) = directives(&src);
        assert_eq!(
            expect,
            "ok",
            "{}: a conformance file expects ok",
            path.display()
        );
        assert_eq!(
            types,
            "machine",
            "{}: a conformance file runs machine types",
            path.display()
        );
        for runtime in [false, true] {
            semi_persistent_egraph::ematch::set_runtime_scheduling(runtime);
            for strategy in [SaturationStrategy::Naive, SaturationStrategy::SemiNaive] {
                let out = run_source(&src, strategy);
                if !out.starts_with("ok") {
                    failures.push(format!(
                        "{} [{strategy:?}, runtime_scheduling={runtime}]: {out}",
                        path.display()
                    ));
                }
            }
        }
    }
    semi_persistent_egraph::ematch::set_runtime_scheduling(false);
    assert!(
        failures.is_empty(),
        "{} of {} conformance files disagree with the model:\n{}",
        failures.len(),
        paths.len(),
        failures.join("\n")
    );
}
