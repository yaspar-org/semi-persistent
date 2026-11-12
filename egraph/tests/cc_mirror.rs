// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The completion mirror on the committed completion corpora.
//!
//! In a debug build every merge of the completion code is checked against the
//! preconditions of the Lean theorem that justifies it (`egraph/src/egraph/cc_mirror.rs`),
//! and a merge that fails its check, or carries no tag, panics. This test runs the
//! completion fixtures (`tests/egg/conform-cc`, `tests/egg/conform-cc-cert`, the `ac_*`,
//! `cc_*` and `*lattice*` files of `tests/egg`) under both evaluation strategies, and
//! asserts that no check fails and that every justification kind was checked at least
//! once.
//!
//! The mirror is compiled in debug builds only, and so is this test.
#![cfg(debug_assertions)]

use semi_persistent_egraph::cc_mirror;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::*;
use semi_persistent_egraph::saturate::SaturationStrategy;

/// The directives of a fixture that change how completion runs.
struct Directives {
    machine: bool,
    union_by: semi_persistent_egraph::UnionBy,
    node_budget: Option<usize>,
}

fn directives(src: &str) -> Directives {
    use semi_persistent_egraph::UnionBy;
    let mut d = Directives {
        machine: false,
        union_by: UnionBy::Rank,
        node_budget: None,
    };
    for line in src.lines().take(8) {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix(";; TYPES:") {
            d.machine = rest.trim() == "machine";
        }
        if let Some(rest) = line.strip_prefix(";; NODE_BUDGET:") {
            d.node_budget = rest.trim().parse().ok();
        }
        if let Some(rest) = line.strip_prefix(";; UNION_BY:") {
            d.union_by = match rest.trim() {
                "size" => UnionBy::Size,
                "uses" => UnionBy::Uses,
                "sum" => UnionBy::Sum,
                _ => UnionBy::Rank,
            };
        }
    }
    d
}

/// Run a program to its end. The outcome is not read: the fixtures' expectations are
/// checked by `egg_tests` and `conform`; here only the mirror's panics matter.
fn run_with<
    L: semi_persistent_egraph::literal::LitVal,
    M: semi_persistent_egraph::lit_model::LitModel<Value = L>,
>(
    src: &str,
    model: M,
    strategy: SaturationStrategy,
    d: &Directives,
) {
    let Ok(surface_cmds) = semi_persistent_egraph::parser::parse_program_v2(src) else {
        return;
    };
    let mut interp =
        Interpreter::<semi_persistent_egraph::nodes::DefaultConfig, L, M, true, false>::new(model);
    interp.set_strategy(strategy);
    interp.set_union_by(d.union_by);
    if let Some(n) = d.node_budget {
        interp.eg.set_completion_node_budget(n);
    }
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let Ok(checked) = semi_persistent_egraph::sortcheck::sortcheck_program(
        surface_cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    ) else {
        return;
    };
    let _ = interp.run_checked(&checked);
}

fn corpus() -> Vec<std::path::PathBuf> {
    let egg = |dir: &str| -> Vec<std::path::PathBuf> {
        std::fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("cannot read {dir}: {e}"))
            .map(|e| e.expect("directory entry").path())
            .filter(|p| p.extension().is_some_and(|x| x == "egg"))
            .collect()
    };
    let mut paths = egg("tests/egg/conform-cc");
    paths.extend(egg("tests/egg/conform-cc-cert"));
    paths.extend(egg("tests/egg").into_iter().filter(|p| {
        let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
        name.starts_with("ac_") || name.starts_with("cc_") || name.contains("lattice")
    }));
    paths.sort();
    paths
}

#[test]
fn completion_merges_meet_their_lean_preconditions_on_the_corpora() {
    let paths = corpus();
    assert!(paths.len() > 400, "the completion corpora are missing");
    let mut failures = Vec::new();
    for path in &paths {
        let src = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        let d = directives(&src);
        for strategy in [SaturationStrategy::Naive, SaturationStrategy::SemiNaive] {
            let run = std::panic::catch_unwind(|| {
                if d.machine {
                    run_with::<MachineLit, MachineModel>(&src, MachineModel, strategy, &d);
                } else {
                    run_with::<BignumLit, BignumModel>(&src, BignumModel, strategy, &d);
                }
            });
            if let Err(panic) = run {
                let msg = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_default();
                failures.push(format!("{} [{strategy:?}]: {msg}", path.display()));
            }
        }
    }
    let counts = cc_mirror::counts();
    println!(
        "completion mirror, {} files, merges checked per kind:",
        paths.len()
    );
    for (kind, n) in &counts {
        println!("  {kind:<20} {n}");
    }
    println!("checked merges that differ from the literal hypotheses:");
    for (note, n) in cc_mirror::notes() {
        println!("  {note:<24} {n}");
    }
    assert!(
        failures.is_empty(),
        "{} runs fail a completion mirror check:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let missing: Vec<&str> = counts
        .iter()
        .filter(|(_, n)| *n == 0)
        .map(|(kind, _)| *kind)
        .collect();
    assert!(
        missing.is_empty(),
        "the corpora exercise no merge of kind {missing:?}"
    );
}
