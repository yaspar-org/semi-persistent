// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The typed surface: every `ok_*.roto` in `tests/surface/` compiles against the
//! binding, and every `bad_*.roto` is rejected at the line its first comment names
//! (`// rejected at line N`). The rejected scripts are the unsound uses the polarity
//! types exist to forbid: requiring an over-estimated condition, subtracting an
//! over-estimate, charging an under-estimate, and gating a part on a non-exact
//! condition.

use semi_persistent_egraph::extraction::CostWidth;
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node};
use semi_persistent_egraph::extraction::rung::RungKind;
use semi_persistent_egraph::extraction::script::Script;
use semi_persistent_egraph::extraction::solve::{Solver, Status};
use std::sync::Arc;

/// `f(g(x), h(x, y))` with a second member in two classes: small enough to solve
/// at every rung, large enough to exercise every call.
fn small() -> Graph {
    let mut g = Graph {
        classes: vec![Vec::new(); 5],
        root: 0,
        ..Default::default()
    };
    let add =
        |g: &mut Graph, op: &str, kids: Vec<usize>, class: usize, kind: Kind, ints: Vec<i64>| {
            g.classes[class].push(g.nodes.len());
            g.nodes.push(Node {
                op: op.into(),
                ints: ints
                    .into_iter()
                    .map(semi_persistent_egraph::extraction::Cost::from)
                    .collect(),
                strings: vec![],
                children: kids,
                mults: Vec::new(),
                class,
                kind,
                subsumed: false,
            });
        };
    add(&mut g, "f", vec![1, 2], 0, Kind::Plain, vec![3]);
    add(&mut g, "Add", vec![1, 2, 3], 0, Kind::MSet, vec![]);
    add(&mut g, "g", vec![3], 1, Kind::Plain, vec![2]);
    add(&mut g, "h", vec![3, 4], 2, Kind::Plain, vec![1]);
    add(&mut g, "k", vec![4], 2, Kind::Plain, vec![5]);
    add(&mut g, "x", vec![], 3, Kind::Plain, vec![]);
    add(&mut g, "y", vec![], 4, Kind::Plain, vec![]);
    g
}

fn strip_ansi(s: &str) -> String {
    let mut out = String::new();
    let mut esc = false;
    for c in s.chars() {
        match (esc, c) {
            (false, '\x1b') => esc = true,
            (true, 'm') => esc = false,
            (true, _) => {}
            (false, c) => out.push(c),
        }
    }
    out
}

#[test]
fn the_surface_accepts_the_sound_scripts_and_rejects_the_unsound_ones_at_their_line() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/surface");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "roto"))
        .collect();
    paths.sort();
    let (mut ok, mut bad) = (0, 0);
    for p in &paths {
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        let result = Script::compile(p.to_str().unwrap());
        if name.starts_with("ok_") {
            let script = match result {
                Ok(s) => s,
                Err(e) => panic!("{name} was rejected:\n{}", strip_ansi(&e)),
            };
            let solver = Solver::Internal {
                max_solves: 1000,
                max_conflicts: None,
            };
            for rung in [RungKind::Selection, RungKind::Splits] {
                let out = script
                    .extract(Arc::new(small()), rung, &solver, CostWidth::default())
                    .unwrap_or_else(|e| panic!("{name} at {rung:?}: {e}"));
                assert_eq!(out.status, Status::Proved, "{name} at {rung:?}");
            }
            ok += 1;
        } else if name.starts_with("bad_") {
            let src = std::fs::read_to_string(p).unwrap();
            let line: usize = src
                .lines()
                .find_map(|l| l.strip_prefix("// rejected at line "))
                .expect("a `// rejected at line N` comment")
                .trim()
                .parse()
                .expect("N in `// rejected at line N` is a line number");
            let err = match result {
                Ok(_) => panic!("{name} compiled"),
                Err(e) => strip_ansi(&e),
            };
            assert!(
                err.contains(&format!("{name}:{line}:")),
                "{name}: expected an error at line {line}:\n{err}"
            );
            bad += 1;
        }
    }
    eprintln!("{ok} scripts compiled, {bad} rejected at their line");
    assert!(ok >= 2 && bad >= 5);
}
