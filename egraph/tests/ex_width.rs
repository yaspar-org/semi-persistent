// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The Roto surface at the edges of the cost width (`doc/integer-audit.md`, area C,
//! C5 to C13). Each script in `tests/width/` reached a wrapped cost, a wrong
//! `Infeasible`, or a panic that aborted the process across the JIT frame. Each now
//! gives the exact result, or an error naming the operation, at the widths below.

use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node};
use semi_persistent_egraph::extraction::rung::RungKind;
use semi_persistent_egraph::extraction::script::Script;
use semi_persistent_egraph::extraction::solve::{Solver, Status};
use semi_persistent_egraph::extraction::{Cost, CostWidth};
use std::sync::Arc;

fn leaf() -> Arc<Graph> {
    Arc::new(Graph {
        nodes: vec![Node {
            op: "a".into(),
            ints: vec![],
            strings: vec![],
            children: vec![],
            mults: vec![],
            class: 0,
            kind: Kind::Plain,
            subsumed: false,
        }],
        classes: vec![vec![0]],
        root: 0,
    })
}

const SOLVER: Solver = Solver::Internal {
    max_solves: 1000,
    max_conflicts: None,
};

fn run(name: &str, width: CostWidth) -> Result<(Status, Option<Cost>), String> {
    let path = format!("{}/tests/width/{name}.roto", env!("CARGO_MANIFEST_DIR"));
    let s = Script::compile(&path).unwrap_or_else(|e| panic!("{name}: {e}"));
    s.extract(leaf(), RungKind::Selection, &SOLVER, width)
        .map(|o| (o.status, o.cost))
}

fn two63() -> Cost {
    Cost::from(1u64 << 63)
}

#[test]
fn every_script_is_exact_or_a_reported_error() {
    // (script, at 64 bits: Ok(cost) or Err(fragment), unbounded: the exact cost)
    let cases: [(&str, Result<Cost, &str>, Option<Cost>); 9] = [
        ("unary", Err("unary"), None),
        ("times", Err("outside the 64-bit"), Some(two63())),
        (
            "linear",
            Ok(Cost::from(-i64::MAX)),
            Some(Cost::from(-i64::MAX)),
        ),
        ("sum", Err("plus"), Some(two63())),
        ("atmost", Ok(Cost::ONE), Some(Cost::ONE)),
        ("chargeif", Err("outside the 64-bit"), Some(two63())),
        ("scale", Err("scale"), Some(two63())),
        ("cardinality", Ok(Cost::ONE), Some(Cost::ONE)),
        (
            "intscaled",
            Err("int"),
            Some(Cost::from(i64::MAX) * Cost::from(2)),
        ),
    ];
    for (name, at64, unbounded) in cases {
        match (run(name, CostWidth::W64), at64) {
            (Ok((_, c)), Ok(want)) => assert_eq!(c, Some(want), "{name} at 64 bits"),
            (Err(e), Err(frag)) => assert!(e.contains(frag), "{name} at 64 bits: {e}"),
            (got, want) => panic!("{name} at 64 bits: {got:?}, wanted {want:?}"),
        }
        match (run(name, CostWidth::Big), unbounded) {
            (Ok((_, c)), Some(want)) => assert_eq!(c, Some(want), "{name} unbounded"),
            (Err(e), None) => assert!(e.contains("unary"), "{name} unbounded: {e}"),
            (got, want) => panic!("{name} unbounded: {got:?}, wanted {want:?}"),
        }
    }
    // At 32 bits a cost of 2^31 is already outside.
    assert!(
        run("intscaled", CostWidth::W32)
            .unwrap_err()
            .contains("outside the 32-bit")
    );
}
