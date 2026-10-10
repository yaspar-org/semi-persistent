// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `IBig` and `UBig` in the Roto binding (`doc/goal-arbitrary-precision-costs.md`,
//! step 3). Each script in `tests/big/` computes with exact integers past 64 bits; the
//! expected cost is computed here in `semi_persistent_egraph::extraction::Cost`. The solvers that hold such
//! numbers (`internal`, `roundingsat`) prove the exact optimum. Every other solver is
//! refused before it runs, with an error naming it (must-fail, no solver installed).

use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node};
use semi_persistent_egraph::extraction::rung::RungKind;
use semi_persistent_egraph::extraction::script::Script;
use semi_persistent_egraph::extraction::solve::{OpbCommand, Outcome, Solver, Status};
use semi_persistent_egraph::extraction::{Cost, CostWidth};
use std::sync::Arc;

fn node(
    op: &str,
    ints: Vec<Cost>,
    children: Vec<usize>,
    mults: Vec<u64>,
    class: usize,
    kind: Kind,
) -> Node {
    Node {
        op: op.into(),
        ints,
        strings: vec![],
        children,
        mults,
        class,
        kind,
        subsumed: false,
    }
}

fn script(name: &str) -> Script {
    let path = format!("{}/tests/big/{name}.roto", env!("CARGO_MANIFEST_DIR"));
    Script::compile(&path).unwrap_or_else(|e| panic!("{name}: {e}"))
}

fn run(name: &str, g: &Arc<Graph>, solver: &Solver) -> Result<Outcome, String> {
    script(name).extract(g.clone(), RungKind::Selection, solver, CostWidth::Big)
}

const INTERNAL: Solver = Solver::Internal {
    max_solves: 1000,
    max_conflicts: None,
};

fn pow2(k: u32) -> Cost {
    (0..k).fold(Cost::ONE, |a, _| a * Cost::from(2))
}

fn leaf() -> Arc<Graph> {
    Arc::new(Graph {
        nodes: vec![node("a", vec![], vec![], vec![], 0, Kind::Plain)],
        classes: vec![vec![0]],
        root: 0,
    })
}

/// Two roots past 2^64: `Add` over `x` with multiplicity 2^64 - 1 costs
/// 1 + 4·(2^64 - 1), and `Big(x)` with payload 2^70 costs 1 + 4 + 2^70. With `x` at 1 the
/// optimum is `Add`, at 4·2^64 - 2.
fn two_big_roots() -> Arc<Graph> {
    Arc::new(Graph {
        nodes: vec![
            node("Add", vec![], vec![1], vec![u64::MAX], 0, Kind::MSet),
            node("Big", vec![pow2(70)], vec![1], vec![], 0, Kind::Plain),
            node("x", vec![], vec![], vec![], 1, Kind::Plain),
        ],
        classes: vec![vec![0, 1], vec![2]],
        root: 0,
    })
}

#[test]
fn a_script_totalizing_multiplicities_past_u64_is_proved_exactly() {
    let g = two_big_roots();
    let want = Cost::from(4) * pow2(64) - Cost::from(2);
    let out = run("totalize", &g, &INTERNAL).unwrap();
    assert_eq!((out.status, out.cost), (Status::Proved, Some(want)));
    assert_eq!(out.term.unwrap().selection, vec![Some(0), Some(2)]);
    match OpbCommand::roundingsat() {
        Some(cmd) => {
            let out = run("totalize", &g, &Solver::Opb(cmd)).unwrap();
            assert_eq!(
                (out.status, out.cost),
                (Status::Proved, Some(want)),
                "roundingsat"
            );
        }
        None => eprintln!("roundingsat not installed: its half of this test did not run"),
    }
}

/// Must fail: the same script on every solver that cannot hold its numbers, refused
/// before the solver runs.
#[test]
fn the_same_script_is_refused_by_every_narrower_solver() {
    let g = two_big_roots();
    let dpw = Solver::Dpw {
        max_solves: 1000,
        max_conflicts: None,
    };
    let err = run("totalize", &g, &dpw).unwrap_err();
    assert!(err.starts_with("dpw:"), "{err}");
    let clasp = Solver::Opb(OpbCommand::new("clasp"));
    let err = run("totalize", &g, &clasp).unwrap_err();
    assert!(err.contains("clasp's 32-bit"), "{err}");
    let other = Solver::Opb(OpbCommand::new("some-pb-solver"));
    let err = run("totalize", &g, &other).unwrap_err();
    assert!(err.contains("some-pb-solver's 64-bit"), "{err}");
    let asp = Solver::Asp(OpbCommand::new("clingo"));
    let err = run("totalize", &g, &asp).unwrap_err();
    assert!(err.contains("clingo's 32-bit"), "{err}");
}

#[test]
fn every_big_method_computes_exactly() {
    let (a, b) = (pow2(70), Cost::from(-3));
    let c = -((a + b) * Cost::from(2) - Cost::ONE);
    let d = c
        .checked_div(Cost::from(7))
        .unwrap()
        .checked_rem(Cost::from(1_000_000_007))
        .unwrap();
    let e = ((c.abs() + Cost::from(5) - Cost::from(2)) * Cost::from(3))
        .checked_div(Cost::from(2))
        .unwrap()
        .checked_rem(Cost::parse("100000000000000000000").unwrap())
        .unwrap()
        .max(Cost::ONE)
        .min(Cost::parse("99999999999999999999999").unwrap());
    let s = Cost::from(1 + 10 + 5)
        + if e.to_u64().is_some() {
            Cost::from(1000)
        } else {
            Cost::ZERO
        };
    let want = d + e + s + c.max(b) + c.min(b) + b.abs();
    let out = run("methods", &leaf(), &INTERNAL).unwrap();
    assert_eq!((out.status, out.cost), (Status::Proved, Some(want)));
}

#[test]
fn every_big_variant_of_a_constant_taking_call_is_exact() {
    let want = (pow2(66) + Cost::from(2))
        + pow2(65)
        + (pow2(65) + Cost::from(3))
        + Cost::from(5 + 17 + 7 + 11 + 13)
        + (pow2(64) + Cost::ONE);
    let out = run("variants", &leaf(), &INTERNAL).unwrap();
    assert_eq!((out.status, out.cost), (Status::Proved, Some(want)));
}

/// Division by zero aborted the process from Roto's own `/`; through `IBig` it is a build
/// error. A negative `UBig` and a malformed decimal string are build errors too.
#[test]
fn big_arithmetic_faults_are_build_errors() {
    for (name, fragment) in [
        ("div0", "div: division by zero"),
        ("negative_ubig", "minus: the result -1 is negative"),
        ("bad_str", "ibig_str: '12x' is not a decimal integer"),
    ] {
        let err = run(name, &leaf(), &INTERNAL).unwrap_err();
        assert!(err.contains(fragment), "{name}: {err}");
    }
}
