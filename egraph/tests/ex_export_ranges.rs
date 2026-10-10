// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Export soundness (`doc/goal-arbitrary-precision-costs.md`, step 4): every number
//! written for a solver is checked against that solver's measured range
//! (`tests/data/solver_width/README.md`) before the solver runs. One must-fail case per
//! row of the goal's table, each refused without the solver installed, and must-pass
//! cases showing that our CNF path and RoundingSat take the same numbers exactly.

use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node};
use semi_persistent_egraph::extraction::oint::Build;
use semi_persistent_egraph::extraction::rung::Selection;
use semi_persistent_egraph::extraction::solve::{
    OpbCommand, Outcome, Prepared, Solver, Status, solve_prepared,
};
use semi_persistent_egraph::extraction::target::Cmp;
use semi_persistent_egraph::extraction::{Cost, CostWidth};
use std::sync::Arc;

fn pow2(k: u32) -> Cost {
    (0..k).fold(Cost::ONE, |a, _| a * Cost::from(2))
}

fn node(op: &str, ints: Vec<Cost>, class: usize) -> Node {
    Node {
        op: op.into(),
        ints,
        strings: vec![],
        children: vec![],
        mults: vec![],
        class,
        kind: Kind::Plain,
        subsumed: false,
    }
}

/// One class with two leaves, `a` and `b`.
fn two_leaves() -> Arc<Graph> {
    Arc::new(Graph {
        nodes: vec![node("a", vec![], 0), node("b", vec![], 0)],
        classes: vec![vec![0, 1]],
        root: 0,
    })
}

fn extract(
    g: &Arc<Graph>,
    cost: &dyn Fn(&Selection, &mut Build),
    solver: &Solver,
) -> Result<Outcome, String> {
    let mut prepared = Prepared::for_solver(solver);
    let (sel, rec) = {
        let mut b = Build::with_width(prepared.target(), CostWidth::Big);
        let sel = Selection::build(g.clone(), &mut b);
        cost(&sel, &mut b);
        (sel, b.detach())
    };
    solve_prepared(g, &sel, &rec, prepared, solver)
}

/// The three kinds of number a pseudo-Boolean back end reads, each at `v`: `a` costs 1 and
/// `b` costs 2, and the extra number forces `a` or leaves the optimum at `a` either way.
fn coefficient(v: Cost) -> impl Fn(&Selection, &mut Build) {
    move |r, b| {
        b.cost_if(r.node(0), 1u64);
        b.cost_if(r.node(1), 2u64);
        // v·[a] >= v forces a.
        b.pb(&[(v, r.node(0))], Cmp::Ge, v);
    }
}
fn bound(v: Cost) -> impl Fn(&Selection, &mut Build) {
    move |r, b| {
        b.cost_if(r.node(0), 1u64);
        b.cost_if(r.node(1), 2u64);
        // [a] + [b] <= v holds always.
        b.pb(
            &[(Cost::ONE, r.node(0)), (Cost::ONE, r.node(1))],
            Cmp::Le,
            v,
        );
    }
}
fn weight(v: Cost) -> impl Fn(&Selection, &mut Build) {
    move |r, b| {
        b.cost_if(r.node(0), 1u64);
        b.cost_if(r.node(1), v);
    }
}

fn must_fail(solver: &Solver, v: Cost, fragment: &str) {
    let g = two_leaves();
    for (what, cost) in [
        (
            "coefficient",
            Box::new(coefficient(v)) as Box<dyn Fn(&Selection, &mut Build)>,
        ),
        ("bound", Box::new(bound(v))),
        ("weight", Box::new(weight(v))),
    ] {
        let err = extract(&g, &*cost, solver)
            .err()
            .unwrap_or_else(|| panic!("{solver:?}: a {what} of {v} was accepted"));
        assert!(err.contains(fragment), "{solver:?} {what} {v}: {err}");
    }
}

fn must_pass(solver: &Solver, v: Cost) {
    let g = two_leaves();
    for cost in [
        Box::new(coefficient(v)) as Box<dyn Fn(&Selection, &mut Build)>,
        Box::new(bound(v)),
        Box::new(weight(v)),
    ] {
        let out = extract(&g, &*cost, solver).unwrap();
        assert_eq!(
            (out.status, out.cost),
            (Status::Proved, Some(Cost::ONE)),
            "{solver:?} {v}"
        );
    }
}

#[test]
fn opb_clasp_refuses_past_32_bits() {
    must_fail(
        &Solver::Opb(OpbCommand::new("clasp")),
        Cost::from(1i64 << 31),
        "clasp's 32-bit",
    );
}

#[test]
fn opb_other_solvers_refuse_past_64_bits() {
    must_fail(
        &Solver::Opb(OpbCommand::new("some-pb-solver")),
        pow2(63),
        "some-pb-solver's 64-bit",
    );
}

#[test]
fn asp_target_refuses_past_32_bits() {
    must_fail(
        &Solver::Asp(OpbCommand::new("clingo")),
        Cost::from(1i64 << 31),
        "clingo's 32-bit",
    );
}

#[test]
fn dpw_refuses_an_objective_past_64_bits() {
    let g = two_leaves();
    let err = extract(
        &g,
        &weight(pow2(64)),
        &Solver::Dpw {
            max_solves: 100,
            max_conflicts: None,
        },
    )
    .unwrap_err();
    assert!(err.starts_with("dpw:"), "{err}");
}

/// Must pass: the internal CNF path holds every one of these numbers exactly, at 2^70.
#[test]
fn the_internal_solver_takes_every_number_exactly() {
    must_pass(
        &Solver::Internal {
            max_solves: 100,
            max_conflicts: None,
        },
        pow2(70),
    );
}

/// Must pass: RoundingSat reads arbitrary precision (measured at 2^70 and 2^100).
#[test]
fn roundingsat_takes_every_number_exactly() {
    match OpbCommand::roundingsat() {
        Some(cmd) => must_pass(&Solver::Opb(cmd), pow2(100)),
        None => eprintln!("roundingsat not installed: this test did not run"),
    }
}

/// A graph whose one node carries `int` as payload and, under `Add`, `mult` as a count.
fn payload(int: Cost, mult: u64) -> (Graph, Graph) {
    let p = Graph {
        nodes: vec![node("Global", vec![Cost::ZERO, int], 0)],
        classes: vec![vec![0]],
        root: 0,
    };
    let mut m = Graph {
        nodes: vec![node("x", vec![], 0)],
        classes: vec![vec![0], vec![1]],
        root: 1,
    };
    let mut add = node("Add", vec![], 1);
    add.kind = Kind::MSet;
    add.children = vec![0];
    add.mults = vec![mult];
    m.nodes.push(add);
    (p, m)
}

/// ASP criteria and MiniZinc criteria: the dump's integers and multiplicities, per
/// solver, each refusal saying that the criteria's own arithmetic is the user's.
#[test]
fn criteria_dumps_refuse_numbers_past_the_solvers_range() {
    let own = "is yours to rule out";
    // clingo, 32-bit.
    for g in [
        payload(Cost::from(1i64 << 31), 1).0,
        payload(Cost::ONE, 1 << 31).1,
    ] {
        let err = semi_persistent_egraph::extraction::lp::fits_clingo(&g).unwrap_err();
        assert!(
            err.contains("clingo's 32-bit") && err.contains(own),
            "{err}"
        );
    }
    let mzn = |s: &str| OpbCommand::new("minizinc").arg("--solver").arg(s);
    let cases: [(&str, Cost, u64, &str); 8] = [
        ("chuffed", Cost::from(1i64 << 31), 1u64 << 31, "32-bit"),
        ("gecode", Cost::from(1i64 << 31), 1u64 << 31, "32-bit"),
        (
            "coinbc",
            Cost::from((1i64 << 53) + 1),
            (1u64 << 53) + 1,
            "double-precision",
        ),
        (
            "highs",
            Cost::from((1i64 << 53) + 1),
            (1u64 << 53) + 1,
            "double-precision",
        ),
        (
            "scip",
            Cost::from((1i64 << 53) + 1),
            (1u64 << 53) + 1,
            "double-precision",
        ),
        (
            "gurobi",
            Cost::from((1i64 << 53) + 1),
            (1u64 << 53) + 1,
            "double-precision",
        ),
        ("cp-sat", pow2(63), 1u64 << 63, "64-bit"),
        ("some-cp-solver", pow2(63), 1u64 << 63, "64-bit"),
    ];
    for (solver, int, mult, range) in cases {
        let (p, m) = payload(int, mult);
        for g in [p, m] {
            let err = semi_persistent_egraph::extraction::mzn::fits_minizinc(&g, &mzn(solver))
                .unwrap_err();
            assert!(
                err.contains(&format!("{solver}'s {range}")) && err.contains(own),
                "{solver}: {err}"
            );
        }
        // One below the limit is accepted.
        let below = payload(int - Cost::ONE, mult - 1);
        assert!(
            semi_persistent_egraph::extraction::mzn::fits_minizinc(&below.0, &mzn(solver)).is_ok(),
            "{solver}"
        );
        assert!(
            semi_persistent_egraph::extraction::mzn::fits_minizinc(&below.1, &mzn(solver)).is_ok(),
            "{solver}"
        );
    }
}
