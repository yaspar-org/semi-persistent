// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Every cost in `tests/mltl/costs/*.mzn` equals its Rust twin in `extraction::mltl_cost`.
//!
//! On random e-graphs over each cost's operators, at every rung, the MiniZinc
//! criteria appended to `mzn::dump` and solved by CP-SAT and by Chuffed, and the Rust
//! cost solved by the internal descent, report the same status and the same optimum;
//! the MiniZinc cost is the objective on the extracted term (a second solve with the
//! term fixed), and the Rust cost of that term is the same.

use semi_persistent_egraph::extraction::graph::{Assoc, Graph, Kind, Node};
use semi_persistent_egraph::extraction::oint::Build;
use semi_persistent_egraph::extraction::rung::{Rung, RungKind};
use semi_persistent_egraph::extraction::script::CostModel;
use semi_persistent_egraph::extraction::solve::{OpbCommand, Solver, Status};
use semi_persistent_egraph::extraction::{Cost, CostWidth};
use std::sync::Arc;

/// Whether `program` runs. A test that needs an external solver returns early, saying
/// so, when it is absent: CI installs none of them.
fn installed(program: &str) -> bool {
    let ok = std::process::Command::new(program)
        .arg("--version")
        .output()
        .is_ok();
    if !ok {
        eprintln!("{program} not installed: this test did not run");
    }
    ok
}

const SOLVER: Solver = Solver::Internal {
    max_solves: 5000,
    max_conflicts: None,
};
const RUNGS: [RungKind; 5] = [
    RungKind::Selection,
    RungKind::Levels,
    RungKind::Splits,
    RungKind::Binary,
    RungKind::Orders,
];

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

/// An operator: name, kind, arity range, and the number of integers it carries.
struct Op(&'static str, Kind, usize, usize, usize);

/// A random e-graph: class 0 is the root, the last two classes hold leaves, and
/// every other class holds one to three nodes whose children lie below it, except
/// for an occasional back edge.
fn random_graph(rng: &mut Rng, ops: &[Op], leaves: &[&'static str], classes: usize) -> Graph {
    let mut g = Graph {
        classes: vec![Vec::new(); classes],
        ..Default::default()
    };
    for c in 0..classes {
        let count = if c + 2 >= classes {
            1 + rng.below(2)
        } else {
            1 + rng.below(3)
        };
        for _ in 0..count {
            let node = if c + 2 >= classes {
                Node {
                    op: leaves[rng.below(leaves.len())].into(),
                    ints: vec![],
                    strings: vec![format!("v{}", rng.below(3))],
                    children: vec![],
                    mults: Vec::new(),
                    class: c,
                    kind: Kind::Plain,
                    subsumed: false,
                }
            } else {
                let op = &ops[rng.below(ops.len())];
                let arity = op.2 + rng.below(op.3 - op.2 + 1);
                let mut children: Vec<usize> = (0..arity)
                    .map(|_| c + 1 + rng.below(classes - c - 1))
                    .collect();
                if rng.below(8) == 0 {
                    children[0] = rng.below(c + 1);
                }
                if op.1 == Kind::Set {
                    children.sort();
                    children.dedup();
                }
                let ints = (0..op.4).map(|_| rng.below(9) as i64).collect::<Vec<_>>();
                let mut ints = ints;
                ints.sort();
                Node {
                    op: op.0.into(),
                    ints: ints
                        .into_iter()
                        .map(semi_persistent_egraph::extraction::Cost::from)
                        .collect(),
                    strings: vec![],
                    children,
                    mults: Vec::new(),
                    class: c,
                    kind: op.1,
                    subsumed: false,
                }
            };
            g.classes[c].push(g.nodes.len());
            g.nodes.push(node);
        }
        if g.classes[c].len() > 1 && rng.below(6) == 0 {
            let n = g.classes[c][0];
            g.nodes[n].subsumed = true;
        }
    }
    // A multiset node may draw one class twice: store it as one operand with its count.
    g.coalesce().unwrap();
    g
}

fn check(
    name: &str,
    native: fn(&dyn Rung, &mut Build),
    ops: &[Op],
    leaves: &[&'static str],
    seed: u64,
    trials: usize,
) {
    let criteria = std::fs::read_to_string(format!(
        "{}/tests/mltl/costs/{name}.mzn",
        env!("CARGO_MANIFEST_DIR")
    ))
    .unwrap();
    let native = CostModel::Native(native);
    let solvers = [
        (
            "cp-sat",
            OpbCommand::new("minizinc")
                .arg("--solver")
                .arg("cp-sat")
                .arg("--time-limit")
                .arg("60000"),
        ),
        (
            "chuffed",
            OpbCommand::new("minizinc")
                .arg("--solver")
                .arg("chuffed")
                .arg("--time-limit")
                .arg("60000"),
        ),
    ];
    let mut rng = Rng(seed);
    let mut proved = 0;
    for trial in 0..trials {
        let size = 5 + rng.below(4);
        let g = Arc::new(random_graph(&mut rng, ops, leaves, size));
        for rung in RUNGS {
            let n = native
                .extract(g.clone(), rung, &SOLVER, CostWidth::default())
                .unwrap();
            for (sname, cmd) in &solvers {
                let what = format!("{name} {trial} {rung:?} {sname}");
                let m = semi_persistent_egraph::extraction::mzn::extract(&g, rung, &criteria, cmd)
                    .unwrap_or_else(|e| panic!("{what}: {e}"));
                assert_eq!(m.status, n.status, "{what}: status");
                if n.status != Status::Proved {
                    continue;
                }
                assert_eq!(m.cost.map(Cost::from), n.cost, "{what}: optimum");
                assert_eq!(
                    Some(native.cost_of(g.clone(), rung, m.term.as_ref().unwrap())),
                    m.cost.map(Cost::from),
                    "{what}: the Rust cost of the MiniZinc term"
                );
                proved += 1;
            }
        }
    }
    eprintln!(
        "{name}: {trials} e-graphs x 5 rungs x 2 solvers, {proved} optima, MiniZinc equals Rust"
    );
    assert!(proved >= trials * 5, "most instances have a term");
}

#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solver under a time limit: --features slow-tests"
)]
fn mltl_memory_minizinc_equals_rust() {
    if !installed("minizinc") {
        return;
    }
    let ops = [
        Op("Global", Kind::Plain, 1, 1, 2),
        Op("Future", Kind::Plain, 1, 1, 2),
        Op("Until", Kind::Plain, 2, 2, 2),
        Op("Not", Kind::Plain, 1, 1, 0),
        Op("And", Kind::MSet, 2, 5, 0),
        Op("Or", Kind::Set, 2, 4, 0),
        Op("Equiv", Kind::Comm, 2, 2, 0),
    ];
    check(
        "mltl_memory",
        |r, b| semi_persistent_egraph::extraction::mltl_cost::mltl_memory(r, b),
        &ops,
        &["Atom", "Bool"],
        0x3171,
        100,
    );
}

#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solver under a time limit: --features slow-tests"
)]
fn pipeline_registers_minizinc_equals_rust() {
    if !installed("minizinc") {
        return;
    }
    let ops = [
        Op("Add", Kind::MSet, 2, 5, 0),
        Op("Mul", Kind::MSet, 2, 4, 0),
        Op("Neg", Kind::Plain, 1, 1, 0),
        Op("Div", Kind::Plain, 2, 2, 0),
        Op("Call2", Kind::Plain, 2, 2, 0),
        Op("Sub", Kind::Seq(Assoc::Left), 2, 4, 0),
        Op("Pow", Kind::Seq(Assoc::Right), 3, 4, 0),
        Op("Cat", Kind::Seq(Assoc::Both), 3, 5, 0),
    ];
    check(
        "pipeline_registers",
        |r, b| semi_persistent_egraph::extraction::mltl_cost::pipeline_registers(r, b),
        &ops,
        &["Var", "Num"],
        0x91BE,
        100,
    );
}

#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solver under a time limit: --features slow-tests"
)]
fn monitor_history_minizinc_equals_rust() {
    if !installed("minizinc") {
        return;
    }
    let ops = [
        Op("Formerly", Kind::Plain, 1, 1, 1),
        Op("Since", Kind::Plain, 2, 2, 1),
        Op("Previous", Kind::Plain, 1, 1, 1),
        Op("Not", Kind::Plain, 1, 1, 0),
        Op("And", Kind::Set, 2, 4, 0),
        Op("Or", Kind::MSet, 2, 3, 0),
    ];
    check(
        "monitor_history",
        |r, b| semi_persistent_egraph::extraction::mltl_cost::monitor_history(r, b),
        &ops,
        &["Atom"],
        0xD06,
        100,
    );
}
