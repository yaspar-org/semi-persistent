// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Every cost script in `tests/mltl/costs/` equals its Rust twin in `extraction::mltl_cost`.
//!
//! On random e-graphs over each cost's operators, at every rung, the script and the
//! Rust cost report the same status and the same optimum, and each scores the
//! other's term as the other does. The second check is the stronger one: two costs
//! that differ on some term can still share an optimum.
//!
//! The graphs mix every node kind: positional, commutative, associative, multiset
//! (with repeated operands), and set nodes, subsumed nodes, and back edges.

use semi_persistent_egraph::extraction::CostWidth;
use semi_persistent_egraph::extraction::graph::{Assoc, Graph, Kind, Node};
use semi_persistent_egraph::extraction::oint::Build;
use semi_persistent_egraph::extraction::rung::{Rung, RungKind};
use semi_persistent_egraph::extraction::script::{CostModel, Script};
use semi_persistent_egraph::extraction::solve::{Solver, Status};
use std::sync::Arc;

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

fn script(name: &str) -> Script {
    let path = format!(
        "{}/tests/mltl/costs/{name}.roto",
        env!("CARGO_MANIFEST_DIR")
    );
    Script::compile(&path).unwrap_or_else(|e| panic!("{e}"))
}

/// The script and the Rust cost agree on `g` at `rung`. Returns whether both proved
/// an optimum (false when no term exists).
fn agree(script: &CostModel, native: &CostModel, g: &Graph, rung: RungKind, what: &str) -> bool {
    let g = Arc::new(g.clone());
    let n = native
        .extract(g.clone(), rung, &SOLVER, CostWidth::default())
        .unwrap();
    let s = script
        .extract(g.clone(), rung, &SOLVER, CostWidth::default())
        .unwrap();
    assert_eq!(s.status, n.status, "{what}: status");
    if n.status == Status::Infeasible {
        return false;
    }
    assert_eq!(n.status, Status::Proved, "{what}");
    assert_eq!(s.cost, n.cost, "{what}: optimum");
    let (nt, st) = (n.term.unwrap(), s.term.unwrap());
    assert_eq!(
        Some(script.cost_of(g.clone(), rung, &nt)),
        n.cost,
        "{what}: the script's cost of the Rust term"
    );
    assert_eq!(
        Some(native.cost_of(g.clone(), rung, &st)),
        s.cost,
        "{what}: the Rust cost of the script's term"
    );
    true
}

fn check(
    name: &str,
    native: fn(&dyn Rung, &mut Build),
    ops: &[Op],
    leaves: &[&'static str],
    seed: u64,
    trials: usize,
) {
    let script = CostModel::Script(script(name));
    let native = CostModel::Native(native);
    let mut rng = Rng(seed);
    let mut proved = 0;
    for trial in 0..trials {
        let size = 5 + rng.below(4);
        let g = random_graph(&mut rng, ops, leaves, size);
        for rung in RUNGS {
            proved += agree(
                &script,
                &native,
                &g,
                rung,
                &format!("{name} {trial} {rung:?}"),
            ) as usize;
        }
    }
    eprintln!("{name}: {trials} e-graphs x 5 rungs, {proved} optima, script equals Rust");
    assert!(proved >= trials * 5 / 2, "most instances have a term");
}

#[test]
fn mltl_memory_script_equals_rust() {
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
        150,
    );
}

#[test]
fn pipeline_registers_script_equals_rust() {
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
        150,
    );
}

#[test]
fn monitor_history_script_equals_rust() {
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
        150,
    );
}

/// The clause-count weight `tools/apps/smt.py` generates, for a fixed table: `k`
/// is the number of children, a repeated operand counted with its multiplicity.
fn smt_weight(n: &Node) -> u64 {
    let k = if n.mults.is_empty() {
        n.children.len() as u64
    } else {
        n.mults.iter().sum()
    }
    .max(1);
    match n.op.as_str() {
        "and" | "or" => k + 1,
        "xor" => 4 * (k - 1),
        "not" => 0,
        "bvadd" => 112 * (k - 1),
        "eq" => 33,
        _ => 0,
    }
}

const SMT_SCRIPT: &str = r#"fn weight(g: Graph, n: Node) -> UBig {
    let zero = g.ubig(0);
    let one = g.ubig(1);
    let k = zero;
    for ch in n.children() {
        k = k.plus(ch.count());
    }
    if k.eq(zero) { k = one; }
    if n.is("and") {
        k.plus(one)
    } else if n.is("bvadd") {
        g.ubig(112).times(k.minus(one))
    } else if n.is("eq") {
        g.ubig(33)
    } else if n.is("not") {
        zero
    } else if n.is("or") {
        k.plus(one)
    } else if n.is("xor") {
        g.ubig(4).times(k.minus(one))
    } else {
        zero
    }
}

fn cost(g: Graph) {
    for n in g.nodes() {
        let w = weight(g, n);
        if w.gt(g.ubig(0)) {
            n.chosen().charge_if_big(w);
        }
    }
}
"#;

#[test]
fn the_generated_smt_weight_script_equals_rust() {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("smt_weight_{}.roto", std::process::id()));
    std::fs::write(&path, SMT_SCRIPT).unwrap();
    let script = CostModel::Script(
        Script::compile(path.to_str().unwrap()).unwrap_or_else(|e| panic!("{e}")),
    );
    let _ = std::fs::remove_file(&path);
    let native = CostModel::Native(|r, b| {
        let g = r.graph();
        for &c in &r.selection().reachable {
            for n in g.candidates(c) {
                let w = smt_weight(&g.nodes[n]);
                if w > 0 {
                    b.cost_if(r.selection().node(n), w);
                }
            }
        }
    });
    let ops = [
        Op("and", Kind::MSet, 2, 5, 0),
        Op("or", Kind::Set, 2, 4, 0),
        Op("xor", Kind::MSet, 2, 4, 0),
        Op("bvadd", Kind::MSet, 2, 4, 0),
        Op("eq", Kind::Comm, 2, 2, 0),
        Op("not", Kind::Plain, 1, 1, 0),
        Op("concat", Kind::Seq(Assoc::Both), 2, 3, 0),
    ];
    let mut rng = Rng(0x5A7);
    let mut proved = 0;
    for trial in 0..150 {
        let size = 5 + rng.below(4);
        let g = random_graph(&mut rng, &ops, &["Sym", "Lit"], size);
        for rung in RUNGS {
            proved += agree(&script, &native, &g, rung, &format!("smt {trial} {rung:?}")) as usize;
        }
    }
    eprintln!("smt weights: 150 e-graphs x 5 rungs, {proved} optima, script equals Rust");
    assert!(proved >= 150 * 5 / 2);
}

const COUNT_SCRIPT: &str = r#"fn cost(g: Graph) {
    let chosen = [];
    for n in g.nodes() {
        chosen.push(n.chosen());
    }
    g.count(chosen).charge();
}
"#;

/// A pseudo-Boolean term charged at once equals the same charges made one by one.
#[test]
fn a_charged_count_equals_one_charge_per_node() {
    let path = std::env::temp_dir().join(format!("count_{}.roto", std::process::id()));
    std::fs::write(&path, COUNT_SCRIPT).unwrap();
    let script = CostModel::Script(
        Script::compile(path.to_str().unwrap()).unwrap_or_else(|e| panic!("{e}")),
    );
    let _ = std::fs::remove_file(&path);
    let native = CostModel::Native(|r, b| {
        let g = r.graph();
        for &c in &r.selection().reachable {
            for n in g.candidates(c) {
                b.cost_if(r.selection().node(n), 1);
            }
        }
    });
    let ops = [
        Op("and", Kind::MSet, 2, 4, 0),
        Op("f", Kind::Plain, 1, 2, 0),
        Op("eq", Kind::Comm, 2, 2, 0),
    ];
    let mut rng = Rng(0xC0C0);
    let mut proved = 0;
    for trial in 0..150 {
        let size = 5 + rng.below(4);
        let g = random_graph(&mut rng, &ops, &["x", "y"], size);
        for rung in RUNGS {
            proved += agree(
                &script,
                &native,
                &g,
                rung,
                &format!("count {trial} {rung:?}"),
            ) as usize;
        }
    }
    eprintln!("count: 150 e-graphs x 5 rungs, {proved} optima, script equals Rust");
    assert!(proved >= 150 * 5 / 2);
}
