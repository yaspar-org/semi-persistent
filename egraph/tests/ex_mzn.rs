// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The MiniZinc dump's rungs against the CNF rungs.
//!
//! For one bracketed node (AC, sequence, or fold) of 3 to 6 operands, every solution
//! of `mzn::dump` with `solve satisfy` (enumerated by Chuffed) is decoded into a
//! tree, and every model of the library's CNF rung is too. The two sets of trees must
//! be equal, with one solution per tree, at every rung.

use cadical_sys::{CaDiCal, Status};
use semi_persistent_egraph::extraction::Lit;
use semi_persistent_egraph::extraction::graph::{Assoc, Graph, Kind, Node, Tree};
use semi_persistent_egraph::extraction::oint::Build;
use semi_persistent_egraph::extraction::rung::{Levels, Orders, Rung, RungKind, Selection, Splits};
use semi_persistent_egraph::extraction::solve::OpbCommand;
use semi_persistent_egraph::extraction::target::CnfTarget;
use std::collections::BTreeSet;
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

fn graph(k: usize, kind: Kind) -> Arc<Graph> {
    let mut g = Graph {
        nodes: Vec::new(),
        classes: vec![Vec::new(); k + 1],
        root: k,
    };
    for c in 0..k {
        g.nodes.push(Node {
            op: "Var".into(),
            ints: vec![],
            strings: vec![format!("p{c}")],
            children: vec![],
            class: c,
            kind: Kind::Plain,
            mults: Vec::new(),
            subsumed: false,
        });
        g.classes[c].push(c);
    }
    g.nodes.push(Node {
        op: "Op".into(),
        ints: vec![],
        strings: vec![],
        children: (0..k).collect(),
        class: k,
        kind,
        mults: Vec::new(),
        subsumed: false,
    });
    g.classes[k].push(k);
    Arc::new(g)
}

fn key(t: &Tree, ordered: bool) -> String {
    if ordered { t.ordered() } else { t.canon() }
}

fn cnf_trees<R: Rung>(
    g: &Arc<Graph>,
    make: &dyn Fn(Selection, &mut Build) -> R,
    ordered: bool,
) -> BTreeSet<String> {
    let n = g.nodes.len() - 1;
    let k = g.nodes[n].children.len();
    let mut cnf = CnfTarget::default();
    let rung = {
        let mut b = Build::new(&mut cnf);
        let sel = Selection::build(g.clone(), &mut b);
        make(sel, &mut b)
    };
    let mut s = CaDiCal::new();
    let add = |s: &mut CaDiCal, cl: &[Lit]| {
        for &l in cl {
            if let Lit::Var { var, sign } = l {
                s.add(if sign { var as i32 } else { -(var as i32) });
            }
        }
        s.add(0);
    };
    for cl in &cnf.sink.clauses {
        add(&mut s, cl);
    }
    let nv = cnf.sink.num_vars();
    let mut out = BTreeSet::new();
    while s.solve() == Status::SATISFIABLE {
        let assign: Vec<bool> = (0..=nv).map(|v| v > 0 && s.val(v as i32) > 0).collect();
        let model = |v: u32| assign[v as usize];
        let term = rung.decode(&model);
        let tree = term
            .trees
            .get(&n)
            .cloned()
            .unwrap_or(Tree::Node((0..k).map(Tree::Leaf).collect()));
        out.insert(key(&tree, ordered));
        let block: Vec<Lit> = rung
            .term_literals(&model, &term)
            .into_iter()
            .map(|l| l.not())
            .collect();
        add(&mut s, &block);
    }
    out
}

fn same(g: &Arc<Graph>, rung: RungKind, cnf: BTreeSet<String>, ordered: bool, what: &str) {
    let n = g.nodes.len() - 1;
    let k = g.nodes[n].children.len();
    let chuffed = OpbCommand::new("minizinc").arg("--solver").arg("chuffed");
    let terms =
        semi_persistent_egraph::extraction::mzn::enumerate(g, rung, "solve satisfy;", &chuffed)
            .unwrap_or_else(|e| panic!("{what}: {e}"));
    let trees: Vec<String> = terms
        .iter()
        .map(|t| {
            key(
                &t.trees
                    .get(&n)
                    .cloned()
                    .unwrap_or(Tree::Node((0..k).map(Tree::Leaf).collect())),
                ordered,
            )
        })
        .collect();
    let set: BTreeSet<String> = trees.iter().cloned().collect();
    assert_eq!(set.len(), trees.len(), "{what}: a tree with two solutions");
    assert_eq!(
        set, cnf,
        "{what}: the MiniZinc trees differ from the CNF ones"
    );
}

#[test]
fn the_minizinc_rungs_have_the_cnf_rungs_trees_each_once() {
    if !installed("minizinc") {
        return;
    }
    let mut checked = 0;
    for k in 3..=6 {
        for (kind, ordered) in [
            (Kind::MSet, false),
            (Kind::Seq(Assoc::Both), true),
            (Kind::Seq(Assoc::Left), true),
            (Kind::Seq(Assoc::Right), true),
        ] {
            let g = graph(k, kind);
            let what = |r: &str| format!("{kind:?} k={k} {r}");
            same(
                &g,
                RungKind::Selection,
                cnf_trees(&g, &|s, _| s, ordered),
                ordered,
                &what("selection"),
            );
            same(
                &g,
                RungKind::Levels,
                cnf_trees(&g, &Levels::build, ordered),
                ordered,
                &what("levels"),
            );
            same(
                &g,
                RungKind::Splits,
                cnf_trees(&g, &|s, b| Splits::build(s, b, false), ordered),
                ordered,
                &what("splits"),
            );
            same(
                &g,
                RungKind::Binary,
                cnf_trees(&g, &|s, b| Splits::build(s, b, true), ordered),
                ordered,
                &what("binary"),
            );
            if k <= 5 {
                let o = kind == Kind::MSet;
                same(
                    &g,
                    RungKind::Orders,
                    cnf_trees(&g, &Orders::build, o || ordered),
                    o || ordered,
                    &what("orders"),
                );
            }
            checked += 1;
        }
    }
    eprintln!("{checked} nodes x 5 rungs: the MiniZinc trees are the CNF trees, each once");
}
