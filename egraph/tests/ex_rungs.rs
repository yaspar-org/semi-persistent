// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E4: each rung encodes exactly its family of trees, each tree once.
//!
//! A flat node over `k` atoms. Every model is enumerated with CaDiCaL, blocking each
//! decoded term on the literals that fix it. The number of models, the number of
//! distinct trees they decode to, and an independent enumeration of the family must
//! all be equal. Every tree found must also be reachable from its canonical
//! assignment: assuming the rung literals `canonical` gives it leaves the formula
//! satisfiable, which is what interpretation relies on.

use cadical_sys::{CaDiCal, Status};
use semi_persistent_egraph::extraction::Lit;
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node, Tree};
use semi_persistent_egraph::extraction::oint::Build;
use semi_persistent_egraph::extraction::rung::{Levels, Orders, Rung, Selection, Splits};
use semi_persistent_egraph::extraction::target::CnfTarget;
use std::collections::BTreeSet;
use std::sync::Arc;

/// A flat node over `mults.len()` atoms, atom `c` occurring `mults[c]` times, as an
/// AC operator's multiset of children.
fn flat_mult(mults: &[usize]) -> Arc<Graph> {
    let k = mults.len();
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
    // Each operand once, with its count, as the e-graph stores it.
    let counts = mults.iter().map(|&m| m as u64).collect();
    g.nodes.push(Node {
        op: "Add".into(),
        ints: vec![],
        strings: vec![],
        children: (0..k).collect(),
        class: k,
        kind: Kind::MSet,
        mults: counts,
        subsumed: false,
    });
    g.classes[k].push(k);
    Arc::new(g)
}

/// Every unordered tree over `items`: a partition into at least two blocks, each a tree.
fn trees(items: &[usize]) -> Vec<Tree> {
    if items.len() == 1 {
        return vec![Tree::Leaf(items[0])];
    }
    fn partitions(xs: &[usize]) -> Vec<Vec<Vec<usize>>> {
        if xs.is_empty() {
            return vec![vec![]];
        }
        let mut out = Vec::new();
        for p in partitions(&xs[1..]) {
            for i in 0..p.len() {
                let mut q = p.clone();
                q[i].insert(0, xs[0]);
                out.push(q);
            }
            let mut q = p.clone();
            q.insert(0, vec![xs[0]]);
            out.push(q);
        }
        out
    }
    let mut out = Vec::new();
    for p in partitions(items) {
        if p.len() < 2 {
            continue;
        }
        let mut combos: Vec<Vec<Tree>> = vec![vec![]];
        for block in &p {
            let sub = trees(block);
            combos = combos
                .into_iter()
                .flat_map(|c| {
                    sub.iter().map(move |t| {
                        let mut c = c.clone();
                        c.push(t.clone());
                        c
                    })
                })
                .collect();
        }
        out.extend(combos.into_iter().map(Tree::Node));
    }
    out
}

fn chain(t: &Tree) -> bool {
    match t {
        Tree::Leaf(_) => true,
        Tree::Node(o) => {
            o.iter().filter(|x| matches!(x, Tree::Node(_))).count() <= 1 && o.iter().all(chain)
        }
    }
}
fn binary(t: &Tree) -> bool {
    match t {
        Tree::Leaf(_) => true,
        Tree::Node(o) => o.len() == 2 && o.iter().all(binary),
    }
}
/// Orderings of a tree's operands, recursively.
fn orderings(t: &Tree) -> usize {
    match t {
        Tree::Leaf(_) => 1,
        Tree::Node(o) => {
            (1..=o.len()).product::<usize>() * o.iter().map(orderings).product::<usize>()
        }
    }
}

fn enumerate<R: Rung>(
    k: usize,
    make: &dyn Fn(Selection, &mut Build) -> R,
    ordered: bool,
) -> (usize, usize) {
    enumerate_mult(&vec![1; k], make, ordered)
}

fn enumerate_mult<R: Rung>(
    mults: &[usize],
    make: &dyn Fn(Selection, &mut Build) -> R,
    ordered: bool,
) -> (usize, usize) {
    let k = mults.len();
    let g = flat_mult(mults);
    let mut cnf = CnfTarget::default();
    let rung = {
        let mut b = Build::new(&mut cnf);
        let sel = Selection::build(g.clone(), &mut b);
        make(sel, &mut b)
    };
    let mut s = CaDiCal::new();
    for cl in &cnf.sink.clauses {
        for &l in cl {
            if let Lit::Var { var, sign } = l {
                s.add(if sign { var as i32 } else { -(var as i32) });
            }
        }
        s.add(0);
    }
    let n = cnf.sink.num_vars();
    let (mut models, mut seen) = (0, BTreeSet::new());
    while s.solve() == Status::SATISFIABLE {
        let assign: Vec<bool> = (0..=n).map(|v| v > 0 && s.val(v as i32) > 0).collect();
        let model = |v: u32| assign[v as usize];
        let term = rung.decode(&model);
        let tree = term
            .trees
            .get(&k)
            .cloned()
            .unwrap_or(Tree::Node((0..k).map(Tree::Leaf).collect()));
        models += 1;
        // The output carries every operand's whole count: operand `c` is referenced
        // once, with count `mults[c]`, in whichever internal node of the tree holds it.
        let json: serde_json::Value =
            serde_json::from_str(&term.to_json(&g).expect("acyclic")).unwrap();
        for (c, &mult) in mults.iter().enumerate() {
            let (mut refs, mut count) = (0usize, 0u64);
            for n in json["nodes"].as_object().unwrap().values() {
                let kids = n["children"].as_array().unwrap();
                for (i, r) in kids.iter().enumerate() {
                    if r.as_str() == Some(&format!("c{c}")) {
                        refs += 1;
                        count += n["mults"].get(i).and_then(|m| m.as_u64()).unwrap_or(1);
                    }
                }
            }
            assert_eq!(
                (refs, count),
                (1, mult as u64),
                "{}: operand {c} of multiplicity {} written {refs} times, count {count}, in {}",
                rung.name(),
                mult,
                tree.ordered()
            );
        }
        seen.insert(if ordered {
            tree.ordered()
        } else {
            tree.canon()
        });
        // The canonical assignment of this term is consistent with the formula.
        let canon = rung.canonical(&term);
        let mut probe = CaDiCal::new();
        for cl in &cnf.sink.clauses {
            for &l in cl {
                if let Lit::Var { var, sign } = l {
                    probe.add(if sign { var as i32 } else { -(var as i32) });
                }
            }
            probe.add(0);
        }
        for (&v, &val) in &canon {
            probe.assume(if val { v as i32 } else { -(v as i32) });
        }
        assert_eq!(
            probe.solve(),
            Status::SATISFIABLE,
            "{} k={k}: canonical assignment of {} is inconsistent",
            rung.name(),
            tree.ordered()
        );
        let back = rung.decode(&|v| canon.get(&v).copied().unwrap_or(false));
        assert_eq!(
            back.trees.get(&k),
            term.trees.get(&k),
            "{} k={k}: canonical assignment decodes differently",
            rung.name()
        );
        let lits = rung.term_literals(&model, &term);
        for l in lits {
            if let Lit::Var { var, sign } = l {
                s.add(if sign { -(var as i32) } else { var as i32 });
            }
        }
        s.add(0);
        assert!(models < 20_000, "runaway");
    }
    (models, seen.len())
}

#[test]
fn every_rung_is_a_bijection_onto_its_family() {
    for k in 3..=6 {
        let all = trees(&(0..k).collect::<Vec<_>>());
        let reference = [
            ("levels", all.iter().filter(|t| chain(t)).count()),
            ("splits", all.len()),
            ("binary", all.iter().filter(|t| binary(t)).count()),
        ];
        let got = [
            ("levels", enumerate(k, &|s, b| Levels::build(s, b), false)),
            (
                "splits",
                enumerate(k, &|s, b| Splits::build(s, b, false), false),
            ),
            (
                "binary",
                enumerate(k, &|s, b| Splits::build(s, b, true), false),
            ),
        ];
        for ((name, want), (_, (models, distinct))) in reference.iter().zip(got.iter()) {
            eprintln!("{name:<7} k={k}: models {models}, distinct {distinct}, reference {want}");
            assert_eq!(models, distinct, "{name} k={k}: a tree has two encodings");
            assert_eq!(distinct, want, "{name} k={k}: family mismatch");
        }
        assert_eq!(
            enumerate(k, &|s, _b| s, false),
            (1, 1),
            "selection keeps the flat node"
        );
    }
    for k in 3..=4 {
        let want: usize = trees(&(0..k).collect::<Vec<_>>())
            .iter()
            .map(orderings)
            .sum();
        let (models, distinct) = enumerate(k, &|s, b| Orders::build(s, b), true);
        eprintln!("orders  k={k}: models {models}, distinct {distinct}, reference {want}");
        assert_eq!(
            models, distinct,
            "orders k={k}: an ordered tree has two encodings"
        );
        assert_eq!(distinct, want, "orders k={k}: family mismatch");
    }
}

/// P1: a repeated operand is one leaf with its whole multiplicity, so every rung has
/// exactly as many trees as over distinct operands, and the output keeps every copy.
#[test]
fn multiplicities_follow_the_operand() {
    for mults in [
        vec![2, 1, 1],
        vec![3, 1, 2],
        vec![1, 2, 1, 3],
        vec![2, 2, 2, 1, 1],
    ] {
        let k = mults.len();
        let all = trees(&(0..k).collect::<Vec<_>>());
        let cases: [(&str, usize, (usize, usize)); 3] = [
            (
                "levels",
                all.iter().filter(|t| chain(t)).count(),
                enumerate_mult(&mults, &|s, b| Levels::build(s, b), false),
            ),
            (
                "splits",
                all.len(),
                enumerate_mult(&mults, &|s, b| Splits::build(s, b, false), false),
            ),
            (
                "binary",
                all.iter().filter(|t| binary(t)).count(),
                enumerate_mult(&mults, &|s, b| Splits::build(s, b, true), false),
            ),
        ];
        for (name, want, (models, distinct)) in cases {
            eprintln!(
                "{name:<7} mults {mults:?}: models {models}, distinct {distinct}, reference {want}"
            );
            assert_eq!((models, distinct), (want, want), "{name} {mults:?}");
        }
        assert_eq!(enumerate_mult(&mults, &|s, _b| s, false), (1, 1));
        if k <= 4 {
            let want: usize = all.iter().map(orderings).sum();
            assert_eq!(
                enumerate_mult(&mults, &|s, b| Orders::build(s, b), true),
                (want, want),
                "orders {mults:?}"
            );
        }
    }
}

// --- sequences --------------------------------------------------------------------

use semi_persistent_egraph::extraction::graph::Assoc;

/// A sequence node over `k` atoms, the atoms in order, one class each unless
/// `repeat` puts atom 0 at the last position as well.
fn sequence(k: usize, kind: Kind, repeat: bool) -> Arc<Graph> {
    let atoms = if repeat { k - 1 } else { k };
    let mut g = Graph {
        nodes: Vec::new(),
        classes: vec![Vec::new(); atoms + 1],
        root: atoms,
    };
    for c in 0..atoms {
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
    let children: Vec<usize> = (0..k)
        .map(|p| if repeat && p == k - 1 { 0 } else { p })
        .collect();
    g.nodes.push(Node {
        op: "Cat".into(),
        ints: vec![],
        strings: vec![],
        children,
        class: atoms,
        kind,
        mults: Vec::new(),
        subsumed: false,
    });
    g.classes[atoms].push(atoms);
    Arc::new(g)
}

fn leaves_in_order(t: &Tree) -> Vec<usize> {
    match t {
        Tree::Leaf(p) => vec![*p],
        Tree::Node(o) => o.iter().flat_map(leaves_in_order).collect(),
    }
}

/// Every tree the rung's models denote for the sequence node, each model's tree
/// once, with the canonical assignment of each term checked against the formula.
fn sequence_trees<R: Rung>(
    g: &Arc<Graph>,
    make: &dyn Fn(Selection, &mut Build) -> R,
) -> (usize, Vec<Tree>, R) {
    let seq = g.nodes.len() - 1;
    let k = g.nodes[seq].children.len();
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
    let n = cnf.sink.num_vars();
    let (mut models, mut trees) = (0, Vec::new());
    while s.solve() == Status::SATISFIABLE {
        let assign: Vec<bool> = (0..=n).map(|v| v > 0 && s.val(v as i32) > 0).collect();
        let model = |v: u32| assign[v as usize];
        let term = rung.decode(&model);
        let tree = term
            .trees
            .get(&seq)
            .cloned()
            .unwrap_or(Tree::Node((0..k).map(Tree::Leaf).collect()));
        models += 1;
        trees.push(tree);
        // The term's canonical assignment satisfies the formula.
        let canon = rung.canonical(&term);
        let mut probe = CaDiCal::new();
        for cl in &cnf.sink.clauses {
            add(&mut probe, cl);
        }
        for (&v, &b) in &canon {
            probe.assume(if b { v as i32 } else { -(v as i32) });
        }
        assert_eq!(
            probe.solve(),
            Status::SATISFIABLE,
            "{}: the canonical assignment of a decoded term is inconsistent",
            rung.name()
        );
        let block: Vec<Lit> = rung
            .term_literals(&model, &term)
            .into_iter()
            .map(|l| l.not())
            .collect();
        add(&mut s, &block);
    }
    (models, trees, rung)
}

/// Chains of nested intervals over `k` positions, the whole excluded: the trees the
/// levels rung must give a sequence.
fn chains(k: usize) -> usize {
    let iv: Vec<(usize, usize)> = (0..k)
        .flat_map(|i| ((i + 1)..k).map(move |j| (i, j)))
        .filter(|&x| x != (0, k - 1))
        .collect();
    // Chains of strictly nested intervals, counted by their innermost element.
    fn count(from: (usize, usize), iv: &[(usize, usize)]) -> usize {
        1 + iv
            .iter()
            .filter(|&&(i, j)| i >= from.0 && j <= from.1 && (i, j) != from)
            .map(|&x| count(x, iv))
            .sum::<usize>()
    }
    1 + iv.iter().map(|&x| count(x, &iv)).sum::<usize>()
}

#[test]
fn a_sequence_has_every_bracketing_once_at_each_rung() {
    // Catalan numbers C(k-1) and little Schröder numbers s(k).
    let catalan = [0, 0, 0, 2, 5, 14, 42, 132];
    let schroeder = [0, 0, 0, 3, 11, 45, 197, 903];
    for k in 3..=7 {
        for repeat in [false, true] {
            let g = sequence(k, Kind::Seq(Assoc::Both), repeat);
            for (name, want) in [
                ("binary", catalan[k]),
                ("splits", schroeder[k]),
                ("orders", schroeder[k]),
                ("levels", chains(k)),
            ] {
                let (models, trees, _) = match name {
                    "binary" => {
                        let (m, t, _) = sequence_trees(&g, &|s, b| Splits::build(s, b, true));
                        (m, t, ())
                    }
                    "splits" => {
                        let (m, t, _) = sequence_trees(&g, &|s, b| Splits::build(s, b, false));
                        (m, t, ())
                    }
                    "orders" => {
                        let (m, t, _) = sequence_trees(&g, &Orders::build);
                        (m, t, ())
                    }
                    _ => {
                        let (m, t, _) = sequence_trees(&g, &Levels::build);
                        (m, t, ())
                    }
                };
                let distinct: BTreeSet<String> = trees.iter().map(|t| t.ordered()).collect();
                assert_eq!(
                    distinct.len(),
                    models,
                    "{name} k={k}: a tree with two models"
                );
                assert_eq!(models, want, "{name} k={k} repeat={repeat}: bracketings");
                for t in &trees {
                    assert_eq!(
                        leaves_in_order(t),
                        (0..k).collect::<Vec<_>>(),
                        "{name} k={k}: leaves out of order in {}",
                        t.ordered()
                    );
                    if name == "binary" {
                        assert!(binary(t), "{name}: {}", t.ordered());
                    }
                    if name == "levels" {
                        assert!(chain(t), "{name}: {}", t.ordered());
                    }
                }
            }
        }
    }
}

#[test]
fn a_fold_has_one_bracketing_at_every_rung() {
    for k in 3..=7 {
        for left in [true, false] {
            let g = sequence(
                k,
                Kind::Seq(if left { Assoc::Left } else { Assoc::Right }),
                false,
            );
            let seq = g.nodes.len() - 1;
            let want: BTreeSet<Vec<usize>> = (2..k)
                .map(|len| {
                    if left {
                        (0..len).collect()
                    } else {
                        (k - len..k).collect()
                    }
                })
                .collect();
            let check = |models: usize, inner: Vec<Vec<usize>>, name: &str| {
                assert_eq!(models, 1, "{name} k={k} left={left}: models");
                let got: BTreeSet<Vec<usize>> = inner.into_iter().collect();
                assert_eq!(got, want, "{name} k={k} left={left}: internal nodes");
            };
            let spans = |r: &dyn Rung| -> Vec<Vec<usize>> {
                r.inner_nodes(seq)
                    .iter()
                    .map(|t| {
                        let mut m: Vec<usize> = t.members.iter().map(|&(_, c)| c).collect();
                        m.sort();
                        m
                    })
                    .collect()
            };
            let (m, _, r) = sequence_trees(&g, &|s, _| s);
            check(m, spans(&r), "selection");
            let (m, _, r) = sequence_trees(&g, &Levels::build);
            check(m, spans(&r), "levels");
            let (m, _, r) = sequence_trees(&g, &|s, b| Splits::build(s, b, false));
            check(m, spans(&r), "splits");
            let (m, _, r) = sequence_trees(&g, &Orders::build);
            check(m, spans(&r), "orders");
        }
    }
}

/// `position(d)` is defined for the depths a tree has, 1 to `k - 1`, and `None` outside
/// them: depth 0 has no constraint deciding it, and a depth past the tree's is out of
/// the variables' range.
#[test]
fn a_position_outside_the_trees_depths_is_none() {
    use semi_persistent_egraph::extraction::rung::Ordering;
    let k = 4;
    let g = flat_mult(&vec![1; k]);
    let mut cnf = CnfTarget::default();
    let mut b = Build::new(&mut cnf);
    let sel = Selection::build(g.clone(), &mut b);
    let rung = Orders::build(sel, &mut b);
    let (node, operand) = (k, 0);
    for d in 1..k {
        assert!(rung.position(&mut b, node, operand, d).is_some(), "depth {d}");
    }
    for d in [0, k, k + 5, usize::MAX] {
        assert!(rung.position(&mut b, node, operand, d).is_none(), "depth {d}");
    }
}
