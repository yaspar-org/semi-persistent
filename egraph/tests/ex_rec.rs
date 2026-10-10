// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Recursive attributes in all four directions, against their definition.
//!
//! On random acyclic graphs, every model is enumerated. For each class of the
//! decoded term, the encoded attribute is compared with the attribute computed on
//! the term: equal is not required, the stated side is (`rec_max` and `rec_min_up`
//! at least the truth, `rec_min` and `rec_max_down` at most), and for every term
//! some model attains the truth.

use cadical_sys::{CaDiCal, Status};
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node, Term};
use semi_persistent_egraph::extraction::oint::{Build, OInt, Polarity, encoded};
use semi_persistent_egraph::extraction::rung::{Rung, Selection};
use semi_persistent_egraph::extraction::target::CnfTarget;
use semi_persistent_egraph::extraction::{Cost, Lit};
use std::collections::BTreeMap;
use std::sync::Arc;

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: u64) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) % n) as usize
    }
}

fn graph(rng: &mut Rng) -> Graph {
    let classes = 3 + rng.below(3);
    let mut g = Graph {
        nodes: Vec::new(),
        classes: vec![Vec::new(); classes],
        root: classes - 1,
    };
    for c in 0..classes {
        let members = if c == 0 { 1 } else { 1 + rng.below(2) };
        for _ in 0..members {
            let arity = if c == 0 { 0 } else { rng.below(3).min(c) };
            let children: Vec<usize> = (0..arity).map(|_| rng.below(c as u64)).collect();
            let n = g.nodes.len();
            g.nodes.push(Node {
                op: "f".into(),
                ints: vec![Cost::from(rng.below(4))],
                strings: vec![],
                children,
                class: c,
                kind: Kind::Plain,
                mults: Vec::new(),
                subsumed: false,
            });
            g.classes[c].push(n);
        }
    }
    g
}

fn truth(g: &Graph, t: &Term, max: bool) -> Vec<u64> {
    let mut v = vec![0; g.classes.len()];
    for c in t.order(g).unwrap() {
        let n = t.selection[c].unwrap();
        let kids = g.operands(n);
        let base = if kids.is_empty() {
            0
        } else if max {
            kids.iter().map(|&k| v[k]).max().unwrap()
        } else {
            kids.iter().map(|&k| v[k]).min().unwrap()
        };
        v[c] = base + g.nodes[n].ints[0].to_u64().unwrap();
    }
    v
}

/// Builds the operands of one check from a selection.
type Make<'a, P> = &'a dyn Fn(&Selection, &mut Build) -> Vec<Option<OInt<P>>>;

fn check<P: Polarity>(name: &str, make: Make<'_, P>, max: bool, at_least: bool) {
    let mut rng = Rng(0x5EC);
    for trial in 0..150 {
        let g = Arc::new(graph(&mut rng));
        let mut cnf = CnfTarget::default();
        let (sel, attr) = {
            let mut b = Build::new(&mut cnf);
            let sel = Selection::build(g.clone(), &mut b);
            let a = make(&sel, &mut b);
            (sel, a)
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
        let mut attained: BTreeMap<Vec<Option<usize>>, bool> = BTreeMap::new();
        let mut models = 0;
        while s.solve() == Status::SATISFIABLE {
            models += 1;
            let assign: Vec<bool> = (0..=n).map(|v| v > 0 && s.val(v as i32) > 0).collect();
            let model = |v: u32| assign[v as usize];
            let term = sel.decode(&model);
            let tv = truth(&g, &term, max);
            let mut exact = true;
            for c in term.order(&g).unwrap() {
                let e = encoded(attr[c].as_ref().unwrap(), &model);
                let tvc = tv[c] as i64;
                assert!(
                    if at_least { e >= tvc } else { e <= tvc },
                    "{name} trial {trial}: class {c} encoded {e}, true {}",
                    tv[c]
                );
                exact &= e == tvc;
            }
            *attained.entry(term.selection.clone()).or_insert(false) |= exact;
            for v in 1..=n {
                s.add(if assign[v as usize] {
                    -(v as i32)
                } else {
                    v as i32
                });
            }
            s.add(0);
            assert!(models < 100_000);
        }
        assert!(
            attained.values().all(|&x| x),
            "{name} trial {trial}: a term never attains its attribute"
        );
    }
    eprintln!("{name}: 150 graphs");
}

#[test]
fn recursive_attributes_in_every_direction() {
    let off = |n: &Node| n.ints[0];
    check("rec_max", &|s, b| b.rec_max(s, &off), true, true);
    check("rec_min", &|s, b| b.rec_min(s, &off), false, false);
    check("rec_max_down", &|s, b| b.rec_max_down(s, &off), true, false);
    check("rec_min_up", &|s, b| b.rec_min_up(s, &off), false, true);
}
