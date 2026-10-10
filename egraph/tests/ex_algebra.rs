// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The cost algebra's polarity claims, against the SAT solver.
//!
//! On random e-graphs of at most 6 classes, every acyclic term is enumerated. For
//! every integer an expression builds and every one of its breakpoints `v`, with the
//! term's selectors assumed:
//!
//! - an over-estimate (or an exact integer) cannot have `[x >= v]` false when its
//!   true value is at least `v`;
//! - an under-estimate (or an exact integer) cannot have `[x >= v]` true when its
//!   true value is below `v`;
//! - the thresholds equal to the truth are satisfiable together, so the encoding
//!   excludes no term.
//!
//! These are the Bool polarities as well: `at_least` of an over-estimate may be
//! spuriously true but never spuriously false, and so on. A free integer's value is a
//! decision; each of its values is assumed in turn.

use cadical_sys::{CaDiCal, Status};
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node, Term};
use semi_persistent_egraph::extraction::oint::{
    Build, Detached, Exact, OInt, Over, Polarity, SumMethod, Under,
};
use semi_persistent_egraph::extraction::pb::Pb;
use semi_persistent_egraph::extraction::rung::{Rung, Selection};
use semi_persistent_egraph::extraction::solve::value_on;
use semi_persistent_egraph::extraction::target::CnfTarget;
use semi_persistent_egraph::extraction::{Cost, CostWidth, Lit};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }
}

fn graph(rng: &mut Rng) -> Graph {
    let classes = 3 + rng.below(4) as usize;
    let mut g = Graph {
        nodes: Vec::new(),
        classes: vec![Vec::new(); classes],
        root: classes - 1,
    };
    for c in 0..classes {
        let members = if c == 0 { 1 } else { 1 + rng.below(2) as usize };
        for _ in 0..members {
            let arity = if c == 0 {
                0
            } else {
                (rng.below(3) as usize).min(c)
            };
            let children: Vec<usize> = (0..arity).map(|_| rng.below(c as u64) as usize).collect();
            let n = g.nodes.len();
            g.nodes.push(Node {
                op: "f".into(),
                ints: vec![Cost::from(rng.below(5))],
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

/// Every acyclic term: one candidate per reachable class, cut to what the root uses.
fn terms(g: &Graph) -> Vec<Term> {
    let reach = g.reachable();
    let choices: Vec<Vec<usize>> = reach.iter().map(|&c| g.candidates(c).collect()).collect();
    let (mut out, mut seen) = (Vec::new(), BTreeSet::new());
    let mut idx = vec![0usize; reach.len()];
    loop {
        let mut selection = vec![None; g.classes.len()];
        for (i, &c) in reach.iter().enumerate() {
            selection[c] = Some(choices[i][idx[i]]);
        }
        let full = Term {
            selection,
            trees: Default::default(),
        };
        if let Ok(order) = full.order(g) {
            let mut sel = vec![None; g.classes.len()];
            for c in order {
                sel[c] = full.selection[c];
            }
            if seen.insert(sel.clone()) {
                out.push(Term {
                    selection: sel,
                    trees: Default::default(),
                });
            }
        }
        let mut i = 0;
        loop {
            if i == idx.len() {
                return out;
            }
            idx[i] += 1;
            if idx[i] < choices[i].len() {
                break;
            }
            idx[i] = 0;
            i += 1;
        }
    }
}

fn dimacs(l: Lit) -> Option<i32> {
    match l {
        Lit::Var { var, sign } => Some(if sign { var as i32 } else { -(var as i32) }),
        _ => None,
    }
}

/// Whether `lits` can all hold together with the formula.
fn sat(s: &mut CaDiCal, lits: &[Lit]) -> bool {
    if lits.contains(&Lit::False) {
        return false;
    }
    for &l in lits {
        if let Some(d) = dimacs(l) {
            s.assume(d);
        }
    }
    s.solve() == Status::SATISFIABLE
}

/// An integer of any polarity, for checking.
/// Evaluates a probe's integer on a decoded term, given the model.
type Eval = Box<dyn Fn(&Detached, &Selection, &Term, &dyn Fn(u32) -> bool) -> Cost>;

struct Probe {
    name: String,
    polarity: &'static str,
    values: Vec<Cost>,
    thresholds: Vec<Lit>,
    eval: Eval,
}

fn probe<P: Polarity>(name: &str, x: &OInt<P>) -> Probe {
    let y = x.clone();
    Probe {
        name: name.to_string(),
        polarity: P::NAME,
        values: x.values().to_vec(),
        thresholds: x.thresholds().map(|(_, l)| l).collect(),
        eval: Box::new(move |b, r, t, m| value_on(b, r, t, &y, m)),
    }
}

/// Every integer the algebra builds from two attributes and a free integer.
fn build(b: &mut Build, sel: &Selection, rng: &mut Rng) -> (Vec<Probe>, OInt<Exact>) {
    let late: Vec<Option<OInt<Over>>> = b.rec_max(sel, &|n| n.ints[0]);
    let early: Vec<Option<OInt<Under>>> = b.rec_max_down(sel, &|n| n.ints[0]);
    let root = sel.graph.root;
    let (late, early) = (late[root].clone().unwrap(), early[root].clone().unwrap());
    let free = b.int(&[0, 2, 5, 9]);
    let (c, lo) = (2 + rng.below(3), rng.below(6) as i64);
    let mut out = vec![
        probe("late", &late),
        probe("early", &early),
        probe("free", &free),
    ];
    out.push(probe("late.scale", &b.scale(&late, c)));
    out.push(probe("early.scale", &b.scale(&early, c)));
    out.push(probe("free.scale", &b.scale(&free, c)));
    out.push(probe("late.clamp", &b.clamp(&late, lo)));
    out.push(probe("early.clamp", &b.clamp(&early, lo)));
    out.push(probe("free.clamp", &b.clamp(&free, lo)));
    let sc = b.scale(&late, c);
    out.push(probe("late.scale.clamp", &b.clamp(&sc, lo)));
    let fs = b.scale(&free, c);
    let fc = b.clamp(&fs, lo);
    out.push(probe("free.scale.clamp.shift", &b.shift(&fc, 3)));

    // Negation, addition, and subtraction as addition after negation.
    out.push(probe("late.neg", &b.neg(&late)));
    out.push(probe("early.neg", &b.neg(&early)));
    out.push(probe("free.neg", &b.neg(&free)));
    let nn = b.neg(&late);
    out.push(probe("late.neg.neg", &b.neg(&nn)));
    let fo = free.clone().over();
    out.push(probe("late.plus.free", &b.plus(&late, &fo)));
    let fu = free.clone().under();
    out.push(probe("early.plus.free", &b.plus(&early, &fu)));
    out.push(probe("free.plus.free", &b.plus(&free, &free)));
    let d = b.minus(&late, &early);
    out.push(probe("late.minus.early", &d));
    out.push(probe("late.minus.early.clamp", &b.clamp(&d, 0)));
    out.push(probe("late.clamp_sub.early", &b.clamp_sub(&late, &early)));
    out.push(probe("early.minus.late", &b.minus(&early, &late)));
    out.push(probe("free.minus.free", &b.minus(&free, &free)));

    // The same sums and clamped differences through the merge network.
    let net = SumMethod::Network;
    out.push(probe("net.late.plus.free", &b.plus_by(&late, &fo, net)));
    out.push(probe("net.early.plus.free", &b.plus_by(&early, &fu, net)));
    out.push(probe("net.free.plus.free", &b.plus_by(&free, &free, net)));
    let nd = b.neg(&early);
    out.push(probe("net.late.minus.early", &b.plus_by(&late, &nd, net)));
    out.push(probe(
        "net.late.clamp_sub.early",
        &b.clamp_sub_by(&late, &early, net),
    ));
    let fs2 = b.scale(&free, 3);
    out.push(probe("net.free.plus.scaled", &b.plus_by(&free, &fs2, net)));
    out.push(probe(
        "net.free.clamp_sub.free",
        &b.clamp_sub_by(&free, &free, net),
    ));

    // Pseudo-Boolean terms, sorted into integers of their polarity.
    let sel_lit = sel.class(sel.reachable[0]);
    let t_over = Pb::of(&late)
        .plus(&Pb::of(&free.clone().over()))
        .plus(&Pb::lit(sel_lit, 2));
    out.push(probe("pb.over.sorted", &b.sorted(&t_over).unwrap()));
    let t_under = Pb::of(&early).minus(&Pb::of(&late));
    let (lo_u, _) = t_under.bounds();
    let t_under = t_under.plus_const(-lo_u);
    out.push(probe("pb.under.sorted", &b.sorted(&t_under).unwrap()));
    let t_exact = Pb::of(&free)
        .times(2)
        .plus(&Pb::lit(sel_lit, 3))
        .minus(&Pb::lit(sel_lit.not(), 1))
        .plus_const(1);
    out.push(probe("pb.exact.sorted", &b.sorted(&t_exact).unwrap()));
    out.push(probe(
        "pb.exact.neg.neg.sorted",
        &b.sorted(&t_exact.neg().neg()).unwrap(),
    ));
    // x.linear().sorted() is x in value: checked by comparing the two probes' truths.
    out.push(probe(
        "late.linear.sorted",
        &b.sorted(&Pb::of(&late)).unwrap(),
    ));
    out.push(probe(
        "early.linear.sorted",
        &b.sorted(&Pb::of(&early)).unwrap(),
    ));
    out.push(probe(
        "free.linear.sorted",
        &b.sorted(&Pb::of(&free)).unwrap(),
    ));

    // Comparison literals, as integers over {0, 1}: `[t >= k]` is the threshold at 1.
    for (name, k) in [("pb.over.at_least", 4i64), ("pb.over.at_least_hi", 9)] {
        let l = b.pb_at_least(&t_over, k);
        let s = b.sorted(&t_over).unwrap();
        out.push(bool_probe(name, "Over", l, s, k));
    }
    for (name, k) in [("pb.under.at_least", 1i64), ("pb.under.at_least_hi", 5)] {
        let l = b.pb_at_least(&t_under, k);
        let s = b.sorted(&t_under).unwrap();
        out.push(bool_probe(name, "Under", l, s, k));
    }
    for (name, k) in [("pb.exact.at_least", 3i64), ("pb.exact.at_least_hi", 12)] {
        let l = b.pb_at_least(&t_exact, k);
        let s = b.sorted(&t_exact).unwrap();
        out.push(bool_probe(name, "Exact", l, s, k));
    }
    (out, free)
}

/// A comparison literal `l` for `t >= k`, checked as the integer `[t >= k]` over
/// `{0, 1}`: its truth is computed from the sorted term's truth.
fn bool_probe<P: Polarity>(
    name: &str,
    polarity: &'static str,
    l: Lit,
    sorted: OInt<P>,
    k: i64,
) -> Probe {
    Probe {
        name: name.to_string(),
        polarity,
        values: vec![Cost::ZERO, Cost::ONE],
        thresholds: vec![Lit::True, l],
        eval: Box::new(move |b, r, t, m| Cost::from((value_on(b, r, t, &sorted, m) >= k) as i64)),
    }
}

#[test]
fn every_integer_the_algebra_builds_is_on_the_side_its_polarity_states() {
    let mut rng = Rng(0xA16E);
    let (mut graphs, mut checks) = (0, 0);
    for _ in 0..200 {
        let g = Arc::new(graph(&mut rng));
        let mut cnf = CnfTarget::default();
        let (sel, probes, free, rec) = {
            let mut b = Build::new(&mut cnf);
            let sel = Selection::build(g.clone(), &mut b);
            let (probes, free) = build(&mut b, &sel, &mut rng);
            (sel, probes, free, b.detach())
        };
        let mut s = CaDiCal::new();
        for c in &cnf.sink.clauses {
            for &l in c {
                if let Some(d) = dimacs(l) {
                    s.add(d);
                }
            }
            s.add(0);
        }
        graphs += 1;
        for t in terms(&g) {
            let fixed: Vec<Lit> = sel
                .canonical(&t)
                .into_iter()
                .map(|(v, b)| if b { Lit::pos(v) } else { Lit::pos(v).not() })
                .collect();
            // The free integer at each of its values, by its thresholds.
            for (j, _) in free.values().iter().enumerate() {
                let ft: Vec<Lit> = free
                    .thresholds()
                    .enumerate()
                    .map(|(i, (_, l))| if i <= j { l } else { l.not() })
                    .collect();
                let fmodel: BTreeMap<u32, bool> = ft
                    .iter()
                    .filter_map(|&l| match l {
                        Lit::Var { var, sign } => Some((var, sign)),
                        _ => None,
                    })
                    .collect();
                let model = |v: u32| fmodel.get(&v).copied().unwrap_or(false);
                let base: Vec<Lit> = fixed.iter().chain(ft.iter()).copied().collect();
                let truth_of = |n: &str| {
                    (probes.iter().find(|p| p.name == n).unwrap().eval)(&rec, &sel, &t, &model)
                };
                for (x, y) in [
                    ("late", "late.neg.neg"),
                    ("late.minus.early.clamp", "late.clamp_sub.early"),
                    ("late.clamp_sub.early", "net.late.clamp_sub.early"),
                    ("late.minus.early", "net.late.minus.early"),
                    ("free.plus.free", "net.free.plus.free"),
                    ("late", "late.linear.sorted"),
                    ("early", "early.linear.sorted"),
                    ("free", "free.linear.sorted"),
                    ("pb.exact.sorted", "pb.exact.neg.neg.sorted"),
                ] {
                    assert_eq!(truth_of(x), truth_of(y), "{x} and {y} differ in value");
                }
                for p in &probes {
                    let truth = (p.eval)(&rec, &sel, &t, &model);
                    for (&v, &l) in p.values.iter().zip(&p.thresholds) {
                        let mut q = base.clone();
                        if truth >= v && p.polarity != "Under" {
                            q.push(l.not());
                            assert!(
                                !sat(&mut s, &q),
                                "{}: [x >= {v}] false while the truth is {truth}",
                                p.name
                            );
                        }
                        if truth < v && p.polarity != "Over" {
                            q.push(l);
                            assert!(
                                !sat(&mut s, &q),
                                "{}: [x >= {v}] true while the truth is {truth}",
                                p.name
                            );
                        }
                        checks += 1;
                    }
                    // The thresholds equal to the truth are satisfiable together.
                    let mut q = base.clone();
                    for (&v, &l) in p.values.iter().zip(&p.thresholds) {
                        q.push(if truth >= v { l } else { l.not() });
                    }
                    assert!(sat(&mut s, &q), "{}: the truth {truth} is excluded", p.name);
                }
            }
        }
    }
    eprintln!("{graphs} e-graphs, {checks} threshold checks: every integer on its stated side");
    assert!(checks > 10_000);
}

/// A value outside the build's width is a build error naming the operation, not a
/// wrapped value; under the unbounded width the same operations are exact.
#[test]
fn an_overflow_is_an_error_naming_the_operation() {
    for (op, make) in [
        (
            "plus",
            Box::new(|b: &mut Build| {
                let x = b.int(&[0, i64::MAX]);
                let one = b.int(&[0, 1]);
                let _ = b.plus(&x, &one);
            }) as Box<dyn Fn(&mut Build)>,
        ),
        (
            "plus_const",
            Box::new(|b: &mut Build| {
                let x = b.int(&[0, i64::MAX]);
                let _ = b.shift(&x, 1);
            }),
        ),
        (
            "neg",
            Box::new(|b: &mut Build| {
                let x = b.int(&[i64::MIN, 0]);
                let _ = b.neg(&x);
            }),
        ),
        (
            "scale",
            Box::new(|b: &mut Build| {
                let x = b.int(&[0, i64::MAX / 2 + 1]);
                let _ = b.scale(&x, 2);
            }),
        ),
    ] {
        let mut cnf = CnfTarget::default();
        let mut b = Build::with_width(&mut cnf, CostWidth::W64);
        make(&mut b);
        let errors = b.detach().errors;
        assert!(
            errors
                .iter()
                .any(|e| e.starts_with(op) && e.contains("outside the 64-bit")),
            "{op}: {errors:?}"
        );
        let mut cnf = CnfTarget::default();
        let mut b = Build::with_width(&mut cnf, CostWidth::Big);
        make(&mut b);
        assert!(
            b.detach().errors.is_empty(),
            "{op} under the unbounded width"
        );
    }
}
