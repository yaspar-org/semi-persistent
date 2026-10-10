// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E2: every operator encodes what its polarity says.
//!
//! For each operator, over random small value sets, every model of the encoding is
//! enumerated with CaDiCaL, projected onto the operands, the gates, and the result.
//! In every model the encoded result stands in the polarity's relation to the true
//! value the expression graph interprets (`=` for `Exact`, `≥` for `Over`, `≤` for
//! `Under`), and for every assignment of operands and gates some model attains the
//! true value exactly.

use cadical_sys::{CaDiCal, Status};
use semi_persistent_egraph::extraction::Lit;
use semi_persistent_egraph::extraction::oint::{Build, Exact, OInt, Polarity, encoded};
use semi_persistent_egraph::extraction::target::{CnfTarget, Target};
use std::collections::{BTreeMap, BTreeSet};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn values(&mut self) -> Vec<u64> {
        let k = 1 + self.below(3);
        (0..k).map(|_| self.below(7)).collect()
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Rel {
    Eq,
    Ge,
    Le,
}

fn rel_of<P: Polarity>() -> Rel {
    match P::NAME {
        "Exact" => Rel::Eq,
        "Over" => Rel::Ge,
        _ => Rel::Le,
    }
}

fn vars_of(ls: &[Lit]) -> Vec<u32> {
    ls.iter()
        .filter_map(|l| {
            if let Lit::Var { var, .. } = l {
                Some(*var)
            } else {
                None
            }
        })
        .collect()
}

/// Enumerate models projected onto `inputs ∪ out`, check the relation in every one,
/// and that each input assignment has a model attaining the true value.
fn check<P: Polarity>(name: &str, b: &Build, cnf: &CnfTarget, out: &OInt<P>, inputs: &[u32]) {
    let rel = rel_of::<P>();
    let out_vars = vars_of(&out.thresholds().map(|(_, l)| l).collect::<Vec<_>>());
    let mut project: Vec<u32> = inputs.iter().chain(out_vars.iter()).copied().collect();
    project.sort_unstable();
    project.dedup();
    let mut s = CaDiCal::new();
    for cl in &cnf.sink.clauses {
        for &l in cl {
            if let Lit::Var { var, sign } = l {
                s.add(if sign { var as i32 } else { -(var as i32) });
            }
        }
        s.add(0);
    }
    let n = cnf.num_vars();
    let mut exact_hit: BTreeMap<Vec<bool>, bool> = BTreeMap::new();
    let mut models = 0;
    while s.solve() == Status::SATISFIABLE {
        models += 1;
        let assign: Vec<bool> = (0..=n).map(|v| v > 0 && s.val(v as i32) > 0).collect();
        let model = |v: u32| assign[v as usize];
        let truth = b.eval(out, &model, &|_| {
            semi_persistent_egraph::extraction::Cost::ZERO
        });
        let enc = encoded(out, &model);
        let ok = match rel {
            Rel::Eq => enc == truth,
            Rel::Ge => enc >= truth,
            Rel::Le => enc <= truth,
        };
        assert!(ok, "{name}: encoded {enc} vs true {truth} violates {rel:?}");
        let key: Vec<bool> = inputs.iter().map(|&v| assign[v as usize]).collect();
        *exact_hit.entry(key).or_insert(false) |= enc == truth;
        for &v in &project {
            s.add(if assign[v as usize] {
                -(v as i32)
            } else {
                v as i32
            });
        }
        s.add(0);
        assert!(models < 200_000, "{name}: runaway enumeration");
    }
    assert!(!exact_hit.is_empty(), "{name}: no model at all");
    for (k, hit) in &exact_hit {
        assert!(
            hit,
            "{name}: inputs {k:?} have no model attaining the true value"
        );
    }
}

fn ints(b: &mut Build, rng: &mut Rng, k: usize) -> (Vec<OInt<Exact>>, Vec<u32>) {
    let mut xs = Vec::new();
    let mut vars = Vec::new();
    for _ in 0..k {
        let x = b.int(&rng.values().iter().map(|&v| v as i64).collect::<Vec<_>>());
        vars.extend(vars_of(&x.thresholds().map(|(_, l)| l).collect::<Vec<_>>()));
        xs.push(x);
    }
    (xs, vars)
}

#[test]
fn every_operator_respects_its_polarity() {
    let mut rng = Rng(0xE2);
    let mut checked = BTreeSet::new();
    for trial in 0..60 {
        macro_rules! case {
            ($name:expr, |$b:ident, $xs:ident, $gs:ident| $body:expr) => {{
                let mut cnf = CnfTarget::default();
                let (out, inputs, b_exprs) = {
                    let mut $b = Build::new(&mut cnf);
                    let ($xs, mut inputs) = ints(&mut $b, &mut rng, 3);
                    let $gs: Vec<Lit> = (0..3).map(|_| $b.target().fresh()).collect();
                    inputs.extend(vars_of(&$gs));
                    let out = $body;
                    (out, inputs, $b)
                };
                let _ = &b_exprs;
                // Rebuilt around the same target to check; the build is moved out above.
                check($name, &b_exprs, unsafe_target(&b_exprs), &out, &inputs);
                checked.insert($name);
            }};
        }
        let _ = trial;
        case!("shift", |b, xs, gs| {
            let _ = &gs;
            b.shift(&xs[0], 3)
        });
        case!("max_of", |b, xs, gs| b.max_of(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1], gs[2]], xs[1].clone()),
            (vec![], xs[2].clone())
        ]));
        case!("max_of_exact", |b, xs, gs| b.max_of_exact(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1]], xs[1].clone())
        ]));
        case!("min_of", |b, xs, gs| b.min_of(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1], gs[2]], xs[1].clone()),
            (vec![], xs[2].clone())
        ]));
        case!("min_of_exact", |b, xs, gs| b.min_of_exact(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1]], xs[1].clone())
        ]));
        case!("max_of_down", |b, xs, gs| b.max_of_down(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1], gs[2]], xs[1].clone()),
            (vec![], xs[2].clone())
        ]));
        case!("min_of_up", |b, xs, gs| b.min_of_up(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1], gs[2]], xs[1].clone()),
            (vec![], xs[2].clone())
        ]));
        case!("min_of_up gated", |b, xs, gs| b.min_of_up(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1]], xs[1].clone())
        ]));
        case!("max_of_down gated", |b, xs, gs| b.max_of_down(&[
            (vec![gs[0]], xs[0].clone()),
            (vec![gs[1]], xs[1].clone())
        ]));
        case!("clamp_sub exact", |b, xs, gs| {
            let _ = &gs;
            b.clamp_sub(&xs[0], &xs[1])
        });
        case!("clamp_sub over-under", |b, xs, gs| {
            let hi = b.max_of(&[(vec![gs[0]], xs[0].clone()), (vec![gs[1]], xs[1].clone())]);
            let lo = b.min_of(&[(vec![gs[1]], xs[1].clone()), (vec![gs[2]], xs[2].clone())]);
            b.clamp_sub(&hi, &lo)
        });
        case!("sum", |b, xs, gs| {
            let _ = &gs;
            b.sum(&xs)
        });
        case!("ite", |b, xs, gs| b.ite(gs[0], &xs[0], &xs[1]));
        case!("when", |b, xs, gs| b.when(gs[0], &xs[0]));
        case!("saturate", |b, xs, gs| {
            let _ = &gs;
            b.saturate(&xs[0], 3)
        });
        case!("shift of max", |b, xs, gs| {
            let m = b.max_of(&[(vec![gs[0]], xs[0].clone()), (vec![], xs[1].clone())]);
            b.shift(&m, 2)
        });
    }
    eprintln!("checked: {checked:?}");
}

/// The builder keeps a mutable borrow of the target; the test needs it back to read
/// the clauses. This reads it through the builder's own accessor.
fn unsafe_target<'a>(b: &'a Build) -> &'a CnfTarget {
    b.cnf().expect("a CNF target")
}
