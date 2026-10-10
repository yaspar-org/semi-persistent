// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E1: both targets mean what the constraints say.
//!
//! Random systems of pseudo-Boolean constraints over at most 8 variables, with
//! negative coefficients, negated literals, repeated variables, and all three
//! relations. The satisfying assignments of the original variables are computed by
//! brute force and compared with (a) the models of the CNF lowering, enumerated by
//! CaDiCaL and projected onto the original variables, and (b) the OPB text, parsed
//! back and evaluated. The minimum of a random objective is compared the same way.

use cadical_sys::{CaDiCal, Status};
use semi_persistent_egraph::extraction::target::{Cmp, CnfTarget, OpbTarget, Target};
use semi_persistent_egraph::extraction::{Cost, Lit};
use std::collections::BTreeSet;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> i64 {
        (self.next() % n) as i64
    }
}

type Con = (Vec<(i64, Lit)>, Cmp, i64);

/// A constraint in the targets' coefficient type.
fn wide(c: &Con) -> (Vec<(Cost, Lit)>, Cmp, Cost) {
    (
        c.0.iter().map(|&(a, l)| (Cost::from(a), l)).collect(),
        c.1,
        Cost::from(c.2),
    )
}

fn holds(c: &Con, a: u32) -> bool {
    let val = |l: Lit| match l {
        Lit::True => true,
        Lit::False => false,
        Lit::Var { var, sign } => ((a >> (var - 1)) & 1 == 1) == sign,
    };
    let s: i64 = c.0.iter().map(|&(w, l)| if val(l) { w } else { 0 }).sum();
    match c.1 {
        Cmp::Ge => s >= c.2,
        Cmp::Le => s <= c.2,
        Cmp::Eq => s == c.2,
    }
}

fn parse_opb(text: &str, n: u32) -> Vec<Con> {
    let mut out = Vec::new();
    for line in text.lines().map(str::trim) {
        if line.starts_with('*') || line.starts_with("min:") || line.is_empty() {
            continue;
        }
        let body = line.strip_suffix(';').unwrap().trim();
        let (lhs, rel, rhs) = if let Some((l, r)) = body.split_once(">=") {
            (l, Cmp::Ge, r)
        } else {
            let (l, r) = body.split_once('=').unwrap();
            (l, Cmp::Eq, r)
        };
        let toks: Vec<&str> = lhs.split_whitespace().collect();
        let terms = toks
            .chunks(2)
            .map(|p| {
                let w: i64 = p[0].trim_start_matches('+').parse().unwrap();
                let (neg, v) = match p[1].strip_prefix('~') {
                    Some(v) => (true, v),
                    None => (false, p[1]),
                };
                let v: u32 = v.strip_prefix('x').unwrap().parse().unwrap();
                assert!(v <= n, "the OPB target writes no auxiliary variables");
                (w, if neg { Lit::neg(v) } else { Lit::pos(v) })
            })
            .collect();
        out.push((terms, rel, rhs.trim().parse().unwrap()));
    }
    out
}

#[test]
fn both_targets_have_exactly_the_brute_force_models() {
    let mut rng = Rng(0xE1);
    for trial in 0..300 {
        let n = 2 + rng.below(7) as u32; // 2..=8 variables
        let mut cons: Vec<Con> = Vec::new();
        for _ in 0..(1 + rng.below(3)) {
            let mut terms = Vec::new();
            for _ in 0..(1 + rng.below(n as u64 + 2)) {
                let v = 1 + rng.below(n as u64) as u32;
                let l = if rng.below(2) == 0 {
                    Lit::pos(v)
                } else {
                    Lit::neg(v)
                };
                terms.push((rng.below(11) - 5, l));
            }
            let cmp = [Cmp::Ge, Cmp::Le, Cmp::Eq][rng.below(3) as usize];
            cons.push((terms, cmp, rng.below(9) - 3));
        }
        let weights: Vec<u64> = (0..n).map(|_| rng.below(6) as u64).collect();
        let brute: BTreeSet<u32> = (0..(1u32 << n))
            .filter(|&a| cons.iter().all(|c| holds(c, a)))
            .collect();
        let cost = |a: u32| -> u64 {
            (0..n)
                .filter(|i| (a >> i) & 1 == 1)
                .map(|i| weights[i as usize])
                .sum()
        };

        // CNF: enumerate models projected onto the original variables.
        let mut cnf = CnfTarget::default();
        for _ in 0..n {
            cnf.fresh();
        }
        for c in &cons {
            let (t, cmp, k) = wide(c);
            cnf.pb(&t, cmp, k).unwrap();
        }
        let mut s = CaDiCal::new();
        for cl in &cnf.sink.clauses {
            for &l in cl {
                if let Lit::Var { var, sign } = l {
                    s.add(if sign { var as i32 } else { -(var as i32) });
                }
            }
            s.add(0);
        }
        let mut models = BTreeSet::new();
        while s.solve() == Status::SATISFIABLE {
            let a: u32 = (1..=n)
                .filter(|&v| s.val(v as i32) > 0)
                .map(|v| 1u32 << (v - 1))
                .sum();
            assert!(
                models.insert(a),
                "trial {trial}: a projected model repeated despite blocking"
            );
            for v in 1..=n {
                s.add(if (a >> (v - 1)) & 1 == 1 {
                    -(v as i32)
                } else {
                    v as i32
                });
            }
            s.add(0);
        }
        assert_eq!(
            models, brute,
            "trial {trial}: CNF models differ from brute force for {cons:?}"
        );

        // OPB: the text, parsed back and evaluated.
        let mut opb = OpbTarget::default();
        for _ in 0..n {
            opb.fresh();
        }
        for c in &cons {
            let (t, cmp, k) = wide(c);
            opb.pb(&t, cmp, k).unwrap();
        }
        let back = parse_opb(&opb.to_opb(&[]), n);
        let opb_models: BTreeSet<u32> = if opb.infeasible {
            BTreeSet::new()
        } else {
            (0..(1u32 << n))
                .filter(|&a| back.iter().all(|c| holds(c, a)))
                .collect()
        };
        assert_eq!(
            opb_models, brute,
            "trial {trial}: OPB models differ from brute force for {cons:?}"
        );

        // The optimum agrees too.
        let want = brute.iter().map(|&a| cost(a)).min();
        assert_eq!(
            models.iter().map(|&a| cost(a)).min(),
            want,
            "trial {trial}: optimum"
        );
    }
}
