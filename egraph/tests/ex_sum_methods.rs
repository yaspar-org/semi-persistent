// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The two ways to add order-encoded integers against their clause estimates.
//!
//! For operands of spans 50 to 800 and breakpoint densities 0.1 to 1, both methods
//! are built in the upward direction and their clauses counted. Each count must lie
//! within a factor of 2 of `SumMethod::estimates`, which is what `SumMethod::choose`
//! decides by. (That both methods give the same values is `algebra.rs`'s check.)

use semi_persistent_egraph::extraction::Cost;
use semi_persistent_egraph::extraction::oint::{Build, OInt, Over, SumMethod};
use semi_persistent_egraph::extraction::target::CnfTarget;

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

fn operand(rng: &mut Rng, span: i64, density: f64) -> Vec<Cost> {
    let mut v: Vec<i64> = vec![0, span];
    for x in 1..span {
        if (rng.below(1000) as f64) < density * 1000.0 {
            v.push(x);
        }
    }
    v.sort();
    v.into_iter().map(Cost::from).collect()
}

fn clauses(a: &[Cost], b: &[Cost], method: SumMethod) -> usize {
    let mut cnf = CnfTarget::default();
    let mut bld = Build::new(&mut cnf);
    let x: OInt<Over> = bld.int(a).over();
    let y: OInt<Over> = bld.int(b).over();
    let before = bld.cnf().unwrap().sink.clauses.len();
    let _ = bld.plus_by(&x, &y, method);
    bld.cnf().unwrap().sink.clauses.len() - before
}

#[test]
fn each_method_is_within_a_factor_of_two_of_its_estimate() {
    let mut rng = Rng(0x5EED);
    let mut rows = Vec::new();
    for span in [50, 200, 800] {
        for density in [0.1, 0.25, 0.5, 1.0] {
            let (a, b) = (
                operand(&mut rng, span, density),
                operand(&mut rng, span, density),
            );
            let (pe, ne) = SumMethod::estimates(&a, &b);
            let (pc, nc) = (
                clauses(&a, &b, SumMethod::Pairwise),
                clauses(&a, &b, SumMethod::Network),
            );
            let (pr, nr) = (pc as f64 / pe as f64, nc as f64 / ne as f64);
            eprintln!(
                "span {span:4} density {density:4}: pairwise {pc:7} (estimate {pe:7}, x{pr:.2}), network {nc:6} (estimate {ne:6}, x{nr:.2}), chosen {:?}",
                SumMethod::choose(&a, &b)
            );
            rows.push((span, density, pr, nr));
        }
    }
    for (span, density, pr, nr) in rows {
        assert!(
            (0.5..=2.0).contains(&pr),
            "pairwise at span {span} density {density}: x{pr:.2}"
        );
        assert!(
            (0.5..=2.0).contains(&nr),
            "network at span {span} density {density}: x{nr:.2}"
        );
    }
}
