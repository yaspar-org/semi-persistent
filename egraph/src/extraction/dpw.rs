// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The objective bounded by rustsat's dynamic polynomial watchdog (DPW).
//!
//! The windowed totalizer (`crate::extraction::totalizer`) keeps every partial sum up
//! to the bound, so its size grows with the bound times the number of nodes: 31 M
//! clauses for Herbie's `Quantum` after rewriting at bound 6,187. DPW encodes the
//! weights bit by bit, and its size grows with the number of terms and the logarithm
//! of the weights, not with the bound. It is the bound the descent uses under
//! [`crate::extraction::solve::Solver::Dpw`].
//!
//! Variables are shared with the formula: a rustsat variable of index `i` is our
//! variable `i + 1`, and rustsat allocates above the sink's next free variable.

use crate::extraction::Lit;
use crate::extraction::cnf::{ClauseSink, VecSink};
use rustsat::encodings::pb::dpw::DynamicPolyWatchdog;
use rustsat::encodings::pb::{BoundUpper, BoundUpperIncremental};
use rustsat::instances::{BasicVarManager, Cnf, ManageVars};
use rustsat::types::{Lit as RLit, Var as RVar};

// Weights and bounds are u64 here and `usize` in rustsat: the casts below are
// lossless only on a 64-bit target, which this assertion requires.
const _: () = assert!(usize::BITS >= 64);

fn to_rs(l: Lit) -> RLit {
    match l {
        Lit::Var { var, sign } => RLit::new(var - 1, !sign),
        _ => unreachable!("objective literals are variables"),
    }
}

fn from_rs(l: RLit) -> Lit {
    let v = Lit::pos(l.var().idx32() + 1);
    if l.is_neg() { v.not() } else { v }
}

/// An objective's watchdog, encoded incrementally as the bound moves down.
pub struct Watchdog {
    dpw: DynamicPolyWatchdog,
    encoded: bool,
}

impl Watchdog {
    pub fn new(objective: &[(Lit, u64)]) -> Self {
        let dpw = objective
            .iter()
            .map(|&(l, w)| (to_rs(l), w as usize))
            .collect();
        Watchdog {
            dpw,
            encoded: false,
        }
    }

    /// Emit into `sink` what bounding the objective by `ub` needs, and return the
    /// literals whose truth enforces `objective <= ub`.
    pub fn at_most(&mut self, sink: &mut VecSink, ub: u64) -> Vec<Lit> {
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(RVar::new(sink.next_var - 1));
        let ub = ub as usize;
        if self.encoded {
            self.dpw
                .encode_ub_change(ub..=ub, &mut cnf, &mut vm)
                .expect("the encoding fits in memory");
        } else {
            self.dpw
                .encode_ub(ub..=ub, &mut cnf, &mut vm)
                .expect("the encoding fits in memory");
            self.encoded = true;
        }
        if let Some(max) = vm.max_var() {
            while sink.next_var <= max.idx32() + 1 {
                sink.fresh();
            }
        }
        for cl in cnf {
            let lits: Vec<Lit> = cl.iter().map(|&l| from_rs(l)).collect();
            sink.clause(&lits);
        }
        self.dpw
            .enforce_ub(ub)
            .expect("encoded for this bound")
            .into_iter()
            .map(from_rs)
            .collect()
    }
}
