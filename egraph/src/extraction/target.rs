// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Where constraints go: CNF for the internal solver, OPB for a third-party one.
//!
//! A cost function states pseudo-Boolean constraints `Σ aᵢ·ℓᵢ ⋈ k` and objective
//! terms; it never chooses how they are encoded. [`CnfTarget`] lowers a constraint
//! to clauses through the windowed totalizer of [`crate::extraction::totalizer`], whose
//! soundness and completeness are checked by exhaustive enumeration there;
//! [`OpbTarget`] writes it as it is.

use crate::extraction::cnf::{ClauseSink, Lit, VecSink};
use crate::extraction::cost::Cost;
use crate::extraction::totalizer::WindowedSum;
use std::collections::BTreeMap;
use std::fmt::Write as _;

/// The relation of a pseudo-Boolean constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmp {
    Ge,
    Le,
    Eq,
}

/// A sink for variables, clauses, pseudo-Boolean constraints, and objective terms.
pub trait Target {
    /// A fresh variable, as its positive literal.
    fn fresh(&mut self) -> Lit;
    /// A clause: at least one literal holds.
    fn clause(&mut self, lits: &[Lit]);
    /// `Σ aᵢ·ℓᵢ ⋈ k`. `Err` when the target cannot represent it, naming the limit.
    fn pb(&mut self, terms: &[(Cost, Lit)], cmp: Cmp, k: Cost) -> Result<(), String>;
    /// Add `w >= 0` to the objective when `lit` holds. `Err` when the target cannot
    /// represent the weight.
    fn objective(&mut self, w: Cost, lit: Lit) -> Result<(), String>;
    /// Add a constant, possibly negative, to the objective. Held exactly by every
    /// target: no solver sees it.
    fn objective_base(&mut self, w: Cost);
    /// Variables allocated so far.
    fn num_vars(&self) -> u32;
    /// For recovering the concrete target.
    fn as_any(&self) -> &dyn std::any::Any;
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any;
}

/// A constraint `Σ wᵢ·ℓᵢ <= bound` with every weight positive and every literal a
/// variable, or a verdict when constants decide it.
pub(crate) enum AtMost {
    True,
    False,
    Sum(Vec<(Lit, Cost)>, Cost),
}

/// Normalize `Σ aᵢ·ℓᵢ <= k`.
///
/// Terms are collected per variable, so `x` and `¬x` in one constraint combine.
/// A negative coefficient `a` on `x` is `a - a·¬x`, which moves `a` into the
/// constant and leaves a positive weight on `¬x`. Exact, in [`Cost`].
pub(crate) fn at_most(terms: &[(Cost, Lit)], k: Cost) -> AtMost {
    let mut constant = Cost::ZERO;
    let mut coef: BTreeMap<u32, Cost> = BTreeMap::new();
    for &(a, l) in terms {
        match l {
            Lit::True => constant += a,
            Lit::False => {}
            Lit::Var { var, sign: true } => *coef.entry(var).or_default() += a,
            // a·¬x = a - a·x
            Lit::Var { var, sign: false } => {
                constant += a;
                *coef.entry(var).or_default() -= a;
            }
        }
    }
    let mut bound = k - constant;
    let mut out = Vec::new();
    for (var, c) in coef {
        if c > 0 {
            out.push((Lit::pos(var), c));
        } else if c < 0 {
            // c·x = c + |c|·¬x
            bound -= c;
            out.push((Lit::neg(var), -c));
        }
    }
    if bound < 0 {
        return AtMost::False;
    }
    let total: Cost = out.iter().map(|&(_, w)| w).sum();
    if total <= bound {
        return AtMost::True;
    }
    AtMost::Sum(out, bound)
}

/// The constraint as one or two `<=` forms.
pub(crate) fn as_at_most(terms: &[(Cost, Lit)], cmp: Cmp, k: Cost) -> Vec<AtMost> {
    let neg: Vec<(Cost, Lit)> = terms.iter().map(|&(a, l)| (-a, l)).collect();
    match cmp {
        Cmp::Le => vec![at_most(terms, k)],
        Cmp::Ge => vec![at_most(&neg, -k)],
        Cmp::Eq => vec![at_most(terms, k), at_most(&neg, -k)],
    }
}

/// The weights in u64, when every one fits.
pub(crate) fn weights_u64(ws: &[(Lit, Cost)]) -> Option<Vec<(Lit, u64)>> {
    ws.iter()
        .map(|&(l, w)| w.to_u64().map(|w| (l, w)))
        .collect()
}

/// CNF, for the internal solver.
pub struct CnfTarget {
    pub sink: VecSink,
    /// Exact weights: the descent bounds them with the u64 totalizer when they fit it,
    /// with the exact one otherwise.
    pub objective: Vec<(Lit, Cost)>,
    pub base: Cost,
    /// Pseudo-Boolean constraints lowered, for reporting.
    pub pb_lowered: usize,
    /// Ranges of `objective` that are the threshold literals of one charged integer,
    /// in order: each range is a sorted block, `[x >= v1]`, `[x >= v2]`, ...
    pub blocks: Vec<std::ops::Range<usize>>,
}

impl Default for CnfTarget {
    fn default() -> Self {
        CnfTarget {
            sink: VecSink::new(0),
            objective: Vec::new(),
            base: Cost::ZERO,
            pb_lowered: 0,
            blocks: Vec::new(),
        }
    }
}

impl Target for CnfTarget {
    fn fresh(&mut self) -> Lit {
        Lit::pos(self.sink.fresh())
    }

    fn clause(&mut self, lits: &[Lit]) {
        if lits.iter().any(|l| matches!(l, Lit::True)) {
            return;
        }
        let kept: Vec<Lit> = lits
            .iter()
            .copied()
            .filter(|l| !matches!(l, Lit::False))
            .collect();
        self.sink.clause(&kept);
    }

    fn pb(&mut self, terms: &[(Cost, Lit)], cmp: Cmp, k: Cost) -> Result<(), String> {
        for form in as_at_most(terms, cmp, k) {
            match form {
                AtMost::True => {}
                AtMost::False => self.sink.clause(&[]),
                AtMost::Sum(ws, bound) => {
                    self.pb_lowered += 1;
                    // A clause needs no counter: `Σ ¬ℓ <= n-1` over unit weights is
                    // "some ℓ holds".
                    if ws.iter().all(|&(_, w)| w == 1) && bound + Cost::ONE == Cost::from(ws.len())
                    {
                        let cl: Vec<Lit> = ws.iter().map(|&(l, _)| l.not()).collect();
                        self.sink.clause(&cl);
                        continue;
                    }
                    // The u64 totalizer when everything fits it, so such a constraint is
                    // encoded as it always was; the exact one otherwise, which has no cap.
                    let small = bound
                        .to_u64()
                        .zip(weights_u64(&ws))
                        .filter(|(b, w)| WindowedSum::fits(w, b).is_ok());
                    let denied = match small {
                        Some((b, w)) => WindowedSum::new(&w, b).deny_above(&mut self.sink, b),
                        None => WindowedSum::new(&ws, bound).deny_above(&mut self.sink, bound),
                    };
                    for l in denied {
                        self.sink.clause(&[l.not()]);
                    }
                }
            }
        }
        Ok(())
    }

    fn objective(&mut self, w: Cost, lit: Lit) -> Result<(), String> {
        match lit {
            Lit::True => self.base += w,
            Lit::False => {}
            l if w > 0 => self.objective.push((l, w)),
            _ => {}
        }
        Ok(())
    }

    fn objective_base(&mut self, w: Cost) {
        self.base += w;
    }

    fn num_vars(&self) -> u32 {
        self.sink.num_vars()
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

/// Native OPB, for a third-party pseudo-Boolean solver.
#[derive(Default)]
pub struct OpbTarget {
    next_var: u32,
    /// Constraints in `Σ wᵢ·ℓᵢ >= k` form with integer weights, of any size: the
    /// format has no width.
    pub constraints: Vec<(Vec<(Cost, Lit)>, Cmp, Cost)>,
    pub objective: Vec<(Lit, Cost)>,
    pub base: Cost,
    /// Set when a constraint normalized to false: the instance is infeasible.
    pub infeasible: bool,
}

impl Target for OpbTarget {
    fn fresh(&mut self) -> Lit {
        self.next_var += 1;
        Lit::pos(self.next_var)
    }

    fn clause(&mut self, lits: &[Lit]) {
        let terms: Vec<(Cost, Lit)> = lits.iter().map(|&l| (Cost::ONE, l)).collect();
        // Unit coefficients: every target represents them.
        let _ = self.pb(&terms, Cmp::Ge, Cost::ONE);
    }

    fn pb(&mut self, terms: &[(Cost, Lit)], cmp: Cmp, k: Cost) -> Result<(), String> {
        // Constants are folded here so the file names only variables; the
        // constraint is otherwise written as stated.
        let mut k = k;
        let mut kept = Vec::new();
        for &(a, l) in terms {
            match l {
                Lit::True => k -= a,
                Lit::False => {}
                l => kept.push((a, l)),
            }
        }
        if kept.is_empty() {
            let holds = match cmp {
                Cmp::Ge => k <= 0,
                Cmp::Le => k >= 0,
                Cmp::Eq => k == 0,
            };
            if !holds {
                self.infeasible = true;
            }
            return Ok(());
        }
        self.constraints.push((kept, cmp, k));
        Ok(())
    }

    fn objective(&mut self, w: Cost, lit: Lit) -> Result<(), String> {
        match lit {
            Lit::True => self.base += w,
            Lit::False => {}
            l if w > 0 => self.objective.push((l, w)),
            _ => {}
        }
        Ok(())
    }

    fn objective_base(&mut self, w: Cost) {
        self.base += w;
    }

    fn num_vars(&self) -> u32 {
        self.next_var
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

fn opb_lit(l: Lit) -> String {
    match l {
        Lit::Var { var, sign: true } => format!("x{var}"),
        Lit::Var { var, sign: false } => format!("~x{var}"),
        _ => unreachable!("constants are folded before writing"),
    }
}

impl OpbTarget {
    /// The instance in the pseudo-Boolean competition format. `extra` lines, such as
    /// cycle exclusions and an incumbent bound, are appended by the solve loop.
    pub fn to_opb(&self, extra: &[(Vec<(Cost, Lit)>, Cmp, Cost)]) -> String {
        self.to_opb_with(extra, false)
    }

    /// As [`Self::to_opb`]. `full_header` adds the `#equal=` and `intsize=` fields
    /// of the competition header, which RoundingSat requires to log a proof and
    /// clasp's parser rejects, so they are written only when a proof is wanted.
    pub fn to_opb_with(
        &self,
        extra: &[(Vec<(Cost, Lit)>, Cmp, Cost)],
        full_header: bool,
    ) -> String {
        let all: Vec<&(Vec<(Cost, Lit)>, Cmp, Cost)> =
            self.constraints.iter().chain(extra.iter()).collect();
        let mut out = String::new();
        // The competition header in full, for a proof-logging solver that numbers
        // constraints from it, counting an equality as two.
        let equal = all.iter().filter(|(_, c, _)| *c == Cmp::Eq).count();
        // `intsize` is the bits of the largest sum of absolute coefficients (with
        // the degree) of any constraint or of the objective, plus a sign bit; a
        // solver that trusts it, as clasp does, fails on an understatement.
        let widest: Cost = all
            .iter()
            .map(|(t, _, k)| t.iter().map(|&(a, _)| a.abs()).sum::<Cost>() + k.abs())
            .chain(std::iter::once(
                self.objective.iter().map(|&(_, w)| w).sum::<Cost>(),
            ))
            .max()
            .unwrap_or(Cost::ONE)
            .max(Cost::ONE);
        let intsize = widest.bits() + 1;
        if full_header {
            let _ = writeln!(
                out,
                "* #variable= {} #constraint= {} #equal= {equal} intsize= {intsize}",
                self.next_var,
                all.len() + self.infeasible as usize
            );
        } else {
            let _ = writeln!(
                out,
                "* #variable= {} #constraint= {}",
                self.next_var,
                all.len() + self.infeasible as usize
            );
        }
        let _ = writeln!(
            out,
            "* base cost (add to the reported optimum): {}",
            self.base
        );
        if !self.objective.is_empty() {
            out.push_str("min:");
            for &(l, w) in &self.objective {
                let _ = write!(out, " +{w} {}", opb_lit(l));
            }
            out.push_str(" ;\n");
        }
        if self.infeasible {
            out.push_str(">= 1 ;\n");
        }
        for (terms, cmp, k) in all {
            // The competition format has `>=` and `=`; `<=` is written negated.
            let (negate, rel, rhs) = match cmp {
                Cmp::Ge => (false, ">=", *k),
                Cmp::Eq => (false, "=", *k),
                Cmp::Le => (true, ">=", -*k),
            };
            for &(a, l) in terms {
                let a = if negate { -a } else { a };
                let _ = write!(out, "{}{a} {} ", if a >= 0 { "+" } else { "" }, opb_lit(l));
            }
            let _ = writeln!(out, "{rel} {rhs} ;");
        }
        out
    }
}
