// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Answer-set programming: a third target, and an extension only it offers.
//!
//! [`AspTarget`] implements [`Target`], so every cost function written against
//! the common layer runs on it unchanged: a variable is a choice atom `x(v)`, a
//! clause an integrity constraint, a pseudo-Boolean constraint a `#sum` constraint,
//! and the objective a `#minimize` statement.
//!
//! [`AspBuild`] is the extension: rules, aggregates over derived atoms, and
//! objectives at other priorities, stated in clingo's language over the atoms of
//! the rung's literals. A cost function taking `&mut AspBuild` cannot be passed to
//! [`crate::extraction::solve::extract`], which offers only [`Build`], so a cost that needs ASP
//! does not compile against the CNF and OPB targets:
//!
//! ```compile_fail
//! use semi_persistent_egraph::extraction::asp::AspBuild;
//! use semi_persistent_egraph::extraction::graph::Graph;
//! use semi_persistent_egraph::extraction::rung::Selection;
//! use semi_persistent_egraph::extraction::solve::{extract, Solver};
//! let g = std::sync::Arc::new(Graph::default());
//! let cost = |_: &Selection, b: &mut AspBuild| b.rules("p.");
//! extract(g, |s, _| s, cost, &Solver::Internal { max_solves: 1, max_conflicts: None });
//! ```
//!
//! The same cost is accepted by [`crate::extraction::solve::extract_asp`]:
//!
//! ```no_run
//! use semi_persistent_egraph::extraction::asp::AspBuild;
//! use semi_persistent_egraph::extraction::graph::Graph;
//! use semi_persistent_egraph::extraction::rung::Selection;
//! use semi_persistent_egraph::extraction::solve::{extract_asp, OpbCommand};
//! let g = std::sync::Arc::new(Graph::default());
//! let cost = |_: &Selection, b: &mut AspBuild| b.rules("p.");
//! extract_asp(g, |s, _| s, cost, &OpbCommand::new("clingo"));
//! ```
//!
//! Acyclicity is not a solve loop here. The solver adds one rule per candidate
//! node, `ok(c) :- sel(n), ok(k1), ..., ok(km).`, and requires `ok(c)` of every
//! selected class. A stable model is supported, so `ok` holds of a class only
//! through a finite derivation, which is what excludes a cyclic selection.

use crate::extraction::Lit;
use crate::extraction::cost::Cost;
use crate::extraction::oint::Build;
use crate::extraction::target::{Cmp, OpbTarget, Target};
use std::fmt::Write as _;

/// A problem as an answer-set program.
pub struct AspTarget {
    inner: OpbTarget,
    /// Rules added through [`AspBuild`], verbatim.
    pub rules: Vec<String>,
    /// `#minimize` elements added through [`AspBuild`].
    pub minimize: Vec<String>,
    /// The priority of the common objective. Higher is more important, as in clingo.
    pub objective_priority: u32,
    /// Whether an extension objective was added, whose value the library cannot
    /// interpret.
    pub extended_objective: bool,
}

impl Default for AspTarget {
    fn default() -> Self {
        AspTarget {
            inner: OpbTarget::default(),
            rules: Vec::new(),
            minimize: Vec::new(),
            objective_priority: 1,
            extended_objective: false,
        }
    }
}

impl Target for AspTarget {
    fn fresh(&mut self) -> Lit {
        self.inner.fresh()
    }
    fn clause(&mut self, lits: &[Lit]) {
        self.inner.clause(lits)
    }
    fn pb(&mut self, terms: &[(Cost, Lit)], cmp: Cmp, k: Cost) -> Result<(), String> {
        let before = self.inner.constraints.len();
        self.inner.pb(terms, cmp, k)?;
        // The constraint as written, its constants folded into the bound.
        if let Some((kept, _, k)) = self.inner.constraints.get(before) {
            for &v in kept.iter().map(|(a, _)| a).chain(std::iter::once(k)) {
                clingo_int("a pseudo-Boolean constraint's coefficient or bound", v)?;
            }
        }
        Ok(())
    }
    fn objective(&mut self, w: Cost, lit: Lit) -> Result<(), String> {
        if !matches!(lit, Lit::True | Lit::False) {
            clingo_int("an objective weight", w)?;
        }
        self.inner.objective(w, lit)
    }
    fn objective_base(&mut self, w: Cost) {
        self.inner.objective_base(w)
    }
    fn num_vars(&self) -> u32 {
        self.inner.num_vars()
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

/// `v`, when clingo's 32-bit integers hold it. Clingo reads a literal past them
/// without an error and wraps it (`3000000000` as `-1294967296`, measured with clingo
/// 5.8.2), so a value outside is refused here.
pub fn clingo_int(what: &str, v: Cost) -> Result<i32, String> {
    v.to_i64()
        .and_then(|x| i32::try_from(x).ok())
        .ok_or_else(|| format!("{what} {v} is outside clingo's 32-bit integers"))
}

/// The ASP spelling of a literal in a rule body.
pub fn atom(l: Lit) -> String {
    match l {
        Lit::True => "#true".into(),
        Lit::False => "#false".into(),
        Lit::Var { var, sign: true } => format!("x({var})"),
        Lit::Var { var, sign: false } => format!("not x({var})"),
    }
}

impl AspTarget {
    /// The constant part of the common objective.
    pub fn base(&self) -> Cost {
        self.inner.base
    }

    /// The whole program, with `extra` rules appended (the solver's acyclicity rules).
    pub fn to_asp(&self, extra: &str) -> String {
        let mut out = String::new();
        let n = self.inner.num_vars();
        if n > 0 {
            let _ = writeln!(out, "{{ x(1..{n}) }}.");
        }
        if self.inner.infeasible {
            out.push_str(":- #true.\n");
        }
        for (terms, cmp, k) in &self.inner.constraints {
            // A clause is an integrity constraint over the negated literals.
            if *cmp == Cmp::Ge && *k == 1 && terms.iter().all(|&(a, _)| a == 1) {
                let body: Vec<String> = terms.iter().map(|&(_, l)| atom(l.not())).collect();
                let _ = writeln!(out, ":- {}.", body.join(", "));
                continue;
            }
            let elems: Vec<String> = terms
                .iter()
                .enumerate()
                .map(|(t, &(a, l))| format!("{a},{t} : {}", atom(l)))
                .collect();
            let rel = match cmp {
                Cmp::Ge => "<",
                Cmp::Le => ">",
                Cmp::Eq => "!=",
            };
            let _ = writeln!(out, ":- #sum {{ {} }} {rel} {k}.", elems.join(" ; "));
        }
        if !self.inner.objective.is_empty() {
            let p = self.objective_priority;
            let elems: Vec<String> = self
                .inner
                .objective
                .iter()
                .enumerate()
                .map(|(t, &(l, w))| format!("{w}@{p},o{t} : {}", atom(l)))
                .collect();
            let _ = writeln!(out, "#minimize {{ {} }}.", elems.join(" ; "));
        }
        for r in &self.rules {
            out.push_str(r);
            out.push('\n');
        }
        for e in &self.minimize {
            let _ = writeln!(out, "#minimize {{ {e} }}.");
        }
        out.push_str(extra);
        out
    }
}

/// A builder over an [`AspTarget`], with the ASP extension.
pub struct AspBuild<'b, 't> {
    b: &'b mut Build<'t>,
}

impl<'b, 't> AspBuild<'b, 't> {
    /// `None` unless `b` writes to an [`AspTarget`].
    pub fn new(b: &'b mut Build<'t>) -> Option<Self> {
        b.target().as_any_mut().downcast_mut::<AspTarget>()?;
        Some(AspBuild { b })
    }

    fn asp(&mut self) -> &mut AspTarget {
        self.b
            .target()
            .as_any_mut()
            .downcast_mut::<AspTarget>()
            .expect("checked at construction")
    }

    /// The ASP literal of `l`.
    pub fn atom(&self, l: Lit) -> String {
        atom(l)
    }

    /// Rules in clingo's language, added verbatim.
    pub fn rules(&mut self, text: &str) {
        self.asp().rules.push(text.to_string());
    }

    /// A `#minimize` statement's elements, `weight@priority,tuple : body; ...`.
    /// Their value is the solver's; interpreting it is the caller's.
    pub fn minimize(&mut self, elements: &str) {
        let t = self.asp();
        t.minimize.push(elements.to_string());
        t.extended_objective = true;
    }

    /// The priority of the objective stated through the common layer.
    pub fn objective_priority(&mut self, p: u32) {
        self.asp().objective_priority = p;
    }
}

impl<'b, 't> std::ops::Deref for AspBuild<'b, 't> {
    type Target = Build<'t>;
    fn deref(&self) -> &Build<'t> {
        self.b
    }
}

impl<'b, 't> std::ops::DerefMut for AspBuild<'b, 't> {
    fn deref_mut(&mut self) -> &mut Build<'t> {
        self.b
    }
}
