// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Literals, clauses, and the assignment model the encoders are specified against.
//!
//! A literal is a nonzero `i32` in DIMACS convention: `v` for the positive
//! literal on variable `v`, `-v` for its negation. Variable 0 does not exist, so
//! a literal of 0 is rejected at construction. Two constants outside that range
//! stand for the truth values an encoder produces when a partial sum is fixed:
//! they are erased when clauses are emitted, rather than being allocated a
//! variable and two unit clauses.

/// A literal, or one of the two truth constants.
///
/// `True` and `False` arise inside the encoders: the partial sum of an empty
/// prefix is at least 0 under every assignment, so the indicator for threshold 0
/// is the constant `True`. Representing it as a constant keeps the clause set
/// free of the unit clause that a fresh variable would need.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Lit {
    /// The positive (`sign == true`) or negative literal on variable `var`.
    Var {
        var: u32,
        sign: bool,
    },
    True,
    False,
}

impl Lit {
    /// The positive literal on `var`.
    pub fn pos(var: u32) -> Lit {
        Lit::Var { var, sign: true }
    }

    /// The negative literal on `var`.
    pub fn neg(var: u32) -> Lit {
        Lit::Var { var, sign: false }
    }

    /// The complement. Negating a constant flips it; negating a literal flips its
    /// sign. An inherent method rather than `std::ops::Not`, so that the hundred-odd
    /// call sites need no trait import.
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> Lit {
        match self {
            Lit::Var { var, sign } => Lit::Var { var, sign: !sign },
            Lit::True => Lit::False,
            Lit::False => Lit::True,
        }
    }

    /// Whether this is a truth constant rather than a literal on a variable.
    pub fn is_const(self) -> bool {
        matches!(self, Lit::True | Lit::False)
    }
}

/// A sink that accumulates clauses and hands out fresh variables.
///
/// The encoders are written against this so one traversal can emit to a vector
/// for testing, or straight to a solver's incremental interface, without the
/// encoding code changing.
pub trait ClauseSink {
    /// Allocate an unused variable.
    fn fresh(&mut self) -> u32;

    /// Emit one clause. A clause containing `Lit::True` is discharged and must
    /// not be recorded; a `Lit::False` inside a clause must be dropped from it.
    fn clause(&mut self, lits: &[Lit]);
}

/// A `ClauseSink` that keeps every clause, for tests and for DIMACS output.
#[derive(Default, Debug)]
pub struct VecSink {
    pub next_var: u32,
    pub clauses: Vec<Vec<Lit>>,
}

impl VecSink {
    /// A sink whose fresh variables start above `used`, the largest variable the
    /// caller has already allocated.
    pub fn new(used: u32) -> Self {
        VecSink {
            next_var: used + 1,
            clauses: Vec::new(),
        }
    }

    /// Total clauses emitted, ignoring the ones simplification discharged.
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Variables allocated by the encoders plus the ones the caller declared.
    pub fn num_vars(&self) -> u32 {
        self.next_var - 1
    }

    /// DIMACS CNF text for the accumulated clause set.
    pub fn to_dimacs(&self) -> String {
        let mut out = format!("p cnf {} {}\n", self.num_vars(), self.clauses.len());
        for c in &self.clauses {
            for l in c {
                match l {
                    Lit::Var { var, sign } => {
                        if *sign {
                            out.push_str(&format!("{var} "));
                        } else {
                            out.push_str(&format!("-{var} "));
                        }
                    }
                    // Simplification removes both constants before a clause is
                    // stored, so reaching one here is a bug in `clause`.
                    Lit::True | Lit::False => {
                        unreachable!("constant survived into a stored clause")
                    }
                }
            }
            out.push_str("0\n");
        }
        out
    }
}

impl ClauseSink for VecSink {
    fn fresh(&mut self) -> u32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn clause(&mut self, lits: &[Lit]) {
        // A clause with a true literal holds under every assignment, so storing
        // it would only cost the solver a pass over it. A false literal cannot
        // help satisfy the clause, so it is dropped. Both simplifications are
        // why `Lit` carries constants at all.
        let mut out: Vec<Lit> = Vec::with_capacity(lits.len());
        for l in lits {
            match l {
                Lit::True => return,
                Lit::False => {}
                Lit::Var { .. } => out.push(*l),
            }
        }
        // An empty clause is unsatisfiable and is kept: an encoder that emits one
        // has been asked for a threshold its inputs cannot reach, and the solver
        // should report that rather than the sink hiding it.
        self.clauses.push(out);
    }
}
