// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ground EUF theory solver: the e-graph as a theory backend for a
//! companion SAT solver.
//!
//! The division of labor (mirroring Z3's legacy `smt` core):
//!
//! - The (future) CDCL driver owns Boolean search: assignments, decisions,
//!   clause learning. Truth values live there, never in the e-graph.
//! - This layer owns the mapping between Boolean *atoms* and e-graph
//!   equality nodes, and answers one question: is the current set of
//!   asserted equalities and disequalities consistent under congruence,
//!   and if not, which asserted literals are jointly to blame?
//!
//! An atom is an interned `Eq` node. Asserting it true merges the two
//! argument classes with [`Justification::Assumption`] carrying the
//! literal, so proof extraction can later cross from an e-graph explanation
//! back into the Boolean domain. Asserting it false records nothing in the
//! e-graph (a disequality is an atom property, not a merge — Z3's design):
//! it is checked against the union-find after each rebuild.
//!
//! Backtracking composes the e-graph's semi-persistent token with this
//! layer's own trail lengths, following the struct-of-tokens convention
//! used throughout the workspace. A single [`Euf::restore`] undoes the
//! merges, the atom-table suffix, and the assignment trail together.

use std::collections::HashMap;

use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::{self, AssumptionId, ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::LitVal;
use semi_persistent_egraph::union_find::{Justification, ProofBuf};
use semi_persistent_egraph::{EGraph31, EGraphToken};

semi_persistent_containers::define_id31! {
    /// A 31-bit index into the EUF atom table. Atoms are created
    /// append-only and truncated by [`Euf::restore`], so an `AtomId` is
    /// stable for the lifetime of the scope that created it.
    pub struct AtomId / StoredAtomId, "atom";
}

/// A Boolean literal over EUF atoms.
///
/// The representation is the [`AssumptionId`] carrying `2 * atom + sign`
/// (low bit set = negative polarity) — the classic SAT packing, chosen so a
/// literal round-trips through [`Justification::Assumption`] with no side
/// table. The doubling means atoms above half the 31-bit id space have no
/// literal; like the deliberately 15-bit `RuleId`, the checked mint turns
/// that exhaustion into a panic rather than a wrapped id.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(AssumptionId);

impl Lit {
    pub fn new(atom: AtomId, positive: bool) -> Self {
        Lit(id::id_at(atom.to_usize() * 2 + usize::from(!positive)))
    }
    pub fn atom(self) -> AtomId {
        // In range by construction: every Lit was minted from an AtomId.
        id::id_at(self.0.to_usize() / 2)
    }
    pub fn is_positive(self) -> bool {
        self.0.to_usize() & 1 == 0
    }
    pub fn negated(self) -> Lit {
        Lit(id::id_at(self.0.to_usize() ^ 1))
    }
    /// The justification payload this literal travels as.
    pub fn assumption(self) -> AssumptionId {
        self.0
    }
    pub fn from_assumption(a: AssumptionId) -> Self {
        Lit(a)
    }
}

struct AtomData {
    /// The interned `Eq` node. One atom per node: `Eq` is a commutative
    /// (sorted-pair) operator, so `eq(a, b)` and `eq(b, a)` intern to the
    /// same node and therefore the same atom.
    node: ENodeId,
    lhs: ENodeId,
    rhs: ENodeId,
    value: Option<bool>,
}

/// Result of [`Euf::check`].
#[derive(Debug, PartialEq, Eq)]
pub enum CheckResult {
    /// The assignment is consistent. Carries equality literals entailed by
    /// the current assignment but not yet assigned (theory propagations);
    /// each can be explained on demand with [`Euf::explain_true_eq`].
    Ok(Vec<Lit>),
    /// The assignment is EUF-inconsistent. The returned literals are all
    /// currently assigned true and are jointly contradictory: the
    /// antecedent equalities that force two classes together, plus the
    /// disequality literal they violate. The learned clause is the negation
    /// of this set.
    Conflict(Vec<Lit>),
}

/// Restore token for [`Euf`]: the e-graph token plus this layer's trail
/// lengths, following the workspace's struct-of-tokens convention.
#[derive(Clone, Copy, Debug)]
pub struct EufToken {
    eg: EGraphToken,
    atoms_len: usize,
    trail_len: usize,
}

/// Ground EUF solver over a proof-tracking e-graph (`PROOFS = true` is
/// required: conflict explanation walks the justification forest).
pub struct Euf<L: LitVal> {
    eg: EGraph31<L, true, true>,
    term_sort: SortId,
    eq_op: OpId,
    atoms: Vec<AtomData>,
    atom_of_node: HashMap<ENodeId, AtomId>,
    /// Assignment order, for unwinding values on restore.
    trail: Vec<AtomId>,
    /// Scratch for proof extraction.
    buf: ProofBuf<ENodeId>,
}

impl<L: LitVal> Default for Euf<L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: LitVal> Euf<L> {
    pub fn new() -> Self {
        let mut eg = EGraph31::new();
        // Interned (not builtin) sorts are non-concrete, which both merge
        // directions need: term classes merge on assertion, and Bool-sorted
        // Eq classes merge when congruence identifies two atoms.
        let term_sort = eg.sorts_mut().intern("EufTerm");
        let bool_sort = eg.sorts_mut().intern("EufBool");
        let eq_op = eg
            .ops_mut()
            .register_c("euf=", [term_sort, term_sort], bool_sort);
        Euf {
            eg,
            term_sort,
            eq_op,
            atoms: Vec::new(),
            atom_of_node: HashMap::new(),
            trail: Vec::new(),
            buf: ProofBuf::new(),
        }
    }

    /// Declare an uninterpreted function `Term^arity -> Term`.
    pub fn declare_fun(&mut self, name: &str, arity: usize) -> OpId {
        let sorts = vec![self.term_sort; arity];
        self.eg.ops_mut().register(name, &sorts, self.term_sort)
    }

    /// Declare an uninterpreted constant and return its e-node.
    pub fn declare_const(&mut self, name: &str) -> ENodeId {
        let op = self.declare_fun(name, 0);
        self.eg.add(op, &[])
    }

    /// Build the term `op(children...)`.
    pub fn term(&mut self, op: OpId, children: &[ENodeId]) -> ENodeId {
        self.eg.add(op, children)
    }

    /// Intern the equality atom for `a = b`, reusing an existing atom when
    /// the (canonicalized, sorted) pair already has one.
    pub fn eq_atom(&mut self, a: ENodeId, b: ENodeId) -> AtomId {
        let node = self.eg.add(self.eq_op, &[a, b]);
        if let Some(&atom) = self.atom_of_node.get(&node) {
            return atom;
        }
        let atom: AtomId = id::id_at(self.atoms.len());
        self.atoms.push(AtomData {
            node,
            lhs: a,
            rhs: b,
            value: None,
        });
        self.atom_of_node.insert(node, atom);
        atom
    }

    pub fn value(&self, atom: AtomId) -> Option<bool> {
        self.atoms[atom.to_usize()].value
    }

    pub fn find(&self, x: ENodeId) -> ENodeId {
        self.eg.find_const(x)
    }

    /// Assert a literal. A positive equality merges the two classes with
    /// the literal as justification; a negative one only records the value
    /// — it is enforced by the next [`Euf::check`]. Re-asserting the same
    /// value is a no-op; asserting the opposite of an assigned literal is a
    /// caller bug (a CDCL driver never does this — it backtracks first).
    pub fn assert_lit(&mut self, lit: Lit) {
        let atom = lit.atom();
        let positive = lit.is_positive();
        let data = &mut self.atoms[atom.to_usize()];
        match data.value {
            Some(v) if v == positive => return,
            Some(_) => panic!("assert_lit on an atom already assigned the opposite value"),
            None => {}
        }
        data.value = Some(positive);
        let (lhs, rhs) = (data.lhs, data.rhs);
        self.trail.push(atom);
        if positive {
            // Already-equal classes make this a no-op merge; the atom's
            // truth is then explained by the pre-existing forest, not this
            // edge.
            self.eg.merge_justified(
                lhs,
                rhs,
                Justification::Assumption {
                    lit: lit.assumption(),
                },
            );
        }
    }

    /// Run congruence closure and check the assignment: rebuild, then scan
    /// the atom table against the union-find. Returns the first conflict,
    /// or the list of entailed-but-unassigned equality literals.
    ///
    /// The full-table scan is Layer 0 simplicity; the incremental version
    /// should drive this from the rebuild's `touched` log instead, which
    /// records exactly the recanonicalized nodes (the analogue of Z3's
    /// reinsert-parents hook).
    pub fn check(&mut self) -> CheckResult {
        self.eg.rebuild();
        let mut propagations = Vec::new();
        for i in 0..self.atoms.len() {
            let (lhs, rhs, value) = {
                let d = &self.atoms[i];
                (d.lhs, d.rhs, d.value)
            };
            if self.eg.find_const(lhs) != self.eg.find_const(rhs) {
                continue;
            }
            let atom: AtomId = id::id_at(i);
            match value {
                Some(true) => {}
                None => propagations.push(Lit::new(atom, true)),
                Some(false) => {
                    // The classes were forced together by asserted
                    // equalities (and congruence), yet the atom says they
                    // must differ.
                    let mut conflict = self.explain_eq_lits(lhs, rhs);
                    conflict.push(Lit::new(atom, false));
                    return CheckResult::Conflict(conflict);
                }
            }
        }
        CheckResult::Ok(propagations)
    }

    /// Explain why an atom's two sides are currently equal, as the set of
    /// asserted equality literals whose merges (closed under congruence)
    /// force it. Returns `None` if the sides are not equal.
    pub fn explain_true_eq(&mut self, atom: AtomId) -> Option<Vec<Lit>> {
        let (lhs, rhs) = {
            let d = &self.atoms[atom.to_usize()];
            (d.lhs, d.rhs)
        };
        if self.eg.find_const(lhs) != self.eg.find_const(rhs) {
            return None;
        }
        Some(self.explain_eq_lits(lhs, rhs))
    }

    /// Deep-explain `a = b` and collect the assumption literals from the
    /// proof steps. `explain_deep` expands every congruence step into child
    /// explanations, so the collection is complete for ground EUF, where
    /// the only leaf justifications are assumptions.
    fn explain_eq_lits(&mut self, a: ENodeId, b: ENodeId) -> Vec<Lit> {
        self.buf.steps.clear();
        let ok = self.eg.explain_deep(a, b, &mut self.buf);
        debug_assert!(ok, "explain_eq_lits on unequal classes");
        let mut lits: Vec<Lit> = self
            .buf
            .steps
            .iter()
            .filter_map(|&(_, _, j)| match j {
                Justification::Assumption { lit } => Some(Lit::from_assumption(lit)),
                _ => None,
            })
            .collect();
        lits.sort_unstable();
        lits.dedup();
        lits
    }

    /// Open a backtracking scope. One token per SAT decision level.
    pub fn mark(&mut self) -> EufToken {
        EufToken {
            eg: self.eg.mark(ShrinkPolicy::Never),
            atoms_len: self.atoms.len(),
            trail_len: self.trail.len(),
        }
    }

    /// Rewind to `token`: undo the e-graph (merges, node creation, proof
    /// edges) via its semi-persistent restore, drop atoms created in the
    /// scope, and unassign literals asserted in it. Restoring to an
    /// ancestor token pops every deeper scope in one call — this is what
    /// makes non-chronological backjumping a single operation.
    pub fn restore(&mut self, token: EufToken) {
        self.eg.restore(token.eg);
        for dropped in self.atoms.drain(token.atoms_len..) {
            self.atom_of_node.remove(&dropped.node);
        }
        for &atom in &self.trail[token.trail_len..] {
            // Atoms above atoms_len were just drained with the suffix.
            if atom.to_usize() < token.atoms_len {
                self.atoms[atom.to_usize()].value = None;
            }
        }
        self.trail.truncate(token.trail_len);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use semi_persistent_egraph::model::MachineLit;

    type E = Euf<MachineLit>;

    fn lit(atom: AtomId, positive: bool) -> Lit {
        Lit::new(atom, positive)
    }

    #[test]
    fn lit_encoding_round_trips() {
        let a: AtomId = id::id_at(7);
        let l = lit(a, false);
        assert_eq!(l.atom(), a);
        assert!(!l.is_positive());
        assert_eq!(l.negated(), lit(a, true));
        assert_eq!(Lit::from_assumption(l.assumption()), l);
    }

    #[test]
    fn eq_atom_is_symmetric() {
        let mut e = E::new();
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        assert_eq!(e.eq_atom(a, b), e.eq_atom(b, a));
    }

    #[test]
    fn transitivity_conflict_names_all_antecedents() {
        let mut e = E::new();
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        let c = e.declare_const("c");
        let ab = e.eq_atom(a, b);
        let bc = e.eq_atom(b, c);
        let ac = e.eq_atom(a, c);
        e.assert_lit(lit(ab, true));
        e.assert_lit(lit(bc, true));
        e.assert_lit(lit(ac, false));
        match e.check() {
            CheckResult::Conflict(mut ls) => {
                ls.sort_unstable();
                let mut expected = vec![lit(ab, true), lit(bc, true), lit(ac, false)];
                expected.sort_unstable();
                assert_eq!(ls, expected);
            }
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    #[test]
    fn congruence_propagates_equality() {
        let mut e = E::new();
        let f = e.declare_fun("f", 1);
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        let fa = e.term(f, &[a]);
        let fb = e.term(f, &[b]);
        let ab = e.eq_atom(a, b);
        let fafb = e.eq_atom(fa, fb);
        e.assert_lit(lit(ab, true));
        match e.check() {
            CheckResult::Ok(props) => assert_eq!(props, vec![lit(fafb, true)]),
            other => panic!("expected propagation, got {other:?}"),
        }
        assert_eq!(e.explain_true_eq(fafb), Some(vec![lit(ab, true)]));
    }

    #[test]
    fn congruence_conflict_crosses_function_symbols() {
        let mut e = E::new();
        let f = e.declare_fun("f", 1);
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        let fa = e.term(f, &[a]);
        let fb = e.term(f, &[b]);
        let ab = e.eq_atom(a, b);
        let fafb = e.eq_atom(fa, fb);
        e.assert_lit(lit(ab, true));
        e.assert_lit(lit(fafb, false));
        match e.check() {
            CheckResult::Conflict(mut ls) => {
                ls.sort_unstable();
                let mut expected = vec![lit(ab, true), lit(fafb, false)];
                expected.sort_unstable();
                assert_eq!(ls, expected);
            }
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    #[test]
    fn restore_reopens_the_branch() {
        let mut e = E::new();
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        let c = e.declare_const("c");
        let ab = e.eq_atom(a, b);
        let bc = e.eq_atom(b, c);
        let ac = e.eq_atom(a, c);
        e.assert_lit(lit(ac, false));
        let level1 = e.mark();
        e.assert_lit(lit(ab, true));
        e.assert_lit(lit(bc, true));
        assert!(matches!(e.check(), CheckResult::Conflict(_)));
        e.restore(level1);
        // The merges and assignments from the popped scope are gone; the
        // base-level disequality survives.
        assert_eq!(e.value(ab), None);
        assert_eq!(e.value(bc), None);
        assert_eq!(e.value(ac), Some(false));
        assert_ne!(e.find(a), e.find(b));
        // The other branch is consistent.
        e.assert_lit(lit(ab, true));
        e.assert_lit(lit(bc, false));
        assert_eq!(e.check(), CheckResult::Ok(vec![]));
    }

    #[test]
    fn backjump_pops_multiple_levels_in_one_restore() {
        let mut e = E::new();
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        let c = e.declare_const("c");
        let d = e.declare_const("d");
        let ab = e.eq_atom(a, b);
        let bc = e.eq_atom(b, c);
        let cd = e.eq_atom(c, d);
        let level1 = e.mark();
        e.assert_lit(lit(ab, true));
        let _level2 = e.mark();
        e.assert_lit(lit(bc, true));
        let _level3 = e.mark();
        e.assert_lit(lit(cd, true));
        assert_eq!(e.find(a), e.find(d));
        // Non-chronological backjump: level 3 -> level 0 directly.
        e.restore(level1);
        for atom in [ab, bc, cd] {
            assert_eq!(e.value(atom), None);
        }
        assert_ne!(e.find(a), e.find(b));
        assert_ne!(e.find(b), e.find(c));
        assert_ne!(e.find(c), e.find(d));
    }

    #[test]
    fn atoms_created_in_scope_are_dropped_on_restore() {
        let mut e = E::new();
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        let base = e.mark();
        let ab = e.eq_atom(a, b);
        assert_eq!(ab.to_usize(), 0);
        e.restore(base);
        // The atom table and the node it referenced are both gone; a fresh
        // interning starts over cleanly.
        let ab2 = e.eq_atom(a, b);
        assert_eq!(ab2.to_usize(), 0);
        assert_eq!(e.value(ab2), None);
    }

    #[test]
    fn deep_congruence_explanation_reaches_leaf_assumptions() {
        // f(f(a)) = f(f(b)) must be explained by a = b through two
        // congruence expansions.
        let mut e = E::new();
        let f = e.declare_fun("f", 1);
        let a = e.declare_const("a");
        let b = e.declare_const("b");
        let fa = e.term(f, &[a]);
        let fb = e.term(f, &[b]);
        let ffa = e.term(f, &[fa]);
        let ffb = e.term(f, &[fb]);
        let ab = e.eq_atom(a, b);
        let top = e.eq_atom(ffa, ffb);
        e.assert_lit(lit(ab, true));
        match e.check() {
            CheckResult::Ok(props) => assert!(props.contains(&lit(top, true))),
            other => panic!("expected propagations, got {other:?}"),
        }
        assert_eq!(e.explain_true_eq(top), Some(vec![lit(ab, true)]));
    }
}
