// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable invariant checks for the AC reduced-basis (design §6b/§9a/§9b).
//!
//! These witness, at runtime, the properties the completion machinery is supposed to
//! maintain, so a diverging run can be inspected via `printf` to see *which* invariant
//! breaks. Investigation tooling, not production hot path: each function rescans all
//! nodes. See `doc/future/ac-congruence-completeness-plan.md` §0.4.
//!
//! The model: every active AC node (not `FLAG_SUBSUMED`, not `FLAG_AC_COLLAPSED`) whose
//! own monomial `M` is strictly `≫_f`-greater than its class's canonical summand form
//! `rhs` is a rule `+M → rhs`. The reduced-basis claims are:
//!  - **antichain**: no active rule's LHS is a sub-multiset of another's (collapse, §6b);
//!  - **irreducible**: no active rule's LHS is reducible by *another* active rule
//!    (equivalent phrasing of the antichain; the §6b property collapse must keep);
//!  - **ac_min consistency**: a non-atomic class's stored `ac_min` really is the
//!    `monomial_cmp`-least AC monomial among that class's nodes.

use crate::ac_multiset::{NfRule, monomial_cmp, multiset_subset, normalize_ms};
use crate::canon::{ACCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use crate::multiplicity::Multiplicity;
use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};
use crate::typed_routing::NodeRef;
use std::collections::BTreeMap;

/// One active AC rule, materialized for inspection.
pub struct BasisRule<G> {
    pub node: G,
    pub op: usize,
    pub lhs: Vec<(G, Multiplicity)>,
    pub rhs: Vec<(G, Multiplicity)>,
}

/// Result of checking the reduced-basis invariants on the current e-graph state.
pub struct BasisReport<G> {
    pub n_ac_nodes: usize,
    pub n_subsumed: usize,
    pub n_collapsed: usize,
    pub rules: Vec<BasisRule<G>>,
    /// Pairs (i, j) of `rules` indices where `rules[i].lhs ⊊ rules[j].lhs` and same op:
    /// `rules[j]` is reducible by `rules[i]`, so it should have been collapsed (§6b).
    /// Non-empty ⟹ the antichain/irreducible invariant is violated (collapse bug).
    pub reducible_pairs: Vec<(usize, usize)>,
    /// Distinct `rules` indices that are reducible (the `j` side of some pair): rules that
    /// inter-reduction would retire. `rules.len() - reducible_rule_count` is the antichain
    /// core (the true reduced-basis size in one collapse pass). A core far below the active
    /// count is the signature of a collapse-ordering bug, not an inherently large basis.
    pub reducible_rule_count: usize,
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Canonical child monomial (class-repr, mult) of an AC node, sorted + coalesced.
    /// Mirrors `ac_complete_round`'s `multiset_of`.
    fn ac_invariant_monomial(&self, id: Cfg::G) -> Vec<(Cfg::G, Multiplicity)> {
        let mut raw = Vec::new();
        self.ac_children(id, &mut raw);
        let mut m: Vec<(Cfg::G, Multiplicity)> = raw
            .into_iter()
            .map(|(g, mult)| (self.class_repr(g), Multiplicity(mult.into())))
            .collect();
        m.sort_by_key(|p| p.0);
        let mut out: Vec<(Cfg::G, Multiplicity)> = Vec::with_capacity(m.len());
        for (g, mult) in m {
            if let Some(last) = out.last_mut()
                && last.0 == g
            {
                last.1 = Multiplicity(last.1.0 + mult.0);
            } else {
                out.push((g, mult));
            }
        }
        out
    }

    /// The class's canonical summand form (the rule RHS): `{class}` if atomic, else the
    /// monomial of the stored `ac_min`. Mirrors `class_rhs_into`.
    fn ac_invariant_rhs(&self, id: Cfg::G) -> Vec<(Cfg::G, Multiplicity)> {
        let cls = self.class_repr(id);
        if self.class_ac_atomic(id) == Some(true) {
            vec![(cls, Multiplicity(1))]
        } else if let Some(min_node) = self.class_ac_min(id) {
            self.ac_invariant_monomial(min_node)
        } else {
            vec![(cls, Multiplicity(1))]
        }
    }

    /// Compute the current active AC rule set and check the reduced-basis invariants.
    /// Pure read; safe to call any time. Investigation tool (rescans all nodes).
    pub fn ac_basis_report(&self) -> BasisReport<Cfg::G> {
        let inactive = FLAG_SUBSUMED | FLAG_AC_COLLAPSED;
        let (mut n_ac_nodes, mut n_subsumed, mut n_collapsed) = (0usize, 0usize, 0usize);
        let mut rules: Vec<BasisRule<Cfg::G>> = Vec::new();

        for i in 0..self.node_count() {
            let gid = Cfg::G::from_usize(i);
            if !matches!(self.node_ref(gid), NodeRef::AC(_)) {
                continue;
            }
            n_ac_nodes += 1;
            let flags = self.node_flags(gid);
            if flags & FLAG_SUBSUMED != 0 {
                n_subsumed += 1;
            }
            if flags & FLAG_AC_COLLAPSED != 0 {
                n_collapsed += 1;
            }
            if flags & inactive != 0 {
                continue;
            }
            let lhs = self.ac_invariant_monomial(gid);
            let rhs = self.ac_invariant_rhs(gid);
            // A node is a rule iff its own monomial is strictly greater than its RHS.
            if monomial_cmp(&lhs, &rhs) == std::cmp::Ordering::Greater {
                rules.push(BasisRule {
                    node: gid,
                    op: self.node_op(gid).to_usize(),
                    lhs,
                    rhs,
                });
            }
        }

        // Reducible pairs: rules[i].lhs ⊊ rules[j].lhs, same op ⟹ j reducible by i.
        let mut reducible_pairs = Vec::new();
        for i in 0..rules.len() {
            for j in 0..rules.len() {
                if i == j || rules[i].op != rules[j].op {
                    continue;
                }
                if rules[i].lhs != rules[j].lhs && multiset_subset(&rules[i].lhs, &rules[j].lhs) {
                    reducible_pairs.push((i, j));
                }
            }
        }

        let mut reducible: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
        for &(_, j) in &reducible_pairs {
            reducible.insert(j);
        }
        let reducible_rule_count = reducible.len();

        BasisReport {
            n_ac_nodes,
            n_subsumed,
            n_collapsed,
            rules,
            reducible_pairs,
            reducible_rule_count,
        }
    }

    /// GROUND-TRUTH check 1: is the RHS each rule actually *uses* the true minimal monomial?
    ///
    /// `ac_basis_report` reads `rhs` exactly as completion does (`class_rhs_into`: `{class}`
    /// if atomic, else the stored `ac_min`). Here we instead brute-force, per (class, op),
    /// the `monomial_cmp`-least monomial over *all* active AC nodes of that op in the class,
    /// and compare. A mismatch means the RHS completion used was **not** minimal at the point
    /// of use (the §1.4 best-effort gap, or, more seriously, the single-op-slot conflating two
    /// AC ops, §9b axis-1). Returns the count of rules whose used RHS is non-minimal, and the
    /// worst offenders. Op-aware: the true min is taken only over same-op nodes.
    pub fn ac_min_used_nonminimal(&self) -> (usize, Vec<(Cfg::G, usize)>) {
        let inactive = FLAG_SUBSUMED | FLAG_AC_COLLAPSED;
        // Per (class repr, op): the true least same-op monomial among active AC nodes.
        let mut truemin: BTreeMap<(Cfg::G, usize), Vec<(Cfg::G, Multiplicity)>> = BTreeMap::new();
        for i in 0..self.node_count() {
            let gid = Cfg::G::from_usize(i);
            if !matches!(self.node_ref(gid), NodeRef::AC(_)) || self.node_flags(gid) & inactive != 0
            {
                continue;
            }
            let key = (self.class_repr(gid), self.node_op(gid).to_usize());
            let m = self.ac_invariant_monomial(gid);
            truemin
                .entry(key)
                .and_modify(|cur| {
                    if monomial_cmp(&m, cur) == std::cmp::Ordering::Less {
                        *cur = m.clone();
                    }
                })
                .or_insert(m);
        }
        // For every active rule, compare the RHS it would *use* to the true min of its op.
        let mut nonminimal = 0usize;
        let mut offenders: Vec<(Cfg::G, usize)> = Vec::new();
        for i in 0..self.node_count() {
            let gid = Cfg::G::from_usize(i);
            if !matches!(self.node_ref(gid), NodeRef::AC(_)) || self.node_flags(gid) & inactive != 0
            {
                continue;
            }
            let op = self.node_op(gid).to_usize();
            let lhs = self.ac_invariant_monomial(gid);
            let rhs = self.ac_invariant_rhs(gid);
            if monomial_cmp(&lhs, &rhs) != std::cmp::Ordering::Greater {
                continue; // not a rule
            }
            // The used RHS is non-minimal iff a strictly smaller same-op monomial exists in
            // the class AND the used RHS is not itself that minimum. `{class}` (atomic) is a
            // legitimately smaller representative, so only flag when the used RHS is the
            // `ac_min` monomial yet a smaller same-op node exists.
            if self.class_ac_atomic(gid) == Some(true) {
                continue; // RHS is `{class}`, the genuine size-1 minimum; not an ac_min question
            }
            if let Some(tm) = truemin.get(&(self.class_repr(gid), op))
                && monomial_cmp(tm, &rhs) == std::cmp::Ordering::Less
            {
                nonminimal += 1;
                offenders.push((gid, op));
            }
        }
        offenders.truncate(20);
        (nonminimal, offenders)
    }

    /// GROUND-TRUTH check 2: is the active rule set *fully reduced* in Kapur's sense (§3),
    /// not just a direct-containment antichain? Kapur-reduced: neither the LHS nor the RHS of
    /// any rule may be rewritten by the *other* rules. `reducible_pairs` only catches direct
    /// sub-multiset containment; this catches reducibility by multi-step normalization too.
    /// Returns (n_lhs_reducible, n_rhs_reducible): rules whose LHS / RHS is `normalize_ms`-
    /// reducible by the rest. Non-zero LHS count ⟹ not Kapur-reduced (collapse incomplete).
    pub fn ac_not_kapur_reduced(&self) -> (usize, usize) {
        let r = self.ac_basis_report();
        // Per op, the NfRule set (every rule except the one under test is the reducer set).
        let mut n_lhs = 0usize;
        let mut n_rhs = 0usize;
        for k in 0..r.rules.len() {
            let op = r.rules[k].op;
            let others: Vec<NfRule<Cfg::G>> = r
                .rules
                .iter()
                .enumerate()
                .filter(|(j, rj)| *j != k && rj.op == op)
                .map(|(_, rj)| NfRule {
                    lhs: rj.lhs.clone(),
                    rhs: rj.rhs.clone(),
                })
                .collect();
            if normalize_ms(&r.rules[k].lhs, &others) != r.rules[k].lhs {
                n_lhs += 1;
            }
            if normalize_ms(&r.rules[k].rhs, &others) != r.rules[k].rhs {
                n_rhs += 1;
            }
        }
        (n_lhs, n_rhs)
    }

    /// Print the basis report (one line per rule + the invariant verdicts). `tag` labels
    /// the call site (e.g. a round number). Investigation tool.
    pub fn ac_basis_dump(&self, tag: &str) {
        let r = self.ac_basis_report();
        let (nonmin, _) = self.ac_min_used_nonminimal();
        let (lhs_red, rhs_red) = self.ac_not_kapur_reduced();
        eprintln!(
            "[basis {tag}] ac_nodes={} subsumed={} collapsed={} active_rules={} reducible_pairs={} reducible_rules={} antichain_core={} | ac_min_used_nonminimal={nonmin} kapur_lhs_reducible={lhs_red} kapur_rhs_reducible={rhs_red}",
            r.n_ac_nodes,
            r.n_subsumed,
            r.n_collapsed,
            r.rules.len(),
            r.reducible_pairs.len(),
            r.reducible_rule_count,
            r.rules.len() - r.reducible_rule_count,
        );
        let show = |m: &[(Cfg::G, Multiplicity)]| -> String {
            let mut s = String::from("{");
            for (k, (g, mult)) in m.iter().enumerate() {
                if k > 0 {
                    s.push(',');
                }
                s.push_str(&format!("{}:{}", g.to_usize(), mult.0));
            }
            s.push('}');
            s
        };
        for (k, rule) in r.rules.iter().enumerate() {
            eprintln!(
                "[basis {tag}]   rule[{k}] node={} op={} lhs={} -> rhs={}",
                rule.node.to_usize(),
                rule.op,
                show(&rule.lhs),
                show(&rule.rhs),
            );
        }
        for &(i, j) in &r.reducible_pairs {
            eprintln!(
                "[basis {tag}]   !! REDUCIBLE: rule[{j}] (node {}) lhs {} contains rule[{i}] (node {}) lhs {} — should be collapsed",
                r.rules[j].node.to_usize(),
                show(&r.rules[j].lhs),
                r.rules[i].node.to_usize(),
                show(&r.rules[i].lhs),
            );
        }
    }
}
