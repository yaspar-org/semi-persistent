// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The semi-persistent e-graph: add, merge, find, rebuild, mark, restore.

use crate::canon::{ACCanon, VarCanon};
use crate::classes::EClasses;
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::containers::ShrinkPolicy;
use crate::literal::{LitVal, LitValStore, LitValStoreToken};
use crate::node_store::{Added, NodeStore, NodeStoreToken};
use crate::registry::{
    AxiomRegistry, AxiomRegistryToken, OpKind, OpRegistry, OpRegistryToken, RuleRegistry,
    RuleRegistryToken, SortRegistry, SortRegistryToken,
};
use crate::typed_routing::NodeRef;
use crate::union_find::{Justification, ProofBuf};

#[derive(Clone, Copy, Debug)]
pub struct EGraphToken {
    classes: crate::classes::EClassesToken,
    nodes: NodeStoreToken,
    sorts: SortRegistryToken,
    ops: OpRegistryToken,
    rules: RuleRegistryToken,
    axioms: AxiomRegistryToken,
    lits: LitValStoreToken,
}

pub struct EGraph<
    Cfg: EGraphConfig,
    L: LitVal,
    const TRACK: bool = true,
    const PROOFS: bool = false,
> {
    sorts: SortRegistry<Cfg::S, TRACK>,
    ops: OpRegistry<Cfg::O, Cfg::S, TRACK>,
    rules: RuleRegistry<TRACK>,
    axioms: AxiomRegistry<Cfg::G, TRACK>,
    lits: LitValStore<L, Cfg::V, TRACK>,
    classes: EClasses<Cfg::G, Cfg::UL, Cfg::UN, TRACK, PROOFS>,
    nodes: NodeStore<Cfg::G, Cfg::O, Cfg::V, Cfg::C, Cfg::Ids, TRACK, PROOFS>,
    worklist: Vec<(Cfg::UL, Cfg::G)>,
    collisions: Vec<(Cfg::G, Cfg::G)>,
    g_buf: Vec<Cfg::G>,
    ac_buf: Vec<Cfg::C>,
}

/// Type alias for the default 31-bit configuration.
pub type EGraph31<L, const TRACK: bool = true, const PROOFS: bool = false> =
    EGraph<crate::nodes::DefaultConfig, L, TRACK, PROOFS>;

/// Type alias for the 63-bit configuration.
pub type EGraph63<L, const TRACK: bool = true, const PROOFS: bool = false> =
    EGraph<crate::nodes::Config64, L, TRACK, PROOFS>;

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> Default
    for EGraph<Cfg, L, TRACK, PROOFS>
where
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pub fn new() -> Self {
        Self {
            sorts: SortRegistry::new(),
            ops: OpRegistry::new(),
            rules: RuleRegistry::new(),
            axioms: AxiomRegistry::new(),
            lits: LitValStore::new(),
            classes: EClasses::new(),
            nodes: NodeStore::new(),
            worklist: Vec::new(),
            collisions: Vec::new(),
            g_buf: Vec::new(),
            ac_buf: Vec::new(),
        }
    }

    /// Create an e-graph with built-in sorts and reserved op names from a `LitModel`.
    pub fn from_model(model: &impl crate::lit_model::LitModel<Value = L>) -> Self {
        let mut eg = Self::new();
        let sort_names: Vec<&str> = model.sorts().iter().map(|s| s.name).collect();
        eg.sorts.register_builtins(&sort_names);
        eg.ops.register_builtins(model, &eg.sorts);
        eg
    }

    /// Create an e-graph with pre-built registries (from sortcheck).
    pub fn with_registries(
        sorts: SortRegistry<Cfg::S, TRACK>,
        ops: OpRegistry<Cfg::O, Cfg::S, TRACK>,
    ) -> Self {
        let mut eg = Self::new();
        eg.sorts = sorts;
        eg.ops = ops;
        eg
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
    pub fn sorts(&self) -> &SortRegistry<Cfg::S, TRACK> {
        &self.sorts
    }
    pub fn sorts_mut(&mut self) -> &mut SortRegistry<Cfg::S, TRACK> {
        &mut self.sorts
    }
    pub fn ops(&self) -> &OpRegistry<Cfg::O, Cfg::S, TRACK> {
        &self.ops
    }

    pub fn ops_mut(&mut self) -> &mut OpRegistry<Cfg::O, Cfg::S, TRACK> {
        &mut self.ops
    }
    pub fn lits(&self) -> &LitValStore<L, Cfg::V, TRACK> {
        &self.lits
    }
    pub fn lits_mut(&mut self) -> &mut LitValStore<L, Cfg::V, TRACK> {
        &mut self.lits
    }

    pub fn rules(&self) -> &RuleRegistry<TRACK> {
        &self.rules
    }
    pub fn register_rule(&mut self, name: &str, lhs: &str, rhs: &str) -> crate::id::RuleId {
        self.rules.register(name, lhs, rhs)
    }

    pub fn axioms(&self) -> &AxiomRegistry<Cfg::G, TRACK> {
        &self.axioms
    }
    pub fn register_axiom(&mut self, name: &str, lhs: Cfg::G, rhs: Cfg::G) -> crate::id::AxiomId {
        self.axioms.register(name, lhs, rhs)
    }

    // Sorts
    pub fn intern_sort(&mut self, name: &str) -> Cfg::S {
        self.sorts.intern(name)
    }
    pub fn sort_name(&self, id: Cfg::S) -> &str {
        self.sorts.name(id)
    }

    pub fn register_op0(&mut self, name: &str, ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, &[], ret)
    }
    pub fn register_op1(&mut self, name: &str, a: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, &[a], ret)
    }
    pub fn register_op2(&mut self, name: &str, a: Cfg::S, b: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, &[a, b], ret)
    }
    pub fn register_op3(
        &mut self,
        name: &str,
        a: Cfg::S,
        b: Cfg::S,
        c: Cfg::S,
        ret: Cfg::S,
    ) -> Cfg::O {
        self.ops.register(name, &[a, b, c], ret)
    }
    pub fn register_opn(&mut self, name: &str, args: &[Cfg::S], ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, args, ret)
    }
    pub fn register_c(&mut self, name: &str, arg_sorts: [Cfg::S; 2], ret: Cfg::S) -> Cfg::O {
        self.ops.register_c(name, arg_sorts, ret)
    }
    pub fn register_a(
        &mut self,
        name: &str,
        arg: Cfg::S,
        ret: Cfg::S,
        dir: crate::registry::AssocDir,
    ) -> Cfg::O {
        self.ops.register_a(name, arg, ret, dir)
    }
    pub fn register_ac(&mut self, name: &str, arg: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register_ac(name, arg, ret)
    }
    pub fn register_aci(&mut self, name: &str, arg: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register_aci(name, arg, ret)
    }
    pub fn register_lit(&mut self, name: &str, ret: Cfg::S) -> Cfg::O {
        self.ops.register_lit(name, ret)
    }
    pub fn op(&self, name: &str) -> Option<Cfg::O> {
        self.ops.id_by_name(name)
    }
    pub fn intern_lit(&mut self, value: L) -> Cfg::V {
        self.lits.intern(value)
    }

    // ── Node operations ──

    /// Run a compiled query plan against this e-graph.
    pub fn run_query(
        &self,
        plan: &crate::schedule::QueryPlan<Cfg::O>,
    ) -> Vec<crate::ematch::Match<Cfg>> {
        let index = crate::index::IndexStore::build(self);
        let empty: crate::resolve::GlobalCtx<Cfg::S, Cfg::G> = crate::resolve::GlobalCtx::new();
        crate::ematch::run_query(plan, self, &index, &empty)
    }

    /// Saturate: apply rules to fixpoint or until `limit` iterations.
    pub fn saturate<M: crate::lit_model::LitModel<Value = L>, S: crate::DenseId + Copy>(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        limit: usize,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> crate::saturate::SatResult {
        crate::saturate::saturate(rules, self, model, limit, globals)
    }

    pub fn find(&mut self, x: Cfg::G) -> Cfg::G {
        self.classes.find(x)
    }

    pub fn find_const(&self, x: Cfg::G) -> Cfg::G {
        self.classes.find_const(x)
    }

    pub fn add(&mut self, op: Cfg::O, children: &[Cfg::G]) -> Cfg::G {
        #[cfg(debug_assertions)]
        {
            let info = self.ops.info(op);
            match &info.kind {
                OpKind::Normal { arg_sorts } => {
                    debug_assert_eq!(
                        children.len(),
                        arg_sorts.len(),
                        "operator '{}' expects {} children, got {}",
                        info.name,
                        arg_sorts.len(),
                        children.len()
                    );
                    for (i, (&c, &s)) in children.iter().zip(arg_sorts.iter()).enumerate() {
                        let got = self.node_sort(c);
                        debug_assert_eq!(
                            got,
                            s,
                            "operator '{}' expected sort '{}' at position {}, got '{}'",
                            info.name,
                            self.sorts.name(s),
                            i,
                            self.sorts.name(got)
                        );
                    }
                }
                OpKind::Commutative { arg_sorts } => {
                    debug_assert_eq!(
                        children.len(),
                        2,
                        "operator '{}' (commutative) expects 2 children, got {}",
                        info.name,
                        children.len()
                    );
                    for (i, (&c, &s)) in children.iter().zip(arg_sorts.iter()).enumerate() {
                        let got = self.node_sort(c);
                        debug_assert_eq!(
                            got,
                            s,
                            "operator '{}' expected sort '{}' at position {}, got '{}'",
                            info.name,
                            self.sorts.name(s),
                            i,
                            self.sorts.name(got)
                        );
                    }
                }
                OpKind::A { arg_sort, .. } | OpKind::AC { arg_sort } | OpKind::ACI { arg_sort } => {
                    for (i, &c) in children.iter().enumerate() {
                        let got = self.node_sort(c);
                        debug_assert_eq!(
                            got,
                            *arg_sort,
                            "operator '{}' expected sort '{}' at position {}, got '{}'",
                            info.name,
                            self.sorts.name(*arg_sort),
                            i,
                            self.sorts.name(got)
                        );
                    }
                }
                OpKind::Lit => {}
            }
        }
        self.g_buf.clear();
        self.g_buf
            .extend(children.iter().map(|&c| self.classes.find(c)));

        let result = match self.ops.info(op).kind {
            OpKind::AC { .. } => {
                self.g_buf.sort_by_key(|id| id.to_usize());
                self.ac_buf.clear();
                for &id in &self.g_buf {
                    if let Some(last) = self.ac_buf.last_mut()
                        && Cfg::ac_child_merge(last, id)
                    {
                        continue;
                    }
                    self.ac_buf.push(Cfg::ac_child_single(id));
                }
                self.nodes.add_ac(op, &self.ac_buf)
            }
            OpKind::ACI { .. } => {
                self.g_buf.sort_by_key(|id| id.to_usize());
                self.g_buf.dedup();
                self.nodes.add_aci(op, &self.g_buf)
            }
            _ => self.nodes.add(op, &self.g_buf, &self.ops),
        };

        let id = self.register_if_fresh(result);
        if result.is_fresh() {
            match self.ops.info(op).kind {
                OpKind::AC { .. } => {
                    for c in &self.ac_buf {
                        let child = Cfg::ac_child_id(c);
                        if let Some(repr) = self.classes.repr_id(child) {
                            self.classes.add_use(repr, id);
                        }
                    }
                }
                _ => {
                    for &child in &self.g_buf {
                        if let Some(repr) = self.classes.repr_id(child) {
                            self.classes.add_use(repr, id);
                        }
                    }
                }
            }
        }
        id
    }

    pub fn add_lit(&mut self, op: Cfg::O, lit: Cfg::V) -> Cfg::G {
        let result = self.nodes.add_lit(op, lit);
        self.register_if_fresh(result)
    }

    pub fn merge(&mut self, a: Cfg::G, b: Cfg::G) -> Option<(Cfg::G, Cfg::G)> {
        debug_assert_eq!(
            self.node_sort(a),
            self.node_sort(b),
            "cannot merge e-classes of different sorts: '{}' has sort '{}', '{}' has sort '{}'",
            self.node_op_name(a),
            self.sorts.name(self.node_sort(a)),
            self.node_op_name(b),
            self.sorts.name(self.node_sort(b))
        );
        debug_assert!(
            !self.sorts.is_concrete(self.node_sort(a)),
            "cannot merge concrete sort '{}' e-classes",
            self.sorts.name(self.node_sort(a))
        );
        let m = self.classes.merge(a, b)?;
        self.worklist.push((m.absorbed_uses, m.survivor));
        Some((m.survivor, m.absorbed))
    }

    pub fn merge_justified(
        &mut self,
        a: Cfg::G,
        b: Cfg::G,
        just: Justification<Cfg::G>,
    ) -> Option<(Cfg::G, Cfg::G)> {
        debug_assert_eq!(
            self.node_sort(a),
            self.node_sort(b),
            "cannot merge e-classes of different sorts: '{}' has sort '{}', '{}' has sort '{}'",
            self.node_op_name(a),
            self.sorts.name(self.node_sort(a)),
            self.node_op_name(b),
            self.sorts.name(self.node_sort(b))
        );
        debug_assert!(
            !self.sorts.is_concrete(self.node_sort(a)),
            "cannot merge concrete sort '{}' e-classes",
            self.sorts.name(self.node_sort(a))
        );
        let m = self.classes.merge_justified(a, b, just)?;
        self.worklist.push((m.absorbed_uses, m.survivor));
        Some((m.survivor, m.absorbed))
    }

    pub fn explain(&self, a: Cfg::G, b: Cfg::G, buf: &mut ProofBuf<Cfg::G>) -> bool {
        self.classes.explain(a, b, buf)
    }

    /// Deep explanation: expand Congruence justifications into child-pair proofs.
    /// Appends all steps (including recursive child explanations) to `buf.steps`.
    /// Uses an iterative worklist — no recursion.
    ///
    /// For C/AC/ACI nodes, children are matched by canonical representative
    /// (group-by-find), not by position. This avoids combinatorial search.
    pub fn explain_deep(&self, a: Cfg::G, b: Cfg::G, buf: &mut ProofBuf<Cfg::G>) -> bool {
        if !self.classes.explain(a, b, buf) {
            return false;
        }

        let mut ac_scratch: Vec<Cfg::C> = Vec::new();
        let mut i = 0;
        while i < buf.steps.len() {
            if let Justification::Congruence { node_a, node_b } = buf.steps[i].2 {
                buf.children_a.clear();
                buf.children_b.clear();
                self.collect_original_children(node_a, &mut buf.children_a, &mut ac_scratch);
                self.collect_original_children(node_b, &mut buf.children_b, &mut ac_scratch);

                let is_ordered = matches!(
                    self.node_ref(node_a),
                    NodeRef::Plain1(_)
                        | NodeRef::Plain2(_)
                        | NodeRef::Plain3(_)
                        | NodeRef::PlainN(_)
                        | NodeRef::A(_)
                );

                if is_ordered {
                    let n = buf.children_a.len().min(buf.children_b.len());
                    for j in 0..n {
                        let ca = buf.children_a[j];
                        let cb = buf.children_b[j];
                        if ca != cb && self.classes.find_const(ca) == self.classes.find_const(cb) {
                            self.classes.explain(ca, cb, buf);
                        }
                    }
                } else {
                    self.explain_grouped(buf);
                }
            }
            i += 1;
        }
        true
    }

    fn explain_grouped(&self, buf: &mut ProofBuf<Cfg::G>) {
        buf.group_a.clear();
        buf.group_a.extend_from_slice(&buf.children_a);
        buf.group_a
            .sort_by_key(|c| self.classes.find_const(*c).to_usize());

        buf.group_b.clear();
        buf.group_b.extend_from_slice(&buf.children_b);
        buf.group_b
            .sort_by_key(|c| self.classes.find_const(*c).to_usize());

        buf.children_a.clear();
        let mut ia = 0;
        let mut ib = 0;
        while ia < buf.group_a.len() && ib < buf.group_b.len() {
            let ra = self.classes.find_const(buf.group_a[ia]).to_usize();
            let rb = self.classes.find_const(buf.group_b[ib]).to_usize();
            if ra < rb {
                ia += 1;
            } else if ra > rb {
                ib += 1;
            } else {
                let ca = buf.group_a[ia];
                let cb = buf.group_b[ib];
                if ca != cb {
                    buf.children_a.push(ca);
                    buf.children_a.push(cb);
                }
                ia += 1;
                ib += 1;
            }
        }

        let mut k = 0;
        while k < buf.children_a.len() {
            let ca = buf.children_a[k];
            let cb = buf.children_a[k + 1];
            self.classes.explain(ca, cb, buf);
            k += 2;
        }
    }

    fn collect_original_children(
        &self,
        id: Cfg::G,
        out: &mut Vec<Cfg::G>,
        ac_scratch: &mut Vec<Cfg::C>,
    ) {
        ac_scratch.clear();
        if self.nodes.original_children(id, out, ac_scratch) {
            for c in ac_scratch.iter() {
                out.push(Cfg::ac_child_id(c));
            }
            return;
        }
        self.for_each_child(id, |child, _mult| out.push(child));
    }

    // -----------------------------------------------------------------------
    // Rebuild — worklist-based congruence closure
    // -----------------------------------------------------------------------

    pub fn rebuild(&mut self) {
        while let Some((absorbed_uses, survivor)) = self.worklist.pop() {
            self.collisions.clear();
            for parent in self.classes.uses().iter(absorbed_uses) {
                let find = |g: Cfg::G| self.classes.find_const(g);
                self.nodes.recanonize_node(
                    parent,
                    find,
                    &mut self.g_buf,
                    &mut self.ac_buf,
                    &mut self.collisions,
                );
            }

            let current_surv = self.classes.find_const(survivor);
            let surv_repr = self.classes.repr_id(current_surv).unwrap();
            let surv_list = self.classes.use_list_id(surv_repr);
            self.classes.splice_uses(surv_list, absorbed_uses);

            for i in 0..self.collisions.len() {
                let (a, b) = self.collisions[i];
                let m = if PROOFS {
                    self.classes.merge_justified(
                        a,
                        b,
                        Justification::Congruence {
                            node_a: a,
                            node_b: b,
                        },
                    )
                } else {
                    self.classes.merge(a, b)
                };
                if let Some(m) = m {
                    self.worklist.push((m.absorbed_uses, m.survivor));
                }
            }
        }
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> EGraphToken {
        self.rebuild();
        EGraphToken {
            classes: self.classes.mark(shrink),
            nodes: self.nodes.mark(shrink),
            sorts: self.sorts.mark(shrink),
            ops: self.ops.mark(shrink),
            rules: self.rules.mark(shrink),
            axioms: self.axioms.mark(shrink),
            lits: self.lits.mark(shrink),
        }
    }

    pub fn restore(&mut self, token: EGraphToken) {
        self.classes.restore(token.classes);
        self.nodes.restore(token.nodes);
        self.sorts.restore(token.sorts);
        self.ops.restore(token.ops);
        self.rules.restore(token.rules);
        self.axioms.restore(token.axioms);
        self.lits.restore(token.lits);
        self.worklist.clear();
        self.collisions.clear();
    }

    fn register_if_fresh(&mut self, result: Added<Cfg::G>) -> Cfg::G {
        if result.is_fresh() {
            self.classes.add_singleton(result.id());
        }
        result.id()
    }

    // -----------------------------------------------------------------------
    // Read-only inspection
    // -----------------------------------------------------------------------

    pub fn node_count(&self) -> usize {
        self.nodes.routing().len()
    }

    pub fn class_repr(&self, id: Cfg::G) -> Cfg::G {
        self.classes.find_const(id)
    }

    pub fn node_ref(&self, id: Cfg::G) -> NodeRef<Cfg::Ids> {
        self.nodes.routing().get(id)
    }

    pub fn node_op(&self, id: Cfg::G) -> Cfg::O {
        match self.node_ref(id) {
            NodeRef::Plain0(l) => self.nodes.plain0.get(l).op(),
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).op(),
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).op(),
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).op(),
            NodeRef::C(l) => self.nodes.c.get(l).op(),
            NodeRef::PlainN(l) => self.nodes.plain_n.get(l).op(),
            NodeRef::A(l) => self.nodes.a.get(l).op(),
            NodeRef::AC(l) => self.nodes.ac.get(l).op(),
            NodeRef::ACI(l) => self.nodes.aci.get(l).op(),
            NodeRef::Lit(l) => self.nodes.lit.get(l).op(),
        }
    }

    pub fn node_op_name(&self, id: Cfg::G) -> &str {
        &self.ops.info(self.node_op(id)).name
    }

    pub fn node_flags(&self, id: Cfg::G) -> u8 {
        match self.node_ref(id) {
            NodeRef::Plain0(l) => self.nodes.plain0.get(l).flags,
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).flags,
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).flags,
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).flags,
            NodeRef::C(l) => self.nodes.c.get(l).flags,
            NodeRef::PlainN(l) => self.nodes.plain_n.get(l).flags,
            NodeRef::A(l) => self.nodes.a.get(l).flags,
            NodeRef::AC(l) => self.nodes.ac.get(l).flags,
            NodeRef::ACI(l) => self.nodes.aci.get(l).flags,
            NodeRef::Lit(l) => self.nodes.lit.get(l).flags,
        }
    }

    pub fn subsume(&mut self, id: Cfg::G) {
        use crate::node_types::FLAG_SUBSUMED;
        macro_rules! flag {
            ($store:expr, $l:expr) => {{
                let mut n = $store.get($l);
                n.flags |= FLAG_SUBSUMED;
                $store.set($l, n);
            }};
        }
        match self.node_ref(id) {
            NodeRef::Plain0(l) => flag!(self.nodes.plain0, l),
            NodeRef::Plain1(l) => flag!(self.nodes.plain1, l),
            NodeRef::Plain2(l) => flag!(self.nodes.plain2, l),
            NodeRef::Plain3(l) => flag!(self.nodes.plain3, l),
            NodeRef::C(l) => flag!(self.nodes.c, l),
            NodeRef::PlainN(l) => flag!(self.nodes.plain_n, l),
            NodeRef::A(l) => flag!(self.nodes.a, l),
            NodeRef::AC(l) => flag!(self.nodes.ac, l),
            NodeRef::ACI(l) => flag!(self.nodes.aci, l),
            NodeRef::Lit(l) => flag!(self.nodes.lit, l),
        }
    }

    /// If `id` is a literal node, return its interned value. Otherwise `None`.
    pub fn get_lit_val(&self, id: Cfg::G) -> Option<&L> {
        if let NodeRef::Lit(l) = self.node_ref(id) {
            Some(self.lits.get(self.nodes.lit.get(l).lit))
        } else {
            None
        }
    }

    /// If `id` is a literal node, return its interned LitValId.
    pub fn get_lit_val_id(&self, id: Cfg::G) -> Option<Cfg::V> {
        if let NodeRef::Lit(l) = self.node_ref(id) {
            Some(self.nodes.lit.get(l).lit)
        } else {
            None
        }
    }

    /// Return sort of a node (from its operator's signature).
    pub fn node_sort(&self, id: Cfg::G) -> Cfg::S {
        self.ops.info(self.node_op(id)).return_sort
    }

    /// Debug: verify all nodes in each e-class have the same sort.
    /// Panics on violation. Only useful in tests / debug builds.
    pub fn debug_check_sort_invariant(&self) {
        use std::collections::HashMap;
        let mut class_sort: HashMap<Cfg::G, Cfg::S> = HashMap::new();
        for i in 0..self.len() {
            let gid = Cfg::G::from_usize(i);
            let repr = self.find_const(gid);
            let sort = self.node_sort(gid);
            if let Some(&existing) = class_sort.get(&repr) {
                assert_eq!(
                    existing,
                    sort,
                    "sort invariant violated: e-class of '{}' has sort {:?}, but '{}' has sort {:?}",
                    self.node_op_name(repr),
                    existing,
                    self.node_op_name(gid),
                    sort
                );
            } else {
                class_sort.insert(repr, sort);
            }
        }
    }

    pub fn for_each_child(&self, id: Cfg::G, mut f: impl FnMut(Cfg::G, u32)) -> usize {
        match self.node_ref(id) {
            NodeRef::Plain0(_) => 0,
            NodeRef::Plain1(l) => {
                for &c in &self.nodes.plain1.get(l).children {
                    f(c, 1);
                }
                1
            }
            NodeRef::Plain2(l) => {
                for &c in &self.nodes.plain2.get(l).children {
                    f(c, 1);
                }
                2
            }
            NodeRef::Plain3(l) => {
                for &c in &self.nodes.plain3.get(l).children {
                    f(c, 1);
                }
                3
            }
            NodeRef::C(l) => {
                for &c in &self.nodes.c.get(l).children {
                    f(c, 1);
                }
                2
            }
            NodeRef::PlainN(l) => {
                let n = self.nodes.plain_n.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.plain_n.pool_get(i), 1);
                }
                e - s
            }
            NodeRef::A(l) => {
                let n = self.nodes.a.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.a.pool_get(i), 1);
                }
                e - s
            }
            NodeRef::AC(l) => {
                let n = self.nodes.ac.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    let c = self.nodes.ac.pool_get(i);
                    f(Cfg::ac_child_id(&c), Cfg::ac_child_mult(&c).into());
                }
                e - s
            }
            NodeRef::ACI(l) => {
                let n = self.nodes.aci.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.aci.pool_get(i), 1);
                }
                e - s
            }
            NodeRef::Lit(_) => 0,
        }
    }

    /// Read the child at position `pos` from a fixed-arity node. O(1).
    /// Panics if `pos` is out of range or node is variadic/lit.
    pub fn child_at(&self, id: Cfg::G, pos: u32) -> Cfg::G {
        let p = pos as usize;
        match self.node_ref(id) {
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).children[p],
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).children[p],
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).children[p],
            NodeRef::C(l) => self.nodes.c.get(l).children[p],
            NodeRef::PlainN(l) => {
                let n = self.nodes.plain_n.get(l);
                let (s, _) = n.span();
                self.nodes.plain_n.pool_get(s + p)
            }
            NodeRef::A(l) => {
                let n = self.nodes.a.get(l);
                let (s, _) = n.span();
                self.nodes.a.pool_get(s + p)
            }
            _ => panic!("child_at: not a plain/sequence node or pos out of range"),
        }
    }

    /// Read AC children as `(id, multiplicity)` pairs into `buf`.
    pub fn ac_children(&self, id: Cfg::G, buf: &mut Vec<(Cfg::G, Cfg::M)>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::AC(l) => {
                let n = self.nodes.ac.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    let c = self.nodes.ac.pool_get(i);
                    buf.push((Cfg::ac_child_id(&c), Cfg::ac_child_mult(&c)));
                }
            }
            _ => panic!("ac_children: not an AC node"),
        }
    }

    /// Read ACI children (ids only, no multiplicities) into `buf`.
    pub fn aci_children(&self, id: Cfg::G, buf: &mut Vec<Cfg::G>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::ACI(l) => {
                let n = self.nodes.aci.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.aci.pool_get(i));
                }
            }
            _ => panic!("aci_children: not an ACI node"),
        }
    }

    /// Read A/PlainN children into `buf` in sequence order.
    pub fn seq_children(&self, id: Cfg::G, buf: &mut Vec<Cfg::G>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::PlainN(l) => {
                let n = self.nodes.plain_n.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.plain_n.pool_get(i));
                }
            }
            NodeRef::A(l) => {
                let n = self.nodes.a.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.a.pool_get(i));
                }
            }
            _ => panic!("seq_children: not a sequence node"),
        }
    }

    pub fn node_lit(&self, id: Cfg::G) -> Option<Cfg::V> {
        match self.node_ref(id) {
            NodeRef::Lit(l) => Some(self.nodes.lit.get(l).lit),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{OpId, SortId};
    use crate::lit_model::LitModel;
    use crate::literal::NiraLitVal;

    struct Th {
        int: SortId,
        x: OpId,
        y: OpId,
        z: OpId,
        w: OpId,
        f: OpId,
        g: OpId,
        h: OpId,
        eq: OpId,
        plus: OpId,
        and: OpId,
        sub: OpId,
        f4: OpId,
    }

    fn eg<const T: bool, const P: bool>() -> (EGraph31<NiraLitVal, T, P>, Th) {
        let mut eg = EGraph31::new();
        let int = eg.intern_sort("Int");
        let th = Th {
            int,
            x: eg.register_op0("x", int),
            y: eg.register_op0("y", int),
            z: eg.register_op0("z", int),
            w: eg.register_op0("w", int),
            f: eg.register_op1("f", int, int),
            g: eg.register_op2("g", int, int, int),
            h: eg.register_op3("h", int, int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            plus: eg.register_ac("plus", int, int),
            and: eg.register_aci("and", int, int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            f4: eg.register_opn("f4", &[int, int, int, int], int),
        };
        (eg, th)
    }

    #[test]
    fn congruence_plain() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);
        assert_ne!(eg.find(fx), eg.find(fy));
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
    }

    #[test]
    fn commutative_dedup() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        assert_eq!(eg.add(th.eq, &[x, y]), eg.add(th.eq, &[y, x]));
    }

    #[test]
    fn congruence_undone_by_restore() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
        eg.restore(token);
        assert_ne!(eg.find(fx), eg.find(fy));
    }

    #[test]
    fn cascading_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);
        let ffx = eg.add(th.f, &[fx]);
        let ffy = eg.add(th.f, &[fy]);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(ffx), eg.find(ffy));
    }

    #[test]
    fn ac_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let n1 = eg.add(th.plus, &[a, b]);
        let n2 = eg.add(th.plus, &[a, c]);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    #[test]
    fn aci_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let n1 = eg.add(th.and, &[a, b]);
        let n2 = eg.add(th.and, &[a, c]);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    #[test]
    fn aci_dedup_after_merge() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let ab = eg.add(th.and, &[a, b]);
        let aa = eg.add(th.and, &[a]);
        eg.merge(a, b);
        eg.rebuild();
        assert_eq!(eg.find(ab), eg.find(aa));
    }

    #[test]
    fn hashcons_dedup() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        assert_eq!(eg.add(th.f, &[x]), eg.add(th.f, &[x]));
        assert_eq!(eg.len(), 2);
    }

    #[test]
    fn add_canonicalizes() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        eg.merge(x, y);
        assert_eq!(fx, eg.add(th.f, &[y]));
    }

    #[test]
    fn rebuild_empty() {
        let (ref mut eg, _) = eg::<false, false>();
        eg.rebuild();
    }

    #[test]
    fn add_after_restore() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let token = eg.mark(ShrinkPolicy::Never);
        eg.add(th.f, &[x]);
        assert_eq!(eg.len(), 2);
        eg.restore(token);
        assert_eq!(eg.len(), 1);
        let gxx = eg.add(th.g, &[x, x]);
        assert_eq!(gxx, eg.add(th.g, &[x, x]));
    }

    #[test]
    fn rebuild_after_restore() {
        let (ref mut eg, th) = eg::<true, false>();
        let (x, y, z) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let (fx, fy, fz) = (eg.add(th.f, &[x]), eg.add(th.f, &[y]), eg.add(th.f, &[z]));
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
        eg.restore(token);
        assert_ne!(eg.find(fx), eg.find(fy));
        eg.merge(x, z);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fz));
        assert_ne!(eg.find(fx), eg.find(fy));
    }

    // -- Proofs --

    #[test]
    fn explain_non_equivalent() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let mut buf = ProofBuf::new();
        assert!(!eg.explain(x, y, &mut buf));
    }

    #[test]
    fn explain_axiom() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(42),
            },
        );
        let mut buf = ProofBuf::new();
        eg.explain(x, y, &mut buf);
        assert!(buf.steps.iter().any(|&(_, _, j)| j
            == Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(42)
            }));
    }

    #[test]
    fn explain_chain() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(1),
            },
        );
        eg.merge_justified(
            y,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(2),
            },
        );
        let mut buf = ProofBuf::new();
        eg.explain(x, z, &mut buf);
        for (from, to, just) in &buf.steps {
            eprintln!("  {:?} ≡ {:?}  by {:?}", from, to, just);
        }
        assert!(buf.steps.len() >= 2);
    }

    #[test]
    fn explain_after_restore() {
        let (ref mut eg, th) = eg::<true, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(0),
            },
        );
        let mut buf = ProofBuf::new();
        assert!(eg.explain(x, y, &mut buf));
        eg.restore(token);
        buf.clear();
        assert!(!eg.explain(x, y, &mut buf));
    }

    /// Regression: `union()` on a PROOFS=true UF must panic, not silently
    /// leave a stale justification.
    #[test]
    #[should_panic(expected = "union() called on a PROOFS=true UnionFind")]
    fn union_without_justification_panics_on_proofs() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        eg.merge(x, y); // must panic
    }

    /// Every step returned by `explain()` must carry the justification that
    /// was explicitly provided via `merge_justified`, never a stale default.
    #[test]
    fn explain_no_stale_justifications() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let ax1 = crate::id::AxiomId::new(10);
        let ax2 = crate::id::AxiomId::new(20);
        eg.merge_justified(x, y, Justification::Axiom { axiom_id: ax1 });
        eg.merge_justified(y, z, Justification::Axiom { axiom_id: ax2 });
        let mut buf = ProofBuf::new();
        eg.explain(x, z, &mut buf);
        for &(_, _, just) in &buf.steps {
            match just {
                Justification::Axiom { axiom_id } => {
                    assert!(
                        axiom_id == ax1 || axiom_id == ax2,
                        "unexpected axiom_id {axiom_id:?} in proof step"
                    );
                }
                Justification::Congruence { .. } => {}
                Justification::Rewrite { .. } => {}
            }
        }
    }

    // -- Rebuild coverage ---------------------------------------------------

    /// Plain3 congruence: h(x,y,z) ≡ h(w,y,z) after merge(x,w)
    #[test]
    fn congruence_plain3() {
        let (ref mut eg, th) = eg::<false, false>();
        let (x, y, z, w) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let n1 = eg.add(th.h, &[x, y, z]);
        let n2 = eg.add(th.h, &[w, y, z]);
        eg.merge(x, w);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// C-node congruence: eq(a,b) and eq(w,c) collide after merge(a,w), merge(b,c)
    #[test]
    fn commutative_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c, w) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let e1 = eg.add(th.eq, &[a, b]);
        let e2 = eg.add(th.eq, &[w, c]);
        eg.merge(a, w);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(e1), eg.find(e2));
    }

    /// C-node: find changes order but no collision (just reindex)
    #[test]
    fn commutative_reorder_no_collision() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
        let e = eg.add(th.eq, &[a, b]);
        eg.merge(a, b);
        eg.rebuild();
        let _ = eg.find(e);
    }

    /// PlainN congruence: f4(a,b,c,d) ≡ f4(a,e,c,d) after merge(b,e)
    #[test]
    fn plain_n_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let c = eg.add(th.z, &[]);
        let d = eg.add(th.w, &[]);
        let e_op = eg.register_op0("e", th.int);
        let e = eg.add(e_op, &[]);
        let n1 = eg.add(th.f4, &[a, b, c, d]);
        let n2 = eg.add(th.f4, &[a, e, c, d]);
        eg.merge(b, e);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// A-node congruence (associative, ordered)
    #[test]
    fn a_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let n1 = eg.add(th.sub, &[a, b]);
        let n2 = eg.add(th.sub, &[a, c]);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// AC: different multiplicities after merge → no false collision
    #[test]
    fn ac_multiplicity_no_false_collision() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c, d) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let n1 = eg.add(th.plus, &[a, b, c]); // plus(a,b,c)
        let n2 = eg.add(th.plus, &[a, d]); // plus(a,d)
        eg.merge(b, d);
        eg.merge(c, d);
        eg.rebuild();
        // n1 → plus(a,2*repr_d), n2 → plus(a,repr_d) — NOT equal
        assert_ne!(eg.find(n1), eg.find(n2));
    }

    /// AC shrink: plus(a,a,b) after merge(a,b) → plus((repr,3))
    #[test]
    fn ac_shrink_after_merge() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let n1 = eg.add(th.plus, &[a, a, b]); // plus((a,2),(b,1))
        let n2 = eg.add(th.plus, &[a, a, a]); // plus((a,3))
        eg.merge(a, b);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// Multiple merges before rebuild: worklist starts with >1 entry
    #[test]
    fn multiple_merges_before_rebuild() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c, d) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let fa = eg.add(th.f, &[a]);
        let fb = eg.add(th.f, &[b]);
        let fc = eg.add(th.f, &[c]);
        let fd = eg.add(th.f, &[d]);
        eg.merge(a, b);
        eg.merge(c, d);
        eg.rebuild();
        assert_eq!(eg.find(fa), eg.find(fb));
        assert_eq!(eg.find(fc), eg.find(fd));
        assert_ne!(eg.find(fa), eg.find(fc));
    }

    /// Diamond: g(a,b) uses both a and b; merge a and b
    #[test]
    fn diamond_fan_in() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
        let gab = eg.add(th.g, &[a, b]);
        eg.merge(a, b);
        eg.rebuild();
        let _ = eg.find(gab);
    }

    /// Fan-out: many parents of different kinds share the same child
    #[test]
    fn fan_out_many_parents() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let p0 = eg.add(th.f, &[a]);
        let p1 = eg.add(th.g, &[a, a]);
        let p2 = eg.add(th.eq, &[a, a]);
        let p3 = eg.add(th.plus, &[a, b]);
        let p4 = eg.add(th.and, &[a, b]);
        eg.merge(a, b);
        eg.rebuild();
        for &p in &[p0, p1, p2, p3, p4] {
            let _ = eg.find(p);
        }
    }

    /// Deep cascade: merge at leaf propagates through 4 levels
    #[test]
    fn deep_cascade_4_levels() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
        let fa = eg.add(th.f, &[a]);
        let fb = eg.add(th.f, &[b]);
        let ffa = eg.add(th.f, &[fa]);
        let ffb = eg.add(th.f, &[fb]);
        let fffa = eg.add(th.f, &[ffa]);
        let fffb = eg.add(th.f, &[ffb]);
        let ffffa = eg.add(th.f, &[fffa]);
        let ffffb = eg.add(th.f, &[fffb]);
        eg.merge(a, b);
        eg.rebuild();
        assert_eq!(eg.find(ffffa), eg.find(ffffb));
    }

    #[test]
    fn egraph63_smoke() {
        let mut eg = EGraph63::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);
        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let fx = eg.add(f, &[x]);
        let fy = eg.add(f, &[y]);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
    }

    #[test]
    fn from_model_registers_builtins() {
        use crate::literal::NiraModel;
        let model = NiraModel;
        let eg = EGraph31::<NiraLitVal, false, false>::from_model(&model);
        for sort_desc in model.sorts() {
            let id = eg.sorts().id_by_name(sort_desc.name).unwrap();
            assert!(
                eg.sorts().is_builtin(id),
                "sort '{}' should be builtin",
                sort_desc.name
            );
        }
        for op_desc in model.ops() {
            let id = eg.ops().id_by_name(op_desc.name).unwrap();
            assert!(
                eg.ops().is_builtin(id),
                "op '{}' should be builtin",
                op_desc.name
            );
        }
    }

    #[test]
    #[should_panic(expected = "already registered")]
    fn from_model_rejects_op_collision() {
        use crate::literal::NiraModel;
        let mut eg = EGraph31::<NiraLitVal, false, false>::from_model(&NiraModel);
        let int = eg.intern_sort("Int");
        // "+" is a builtin op from NiraModel, registering again should panic
        eg.register_op2("+", int, int, int);
    }
}

/// Run all core e-graph tests with both 31-bit and 63-bit configs.
#[cfg(test)]
mod dual_config_tests {
    use crate::canon::{ACCanon, VarCanon};
    use crate::config::EGraphConfig;
    use crate::containers::ShrinkPolicy;
    use crate::egraph::EGraph;
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};

    struct Th<Cfg: EGraphConfig> {
        x: Cfg::O,
        y: Cfg::O,
        z: Cfg::O,
        w: Cfg::O,
        f: Cfg::O,
        h: Cfg::O,
        eq: Cfg::O,
        plus: Cfg::O,
        and: Cfg::O,
        sub: Cfg::O,
        f4: Cfg::O,
        lit_op: Cfg::O,
    }

    fn setup<Cfg: EGraphConfig, const T: bool, const P: bool>()
    -> (EGraph<Cfg, NiraLitVal, T, P>, Th<Cfg>)
    where
        ACCanon: VarCanon<Cfg::G, Cfg::C>,
    {
        let mut eg = EGraph::new();
        let int = eg.intern_sort("Int");
        let th = Th {
            x: eg.register_op0("x", int),
            y: eg.register_op0("y", int),
            z: eg.register_op0("z", int),
            w: eg.register_op0("w", int),
            f: eg.register_op1("f", int, int),
            h: eg.register_op3("h", int, int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            plus: eg.register_ac("plus", int, int),
            and: eg.register_aci("and", int, int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            f4: eg.register_opn("f4", &[int, int, int, int], int),
            lit_op: eg.register_lit("lit", int),
        };
        (eg, th)
    }

    macro_rules! dual {
        ($(fn $name:ident<$Cfg:ident>() $body:block)*) => {$(
            mod $name {
                use super::*;
                fn run<$Cfg: EGraphConfig>() where ACCanon: VarCanon<$Cfg::G, $Cfg::C> $body
                #[test] fn bits31() { run::<crate::nodes::DefaultConfig>(); }
                #[test] fn bits63() { run::<crate::nodes::Config64>(); }
            }
        )*};
    }

    dual! {
        fn congruence_plain<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
        }

        fn commutative_dedup<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            assert_eq!(eg.add(th.eq, &[x, y]), eg.add(th.eq, &[y, x]));
        }

        fn cascading_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            let ffx = eg.add(th.f, &[fx]);
            let ffy = eg.add(th.f, &[fy]);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(ffx), eg.find(ffy));
        }

        fn ac_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let n1 = eg.add(th.plus, &[a, b]);
            let n2 = eg.add(th.plus, &[a, c]);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn aci_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let n1 = eg.add(th.and, &[a, b]);
            let n2 = eg.add(th.and, &[a, c]);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn aci_dedup_after_merge<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let a = eg.add(th.x, &[]);
            let b = eg.add(th.y, &[]);
            let ab = eg.add(th.and, &[a, b]);
            let aa = eg.add(th.and, &[a]);
            eg.merge(a, b);
            eg.rebuild();
            assert_eq!(eg.find(ab), eg.find(aa));
        }

        fn hashcons_dedup<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            assert_eq!(eg.add(th.f, &[x]), eg.add(th.f, &[x]));
            assert_eq!(eg.len(), 2);
        }

        fn add_canonicalizes<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            eg.merge(x, y);
            assert_eq!(fx, eg.add(th.f, &[y]));
        }

        fn congruence_undone_by_restore<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, true, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            let token = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            eg.restore(token);
            assert_ne!(eg.find(fx), eg.find(fy));
        }

        fn rebuild_after_restore<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, true, false>();
            let (x, y, z) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let (fx, fy, fz) = (eg.add(th.f, &[x]), eg.add(th.f, &[y]), eg.add(th.f, &[z]));
            let token = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            eg.restore(token);
            assert_ne!(eg.find(fx), eg.find(fy));
            eg.merge(x, z);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fz));
            assert_ne!(eg.find(fx), eg.find(fy));
        }

        fn congruence_plain3<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (x, y, z, w) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let n1 = eg.add(th.h, &[x, y, z]);
            let n2 = eg.add(th.h, &[w, y, z]);
            eg.merge(x, w);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn commutative_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c, w) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let e1 = eg.add(th.eq, &[a, b]);
            let e2 = eg.add(th.eq, &[w, c]);
            eg.merge(a, w);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(e1), eg.find(e2));
        }

        fn a_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let n1 = eg.add(th.sub, &[a, b]);
            let n2 = eg.add(th.sub, &[a, c]);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn ac_shrink_after_merge<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let a = eg.add(th.x, &[]);
            let b = eg.add(th.y, &[]);
            let n1 = eg.add(th.plus, &[a, a, b]);
            let n2 = eg.add(th.plus, &[a, a, a]);
            eg.merge(a, b);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn deep_cascade_4_levels<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
            let fa = eg.add(th.f, &[a]);
            let fb = eg.add(th.f, &[b]);
            let ffa = eg.add(th.f, &[fa]);
            let ffb = eg.add(th.f, &[fb]);
            let fffa = eg.add(th.f, &[ffa]);
            let fffb = eg.add(th.f, &[ffb]);
            let ffffa = eg.add(th.f, &[fffa]);
            let ffffb = eg.add(th.f, &[fffb]);
            eg.merge(a, b);
            eg.rebuild();
            assert_eq!(eg.find(ffffa), eg.find(ffffb));
        }

        fn multiple_merges_before_rebuild<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c, d) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let fa = eg.add(th.f, &[a]);
            let fb = eg.add(th.f, &[b]);
            let fc = eg.add(th.f, &[c]);
            let fd = eg.add(th.f, &[d]);
            eg.merge(a, b);
            eg.merge(c, d);
            eg.rebuild();
            assert_eq!(eg.find(fa), eg.find(fb));
            assert_eq!(eg.find(fc), eg.find(fd));
            assert_ne!(eg.find(fa), eg.find(fc));
        }

        fn explain_proof<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, true>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let z = eg.add(th.z, &[]);
            eg.merge_justified(x, y, Justification::Axiom { axiom_id: crate::id::AxiomId::new(1) });
            eg.merge_justified(y, z, Justification::Axiom { axiom_id: crate::id::AxiomId::new(2) });
            let mut buf = ProofBuf::new();
            eg.explain(x, z, &mut buf);
            assert!(buf.steps.len() >= 2);
        }

        fn explain_deep_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, true>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            eg.merge_justified(x, y, Justification::Axiom { axiom_id: crate::id::AxiomId::new(10) });
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            let mut buf = ProofBuf::new();
            assert!(eg.explain_deep(fx, fy, &mut buf));
            assert!(buf.steps.iter().any(|(_, _, j)| matches!(j, Justification::Congruence { .. })));
            assert!(buf.steps.iter().any(|(_, _, j)| *j == Justification::Axiom { axiom_id: crate::id::AxiomId::new(10) }));
        }

        fn plain_n_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (x, y, z, w) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let n1 = eg.add(th.f4, &[x, y, z, w]);
            let n2 = eg.add(th.f4, &[x, y, z, x]);
            eg.merge(w, x);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn a_not_commutative<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
            let ab = eg.add(th.sub, &[a, b]);
            let ba = eg.add(th.sub, &[b, a]);
            assert_ne!(eg.find(ab), eg.find(ba));
        }

        fn lit_node<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            use crate::literal::NiraLitVal;
            use num_bigint::BigInt;
            let v1 = eg.intern_lit(NiraLitVal::Int(BigInt::from(42)));
            let v2 = eg.intern_lit(NiraLitVal::Int(BigInt::from(42)));
            assert_eq!(v1, v2);
            let n1 = eg.add_lit(th.lit_op, v1);
            let n2 = eg.add_lit(th.lit_op, v1);
            assert_eq!(n1, n2);
            let v3 = eg.intern_lit(NiraLitVal::Int(BigInt::from(99)));
            let n3 = eg.add_lit(th.lit_op, v3);
            assert_ne!(n1, n3);
        }

        fn is_empty_check<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            // setup registers ops which add nodes, but is_empty checks node count
            let before = eg.len();
            let x = eg.add(th.x, &[]);
            assert_eq!(eg.len(), before + 1);
            let _ = x;
        }

        fn nested_mark_restore<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, true, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let z = eg.add(th.z, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            let fz = eg.add(th.f, &[z]);
            let t1 = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            let t2 = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, z);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fz));
            eg.restore(t2);
            assert_eq!(eg.find(fx), eg.find(fy));
            assert_ne!(eg.find(fx), eg.find(fz));
            eg.restore(t1);
            assert_ne!(eg.find(fx), eg.find(fy));
            assert_ne!(eg.find(fx), eg.find(fz));
        }
    }
}
