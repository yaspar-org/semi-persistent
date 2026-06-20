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
    /// Semi-naive touched log: node ids created or recanonicalized since the
    /// last `clear_touched`. Round-local scratch (cleared on `restore`);
    /// drives the per-round delta index. Not part of persistent state.
    touched: Vec<Cfg::G>,
    /// Whether `rebuild` runs the AC congruence-completion pass (superposition +
    /// inter-reduction). **Default off**: completion can materialize nested same-op
    /// nodes, which the matcher cannot handle until AC flattening lands (`WF_flat`,
    /// see `doc/design/ac-congruence-completeness.md` §6b). Opt in with
    /// [`set_ac_complete`](Self::set_ac_complete) once flattening is in place; the
    /// completion tests enable it for the flat scenarios they exercise.
    ac_complete: bool,
    /// Reusable scratch for comparing two nodes' AC monomials (`monomial_cmp` on the
    /// per-class `ac_min`, §9a). Two buffers to hold both sides without aliasing;
    /// cleared and refilled per comparison, never grown per merge.
    cmp_buf_a: Vec<(Cfg::G, crate::multiplicity::Multiplicity)>,
    cmp_buf_b: Vec<(Cfg::G, crate::multiplicity::Multiplicity)>,
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
            touched: Vec::new(),
            ac_complete: false,
            cmp_buf_a: Vec::new(),
            cmp_buf_b: Vec::new(),
        }
    }

    /// Enable or disable the AC congruence-completion pass in `rebuild` (default off).
    /// Off until nested same-op flattening lands — see `ac_complete` field docs.
    pub fn set_ac_complete(&mut self, enabled: bool) {
        self.ac_complete = enabled;
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
        let vindex = crate::index::VariantIndex::naive(&index);
        let empty: crate::resolve::GlobalCtx<Cfg::S, Cfg::G> = crate::resolve::GlobalCtx::new();
        crate::ematch::run_query(plan, self, &vindex, &empty)
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

    /// Semi-naive saturation (each round matches only what changed). No
    /// automatic fallback to the naive path.
    pub fn saturate_semi<M: crate::lit_model::LitModel<Value = L>, S: crate::DenseId + Copy>(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        limit: usize,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> crate::saturate::SatResult {
        crate::saturate::saturate_semi(rules, self, model, limit, globals)
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

    /// Fill `buf` with `node`'s monomial for `monomial_cmp`: its canonical AC child
    /// multiset if it is an AC node, else the singleton `{node}` (a non-AC node is a
    /// size-1 monomial, §9b). Children are `find`-canonicalized and coalesced.
    fn node_monomial_into(
        &self,
        node: Cfg::G,
        buf: &mut Vec<(Cfg::G, crate::multiplicity::Multiplicity)>,
    ) {
        use crate::multiplicity::Multiplicity;
        buf.clear();
        if matches!(self.node_ref(node), NodeRef::AC(_)) {
            // ac_children, find-canonicalized + coalesced (same form as ACCanon).
            let mut raw = Vec::new();
            self.ac_children(node, &mut raw);
            let mut m: Vec<(Cfg::G, Multiplicity)> = raw
                .into_iter()
                .map(|(g, mult)| (self.classes.find_const(g), Multiplicity(mult.into())))
                .collect();
            m.sort_by_key(|p| p.0);
            for (g, mult) in m {
                if let Some(last) = buf.last_mut()
                    && last.0 == g
                {
                    last.1 = Multiplicity(last.1.0 + mult.0);
                } else {
                    buf.push((g, mult));
                }
            }
        } else {
            buf.push((self.classes.find_const(node), Multiplicity(1)));
        }
    }

    /// Fill `buf` with the completion rule right-hand side for the class of `node`: the
    /// size-1 monomial `{find(node)}` if the class is `atomic` (referenced as a child),
    /// else the monomial of the class's stored `ac_min` (§9a). Reads the per-class slot;
    /// O(1) plus the `ac_min` monomial read. Returns `false` if `node` has no class.
    fn class_rhs_into(
        &self,
        node: Cfg::G,
        buf: &mut Vec<(Cfg::G, crate::multiplicity::Multiplicity)>,
    ) -> bool {
        use crate::multiplicity::Multiplicity;
        let cls = self.classes.find_const(node);
        let Some(repr) = self.classes.repr_id(cls) else {
            return false;
        };
        if self.classes.ac_atomic(repr) {
            buf.clear();
            buf.push((cls, Multiplicity(1)));
        } else {
            self.node_monomial_into(self.classes.ac_min(repr), buf);
        }
        true
    }

    /// After a merge, fold the absorbed class's per-class AC data into the survivor's:
    /// keep the `monomial_cmp`-least `ac_min` node, and OR-in the `atomic` flag (the
    /// completion rule RHS, §9a). O(1) plus the two monomial reads, into reusable
    /// buffers. Done here, not in `EClasses`, because the comparison needs node
    /// (AC-children) access. Best-effort under merge-cascade staleness; completion's
    /// read-time orientation guard makes that safe (§9b).
    fn fold_ac_class(&mut self, survivor: Cfg::G, absorbed_ac_min: Cfg::G, absorbed_atomic: bool) {
        let surv_repr = match self.classes.repr_id(self.classes.find_const(survivor)) {
            Some(r) => r,
            None => return,
        };
        if absorbed_atomic {
            self.classes.set_ac_atomic(surv_repr);
        }
        let surv_min = self.classes.ac_min(surv_repr);
        if surv_min == absorbed_ac_min {
            return;
        }
        // Compare the two candidate minima; keep the smaller in degree-lex order.
        let mut a = std::mem::take(&mut self.cmp_buf_a);
        let mut b = std::mem::take(&mut self.cmp_buf_b);
        self.node_monomial_into(surv_min, &mut a);
        self.node_monomial_into(absorbed_ac_min, &mut b);
        if crate::ac_multiset::monomial_cmp(&b, &a) == std::cmp::Ordering::Less {
            self.classes.set_ac_min(surv_repr, absorbed_ac_min);
        }
        self.cmp_buf_a = a;
        self.cmp_buf_b = b;
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
        self.fold_ac_class(m.survivor, m.absorbed_ac_min, m.absorbed_atomic);
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
        self.fold_ac_class(m.survivor, m.absorbed_ac_min, m.absorbed_atomic);
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

    /// Rebuild to a congruence-closed, AC-congruence-closed fixpoint.
    ///
    /// Two interleaved closures run to a joint fixpoint (see
    /// `doc/future/ac-congruence-completeness-plan.md` §2, Option A):
    /// - [`rebuild_congruence`](Self::rebuild_congruence): ordinary worklist-driven
    ///   congruence closure (substitutes equal *atoms* into recanonicalized nodes);
    /// - [`ac_complete_round`](Self::ac_complete_round): AC completion (substitutes
    ///   equal *sub-sums*), which canonization alone misses.
    ///
    /// A completion round may push new merges onto the worklist; we drain them with
    /// another congruence pass, then complete again, until a whole completion round
    /// adds nothing. The fixpoint is the AC congruence closure of the asserted
    /// equalities.
    pub fn rebuild(&mut self) {
        // Ordinary atom-level congruence closure always runs. AC completion runs only
        // when opted in (default off until nested same-op flattening lands — §6b).
        if !self.ac_complete {
            self.rebuild_congruence();
            return;
        }
        let trace = std::env::var_os("AC_COMPLETE_TRACE").is_some();
        // Safety backstop against a diverging completion (minting unbounded
        // critical-pair nodes). A convergent completion adds few nodes; if the AC
        // node count balloons past this many beyond where it started, we stop
        // rather than OOM. This is NOT the termination argument — it is a guard
        // rail while the proper inter-reduction is being put in place.
        const MAX_COMPLETION_NODE_GROWTH: usize = 50_000;
        let start_nodes = self.node_count();
        let mut round = 0usize;
        loop {
            self.rebuild_congruence();
            let before = self.node_count();
            let changed = self.ac_complete_round();
            if trace {
                eprintln!(
                    "[ac-complete] round {round}: nodes {before} -> {} (+{}), changed={changed}",
                    self.node_count(),
                    self.node_count() - before
                );
            }
            round += 1;
            if !changed {
                return;
            }
            if self.node_count() - start_nodes > MAX_COMPLETION_NODE_GROWTH {
                self.rebuild_congruence();
                debug_assert!(
                    false,
                    "ac completion diverged: added >{MAX_COMPLETION_NODE_GROWTH} nodes \
                     without converging (set AC_COMPLETE_TRACE=1 to inspect growth)"
                );
                return;
            }
        }
    }

    /// Ordinary worklist-driven congruence closure: drain the merge worklist,
    /// recanonicalizing the parents of each absorbed class and merging the
    /// resulting hash-cons collisions, to a fixpoint.
    fn rebuild_congruence(&mut self) {
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
                    &mut self.touched,
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
                    self.fold_ac_class(m.survivor, m.absorbed_ac_min, m.absorbed_atomic);
                    self.worklist.push((m.absorbed_uses, m.survivor));
                }
            }
        }
    }

    /// One AC congruence-completion round (Kapur FSCD 2021 Algorithm 1, the steps our
    /// rebuild otherwise omits). Returns `true` if it scheduled any new merge.
    ///
    /// Reading each non-subsumed AC node `+M = d` as a ground rule `+M → d`, over a
    /// frozen snapshot of the active AC nodes
    /// ([`crate::ac_complete::AcPartnerSnapshot`]), for each pair of partners (same op,
    /// sharing ≥1 child class):
    ///
    /// - **(A) inter-reduction + Collapse** — if `A ⊊ M`, the sub-sum `+A` equals `a`,
    ///   so the residual `(M − A) ⊎ {a}`, **normalized to a fixpoint**, equals `d`:
    ///   merge, then **mark `+M` subsumed** so it leaves the active set. The collapse
    ///   is what keeps the active rule LHSs a Dickson antichain — without it completion
    ///   diverges (design doc §6b).
    /// - **(B) superposition** — if `A` and `M` overlap but neither contains the other,
    ///   build the lcm `AB`, **normalize both reducts** `(AB−M)⊎{d}` and `(AB−A)⊎{a}`
    ///   to normal form, and merge if they still differ (design doc §4b, §6 (B)).
    ///
    /// Disjoint partners are skipped (trivial critical pair). The crucial corrections
    /// over a naïve materialize-and-merge (design §6b): every reduct is reduced to
    /// **normal form before** being materialized (a raw reduct can be a superset of an
    /// existing rule's LHS, hence itself reducible, and would persist as a runaway
    /// superposition source), and reducible source rules are **collapsed** (subsumed).
    ///
    /// "Subsumed" is the non-deletable form of Kapur/Conchon's rule retirement: the
    /// node and the equality it established stay in the DAG (sound, restorable), but the
    /// snapshot/index builders skip it, so it is no longer a partner or a match target.
    fn ac_complete_round(&mut self) -> bool {
        use crate::ac_multiset::{
            NfRule, multiset_disjoint, multiset_lcm, multiset_subset, normalize_ms,
        };
        use crate::multiplicity::Multiplicity;

        // Canonical child multiset of an AC node as sorted, coalesced (class-repr, mult).
        let multiset_of = |eg: &Self, id: Cfg::G| -> Vec<(Cfg::G, Multiplicity)> {
            let mut raw = Vec::new();
            eg.ac_children(id, &mut raw);
            let mut m: Vec<(Cfg::G, Multiplicity)> = raw
                .into_iter()
                .map(|(g, mult)| (eg.classes.find_const(g), Multiplicity(mult.into())))
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
        };

        use crate::ac_multiset::monomial_cmp;
        use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};

        // Completion's active set excludes nodes that are user-subsumed (not matchable)
        // OR AC-collapsed (reducible by a smaller rule). Either way they are not rules.
        let inactive = FLAG_SUBSUMED | FLAG_AC_COLLAPSED;

        // Each active AC node is a candidate rule `+M → rhs(class)`, where the RHS comes
        // from the per-class slot (`class_rhs_into`: `{class}` if atomic, else the stored
        // `ac_min` monomial, §9a) — not recomputed per round. The orientation guard keeps
        // only nodes whose own monomial `M` is strictly `≫_f`-greater than that RHS: those
        // are the genuine rules (a node equal to its class's normal form is no rule, and a
        // mis-oriented `M ≺ rhs` is dropped, §9b axis-2a). `node` lets us collapse it.
        struct Rule<G> {
            op: usize,
            lhs: Vec<(G, Multiplicity)>,
            rhs: Vec<(G, Multiplicity)>,
            node: G,
        }
        let mut rules: Vec<Rule<Cfg::G>> = Vec::new();
        let mut rhs_buf: Vec<(Cfg::G, Multiplicity)> = Vec::new();
        for i in 0..self.node_count() {
            let gid = Cfg::G::from_usize(i);
            if self.node_flags(gid) & inactive != 0 {
                continue;
            }
            let op = self.node_op(gid);
            if !self.ops.is_ac(op) {
                continue;
            }
            let lhs = multiset_of(self, gid);
            if !self.class_rhs_into(gid, &mut rhs_buf) {
                continue;
            }
            // Read-time orientation guard (§9b): only `M ≫ rhs` is a rule.
            if monomial_cmp(&lhs, &rhs_buf) == std::cmp::Ordering::Greater {
                rules.push(Rule {
                    op: op.to_usize(),
                    lhs,
                    rhs: rhs_buf.clone(),
                    node: gid,
                });
            }
        }
        // Built in ascending node-id order, so `rules` is sorted by `node`. The (B)
        // partner search binary-searches it by node id; keep that invariant true.
        debug_assert!(rules.windows(2).all(|w| w[0].node < w[1].node));

        // Expand a multiset to a flat child list; `add` re-sorts and re-coalesces.
        let materialize = |eg: &mut Self, op: Cfg::O, ms: &[(Cfg::G, Multiplicity)]| -> Cfg::G {
            let mut children: Vec<Cfg::G> = Vec::new();
            for (g, mult) in ms {
                for _ in 0..mult.0 {
                    children.push(*g);
                }
            }
            eg.add(op, &children)
        };
        let do_merge = |eg: &mut Self, x: Cfg::G, y: Cfg::G| -> bool {
            if eg.classes.find_const(x) == eg.classes.find_const(y) {
                return false;
            }
            let m = if PROOFS {
                eg.classes.merge_justified(
                    x,
                    y,
                    Justification::Congruence {
                        node_a: x,
                        node_b: y,
                    },
                )
            } else {
                eg.classes.merge(x, y)
            };
            match m {
                Some(m) => {
                    eg.fold_ac_class(m.survivor, m.absorbed_ac_min, m.absorbed_atomic);
                    eg.worklist.push((m.absorbed_uses, m.survivor));
                    true
                }
                None => false,
            }
        };

        // Collect work over pairs of rules (same op), then apply (so the rule set we
        // normalize against does not shift mid-scan). Superposition (B) and collapse (A)
        // both range over *rules*: Kapur superposes/inter-reduces rule left sides, and a
        // class's minimal monomial (a normal form) is never a rule, so it cannot be a
        // source or a collapse target. The search ranges over the `rules` Vec directly
        // (already the small active set), via an all-pairs loop.
        //   targets — (A): collapse a node's class into its residual's normal form.
        //   crit    — (B): merge the normal forms of the two lcm reducts.
        let mut crit: Vec<(
            Cfg::O,
            Vec<(Cfg::G, Multiplicity)>,
            Vec<(Cfg::G, Multiplicity)>,
        )> = Vec::new();

        // (A′) Normalize every active monomial node against the rules and merge its
        // normal form back in (Kapur Algo 2 step 2, "normalize Sf"). This subsumes plain
        // inter-reduction (A): a node +{a,b,neg(c)} with rule +{a,b}→{c} reduces to
        // +{c,neg(c)}, which is *materialized* so the ordinary matcher reaches it
        // (design §5b). `(op, monomial, class, node, is_rule)`: a node that was itself a
        // rule (its own LHS reducible) is collapsed/subsumed after the merge (design §6b).
        let mut targets: Vec<(Cfg::O, Vec<(Cfg::G, Multiplicity)>, Cfg::G, Cfg::G, bool)> =
            Vec::new();
        for i in 0..self.node_count() {
            let gid = Cfg::G::from_usize(i);
            if self.node_flags(gid) & inactive != 0 {
                continue;
            }
            let op = self.node_op(gid);
            if !self.ops.is_ac(op) {
                continue;
            }
            targets.push((
                op,
                multiset_of(self, gid),
                self.classes.find_const(gid),
                gid,
                rules.iter().any(|r| r.node == gid),
            ));
        }

        // (B) Superposition critical pairs over pairs of *rules* sharing ≥1 child class,
        // neither containing the other (overlap). Partners are found via the use-lists
        // (`iter_uses`), not an O(rules²) all-pairs scan: a partner of rule `+M` must
        // share a child with `M`, so it appears in some `iter_uses(x)` for `x ∈ M`. `rules`
        // is built in node-id order, so it is sorted by `node`; look a partner's rule up by
        // binary search (no map, no per-round allocation). Each unordered pair is processed
        // once (`ti.node < partner.node`). Both reducts are normalized before merge.
        let mut partner_buf: Vec<Cfg::G> = Vec::new();
        for ti in 0..rules.len() {
            let op_u = rules[ti].op;
            let op = Cfg::O::from_usize(op_u);
            let m_node = rules[ti].node;

            // Gather candidate partner nodes from the use-lists of M's distinct children.
            partner_buf.clear();
            for &(x, _) in &rules[ti].lhs {
                if let Some(x_repr) = self.classes.repr_id(self.classes.find_const(x)) {
                    for p in self.classes.iter_uses(x_repr) {
                        partner_buf.push(p);
                    }
                }
            }
            partner_buf.sort_unstable();
            partner_buf.dedup();

            for k in 0..partner_buf.len() {
                let p_node = partner_buf[k];
                // Process each unordered pair once; skip self.
                if p_node <= m_node {
                    continue;
                }
                if self.node_flags(p_node) & inactive != 0 || self.node_op(p_node) != op {
                    continue;
                }
                // The partner must itself be a rule: binary-search the sorted `rules`.
                let Ok(pi) = rules.binary_search_by(|r| r.node.cmp(&p_node)) else {
                    continue;
                };
                let m = &rules[ti].lhs;
                let a = &rules[pi].lhs;
                // Shared by construction; skip the non-overlap / containment cases
                // (containment is handled by the (A′) normalize pass).
                debug_assert!(!multiset_disjoint(a, m));
                if multiset_subset(a, m) || multiset_subset(m, a) {
                    continue;
                }
                let ab = multiset_lcm(m, a);
                let r1 = crate::ac_multiset::multiset_union(
                    &crate::ac_multiset::multiset_subtract(&ab, m),
                    &rules[ti].rhs,
                );
                let r2 = crate::ac_multiset::multiset_union(
                    &crate::ac_multiset::multiset_subtract(&ab, a),
                    &rules[pi].rhs,
                );
                crit.push((op, r1, r2));
            }
        }

        // Per-op rewrite rules for normalization. `nf` reduces a multiset to normal
        // form against these (rewrite by any LHS ⊆ current, substitute its monomial RHS,
        // to a fixpoint), then materializes the NORMAL FORM. Each step strictly lowers
        // the multiset in degree-lex order, so it terminates; only the irreducible result
        // becomes a node — this is what stops the runaway (design §6b).
        let nf = |eg: &mut Self,
                  op: Cfg::O,
                  ms: &[(Cfg::G, Multiplicity)],
                  rules: &[Rule<Cfg::G>]|
         -> Cfg::G {
            let nf_rules: Vec<NfRule<Cfg::G>> = rules
                .iter()
                .filter(|r| r.op == op.to_usize())
                .map(|r| NfRule {
                    lhs: r.lhs.clone(),
                    rhs: r.rhs.clone(),
                })
                .collect();
            let normal = normalize_ms(ms, &nf_rules);
            materialize(eg, op, &normal)
        };

        if std::env::var_os("AC_COMPLETE_TRACE").is_some() {
            eprintln!(
                "[ac-complete]   active(rules)={} targets(A′)={} crit(B)={}",
                rules.len(),
                targets.len(),
                crit.len()
            );
        }

        let mut changed = false;
        // (A′) normalize each monomial; materialize+merge its normal form; collapse rules.
        // A node is normalized by all OTHER rules, never by its own node-rule (a rule's
        // LHS is in normal form w.r.t. itself; reducing it by itself would subsume the
        // rule before it can superpose — the §4b regression). So a node is collapsed only
        // when a *different*, strictly-contained rule reduces it (genuine inter-reduction).
        for (op, mset, class, node, _is_rule) in targets {
            let normal = {
                let nf_rules: Vec<NfRule<Cfg::G>> = rules
                    .iter()
                    .filter(|r| r.op == op.to_usize() && r.node != node)
                    .map(|r| NfRule {
                        lhs: r.lhs.clone(),
                        rhs: r.rhs.clone(),
                    })
                    .collect();
                normalize_ms(&mset, &nf_rules)
            };
            if normal != mset {
                let c_prime = materialize(self, op, &normal);
                changed |= do_merge(self, c_prime, class);
                // Collapse: the node was reducible by another rule (proper containment),
                // so retire it from the active AC rule set (design §6b). FLAG_AC_COLLAPSED,
                // NOT subsume — the node stays matchable and a legal child; only
                // completion's active set excludes it. Merge first, mark second.
                self.set_ac_collapsed(node);
            }
        }
        // (B) close each critical pair by merging the normal forms of its two reducts.
        for (op, r1, r2) in crit {
            let c1 = nf(self, op, &r1, &rules);
            let c2 = nf(self, op, &r2, &rules);
            changed |= do_merge(self, c1, c2);
        }
        changed
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
        self.touched.clear();
    }

    fn register_if_fresh(&mut self, result: Added<Cfg::G>) -> Cfg::G {
        if result.is_fresh() {
            let id = result.id();
            let repr = self.classes.add_singleton(id);
            // A fresh non-AC node makes its class `atomic`: the class has a member that
            // is not an AC monomial, so the size-1 monomial `{class}` is its normal-form
            // representative (the completion rule RHS, §9a). AC nodes are not atomic by
            // themselves; they become atomic only when referenced as a child (`add_use`).
            if !matches!(self.node_ref(id), NodeRef::AC(_)) {
                self.classes.set_ac_atomic(repr);
            }
            self.touched.push(id);
        }
        result.id()
    }

    /// Semi-naive: node ids created or recanonicalized since the last
    /// `clear_touched` (or `restore`). May contain duplicates; the delta
    /// index builder deduplicates. Superset of all genuinely-changed nodes.
    pub fn touched(&self) -> &[Cfg::G] {
        &self.touched
    }

    /// Clear the touched log (call at a semi-naive round boundary, after the
    /// delta index for the round has been built).
    pub fn clear_touched(&mut self) {
        self.touched.clear();
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

    /// The AC minimum-monomial node stored for `id`'s class (the completion rule RHS,
    /// §9a). Maintained on merge by `fold_ac_class`. Returns `None` if `id` has no class.
    /// Consumed by the incremental completion pass (S3); currently read by tests only.
    #[allow(dead_code)]
    pub(crate) fn class_ac_min(&self, id: Cfg::G) -> Option<Cfg::G> {
        let repr = self.classes.repr_id(self.classes.find_const(id))?;
        Some(self.classes.ac_min(repr))
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

    /// Set one of the per-node control flags ([`FLAG_SUBSUMED`](crate::node_types::FLAG_SUBSUMED),
    /// [`FLAG_AC_COLLAPSED`](crate::node_types::FLAG_AC_COLLAPSED)) on `id`'s node.
    fn set_node_flag(&mut self, id: Cfg::G, flag: u8) {
        macro_rules! flag {
            ($store:expr, $l:expr) => {{
                let mut n = $store.get($l);
                n.flags |= flag;
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

    /// User-level subsumption: exclude `id` from future pattern matching (the matcher's
    /// indices skip `FLAG_SUBSUMED`). Distinct from AC-collapse — see `FLAG_AC_COLLAPSED`.
    pub fn subsume(&mut self, id: Cfg::G) {
        self.set_node_flag(id, crate::node_types::FLAG_SUBSUMED);
    }

    /// AC-completion collapse: retire `id` from the active AC rule set (its child
    /// multiset is reducible by a smaller AC rule, so it is no longer a superposition or
    /// inter-reduction source). The node stays **matchable** and a legal child; only
    /// completion's active set excludes it (design §6b). Distinct from `subsume`.
    pub(crate) fn set_ac_collapsed(&mut self, id: Cfg::G) {
        debug_assert!(
            matches!(self.node_ref(id), NodeRef::AC(_)),
            "set_ac_collapsed on a non-AC node"
        );
        self.set_node_flag(id, crate::node_types::FLAG_AC_COLLAPSED);
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

    // S1: the per-class ac_min slot tracks the degree-lex-least monomial across
    // merges (a constant is a size-1 monomial, so it wins over any sum) and rolls
    // back with the e-graph token. See design §9a.
    #[test]
    fn ac_min_tracks_least_monomial_and_rolls_back() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let c = eg.add(th.w, &[]); // a leaf constant, to merge a sum into
        let s_xy = eg.add(th.plus, &[x, y]); // +{x,y}, size 2
        let s_xyz = eg.add(th.plus, &[x, y, z]); // +{x,y,z}, size 3

        // Each fresh class's ac_min is its own node.
        assert_eq!(eg.class_ac_min(s_xy), Some(s_xy));
        assert_eq!(eg.class_ac_min(c), Some(c));

        // Merge the two sums: the smaller monomial (+{x,y}, size 2) wins over +{x,y,z}.
        eg.merge(s_xy, s_xyz);
        let repr_min = eg.class_ac_min(s_xy).unwrap();
        assert_eq!(eg.class_repr(repr_min), eg.class_repr(s_xy));
        assert_eq!(repr_min, s_xy, "ac_min should pick the smaller sum");

        // Snapshot, then merge the leaf constant c in: a size-1 monomial beats both sums.
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(c, s_xy);
        assert_eq!(
            eg.class_ac_min(c),
            Some(c),
            "a constant (size-1 monomial) is the least, so ac_min becomes c"
        );

        // Restore: the post-token merge is undone, and ac_min reverts to the sum.
        eg.restore(token);
        assert_eq!(
            eg.class_ac_min(s_xy),
            Some(s_xy),
            "ac_min must roll back with the e-graph token"
        );
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
                Justification::Filler => unreachable!("filler is never a real proof step"),
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
