// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The semi-persistent e-graph: add, merge, find, rebuild, mark, restore.

use crate::canon::{MSetCanon, MSetClamp, VarCanon};
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

/// How a completion op's monomial counts are bounded during normalization (design "three
/// independent axes"): unbounded ℕ (MSet), clamped to {0,1} by dedup (Set idempotent = ACI),
/// or reduced mod `order` (Set nilpotent, e.g. XOR at order 2). Selects the normalize/reduct
/// reduction in `cc_round`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompletionClamp {
    Multiset,
    Idempotent,
    Nilpotent { order: u8 },
}

#[derive(Clone, Copy, Debug)]
pub struct EGraphToken {
    classes: crate::classes::EClassesToken,
    nodes: NodeStoreToken,
    sorts: SortRegistryToken,
    ops: OpRegistryToken,
    rules: RuleRegistryToken,
    axioms: AxiomRegistryToken,
    lits: LitValStoreToken,
    unit_node: crate::containers::MapToken,
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
    /// Reusable scratch for a node's child ids as bare `G` (the canonical-children buffer for
    /// every representation except MSet). Paired with `mset_buf`, which holds the MSet variant.
    g_buf: Vec<Cfg::G>,
    /// Reusable scratch for MSet children, child type `C` = `(G, mult)` (the multiset
    /// representation needs the multiplicity that bare `G` in `g_buf` cannot carry).
    mset_buf: Vec<Cfg::C>,
    /// Semi-naive touched log: node ids created or recanonicalized since the
    /// last `clear_touched`. Round-local scratch (cleared on `restore`);
    /// drives the per-round delta index. Not part of persistent state.
    touched: Vec<Cfg::G>,
    /// Whether `rebuild` runs the AC congruence-completion pass (superposition +
    /// inter-reduction). **Default off**: completion can materialize nested same-op
    /// nodes, which the matcher cannot handle until AC flattening lands (`WF_flat`,
    /// see `doc/design/ac-congruence-completeness.md` §6b). Opt in with
    /// [`set_cc`](Self::set_cc) once flattening is in place; the
    /// completion tests enable it for the flat scenarios they exercise.
    cc: bool,
    /// Whether `rebuild` runs the AC reduced-basis invariant checks (`cc_basis_dump`:
    /// `min_monomial` minimality, the Kapur-reduced antichain, etc., see `ac_invariants.rs`).
    /// **Default off** and only consulted when `cc` is on: the ground-truth checks
    /// brute-force per-class minima and multi-step normalization (superlinear), so they are
    /// diagnostic/test-only, never on the production hot path. Seeded from the `AC_BASIS_DUMP`
    /// env var at construction (so existing diagnostic runs keep working) and overridable via
    /// [`set_basis_checks`](Self::set_basis_checks).
    basis_checks: bool,
    /// Reusable scratch for comparing two nodes' AC monomials (`monomial_cmp` on the
    /// per-class `min_monomial`, §9a). Two buffers to hold both sides without aliasing;
    /// cleared and refilled per comparison, never grown per merge.
    cmp_buf_a: Vec<(Cfg::G, crate::multiplicity::Multiplicity)>,
    cmp_buf_b: Vec<(Cfg::G, crate::multiplicity::Multiplicity)>,
    /// Reusable scratch for flattening nested same-op AC children (`WF_flat`,
    /// design §6c). Worklist of children still to expand; never grown per add.
    flatten_buf: Vec<Cfg::G>,
    /// Per-op identity (unit) element node, for completion ops declared with `:identity e`
    /// (`x ∘ e = x`; the unit drops from monomials). Resolved to a real node at registration
    /// (sortcheck has the model to parse the term and builds the node), keyed by op id. Stored
    /// here rather than on `OpKind<S>` because a node id is `Cfg::G`, which `OpKind<S>` cannot
    /// carry. Semi-persistent (its own token), so it rolls back with the op declarations that
    /// created the units. Absent key = the op has no declared identity.
    unit_node: crate::containers::Map<Cfg::O, Cfg::G, TRACK>,
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
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
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
            mset_buf: Vec::new(),
            touched: Vec::new(),
            cc: false,
            basis_checks: std::env::var_os("AC_BASIS_DUMP").is_some(),
            cmp_buf_a: Vec::new(),
            cmp_buf_b: Vec::new(),
            flatten_buf: Vec::new(),
            unit_node: crate::containers::Map::new(),
        }
    }

    /// Enable or disable the AC congruence-completion pass in `rebuild` (default off).
    /// Off until nested same-op flattening lands — see `cc` field docs.
    pub fn set_cc(&mut self, enabled: bool) {
        self.cc = enabled;
    }

    /// Enable or disable the AC reduced-basis invariant checks in `rebuild` (default off,
    /// seeded from the `AC_BASIS_DUMP` env var). When on (and `cc` is on), each
    /// completion round prints `cc_basis_dump`, which runs the ground-truth checkers
    /// (`min_monomial` minimality, Kapur-reducedness). These are superlinear brute-force checks,
    /// so leave this off outside diagnosis and tests. See `ac_invariants.rs`.
    pub fn set_basis_checks(&mut self, enabled: bool) {
        self.basis_checks = enabled;
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
    pub fn register_mset(&mut self, name: &str, arg: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register_mset(name, arg, ret)
    }
    pub fn register_set(&mut self, name: &str, arg: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register_set(name, arg, ret)
    }
    /// Register an op from a fully-resolved `OpKind` (the property-tag resolver in `sortcheck`).
    pub fn register_kind(&mut self, name: &str, ret: Cfg::S, kind: OpKind<Cfg::S>) -> Cfg::O {
        self.ops.register_kind(name, ret, kind)
    }
    /// Record `op`'s identity (unit) element node (`x ∘ e = x`; the unit drops from monomials).
    /// Called by the resolver in `sortcheck` after it builds the `:identity` term to a node.
    pub fn set_unit_node(&mut self, op: Cfg::O, unit: Cfg::G) {
        self.unit_node.insert(op, unit);
    }
    /// The identity (unit) element node of `op`, or `None` if `op` has no declared identity.
    pub fn unit_node(&self, op: Cfg::O) -> Option<Cfg::G> {
        self.unit_node.get_by_key(&op).copied()
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
                OpKind::A { arg_sort, .. }
                | OpKind::MSet { arg_sort, .. }
                | OpKind::Set { arg_sort, .. } => {
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

        // Flatten nested same-op AC children (associativity, `WF_flat`, design §6c): splice
        // any child whose class is a pure same-op sum, keyed on the class's canonical
        // summand form (atomic-aware), so `+(+(a,b), c)` becomes `+(a,b,c)`. An atomic child
        // (e.g. `c` used as `neg`'s child in §5b) is kept as a summand.
        if matches!(self.ops.info(op).kind, OpKind::MSet { .. }) {
            self.flatten_ac_children(op);
        }

        // Canonization must *establish* the op's algebraic normal form at build time (not defer
        // it to completion): coalesce/dedup, drop the identity's unit class, apply the count clamp
        // (nilpotent mod-n), and resolve a degenerate arity. Degeneracy is an equality, so the
        // last step returns an *existing* class id instead of a fresh node:
        //   - empty multiset  ⇒ the term IS the unit  (`xor(a,a) → {} = e`)
        //   - single mult-1    ⇒ the term IS that child (`+(a, e) → {a} = a`, `and(a,a) → {a} = a`)
        // These hold with completion off; completion only adds the cross-rule (superposition)
        // consequences. `find_unit`/degeneracy read `unit_node`, resolved at registration.
        let unit = self.unit_node(op);
        let result = match self.ops.info(op).kind {
            OpKind::MSet { .. } => {
                self.g_buf.sort_by_key(|id| id.to_usize());
                self.mset_buf.clear();
                for &id in &self.g_buf {
                    if let Some(last) = self.mset_buf.last_mut()
                        && Cfg::mset_child_merge(last, id)
                    {
                        continue;
                    }
                    self.mset_buf.push(Cfg::mset_child_single(id));
                }
                // Identity: drop the unit's class (`+(a, e) → {a}`).
                if let Some(u) = unit {
                    let uc = self.classes.find_const(u);
                    self.mset_buf.retain(|c| Cfg::mset_child_id(c) != uc);
                }
                // Nilpotent clamp: reduce each multiplicity mod n, drop zeros (`xor(a,a) → {}`).
                // Routed through the SINGLE source of the mod-n law, `MSetCanon::clamp_multiset`
                // (also used by the recanonize path), so the two paths cannot drift. `Cfg::C` is
                // concretely `(G, Multiplicity)` but opaque to generic code, so we convert the
                // buffer through the config accessors around the shared call. Nilpotent-only, so
                // the conversion never touches the common plain-AC / idempotent build.
                if let crate::registry::Clamp::Nilpotent { order } = self.op_clamp_kind(op) {
                    use crate::multiplicity::Multiplicity;
                    let mut tuples: Vec<(Cfg::G, Multiplicity)> = self
                        .mset_buf
                        .iter()
                        .map(|c| {
                            (
                                Cfg::mset_child_id(c),
                                Multiplicity(Cfg::mset_child_mult(c).into()),
                            )
                        })
                        .collect();
                    MSetCanon::clamp_multiset(&mut tuples, MSetClamp::Nilpotent { order });
                    self.mset_buf.clear();
                    self.mset_buf.extend(
                        tuples
                            .iter()
                            .map(|(g, m)| Cfg::mset_child_with_mult(*g, Cfg::M::from(m.0))),
                    );
                }
                // Degenerate arity ⇒ an existing class, not a fresh node. An empty monomial is the
                // unit; a single mult-1 summand is that summand's class. Empty *without* a declared
                // unit (only reachable for a plain AC op built with no non-unit children) falls
                // through to the (empty) node, the pre-canonization behavior.
                match self.mset_buf.len() {
                    0 => match unit {
                        Some(u) => return u,
                        None => self.nodes.add_mset(op, &self.mset_buf),
                    },
                    1 if Cfg::mset_child_mult(&self.mset_buf[0]).into() == 1 => {
                        return self.classes.find(Cfg::mset_child_id(&self.mset_buf[0]));
                    }
                    _ => self.nodes.add_mset(op, &self.mset_buf),
                }
            }
            OpKind::Set { .. } => {
                self.g_buf.sort_by_key(|id| id.to_usize());
                self.g_buf.dedup();
                // Identity: drop the unit's class (`and(a, unit) → {a}`).
                if let Some(u) = unit {
                    let uc = self.classes.find_const(u);
                    self.g_buf.retain(|&g| g != uc);
                }
                // Degenerate arity ⇒ an existing class (idempotent has no nilpotent clamp, so a
                // Set monomial only reaches {} via identity-drop, and size-1 via dedup/drop).
                // Empty without a declared unit falls through (pre-canonization behavior).
                match self.g_buf.len() {
                    0 => match unit {
                        Some(u) => return u,
                        None => self.nodes.add_set(op, &self.g_buf),
                    },
                    1 => return self.classes.find(self.g_buf[0]),
                    _ => self.nodes.add_set(op, &self.g_buf),
                }
            }
            _ => self.nodes.add(op, &self.g_buf, &self.ops),
        };

        let id = self.register_if_fresh(result);
        if result.is_fresh() {
            match self.ops.info(op).kind {
                OpKind::MSet { .. } => {
                    for c in &self.mset_buf {
                        let child = Cfg::mset_child_id(c);
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

    /// Build a *ground* checked term (a literal or a constructor applied to ground args) into a
    /// node, returning its id. Mirrors the interpreter's `build_cterm` for the ground cases; it
    /// has no access to globals, so a `CTerm::Global` is unreachable here (a unit is always
    /// ground) and panics. Used by the property-tag resolver to materialize an op's `:identity`
    /// unit at registration.
    pub fn build_ground_cterm(
        &mut self,
        ct: &crate::sortcheck::CTerm<Cfg::O, Cfg::S, L>,
    ) -> Cfg::G {
        match ct {
            crate::sortcheck::CTerm::Lit(val, sort) => {
                let lit_op = self
                    .ops
                    .lit_op_for_sort(*sort)
                    .expect("no lit op for identity's sort");
                let vid = self.lits.intern(val.clone());
                self.add_lit(lit_op, vid)
            }
            crate::sortcheck::CTerm::App { op, children, .. } => {
                let child_ids: Vec<Cfg::G> = children
                    .iter()
                    .map(|c| self.build_ground_cterm(c))
                    .collect();
                self.add(*op, &child_ids)
            }
            crate::sortcheck::CTerm::Global(..) => {
                panic!("identity unit must be a ground term, not a global reference")
            }
        }
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
        match self.node_ref(node) {
            NodeRef::MSet(_) => {
                // mset_children, find-canonicalized + coalesced (same form as MSetCanon).
                let mut raw = Vec::new();
                self.mset_children(node, &mut raw);
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
            }
            NodeRef::Set(_) => {
                // set_children, find-canonicalized + deduped (set semantics, all mult 1 —
                // same form as SetCanon). This is the ACI monomial.
                let mut raw = Vec::new();
                self.set_children(node, &mut raw);
                let mut m: Vec<Cfg::G> = raw
                    .into_iter()
                    .map(|g| self.classes.find_const(g))
                    .collect();
                m.sort();
                m.dedup();
                for g in m {
                    buf.push((g, Multiplicity(1)));
                }
            }
            _ => {
                buf.push((self.classes.find_const(node), Multiplicity(1)));
            }
        }
        // No clamp / unit-drop here: canonization (`add`, `recanonize_node`) already established
        // the op's algebraic normal form (nilpotent mod-n, identity unit-drop) in the stored node,
        // and `cc_round` only runs after `rebuild_congruence` recanonicalizes every node. So a
        // stored MSet/Set node's children are already the canonical monomial; reading them back is
        // enough. (This used to re-apply the clamp/drop, which was the symptom of the clamp living
        // in completion rather than canonization — now fixed.)
    }

    /// The completion column of `node`'s op (its position in the registry `completion_ops`
    /// array), or `None` if `node`'s op is not a completion (MSet/Set) op.
    fn completion_column(&self, node: Cfg::G) -> Option<usize> {
        self.ops.completion_column(self.node_op(node))
    }

    /// The op's registry count `Clamp` (`None` / `Idempotent` / `Nilpotent`). The build/canonize
    /// path reads this directly (the algebraic normal form), where `op_clamp`'s `CompletionClamp`
    /// projection is completion-shaped. `None` for a non-AC op.
    fn op_clamp_kind(&self, op: Cfg::O) -> crate::registry::Clamp {
        match self.ops.info(op).kind {
            OpKind::MSet { clamp, .. } | OpKind::Set { clamp, .. } => clamp,
            _ => crate::registry::Clamp::None,
        }
    }

    /// The normalization clamp for an op's completion monomials: unbounded (MSet), clamp-to-1
    /// (Set idempotent, ACI), or mod-n (Set nilpotent). Determines how reducts and normal forms
    /// are reduced (design "three independent axes").
    fn op_clamp(&self, op: Cfg::O) -> CompletionClamp {
        use crate::registry::Clamp;
        match self.ops.info(op).kind {
            // Nilpotent is stored MSet (keeps multiplicities); its clamp is read here.
            OpKind::MSet {
                clamp: Clamp::Nilpotent { order },
                ..
            } => CompletionClamp::Nilpotent { order },
            OpKind::MSet { .. } => CompletionClamp::Multiset,
            OpKind::Set {
                clamp: Clamp::Idempotent,
                ..
            } => CompletionClamp::Idempotent,
            // A Set with any other clamp is never constructed (resolver invariant); treat as ACI.
            OpKind::Set { .. } => CompletionClamp::Idempotent,
            _ => CompletionClamp::Multiset, // non-completion op; never reached in the round
        }
    }

    /// Fill `buf` with the completion rule right-hand side for the class of `node`: the
    /// size-1 monomial `{find(node)}` if the class is `atomic` (referenced as a child), else
    /// the monomial of the class's stored min-monomial for `node`'s op column (§9a). Reads the
    /// per-class pool slot; O(1) plus the monomial read. Returns `false` if `node` has no class
    /// (or, in the non-atomic case, no stored monomial for its op — a genuine rule always has
    /// one, so this only guards the degenerate case).
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
        if self.classes.atomic(repr) {
            buf.clear();
            buf.push((cls, Multiplicity(1)));
            return true;
        }
        let Some(col) = self.completion_column(node) else {
            return false;
        };
        let Some(min) = self.classes.min_monomial(repr, col) else {
            return false;
        };
        self.node_monomial_into(min, buf);
        true
    }

    /// After a merge, fold the absorbed class's per-class AC data into the survivor's,
    /// per completion column: keep the `monomial_cmp`-least min-monomial node for each op, and
    /// OR-in the `atomic` flag (§9a). O(nb_completion) columns, each O(1) plus a monomial read,
    /// into reusable buffers. Done here, not in `EClasses`, because the comparison needs node
    /// (AC-children) access and the op→column map. Best-effort under merge-cascade staleness;
    /// completion's read-time orientation guard makes that safe (§9b).
    fn fold_min_monomial(
        &mut self,
        survivor: Cfg::G,
        absorbed_min_row: Option<usize>,
        absorbed_atomic: bool,
    ) {
        let surv_repr = match self.classes.repr_id(self.classes.find_const(survivor)) {
            Some(r) => r,
            None => return,
        };
        if absorbed_atomic {
            self.classes.set_atomic(surv_repr);
        }
        let mut a = std::mem::take(&mut self.cmp_buf_a);
        let mut b = std::mem::take(&mut self.cmp_buf_b);
        for col in 0..self.classes.min_width() {
            let Some(absorbed_min) = self.classes.min_monomial_at_row(absorbed_min_row, col) else {
                continue; // absorbed class has no monomial for this op
            };
            match self.classes.min_monomial(surv_repr, col) {
                None => {
                    // survivor had no monomial for this op; take the absorbed one.
                    self.classes.set_min_monomial(surv_repr, col, absorbed_min);
                }
                Some(surv_min) if surv_min != absorbed_min => {
                    self.node_monomial_into(surv_min, &mut a);
                    self.node_monomial_into(absorbed_min, &mut b);
                    if crate::multiset::monomial_cmp(&b, &a) == std::cmp::Ordering::Less {
                        self.classes.set_min_monomial(surv_repr, col, absorbed_min);
                    }
                }
                Some(_) => {} // equal; nothing to do
            }
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
        self.fold_min_monomial(m.survivor, m.absorbed_min_row, m.absorbed_atomic);
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
        self.fold_min_monomial(m.survivor, m.absorbed_min_row, m.absorbed_atomic);
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
                        | NodeRef::Seq(_)
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
                out.push(Cfg::mset_child_id(c));
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
    /// - [`cc_round`](Self::cc_round): AC completion (substitutes
    ///   equal *sub-sums*), which canonization alone misses.
    ///
    /// A completion round may push new merges onto the worklist; we drain them with
    /// another congruence pass, then complete again, until a whole completion round
    /// adds nothing. The fixpoint is the AC congruence closure of the asserted
    /// equalities.
    pub fn rebuild(&mut self) {
        // Ordinary atom-level congruence closure always runs. AC completion runs only
        // when opted in (default off until nested same-op flattening lands — §6b).
        if !self.cc {
            self.rebuild_congruence();
            return;
        }
        // Multiple MSet symbols are supported: the per-class min-monomial pool stores a
        // separate least-monomial per completion op (step 3), and the round groups rules by op
        // (superposition/normalization filter on `r.op`, RHS via the node's own op column). Two
        // MSet ops therefore complete as independent rule sets sharing only the constant pool;
        // a class holding monomials of both (`a+b = a*b`) keeps each in its own column, and
        // union-find records the cross-op equality (Kapur's shared-constant case). Set (ACI)
        // completion is not yet driven (step 5): Set ops canonicalize but the round only reads
        // the MSet partition, so a registered Set op is sound-but-uncompleted, as before.
        let trace = std::env::var_os("AC_COMPLETE_TRACE").is_some();
        // Safety backstop against a diverging completion (minting unbounded
        // critical-pair nodes). A convergent completion adds few nodes; if the AC
        // node count balloons past this many beyond where it started, we stop
        // rather than OOM. This is NOT the termination argument — it is a guard
        // rail while the proper inter-reduction is being put in place.
        const MAX_COMPLETION_NODE_GROWTH: usize = 50_000;
        let start_nodes = self.node_count();
        let basis_dump = self.basis_checks;
        let mut round = 0usize;
        // Watermark into the `touched` log: rules whose `(op, monomial)` changed since the
        // previous round are exactly the nodes touched (created or recanonicalized) in the
        // slice `touched[prev_mark..mark]`. Superposition (B) is incremental over this delta
        // (S3b): round 0 is a full pass (base case), each later round superposes only pairs
        // with ≥1 endpoint in the delta. Old×old pairs were closed earlier and stay closed.
        let mut prev_mark = 0usize;
        // Incremental rounds run until one finds nothing; then a single *full* confirmation
        // round certifies convergence (S3b completeness net). The node-touch delta misses a
        // pair only if a rule's RHS shifted without its node being recanonicalized (its own
        // class merged, not a child's); a full round closes any such pair. Convergence is
        // declared only when a *full* round is unchanged, so the net is sound. Full rounds
        // run only at would-be-convergence, where every pair is trivial and cheap.
        let mut full = true; // round 0 is full (base case)
        loop {
            self.rebuild_congruence();
            if basis_dump {
                self.cc_basis_dump(&format!("round {round} pre"));
            }
            let before = self.node_count();
            let mark = self.touched.len();
            let was_full = full;
            let changed = self.cc_round(full, prev_mark, mark);
            prev_mark = mark;
            if trace {
                eprintln!(
                    "[ac-complete] round {round}{}: nodes {before} -> {} (+{}), changed={changed}",
                    if was_full { " (full)" } else { "" },
                    self.node_count(),
                    self.node_count() - before
                );
            }
            round += 1;
            if !changed {
                // Incremental round found nothing: confirm with a full round before exiting.
                // A full round that also finds nothing is true convergence.
                if was_full {
                    return;
                }
                full = true;
                continue;
            }
            // Made progress: stay incremental for the next round.
            full = false;
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

    /// If a (just-recanonized) MSet/Set node has a degenerate canonical arity, return the
    /// equality `(node, target)` it now denotes: an empty monomial equals the op's unit, a
    /// single mult-1 summand equals that summand's class. Returns `None` for a well-formed
    /// (≥2, or size-1-with-mult>1) monomial or a non-AC node. This is canonization's
    /// "AC-of-nothing/one" law read off the stored form; the caller merges the pair. Mirrors
    /// the build-path (`add`) degeneracy resolution, for nodes that go degenerate via a child
    /// merge rather than at build.
    fn degeneracy_merge(&self, node: Cfg::G) -> Option<(Cfg::G, Cfg::G)> {
        // Peek the node's canonical child span length (no child read, no alloc) and act only on a
        // degenerate arity — the common ≥2 case returns immediately. Recanonize has already
        // written the coalesced/clamped children, so the span length *is* the canonical child
        // count. Only when arity is exactly 1 do we read that one child.
        match self.node_ref(node) {
            NodeRef::MSet(l) => {
                let n = self.nodes.mset.get(l);
                let (s, e) = n.span();
                match e - s {
                    0 => self.unit_node(self.node_op(node)).map(|u| (node, u)),
                    1 => {
                        let c = self.nodes.mset.pool_get(s);
                        // Size-1 collapses to the child only at multiplicity 1 (`{a:2}` is not a
                        // degenerate `a`; for a nilpotent op it would already have clamped to `{}`).
                        (Cfg::mset_child_mult(&c).into() == 1)
                            .then(|| (node, Cfg::mset_child_id(&c)))
                    }
                    _ => None,
                }
            }
            NodeRef::Set(l) => {
                let n = self.nodes.set.get(l);
                let (s, e) = n.span();
                match e - s {
                    0 => self.unit_node(self.node_op(node)).map(|u| (node, u)),
                    1 => Some((node, self.nodes.set.pool_get(s))),
                    _ => None,
                }
            }
            _ => None,
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
                    &mut self.mset_buf,
                    &mut self.collisions,
                    &mut self.touched,
                    &self.ops,
                );
                // Canonization can shrink an MSet/Set node to a degenerate arity (a child merge
                // pushes a nilpotent count to 0, or coalesces/drops to a single summand): the node
                // then *equals* an existing class — empty ⇒ the unit, size-1 mult-1 ⇒ that child.
                // Recanonize (representation) can't express that equality, so record it as a merge
                // here (the congruence layer), alongside the hash-cons collisions. `and(a,b)` after
                // `a=b` becomes `{a}` = `a`; `xor(a,b)` after `a=b` becomes `{}` = the unit.
                if let Some(pair) = self.degeneracy_merge(parent) {
                    self.collisions.push(pair);
                }
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
                    self.fold_min_monomial(m.survivor, m.absorbed_min_row, m.absorbed_atomic);
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
    /// ([`crate::cc::CcSnapshot`]), for each pair of partners (same op,
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
    /// One AC completion round. Superposition (B) is incremental (S3b): when `full` is
    /// false, only critical pairs with ≥1 endpoint among the *delta rules* (nodes touched
    /// in `self.touched[delta_lo..delta_hi]`, i.e. created or recanonicalized since the
    /// previous round) are generated; old×old pairs were closed in an earlier round and
    /// stay closed under monotone merges. `full` (round 0) generates every pair. The (A′)
    /// collapse/normalize pass and the antichain `reducible` check stay full scans: a small
    /// new rule must still be able to collapse a large old one.
    fn cc_round(&mut self, full: bool, delta_lo: usize, delta_hi: usize) -> bool {
        use crate::multiplicity::Multiplicity;
        use crate::multiset::{
            NfRule, multiset_disjoint, multiset_lcm, multiset_subset, normalize_ms,
        };

        // Canonical monomial of a completion node as sorted (class-repr, mult): coalesced
        // multiplicities for an MSet op, deduped set (all mult 1) for a Set (ACI) op.
        // Delegates to `node_monomial_into`, which dispatches on the node's representation.
        let multiset_of = |eg: &Self, id: Cfg::G| -> Vec<(Cfg::G, Multiplicity)> {
            let mut out = Vec::new();
            eg.node_monomial_into(id, &mut out);
            out
        };

        use crate::multiset::monomial_cmp;
        use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};

        // Completion's active set excludes nodes that are user-subsumed (not matchable)
        // OR AC-collapsed (reducible by a smaller rule). Either way they are not rules.
        let inactive = FLAG_SUBSUMED | FLAG_AC_COLLAPSED;

        // Each active AC node is a candidate rule `+M → rhs(class)`, where the RHS comes
        // from the per-class slot (`class_rhs_into`: `{class}` if atomic, else the stored
        // `min_monomial` monomial, §9a) — not recomputed per round. The orientation guard keeps
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
        // Iterate the AC node partition directly (ascending global id), not all nodes: the
        // `is_mset` filter is implicit and the non-AC majority is never visited.
        for gid in self.completion_node_ids() {
            if self.node_flags(gid) & inactive != 0 {
                continue;
            }
            let op = self.node_op(gid);
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
        // The (B) partner search binary-searches `rules` by global node id, so it must be
        // sorted by `node`. `completion_node_ids` yields the MSet partition then the Set
        // partition, each internally id-sorted but interleaved in the global id space, so sort
        // by `node` here (a cheap merge of two sorted runs). Distinct nodes ⇒ strictly sorted.
        rules.sort_unstable_by_key(|r| r.node);
        debug_assert!(rules.windows(2).all(|w| w[0].node < w[1].node));

        // Dedup the reducer/superposition set by (op, LHS). Congruent AC nodes can
        // recanonicalize to the same monomial after a child merge without being hash-consed
        // into one node, so the same rule `+M → r` appears as several nodes. Kapur step 2
        // discards a duplicate equation and keeps one; here we keep the lowest-node-id copy
        // as the canonical rule and drop the rest from `rules`. This is what makes the active
        // set Kapur-*reduced* (no LHS reducible by another's), not merely a strict-containment
        // antichain: identical-LHS copies were the whole measured gap between `reducible_pairs`
        // and the ground-truth `kapur_lhs_reducible` (ac_invariants). The dropped copies are
        // NOT lost: they remain in `targets`, so (A′) still collapses each (its monomial
        // reduces to the shared RHS via the kept rule) and still merges any differing-RHS copy
        // (the implied equality fires through `targets`, not `rules`). Without the dedup, every
        // copy reduces every other copy, so they mutually collapse and the rule vanishes
        // entirely (the §6b "merge before mark" / self-reduction hazard, at the set level).
        // O(rules) with one hash per rule; in line with the batch round's existing per-rule
        // clones (the DPS rewrite is S3b).
        {
            let mut seen: std::collections::HashSet<(usize, Vec<(Cfg::G, Multiplicity)>)> =
                std::collections::HashSet::with_capacity(rules.len());
            rules.retain(|r| seen.insert((r.op, r.lhs.clone())));
        }

        // Delta rule-node set for incremental (B): sorted, dedup'd node ids touched since
        // the previous round. `touched` may contain duplicates; sort+dedup once, then test
        // a rule's membership by binary search (mirrors the `rules` binary-search idiom).
        let delta: Vec<Cfg::G> = if full {
            Vec::new()
        } else {
            let mut d: Vec<Cfg::G> = self.touched[delta_lo..delta_hi].to_vec();
            d.sort_unstable();
            d.dedup();
            d
        };
        let in_delta = |n: Cfg::G| -> bool { full || delta.binary_search(&n).is_ok() };

        // Reducibility flag per rule: a rule whose LHS strictly contains another rule's LHS
        // (same op) is reducible by it, so collapse will retire it. Kapur superposes only
        // over the inter-reduced *antichain*, never over a reducible rule (FSCD'21 Algo 1:
        // collapse before superpose). The batch round collapses these only on the *next*
        // round, so excluding them as (B) sources/partners here is what keeps the active
        // set an antichain within the round and stops the critical-pair blowup (plan §0.4).
        // O(rules²) over the small active set; acceptable while the worklist rewrite (S3b)
        // is pending.
        let phase_time = std::env::var_os("AC_PHASE_TIME").is_some();
        let t_reducible = std::time::Instant::now();
        let reducible: Vec<bool> = (0..rules.len())
            .map(|i| {
                rules.iter().enumerate().any(|(j, rj)| {
                    j != i
                        && rj.op == rules[i].op
                        && rj.lhs != rules[i].lhs
                        && multiset_subset(&rj.lhs, &rules[i].lhs)
                })
            })
            .collect();
        let dt_reducible = t_reducible.elapsed();

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
                    eg.fold_min_monomial(m.survivor, m.absorbed_min_row, m.absorbed_atomic);
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
        let t_gen = std::time::Instant::now();
        let mut targets: Vec<(Cfg::O, Vec<(Cfg::G, Multiplicity)>, Cfg::G, Cfg::G, bool)> =
            Vec::new();
        // AC partition only, same as the rules scan (no full-graph walk, no `is_mset` filter).
        for gid in self.completion_node_ids() {
            if self.node_flags(gid) & inactive != 0 {
                continue;
            }
            let op = self.node_op(gid);
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
        let mut delta_skipped = 0usize;
        let delta_in_rules = rules.iter().filter(|r| in_delta(r.node)).count();
        for ti in 0..rules.len() {
            // A reducible rule is not a member of the antichain: collapse will retire it,
            // so it must not seed critical pairs (plan §0.4).
            if reducible[ti] {
                continue;
            }
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
                // ...and a member of the antichain (a reducible partner will be collapsed).
                if reducible[pi] {
                    continue;
                }
                // Incremental (B): an unordered pair is a *new* critical pair only if at
                // least one of its rules changed since the previous round (S3b). When
                // neither endpoint is in the delta the pair was closed in an earlier round
                // and stays closed; skip it. `full` (round 0) makes `in_delta` always true.
                if !in_delta(m_node) && !in_delta(p_node) {
                    delta_skipped += 1;
                    continue;
                }
                let m = &rules[ti].lhs;
                let a = &rules[pi].lhs;
                // Shared by construction; skip the non-overlap / containment cases
                // (containment is handled by the (A′) normalize pass).
                debug_assert!(!multiset_disjoint(a, m));
                if multiset_subset(a, m) || multiset_subset(m, a) {
                    continue;
                }
                let ab = multiset_lcm(m, a);
                let mut r1 = crate::multiset::multiset_union(
                    &crate::multiset::multiset_subtract(&ab, m),
                    &rules[ti].rhs,
                );
                let mut r2 = crate::multiset::multiset_union(
                    &crate::multiset::multiset_subtract(&ab, a),
                    &rules[pi].rhs,
                );
                // Clamp the reducts to the op's normal-form count domain before the pair is
                // closed: idempotent → {0,1} (ACI union), nilpotent → mod-n (symmetric
                // difference). Multiset (plain AC) keeps ℕ counts, no clamp.
                match self.op_clamp(op) {
                    CompletionClamp::Idempotent => {
                        crate::multiset::clamp_idempotent(&mut r1);
                        crate::multiset::clamp_idempotent(&mut r2);
                    }
                    CompletionClamp::Nilpotent { order } => {
                        crate::multiset::clamp_nilpotent(&mut r1, order);
                        crate::multiset::clamp_nilpotent(&mut r2, order);
                    }
                    CompletionClamp::Multiset => {}
                }
                crit.push((op, r1, r2));
            }
        }

        // Critical-pair reducts are normalized to multisets (each step strictly lowers the
        // multiset in degree-lex order against the rule set, so it terminates), then only a
        // genuinely-divergent pair is materialized — this is what stops the runaway
        // (design §6b). See the (B) close loop below.

        if std::env::var_os("AC_COMPLETE_TRACE").is_some() {
            eprintln!(
                "[ac-complete]   active(rules)={} targets(A′)={} crit(B)={}",
                rules.len(),
                targets.len(),
                crit.len()
            );
        }

        let dt_gen = t_gen.elapsed();
        let mut changed = false;
        let t_aprime = std::time::Instant::now();
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
                // Normalize in the op's count domain: idempotent → set (clamp to 1); nilpotent →
                // mod-n; plain AC (MSet) → ℕ.
                match self.op_clamp(op) {
                    CompletionClamp::Idempotent => crate::multiset::normalize_set(&mset, &nf_rules),
                    CompletionClamp::Nilpotent { order } => {
                        crate::multiset::normalize_nilpotent(&mset, &nf_rules, order)
                    }
                    CompletionClamp::Multiset => normalize_ms(&mset, &nf_rules),
                }
            };
            // If normalization by the other rules changed the monomial, materialize the normal
            // form and merge. `materialize` calls `add`, which now resolves a degenerate result
            // itself: an emptied monomial (`a ⊕ a → {}`, or `+(a,e)`-style cancellation) becomes
            // the unit, and a single mult-1 summand (`a ⊕ a ⊕ b → {b}`) becomes that class — so
            // this one branch covers the empty/size-1 cases too (a completion target always has
            // `mset.len() ≥ 2`, canonization never stores a degenerate node, so any empty/size-1
            // `normal` differs from `mset` and lands here).
            if normal != mset {
                let c_prime = materialize(self, op, &normal);
                changed |= do_merge(self, c_prime, class);
                // Collapse: the node was reducible by another rule (proper containment),
                // so retire it from the active AC rule set (design §6b). FLAG_AC_COLLAPSED,
                // NOT subsume — the node stays matchable and a legal child; only
                // completion's active set excludes it. Merge first, mark second.
                self.set_cc_collapsed(node);
            }
        }
        let dt_aprime = t_aprime.elapsed();
        let t_bclose = std::time::Instant::now();
        // (B) close each critical pair by merging the normal forms of its two reducts.
        // Normalize BOTH reducts to multisets first; if they coincide the pair is already
        // joinable (a trivial critical pair) — skip it, minting no node and no merge.
        // Materializing trivial pairs was a second blowup source: each spurious node became
        // a fresh rule that fed the next round (plan §0.4). Only genuinely-divergent pairs
        // are materialized and merged.
        let mut trivial = 0usize;
        let mut nontrivial = 0usize;
        let mut trivial_after_nf = 0usize; // trivial pairs that needed full normalize to see it
        // The rule set used to normalize a reduct is the same for every pair of a given op, so
        // build the per-op rule sets ONCE (outside the loop), not per pair — the `Bclose` hoist
        // (perf doc §2). A reduct of op X must normalize ONLY against op-X rules: a different
        // op's LHS is a set of class ids that could spuriously match inside X's monomial. So
        // group `nf_rules` by op. Keyed by op index; lookup is a small linear scan (few ops).
        let mut nf_by_op: Vec<(usize, Vec<NfRule<Cfg::G>>)> = Vec::new();
        for r in &rules {
            let entry = match nf_by_op.iter_mut().find(|(o, _)| *o == r.op) {
                Some(e) => &mut e.1,
                None => {
                    nf_by_op.push((r.op, Vec::new()));
                    &mut nf_by_op.last_mut().unwrap().1
                }
            };
            entry.push(NfRule {
                lhs: r.lhs.clone(),
                rhs: r.rhs.clone(),
            });
        }
        let empty_nf: Vec<NfRule<Cfg::G>> = Vec::new();
        let crit_generated = crit.len();
        for (op, r1, r2) in crit {
            // Cheap raw-equality reject: most critical pairs are trivial (the two reducts
            // already coincide as multisets), so skip the two full normalizations entirely
            // when r1 == r2 already.
            if r1 == r2 {
                trivial += 1;
                continue;
            }
            let nf_rules = nf_by_op
                .iter()
                .find(|(o, _)| *o == op.to_usize())
                .map_or(&empty_nf, |(_, v)| v);
            // Normalize both reducts in the op's count domain (idempotent → set, nilpotent →
            // mod-n, plain AC → ℕ) before comparing/merging.
            let (n1, n2) = match self.op_clamp(op) {
                CompletionClamp::Idempotent => (
                    crate::multiset::normalize_set(&r1, nf_rules),
                    crate::multiset::normalize_set(&r2, nf_rules),
                ),
                CompletionClamp::Nilpotent { order } => (
                    crate::multiset::normalize_nilpotent(&r1, nf_rules, order),
                    crate::multiset::normalize_nilpotent(&r2, nf_rules, order),
                ),
                CompletionClamp::Multiset => {
                    (normalize_ms(&r1, nf_rules), normalize_ms(&r2, nf_rules))
                }
            };
            if n1 == n2 {
                trivial += 1;
                trivial_after_nf += 1;
                continue;
            }
            nontrivial += 1;
            // `materialize` calls `add`, which resolves a degenerate reduct itself: an emptied
            // reduct (nilpotent cancellation / identity drop) becomes the unit, a single mult-1
            // summand becomes that class. So no empty/size-1 special-casing is needed here.
            let c1 = materialize(self, op, &n1);
            let c2 = materialize(self, op, &n2);
            changed |= do_merge(self, c1, c2);
        }
        if std::env::var_os("AC_COMPLETE_TRACE").is_some() {
            eprintln!(
                "[ac-complete]   crit(B) trivial={trivial} (raw-eq={}, after-nf={trivial_after_nf}) nontrivial={nontrivial}",
                trivial - trivial_after_nf
            );
            eprintln!(
                "[ac-complete]   full={full} rules={} delta_in_rules={delta_in_rules} delta_skipped_pairs={delta_skipped} crit_generated={crit_generated}",
                rules.len(),
            );
        }
        if phase_time {
            let dt_bclose = t_bclose.elapsed();
            eprintln!(
                "[ac-phase] rules={} reducible={:.1}ms gen+targets={:.1}ms A'={:.1}ms Bclose={:.1}ms",
                rules.len(),
                dt_reducible.as_secs_f64() * 1e3,
                dt_gen.as_secs_f64() * 1e3,
                dt_aprime.as_secs_f64() * 1e3,
                dt_bclose.as_secs_f64() * 1e3,
            );
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
            unit_node: self.unit_node.mark(shrink),
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
        self.unit_node.restore(token.unit_node);
        self.worklist.clear();
        self.collisions.clear();
        self.touched.clear();
    }

    fn register_if_fresh(&mut self, result: Added<Cfg::G>) -> Cfg::G {
        if result.is_fresh() {
            let id = result.id();
            let repr = self.classes.add_singleton(id);
            // Seed the per-class min-monomial pool. A completion node (MSet or Set) is its
            // class's only monomial for its own op, so seed that op's column to itself. A
            // non-completion node instead makes its class `atomic`: the class has a member
            // that is not a monomial, so the size-1 monomial `{class}` is its normal-form
            // representative (the completion rule RHS, §9a). Completion nodes are not atomic
            // by themselves; they become atomic only when referenced as a child (`add_use`).
            match self.completion_column(id) {
                Some(col) => {
                    // Fix the pool row width to nb_completion on first completion-node seed.
                    // Ops are declared before terms (declare-before-build), so the count is
                    // stable here; `set_min_width` is idempotent when unchanged and rejects a
                    // change once rows exist.
                    self.classes.set_min_width(self.ops.completion_op_count());
                    self.classes.set_min_monomial(repr, col, id);
                }
                None => self.classes.set_atomic(repr),
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

    /// The minimum-monomial node stored for `id`'s class in `id`'s op column (the completion
    /// rule RHS, §9a). Maintained on merge by `fold_min_monomial`. Returns `None` if `id` has
    /// no class or its op has no stored monomial for that class. Read by tests only.
    #[allow(dead_code)]
    pub(crate) fn class_min_monomial(&self, id: Cfg::G) -> Option<Cfg::G> {
        let repr = self.classes.repr_id(self.classes.find_const(id))?;
        let col = self.completion_column(id)?;
        self.classes.min_monomial(repr, col)
    }

    /// Whether `id`'s class is `atomic` (referenced as a child / has a non-AC node, so
    /// `{class}` is its canonical summand form, §9a). `None` if `id` has no class.
    #[allow(dead_code)]
    pub(crate) fn class_atomic(&self, id: Cfg::G) -> Option<bool> {
        let repr = self.classes.repr_id(self.classes.find_const(id))?;
        Some(self.classes.atomic(repr))
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
            NodeRef::SPair(l) => self.nodes.spair.get(l).op(),
            NodeRef::PlainN(l) => self.nodes.plain_n.get(l).op(),
            NodeRef::Seq(l) => self.nodes.seq.get(l).op(),
            NodeRef::MSet(l) => self.nodes.mset.get(l).op(),
            NodeRef::Set(l) => self.nodes.set.get(l).op(),
            NodeRef::Lit(l) => self.nodes.lit.get(l).op(),
        }
    }

    pub fn node_op_name(&self, id: Cfg::G) -> &str {
        &self.ops.info(self.node_op(id)).name
    }

    /// Global ids of every AC e-node, ascending (the AC partition is append-only, so local
    /// id order is global-id order). The completion round iterates this instead of all
    /// `node_count()` nodes: it visits only AC nodes, never the non-AC majority (leaves,
    /// `Plain`/`Lit`/other-op nodes). On AC-dense stress graphs this is ~neutral, but on a
    /// general e-graph (mostly non-AC structure) the AC nodes are a small fraction, so the
    /// per-round scan drops from O(total nodes) to O(AC nodes). Includes collapsed/subsumed
    /// AC nodes; the caller filters by flag.
    fn completion_node_ids(&self) -> impl Iterator<Item = Cfg::G> + '_ {
        use crate::containers::DenseId;
        use crate::typed_routing::NodeIds;
        // Both completion partitions: MSet (multiset, AC) and Set (idempotent/nilpotent, ACI).
        let n_mset = self.nodes.mset.len().to_usize();
        let n_set = self.nodes.set.len().to_usize();
        let mset = (0..n_mset).map(move |i| {
            let l = <Cfg::Ids as NodeIds>::LMSet::from_usize(i);
            self.nodes.mset.get(l).global_id()
        });
        let set = (0..n_set).map(move |i| {
            let l = <Cfg::Ids as NodeIds>::LSet::from_usize(i);
            self.nodes.set.get(l).global_id()
        });
        mset.chain(set)
    }

    pub fn node_flags(&self, id: Cfg::G) -> u8 {
        match self.node_ref(id) {
            NodeRef::Plain0(l) => self.nodes.plain0.get(l).flags,
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).flags,
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).flags,
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).flags,
            NodeRef::SPair(l) => self.nodes.spair.get(l).flags,
            NodeRef::PlainN(l) => self.nodes.plain_n.get(l).flags,
            NodeRef::Seq(l) => self.nodes.seq.get(l).flags,
            NodeRef::MSet(l) => self.nodes.mset.get(l).flags,
            NodeRef::Set(l) => self.nodes.set.get(l).flags,
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
            NodeRef::SPair(l) => flag!(self.nodes.spair, l),
            NodeRef::PlainN(l) => flag!(self.nodes.plain_n, l),
            NodeRef::Seq(l) => flag!(self.nodes.seq, l),
            NodeRef::MSet(l) => flag!(self.nodes.mset, l),
            NodeRef::Set(l) => flag!(self.nodes.set, l),
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
    pub(crate) fn set_cc_collapsed(&mut self, id: Cfg::G) {
        debug_assert!(
            matches!(self.node_ref(id), NodeRef::MSet(_) | NodeRef::Set(_)),
            "set_cc_collapsed on a non-completion node"
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
            NodeRef::SPair(l) => {
                for &c in &self.nodes.spair.get(l).children {
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
            NodeRef::Seq(l) => {
                let n = self.nodes.seq.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.seq.pool_get(i), 1);
                }
                e - s
            }
            NodeRef::MSet(l) => {
                let n = self.nodes.mset.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    let c = self.nodes.mset.pool_get(i);
                    f(Cfg::mset_child_id(&c), Cfg::mset_child_mult(&c).into());
                }
                e - s
            }
            NodeRef::Set(l) => {
                let n = self.nodes.set.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.set.pool_get(i), 1);
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
            NodeRef::SPair(l) => self.nodes.spair.get(l).children[p],
            NodeRef::PlainN(l) => {
                let n = self.nodes.plain_n.get(l);
                let (s, _) = n.span();
                self.nodes.plain_n.pool_get(s + p)
            }
            NodeRef::Seq(l) => {
                let n = self.nodes.seq.get(l);
                let (s, _) = n.span();
                self.nodes.seq.pool_get(s + p)
            }
            _ => panic!("child_at: not a plain/sequence node or pos out of range"),
        }
    }

    /// Read AC children as `(id, multiplicity)` pairs into `buf`.
    pub fn mset_children(&self, id: Cfg::G, buf: &mut Vec<(Cfg::G, Cfg::M)>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::MSet(l) => {
                let n = self.nodes.mset.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    let c = self.nodes.mset.pool_get(i);
                    buf.push((Cfg::mset_child_id(&c), Cfg::mset_child_mult(&c)));
                }
            }
            _ => panic!("mset_children: not an MSet node"),
        }
    }

    /// Flatten nested same-op AC children of `op` in `self.g_buf`, to a fixpoint
    /// (`WF_flat`, design §6c). Each element is examined by its class's *canonical summand
    /// form* (`summand_form`, §9a), NOT by its union-find representative (that depends on
    /// merge order and is non-canonical — the F1 bug, §0.1):
    ///
    /// - if the child's class is **non-`atomic`** (a pure `op`-sum), splice in that class's
    ///   `min_monomial` children (each by multiplicity), recursively;
    /// - otherwise (the class is `atomic`: referenced as a child, or has a non-AC node) the
    ///   single atom `{class}` is its canonical summand form, so keep the child as a summand.
    ///
    /// `g_buf` already holds `find`'d ids. Preserves §5b: `+{a,b}` used as `neg`'s child is
    /// `atomic`, so it is kept, not flattened. Bounded: a spliced class's `min_monomial` is a
    /// strictly smaller monomial over the existing constants, so the worklist drains.
    fn flatten_ac_children(&mut self, op: Cfg::O) {
        // Move the buffers out to satisfy the borrow checker while reading `self`.
        let mut work = std::mem::take(&mut self.flatten_buf);
        let mut out = std::mem::take(&mut self.g_buf);
        // Seed the worklist with the current children (reverse, so popping preserves
        // a stable order — order doesn't matter for AC but keeps traces readable).
        work.clear();
        work.extend(out.iter().rev().copied());
        out.clear();

        // Safety cap on emitted children. Each splice replaces a child by a strictly
        // smaller monomial, so a well-formed graph drains well under this bound; the cap
        // only guards a degenerate cyclic class, which we must not loop on.
        let cap = 1 + 64 * self.node_count();
        let op_col = self.ops.completion_column(op);
        let mut mset_kids: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        while let Some(g) = work.pop() {
            let cls = self.classes.find_const(g);
            // A child is a pure `op`-sum to splice iff its class is non-atomic AND its
            // canonical summand for `op`'s column (`min_monomial`) is an AC node of this same
            // `op`. Both reads are representative-independent (per-class pool), never
            // `find`-keyed.
            let mut spliced = false;
            if out.len() <= cap
                && let Some(col) = op_col
                && let Some(repr) = self.classes.repr_id(cls)
                && !self.classes.atomic(repr)
                && let Some(min_node) = self.classes.min_monomial(repr, col)
                && self.node_op(min_node) == op
                && matches!(self.node_ref(min_node), NodeRef::MSet(_))
            {
                self.mset_children(min_node, &mut mset_kids);
                for (cg, m) in mset_kids.iter() {
                    let times: u32 = (*m).into();
                    for _ in 0..times {
                        work.push(*cg);
                    }
                }
                spliced = true;
            }
            if !spliced {
                out.push(g);
            }
        }
        debug_assert!(
            out.len() <= cap,
            "flatten_ac_children exceeded cap (degenerate cyclic AC class?)"
        );

        self.g_buf = out;
        self.flatten_buf = work;
    }

    /// Read ACI children (ids only, no multiplicities) into `buf`.
    pub fn set_children(&self, id: Cfg::G, buf: &mut Vec<Cfg::G>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::Set(l) => {
                let n = self.nodes.set.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.set.pool_get(i));
                }
            }
            _ => panic!("set_children: not a Set node"),
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
            NodeRef::Seq(l) => {
                let n = self.nodes.seq.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.seq.pool_get(i));
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
            plus: eg.register_mset("plus", int, int),
            and: eg.register_set("and", int, int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            f4: eg.register_opn("f4", &[int, int, int, int], int),
        };
        (eg, th)
    }

    /// Randomized canonization coverage for the AC count-clamp / identity-drop / degenerate-arity
    /// normal form, with completion OFF (these are canonization facts, not completion — see the
    /// design doc "Canonization, not completion"). The oracle is an *independent* reference
    /// normalizer (`ref_normal`), so `add` is checked against a from-scratch computation of what
    /// the canonical class should be, over random inputs — the coverage the hand-written fixtures
    /// lack. Exercises plain AC, nilpotent order 2 AND order 3, idempotent, and identity, and both
    /// the build path (`add`) and the recanonize path (build distinct, then merge children).
    mod canonize_prop {
        use super::*;
        use crate::registry::{Clamp, OpKind};
        use proptest::prelude::*;
        use std::collections::BTreeMap;

        type Cfg31G = crate::id::ENodeId;

        /// Which AC op a random term uses; each is a distinct registered op sharing one sort.
        #[derive(Clone, Copy, Debug)]
        enum Kind {
            PlainAc,      // + : ℕ counts, no unit
            Nilpotent2,   // xor : count mod 2, unit e
            Nilpotent3,   // nz  : count mod 3, unit e
            Idempotent,   // and : count → 1
            IdentityPlus, // ip  : ℕ counts, unit e dropped
        }

        struct Env {
            eg: EGraph31<NiraLitVal, false, false>,
            atoms: Vec<Cfg31G>, // the 4 leaf classes usable as children
            unit: Cfg31G,       // the declared unit `e`
            plain: OpId,
            nil2: OpId,
            nil3: OpId,
            idem: OpId,
            ident: OpId,
        }

        fn op_of(env: &Env, k: Kind) -> OpId {
            match k {
                Kind::PlainAc => env.plain,
                Kind::Nilpotent2 => env.nil2,
                Kind::Nilpotent3 => env.nil3,
                Kind::Idempotent => env.idem,
                Kind::IdentityPlus => env.ident,
            }
        }

        fn make_env() -> Env {
            let mut eg = EGraph31::<NiraLitVal, false, false>::new();
            let s = eg.intern_sort("E");
            let e_op = eg.register_op0("e", s);
            let unit = eg.add(e_op, &[]);
            // The descriptor's `identity: UnitRef` is only read by the sortcheck resolver; the
            // egraph resolves the unit via `set_unit_node` (below), so pass `None` here. The clamp
            // field is what canonization reads.
            let mk = |eg: &mut EGraph31<NiraLitVal, false, false>, name: &str, clamp: Clamp| {
                eg.register_kind(
                    name,
                    s,
                    OpKind::MSet {
                        arg_sort: s,
                        clamp,
                        identity: None,
                        cancellative: false,
                    },
                )
            };
            let plain = mk(&mut eg, "plus", Clamp::None);
            let nil2 = mk(&mut eg, "xr2", Clamp::Nilpotent { order: 2 });
            let nil3 = mk(&mut eg, "xr3", Clamp::Nilpotent { order: 3 });
            let idem = eg.register_kind(
                "andop",
                s,
                OpKind::Set {
                    arg_sort: s,
                    clamp: Clamp::Idempotent,
                    identity: None,
                    cancellative: false,
                },
            );
            let ident = mk(&mut eg, "ip", Clamp::None);
            eg.set_unit_node(nil2, unit);
            eg.set_unit_node(nil3, unit);
            eg.set_unit_node(ident, unit);
            let a = eg.register_op0("a", s);
            let b = eg.register_op0("b", s);
            let c = eg.register_op0("c", s);
            let d = eg.register_op0("d", s);
            let atoms = vec![
                eg.add(a, &[]),
                eg.add(b, &[]),
                eg.add(c, &[]),
                eg.add(d, &[]),
            ];
            Env {
                eg,
                atoms,
                unit,
                plain,
                nil2,
                nil3,
                idem,
                ident,
            }
        }

        /// Independent reference: the canonical class a well-formed AC term over `children` (given
        /// as current class ids) should land in, computed from scratch — the oracle. Mirrors the
        /// *spec*: coalesce by class → drop unit (ops with an identity) → clamp counts → resolve
        /// degeneracy (empty ⇒ unit, single mult-1 ⇒ that child, else a built node).
        fn ref_normal(env: &mut Env, k: Kind, children: &[Cfg31G]) -> Cfg31G {
            let has_unit = matches!(k, Kind::Nilpotent2 | Kind::Nilpotent3 | Kind::IdentityPlus);
            let unit_cls = env.eg.find(env.unit);
            let mut counts: BTreeMap<u32, u32> = BTreeMap::new();
            for &g in children {
                *counts.entry(env.eg.find(g).raw()).or_insert(0) += 1;
            }
            if has_unit {
                counts.remove(&unit_cls.raw());
            }
            match k {
                Kind::Idempotent => {
                    for v in counts.values_mut() {
                        *v = 1;
                    }
                }
                Kind::Nilpotent2 => counts.retain(|_, v| {
                    *v %= 2;
                    *v != 0
                }),
                Kind::Nilpotent3 => counts.retain(|_, v| {
                    *v %= 3;
                    *v != 0
                }),
                Kind::PlainAc | Kind::IdentityPlus => {}
            }
            let total: u32 = counts.values().sum();
            if total == 0 {
                return env.eg.find(env.unit);
            }
            if counts.len() == 1 && *counts.values().next().unwrap() == 1 {
                return env
                    .eg
                    .find(crate::id::ENodeId::new(*counts.keys().next().unwrap()));
            }
            let mut flat: Vec<Cfg31G> = Vec::new();
            for (cls, cnt) in &counts {
                for _ in 0..*cnt {
                    flat.push(crate::id::ENodeId::new(*cls));
                }
            }
            let op = op_of(env, k);
            env.eg.add(op, &flat)
        }

        fn all_kinds() -> impl Strategy<Value = Kind> {
            prop_oneof![
                Just(Kind::PlainAc),
                Just(Kind::Nilpotent2),
                Just(Kind::Nilpotent3),
                Just(Kind::Idempotent),
                Just(Kind::IdentityPlus),
            ]
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(400))]

            /// `add` must agree with the independent reference normalizer, and be permutation-
            /// invariant (AC). Child index 4 selects the unit, so unit-drop is exercised.
            /// Completion is OFF: this is pure canonization.
            #[test]
            fn add_matches_reference(
                k in all_kinds(),
                idxs in proptest::collection::vec(0usize..5, 1..8),
                perm_seed in any::<u64>(),
            ) {
                let mut env = make_env();
                let pick = |i: usize, env: &Env| if i < 4 { env.atoms[i] } else { env.unit };
                let children: Vec<Cfg31G> = idxs.iter().map(|&i| pick(i, &env)).collect();

                let op = op_of(&env, k);
                let built = env.eg.add(op, &children);
                let expected = ref_normal(&mut env, k, &children);
                prop_assert_eq!(
                    env.eg.find(built),
                    env.eg.find(expected),
                    "add vs reference: kind={:?} idxs={:?}", k, idxs
                );

                let mut shuffled = children.clone();
                let n = shuffled.len();
                for i in 0..n {
                    let j = ((perm_seed.wrapping_mul(6364136223846793005).wrapping_add(i as u64))
                        as usize) % n;
                    shuffled.swap(i, j);
                }
                let built2 = env.eg.add(op, &shuffled);
                prop_assert_eq!(env.eg.find(built), env.eg.find(built2), "permutation invariance");
            }

            /// Recanonize path: build a node with distinct children, merge a pair of children,
            /// rebuild (completion OFF → congruence + canonization only). The node's class must
            /// match the reference recomputed with the merge applied.
            #[test]
            fn recanonize_matches_reference(
                k in all_kinds(),
                idxs in proptest::collection::vec(0usize..4, 2..6),
                mi in 0usize..4,
                mj in 0usize..4,
            ) {
                prop_assume!(mi != mj);
                let mut env = make_env();
                let children: Vec<Cfg31G> = idxs.iter().map(|&i| env.atoms[i]).collect();
                let op = op_of(&env, k);
                let node = env.eg.add(op, &children);

                env.eg.merge(env.atoms[mi], env.atoms[mj]);
                env.eg.rebuild();

                let expected = ref_normal(&mut env, k, &children);
                prop_assert_eq!(
                    env.eg.find(node),
                    env.eg.find(expected),
                    "recanonize vs reference: kind={:?} idxs={:?} merge {}->{}", k, idxs, mi, mj
                );
            }
        }
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

    // S1: the per-class min-monomial pool column for the `plus` op tracks the degree-lex-least
    // `plus`-monomial across merges, and rolls back with the e-graph token. A leaf constant is
    // NOT a `plus`-monomial (it has no `plus` column); merging it in makes the class `atomic`
    // rather than lowering the `plus` column. See design §9a and the pool design in
    // `doc/future/multi-ac-aci-completion-plan.md`.
    #[test]
    fn min_monomial_tracks_least_and_rolls_back() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let c = eg.add(th.w, &[]); // a leaf constant, to merge a sum into
        let s_xy = eg.add(th.plus, &[x, y]); // +{x,y}, size 2
        let s_xyz = eg.add(th.plus, &[x, y, z]); // +{x,y,z}, size 3

        // A fresh `plus` node's class holds itself in the `plus` column; a non-completion
        // constant has no completion column at all.
        assert_eq!(eg.class_min_monomial(s_xy), Some(s_xy));
        assert_eq!(eg.class_min_monomial(c), None);

        // Merge the two sums: the smaller monomial (+{x,y}, size 2) wins over +{x,y,z}.
        eg.merge(s_xy, s_xyz);
        let repr_min = eg.class_min_monomial(s_xy).unwrap();
        assert_eq!(eg.class_repr(repr_min), eg.class_repr(s_xy));
        assert_eq!(repr_min, s_xy, "min_monomial should pick the smaller sum");

        // Snapshot, then merge the leaf constant c in: the class becomes `atomic` (a constant
        // is its normal-form representative), while the `plus` column still holds the sum.
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(c, s_xy);
        assert_eq!(
            eg.class_atomic(c),
            Some(true),
            "merging a constant in makes the class atomic"
        );
        assert_eq!(
            eg.class_min_monomial(s_xy),
            Some(s_xy),
            "the plus column keeps the least sum after the constant merge"
        );

        // Restore: the post-token merge is undone, atomicity reverts.
        eg.restore(token);
        assert_eq!(
            eg.class_min_monomial(s_xy),
            Some(s_xy),
            "min_monomial must roll back with the e-graph token"
        );
        assert_eq!(
            eg.class_atomic(s_xy),
            Some(false),
            "atomicity must roll back with the e-graph token"
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

    // Multiple MSet symbols are now supported (per-op min-monomial pool, step 4): rebuild with
    // two AC ops registered no longer panics. (End-to-end independence is checked by the
    // `ac_complete_multi_mset.egg` fixture.)
    #[test]
    fn cc_allows_two_mset_symbols() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let _plus = eg.register_mset("plus", int, int);
        let _times = eg.register_mset("times", int, int);
        eg.set_cc(true);
        eg.rebuild(); // two MSet ops => allowed, completes each independently
    }

    // One MSet op plus a Set (ACI) op is fine.
    #[test]
    fn cc_allows_one_mset_symbol() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let _plus = eg.register_mset("plus", int, int);
        let _and = eg.register_set("and", int, int);
        eg.set_cc(true);
        eg.rebuild();
    }
}

/// Run all core e-graph tests with both 31-bit and 63-bit configs.
#[cfg(test)]
mod dual_config_tests {
    use crate::canon::{MSetCanon, VarCanon};
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
        MSetCanon: VarCanon<Cfg::G, Cfg::C>,
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
            plus: eg.register_mset("plus", int, int),
            and: eg.register_set("and", int, int),
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
                fn run<$Cfg: EGraphConfig>() where MSetCanon: VarCanon<$Cfg::G, $Cfg::C> $body
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
