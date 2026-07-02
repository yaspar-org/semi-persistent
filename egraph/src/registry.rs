// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Sort and operator registries.

use crate::containers::DenseId;
use crate::containers::Map;
use crate::containers::MapToken;
use crate::containers::ShrinkPolicy;
use crate::id::ENodeKind;

/// Opaque token for [`SortRegistry::mark`] / [`SortRegistry::restore`].
#[derive(Clone, Copy, Debug)]
pub struct SortRegistryToken(MapToken);

/// Opaque token for [`OpRegistry::mark`] / [`OpRegistry::restore`].
#[derive(Clone, Copy, Debug)]
pub struct OpRegistryToken(MapToken);

/// Associativity direction for A/MSet/Set operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssocDir {
    Left,
    Right,
    Both,
}

/// How an AC op's normal form bounds a summand's count (design "three independent axes", the
/// 2026-07-01 correction). This is a *unified* axis carried on BOTH `MSet` and `Set` descriptors,
/// independent of the storage partition: the partition is derived from the clamp (`Idempotent →
/// Set`; `None` / `Nilpotent → MSet`). See `doc/future/multi-ac-aci-completion-plan.md`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Clamp {
    /// No count bound: counts stay in ℕ. Plain AC (`+`, `*`). Stored as `MSet`.
    None,
    /// `x∘x = x`: duplicate summands collapse to one (dedup at build via `SetCanon`). `and`, `or`.
    /// Stored as `Set` (bare children); dedup is the correct build/recanonize canonize rule.
    Idempotent,
    /// `x∘x = e` (order 2), or count mod `order` in general: pairs cancel to the unit. `xor`,
    /// `bvxor`. Requires an `identity`. Stored as `MSet` (NOT `Set`): computing count-mod-n needs
    /// the true multiplicity, which the `Set` dedup canonize would destroy at build time; the
    /// mod-n reduction happens at completion instead. The NF counts are {0,1} at order 2 but the
    /// *storage* is MSet regardless of order.
    Nilpotent { order: u8 },
}

/// A deferred reference to an operator's identity (unit) element (design "the unit is a
/// deferred ground term"). Parsed and sort-checked at registration, but the actual e-node is
/// built lazily at first completion use, so registration stays side-effect-free on the e-graph.
#[derive(Clone, Debug)]
pub enum UnitRef {
    /// A literal unit (`0`, `true`, `#b0000`): its surface token and the sort to parse it at.
    Lit { token: String },
    /// A constructed unit (`(zero)`): the parsed surface term, built via the term builder.
    Ctor { term: crate::ast::Term },
}

/// Signature and algebraic kind of a registered operator.
///
/// The `MSet`/`Set` variants carry the resolved algebra beyond the representation: an optional
/// `identity` (unit-drop; applies to either representation) and `cancellative` flag, plus a
/// Set-only `clamp`. The group `inverse` op is deferred until the group facet is implemented
/// (it needs the op-id type, which `OpKind<S>` does not carry); the `:inverse` tag parses and
/// validates but its resolved op is not stored here yet. See
/// `doc/future/multi-ac-aci-tasks.md`.
#[derive(Clone, Debug)]
pub enum OpKind<S: DenseId> {
    Normal {
        arg_sorts: Vec<S>,
    },
    Commutative {
        arg_sorts: [S; 2],
    },
    A {
        arg_sort: S,
        dir: AssocDir,
    },
    /// Associative-commutative, multiset child representation (`(G, mult)`, ℕ counts). Holds
    /// `clamp ∈ {None, Nilpotent}` — plain AC (`None`) or nilpotent (`Nilpotent`, which is stored
    /// MSet to keep true multiplicities for the completion-time mod-n reduction). Never
    /// `Idempotent` (that is the `Set` partition).
    MSet {
        arg_sort: S,
        clamp: Clamp,
        identity: Option<UnitRef>,
        cancellative: bool,
    },
    /// Associative-commutative with {0,1}-bounded counts, set child representation (bare `G`).
    /// `clamp` is always `Idempotent` here (dedup is the build/recanonize canonize rule); the
    /// field is kept for uniformity with `MSet` and the `op_clamp` read.
    Set {
        arg_sort: S,
        clamp: Clamp,
        identity: Option<UnitRef>,
        cancellative: bool,
    },
    Lit,
}

/// Metadata for a registered operator.
#[derive(Clone, Debug)]
pub struct OpInfo<S: DenseId> {
    pub name: String,
    pub return_sort: S,
    pub kind: OpKind<S>,
    pub is_constructor: bool,
}

impl<S: DenseId> OpInfo<S> {
    pub fn canon_class(&self) -> ENodeKind {
        match &self.kind {
            OpKind::Normal { arg_sorts } => match arg_sorts.len() {
                0 => ENodeKind::Plain0,
                1 => ENodeKind::Plain1,
                2 => ENodeKind::Plain2,
                3 => ENodeKind::Plain3,
                _ => ENodeKind::PlainN,
            },
            OpKind::Commutative { .. } => ENodeKind::C,
            OpKind::A { .. } => ENodeKind::A,
            OpKind::MSet { .. } => ENodeKind::MSet,
            OpKind::Set { .. } => ENodeKind::Set,
            OpKind::Lit => ENodeKind::Lit,
        }
    }
}

/// Append-only sort registry backed by `Map`.
#[derive(Debug)]
pub struct SortRegistry<S: DenseId, const TRACK: bool> {
    map: Map<String, (), TRACK>,
    builtin_count: usize,
    concrete_count: usize,
    _phantom: core::marker::PhantomData<S>,
}

impl<S: DenseId, const TRACK: bool> Default for SortRegistry<S, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: DenseId, const TRACK: bool> SortRegistry<S, TRACK> {
    pub fn new() -> Self {
        Self {
            map: Map::new(),
            builtin_count: 0,
            concrete_count: 0,
            _phantom: core::marker::PhantomData,
        }
    }

    pub fn register_builtins(&mut self, sort_names: &[&str]) {
        assert!(
            self.map.is_empty(),
            "register_builtins must be called on empty registry"
        );
        for name in sort_names {
            self.map.insert(name.to_string(), ());
        }
        self.builtin_count = self.map.len();
        self.concrete_count = self.map.len();
    }

    pub fn intern(&mut self, name: &str) -> S {
        if let Some(id) = self.map.id_of(&name.to_owned()) {
            return S::from_usize(id);
        }
        let id = self.map.insert(name.to_owned(), ());
        S::from_usize(id)
    }

    pub fn name(&self, id: S) -> &str {
        self.map.key(id.to_usize())
    }

    pub fn is_builtin(&self, id: S) -> bool {
        id.to_usize() < self.builtin_count
    }

    pub fn is_concrete(&self, id: S) -> bool {
        id.to_usize() < self.concrete_count
    }

    pub fn concrete_count(&self) -> usize {
        self.concrete_count
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn len(&self) -> usize {
        self.map.log_len()
    }

    pub fn id_by_name(&self, name: &str) -> Option<S> {
        self.map.id_of(&name.to_owned()).map(S::from_usize)
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> SortRegistryToken {
        SortRegistryToken(self.map.mark(shrink))
    }

    pub fn restore(&mut self, token: SortRegistryToken) {
        self.map.restore(token.0);
    }
}

/// Append-only operator registry backed by `Map`.
#[derive(Debug)]
pub struct OpRegistry<O: DenseId, S: DenseId, const TRACK: bool> {
    map: Map<String, OpInfo<S>, TRACK>,
    builtin_count: usize,
    concrete_sort_count: usize,
    _phantom: core::marker::PhantomData<O>,
}

impl<O: crate::DenseId, S: DenseId, const TRACK: bool> Default for OpRegistry<O, S, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: crate::DenseId, S: DenseId, const TRACK: bool> OpRegistry<O, S, TRACK> {
    pub fn new() -> Self {
        Self {
            map: Map::new(),
            builtin_count: 0,
            concrete_sort_count: 0,
            _phantom: core::marker::PhantomData,
        }
    }

    /// Register builtin ops from a LitModel. Must be called before any user ops.
    /// Each LitOpDesc becomes a real OpId with OpKind::Normal.
    /// The OpId indices match LitModel::ops() indices for eval lookup.
    pub fn register_builtins<
        L: crate::literal::LitVal,
        M: crate::lit_model::LitModel<Value = L>,
    >(
        &mut self,
        model: &M,
        sorts: &SortRegistry<S, TRACK>,
    ) {
        assert!(
            self.map.is_empty(),
            "register_builtins must be called on empty registry"
        );
        for op_desc in model.ops() {
            let arg_sorts: Vec<S> = op_desc
                .arg_sorts
                .iter()
                .map(|name| {
                    sorts.id_by_name(name).unwrap_or_else(|| {
                        panic!("unknown sort '{name}' in LitOpDesc '{}'", op_desc.name)
                    })
                })
                .collect();
            let ret_sort = sorts.id_by_name(op_desc.ret_sort).unwrap_or_else(|| {
                panic!(
                    "unknown sort '{}' in LitOpDesc '{}'",
                    op_desc.ret_sort, op_desc.name
                )
            });
            self.insert(op_desc.name, ret_sort, OpKind::Normal { arg_sorts });
        }
        // Auto-register a LitNode op for each concrete sort.
        for sort_desc in model.sorts() {
            let sort_id = sorts.id_by_name(sort_desc.name).unwrap();
            let lit_name = format!("@{}", sort_desc.name);
            self.insert(&lit_name, sort_id, OpKind::Lit);
        }
        self.builtin_count = self.map.log_len();
        self.concrete_sort_count = sorts.concrete_count();
    }

    /// Is this a builtin op (from LitModel)?
    pub fn is_builtin(&self, id: O) -> bool {
        id.to_usize() < self.builtin_count
    }

    /// Is this a primitive op (from LitModel::ops(), not a @-prefixed lit wrap)?
    pub fn is_prim_op(&self, id: O) -> bool {
        self.is_builtin(id) && !matches!(self.map.get(id.to_usize()).kind, OpKind::Lit)
    }

    pub fn register(&mut self, name: &str, arg_sorts: &[S], return_sort: S) -> O {
        self.insert(
            name,
            return_sort,
            OpKind::Normal {
                arg_sorts: arg_sorts.to_vec(),
            },
        )
    }

    pub fn register_c(&mut self, name: &str, arg_sorts: [S; 2], return_sort: S) -> O {
        self.insert(name, return_sort, OpKind::Commutative { arg_sorts })
    }

    pub fn register_a(&mut self, name: &str, arg_sort: S, return_sort: S, dir: AssocDir) -> O {
        self.insert(name, return_sort, OpKind::A { arg_sort, dir })
    }

    /// Register a plain AC (multiset) op: no identity, not cancellative. Richer algebra
    /// (identity/cancellative) is set via the property-tag resolver (`register_with_algebra`).
    pub fn register_mset(&mut self, name: &str, arg_sort: S, return_sort: S) -> O {
        self.insert(
            name,
            return_sort,
            OpKind::MSet {
                arg_sort,
                clamp: Clamp::None,
                identity: None,
                cancellative: false,
            },
        )
    }

    /// Register a plain ACI (idempotent set) op: no identity, not cancellative. This is the
    /// `Clamp::Idempotent` case; nilpotent (MSet) comes via the property-tag resolver.
    pub fn register_set(&mut self, name: &str, arg_sort: S, return_sort: S) -> O {
        self.insert(
            name,
            return_sort,
            OpKind::Set {
                arg_sort,
                clamp: Clamp::Idempotent,
                identity: None,
                cancellative: false,
            },
        )
    }

    pub fn register_lit(&mut self, name: &str, return_sort: S) -> O {
        self.insert(name, return_sort, OpKind::Lit)
    }

    /// Register an op from a fully-resolved `OpKind`. Used by the property-tag resolver
    /// (`sortcheck`), which builds the `MSet`/`Set` descriptor (clamp/identity/cancellative)
    /// from the parsed tag set. The plain `register_mset`/`register_set` are the default-filled
    /// special cases of this.
    pub fn register_kind(&mut self, name: &str, return_sort: S, kind: OpKind<S>) -> O {
        self.insert(name, return_sort, kind)
    }

    pub fn info(&self, id: O) -> &OpInfo<S> {
        self.map.get(id.to_usize())
    }

    /// Is this op associative-commutative (`OpKind::MSet`)? Note this is `false`
    /// for ACI ops, which are a distinct kind.
    pub fn is_mset(&self, id: O) -> bool {
        matches!(self.map.get(id.to_usize()).kind, OpKind::MSet { .. })
    }

    /// Iterator over the ids of all registered AC ops. Used by AC congruence
    /// completion to drive the per-AC-op critical-pair pass (see
    /// `doc/future/ac-congruence-completeness-plan.md`). Excludes ACI ops.
    pub fn mset_ops(&self) -> impl Iterator<Item = O> + '_ {
        self.map
            .iter()
            .enumerate()
            .filter(|(_, (_, info))| matches!(info.kind, OpKind::MSet { .. }))
            .map(|(i, _)| O::from_usize(i))
    }

    /// Number of registered `OpKind::MSet` ops (excludes Set). Until the per-op
    /// `min_monomial` pool lands, completion supports exactly one MSet symbol (the single
    /// per-class slot holds one op's minimal monomial); `rebuild` checks this.
    pub fn mset_op_count(&self) -> usize {
        self.mset_ops().count()
    }

    /// Is this op a `Set` (idempotent/nilpotent) op?
    pub fn is_set(&self, id: O) -> bool {
        matches!(self.map.get(id.to_usize()).kind, OpKind::Set { .. })
    }

    /// Iterator over the ids of all registered `Set` ops (idempotent or nilpotent), in
    /// registration order. The Set analogue of [`mset_ops`](Self::mset_ops).
    pub fn set_ops(&self) -> impl Iterator<Item = O> + '_ {
        self.map
            .iter()
            .enumerate()
            .filter(|(_, (_, info))| matches!(info.kind, OpKind::Set { .. }))
            .map(|(i, _)| O::from_usize(i))
    }

    /// Number of registered `Set` ops.
    pub fn set_op_count(&self) -> usize {
        self.set_ops().count()
    }

    /// The ordered list of *completion* ops (MSet then Set, each in registration order). This
    /// is the column → op reference array for the per-op `min_monomial` pool (design "the
    /// column → op reference array"): `completion_ops()[k]` is the op owning pool column `k`,
    /// and its length is the fixed row width `nb_completion`. Registration order is stable
    /// (the backing `Map` is append-only, never renumbered), so a column's meaning is fixed
    /// for the run.
    pub fn completion_ops(&self) -> Vec<O> {
        let mut v: Vec<O> = self.mset_ops().collect();
        v.extend(self.set_ops());
        v
    }

    /// Number of completion ops (`nb_completion` = MSet + Set), the `min_monomial` pool row
    /// width.
    pub fn completion_op_count(&self) -> usize {
        self.mset_op_count() + self.set_op_count()
    }

    /// The pool column index of a completion op, or `None` if `id` is not an MSet/Set op.
    /// O(nb_completion) scan of [`completion_ops`](Self::completion_ops); `nb_completion` is
    /// tiny (a handful), and the pool builder caches the array per round rather than calling
    /// this in a hot loop.
    pub fn completion_column(&self, id: O) -> Option<usize> {
        self.completion_ops().iter().position(|&o| o == id)
    }

    pub fn id_by_name(&self, name: &str) -> Option<O> {
        self.map.id_of(&name.to_owned()).map(O::from_usize)
    }

    pub fn lit_op_for_sort(&self, sort: S) -> Option<O> {
        self.map
            .iter()
            .enumerate()
            .find(|(_, (_, info))| matches!(info.kind, OpKind::Lit) && info.return_sort == sort)
            .map(|(i, _)| O::from_usize(i))
    }

    /// Find a unary op that takes `from` and returns `to` (e.g. ILit: IBig → IExpr).
    pub fn find_lift_op(&self, from: S, to: S) -> Option<O> {
        self.map
            .iter()
            .enumerate()
            .find(|(_, (_, info))| {
                info.return_sort == to
                    && matches!(&info.kind, OpKind::Normal { arg_sorts } if arg_sorts.len() == 1 && arg_sorts[0] == from)
            })
            .map(|(i, _)| O::from_usize(i))
    }

    fn insert(&mut self, name: &str, return_sort: S, kind: OpKind<S>) -> O {
        assert!(
            !self.map.contains_key(&name.to_owned()),
            "operator '{name}' already registered"
        );
        if self.builtin_count > 0 && return_sort.to_usize() < self.concrete_sort_count {
            panic!(
                "operator '{name}' cannot return concrete sort (index {})",
                return_sort.to_usize()
            );
        }
        let id = self.map.insert(
            name.to_owned(),
            OpInfo {
                name: name.to_owned(),
                return_sort,
                kind,
                is_constructor: false,
            },
        );
        O::from_usize(id)
    }

    pub fn set_constructor(&mut self, id: O) {
        let info = self.map.get_mut(id.to_usize());
        info.is_constructor = true;
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> OpRegistryToken {
        OpRegistryToken(self.map.mark(shrink))
    }

    pub fn restore(&mut self, token: OpRegistryToken) {
        self.map.restore(token.0);
    }
}

// ---------------------------------------------------------------------------
// Rule registry
// ---------------------------------------------------------------------------

/// Opaque token for [`RuleRegistry::mark`] / [`RuleRegistry::restore`].
#[derive(Clone, Copy, Debug)]
pub struct RuleRegistryToken(MapToken);

/// Metadata for a registered rewrite rule.
#[derive(Clone, Debug)]
pub struct RuleInfo {
    pub name: String,
    pub lhs: String,
    pub rhs: String,
}

/// Append-only rule registry backed by `Map`.
pub struct RuleRegistry<const TRACK: bool> {
    map: Map<String, RuleInfo, TRACK>,
}

impl<const TRACK: bool> Default for RuleRegistry<TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const TRACK: bool> RuleRegistry<TRACK> {
    pub fn new() -> Self {
        Self { map: Map::new() }
    }

    pub fn register(&mut self, name: &str, lhs: &str, rhs: &str) -> crate::id::RuleId {
        let id = self.map.insert(
            name.to_owned(),
            RuleInfo {
                name: name.to_owned(),
                lhs: lhs.to_owned(),
                rhs: rhs.to_owned(),
            },
        );
        crate::id::RuleId::from_usize(id)
    }

    pub fn info(&self, id: crate::id::RuleId) -> &RuleInfo {
        self.map.get(id.to_usize())
    }

    pub fn name(&self, id: crate::id::RuleId) -> &str {
        self.map.key(id.to_usize())
    }

    pub fn len(&self) -> usize {
        self.map.log_len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn id_by_name(&self, name: &str) -> Option<crate::id::RuleId> {
        self.map
            .id_of(&name.to_owned())
            .map(crate::id::RuleId::from_usize)
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> RuleRegistryToken {
        RuleRegistryToken(self.map.mark(shrink))
    }

    pub fn restore(&mut self, token: RuleRegistryToken) {
        self.map.restore(token.0);
    }
}

// ---------------------------------------------------------------------------
// Axiom registry
// ---------------------------------------------------------------------------

/// Opaque token for [`AxiomRegistry::mark`] / [`AxiomRegistry::restore`].
#[derive(Clone, Copy, Debug)]
pub struct AxiomRegistryToken(MapToken);

/// Metadata for a registered axiom (user-asserted equality).
#[derive(Clone, Debug)]
pub struct AxiomInfo<G: Copy> {
    pub name: String,
    pub lhs: G,
    pub rhs: G,
}

/// Append-only axiom registry backed by `Map`.
pub struct AxiomRegistry<G: Copy + DenseId, const TRACK: bool> {
    map: Map<String, AxiomInfo<G>, TRACK>,
}

impl<G: Copy + DenseId, const TRACK: bool> Default for AxiomRegistry<G, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<G: Copy + DenseId, const TRACK: bool> AxiomRegistry<G, TRACK> {
    pub fn new() -> Self {
        Self { map: Map::new() }
    }

    pub fn register(&mut self, name: &str, lhs: G, rhs: G) -> crate::id::AxiomId {
        let id = self.map.insert(
            name.to_owned(),
            AxiomInfo {
                name: name.to_owned(),
                lhs,
                rhs,
            },
        );
        crate::id::AxiomId::from_usize(id)
    }

    pub fn info(&self, id: crate::id::AxiomId) -> &AxiomInfo<G> {
        self.map.get(id.to_usize())
    }

    pub fn name(&self, id: crate::id::AxiomId) -> &str {
        self.map.key(id.to_usize())
    }

    pub fn len(&self) -> usize {
        self.map.log_len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> AxiomRegistryToken {
        AxiomRegistryToken(self.map.mark(shrink))
    }

    pub fn restore(&mut self, token: AxiomRegistryToken) {
        self.map.restore(token.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{OpId, SortId};

    type SR = SortRegistry<SortId, false>;
    type OR = OpRegistry<OpId, SortId, false>;

    #[test]
    fn builtin_sorts() {
        let mut r = SR::new();
        r.register_builtins(&["Bool", "Int", "Real"]);
        assert_eq!(r.name(SortId::new(0)), "Bool");
        assert_eq!(r.name(SortId::new(1)), "Int");
        assert_eq!(r.name(SortId::new(2)), "Real");
        assert!(r.is_builtin(SortId::new(0)));
        assert!(r.is_builtin(SortId::new(2)));
        let user = r.intern("BitVec");
        assert!(!r.is_builtin(user));
    }

    #[test]
    fn sort_intern_dedup() {
        let mut r = SR::new();
        let a = r.intern("BitVec");
        let b = r.intern("BitVec");
        assert_eq!(a, b);
    }

    #[test]
    fn canon_class_all_kinds() {
        let mut sorts = SR::new();
        let bool_sort = sorts.intern("Bool");
        let int_sort = sorts.intern("Int");

        let mut ops = OR::new();
        let lit = ops.register_lit("BLit", bool_sort);
        let not = ops.register("Not", &[bool_sort], bool_sort);
        let ite = ops.register("ITE", &[bool_sort, int_sort, int_sort], int_sort);
        let eq = ops.register_c("Eq", [int_sort, int_sort], bool_sort);
        let sub = ops.register_a("Sub", int_sort, int_sort, AssocDir::Left);
        let add = ops.register_mset("Add", int_sort, int_sort);
        let and = ops.register_set("And", bool_sort, bool_sort);

        assert_eq!(ops.info(lit).canon_class(), ENodeKind::Lit);
        assert_eq!(ops.info(not).canon_class(), ENodeKind::Plain1);
        assert_eq!(ops.info(ite).canon_class(), ENodeKind::Plain3);
        assert_eq!(ops.info(eq).canon_class(), ENodeKind::C);
        assert_eq!(ops.info(sub).canon_class(), ENodeKind::A);
        assert_eq!(ops.info(add).canon_class(), ENodeKind::MSet);
        assert_eq!(ops.info(and).canon_class(), ENodeKind::Set);
    }

    #[test]
    fn plain0_for_constants() {
        let int_sort = SortId::new(1);
        let mut ops = OR::new();
        let zero = ops.register("Zero", &[], int_sort);
        assert_eq!(ops.info(zero).canon_class(), ENodeKind::Plain0);
    }

    #[test]
    fn plainn_for_high_arity() {
        let int_sort = SortId::new(1);
        let mut ops = OR::new();
        let f = ops.register("F4", &[int_sort; 4], int_sort);
        assert_eq!(ops.info(f).canon_class(), ENodeKind::PlainN);
    }

    #[test]
    fn id_by_name() {
        let int_sort = SortId::new(1);
        let mut ops = OR::new();
        let add = ops.register_mset("Add", int_sort, int_sort);
        assert_eq!(ops.id_by_name("Add"), Some(add));
        assert_eq!(ops.id_by_name("nonexistent"), None);
    }

    #[test]
    #[should_panic(expected = "already registered")]
    fn duplicate_name_panics() {
        let int_sort = SortId::new(1);
        let mut ops = OR::new();
        ops.register_mset("Add", int_sort, int_sort);
        ops.register_mset("Add", int_sort, int_sort);
    }

    #[test]
    fn mset_ops_lists_only_mset() {
        let mut sorts = SR::new();
        let bool_sort = sorts.intern("Bool");
        let int_sort = sorts.intern("Int");

        let mut ops = OR::new();
        ops.register("Not", &[bool_sort], bool_sort); // Normal
        ops.register_c("Eq", [int_sort, int_sort], bool_sort); // Commutative
        ops.register_a("Sub", int_sort, int_sort, AssocDir::Left); // A
        let add = ops.register_mset("Add", int_sort, int_sort); // AC
        let mul = ops.register_mset("Mul", int_sort, int_sort); // AC
        ops.register_set("And", bool_sort, bool_sort); // ACI — must be excluded

        // mset_ops yields exactly the two MSet ids, and is_mset agrees per-op.
        let mut mset_ids: Vec<OpId> = ops.mset_ops().collect();
        mset_ids.sort();
        assert_eq!(mset_ids, vec![add, mul]);

        assert!(ops.is_mset(add));
        assert!(ops.is_mset(mul));
        // ACI is a distinct kind — not AC.
        assert!(!ops.is_mset(ops.id_by_name("And").unwrap()));
        assert!(!ops.is_mset(ops.id_by_name("Sub").unwrap()));
        assert!(!ops.is_mset(ops.id_by_name("Not").unwrap()));
    }

    #[test]
    fn mset_ops_empty_when_none_registered() {
        let int_sort = SortId::new(1);
        let mut ops = OR::new();
        ops.register("F", &[int_sort], int_sort);
        assert_eq!(ops.mset_ops().count(), 0);
    }

    #[test]
    fn completion_ops_mset_then_set_in_registration_order() {
        let mut sorts = SR::new();
        let bool_sort = sorts.intern("Bool");
        let int_sort = sorts.intern("Int");

        let mut ops = OR::new();
        let add = ops.register_mset("Add", int_sort, int_sort);
        let and = ops.register_set("And", bool_sort, bool_sort);
        let mul = ops.register_mset("Mul", int_sort, int_sort);
        let or = ops.register_set("Or", bool_sort, bool_sort);
        ops.register("Not", &[bool_sort], bool_sort); // non-completion op, excluded

        // completion_ops = all MSet (registration order) then all Set (registration order).
        assert_eq!(ops.completion_ops(), vec![add, mul, and, or]);
        assert_eq!(ops.completion_op_count(), 4);
        assert_eq!(ops.set_op_count(), 2);
        assert_eq!(ops.mset_op_count(), 2);

        // column() is the position in that array; non-completion ops have none.
        assert_eq!(ops.completion_column(add), Some(0));
        assert_eq!(ops.completion_column(mul), Some(1));
        assert_eq!(ops.completion_column(and), Some(2));
        assert_eq!(ops.completion_column(or), Some(3));
        assert_eq!(ops.completion_column(ops.id_by_name("Not").unwrap()), None);

        // is_set agrees.
        assert!(ops.is_set(and) && ops.is_set(or));
        assert!(!ops.is_set(add));
    }

    #[test]
    fn completion_ops_empty_when_none() {
        let int_sort = SortId::new(1);
        let mut ops = OR::new();
        ops.register("F", &[int_sort], int_sort);
        assert_eq!(ops.completion_ops(), Vec::<OpId>::new());
        assert_eq!(ops.completion_op_count(), 0);
    }
}
