// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Generic node store facade — caches + typed routing, parameterized by id types.

use std::hash::Hash;

use crate::caches::*;
use crate::canon::{CCanon, MSetCanon, OrderedCanon, PlainCanon, SetCanon, VarCanon};
use crate::containers::DenseId;
use crate::containers::ShrinkPolicy;
use crate::containers::Tagged;
use crate::multiplicity::Multiplicity;
use crate::registry::{Clamp, OpKind, OpRegistry};
use crate::typed_routing::{NodeIds, NodeRef, RoutingToken, TypedRouting};

/// Map an MSet op's descriptor `Clamp` to the canonizer's [`crate::canon::MSetClamp`]. An MSet op
/// carries `Clamp::None` (plain AC) or `Clamp::Nilpotent` (`Idempotent` is the Set partition, and
/// is never on an MSet op — treat defensively as no clamp). Keeps `canon.rs` free of a `registry`
/// dependency: the store, which has the op registry, does the mapping.
fn mset_clamp_of<O: DenseId, S: DenseId, const TRACK: bool>(
    ops: &OpRegistry<O, S, TRACK>,
    op: O,
) -> crate::canon::MSetClamp {
    match ops.info(op).kind {
        OpKind::MSet {
            clamp: Clamp::Nilpotent { order },
            ..
        } => crate::canon::MSetClamp::Nilpotent { order },
        _ => crate::canon::MSetClamp::None,
    }
}

pub type MSetChild<G> = (G, Multiplicity);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Added<G> {
    Existing(G),
    Fresh(G),
}

impl<G: Copy> Added<G> {
    pub fn id(&self) -> G {
        match *self {
            Added::Existing(id) | Added::Fresh(id) => id,
        }
    }
    pub fn is_fresh(&self) -> bool {
        matches!(self, Added::Fresh(_))
    }
}

pub struct NodeStore<
    G: DenseId,
    O: DenseId,
    V: DenseId,
    C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug,
    I: NodeIds,
    const TRACK: bool = true,
    const PROOFS: bool = false,
> {
    routing: TypedRouting<G, I>,
    pub plain0: FixedArityCache<G, O, I::L0, 0, TRACK, PROOFS>,
    pub plain1: FixedArityCache<G, O, I::L1, 1, TRACK, PROOFS>,
    pub plain2: FixedArityCache<G, O, I::L2, 2, TRACK, PROOFS>,
    pub plain3: FixedArityCache<G, O, I::L3, 3, TRACK, PROOFS>,
    pub spair: FixedArityCache<G, O, I::LSPair, 2, TRACK, PROOFS>,
    pub plain_n: VariableArityCache<G, O, G, I::LN, TRACK, PROOFS>,
    pub seq: VariableArityCache<G, O, G, I::LSeq, TRACK, PROOFS>,
    pub mset: VariableArityCache<G, O, C, I::LMSet, TRACK, PROOFS>,
    pub set: VariableArityCache<G, O, G, I::LSet, TRACK, PROOFS>,
    pub lit: LitCache<G, O, V, I::LLit, TRACK>,
}

impl<G, O, V, C, I, const TRACK: bool, const PROOFS: bool> Default
    for NodeStore<G, O, V, C, I, TRACK, PROOFS>
where
    G: DenseId + Hash,
    O: DenseId + Hash,
    V: DenseId + Hash,
    C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug,
    I: NodeIds,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<G, O, V, C, I, const TRACK: bool, const PROOFS: bool> NodeStore<G, O, V, C, I, TRACK, PROOFS>
where
    G: DenseId + Hash,
    O: DenseId + Hash,
    V: DenseId + Hash,
    C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug,
    I: NodeIds,
{
    pub fn new() -> Self {
        Self {
            routing: TypedRouting::new(),
            plain0: FixedArityCache::new(),
            plain1: FixedArityCache::new(),
            plain2: FixedArityCache::new(),
            plain3: FixedArityCache::new(),
            spair: FixedArityCache::new(),
            plain_n: VariableArityCache::new(),
            seq: VariableArityCache::new(),
            mset: VariableArityCache::new(),
            set: VariableArityCache::new(),
            lit: LitCache::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.routing.len()
    }
    pub fn is_empty(&self) -> bool {
        self.routing.is_empty()
    }
    pub fn routing(&self) -> &TypedRouting<G, I> {
        &self.routing
    }

    // -----------------------------------------------------------------------
    // High-level dispatch
    // -----------------------------------------------------------------------

    pub fn add<S: crate::DenseId>(
        &mut self,
        op: O,
        children: &[G],
        ops: &OpRegistry<O, S, TRACK>,
    ) -> Added<G> {
        match ops.info(op).kind {
            OpKind::Normal { .. } => match children.len() {
                0 => self.add_plain0(op),
                1 => self.add_plain1(op, children[0]),
                2 => self.add_plain2(op, [children[0], children[1]]),
                3 => self.add_plain3(op, [children[0], children[1], children[2]]),
                _ => self.add_plain_n(op, children),
            },
            OpKind::Commutative { .. } => {
                assert_eq!(children.len(), 2);
                let pair = if children[0].to_usize() <= children[1].to_usize() {
                    [children[0], children[1]]
                } else {
                    [children[1], children[0]]
                };
                self.add_c(op, pair)
            }
            OpKind::A { .. } => self.add_a(op, children),
            OpKind::MSet { .. } => panic!("use add_mset with pre-canonicalized children"),
            OpKind::Set { .. } => panic!("use add_set with pre-canonicalized children"),
            OpKind::Lit => panic!("use add_lit for literal operators"),
        }
    }

    // -----------------------------------------------------------------------
    // Per-kind insertion
    // -----------------------------------------------------------------------

    pub fn add_plain0(&mut self, op: O) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.plain0.probe_or_insert(fresh, op, []) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::Plain0(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_plain1(&mut self, op: O, child: G) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.plain1.probe_or_insert(fresh, op, [child]) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::Plain1(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_plain2(&mut self, op: O, children: [G; 2]) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.plain2.probe_or_insert(fresh, op, children) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::Plain2(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_plain3(&mut self, op: O, children: [G; 3]) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.plain3.probe_or_insert(fresh, op, children) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::Plain3(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_c(&mut self, op: O, children: [G; 2]) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.spair.probe_or_insert(fresh, op, children) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::SPair(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_plain_n(&mut self, op: O, children: &[G]) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.plain_n.probe_or_insert(fresh, op, children) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::PlainN(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_a(&mut self, op: O, children: &[G]) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.seq.probe_or_insert(fresh, op, children) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::Seq(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_mset(&mut self, op: O, children: &[C]) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.mset.probe_or_insert(fresh, op, children) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::MSet(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_set(&mut self, op: O, children: &[G]) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.set.probe_or_insert(fresh, op, children) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::Set(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    pub fn add_lit(&mut self, op: O, lit: V) -> Added<G> {
        let fresh = self.routing.reserve();
        match self.lit.probe_or_insert(fresh, op, lit) {
            InsertResult::Hit { global_id } => {
                self.routing.unreserve();
                Added::Existing(global_id)
            }
            InsertResult::Inserted { local_id } => {
                self.routing.finalize(fresh, NodeRef::Lit(local_id));
                Added::Fresh(fresh)
            }
        }
    }

    // -----------------------------------------------------------------------
    // Recanonize
    // -----------------------------------------------------------------------

    /// Recanonize a single node's children after a union. Dispatches to the
    /// appropriate cache with the correct canonization strategy.
    /// `g_buf` — scratch for PlainN/A/ACI (child type G).
    /// `mset_buf` — scratch for MSet children (child type `C` = `(G, mult)`).
    /// `collisions` — destination for collision pairs to push onto worklist.
    /// `unit_of` resolves an op to its identity (unit) **class** as of this rebuild
    /// (the caller composes the per-op unit node with `find`), or `None` for ops without
    /// a declared identity. It feeds the class-relative unit-drop law into MSet/Set
    /// canonization, so a summand that merged into the unit's class is dropped on
    /// recanonize exactly as at build.
    pub fn recanonize_node<S: crate::DenseId>(
        &mut self,
        id: G,
        find: impl Fn(G) -> G,
        unit_of: impl Fn(O) -> Option<G>,
        g_buf: &mut Vec<G>,
        mset_buf: &mut Vec<C>,
        collisions: &mut Vec<(G, G)>,
        touched: &mut Vec<G>,
        ops: &OpRegistry<O, S, TRACK>,
    ) where
        MSetCanon: VarCanon<G, C>,
    {
        use crate::canon::CanonMode;
        match self.routing.get(id) {
            NodeRef::Plain0(_) => {}
            NodeRef::Plain1(l) => self
                .plain1
                .recanonize_node::<PlainCanon>(l, &find, collisions, touched),
            NodeRef::Plain2(l) => self
                .plain2
                .recanonize_node::<PlainCanon>(l, &find, collisions, touched),
            NodeRef::Plain3(l) => self
                .plain3
                .recanonize_node::<PlainCanon>(l, &find, collisions, touched),
            NodeRef::SPair(l) => self
                .spair
                .recanonize_node::<CCanon>(l, &find, collisions, touched),
            NodeRef::PlainN(l) => self.plain_n.recanonize_node::<OrderedCanon>(
                l,
                &find,
                g_buf,
                collisions,
                touched,
                CanonMode::PLAIN,
            ),
            NodeRef::Seq(l) => self.seq.recanonize_node::<OrderedCanon>(
                l,
                &find,
                g_buf,
                collisions,
                touched,
                CanonMode::PLAIN,
            ),
            NodeRef::MSet(l) => {
                // Fetch the op's count clamp from the registry before canonizing this slice, so
                // canonize establishes the full canonical form (find+sort+coalesce + mod-n clamp)
                // in one step. The node's op is known here (we route on it), matching the `add`
                // path that already takes `&ops`.
                let op = self.mset.get(l).op();
                let mode = CanonMode {
                    clamp: mset_clamp_of(ops, op),
                    unit: unit_of(op),
                };
                self.mset
                    .recanonize_node::<MSetCanon>(l, &find, mset_buf, collisions, touched, mode)
            }
            NodeRef::Set(l) => {
                let op = self.set.get(l).op();
                let mode = CanonMode {
                    clamp: crate::canon::MSetClamp::None,
                    unit: unit_of(op),
                };
                self.set
                    .recanonize_node::<SetCanon>(l, &find, g_buf, collisions, touched, mode)
            }
            NodeRef::Lit(_) => {}
        }
    }

    // -----------------------------------------------------------------------
    // History lookup (PROOFS=true)
    // -----------------------------------------------------------------------

    /// Retrieve original (pre-recanonize) children of a node.
    /// Appends to `g_out` for all kinds except AC (which appends to `mset_out`).
    /// Returns true if history was found.
    pub fn original_children(&self, id: G, g_out: &mut Vec<G>, mset_out: &mut Vec<C>) -> bool
    where
        MSetCanon: VarCanon<G, C>,
    {
        match self.routing.get(id) {
            NodeRef::Plain0(_) | NodeRef::Lit(_) => false,
            NodeRef::Plain1(_) => {
                if let Some(c) = self.plain1.original_children(id) {
                    g_out.extend_from_slice(&c);
                    true
                } else {
                    false
                }
            }
            NodeRef::Plain2(_) => {
                if let Some(c) = self.plain2.original_children(id) {
                    g_out.extend_from_slice(&c);
                    true
                } else {
                    false
                }
            }
            NodeRef::Plain3(_) => {
                if let Some(c) = self.plain3.original_children(id) {
                    g_out.extend_from_slice(&c);
                    true
                } else {
                    false
                }
            }
            NodeRef::SPair(_) => {
                if let Some(c) = self.spair.original_children(id) {
                    g_out.extend_from_slice(&c);
                    true
                } else {
                    false
                }
            }
            NodeRef::PlainN(_) => self.plain_n.original_children(id, g_out),
            NodeRef::Seq(_) => self.seq.original_children(id, g_out),
            NodeRef::MSet(_) => self.mset.original_children(id, mset_out),
            NodeRef::Set(_) => self.set.original_children(id, g_out),
        }
    }

    // -----------------------------------------------------------------------
    // Semi-persistence
    // -----------------------------------------------------------------------

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> NodeStoreToken {
        NodeStoreToken {
            routing: self.routing.mark(shrink),
            plain0: self.plain0.mark(shrink),
            plain1: self.plain1.mark(shrink),
            plain2: self.plain2.mark(shrink),
            plain3: self.plain3.mark(shrink),
            spair: self.spair.mark(shrink),
            plain_n: self.plain_n.mark(shrink),
            seq: self.seq.mark(shrink),
            mset: self.mset.mark(shrink),
            set: self.set.mark(shrink),
            lit: self.lit.mark(shrink),
        }
    }

    pub fn restore(&mut self, token: NodeStoreToken) {
        self.routing.restore(token.routing);
        self.plain0.restore(token.plain0);
        self.plain1.restore(token.plain1);
        self.plain2.restore(token.plain2);
        self.plain3.restore(token.plain3);
        self.spair.restore(token.spair);
        self.plain_n.restore(token.plain_n);
        self.seq.restore(token.seq);
        self.mset.restore(token.mset);
        self.set.restore(token.set);
        self.lit.restore(token.lit);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct NodeStoreToken {
    routing: RoutingToken,
    plain0: CacheToken,
    plain1: CacheToken,
    plain2: CacheToken,
    plain3: CacheToken,
    spair: CacheToken,
    plain_n: PoolCacheToken,
    seq: PoolCacheToken,
    mset: PoolCacheToken,
    set: PoolCacheToken,
    lit: CacheToken,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{ENodeId, OpId, SortId};
    use crate::nodes::*;
    use crate::registry::SortRegistry;

    struct TestIds;
    impl NodeIds for TestIds {
        type Index = u32;
        type L0 = Plain0Id;
        type L1 = Plain1Id;
        type L2 = Plain2Id;
        type L3 = Plain3Id;
        type LSPair = SPairNodeId;
        type LN = PlainNId;
        type LSeq = SeqNodeId;
        type LMSet = MSetNodeId;
        type LSet = SetNodeId;
        type LLit = LitNodeId;
    }

    type NS = NodeStore<ENodeId, OpId, LitValId, MSetChild<ENodeId>, TestIds, false>;

    fn setup() -> (NS, OpRegistry<OpId, SortId, false>) {
        let mut sorts: SortRegistry<SortId, false> = SortRegistry::new();
        let int = sorts.intern("Int");
        let bool_ = sorts.intern("Bool");

        let mut ops: OpRegistry<OpId, SortId, false> = OpRegistry::new();
        ops.register("Zero", &[], int);
        ops.register("Neg", &[int], int);
        ops.register("Div", &[int, int], int);
        ops.register("ITE", &[bool_, int, int], int);
        ops.register_c("Eq", [int, int], bool_);
        ops.register_a("Sub", int, int, crate::registry::AssocDir::Left);
        ops.register_mset("Add", int, int);
        ops.register_set("And", bool_, bool_);
        ops.register_lit("ILit", int);

        (NS::new(), ops)
    }

    #[test]
    fn add_and_dedup() {
        let (mut ns, ops) = setup();
        let zero = ops.id_by_name("Zero").unwrap();

        let a = ns.add(zero, &[], &ops);
        assert!(a.is_fresh());
        let b = ns.add(zero, &[], &ops);
        assert!(!b.is_fresh());
        assert_eq!(a.id(), b.id());
        assert_eq!(ns.len(), 1);
    }

    #[test]
    fn commutative_dedup() {
        let (mut ns, ops) = setup();
        let eq = ops.id_by_name("Eq").unwrap();
        let ilit = ops.id_by_name("ILit").unwrap();

        let a = ns.add_lit(ilit, LitValId::new(0));
        let b = ns.add_lit(ilit, LitValId::new(1));

        let e1 = ns.add(eq, &[a.id(), b.id()], &ops);
        let e2 = ns.add(eq, &[b.id(), a.id()], &ops);
        assert!(e1.is_fresh());
        assert!(!e2.is_fresh());
        assert_eq!(e1.id(), e2.id());
    }

    #[test]
    fn routing_roundtrip() {
        let (mut ns, ops) = setup();
        let neg = ops.id_by_name("Neg").unwrap();
        let ilit = ops.id_by_name("ILit").unwrap();

        let lit = ns.add_lit(ilit, LitValId::new(42));
        let n = ns.add(neg, &[lit.id()], &ops);
        let r = ns.routing().get(n.id());
        assert!(matches!(r, NodeRef::Plain1(_)));
    }

    #[test]
    fn recanonize_plain_collision() {
        let (mut ns, ops) = setup();
        let neg = ops.id_by_name("Neg").unwrap();
        let ilit = ops.id_by_name("ILit").unwrap();

        let a = ns.add_lit(ilit, LitValId::new(0)).id(); // e0
        let b = ns.add_lit(ilit, LitValId::new(1)).id(); // e1
        let na = ns.add(neg, &[a], &ops).id(); // neg(e0) = e2
        let nb = ns.add(neg, &[b], &ops).id(); // neg(e1) = e3

        // simulate union(a, b) → find(b) = a
        let mut g_buf = Vec::new();
        let mut mset_buf = Vec::new();
        let mut collisions = Vec::new();
        ns.recanonize_node(
            nb,
            |g| if g == b { a } else { g },
            |_op| None,
            &mut g_buf,
            &mut mset_buf,
            &mut collisions,
            &mut Vec::new(),
            &ops,
        );
        // neg(e1) became neg(e0) → collision with na
        assert_eq!(collisions, vec![(nb, na)]);
    }

    #[test]
    fn recanonize_no_change() {
        let (mut ns, ops) = setup();
        let neg = ops.id_by_name("Neg").unwrap();
        let ilit = ops.id_by_name("ILit").unwrap();

        let a = ns.add_lit(ilit, LitValId::new(0)).id();
        let _na = ns.add(neg, &[a], &ops).id();

        let mut g_buf = Vec::new();
        let mut mset_buf = Vec::new();
        let mut collisions = Vec::new();
        ns.recanonize_node(
            _na,
            |g| g,
            |_op| None,
            &mut g_buf,
            &mut mset_buf,
            &mut collisions,
            &mut Vec::new(),
            &ops,
        );
        assert!(collisions.is_empty());
    }
}
