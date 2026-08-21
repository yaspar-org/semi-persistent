// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Typed routing table: maps global id `G` → `NodeRef<I>`.
//!
//! Append-only with truncation on backtrack. Two-phase protocol:
//! `reserve()` → probe cache → `finalize()` or `unreserve()`.

use crate::containers::AppendOnlyVec;
use crate::containers::DenseId;
use crate::containers::IndexLike;
use crate::containers::ShrinkPolicy;
use crate::containers::VecToken;

/// Bundle of local DenseId types — one per node kind.
pub trait NodeIds {
    /// Backing word; must match the owning config's `Index`.
    type Index: crate::containers::IndexLike + crate::containers::Tagged;
    type L0: DenseId<Index = Self::Index>;
    type L1: DenseId<Index = Self::Index>;
    type L2: DenseId<Index = Self::Index>;
    type L3: DenseId<Index = Self::Index>;
    type LSPair: DenseId<Index = Self::Index>;
    type LN: DenseId<Index = Self::Index>;
    type LSeq: DenseId<Index = Self::Index>;
    type LMSet: DenseId<Index = Self::Index>;
    type LSet: DenseId<Index = Self::Index>;
    type LLit: DenseId<Index = Self::Index>;
}

/// Typed local id reference — one variant per node kind.
pub enum NodeRef<I: NodeIds> {
    Plain0(I::L0),
    Plain1(I::L1),
    Plain2(I::L2),
    Plain3(I::L3),
    SPair(I::LSPair),
    PlainN(I::LN),
    Seq(I::LSeq),
    MSet(I::LMSet),
    Set(I::LSet),
    Lit(I::LLit),
}

impl<I: NodeIds> Clone for NodeRef<I> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<I: NodeIds> Copy for NodeRef<I> {}

impl<I: NodeIds> PartialEq for NodeRef<I> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Plain0(a), Self::Plain0(b)) => a == b,
            (Self::Plain1(a), Self::Plain1(b)) => a == b,
            (Self::Plain2(a), Self::Plain2(b)) => a == b,
            (Self::Plain3(a), Self::Plain3(b)) => a == b,
            (Self::SPair(a), Self::SPair(b)) => a == b,
            (Self::PlainN(a), Self::PlainN(b)) => a == b,
            (Self::Seq(a), Self::Seq(b)) => a == b,
            (Self::MSet(a), Self::MSet(b)) => a == b,
            (Self::Set(a), Self::Set(b)) => a == b,
            (Self::Lit(a), Self::Lit(b)) => a == b,
            _ => false,
        }
    }
}
impl<I: NodeIds> Eq for NodeRef<I> {}

impl<I: NodeIds> core::fmt::Debug for NodeRef<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Plain0(id) => write!(f, "Plain0({:?})", id),
            Self::Plain1(id) => write!(f, "Plain1({:?})", id),
            Self::Plain2(id) => write!(f, "Plain2({:?})", id),
            Self::Plain3(id) => write!(f, "Plain3({:?})", id),
            Self::SPair(id) => write!(f, "SPair({:?})", id),
            Self::PlainN(id) => write!(f, "PlainN({:?})", id),
            Self::Seq(id) => write!(f, "Seq({:?})", id),
            Self::MSet(id) => write!(f, "MSet({:?})", id),
            Self::Set(id) => write!(f, "Set({:?})", id),
            Self::Lit(id) => write!(f, "Lit({:?})", id),
        }
    }
}

/// Routing table: id `G` → `NodeRef<I>`, backed by the verified append-only
/// semi-persistent vector. Entries are strictly append-only with never-reused
/// ids and restored purely by length rollback — exactly `AppendOnlyVec`'s
/// contract, so it carries the mark/restore proofs for free (no hand
/// `truncate`). `TRACK` matches the owning `NodeStore` (mark/restore are
/// caller errors when `TRACK == false`, container parity).
pub struct TypedRouting<G: DenseId<Index = I::Index>, I: NodeIds, const TRACK: bool = true> {
    /// The routing table's index word is the config's: an entry per node, addressed
    /// by the same `G` whose `Index` this is, so position and id share a width and
    /// `to_index()` bridges them without a conversion.
    entries: AppendOnlyVec<NodeRef<I>, I::Index, TRACK>,
    reserved: bool,
    _phantom: core::marker::PhantomData<G>,
}

impl<G: DenseId<Index = I::Index>, I: NodeIds, const TRACK: bool> Default
    for TypedRouting<G, I, TRACK>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<G: DenseId<Index = I::Index>, I: NodeIds, const TRACK: bool> TypedRouting<G, I, TRACK> {
    pub fn new() -> Self {
        Self {
            entries: AppendOnlyVec::new(),
            reserved: false,
            _phantom: core::marker::PhantomData,
        }
    }

    pub fn reserve(&mut self) -> G {
        assert!(!self.reserved, "already have a reserved id");
        self.reserved = true;
        // `try_new`, not `from_usize`: the table can hold more entries than the id
        // space has ids (`I::Index` spans `2 * id_bound()` for a bit-stealing id), and
        // `from_usize` would mask the excess and hand back an id that already names a
        // different node.
        G::try_new(self.entries.len().as_usize()).expect("routing table exceeds the id space")
    }

    pub fn finalize(&mut self, fresh_id: G, entry: NodeRef<I>) {
        assert!(self.reserved, "no reserved id to finalize");
        assert_eq!(fresh_id.to_index(), self.entries.len());
        self.entries
            .try_push(entry)
            .expect("routing entries exhausted the id index word (reserve checked the id bound)");
        self.reserved = false;
    }

    pub fn unreserve(&mut self) {
        assert!(self.reserved, "no reserved id to cancel");
        self.reserved = false;
    }

    pub fn get(&self, id: G) -> NodeRef<I> {
        *self.entries.get(id.to_index())
    }

    pub fn len(&self) -> usize {
        self.entries.len().as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> RoutingToken {
        RoutingToken {
            entries: self
                .entries
                .try_mark(shrink)
                .expect("routing mark: depth is bounded by the saturation driver"),
        }
    }

    pub fn restore(&mut self, token: RoutingToken) {
        self.entries
            .try_restore(token.entries)
            .expect("routing restore: token minted by this container's own mark");
        self.reserved = false;
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RoutingToken {
    entries: VecToken,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::ENodeId;
    use crate::nodes::*;

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

    type RT = TypedRouting<ENodeId, TestIds, true>;

    #[test]
    fn reserve_finalize() {
        let mut rt = RT::new();
        let id0 = rt.reserve();
        rt.finalize(id0, NodeRef::Plain0(Plain0Id::new(0)));
        let id1 = rt.reserve();
        rt.finalize(id1, NodeRef::MSet(MSetNodeId::new(0)));
        assert_eq!(rt.get(id0), NodeRef::Plain0(Plain0Id::new(0)));
        assert_eq!(rt.get(id1), NodeRef::MSet(MSetNodeId::new(0)));
        assert_eq!(rt.len(), 2);
    }

    #[test]
    fn unreserve() {
        let mut rt = RT::new();
        rt.reserve();
        rt.unreserve();
        assert_eq!(rt.len(), 0);
        let id = rt.reserve();
        rt.finalize(id, NodeRef::Lit(LitNodeId::new(0)));
        assert_eq!(rt.len(), 1);
    }

    #[test]
    fn mark_restore_rolls_back() {
        let mut rt = RT::new();
        let id0 = rt.reserve();
        rt.finalize(id0, NodeRef::Plain1(Plain1Id::new(0)));
        let token = rt.mark(ShrinkPolicy::Never);
        let id1 = rt.reserve();
        rt.finalize(id1, NodeRef::SPair(SPairNodeId::new(0)));
        assert_eq!(rt.len(), 2);
        rt.restore(token);
        assert_eq!(rt.len(), 1);
        assert_eq!(rt.get(id0), NodeRef::Plain1(Plain1Id::new(0)));
    }

    #[test]
    #[should_panic(expected = "already have")]
    fn double_reserve_panics() {
        let mut rt = RT::new();
        rt.reserve();
        rt.reserve();
    }
}
