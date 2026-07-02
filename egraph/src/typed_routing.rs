// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Typed routing table: maps global id `G` → `NodeRef<I>`.
//!
//! Append-only with truncation on backtrack. Two-phase protocol:
//! `reserve()` → probe cache → `finalize()` or `unreserve()`.

use crate::containers::DenseId;
use crate::containers::ShrinkPolicy;

/// Bundle of local DenseId types — one per node kind.
pub trait NodeIds {
    type L0: DenseId;
    type L1: DenseId;
    type L2: DenseId;
    type L3: DenseId;
    type LC: DenseId;
    type LN: DenseId;
    type LA: DenseId;
    type LMSet: DenseId;
    type LSet: DenseId;
    type LLit: DenseId;
}

/// Typed local id reference — one variant per node kind.
pub enum NodeRef<I: NodeIds> {
    Plain0(I::L0),
    Plain1(I::L1),
    Plain2(I::L2),
    Plain3(I::L3),
    C(I::LC),
    PlainN(I::LN),
    A(I::LA),
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
            (Self::C(a), Self::C(b)) => a == b,
            (Self::PlainN(a), Self::PlainN(b)) => a == b,
            (Self::A(a), Self::A(b)) => a == b,
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
            Self::C(id) => write!(f, "C({:?})", id),
            Self::PlainN(id) => write!(f, "PlainN({:?})", id),
            Self::A(id) => write!(f, "A({:?})", id),
            Self::MSet(id) => write!(f, "MSet({:?})", id),
            Self::Set(id) => write!(f, "Set({:?})", id),
            Self::Lit(id) => write!(f, "Lit({:?})", id),
        }
    }
}

pub struct TypedRouting<G: DenseId, I: NodeIds> {
    entries: Vec<NodeRef<I>>,
    reserved: bool,
    _phantom: core::marker::PhantomData<G>,
}

impl<G: DenseId, I: NodeIds> Default for TypedRouting<G, I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<G: DenseId, I: NodeIds> TypedRouting<G, I> {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            reserved: false,
            _phantom: core::marker::PhantomData,
        }
    }

    pub fn reserve(&mut self) -> G {
        assert!(!self.reserved, "already have a reserved id");
        self.reserved = true;
        G::from_usize(self.entries.len())
    }

    pub fn finalize(&mut self, fresh_id: G, entry: NodeRef<I>) {
        assert!(self.reserved, "no reserved id to finalize");
        assert_eq!(fresh_id.to_usize(), self.entries.len());
        self.entries.push(entry);
        self.reserved = false;
    }

    pub fn unreserve(&mut self) {
        assert!(self.reserved, "no reserved id to cancel");
        self.reserved = false;
    }

    pub fn get(&self, id: G) -> NodeRef<I> {
        self.entries[id.to_usize()]
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn truncate(&mut self, len: usize) {
        self.entries.truncate(len);
        self.reserved = false;
    }

    pub fn mark(&mut self, _shrink: ShrinkPolicy) -> RoutingToken {
        RoutingToken {
            len: self.entries.len(),
        }
    }

    pub fn restore(&mut self, token: RoutingToken) {
        self.entries.truncate(token.len);
        self.reserved = false;
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RoutingToken {
    len: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::ENodeId;
    use crate::nodes::*;

    struct TestIds;
    impl NodeIds for TestIds {
        type L0 = Plain0Id;
        type L1 = Plain1Id;
        type L2 = Plain2Id;
        type L3 = Plain3Id;
        type LC = CNodeId;
        type LN = PlainNId;
        type LA = ANodeId;
        type LMSet = MSetNodeId;
        type LSet = SetNodeId;
        type LLit = LitNodeId;
    }

    type RT = TypedRouting<ENodeId, TestIds>;

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
    fn truncate() {
        let mut rt = RT::new();
        let id0 = rt.reserve();
        rt.finalize(id0, NodeRef::Plain1(Plain1Id::new(0)));
        let id1 = rt.reserve();
        rt.finalize(id1, NodeRef::C(CNodeId::new(0)));
        rt.truncate(1);
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
