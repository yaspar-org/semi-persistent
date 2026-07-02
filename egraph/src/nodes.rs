// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Concrete local DenseId types (one per node kind) and DefaultNodeIds.

// ---------------------------------------------------------------------------
// Local DenseId types — one per store
// ---------------------------------------------------------------------------

semi_persistent_containers::define_id31! {
    pub struct Plain0Id / StoredPlain0Id, "p0";
}
semi_persistent_containers::define_id31! {
    pub struct Plain1Id / StoredPlain1Id, "p1";
}
semi_persistent_containers::define_id31! {
    pub struct Plain2Id / StoredPlain2Id, "p2";
}
semi_persistent_containers::define_id31! {
    pub struct Plain3Id / StoredPlain3Id, "p3";
}
semi_persistent_containers::define_id31! {
    pub struct PlainNId / StoredPlainNId, "pN";
}
semi_persistent_containers::define_id31! {
    pub struct CNodeId / StoredCNodeId, "c";
}
semi_persistent_containers::define_id31! {
    pub struct ANodeId / StoredANodeId, "a";
}
semi_persistent_containers::define_id31! {
    pub struct MSetNodeId / StoredMSetNodeId, "mset";
}
semi_persistent_containers::define_id31! {
    pub struct SetNodeId / StoredSetNodeId, "set";
}
semi_persistent_containers::define_id31! {
    pub struct LitNodeId / StoredLitNodeId, "lit";
}

/// Standard node-id configuration for the generic node store.
pub struct DefaultNodeIds;
impl crate::typed_routing::NodeIds for DefaultNodeIds {
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

semi_persistent_containers::define_id31! {
    /// Interned literal value id.
    pub struct LitValId / StoredLitValId, "lv";
}

/// Default 31-bit e-graph configuration.
pub struct DefaultConfig;
impl crate::config::EGraphConfig for DefaultConfig {
    type G = crate::id::ENodeId;
    type O = crate::id::OpId;
    type S = crate::id::SortId;
    type V = LitValId;
    type UL = crate::id::UseListId;
    type UN = crate::id::UseNodeId;
    type C = crate::node_store::MSetChild<crate::id::ENodeId>;
    type M = crate::multiplicity::Multiplicity;
    type Ids = DefaultNodeIds;

    fn mset_child_id(c: &Self::C) -> Self::G {
        c.0
    }
    fn mset_child_mult(c: &Self::C) -> Self::M {
        c.1
    }
    fn mset_child_single(g: Self::G) -> Self::C {
        (g, crate::multiplicity::Multiplicity(1))
    }
    fn mset_child_with_mult(g: Self::G, mult: Self::M) -> Self::C {
        (g, mult)
    }
    fn mset_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool {
        if existing.0 == new_g {
            existing.1 = crate::multiplicity::Multiplicity(existing.1.0 + 1);
            true
        } else {
            false
        }
    }
}

// ---------------------------------------------------------------------------
// 63-bit id types
// ---------------------------------------------------------------------------

semi_persistent_containers::define_id63! { pub struct ENodeId64 / StoredENodeId64, "e64"; }
semi_persistent_containers::define_id63! { pub struct OpId64 / StoredOpId64, "op64"; }
semi_persistent_containers::define_id63! { pub struct SortId64 / StoredSortId64, "s64"; }
semi_persistent_containers::define_id63! { pub struct UseListId64 / StoredUseListId64, "ul64"; }
semi_persistent_containers::define_id63! { pub struct UseNodeId64 / StoredUseNodeId64, "un64"; }
semi_persistent_containers::define_id63! { pub struct LitValId64 / StoredLitValId64, "lv64"; }
semi_persistent_containers::define_id63! { pub struct Plain0Id64 / StoredPlain0Id64, "p0_64"; }
semi_persistent_containers::define_id63! { pub struct Plain1Id64 / StoredPlain1Id64, "p1_64"; }
semi_persistent_containers::define_id63! { pub struct Plain2Id64 / StoredPlain2Id64, "p2_64"; }
semi_persistent_containers::define_id63! { pub struct Plain3Id64 / StoredPlain3Id64, "p3_64"; }
semi_persistent_containers::define_id63! { pub struct PlainNId64 / StoredPlainNId64, "pN_64"; }
semi_persistent_containers::define_id63! { pub struct CNodeId64 / StoredCNodeId64, "c64"; }
semi_persistent_containers::define_id63! { pub struct ANodeId64 / StoredANodeId64, "a64"; }
semi_persistent_containers::define_id63! { pub struct MSetNodeId64 / StoredMSetNodeId64, "mset64"; }
semi_persistent_containers::define_id63! { pub struct SetNodeId64 / StoredSetNodeId64, "set64"; }
semi_persistent_containers::define_id63! { pub struct LitNodeId64 / StoredLitNodeId64, "lit64"; }

pub struct NodeIds64;
impl crate::typed_routing::NodeIds for NodeIds64 {
    type L0 = Plain0Id64;
    type L1 = Plain1Id64;
    type L2 = Plain2Id64;
    type L3 = Plain3Id64;
    type LC = CNodeId64;
    type LN = PlainNId64;
    type LA = ANodeId64;
    type LMSet = MSetNodeId64;
    type LSet = SetNodeId64;
    type LLit = LitNodeId64;
}

/// 63-bit e-graph configuration.
pub struct Config64;
impl crate::config::EGraphConfig for Config64 {
    type G = ENodeId64;
    type O = OpId64;
    type S = SortId64;
    type V = LitValId64;
    type UL = UseListId64;
    type UN = UseNodeId64;
    type C = crate::node_store::MSetChild<ENodeId64>;
    type M = crate::multiplicity::Multiplicity;
    type Ids = NodeIds64;

    fn mset_child_id(c: &Self::C) -> Self::G {
        c.0
    }
    fn mset_child_mult(c: &Self::C) -> Self::M {
        c.1
    }
    fn mset_child_single(g: Self::G) -> Self::C {
        (g, crate::multiplicity::Multiplicity(1))
    }
    fn mset_child_with_mult(g: Self::G, mult: Self::M) -> Self::C {
        (g, mult)
    }
    fn mset_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool {
        if existing.0 == new_g {
            existing.1 = crate::multiplicity::Multiplicity(existing.1.0 + 1);
            true
        } else {
            false
        }
    }
}
