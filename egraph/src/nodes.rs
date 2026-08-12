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
    pub struct SPairNodeId / StoredSPairNodeId, "sp";
}
semi_persistent_containers::define_id31! {
    pub struct SeqNodeId / StoredSeqNodeId, "sq";
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

semi_persistent_containers::define_id31! {
    /// Interned literal value id.
    pub struct LitValId / StoredLitValId, "lv";
}

/// Default 31-bit e-graph configuration.
pub struct DefaultConfig;
impl crate::config::EGraphConfig for DefaultConfig {
    type Index = u32;
    type G = crate::id::ENodeId;
    type O = crate::id::OpId;
    type S = crate::id::SortId;
    type V = LitValId;
    type UL = crate::id::UseListId;
    type UN = crate::id::UseNodeId;
    type C = crate::node_store::MSetChild<crate::id::ENodeId>;
    type M = crate::multiplicity::Multiplicity;
    type Ids = DefaultNodeIds;
    type Au = crate::au::AuIds31;

    crate::impl_mset_child_pair!();
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
semi_persistent_containers::define_id63! { pub struct SPairNodeId64 / StoredSPairNodeId64, "sp64"; }
semi_persistent_containers::define_id63! { pub struct SeqNodeId64 / StoredSeqNodeId64, "sq64"; }
semi_persistent_containers::define_id63! { pub struct MSetNodeId64 / StoredMSetNodeId64, "mset64"; }
semi_persistent_containers::define_id63! { pub struct SetNodeId64 / StoredSetNodeId64, "set64"; }
semi_persistent_containers::define_id63! { pub struct LitNodeId64 / StoredLitNodeId64, "lit64"; }

pub struct NodeIds64;
impl crate::typed_routing::NodeIds for NodeIds64 {
    type Index = u64;
    type L0 = Plain0Id64;
    type L1 = Plain1Id64;
    type L2 = Plain2Id64;
    type L3 = Plain3Id64;
    type LSPair = SPairNodeId64;
    type LN = PlainNId64;
    type LSeq = SeqNodeId64;
    type LMSet = MSetNodeId64;
    type LSet = SetNodeId64;
    type LLit = LitNodeId64;
}

/// 63-bit e-graph configuration (63 payload bits in a u64 word).
pub struct Config64;
impl crate::config::EGraphConfig for Config64 {
    type Index = u64;
    type G = ENodeId64;
    type O = OpId64;
    type S = SortId64;
    type V = LitValId64;
    type UL = UseListId64;
    type UN = UseNodeId64;
    type C = crate::node_store::MSetChild<ENodeId64, crate::multiplicity::Multiplicity64>;
    // A 64-bit multiplicity, because at this id width it is free: an AC child pairs an
    // 8-byte id with the count, and the pair is 16 bytes whether the count is 2, 4, or 8
    // bytes wide — the alignment of the id decides. Anything narrower would leave a
    // reachable ceiling in place for nothing: a 63-bit e-graph admits up to 2^63 nodes, so
    // `for_each_child`'s 64·N bound on a single multiplicity runs far past `u32`.
    type M = crate::multiplicity::Multiplicity64;
    type Ids = NodeIds64;
    type Au = crate::au::AuIds64;

    crate::impl_mset_child_pair!();
}

/// 31-bit ids with a **16-bit** multiplicity: the low-ceiling witness for the width axis.
///
/// This is the same 31-bit e-graph as [`DefaultConfig`] with a deliberately small
/// multiplicity ceiling (65535 occurrences of one child in one AC node). Its purpose is to
/// keep `EGraphConfig::M` honest, in two ways a second *wide* config cannot:
///
/// * it does not compile against a hardcoded `Multiplicity` anywhere on the generic paths,
///   so the parameterization cannot silently rot back to a fixed `u32`;
/// * its ceiling is reachable by a test. The checked narrowing and overflow paths are the
///   whole point of the design, and at 32 bits provoking them needs four billion children.
///
/// It is not a space optimization: an AC child pairs a 4-byte id with the count and pads to
/// 8 bytes at both 16 and 32 bits. Pick it when a low ceiling is *wanted* as a guard, not to
/// save memory.
pub struct ConfigM16;
impl crate::config::EGraphConfig for ConfigM16 {
    type Index = u32;
    type G = crate::id::ENodeId;
    type O = crate::id::OpId;
    type S = crate::id::SortId;
    type V = LitValId;
    type UL = crate::id::UseListId;
    type UN = crate::id::UseNodeId;
    type C = crate::node_store::MSetChild<crate::id::ENodeId, crate::multiplicity::Multiplicity16>;
    type M = crate::multiplicity::Multiplicity16;
    type Ids = DefaultNodeIds;
    type Au = crate::au::AuIds31;

    crate::impl_mset_child_pair!();
}
