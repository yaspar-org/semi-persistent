// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E-graph configuration trait — bundles all id types for a concrete e-graph.

use crate::containers::{DenseId, IndexLike, Tagged};
use crate::typed_routing::NodeIds;
use core::hash::Hash;

/// Configuration for an e-graph instance.
/// Bundles all id types so the EGraph struct has a single type parameter.
pub trait EGraphConfig: 'static {
    /// Unsigned machine word backing all capacity-coupled DenseIds.
    ///
    /// DenseIds reserve the most-significant bit for inline tagging, so the
    /// payload capacity is one bit less than the word:
    /// * `u32` gives 31 payload bits (`define_id31!` types),
    /// * `u64` gives 63 payload bits (`define_id63!` types).
    ///
    /// Every id whose capacity must scale with the configured e-graph (node
    /// ids, operator ids, per-kind local ids, AU search/pool ids) is
    /// constrained to this word. Intentionally bounded semantic registries
    /// (e.g. rule ids) may remain narrower; each such exception is documented
    /// at its definition.
    type Index: IndexLike + Tagged;

    /// Global e-node id (e.g. 31-bit `ENodeId`).
    type G: DenseId<Index = Self::Index> + Hash;
    /// Operator id.
    type O: DenseId<Index = Self::Index> + Hash;
    /// Sort id.
    type S: DenseId<Index = Self::Index>;
    /// Interned literal value id.
    type V: DenseId<Index = Self::Index> + Hash;
    /// Use-list id.
    type UL: DenseId<Index = Self::Index>;
    /// Use-list node id.
    type UN: DenseId<Index = Self::Index>;
    /// AC child type (e.g. `(G, Multiplicity)`).
    type C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug;
    /// Multiplicity type for AC nodes.
    type M: Copy + Clone + Eq + Ord + Hash + core::fmt::Debug + From<u32> + Into<u32>;
    /// Extract the global id from an AC child.
    fn mset_child_id(c: &Self::C) -> Self::G;
    /// Extract the multiplicity from an AC child.
    fn mset_child_mult(c: &Self::C) -> Self::M;
    /// Create an AC child with multiplicity 1.
    fn mset_child_single(g: Self::G) -> Self::C;
    /// Create an AC child with a given multiplicity.
    fn mset_child_with_mult(g: Self::G, mult: Self::M) -> Self::C;
    /// Increment the multiplicity of an AC child. Returns true if same group.
    fn mset_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool;
    /// Local id bundle for the node store.
    type Ids: NodeIds<Index = Self::Index>;
    /// AU search/snapshot/pool id bundle.
    type Au: AuIds;
}

/// Id bundle for the anti-unification subsystem: search-graph identities,
/// snapshot identities, and typed positions into flattened persistent pools.
/// Selected by `EGraphConfig::Au` so a wide e-graph gets wide AU arenas.
pub trait AuIds: 'static {
    /// Backing word; equals the owning config's `Index`.
    type Index: IndexLike + Tagged;

    // --- Direct identities ---
    /// Dense live-class index inside one AU snapshot.
    type Class: DenseId<Index = Self::Index> + Hash;
    /// Strongly connected component index in the snapshot's class graph.
    type Scc: DenseId<Index = Self::Index>;
    /// OR node (subproblem) in the search space.
    type Or: DenseId<Index = Self::Index> + Hash;
    /// Cached action list in the action cache.
    type Action: DenseId<Index = Self::Index>;
    /// Interned cycle context.
    type Context: DenseId<Index = Self::Index> + Hash;
    /// Hash-consed result term.
    type Term: DenseId<Index = Self::Index> + Hash;
    /// MCGS OR-statistics entry.
    type OrStats: DenseId<Index = Self::Index>;
    /// MCGS AND-statistics entry.
    type AndStats: DenseId<Index = Self::Index>;

    // --- Typed positions into flattened persistent pools ---
    /// Position in the snapshot's flattened member pool.
    type SnapshotMember: DenseId<Index = Self::Index>;
    /// Position in the context interner's class pool.
    type ContextElem: DenseId<Index = Self::Index>;
    /// Position in the term pool's child pool.
    type TermChild: DenseId<Index = Self::Index>;
    /// Position in the reachability bit-block pool.
    type ReachBlock: DenseId<Index = Self::Index>;
    /// Position in the flattened MCGS OR-edge statistics pools.
    type OrEdgeStat: DenseId<Index = Self::Index>;
    /// Position in the flattened MCGS AND-child statistics pools.
    type AndChildStat: DenseId<Index = Self::Index>;
}
