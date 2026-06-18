// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E-graph configuration trait — bundles all id types for a concrete e-graph.

use crate::containers::DenseId;
use crate::containers::Tagged;
use crate::typed_routing::NodeIds;
use core::hash::Hash;

/// Configuration for an e-graph instance.
/// Bundles all id types so the EGraph struct has a single type parameter.
pub trait EGraphConfig: 'static {
    /// Global e-node id (e.g. 31-bit `ENodeId`).
    type G: DenseId + Hash;
    /// Operator id.
    type O: DenseId + Hash;
    /// Sort id.
    type S: DenseId;
    /// Interned literal value id.
    type V: DenseId + Hash;
    /// Use-list id.
    type UL: DenseId;
    /// Use-list node id.
    type UN: DenseId;
    /// AC child type (e.g. `(G, Multiplicity)`).
    type C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug;
    /// Multiplicity type for AC nodes.
    type M: Copy + Clone + Eq + Ord + Hash + core::fmt::Debug + From<u32> + Into<u32>;
    /// Extract the global id from an AC child.
    fn ac_child_id(c: &Self::C) -> Self::G;
    /// Extract the multiplicity from an AC child.
    fn ac_child_mult(c: &Self::C) -> Self::M;
    /// Create an AC child with multiplicity 1.
    fn ac_child_single(g: Self::G) -> Self::C;
    /// Create an AC child with a given multiplicity.
    fn ac_child_with_mult(g: Self::G, mult: Self::M) -> Self::C;
    /// Increment the multiplicity of an AC child. Returns true if same group.
    fn ac_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool;
    /// Local id bundle.
    type Ids: NodeIds;
}
