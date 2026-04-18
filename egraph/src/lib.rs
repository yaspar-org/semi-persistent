// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::too_many_arguments)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::type_complexity)]

// Re-export semi_persistent_containers as `containers` so internal code can
// use `crate::containers::Vec`, `crate::containers::Tagged`, etc.
pub use semi_persistent_containers as containers;

pub mod apply;
pub mod ast;
pub mod caches;
pub mod canon;
pub mod classes;
pub mod compile;
pub mod config;
pub mod director;
mod egraph;
mod egraph_proof_test;
pub mod ematch;
pub mod extract;
pub mod id;
pub mod index;
pub mod interpret;
pub mod lca;
pub mod leapfrog;
pub mod lit_model;
pub mod literal;
pub mod model;
pub mod multiplicity;
pub mod node_store;
pub mod node_types;
pub mod nodes;
pub mod parser;
pub mod registry;
pub mod resolve;
pub mod saturate;
pub mod schedule;
pub mod sortcheck;
pub mod surface_ast;
#[cfg(test)]
pub(crate) mod test_helpers;
pub mod typed_routing;
pub mod union_find;
pub mod viz;

// Flat re-exports from containers
pub use containers::{DenseId, IdFactory, IndexLike, SparseSet};

// Flat re-exports from egraph module
pub use egraph::{EGraph, EGraph31, EGraph63, EGraphToken};

// Flat re-exports from other modules
pub use classes::EClasses;
pub use config::EGraphConfig;
pub use id::{ENodeId, ENodeKind, OpId, SortId};
pub use registry::{OpRegistry, SortRegistry};
pub use union_find::UnionFind;
