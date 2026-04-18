// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent data structures, e-graphs, and tree traversals.
//!
//! This crate re-exports the individual subcrates for convenience:
//!
//! - [`containers`] — semi-persistent vectors, maps, and supporting data structures
//! - [`egraph`] — equality saturation engine
//! - [`traversals`] — stack-safe recursion schemes and tree traversals

pub use semi_persistent_containers as containers;
pub use semi_persistent_egraph as egraph;
pub use semi_persistent_traversals as traversals;
