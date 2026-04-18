// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent data structures and supporting types.

#![allow(clippy::too_many_arguments)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::type_complexity)]

// --- Semi-persistent containers ---
mod append_only_vec;
pub mod bitset;
mod diff_store;
mod map;
mod tagged;
pub(crate) mod token;
mod vec;

pub use self::append_only_vec::AppendOnlyVec;
pub use self::diff_store::{DiffStore, InlineStore, ParallelStore};
pub use self::map::{Map, MapToken};
pub use self::tagged::{BoolTagged, Opt, Tagged};
pub use self::token::{ForkHistory, VecToken};
pub use self::vec::{ShrinkPolicy, Vec, View, ViewIter};

/// Inline capture: flag inside T::Repr. Requires `T: Tagged`.
pub type VecI<T, I, const TRACK: bool = true> = Vec<T, I, InlineStore<T, I>, TRACK>;

/// Parallel capture: flag in separate bitvector. Works with any `T: Clone`.
pub type VecP<T, I, const TRACK: bool = true> = Vec<T, I, ParallelStore<T, I>, TRACK>;

// --- Supporting data structures ---
pub mod bplus;
pub mod dense_id;
pub mod id;
pub mod list;
pub mod sparse_set;

pub use bplus::{BPlusCursor, BPlusNode, BPlusToken, BPlusTreeSet};
pub use dense_id::{DenseId, IdFactory, IndexLike};
pub use id::IdRangeError;
pub use list::{ListArena, ListArenaToken, ListIter};
pub use sparse_set::{SparseSet, SparseSetToken};
