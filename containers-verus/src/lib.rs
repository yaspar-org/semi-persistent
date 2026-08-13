// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! semi-persistent-containers-verus: Verus port of the semi-persistent containers,
//! built to be formally verified.
//!
//! Goals:
//! - When `TRACK = false`, every container is observationally equivalent to its
//!   non-semi-persistent counterpart (`std::Vec`, `Map`, `Set`, ...). Mark/restore
//!   are not callable in this mode.
//! - When `TRACK = true`, an internal ghost stack of deep copies records the
//!   container's value at each `mark()`. After `restore(token)`, the container's
//!   `view()` equals the deep copy at the corresponding frame.
//! - Branch-cut safety: `restore(t)` requires `t` to be on the current branch of
//!   a fork tree. Tokens for cut subtrees are statically rejected.
//!
//! Module layout:
//! - `tagged`         — `Tagged` trait with niche/encoding axioms
//! - `index_like`     — `IndexLike` trait with bijection axioms
//! - `diff_store`     — `DiffStore` trait, the capture protocol contract
//! - `parallel_store` — `ParallelStore<T,I>` impl + lemmas
//! - `inline_store`   — `InlineStore<T,I>` impl + lemmas (T: Tagged)
//! - `frame`          — frame stack
//! - `fork_history`   — executable fork history + refinement to ghost ForkTree
//! - `container_id`   — opaque per-container identity (atomics, external_body)
//! - `vec`            — `Vec<T,I,S,TRACK>` with full proofs over the trait specs

// Verus crates routinely trip lints that don't apply to verified code: the
// `verus!` macro leaves imports/params "unused" from cargo's view after ghost
// erasure, and proof-adjacent exec code is often clearer in a "manual" form
// than clippy's idiomatic rewrite (and a blind rewrite can disturb a proof).
// These allows mirror the `abstract-domains` crate's convention.
#![allow(unused_imports, unused_variables)]
#![allow(
    clippy::new_without_default,    // constructors carry verus preconditions; Default isn't always sound
    clippy::should_implement_trait, // `eq`/`next` are deliberate inherent methods, not the std traits
    clippy::len_zero,               // `len() == 0` reads clearer next to length-based proof obligations
    clippy::assign_op_pattern,      // explicit `i = i + 1` mirrors the loop's decreases/invariant
    clippy::manual_map,             // explicit match is clearer alongside spec annotations
    clippy::derivable_impls,        // hand-written Default documents the niche/empty encoding
    clippy::len_without_is_empty,   // `CaptureBits::len` mirrors a DiffStore length obligation; emptiness is read via `len`
    clippy::doc_lazy_continuation,        // doc-list wrapping in the design-heavy module comments
    clippy::doc_overindented_list_items,  // same: design-doc-style comment formatting
    // `global size_of usize == 8;` is verus syntax; clippy sees the macro expansion as braces.
    unused_braces,
    // `($leaf_cap + 1) / 2` is verified exec arithmetic that must match `split_mid_spec()`'s
    // same expression; vstd (2026-04-12) has no `div_ceil` spec, so a `.div_ceil(2)` rewrite
    // would jeopardise the `split_mid` ensures for a pure style change.
    clippy::manual_div_ceil,
    // Same reasoning as `manual_div_ceil` above, for `keep_bits % 64 == 0` in
    // `CaptureBits::truncate_words_for`: that expression appears verbatim in the
    // `by (nonlinear_arith)` block that proves the retained words still cover
    // every kept bit. `is_multiple_of` has no vstd spec (2026-04-12), so the
    // rewrite would break the proof for a pure style change.
    clippy::manual_is_multiple_of,
    // insert_rec / insert_rec_leaf take 8 args including GHOST proof parameters (is_root, the
    // split sub-models); bundling them into a struct would obscure the proof and break
    // production-signature parity.
    clippy::too_many_arguments,
    // the `SpVec<Node, ArenaIdx, InlineStore<..>, TRACK>` field type and the insert-recursion
    // return tuple `(bool, Option<(Word, ArenaIdx)>, Ghost<Tree>, Ghost<Tree>)` are intrinsic to
    // the generic design; a `type` alias would just relocate the complexity.
    clippy::type_complexity,
    // `let ret_pos;` in `seek_leaf` is assigned at the leaf-break inside a verified
    // `while !done` loop carrying an invariant; clippy's "initialise at declaration" does not
    // fit the loop control flow.
    clippy::needless_late_init,
    // ListNode construction goes Default-then-set_next because set_next is the verified
    // packing primitive (its ensures establish next_wf/next_ref); a struct literal would
    // bypass the proof surface.
    clippy::field_reassign_with_default
)]

pub mod append_only_vec;
pub mod bplus;
pub mod bplus_layout;
#[cfg(test)]
mod bplus_layout_tests;
pub mod bplus_search;
pub mod bplus_tree;
#[cfg(feature = "literal-types")]
pub mod canonical_keys;
pub mod capture_bits;
pub mod circular_list;
pub mod container_id;
pub mod dense_id;
pub mod diff_store;
pub mod error;
#[cfg(feature = "literal-types")]
pub mod external_specs;
pub mod fork_history;
pub mod frame;
pub mod guard;
pub mod hasher_spec;
pub mod id_factory;
#[macro_use]
pub mod id_macros;
pub mod index_like;
pub mod inline_store;
pub mod list;
pub mod map;
pub mod opt;
pub mod parallel_store;
pub mod sorted_cursor;
pub mod sorted_vec_cursor;
pub mod sparse_set;
pub mod tagged;
pub mod vec;

// ---------------------------------------------------------------------------
// Root re-exports (migration plan Phase 4): production-style flat surface
// under the verus names. One name per thing, workspace-wide.
// ---------------------------------------------------------------------------

pub use append_only_vec::AppendOnlyVec;
pub use bplus::{BPlusCursor, BPlusToken, BPlusTreeSet};
pub use bplus_layout::{
    Layout64U32, Layout128U32, Layout128U64, Layout256U32, Layout256U64, Layout512U64, NodeLayout,
};
pub use bplus_search::{BinarySearch, Branchless, SearchKind};
#[cfg(feature = "literal-types")]
pub use canonical_keys::{BitsF64, CanonicalF64, CanonicalRational};
pub use circular_list::{CircularList, CircularListToken, RingIter};
pub use container_id::ContainerId;
pub use dense_id::{DenseId31, DenseId63};
pub use diff_store::DiffStore;
pub use fork_history::ForkHistory;
pub use id_factory::{IdFactory, IdRangeError};
pub use id_macros::ids::{SparseSetId, UseListId, UseNodeId};
pub use index_like::IndexLike;
pub use inline_store::InlineStore;
pub use list::{ListArena, ListArenaToken};
pub use map::{MapToken, SpMap};
pub use opt::{DenseId, Opt};
pub use parallel_store::ParallelStore;
pub use sorted_cursor::SortedCursor;
pub use sorted_vec_cursor::SortedVecCursor;
pub use sparse_set::{SparseSet, SparseSetToken};
pub use tagged::{BoolTagged, Pair, Tagged};
pub use vec::{ShrinkPolicy, Vec, VecToken, VecView, VecViewIter};

// A compact bitset utility, kept outside the container proofs (production
// exposes it too). Permanent — not part of the retired compat-gate surface.
pub mod bitset;

/// Inline capture: flag stolen inside `T::Repr`. Requires `T: Tagged`.
/// (Production's `VecI` alias, verbatim.)
pub type VecI<T, I, const TRACK: bool = true> = Vec<T, I, InlineStore<T, I>, TRACK>;

/// Parallel capture: flag in a packed side bitvector. Works with any
/// `T: Copy`. (Production's `VecP` alias; production accepted `T: Clone` —
/// the Copy narrowing is the documented Phase 0 scope decision.)
pub type VecP<T, I, const TRACK: bool = true> = Vec<T, I, ParallelStore<T, I>, TRACK>;
