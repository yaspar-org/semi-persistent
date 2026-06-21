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
    clippy::needless_late_init
)]

pub mod append_only_vec;
pub mod bplus;
pub mod bplus_layout;
pub mod bplus_search;
pub mod bplus_tree;
pub mod capture_bits;
pub mod circular_list;
pub mod container_id;
pub mod dense_id;
pub mod diff_store;
pub mod fork_history;
pub mod frame;
pub mod index_like;
pub mod inline_store;
pub mod list;
pub mod map;
pub mod opt;
pub mod parallel_store;
pub mod sparse_set;
pub mod tagged;
pub mod vec;
