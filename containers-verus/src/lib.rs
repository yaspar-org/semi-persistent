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

#![allow(unused_imports)]

pub mod append_only_vec;
pub mod container_id;
pub mod diff_store;
pub mod fork_history;
pub mod frame;
pub mod index_like;
pub mod inline_store;
pub mod parallel_store;
pub mod tagged;
pub mod vec;
