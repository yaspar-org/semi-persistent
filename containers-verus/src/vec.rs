// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Vec<T, I, S, const TRACK: bool>`: the headline semi-persistent vector.
//!
//! Two-mode specification:
//!
//! - `TRACK = false`:
//!   No ghost machinery. `view() : Seq<T>` evolves like `std::Vec<T>`. `mark`
//!   and `restore` have `requires TRACK == true`, so they are statically
//!   uncallable.
//!
//! - `TRACK = true`:
//!   A ghost `snapshots: Seq<Seq<T>>` records the deep copy of `view()` at
//!   each `mark()`. A ghost `fork_tree: ForkTree` records branch history.
//!     - `mark()`     pushes `view()` onto `snapshots`, extends `fork_tree`.
//!     - `restore(t)` requires `fork_tree.is_valid(t)` and ensures
//!                    `view() == snapshots[t.frame_idx]`, truncating both
//!                    `snapshots` and `fork_tree.current_path` accordingly.
//!
//! Public spec functions:
//!   - `view(&self) -> Seq<T>`
//!   - `snapshots(&self) -> Seq<Seq<T>>`
//!   - `fork_tree(&self) -> ForkTree`
//!   - `is_token_valid(&self, t: VecToken) -> bool` (exec; mirrors the spec)
//!
//! Proofs land across M3 (single-frame), M4 (nested), M5 (branch-cut safety).

use vstd::prelude::*;

verus! {

// Type definition + impl will land here.

} // verus!
