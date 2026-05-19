// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Fork-history machinery for branch-cut safety.
//!
//! Two layers:
//!   - `ForkTree` (ghost): an append-only tree of nodes, each carrying a
//!     deep-copy `saved_view`, plus a `current_path` from root to the head.
//!     Token validity is `current_path.contains(t.node_id)`.
//!   - `ForkHistory` (exec): the production data structure — a
//!     `current_branch_id` and a list of `(parent_branch_id, fork_depth)`
//!     entries. We prove the executable `is_valid` walk computes the same
//!     predicate as `ForkTree::is_valid`.
//!
//! `Vec::is_token_valid(t)` exposes the predicate as an exec method so
//! callers can branch on it before calling `restore`.
//!
//! Proved in M5.

use vstd::prelude::*;

verus! {

// Ghost ForkTree, exec ForkHistory, and the refinement lemma will land here.

} // verus!
