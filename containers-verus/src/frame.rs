// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Frame`: a single mark frame on the frame stack.
//!
//! Stores `(saved_len, diff_start)`. The frame-replay invariant says:
//!
//!   forall k: snapshots[k] == replay_reverse(view, diff_log[frames[k].diff_start..])
//!                              .subrange(0, frames[k].saved_len)
//!
//! Proved as part of `Vec`'s `wf()` in M3/M4.

use vstd::prelude::*;

verus! {

// Type definition + invariants will land here in milestone M3.

} // verus!
