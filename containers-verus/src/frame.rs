// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Frame`: a single mark frame on the frame stack.
//!
//! Stores `(saved_len, diff_start)` — the length the vector had at mark
//! time, and where the diff log was when this frame began. Production uses
//! `u32` here for both fields. We carry them as `nat` in the spec view and
//! as `usize` at the exec layer.
//!
//! The frame-replay invariant (used in M3/M4) says:
//!
//!   forall k: snapshots[k] == replay_reverse(view, diff_log[frames[k].diff_start..])
//!                              .subrange(0, frames[k].saved_len)
//!
//! That invariant is `Vec`'s job to maintain; this file just defines the
//! shape.

use vstd::prelude::*;

verus! {

#[derive(Copy, Clone)]
pub struct Frame {
    pub saved_len: usize,
    pub diff_start: usize,
}

} // verus!
