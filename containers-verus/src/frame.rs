// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Frame<I>`: a single mark frame on the frame stack.
//!
//! `saved_len: I` matches the vector's index type, so vectors with
//! `I = u64` can grow past `u32::MAX` slots without truncation. The
//! production crate had this field as `u32`, which silently wrapped at
//! 4B slots — fixed in this release alongside the verus port.
//!
//! `diff_start: usize` indexes into the diff log (a `std::Vec`, sized by
//! `usize`), so the natural fit there is `usize`, independent of `I`.
//!
//! The frame-replay invariant (used in M3/M4) says:
//!
//!   forall k: snapshots[k] == replay_reverse(view, diff_log[frames[k].diff_start..])
//!                              .subrange(0, frames[k].saved_len.as_nat())
//!
//! That invariant is `Vec`'s job to maintain; this file just defines the
//! shape.

use vstd::prelude::*;

use crate::index_like::IndexLike;

verus! {

#[derive(Copy, Clone)]
pub struct Frame<I: IndexLike> {
    pub saved_len: I,
    pub diff_start: usize,
}

} // verus!
