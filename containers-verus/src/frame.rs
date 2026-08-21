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
//! The frame-replay invariant says:
//!
//!   forall k: snapshots[k] == replay_reverse(view, diff_log[frames[k].diff_start..])
//!                              .subrange(0, frames[k].saved_len.as_nat())
//!
//! That invariant is `Vec`'s job to maintain; this file just defines the
//! shape.

use vstd::prelude::*;

use crate::index_like::IndexLike;

verus! {

#[derive(Copy)]
pub struct Frame<I: IndexLike> {
    pub(crate) saved_len: I,
    pub(crate) diff_start: usize,
}

// Hand-written `Clone` (a plain copy) so Verus has a spec for it; the autoderived
// `Clone` on a generic struct emits a "clone is not a copy" warning otherwise.
impl<I: IndexLike> Clone for Frame<I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

} // verus!

// Production-surface parity (production derives Debug).
impl<I: crate::index_like::IndexLike + core::fmt::Debug> core::fmt::Debug for Frame<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Frame")
            .field("saved_len", &self.saved_len)
            .field("diff_start", &self.diff_start)
            .finish()
    }
}
