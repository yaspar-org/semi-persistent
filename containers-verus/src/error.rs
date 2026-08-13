// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The total public API's error type (total-API plan, phase 2).
//!
//! Every `try_` wrapper returns `Result<_, ContainerError>`; the variant
//! names which precondition failed, so a caller can distinguish operational
//! exhaustion (capacity, depth, forks — conditions a correct program can
//! meet at scale) from contract violations (a foreign or stale token).

use vstd::prelude::*;

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ContainerError {
    /// The container's index word cannot represent one more element.
    CapacityExhausted,
    /// The mark/restore frame stack is at its u32 depth ceiling.
    DepthLimit,
    /// The fork counter is at its u32 ceiling.
    ForkLimit,
    /// The token does not name a restorable frame of this container
    /// (wrong container, stale genealogy, or cut branch).
    InvalidToken,
    /// The operation needs TRACK=true (mark/restore on an untracked container).
    Untracked,
    /// An index beyond the current length.
    IndexOutOfBounds,
    /// Input violates an ordering/shape requirement (e.g. `from_sorted` on
    /// keys that are not strictly ascending).
    NotSorted,
    /// The key type lacks a property the container requires statically
    /// (e.g. a non-bit-stealing id family on the B+tree).
    UnsupportedKey,
}

} // verus!

impl core::fmt::Display for ContainerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            ContainerError::CapacityExhausted => "container capacity exhausted for its index word",
            ContainerError::DepthLimit => "mark depth at u32 ceiling",
            ContainerError::ForkLimit => "fork count at u32 ceiling",
            ContainerError::InvalidToken => "token does not name a restorable frame",
            ContainerError::Untracked => "operation requires a tracked (TRACK=true) container",
            ContainerError::IndexOutOfBounds => "index beyond current length",
            ContainerError::NotSorted => "input keys not strictly ascending",
            ContainerError::UnsupportedKey => "key type lacks a required static property",
        };
        f.write_str(s)
    }
}

impl std::error::Error for ContainerError {}
