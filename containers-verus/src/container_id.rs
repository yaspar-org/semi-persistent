// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `ContainerId`: opaque per-container identity.
//!
//! Production code uses a process-global `AtomicU32` counter so each `Vec`
//! instance gets a unique id; `restore` rejects a token whose `container_id`
//! doesn't match. Verus models this with an `external_body` wrapper around the
//! runtime `u32` plus a ghost `id: nat` projection. The exec equality test
//! `eq` is specified to reflect ghost-id equality exactly, which is all the
//! `restore` cross-container guard needs:
//!
//!   token.container_id.eq(self.id)  ⟺  token.container_id.id() == self.id.id()
//!
//! We do NOT axiomatize a global fresh-id source (a mutable static is not
//! expressible in spec). Distinctness of two live containers is instead a
//! *hypothesis* a caller supplies when relevant; the verified guarantee is the
//! faithful reflection above — a matching id provably means the exec check
//! passed, so a token minted by another container (different ghost id) is
//! provably rejected. That is the soundness-relevant direction.

use vstd::prelude::*;

verus! {

/// Opaque per-`Vec` identity. The runtime payload is a `u32` (as in
/// production); the ghost `id` is its abstract value, used in specs.
#[verifier::external_body]
#[derive(Clone, Copy)]
pub struct ContainerId {
    raw: u32,
}

impl ContainerId {
    /// Ghost projection: the abstract identity.
    pub uninterp spec fn id(self) -> nat;

    /// Exec equality, reflecting ghost-id equality exactly. This is the only
    /// observation `restore`/`is_valid_token` make on a `ContainerId`.
    #[verifier::external_body]
    pub fn eq(self, other: ContainerId) -> (b: bool)
        ensures b == (self.id() == other.id())
    {
        self.raw == other.raw
    }

    /// Mint a fresh id (production: atomic fetch-add). `external_body`: the
    /// returned id's ghost value is unconstrained here — distinctness from a
    /// specific other container, when needed, is supplied by the caller as a
    /// hypothesis. Marked so each call site sees an opaque, independent id.
    #[verifier::external_body]
    pub fn new() -> ContainerId {
        use core::sync::atomic::{AtomicU32, Ordering};
        static NEXT: AtomicU32 = AtomicU32::new(1);
        ContainerId { raw: NEXT.fetch_add(1, Ordering::Relaxed) }
    }
}

} // verus!
