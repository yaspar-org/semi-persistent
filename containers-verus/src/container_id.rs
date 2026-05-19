// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `ContainerId`: opaque per-container identity.
//!
//! Production code uses an atomic `u32` counter. Verus models this via
//! `external_body` plus a ghost `id: nat` axiomatized to be distinct on every
//! call. That gives us `t.container_id == self.id` as an unforgeable
//! cross-container check inside the `is_valid` predicate.
//!
//! Lands in M5 alongside `fork_history`.

use vstd::prelude::*;

verus! {

// Type definition + ghost-id axioms will land here.

} // verus!
