// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `InlineStore<T, I>` for `T: Tagged`: capture flag packed into `T::Repr`.
//!
//! The deep-copy ghost stack stores `Seq<Seq<T>>` — tag-stripped values.
//! The `Tagged` contract guarantees that `set_tag`/`clear_tag` preserve
//! `value(Repr)`, so the abstract view is invariant under capture-bit edits.
//!
//! Implements `DiffStore<T, I, TRACK>`. Proofs land in M2.

use vstd::prelude::*;

verus! {

// Type definition + impl will land here in milestone M2.

} // verus!
