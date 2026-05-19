// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `DiffStore`: the capture-protocol contract.
//!
//! A storage backend exposes a ghost `data: Seq<T>` (the abstract sequence)
//! and a ghost `captured: Seq<bool>` (the per-slot capture flag). Every public
//! method has a contract spelled out in those terms:
//!   - `push(v)`     extends `data` and `captured`
//!   - `set_raw`     overwrites `data[i]`, captured unchanged
//!   - `capture`     first-write-wins: appends to the diff log iff `!captured[i]`
//!   - `restore_entry` rewinds `data[i]` to a logged old value
//!   - `prepare_mark` clears tags / bits across `[0, saved_len)`
//!   - `finish_restore` rebuilds `captured` from the surviving diff suffix
//!
//! Both `ParallelStore` and `InlineStore` will be proved to satisfy this
//! contract (M2). The `Vec` proof talks only to `DiffStore`'s contract,
//! so it's parametric in storage.

use vstd::prelude::*;

verus! {

// Trait specification will land here in milestone M1.

} // verus!
