// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Vec<T, I, S, const TRACK: bool>`: the headline semi-persistent vector.
//!
//! M3a (this commit): scaffold — push, set, get, view. No mark/restore yet.
//! Headline obligation discharged here: `view()` matches `store.data()`
//! pointwise, and push/set/get refine to the obvious sequence operations.
//!
//! M3b will add `mark`/`restore` with a ghost `snapshots: Seq<Seq<T>>` and
//! prove the single-frame correctness theorem
//!   `view() == snapshots[token.frame_idx]` after restore.
//!
//! M4 will extend that to nested marks; M5 to branch-cut safety.

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::frame::Frame;
use crate::index_like::IndexLike;

verus! {

/// Semi-persistent vector parameterized by storage backend `S` and index
/// type `I`. `TRACK` compiles out all tracking when false.
///
/// This is `Vec` mirroring the production naming. Field types use the
/// fully-qualified `::alloc::vec::Vec` to avoid self-reference.
pub struct Vec<T, I, S, const TRACK: bool>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub store: S,
    pub diff_log: std::vec::Vec<(T, I)>,
    pub frames: std::vec::Vec<Frame>,
    pub phantom: core::marker::PhantomData<(T, I)>,
}

impl<T, I, S, const TRACK: bool> Vec<T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// Public spec view: the abstract sequence of stored values, observed
    /// at the current point in time. Equal to the storage backend's
    /// `data()` — this Vec adds tracking machinery, not a different
    /// observable state.
    pub open spec fn view(&self) -> Seq<T> {
        self.store.data()
    }

    /// Well-formedness. M3a only requires the storage to be well-formed;
    /// M3b will add the frame-replay invariant on top.
    pub open spec fn wf(&self) -> bool {
        self.store.wf()
    }

    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        self.store.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() == 0),
    {
        self.store.is_empty()
    }

    pub fn get(&self, i: I) -> (v: T)
        requires
            self.wf(),
            i.as_nat() < self.view().len(),
        ensures v == self.view()[i.as_nat() as int],
    {
        self.store.get(i)
    }

    pub fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            self.wf(),
            self.view() == old(self).view().push(value),
    {
        self.store.push(value);
    }

    pub fn set(&mut self, i: I, value: T)
        requires
            old(self).wf(),
            i.as_nat() < old(self).view().len(),
        ensures
            self.wf(),
            self.view() == old(self).view().update(i.as_nat() as int, value),
    {
        self.store.set_raw(i, value);
    }
}

} // verus!
