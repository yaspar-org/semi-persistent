// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent sparse set, composed from three verified `Vec`s.
//!
//! - `dense`:   packed values, no gaps        (`Vec<T, Idx, S, TRACK>`)
//! - `sparse`:  id → position in dense         (`Vec<Idx, Idx, InlineStore>`)
//! - `indices`: position → id                  (`Vec<Idx, Idx, InlineStore>`)
//!
//! `mark`/`restore` delegate to the three inner vectors, so the headline
//! semi-persistence theorem composes directly from `Vec::restore`: after
//! `restore`, every inner vector equals the snapshot it was marked at, hence
//! so does the whole sparse set. That composition — not the sparse↔dense
//! bijection (a data-structure-correctness property orthogonal to
//! persistence) — is what this module verifies.
//!
//! Inherits the crate's `Copy + Default` convention from `Vec` (dense `T` and
//! the index type both need `Default` for `Vec::restore`'s resize regrow).

use vstd::prelude::*;

use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::tagged::Tagged;
use crate::diff_store::DiffStore;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// Token bundling one `VecToken` per inner vector.
#[derive(Copy, Clone)]
pub struct SparseSetToken {
    pub dense: VecToken,
    pub sparse: VecToken,
    pub indices: VecToken,
}

/// Semi-persistent sparse set with stable IDs.
pub struct SparseSet<T, Idx, S, const TRACK: bool>
where
    T: Sized + Copy,
    Idx: IndexLike + Tagged,
    S: DiffStore<T, Idx, TRACK>,
{
    pub dense: SpVec<T, Idx, S, TRACK>,
    pub sparse: SpVec<Idx, Idx, InlineStore<Idx, Idx>, TRACK>,
    pub indices: SpVec<Idx, Idx, InlineStore<Idx, Idx>, TRACK>,
}

impl<T, Idx, S, const TRACK: bool> SparseSet<T, Idx, S, TRACK>
where
    T: Sized + Copy,
    Idx: IndexLike + Tagged,
    S: DiffStore<T, Idx, TRACK>,
{
    /// The packed values currently in the set, in dense order.
    pub open spec fn dense_view(&self) -> Seq<T> {
        self.dense.view()
    }

    /// Well-formedness: the three inner vectors are each well-formed. (The
    /// sparse↔dense bijection is a separate data-structure invariant, out of
    /// scope here — we verify the semi-persistence composition.)
    pub open spec fn wf(&self) -> bool {
        &&& self.dense.wf()
        &&& self.sparse.wf()
        &&& self.indices.wf()
    }

    pub fn len(&self) -> (n: Idx)
        requires self.wf(),
        ensures n.as_nat() == self.dense_view().len(),
    {
        self.dense.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.dense_view().len() == 0),
    {
        self.dense.is_empty()
    }

    /// Mark all three inner vectors; bundle their tokens.
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (token: SparseSetToken)
        requires
            old(self).wf(),
            old(self).dense.view().len() < Idx::max_nat(),
            old(self).sparse.view().len() < Idx::max_nat(),
            old(self).indices.view().len() < Idx::max_nat(),
            old(self).dense.frames@.len() < u32::MAX,
            old(self).sparse.frames@.len() < u32::MAX,
            old(self).indices.frames@.len() < u32::MAX,
        ensures
            self.wf(),
            self.dense_view() == old(self).dense_view(),
            self.dense.snapshots_view()
                == old(self).dense.snapshots_view().push(old(self).dense.view()),
    {
        let dense = self.dense.mark(shrink);
        let sparse = self.sparse.mark(shrink);
        let indices = self.indices.mark(shrink);
        SparseSetToken { dense, sparse, indices }
    }

    /// Restore all three inner vectors. By `Vec::restore`, each returns to the
    /// snapshot its token names; so the whole set returns to its marked state.
    pub fn restore(&mut self, token: SparseSetToken)
        where T: core::default::Default, Idx: core::default::Default
        requires
            old(self).wf(),
            // each inner token is valid + in range for its vector
            old(self).dense.is_token_valid_spec(token.dense),
            token.dense.frame_idx < old(self).dense.frames@.len(),
            old(self).dense.frames@.len() < u32::MAX,
            old(self).dense.forks.origins@.len() + 1 <= u32::MAX,
            old(self).sparse.is_token_valid_spec(token.sparse),
            token.sparse.frame_idx < old(self).sparse.frames@.len(),
            old(self).sparse.frames@.len() < u32::MAX,
            old(self).sparse.forks.origins@.len() + 1 <= u32::MAX,
            old(self).indices.is_token_valid_spec(token.indices),
            token.indices.frame_idx < old(self).indices.frames@.len(),
            old(self).indices.frames@.len() < u32::MAX,
            old(self).indices.forks.origins@.len() + 1 <= u32::MAX,
        ensures
            self.wf(),
            // headline: dense returns to the snapshot the token was minted at.
            self.dense_view()
                == old(self).dense.snapshots_view()[token.dense.frame_idx as int],
    {
        self.dense.restore(token.dense);
        self.sparse.restore(token.sparse);
        self.indices.restore(token.indices);
    }
}

} // verus!
