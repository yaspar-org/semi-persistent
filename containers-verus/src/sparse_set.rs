// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent sparse set with stable IDs, composed from three verified
//! `Vec`s:
//!   - `dense`:   packed values `[0, n)`, no gaps   (`Vec<T, Idx, S>`)
//!   - `sparse`:  id → position                      (`Vec<Idx, Idx, Inline>`)
//!   - `indices`: position → id                      (`Vec<Idx, Idx, Inline>`)
//!
//! ## The real invariant (`wf`)
//! Let `cap = sparse.len() = indices.len()`, `n = dense.len() <= cap`.
//!   1. `indices` is a PERMUTATION of `[0, cap)`: each `indices[p] < cap`, and
//!      `indices` is injective (hence bijective position→id).
//!   2. INVERSE-ON-LIVE: for live positions `p in [0, n)`,
//!      `sparse[indices[p]] == p`.
//! Positions `[n, cap)` are the FREE region — recently-removed ids parked for
//! recycling; their `sparse` entries may be stale, which is harmless because
//! injectivity (1) stops a free id from passing the liveness test.
//!
//! From this:
//!   - **liveness**: `contains(id) = id<cap && sparse[id]<n &&
//!     indices[sparse[id]]==id` holds iff `id` is some `indices[p]` with `p<n`
//!     (proved: a free id fails the test by injectivity).
//!   - **stable identity**: a live id's value is `dense[sparse[id]]`; other
//!     ops keep that mapping (remove's swap updates `sparse[last_id]`).
//!   - **id recycling**: `remove` parks the freed id at `indices[n-1]`; `add`
//!     recycles exactly `indices[n]` and repairs its `sparse` entry.
//!   - **semi-persistence**: `mark`/`restore` delegate to the three inner
//!     vectors; restore composition gives back the marked state.
//!
//! Inherits the crate's `Copy + Default` convention (dense `T` and `Idx` both
//! need `Default` for `Vec::restore`'s resize regrow).

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

    pub open spec fn cap_spec(&self) -> nat {
        self.sparse.view().len()
    }

    pub open spec fn n_spec(&self) -> nat {
        self.dense.view().len()
    }

    /// The structural sparse-set invariant (permutation + inverse-on-live),
    /// on top of the three inner vectors' own well-formedness.
    pub open spec fn wf(&self) -> bool {
        let sparse = self.sparse.view();
        let indices = self.indices.view();
        let cap = self.cap_spec();
        let n = self.n_spec();
        &&& self.dense.wf()
        &&& self.sparse.wf()
        &&& self.indices.wf()
        &&& indices.len() == cap
        &&& n <= cap
        // (1a) indices in range [0, cap)
        &&& (forall|p: int| 0 <= p < cap ==> (#[trigger] indices[p]).as_nat() < cap)
        // (1b) indices injective ⇒ permutation of [0, cap)
        &&& (forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
                (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat())
        // (2) inverse on the live region [0, n)
        &&& (forall|p: int| 0 <= p < n ==>
                sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p)
    }

    /// `id` is live: allocated, its position is in `[0, n)`, and the position
    /// maps back to it. (Proved equivalent to "id == indices[p] for p < n".)
    pub open spec fn contains_spec(&self, id: Idx) -> bool {
        let sparse = self.sparse.view();
        let indices = self.indices.view();
        let n = self.n_spec();
        &&& id.as_nat() < sparse.len()
        &&& sparse[id.as_nat() as int].as_nat() < n
        &&& indices[sparse[id.as_nat() as int].as_nat() as int].as_nat() == id.as_nat()
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

    /// Liveness test. Returns exactly `contains_spec(id)`.
    pub fn contains(&self, id: Idx) -> (b: bool)
        requires self.wf(),
        ensures b == self.contains_spec(id),
    {
        let cap = self.sparse.len();
        if id.as_usize() >= cap.as_usize() {
            return false;
        }
        let pos = self.sparse.get(id);
        let nlen = self.dense.len();
        if pos.as_usize() >= nlen.as_usize() {
            return false;
        }
        let idx_at = self.indices.get(pos);
        idx_at.as_usize() == id.as_usize()
    }

    /// Value of a live id (through the stable indirection).
    pub fn get(&self, id: Idx) -> (v: T)
        requires self.wf(), self.contains_spec(id),
        ensures v == self.dense_view()[self.sparse.view()[id.as_nat() as int].as_nat() as int],
    {
        let pos = self.sparse.get(id);
        self.dense.get(pos)
    }

    /// Overwrite a live id's value in place (position and id unchanged).
    pub fn set(&mut self, id: Idx, value: T)
        requires old(self).wf(), old(self).contains_spec(id),
        ensures
            self.wf(),
            self.cap_spec() == old(self).cap_spec(),
            self.n_spec() == old(self).n_spec(),
    {
        let pos = self.sparse.get(id);
        self.dense.set(pos, value);
        proof {
            // dense.set changes only dense's values, not lengths; sparse and
            // indices are untouched, so the permutation + inverse carry.
            assert(self.sparse.view() == old(self).sparse.view());
            assert(self.indices.view() == old(self).indices.view());
            assert(self.dense.view().len() == old(self).dense.view().len());
        }
    }

    /// Add a value, returning a stable id. If a free slot exists (`n < cap`),
    /// recycle the id parked at `indices[n]`; otherwise allocate a fresh id
    /// `== n`. The new element occupies dense position `n`.
    pub fn add(&mut self, value: T) -> (id: Idx)
        requires
            old(self).wf(),
            old(self).dense.view().len() + 1 < Idx::max_nat(),
            old(self).sparse.view().len() + 1 < Idx::max_nat(),
            old(self).indices.view().len() + 1 < Idx::max_nat(),
        ensures
            self.wf(),
            self.n_spec() == old(self).n_spec() + 1,
            // the returned id is now live
            self.contains_spec(id),
    {
        let ghost old_n = self.dense.view().len();
        let ghost old_cap = self.sparse.view().len();
        let pos = self.dense.len();
        self.dense.push(value);

        let cap = self.sparse.len();
        if pos.as_usize() < cap.as_usize() {
            // Recycle: indices[pos] is the first free id (pos == old_n).
            let recycled_id = self.indices.get(pos);
            self.sparse.set(recycled_id, pos);
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let n = self.dense.view().len();  // old_n + 1
                assert(indices == old(self).indices.view());
                assert(n == old_n + 1);
                assert(pos.as_nat() == old_n);
                // indices unchanged ⇒ permutation (1a,1b) carry.
                // inverse-on-live now needs to hold for p in [0, old_n+1):
                //  - p < old_n: indices[p] != recycled_id (= indices[old_n], and
                //    injectivity with p != old_n), so sparse[indices[p]] is
                //    unchanged == p (old inverse).
                //  - p == old_n: indices[old_n] == recycled_id and we just set
                //    sparse[recycled_id] = old_n == pos.
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    if p == old_n as int {
                        assert(indices[p].as_nat() == recycled_id.as_nat());
                        assert(sparse[recycled_id.as_nat() as int].as_nat() == old_n);
                    } else {
                        assert(indices[p].as_nat() != indices[old_n as int].as_nat());
                        assert(indices[old_n as int].as_nat() == recycled_id.as_nat());
                        assert(sparse[indices[p].as_nat() as int]
                            == old(self).sparse.view()[indices[p].as_nat() as int]);
                    }
                }
                // returned id (recycled_id) is live: sparse[recycled_id]=old_n<n,
                // indices[old_n]==recycled_id.
                assert(recycled_id.as_nat() < old_cap);
            }
            recycled_id
        } else {
            // Fresh id == pos == old_n == old_cap.
            self.sparse.push(pos);
            self.indices.push(pos);
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let cap = sparse.len();   // old_cap + 1
                let n = self.dense.view().len();  // old_n + 1, and old_n == old_cap
                assert(pos.as_nat() == old_n);
                assert(old_n == old_cap);
                assert(cap == old_cap + 1);
                assert(indices[old_cap as int].as_nat() == pos.as_nat() == old_cap);
                // (1a) in range: old entries < old_cap < cap; new entry == old_cap < cap.
                assert forall|p: int| 0 <= p < cap implies (#[trigger] indices[p]).as_nat() < cap by {
                    if p < old_cap { } else { assert(indices[p].as_nat() == old_cap); }
                }
                // (1b) injective: new value old_cap differs from all old (< old_cap).
                assert forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q implies
                    (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat() by {
                    if p < old_cap && q < old_cap {
                    } else {
                        // one is the new slot (value old_cap), the other old (< old_cap).
                    }
                }
                // (2) inverse-on-live for [0, old_cap+1): old positions carry
                // (sparse extended, prefix unchanged); new position old_cap has
                // indices[old_cap]==old_cap and sparse[old_cap]==pos==old_cap.
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    if p < old_n as int {
                        assert(indices[p] == old(self).indices.view()[p]);
                        assert(indices[p].as_nat() < old_cap);
                        assert(sparse[indices[p].as_nat() as int]
                            == old(self).sparse.view()[indices[p].as_nat() as int]);
                    } else {
                        assert(p == old_cap as int);
                        assert(indices[p].as_nat() == old_cap);
                        assert(sparse[old_cap as int].as_nat() == pos.as_nat() == old_cap);
                    }
                }
            }
            pos
        }
    }

    /// Remove a live id. Swap-removes its dense slot with the last element and
    /// parks the freed id at the new boundary `indices[n-1]` (the first free
    /// slot), preserving the permutation by a transposition.
    pub fn remove(&mut self, id: Idx)
        requires old(self).wf(), old(self).contains_spec(id),
        ensures
            self.wf(),
            self.n_spec() == old(self).n_spec() - 1,
            self.cap_spec() == old(self).cap_spec(),
    {
        let ghost old_n = self.dense.view().len();
        let ghost old_cap = self.sparse.view().len();
        let ghost old_sparse = self.sparse.view();
        let ghost old_indices = self.indices.view();
        let pos = self.sparse.get(id);
        let nlen = self.dense.len();
        // last_pos = n - 1 (n >= 1 since id is live ⇒ pos < n).
        proof { nlen.lemma_as_nat_bounded(); }
        let last_pos = match Idx::try_from_usize(nlen.as_usize() - 1) {
            Some(x) => x,
            None => { assert(false); return; },
        };

        if pos.as_usize() != last_pos.as_usize() {
            let last_id = self.indices.get(last_pos);
            let last_val = self.dense.get(last_pos);
            proof {
                // From inverse-on-live: indices[pos]==id and sparse[last_id]==last_pos.
                assert(pos.as_nat() < old_n);          // id live
                assert(old_indices[pos.as_nat() as int].as_nat() == id.as_nat());
                assert(last_pos.as_nat() == old_n - 1);
                assert(old_sparse[old_indices[(old_n - 1) as int].as_nat() as int].as_nat()
                    == (old_n - 1));  // inverse at last_pos
                assert(last_id.as_nat() == old_indices[(old_n - 1) as int].as_nat());
            }
            self.dense.set(pos, last_val);
            self.indices.set(pos, last_id);
            self.indices.set(last_pos, id);
            self.sparse.set(last_id, pos);
            self.dense.pop();
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let n = self.dense.view().len();   // old_n - 1
                let cap = sparse.len();
                assert(n == old_n - 1);
                assert(cap == old_cap);
                // indices' is old_indices with [pos]:=last_id, [last_pos]:=id —
                // a transposition of the values at pos and last_pos (old
                // indices[pos]==id, indices[last_pos]==last_id), so still a
                // permutation of [0, cap).
                assert(indices =~= old_indices.update(pos.as_nat() as int, last_id)
                    .update(last_pos.as_nat() as int, id));
                // (1a) in range: values unchanged as a multiset.
                assert forall|p: int| 0 <= p < cap implies (#[trigger] indices[p]).as_nat() < cap by {
                    if p == pos.as_nat() {
                        assert(indices[p].as_nat() == last_id.as_nat());
                        assert(old_indices[(old_n - 1) as int].as_nat() < old_cap);
                    } else if p == last_pos.as_nat() {
                        assert(indices[p].as_nat() == id.as_nat());
                        assert(old_indices[pos.as_nat() as int].as_nat() == id.as_nat());
                    } else {
                        assert(indices[p] == old_indices[p]);
                    }
                }
                // (1b) injective: a transposition of an injective seq.
                lemma_transposition_injective(old_indices, indices,
                    pos.as_nat() as int, last_pos.as_nat() as int, cap as int);
                // (2) inverse-on-live for [0, n) = [0, old_n - 1):
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    if p == pos.as_nat() {
                        // indices[pos]==last_id, sparse[last_id]:=pos.
                        assert(indices[p].as_nat() == last_id.as_nat());
                        assert(sparse[last_id.as_nat() as int].as_nat() == pos.as_nat());
                    } else {
                        // p < n-1... actually p in [0,n) with p != pos, and
                        // p != last_pos (since last_pos == old_n-1 == n >= p+? );
                        // p < n = old_n-1 < last_pos, so p != last_pos.
                        assert(p < (old_n - 1));
                        assert(p != last_pos.as_nat());
                        assert(indices[p] == old_indices[p]);
                        // indices[p] != last_id (injective, p != last_pos), so
                        // sparse[indices[p]] unchanged from old (only last_id set).
                        assert(old_indices[p].as_nat() != old_indices[(old_n - 1) as int].as_nat());
                        assert(indices[p].as_nat() != last_id.as_nat());
                        assert(sparse[indices[p].as_nat() as int]
                            == old_sparse[indices[p].as_nat() as int]);
                        assert(old_sparse[old_indices[p].as_nat() as int].as_nat() == p);
                    }
                }
            }
        } else {
            // Removing the last live element: just shrink. The id stays parked
            // at indices[last_pos] = indices[n-1] (now the first free slot).
            self.dense.pop();
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let n = self.dense.view().len();  // old_n - 1
                assert(n == old_n - 1);
                assert(indices == old_indices);
                assert(sparse == old_sparse);
                // sparse/indices untouched; inverse-on-live shrinks to [0,n).
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    assert(p < old_n);
                }
            }
        }
    }

    // ---- semi-persistence: delegate to the three inner vectors ----

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

    pub fn restore(&mut self, token: SparseSetToken)
        where T: core::default::Default, Idx: core::default::Default
        requires
            old(self).wf(),
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
            // the snapshots being restored form a valid sparse-set state
            sparse_set_snap_wf(
                old(self).dense.snapshots_view()[token.dense.frame_idx as int],
                old(self).sparse.snapshots_view()[token.sparse.frame_idx as int],
                old(self).indices.snapshots_view()[token.indices.frame_idx as int]),
        ensures
            self.wf(),
            self.dense_view()
                == old(self).dense.snapshots_view()[token.dense.frame_idx as int],
    {
        self.dense.restore(token.dense);
        self.sparse.restore(token.sparse);
        self.indices.restore(token.indices);
    }
}

/// The sparse-set structural invariant stated over raw snapshot sequences (for
/// `restore`: the three snapshots being restored must jointly form a valid
/// state, so the restored set is `wf`). Mirrors `wf`'s clauses (2)/(1).
pub open spec fn sparse_set_snap_wf<T, Idx: IndexLike>(
    dense: Seq<T>, sparse: Seq<Idx>, indices: Seq<Idx>,
) -> bool {
    let cap = sparse.len();
    let n = dense.len();
    &&& indices.len() == cap
    &&& n <= cap
    &&& (forall|p: int| 0 <= p < cap ==> (#[trigger] indices[p]).as_nat() < cap)
    &&& (forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat())
    &&& (forall|p: int| 0 <= p < n ==>
            sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p)
}

/// A transposition of two positions in an injective sequence is injective.
/// `b` is `a` with values at `i` and `j` swapped (`a[i]==b[j]`, `a[j]==b[i]`,
/// equal elsewhere); both same length `cap`.
pub proof fn lemma_transposition_injective<Idx: IndexLike>(
    a: Seq<Idx>, b: Seq<Idx>, i: int, j: int, cap: int,
)
    requires
        0 <= i < cap <= a.len(),
        0 <= j < cap,
        b.len() == a.len(),
        i != j,
        b[i].as_nat() == a[j].as_nat(),
        b[j].as_nat() == a[i].as_nat(),
        forall|k: int| 0 <= k < cap && k != i && k != j ==> b[k].as_nat() == a[k].as_nat(),
        forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] a[p]).as_nat() != (#[trigger] a[q]).as_nat(),
    ensures
        forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] b[p]).as_nat() != (#[trigger] b[q]).as_nat(),
{
    assert forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q implies
        (#[trigger] b[p]).as_nat() != (#[trigger] b[q]).as_nat() by {
        // b's value at any position equals a's value at the transposed position;
        // since a is injective and the transposition is a bijection on indices,
        // distinct p,q map to distinct source positions, hence distinct values.
        let sp = if p == i { j } else if p == j { i } else { p };
        let sq = if q == i { j } else if q == j { i } else { q };
        assert(b[p].as_nat() == a[sp].as_nat());
        assert(b[q].as_nat() == a[sq].as_nat());
        assert(sp != sq);
        assert(0 <= sp < cap && 0 <= sq < cap);
    }
}

} // verus!
