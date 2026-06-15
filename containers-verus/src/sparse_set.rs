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

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::tagged::Tagged;
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

    // ===================================================================
    // Abstraction: the sparse set IS a ghost set of live ids together with a
    // hand-rolled index pool of recycled ids (user-requested refinement). The
    // permutation invariant (`wf`) is exactly what makes this abstraction sound.
    // ===================================================================

    /// The abstract set of live ids: the image of `indices` over `[0, n)`.
    pub open spec fn id_set(&self) -> Set<nat> {
        let indices = self.indices.view();
        Set::new(|id: nat| exists|p: int| 0 <= p < self.n_spec()
            && (#[trigger] indices[p]).as_nat() == id)
    }

    /// The index pool of recycled-but-not-reallocated ids: `indices[n .. cap)`,
    /// as a sequence (the parking order; `add` reuses the slot at position `n`,
    /// `remove` parks at `n-1`). Its multiset is the free ids.
    pub open spec fn free_pool(&self) -> Seq<nat> {
        let indices = self.indices.view();
        Seq::new((self.cap_spec() - self.n_spec()) as nat,
            |k: int| indices[self.n_spec() as int + k].as_nat())
    }

    /// Membership refinement: the runtime liveness test decides exactly the
    /// abstract set. (⟸ uses inverse-on-live; ⟹ uses the round-trip test.)
    pub proof fn lemma_contains_iff_id_set(&self, id: Idx)
        requires self.wf(),
        ensures self.contains_spec(id) <==> self.id_set().contains(id.as_nat()),
    {
        let indices = self.indices.view();
        let sparse = self.sparse.view();
        let n = self.n_spec();
        if self.contains_spec(id) {
            // position p = sparse[id] < n witnesses membership.
            let p = sparse[id.as_nat() as int].as_nat() as int;
            assert(0 <= p < n && indices[p].as_nat() == id.as_nat());
        }
        if self.id_set().contains(id.as_nat()) {
            // some p<n has indices[p]==id; inverse-on-live ⇒ sparse[id]==p<n,
            // and indices[sparse[id]]==indices[p]==id ⇒ contains_spec.
            let p = choose|p: int| 0 <= p < n && (#[trigger] indices[p]).as_nat() == id.as_nat();
            assert(sparse[indices[p].as_nat() as int].as_nat() == p);  // inverse
            assert(id.as_nat() < sparse.len());  // id == indices[p] < cap == sparse.len()
        }
    }

    /// Set and pool are DISJOINT and together exhaust the allocated id space:
    /// every id in `[0, cap)` is either live or free, never both. (Direct from
    /// the permutation invariant: `indices` bijects positions to ids, the live
    /// positions `[0,n)` give the set, the free positions `[n,cap)` give the
    /// pool.)
    pub proof fn lemma_set_pool_partition(&self)
        requires self.wf(),
        ensures
            // disjoint
            forall|id: nat| self.id_set().contains(id) ==> !self.free_pool().contains(id),
            // every allocated id is in exactly one
            forall|id: nat| id < self.cap_spec() ==>
                (self.id_set().contains(id) || self.free_pool().contains(id)),
    {
        let indices = self.indices.view();
        let n = self.n_spec();
        let cap = self.cap_spec();
        // disjoint: a live id has a witness p<n; a pooled id has witness k with
        // position n+k >= n. Same id at two positions violates injectivity.
        assert forall|id: nat| self.id_set().contains(id) implies
            !self.free_pool().contains(id) by {
            let p = choose|p: int| 0 <= p < n && (#[trigger] indices[p]).as_nat() == id;
            if self.free_pool().contains(id) {
                let k = choose|k: int| 0 <= k < (cap - n)
                    && (#[trigger] self.free_pool()[k]) == id;
                assert(indices[n + k].as_nat() == id);
                assert(p != n + k);  // p < n <= n+k
                // injectivity: indices[p] != indices[n+k], contradiction.
                assert(indices[p].as_nat() != indices[n + k].as_nat());
            }
        }
        // exhaustive: id < cap. By surjectivity of the permutation (in-range +
        // injective on a finite set ⇒ bijective), id == indices[p] for some
        // p < cap; p < n ⇒ live, else pooled.
        assert forall|id: nat| id < cap implies
            (self.id_set().contains(id) || self.free_pool().contains(id)) by {
            lemma_perm_surjective(indices, cap as int, id);
            let p = choose|p: int| 0 <= p < cap && (#[trigger] indices[p]).as_nat() == id;
            if p < n {
                assert(self.id_set().contains(id));
            } else {
                assert(self.free_pool()[p - n] == id);
                assert(self.free_pool().contains(id));
            }
        }
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
            // ABSTRACT EFFECT: the live set gains exactly `id`, which was not
            // live before.
            !old(self).id_set().contains(id.as_nat()),
            self.id_set() =~= old(self).id_set().insert(id.as_nat()),
            // INDEX-POOL REUSE: if a free id was available, `add` recycles the
            // one parked at the pool front (LIFO with `remove`), and the pool
            // shrinks by that element; otherwise a fresh id `== old cap` is
            // allocated and the (empty) pool stays empty.
            old(self).free_pool().len() > 0 ==>
                (id.as_nat() == old(self).free_pool()[0]
                 && self.free_pool() =~= old(self).free_pool().drop_first()),
            old(self).free_pool().len() == 0 ==>
                (id.as_nat() == old(self).cap_spec() && self.free_pool().len() == 0),
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

                // --- abstract effect: set gains recycled_id, pool drops front.
                // indices unchanged, n: old_n -> old_n+1. id_set is the image of
                // [0,n); the only new position is old_n, whose value is
                // recycled_id == old free_pool[0].
                assert(old(self).free_pool().len() > 0);   // old_n < old_cap
                assert(old(self).free_pool()[0] == recycled_id.as_nat()) by {
                    assert(old(self).indices.view()[old_n as int].as_nat()
                        == recycled_id.as_nat());
                }
                assert(!old(self).id_set().contains(recycled_id.as_nat())) by {
                    // recycled_id at position old_n >= old_n; a live witness p
                    // would be < old_n, violating injectivity.
                    if old(self).id_set().contains(recycled_id.as_nat()) {
                        let p = choose|p: int| 0 <= p < old_n
                            && (#[trigger] old(self).indices.view()[p]).as_nat()
                                == recycled_id.as_nat();
                        assert(old(self).indices.view()[p].as_nat()
                            != old(self).indices.view()[old_n as int].as_nat());
                    }
                }
                assert(self.id_set() =~= old(self).id_set().insert(recycled_id.as_nat())) by {
                    assert forall|v: nat| self.id_set().contains(v)
                        <==> old(self).id_set().insert(recycled_id.as_nat()).contains(v) by {
                        if self.id_set().contains(v) {
                            let p = choose|p: int| 0 <= p < n
                                && (#[trigger] indices[p]).as_nat() == v;
                            if p < old_n { } else { assert(v == recycled_id.as_nat()); }
                        }
                    }
                }
                assert(self.free_pool() =~= old(self).free_pool().drop_first()) by {
                    // both have length old_cap - old_n - 1; element k of the new
                    // pool is indices[(old_n+1)+k] == old pool element k+1.
                    assert(self.free_pool().len() == old(self).free_pool().drop_first().len());
                    assert forall|k: int| 0 <= k < self.free_pool().len() implies
                        self.free_pool()[k] == old(self).free_pool().drop_first()[k] by {
                        assert(self.free_pool()[k] == indices[(old_n + 1) + k].as_nat());
                        assert(old(self).free_pool().drop_first()[k]
                            == old(self).free_pool()[k + 1]);
                    }
                }
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
                // --- abstract effect: fresh allocation. old pool was empty
                // (old_n == old_cap), new id == old_cap, new pool empty too.
                assert(old(self).free_pool().len() == 0);   // old_cap - old_n == 0
                assert(!old(self).id_set().contains(old_cap as nat)) by {
                    // a live witness p < old_n would have indices[p] < old_cap.
                    if old(self).id_set().contains(old_cap as nat) {
                        let p = choose|p: int| 0 <= p < old_n
                            && (#[trigger] old(self).indices.view()[p]).as_nat() == old_cap as nat;
                    }
                }
                assert(self.id_set() =~= old(self).id_set().insert(old_cap as nat)) by {
                    assert forall|v: nat| self.id_set().contains(v)
                        <==> old(self).id_set().insert(old_cap as nat).contains(v) by {
                        if self.id_set().contains(v) {
                            let p = choose|p: int| 0 <= p < n
                                && (#[trigger] indices[p]).as_nat() == v;
                            if p < old_n {
                                assert(indices[p] == old(self).indices.view()[p]);
                            } else {
                                assert(v == old_cap);
                            }
                        }
                        // reverse: old members keep their witness; old_cap is at
                        // position old_n == old_cap.
                        if old(self).id_set().contains(v) {
                            let q = choose|q: int| 0 <= q < old_n
                                && (#[trigger] old(self).indices.view()[q]).as_nat() == v;
                            assert(indices[q] == old(self).indices.view()[q]);
                            assert(0 <= q < n);
                        }
                        if v == old_cap as nat {
                            assert(indices[old_cap as int].as_nat() == old_cap);
                            assert(0 <= old_cap < n);
                        }
                    }
                }
                assert(self.free_pool().len() == 0);  // cap == n == old_cap+1
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
            // ABSTRACT EFFECT: the live set loses exactly `id`.
            self.id_set() =~= old(self).id_set().remove(id.as_nat()),
            // INDEX-POOL PARKING: the freed id is pushed to the pool FRONT
            // (so the next `add` recycles it — LIFO), the rest of the pool
            // shifts back by one.
            self.free_pool() =~= old(self).free_pool().insert(0, id.as_nat()),
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
        // --- abstract effect (both branches): set loses `id`, pool gains it
        // at the front. Branch-uniform facts established locally above:
        //   - indices[n].as_nat() == id  (id parked at the new pool front);
        //   - for every OLD live position q < old_n with old value v != id, the
        //     NEW indices still has v at some position < n (proved per branch
        //     into `old_to_new_live` below);
        //   - the prefix relation for the pool tail.
        proof {
            let indices = self.indices.view();
            let n = self.dense.view().len();   // old_n - 1
            assert(n == old_n - 1);
            assert(indices[n as int].as_nat() == id.as_nat());
            // id is NOT in the new live image (it sits at position n; a live
            // witness q < n would collide by injectivity).
            assert(!self.id_set().contains(id.as_nat())) by {
                if self.id_set().contains(id.as_nat()) {
                    let q = choose|q: int| 0 <= q < n && (#[trigger] indices[q]).as_nat() == id.as_nat();
                    assert(indices[q].as_nat() != indices[n as int].as_nat());
                }
            }
            assert(self.id_set() =~= old(self).id_set().remove(id.as_nat())) by {
                assert forall|v: nat| self.id_set().contains(v)
                    <==> old(self).id_set().remove(id.as_nat()).contains(v) by {
                    // forward: v new-live ⇒ v old-live (its new witness q<n maps,
                    // in both branches, back to an old live position) and v != id.
                    if self.id_set().contains(v) {
                        let q = choose|q: int| 0 <= q < n && (#[trigger] indices[q]).as_nat() == v;
                        assert(indices[q].as_nat() != indices[n as int].as_nat());  // v != id
                        // q's value came from some old live position:
                        //  - last-element branch: indices==old_indices, q<n<old_n.
                        //  - swap branch: if q==pos, indices[pos]==last_id==
                        //    old_indices[old_n-1] (old live); else indices[q]==
                        //    old_indices[q] (old live, q<n<old_n).
                        assert(old(self).id_set().contains(v)) by {
                            if pos.as_nat() == last_pos.as_nat() {
                                assert(old_indices[q].as_nat() == v);
                            } else if q == pos.as_nat() {
                                assert(indices[pos.as_nat() as int].as_nat()
                                    == old_indices[(old_n - 1) as int].as_nat());
                            } else {
                                assert(old_indices[q].as_nat() == v);
                            }
                        }
                    }
                    // reverse: v old-live and v != id ⇒ v new-live. v's old
                    // witness q0 < old_n. The only old live position that loses
                    // its value is `pos` (held id, now last_id) — but v != id,
                    // so v survives at some new position < n.
                    if old(self).id_set().remove(id.as_nat()).contains(v) {
                        let q0 = choose|q0: int| 0 <= q0 < old_n
                            && (#[trigger] old_indices[q0]).as_nat() == v;
                        assert(v != id.as_nat());
                        // old_indices[pos]==id (inverse-on-live), so q0 != pos.
                        assert(old_indices[pos.as_nat() as int].as_nat() == id.as_nat());
                        assert(q0 != pos.as_nat());
                        if pos.as_nat() == last_pos.as_nat() {
                            // last-element: indices==old_indices, q0 != pos==n,
                            // so q0 < n and indices[q0]==v.
                            assert(q0 < n);
                            assert(indices[q0].as_nat() == v);
                        } else {
                            // swap: last value (old_indices[old_n-1]) moved to pos.
                            if q0 == old_n - 1 {
                                assert(indices[pos.as_nat() as int].as_nat() == v);
                                assert(pos.as_nat() < n);
                            } else {
                                // q0 < old_n-1 == n and q0 != pos ⇒ unchanged.
                                assert(q0 < n);
                                assert(indices[q0].as_nat() == v);
                            }
                        }
                    }
                }
            }
            // pool gains id at the front: new pool is indices[n..cap], and
            // indices[n] == id, indices[n+1..cap] == old indices[n+1..cap]
            // == old pool (old pool was indices[old_n..cap] = indices[n+1..cap]).
            assert(self.free_pool() =~= old(self).free_pool().insert(0, id.as_nat())) by {
                let np = self.free_pool();
                let op = old(self).free_pool().insert(0, id.as_nat());
                assert(np.len() == op.len());
                assert forall|k: int| 0 <= k < np.len() implies np[k] == op[k] by {
                    if k == 0 {
                        assert(np[0] == indices[n as int].as_nat());
                    } else {
                        assert(np[k] == indices[n as int + k].as_nat());
                        assert(op[k] == old(self).free_pool()[k - 1]);
                        assert(old(self).free_pool()[k - 1]
                            == old_indices[old_n as int + (k - 1)].as_nat());
                        // position n+k == old_n+k-1 > n is unchanged: the swap
                        // touched only pos (< n) and last_pos (== n); the
                        // last-element branch left indices == old_indices.
                        assert(n as int + k > n);
                        assert(indices[n as int + k] == old_indices[n as int + k]);
                        assert(n as int + k == old_n as int + (k - 1));
                    }
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

/// The set of values `{ indices[p].as_nat() : 0 <= p < m }`.
pub open spec fn image_prefix<Idx: IndexLike>(indices: Seq<Idx>, m: int) -> Set<nat> {
    Set::new(|id: nat| exists|p: int| 0 <= p < m && (#[trigger] indices[p]).as_nat() == id)
}

/// An injective, in-range `indices` (over `[0, cap)`) hits every value in
/// `[0, cap)`: there is a `p < cap` with `indices[p].as_nat() == id` for each
/// `id < cap`. This is finite surjectivity-from-injectivity (pigeonhole),
/// proved via image cardinality: `|image_prefix(cap)| == cap` (each position
/// contributes a fresh value, by injectivity), and a `cap`-sized subset of the
/// `cap`-sized range `[0, cap)` must be the whole range.
pub proof fn lemma_perm_surjective<Idx: IndexLike>(indices: Seq<Idx>, cap: int, id: nat)
    requires
        cap <= indices.len(),
        id < cap,
        forall|p: int| 0 <= p < cap ==> (#[trigger] indices[p]).as_nat() < cap,
        forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat(),
    ensures
        exists|p: int| 0 <= p < cap && (#[trigger] indices[p]).as_nat() == id,
{
    lemma_image_prefix_card(indices, cap);
    let img = image_prefix(indices, cap);
    let rng = Set::new(|v: nat| v < cap);
    // img subset of rng (in-range), both size cap ⇒ equal ⇒ id in img.
    assert(img.subset_of(rng)) by {
        assert forall|v: nat| img.contains(v) implies rng.contains(v) by {
            let p = choose|p: int| 0 <= p < cap && (#[trigger] indices[p]).as_nat() == v;
        }
    }
    lemma_nat_range_card(cap);
    vstd::set_lib::lemma_len_subset(img, rng);
    vstd::set_lib::lemma_subset_equality(img, rng);
    assert(rng.contains(id));
    assert(img.contains(id));
}

/// `|image_prefix(indices, m)| == m` for injective in-range `indices`, by
/// induction on `m`: the value at position `m-1` is fresh (injectivity), so it
/// extends the prefix image by exactly one.
pub proof fn lemma_image_prefix_card<Idx: IndexLike>(indices: Seq<Idx>, m: int)
    requires
        0 <= m <= indices.len(),
        forall|p: int, q: int| 0 <= p < m && 0 <= q < m && p != q ==>
            (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat(),
    ensures
        image_prefix(indices, m).finite(),
        image_prefix(indices, m).len() == m,
    decreases m,
{
    if m == 0 {
        assert(image_prefix(indices, 0) =~= Set::<nat>::empty());
    } else {
        lemma_image_prefix_card(indices, m - 1);
        let prev = image_prefix(indices, m - 1);
        let cur = image_prefix(indices, m);
        let last = indices[m - 1].as_nat();
        // last is not in prev (injectivity: no p < m-1 equals position m-1).
        assert(!prev.contains(last)) by {
            if prev.contains(last) {
                let p = choose|p: int| 0 <= p < m - 1 && (#[trigger] indices[p]).as_nat() == last;
                assert(indices[p].as_nat() != indices[m - 1].as_nat());
            }
        }
        // cur == prev ∪ {last}.
        assert(cur =~= prev.insert(last)) by {
            assert forall|v: nat| cur.contains(v) <==> prev.insert(last).contains(v) by {
                if cur.contains(v) {
                    let p = choose|p: int| 0 <= p < m && (#[trigger] indices[p]).as_nat() == v;
                    if p < m - 1 { assert(prev.contains(v)); } else { assert(v == last); }
                }
            }
        }
        assert(cur.len() == prev.len() + 1);
    }
}

/// `{ v : v < cap }` is finite with size `cap`.
pub proof fn lemma_nat_range_card(cap: int)
    requires cap >= 0,
    ensures
        Set::new(|v: nat| v < cap).finite(),
        Set::new(|v: nat| v < cap).len() == cap,
    decreases cap,
{
    if cap == 0 {
        assert(Set::new(|v: nat| v < 0) =~= Set::<nat>::empty());
    } else {
        lemma_nat_range_card(cap - 1);
        assert(Set::new(|v: nat| v < cap)
            =~= Set::new(|v: nat| v < cap - 1).insert((cap - 1) as nat));
    }
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
