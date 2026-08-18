// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Incremental layer over [`DenseSpanMap`]: a base generation plus one delta
//! generation, with per-key invalidation (verified).
//!
//! `DenseSpanMap` is built once and read many times. A consumer that rebuilds
//! it every round pays O(base) per round even when the round changed a handful
//! of keys. `LayeredSpanMap<V>` keeps the previous round's map as a `base`,
//! represents the round's additions as a `delta` built over the same key space,
//! and records the keys whose base bucket the round invalidated. The logical
//! contents of key `k` are then
//!
//! ```text
//! view(k) == (if invalidated(k) { empty } else { base.view(k) }) ++ delta.view(k)
//! ```
//!
//! and the whole map refines a single logical stream: the base stream with the
//! invalidated keys' entries removed, followed by the delta stream
//! (`refines()`). The three properties `DenseSpanMap` establishes are restated
//! against that logical stream, so a consumer reasons about one sequence per key
//! and not about two generations.
//!
//! Invalidation is per KEY, not per (key, value) pair. That is the decision this
//! module turns on and `doc/design/16-layered-span-map.md` argues: a per-pair
//! tombstone set makes the base segment non-contiguous, and a non-contiguous
//! segment cannot be handed to a galloping seek, which is the entire reason the
//! values live in a flat pool. Per-key invalidation keeps both segments
//! contiguous, so `get` returns two slices and costs one binary search over the
//! invalidated-key list.
//!
//! Exactly one delta layer is kept. `flatten` rebuilds a single `DenseSpanMap`
//! equal to the logical view, and `needs_flatten` is the threshold predicate the
//! caller drives it with. Stacking N layers would make `get` return N slices and
//! turn the consumer's seek into an N-way merge; the read path is the hot path,
//! so the layer count is pinned at two and the cost is moved into an amortized
//! rebuild.

use vstd::prelude::*;

verus! {

use crate::dense_span_map::DenseSpanMap;
use vstd::seq_lib::*;

// ---------------------------------------------------------------------------
// Named spec functions (same discipline as `dense_span_map`: a predicate handed
// to `Seq::filter` is produced by a named spec fn, never by an inline closure,
// so the term an invariant carries and the term a lemma receives are identical).
// ---------------------------------------------------------------------------
/// "This stream entry's key was not invalidated."
pub open spec fn not_invalidated<V>(inv: Seq<usize>) -> spec_fn((usize, V)) -> bool {
    |p: (usize, V)| !inv.contains(p.0)
}

/// Strictly ascending, stated one adjacent pair at a time.
///
/// The pairwise phrasing (`forall|i, j| i < j ==> s[i] < s[j]`) is the
/// quadratic-trigger shape the proof-performance playbook section 9 records; the
/// pairwise fact is derived on demand by [`lemma_ascending_pairwise`].
pub open spec fn strictly_ascending(s: Seq<usize>) -> bool {
    forall|i: int| 0 <= i && i + 1 < s.len() ==> (#[trigger] s[i]) < s[i + 1]
}

/// In a strictly ascending sequence, order follows index.
pub proof fn lemma_ascending_pairwise(s: Seq<usize>, i: int, j: int)
    requires
        strictly_ascending(s),
        0 <= i < j < s.len(),
    ensures
        s[i] < s[j],
    decreases j - i,
{
    if i + 1 < j {
        lemma_ascending_pairwise(s, i, j - 1);
        assert(0 <= (j - 1) && (j - 1) + 1 < s.len());
        assert(s[j - 1] < s[j]);
    }
}

// ---------------------------------------------------------------------------
// Bare-sequence lemmas about the logical stream.
// ---------------------------------------------------------------------------
/// `key_slice` distributes over concatenation: the per-key filter of `a ++ b` is
/// the filter of `a` followed by the filter of `b`. This is what lets the
/// two-segment `view` and the one-stream `refines` be the same statement.
pub proof fn lemma_key_slice_add<V>(a: Seq<(usize, V)>, b: Seq<(usize, V)>, k: nat)
    ensures
        crate::dense_span_map::key_slice(a + b, k) == crate::dense_span_map::key_slice(a, k) + crate::dense_span_map::key_slice(b, k),
{
    Seq::filter_distributes_over_add(a, b, crate::dense_span_map::is_key::<V>(k));
    let fa = a.filter(crate::dense_span_map::is_key::<V>(k));
    let fb = b.filter(crate::dense_span_map::is_key::<V>(k));
    assert((fa + fb).map_values(crate::dense_span_map::snd::<V>()) =~= fa.map_values(crate::dense_span_map::snd::<V>()) + fb.map_values(
        crate::dense_span_map::snd::<V>(),
    ));
}

/// Dropping the invalidated keys' entries empties exactly those keys and leaves
/// every other key's filtered stream alone. Stated over the pair sequences;
/// [`lemma_key_slice_filter_invalid`] is the `key_slice` corollary.
pub proof fn lemma_filter_invalid<V>(s: Seq<(usize, V)>, inv: Seq<usize>, k: usize)
    ensures
        inv.contains(k) ==> s.filter(not_invalidated::<V>(inv)).filter(
            crate::dense_span_map::is_key::<V>(k as nat),
        ) == Seq::<(usize, V)>::empty(),
        !inv.contains(k) ==> s.filter(not_invalidated::<V>(inv)).filter(
            crate::dense_span_map::is_key::<V>(k as nat),
        ) == s.filter(crate::dense_span_map::is_key::<V>(k as nat)),
    decreases s.len(),
{
    reveal(Seq::filter);
    let np = not_invalidated::<V>(inv);
    let kp = crate::dense_span_map::is_key::<V>(k as nat);
    if s.len() == 0 {
        assert(s.filter(np) =~= s);
        assert(s.filter(kp) =~= s);
    } else {
        let rest = s.drop_last();
        let last = s.last();
        assert(s =~= rest.push(last));
        lemma_filter_invalid(rest, inv, k);
        rest.lemma_filter_push(last, np);
        rest.lemma_filter_push(last, kp);
        rest.filter(np).lemma_filter_push(last, kp);
        // An entry cannot both survive the invalidation filter and carry an
        // invalidated key, which is the only case the two branches differ on.
        if inv.contains(k) {
            assert(!(np(last) && kp(last)));
        }
    }
}

/// `key_slice` form of [`lemma_filter_invalid`].
pub proof fn lemma_key_slice_filter_invalid<V>(s: Seq<(usize, V)>, inv: Seq<usize>, k: usize)
    ensures
        inv.contains(k) ==> crate::dense_span_map::key_slice(s.filter(not_invalidated::<V>(inv)), k as nat)
            == Seq::<V>::empty(),
        !inv.contains(k) ==> crate::dense_span_map::key_slice(s.filter(not_invalidated::<V>(inv)), k as nat) == crate::dense_span_map::key_slice(
            s,
            k as nat,
        ),
{
    lemma_filter_invalid::<V>(s, inv, k);
    if inv.contains(k) {
        assert(Seq::<(usize, V)>::empty().map_values(crate::dense_span_map::snd::<V>()) =~= Seq::<V>::empty());
    }
}

/// Concatenating two sorted sequences yields a sorted sequence when every
/// element of the first precedes every element of the second.
///
/// THE cross-generation lemma. The separation hypothesis is not automatic: it is
/// a property of how the caller assigns values across generations, and
/// `doc/design/16-layered-span-map.md` states the obligation that discharges it.
pub proof fn lemma_concat_sorted<A>(a: Seq<A>, b: Seq<A>, rel: spec_fn(A, A) -> bool)
    requires
        vstd::relations::sorted_by(a, rel),
        vstd::relations::sorted_by(b, rel),
        forall|i: int, j: int|
            0 <= i < a.len() && 0 <= j < b.len() ==> #[trigger] rel(a[i], b[j]),
    ensures
        vstd::relations::sorted_by(a + b, rel),
{
    assert forall|i: int, j: int| 0 <= i < j < (a + b).len() implies #[trigger] rel(
        (a + b)[i],
        (a + b)[j],
    ) by {
        if j < a.len() {
            assert((a + b)[i] == a[i]);
            assert((a + b)[j] == a[j]);
        } else if a.len() <= i {
            assert((a + b)[i] == b[i - a.len()]);
            assert((a + b)[j] == b[j - a.len()]);
            assert(0 <= i - a.len() < j - a.len() < b.len());
        } else {
            assert((a + b)[i] == a[i]);
            assert((a + b)[j] == b[j - a.len()]);
            assert(0 <= j - a.len() < b.len());
        }
    }
}

// ---------------------------------------------------------------------------
// The container
// ---------------------------------------------------------------------------
/// A base generation, one delta generation, and the keys whose base bucket the
/// delta invalidated.
pub struct LayeredSpanMap<V: Copy + Default> {
    pub(crate) base: DenseSpanMap<V>,
    pub(crate) delta: DenseSpanMap<V>,
    /// Strictly ascending, every entry below the key count. Strictness is what
    /// makes the read path a binary search rather than a scan.
    pub(crate) invalid: std::vec::Vec<usize>,
}

impl<V: Copy + Default> LayeredSpanMap<V> {
    /// "Key `k`'s base bucket was dropped by the delta generation."
    pub open(crate) spec fn invalidated(&self, k: int) -> bool {
        exists|i: int| 0 <= i < self.invalid@.len() && (#[trigger] self.invalid@[i]) as int == k
    }

    /// The surviving base segment of key `k`.
    pub open(crate) spec fn base_segment(&self, k: int) -> Seq<V> {
        if self.invalidated(k) {
            Seq::<V>::empty()
        } else {
            self.base.view()[k]
        }
    }

    /// The delta segment of key `k`.
    pub open(crate) spec fn delta_segment(&self, k: int) -> Seq<V> {
        self.delta.view()[k]
    }

    /// The logical contents: surviving base followed by delta, per key.
    pub open(crate) spec fn view(&self) -> Seq<Seq<V>> {
        Seq::new(
            self.base.view().len(),
            |k: int| self.base_segment(k) + self.delta_segment(k),
        )
    }

    /// The single stream the layered map refines: the base stream with the
    /// invalidated keys removed, followed by the delta stream.
    pub open(crate) spec fn logical_stream(&self) -> Seq<(usize, V)> {
        self.base.stream_view().filter(not_invalidated::<V>(self.invalid@))
            + self.delta.stream_view()
    }

    /// Structural well-formedness. Purely structural (playbook section 4): the
    /// refinement is the separate `refines()`.
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.base.wf()
        &&& self.delta.wf()
        &&& self.base.view().len() == self.delta.view().len()
        &&& strictly_ascending(self.invalid@)
        &&& forall|i: int|
            0 <= i < self.invalid@.len() ==> (#[trigger] self.invalid@[i]) < self.base.view().len()
    }

    /// Refinement to the logical stream: no invented and no dropped values,
    /// order preserved, stated exactly as `DenseSpanMap::refines` is.
    pub open(crate) spec fn refines(&self) -> bool {
        forall|k: int|
            0 <= k < self.view().len() ==> #[trigger] self.view()[k] == crate::dense_span_map::key_slice(
                self.logical_stream(),
                k as nat,
            )
    }

    /// Key count.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self.view().len(),
    {
        self.base.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        ensures
            b == (self.view().len() == 0),
    {
        self.base.is_empty()
    }

    /// Value count of the delta generation (spec counterpart: fields are `pub(crate)`,
    /// so public contracts phrase counts through these).
    pub open(crate) spec fn delta_total_spec(&self) -> nat {
        self.delta.total_spec()
    }

    /// Value count of the base generation, including invalidated keys' values.
    pub open(crate) spec fn base_total_spec(&self) -> nat {
        self.base.total_spec()
    }

    /// Number of invalidated keys.
    pub open(crate) spec fn invalid_count_spec(&self) -> nat {
        self.invalid@.len()
    }

    /// Number of values the delta generation holds.
    pub fn delta_total(&self) -> (n: usize)
        ensures
            n == self.delta_total_spec(),
    {
        self.delta.total()
    }

    /// Number of values the base generation holds, including invalidated ones.
    pub fn base_total(&self) -> (n: usize)
        ensures
            n == self.base_total_spec(),
    {
        self.base.total()
    }

    /// Number of invalidated keys.
    pub fn invalid_count(&self) -> (n: usize)
        ensures
            n == self.invalid_count_spec(),
    {
        self.invalid.len()
    }

    /// Is key `k` invalidated? Binary search over the ascending key list, so the
    /// read path pays O(log t) in the number of invalidated keys and touches no
    /// value.
    ///
    /// Total: the postcondition is conditioned on the list being ascending
    /// rather than requiring it, so an unverified caller cannot violate a
    /// precondition.
    pub fn is_invalidated(&self, k: usize) -> (b: bool)
        ensures
            self.wf() ==> b == self.invalidated(k as int),
    {
        let mut lo: usize = 0;
        let mut hi: usize = self.invalid.len();
        while lo < hi
            invariant
                lo <= hi <= self.invalid@.len(),
                strictly_ascending(self.invalid@) ==> (self.invalidated(k as int) ==> exists|i: int|
                    lo <= i < hi && (#[trigger] self.invalid@[i]) as int == k as int),
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let probe = self.invalid[mid];
            if probe == k {
                assert(self.invalid@[mid as int] == k);
                return true;
            }
            if probe < k {
                proof {
                    // Anything at or below `mid` is <= probe < k, so a match
                    // must sit above `mid`.
                    if strictly_ascending(self.invalid@) {
                        assert forall|i: int| 0 <= i <= (mid as int) implies self.invalid@[i]
                            < k by {
                            if i < (mid as int) {
                                lemma_ascending_pairwise(self.invalid@, i, mid as int);
                            }
                        }
                    }
                }
                lo = mid + 1;
            } else {
                proof {
                    if strictly_ascending(self.invalid@) {
                        assert forall|i: int| (mid as int) <= i < self.invalid@.len() implies
                            self.invalid@[i] > k by {
                            if (mid as int) < i {
                                lemma_ascending_pairwise(self.invalid@, mid as int, i);
                            }
                        }
                    }
                }
                hi = mid;
            }
        }
        false
    }

    /// Key `k`'s logical contents, as the two segments that concatenate to it.
    ///
    /// Two slices rather than one: materializing the concatenation would copy
    /// the base bucket on every probe, which is the cost the layering exists to
    /// avoid. Both segments are contiguous, so each is directly consumable by a
    /// galloping seek.
    ///
    /// Total, with the postcondition conditioned on `wf()`.
    pub fn get(&self, k: usize) -> (r: (&[V], &[V]))
        ensures
            self.wf() && k < self.view().len() ==> {
                &&& r.0@ == self.base_segment(k as int)
                &&& r.1@ == self.delta_segment(k as int)
                &&& r.0@ + r.1@ == self.view()[k as int]
            },
    {
        let delta_slice = self.delta.get(k);
        let base_slice = self.base.get(k);
        if self.is_invalidated(k) {
            // The empty prefix of the base slice, rather than an empty array
            // literal: `split_at` carries a direct `subrange` postcondition.
            let (empty, _) = base_slice.split_at(0);
            proof {
                assert(empty@ =~= Seq::<V>::empty());
            }
            (empty, delta_slice)
        } else {
            (base_slice, delta_slice)
        }
    }

    /// Number of values under key `k`, across both generations.
    pub fn key_len(&self, k: usize) -> (n: usize)
        ensures
            self.wf() && k < self.view().len() ==> n == self.view()[k as int].len(),
    {
        let (b, d) = self.get(k);
        let bl = b.len();
        let dl = d.len();
        // Both segments are slices of pools that fit `usize`, and they are
        // disjoint parts of the logical view, so the sum cannot overflow.
        if bl > usize::MAX - dl {
            crate::guard::refuse("LayeredSpanMap::key_len: segment lengths overflow usize");
        }
        bl + dl
    }
}

// ---------------------------------------------------------------------------
// Stream lemmas used by the constructors
// ---------------------------------------------------------------------------
/// Filtering by a predicate every element satisfies is the identity.
pub proof fn lemma_filter_all<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i]),
    ensures
        s.filter(p) == s,
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let rest = s.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies p(#[trigger] rest[i]) by {
            assert(rest[i] == s[i]);
        }
        lemma_filter_all(rest, p);
        assert(s =~= rest.push(s.last()));
    }
}

/// A key no entry carries has an empty slice.
pub proof fn lemma_key_slice_absent<V>(s: Seq<(usize, V)>, j: nat)
    requires
        forall|i: int| 0 <= i < s.len() ==> ((#[trigger] s[i]).0 as nat) != j,
    ensures
        crate::dense_span_map::key_slice(s, j) == Seq::<V>::empty(),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let rest = s.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies ((#[trigger] rest[i]).0 as nat) != j by {
            assert(rest[i] == s[i]);
        }
        lemma_key_slice_absent(rest, j);
        assert(s.filter(crate::dense_span_map::is_key::<V>(j)) =~= rest.filter(
            crate::dense_span_map::is_key::<V>(j),
        ));
    }
    assert(crate::dense_span_map::key_slice(s, j) =~= Seq::<V>::empty());
}

/// Appending one entry extends exactly that key's slice.
pub proof fn lemma_key_slice_push<V>(s: Seq<(usize, V)>, k: usize, v: V, j: nat)
    ensures
        crate::dense_span_map::key_slice(s.push((k, v)), j) == if k as nat == j {
            crate::dense_span_map::key_slice(s, j).push(v)
        } else {
            crate::dense_span_map::key_slice(s, j)
        },
{
    let kp = crate::dense_span_map::is_key::<V>(j);
    s.lemma_filter_push((k, v), kp);
    if k as nat == j {
        assert(kp((k, v)));
        assert(s.filter(kp).push((k, v)).map_values(crate::dense_span_map::snd::<V>()) =~= s.filter(kp).map_values(
            crate::dense_span_map::snd::<V>(),
        ).push(v));
    }
}

impl<V: Copy + Default> LayeredSpanMap<V> {
    /// The base generation's build stream.
    pub open(crate) spec fn base_stream(&self) -> Seq<(usize, V)> {
        self.base.stream_view()
    }

    /// The delta generation's build stream.
    pub open(crate) spec fn delta_stream(&self) -> Seq<(usize, V)> {
        self.delta.stream_view()
    }

    /// The base generation's contents, per key. NOT the logical view: it is
    /// what remains if the delta generation and the invalidations are discarded.
    pub open(crate) spec fn base_view(&self) -> Seq<Seq<V>> {
        self.base.view()
    }

    /// The base generation refines its stream.
    pub open(crate) spec fn base_refines(&self) -> bool {
        self.base.refines()
    }

    /// The delta generation refines its stream.
    pub open(crate) spec fn delta_refines(&self) -> bool {
        self.delta.refines()
    }

    /// `invalidated` agrees with membership in the invalidated-key list.
    pub(crate) proof fn lemma_invalidated_contains(&self, k: usize)
        ensures
            self.invalidated(k as int) == self.invalid@.contains(k),
    {
        if self.invalidated(k as int) {
            let i = choose|i: int|
                0 <= i < self.invalid@.len() && self.invalid@[i] as int == k as int;
            assert(self.invalid@[i] == k);
        }
        if self.invalid@.contains(k) {
            let i = choose|i: int| 0 <= i < self.invalid@.len() && self.invalid@[i] == k;
            assert(self.invalid@[i] as int == k as int);
        }
    }

    /// A base generation with no delta and nothing invalidated.
    pub fn try_build_base(stream: &[(usize, V)], num_keys: usize) -> (r: Result<
        Self,
        crate::error::ContainerError,
    >)
        ensures
            r matches Ok(m) ==> m.wf(),
            r matches Ok(m) ==> m.view().len() == num_keys,
            r matches Ok(m) ==> m.base_stream() == stream@,
            r matches Ok(m) ==> m.delta_total_spec() == 0,
            r matches Ok(m) ==> m.invalid_count_spec() == 0,
            r matches Ok(m) ==> (forall|k: int|
                0 <= k < num_keys ==> #[trigger] m.view()[k] == crate::dense_span_map::key_slice(stream@, k as nat)),
            r matches Ok(m) ==> m.refines(),
            r matches Err(e) ==> e == crate::error::ContainerError::IndexOutOfBounds,
    {
        if !DenseSpanMap::can_build(stream, num_keys) {
            return Err(crate::error::ContainerError::IndexOutOfBounds);
        }
        // The empty prefix of `stream`, rather than an empty array literal:
        // `split_at` carries a direct `subrange` postcondition.
        let (empty, _) = stream.split_at(0);
        proof {
            assert(empty@ =~= Seq::<(usize, V)>::empty());
        }
        let base = DenseSpanMap::build(stream, num_keys);
        let delta = DenseSpanMap::build(empty, num_keys);
        let m = LayeredSpanMap { base, delta, invalid: std::vec::Vec::new() };
        proof {
            assert(m.invalid@ =~= Seq::<usize>::empty());
            assert forall|k: int| 0 <= k < num_keys implies #[trigger] m.view()[k] == crate::dense_span_map::key_slice(
                stream@,
                k as nat,
            ) by {
                assert(!m.invalidated(k));
                assert(m.delta.view()[k] == crate::dense_span_map::key_slice(Seq::<(usize, V)>::empty(), k as nat));
                reveal(Seq::filter);
                assert(m.delta.view()[k] =~= Seq::<V>::empty());
                assert(m.base_segment(k) + m.delta_segment(k) =~= m.base.view()[k]);
            }
            // logical_stream is the base stream unchanged: nothing is invalidated.
            lemma_filter_all(m.base.stream_view(), not_invalidated::<V>(m.invalid@));
            assert(m.logical_stream() =~= stream@);
        }
        Ok(m)
    }

    /// Install a delta generation over an existing base.
    ///
    /// `invalid` names the keys whose base bucket this generation drops; it must
    /// be strictly ascending and in range, which is what makes the read path a
    /// binary search. Cost is O(delta_stream + invalid): the base is not read.
    pub fn try_with_delta(
        base: DenseSpanMap<V>,
        delta_stream: &[(usize, V)],
        invalid: &[usize],
    ) -> (r: Result<Self, crate::error::ContainerError>)
        ensures
            r matches Ok(m) ==> (base.wf() ==> m.wf()),
            r matches Ok(m) ==> m.view().len() == base.view().len(),
            r matches Ok(m) ==> m.base_stream() == base.stream_view(),
            r matches Ok(m) ==> m.base_view() == base.view(),
            r matches Ok(m) ==> m.delta_stream() == delta_stream@,
            r matches Ok(m) ==> m.invalid_count_spec() == invalid@.len(),
            r matches Ok(m) ==> (base.refines() ==> m.refines()),
    {
        let num_keys = base.len();
        if !DenseSpanMap::can_build(delta_stream, num_keys) {
            return Err(crate::error::ContainerError::IndexOutOfBounds);
        }
        // Strictly ascending and in range.
        let mut i: usize = 0;
        let mut inv: std::vec::Vec<usize> = std::vec::Vec::new();
        while i < invalid.len()
            invariant
                i <= invalid@.len(),
                inv@.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] inv@[j] == invalid@[j],
                strictly_ascending(inv@),
                forall|j: int| 0 <= j < i ==> (#[trigger] inv@[j]) < num_keys,
            decreases invalid@.len() - i,
        {
            let x = invalid[i];
            if x >= num_keys {
                return Err(crate::error::ContainerError::IndexOutOfBounds);
            }
            if i > 0 {
                let prev = inv[i - 1];
                if !(prev < x) {
                    return Err(crate::error::ContainerError::NotSorted);
                }
            }
            inv.push(x);
            i = i + 1;
        }
        proof {
            assert(inv@ =~= invalid@);
        }

        let delta = DenseSpanMap::build(delta_stream, num_keys);
        let m = LayeredSpanMap { base, delta, invalid: inv };

        proof {
            if m.base.refines() {
                assert forall|k: int| 0 <= k < m.view().len() implies #[trigger] m.view()[k]
                    == crate::dense_span_map::key_slice(m.logical_stream(), k as nat) by {
                    lemma_key_slice_add::<V>(
                        m.base.stream_view().filter(not_invalidated::<V>(m.invalid@)),
                        m.delta.stream_view(),
                        k as nat,
                    );
                    lemma_key_slice_filter_invalid::<V>(
                        m.base.stream_view(),
                        m.invalid@,
                        k as usize,
                    );
                    m.lemma_invalidated_contains(k as usize);
                    if m.invalidated(k) {
                        assert(m.base_segment(k) =~= Seq::<V>::empty());
                    }
                }
            }
        }
        Ok(m)
    }

    /// Take the base generation back out, discarding the delta generation and
    /// the invalidations. O(1): it is a move, nothing is read or copied.
    ///
    /// The result is the BASE, not the logical view. A caller that wants the
    /// logical contents as one map wants `flatten`; this is the cheap inverse of
    /// `try_with_delta` for a caller that is about to install a different delta,
    /// and the route back to a `DenseSpanMap` for anything that needs one.
    pub fn into_base(self) -> (r: DenseSpanMap<V>)
        ensures
            r.view() == self.base_view(),
            r.stream_view() == self.base_stream(),
            r.view().len() == self.view().len(),
            self.wf() ==> r.wf(),
            self.base_refines() ==> r.refines(),
    {
        self.base
    }

    /// Install a different delta generation over the same base.
    ///
    /// THE cross-round operation: round N+1 hands in the accumulated delta
    /// stream and the accumulated invalidations, and the base carries over
    /// untouched. Cost is O(delta_stream + invalid); the base is not read, which
    /// is the whole point of the layering. `doc/design/16-layered-span-map.md`
    /// section 4 states the accumulate-and-reinstall policy this implements.
    ///
    /// The previous delta generation is discarded, so the caller accumulates the
    /// delta stream across rounds rather than handing in only the newest round's
    /// entries. Handing in only the newest round would drop the earlier rounds'
    /// additions.
    pub fn replace_delta(
        self,
        delta_stream: &[(usize, V)],
        invalid: &[usize],
    ) -> (r: Result<Self, crate::error::ContainerError>)
        ensures
            r matches Ok(m) ==> (self.wf() ==> m.wf()),
            r matches Ok(m) ==> m.view().len() == self.view().len(),
            r matches Ok(m) ==> m.base_stream() == self.base_stream(),
            r matches Ok(m) ==> m.base_view() == self.base_view(),
            r matches Ok(m) ==> m.delta_stream() == delta_stream@,
            r matches Ok(m) ==> m.invalid_count_spec() == invalid@.len(),
            r matches Ok(m) ==> (self.base_refines() ==> m.refines()),
    {
        let base = self.into_base();
        Self::try_with_delta(base, delta_stream, invalid)
    }

    /// True when the delta generation plus the invalidated keys exceed a quarter
    /// of the base. `c = 1/4` mirrors the rebuild threshold the e-graph's cache
    /// layer already uses; the caller drives `flatten` from this.
    pub fn needs_flatten(&self) -> (b: bool)
        ensures
            b == (self.delta_total_spec() + self.invalid_count_spec() > self.base_total_spec() / 4),
    {
        let d = self.delta_total();
        let n = self.invalid_count();
        if d > usize::MAX - n {
            crate::guard::refuse("LayeredSpanMap::needs_flatten: delta and invalid counts overflow");
        }
        d + n > self.base_total() / 4
    }

    /// Collapse both generations into a single `DenseSpanMap` with the same
    /// logical contents. O(base + delta); the caller amortizes it against
    /// `needs_flatten`.
    ///
    /// The rebuilt stream is grouped by key rather than in original stream
    /// order. Grouping does not change any key's slice, because a slice is the
    /// stream's filter down to that key and filtering ignores the positions of
    /// other keys' entries.
    pub fn flatten(&self) -> (r: DenseSpanMap<V>)
        ensures
            self.wf() ==> {
                &&& r.wf()
                &&& r.view().len() == self.view().len()
                &&& forall|k: int|
                    0 <= k < self.view().len() ==> #[trigger] r.view()[k] == self.view()[k]
            },
    {
        let n = self.len();
        let ghost ok = self.wf();
        let mut out: std::vec::Vec<(usize, V)> = std::vec::Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                n == self.view().len(),
                ok == self.wf(),
                forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).0 < k,
                ok ==> forall|j: int|
                    0 <= j < k ==> #[trigger] crate::dense_span_map::key_slice(out@, j as nat) == self.view()[j],
            decreases n - k,
        {
            let (bseg, dseg) = self.get(k);
            let ghost out0 = out@;

            let mut i: usize = 0;
            while i < bseg.len()
                invariant
                    i <= bseg@.len(),
                    k < n,
                    forall|q: int| 0 <= q < out0.len() ==> (#[trigger] out0[q]).0 < k,
                    forall|q: int| 0 <= q < out@.len() ==> (#[trigger] out@[q]).0 <= k,
                    forall|j: int|
                        0 <= j < n && j != k as int ==> #[trigger] crate::dense_span_map::key_slice(out@, j as nat)
                            == crate::dense_span_map::key_slice(out0, j as nat),
                    crate::dense_span_map::key_slice(out@, k as nat) == crate::dense_span_map::key_slice(out0, k as nat) + bseg@.take(i as int),
                decreases bseg@.len() - i,
            {
                let v = bseg[i];
                let ghost prev = out@;
                out.push((k, v));
                proof {
                    assert(out@ =~= prev.push((k, v)));
                    // key k: the run grows by exactly this value.
                    lemma_key_slice_push::<V>(prev, k, v, k as nat);
                    assert(bseg@.take((i + 1) as int) =~= bseg@.take(i as int).push(v));
                    assert((crate::dense_span_map::key_slice(out0, k as nat) + bseg@.take(i as int)).push(v)
                        =~= crate::dense_span_map::key_slice(out0, k as nat) + bseg@.take(i as int).push(v));
                    // every other key is untouched.
                    assert forall|j: int| 0 <= j < n && j != k as int implies #[trigger] crate::dense_span_map::key_slice(
                        out@,
                        j as nat,
                    ) == crate::dense_span_map::key_slice(out0, j as nat) by {
                        lemma_key_slice_push::<V>(prev, k, v, j as nat);
                    }
                }
                i = i + 1;
            }
            proof {
                assert(bseg@.take(bseg@.len() as int) =~= bseg@);
            }
            let ghost out1 = out@;

            let mut i2: usize = 0;
            while i2 < dseg.len()
                invariant
                    i2 <= dseg@.len(),
                    k < n,
                    crate::dense_span_map::key_slice(out1, k as nat) == crate::dense_span_map::key_slice(out0, k as nat) + bseg@,
                    forall|q: int| 0 <= q < out0.len() ==> (#[trigger] out0[q]).0 < k,
                    forall|q: int| 0 <= q < out1.len() ==> (#[trigger] out1[q]).0 <= k,
                    forall|q: int| 0 <= q < out@.len() ==> (#[trigger] out@[q]).0 <= k,
                    forall|j: int|
                        0 <= j < n && j != k as int ==> #[trigger] crate::dense_span_map::key_slice(out1, j as nat)
                            == crate::dense_span_map::key_slice(out0, j as nat),
                    forall|j: int|
                        0 <= j < n && j != k as int ==> #[trigger] crate::dense_span_map::key_slice(out@, j as nat)
                            == crate::dense_span_map::key_slice(out1, j as nat),
                    crate::dense_span_map::key_slice(out@, k as nat) == crate::dense_span_map::key_slice(out1, k as nat) + dseg@.take(i2 as int),
                decreases dseg@.len() - i2,
            {
                let v = dseg[i2];
                let ghost prev = out@;
                out.push((k, v));
                proof {
                    assert(out@ =~= prev.push((k, v)));
                    lemma_key_slice_push::<V>(prev, k, v, k as nat);
                    assert(dseg@.take((i2 + 1) as int) =~= dseg@.take(i2 as int).push(v));
                    assert((crate::dense_span_map::key_slice(out1, k as nat) + dseg@.take(i2 as int)).push(v)
                        =~= crate::dense_span_map::key_slice(out1, k as nat) + dseg@.take(i2 as int).push(v));
                    assert forall|j: int| 0 <= j < n && j != k as int implies #[trigger] crate::dense_span_map::key_slice(
                        out@,
                        j as nat,
                    ) == crate::dense_span_map::key_slice(out1, j as nat) by {
                        lemma_key_slice_push::<V>(prev, k, v, j as nat);
                    }
                }
                i2 = i2 + 1;
            }
            proof {
                assert(dseg@.take(dseg@.len() as int) =~= dseg@);
                // Key k's accumulated run is the two segments, which is view()[k].
                if ok {
                    assert(bseg@ == self.base_segment(k as int));
                    assert(dseg@ == self.delta_segment(k as int));
                    lemma_key_slice_absent::<V>(out0, k as nat);
                    assert(crate::dense_span_map::key_slice(out@, k as nat) =~= self.base_segment(k as int)
                        + self.delta_segment(k as int));
                    assert(self.view()[k as int] == self.base_segment(k as int)
                        + self.delta_segment(k as int));
                }
            }
            k = k + 1;
        }
        proof {
            assert(k == n);
        }
        DenseSpanMap::build(out.as_slice(), n)
    }
}

// ---------------------------------------------------------------------------
// Cross-generation sortedness
// ---------------------------------------------------------------------------
/// If both generations' streams are sorted and every base value under key `k`
/// precedes every delta value under key `k`, then key `k`'s logical slice is
/// sorted: the consumer may treat the two segments as one sorted run.
///
/// The separation hypothesis is the caller's obligation and is NOT implied by
/// the container. `doc/design/16-layered-span-map.md` states when it holds and
/// what to do when it does not.
pub proof fn lemma_view_sorted<V: Copy + Default>(
    m: &LayeredSpanMap<V>,
    k: int,
    rel: spec_fn(V, V) -> bool,
    entry_rel: spec_fn((usize, V), (usize, V)) -> bool,
)
    requires
        m.wf(),
        m.base_refines(),
        m.delta_refines(),
        0 <= k < m.view().len(),
        entry_rel == (|x: (usize, V), y: (usize, V)| rel(x.1, y.1)),
        vstd::relations::sorted_by(m.base_stream(), entry_rel),
        vstd::relations::sorted_by(m.delta_stream(), entry_rel),
        forall|i: int, j: int|
            0 <= i < m.base_segment(k).len() && 0 <= j < m.delta_segment(k).len()
                ==> #[trigger] rel(m.base_segment(k)[i], m.delta_segment(k)[j]),
    ensures
        vstd::relations::sorted_by(m.view()[k], rel),
{
    crate::dense_span_map::lemma_view_sorted(&m.base, k, rel, entry_rel);
    crate::dense_span_map::lemma_view_sorted(&m.delta, k, rel, entry_rel);
    assert(vstd::relations::sorted_by(m.base_segment(k), rel)) by {
        if m.invalidated(k) {
            assert(m.base_segment(k) =~= Seq::<V>::empty());
        }
    }
    lemma_concat_sorted(m.base_segment(k), m.delta_segment(k), rel);
    assert(m.view()[k] == m.base_segment(k) + m.delta_segment(k));
}


} // verus!
