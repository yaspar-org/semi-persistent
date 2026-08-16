// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Dense-keyed span multimap: build once, read many (verified).
//!
//! `DenseSpanMap<V>` stores a multimap from a dense key `k < num_keys` to a
//! sequence of values in two flat vectors: a `pool` holding every value, and a
//! `spans` vector where `spans[k]` names the half-open pool range `[off, off+len)`
//! carrying key `k`'s values. It is built in one shot from a `(key, value)`
//! stream by the standard two-pass counting sort: pass 1 counts per key and
//! prefix-sums the counts into offsets, pass 2 walks the stream again and drops
//! each value at its key's running cursor. It is read-only afterwards. There is
//! no mark/restore: the egraph rebuilds these per round, so semi-persistence
//! would only pay for a rollback nobody performs.
//!
//! Three obligations are discharged here (`doc/design/15-dense-span-map.md`):
//!
//!  1. *No wrong-slice reads.* [`DenseSpanMap::wf`] states that the spans tile the
//!     pool exactly: first span at 0, each span starting where the previous ends,
//!     last ending at `pool.len()`. Pairwise disjointness is the derived
//!     [`lemma_spans_disjoint`], not the invariant, because the natural pairwise
//!     phrasing is the quadratic-trigger shape the playbook (§9) charges 223 s for.
//!  2. *No invented and no dropped values.* [`DenseSpanMap::refines`] pins the
//!     model against the build stream: `view()[k]` is the order-preserving filter
//!     of the stream down to key `k`. Nothing else is a legal `pool` content.
//!  3. *Sortedness transfer.* [`lemma_view_sorted`] carries any ordering of the
//!     stream into every per-key slice, because a filter preserves relative order.
//!
//! `wf()` is deliberately *structural only* and `refines()` is separate (playbook
//! §4): `get` needs the tiling and nothing else, so it must not drag the
//! refinement's quantifier into scope.

use vstd::prelude::*;

verus! {

use vstd::seq_lib::*;

/// A half-open run of `pool` positions, `[off, off + len)`.
#[derive(Clone, Copy)]
pub struct Span {
    pub off: usize,
    pub len: usize,
}

// ---------------------------------------------------------------------------
// Named spec functions.
//
// Every predicate handed to `Seq::filter` is produced by one of these, never by
// an inline closure. Two syntactically identical closures are two *different*
// spec terms, so a `filter(|p| p.0 == k)` written in an invariant and another
// written at a lemma call site do not match, and vstd's filter lemmas silently
// fail to apply to the term the invariant actually carries.
// ---------------------------------------------------------------------------
/// "This stream entry carries key `k`."
pub open spec fn is_key<V>(k: nat) -> spec_fn((usize, V)) -> bool {
    |p: (usize, V)| p.0 as nat == k
}

/// "This stream entry carries a key below `k`."
pub open spec fn is_below<V>(k: nat) -> spec_fn((usize, V)) -> bool {
    |p: (usize, V)| (p.0 as nat) < k
}

/// Value projection of a stream entry.
pub open spec fn snd<V>() -> spec_fn((usize, V)) -> V {
    |p: (usize, V)| p.1
}

/// THE model of key `k`: the stream filtered to `k`, in stream order, values only.
pub open spec fn key_slice<V>(stream: Seq<(usize, V)>, k: nat) -> Seq<V> {
    stream.filter(is_key(k)).map_values(snd())
}

/// How many stream entries carry key `k` (= `key_slice`'s length).
pub open spec fn count_key<V>(stream: Seq<(usize, V)>, k: nat) -> nat {
    stream.filter(is_key(k)).len()
}

/// How many stream entries carry a key below `k`. This is the whole overflow
/// story: every `usize` obligation in `build` reduces to `offsets[k] ==
/// count_below(stream, k)`, and a count of a subsequence of `stream` is bounded
/// by `stream.len()`, which is a `usize` by construction.
pub open spec fn count_below<V>(stream: Seq<(usize, V)>, k: nat) -> nat {
    stream.filter(is_below(k)).len()
}

// ---------------------------------------------------------------------------
// Bare-sequence lemmas.
//
// All of these are stated over plain `Seq`s rather than over `self` or the build
// loop's locals. That is playbook §9: proof cost scales with what the solver can
// *see*, and a lemma with nothing but its own arguments in scope is cheap even
// when the same goal inline in an exec body is not.
// ---------------------------------------------------------------------------
/// `key_slice` and `count_key` agree on length (`map_values` preserves it).
pub proof fn lemma_key_slice_len<V>(stream: Seq<(usize, V)>, k: nat)
    ensures
        key_slice(stream, k).len() == count_key(stream, k),
{
}

/// A count of a filtered subsequence never exceeds the whole.
pub proof fn lemma_count_below_bound<V>(stream: Seq<(usize, V)>, k: nat)
    ensures
        count_below(stream, k) <= stream.len(),
{
    stream.lemma_filter_len(is_below::<V>(k));
}

/// Same, for a single key.
pub proof fn lemma_count_key_bound<V>(stream: Seq<(usize, V)>, k: nat)
    ensures
        count_key(stream, k) <= stream.len(),
{
    stream.lemma_filter_len(is_key::<V>(k));
}

/// Nothing sits below key 0.
pub proof fn lemma_count_below_zero<V>(stream: Seq<(usize, V)>)
    ensures
        count_below(stream, 0) == 0,
    decreases stream.len(),
{
    reveal(Seq::filter);
    if stream.len() > 0 {
        lemma_count_below_zero(stream.drop_last());
    }
}

/// The prefix-sum step: widening the "below" threshold by one key adds exactly
/// that key's count. This is the identity the offset accumulator is proved
/// equal to, and thereby the reason it cannot overflow.
pub proof fn lemma_count_below_step<V>(stream: Seq<(usize, V)>, k: nat)
    ensures
        count_below(stream, k + 1) == count_below(stream, k) + count_key(stream, k),
    decreases stream.len(),
{
    reveal(Seq::filter);
    if stream.len() > 0 {
        lemma_count_below_step(stream.drop_last(), k);
    }
}

/// If every key in the stream is below `num_keys`, the "below" filter keeps
/// everything: the last offset is the pool size.
pub proof fn lemma_count_below_all<V>(stream: Seq<(usize, V)>, num_keys: nat)
    requires
        forall|i: int| 0 <= i < stream.len() ==> ((#[trigger] stream[i]).0 as nat) < num_keys,
    ensures
        count_below(stream, num_keys) == stream.len(),
    decreases stream.len(),
{
    reveal(Seq::filter);
    if stream.len() > 0 {
        let rest = stream.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies ((#[trigger] rest[i]).0 as nat) < num_keys by {
            assert(rest[i] == stream[i]);
        }
        lemma_count_below_all(rest, num_keys);
    }
}

/// The tiling predicate: `spans` partitions `[0, total)` into consecutive runs.
///
/// Every clause quantifies over a *single* variable. The pairwise-disjointness
/// phrasing (`forall|i, j| ... i != j ==> ranges disjoint`) is the shape playbook
/// §9 identifies as quadratic, because a trigger set with two disjoint
/// bound-variable groups instantiates over every pair of matching terms. It is
/// derived on demand by [`lemma_spans_disjoint`] instead of asserted here.
pub open spec fn spans_tile(spans: Seq<Span>, total: nat) -> bool {
    &&& (spans.len() == 0 ==> total == 0)
    &&& (spans.len() > 0 ==> spans[0].off == 0)
    &&& (forall|k: int|
        0 <= k < spans.len() ==> (#[trigger] spans[k]).off + spans[k].len <= total)
    &&& (forall|k: int|
        0 <= k && k + 1 < spans.len() ==> (#[trigger] spans[k]).off + spans[k].len
            == spans[k + 1].off)
    &&& (spans.len() > 0 ==> spans[spans.len() - 1].off + spans[spans.len() - 1].len == total)
}

/// Spans are monotone: a later span starts at or after an earlier one ends.
pub proof fn lemma_spans_monotone(spans: Seq<Span>, total: nat, a: int, b: int)
    requires
        spans_tile(spans, total),
        0 <= a <= b < spans.len(),
    ensures
        spans[a].off + spans[a].len <= spans[b].off + spans[b].len,
        spans[a].off <= spans[b].off,
    decreases b - a,
{
    if a < b {
        lemma_spans_monotone(spans, total, a, b - 1);
        assert(0 <= (b - 1) && (b - 1) + 1 < spans.len());
        assert(spans[b - 1].off + spans[b - 1].len == spans[b].off);
    }
}

/// THE no-wrong-slice-reads property, derived from the tiling: distinct keys
/// name non-overlapping pool ranges.
pub proof fn lemma_spans_disjoint(spans: Seq<Span>, total: nat, i: int, j: int)
    requires
        spans_tile(spans, total),
        0 <= i < j < spans.len(),
    ensures
        spans[i].off + spans[i].len <= spans[j].off,
{
    lemma_spans_monotone(spans, total, i, j - 1);
    assert(0 <= (j - 1) && (j - 1) + 1 < spans.len());
    assert(spans[j - 1].off + spans[j - 1].len == spans[j].off);
}

/// Writing outside a range leaves that range's contents alone.
pub proof fn lemma_update_outside<V>(pool: Seq<V>, lo: int, hi: int, pos: int, val: V)
    requires
        0 <= lo <= hi <= pool.len(),
        0 <= pos < pool.len(),
        pos < lo || hi <= pos,
    ensures
        pool.update(pos, val).subrange(lo, hi) == pool.subrange(lo, hi),
{
    assert(pool.update(pos, val).subrange(lo, hi) =~= pool.subrange(lo, hi));
}

/// Writing at a range's one-past-the-end extends it by exactly that value.
pub proof fn lemma_update_at_end<V>(pool: Seq<V>, lo: int, pos: int, val: V)
    requires
        0 <= lo <= pos < pool.len(),
    ensures
        pool.update(pos, val).subrange(lo, pos + 1) == pool.subrange(lo, pos).push(val),
{
    assert(pool.update(pos, val).subrange(lo, pos + 1) =~= pool.subrange(lo, pos).push(val));
}

/// The placement step, over bare sequences: region `k0` is extended by `val` and
/// every other region is untouched. The build loop's locals are deliberately not
/// in scope (playbook §9).
///
/// `bound[k] == offsets[k] + counts[k]` is key `k`'s allocated extent; the
/// hypotheses say the regions are nested inside consecutive allocated extents and
/// that `k0` has room left.
pub proof fn lemma_place_step<V>(
    pool: Seq<V>,
    offsets: Seq<usize>,
    counts: Seq<usize>,
    cursor: Seq<usize>,
    n: int,
    k0: int,
    val: V,
)
    requires
        0 <= n <= offsets.len(),
        n <= counts.len(),
        n <= cursor.len(),
        0 <= k0 < n,
        forall|k: int|
            0 <= k < n ==> offsets[k] <= #[trigger] cursor[k] <= offsets[k] + counts[k],
        forall|k: int|
            0 <= k && k + 1 < n ==> (#[trigger] offsets[k]) + counts[k] == offsets[k + 1],
        cursor[k0] < offsets[k0] + counts[k0],
        forall|k: int| 0 <= k < n ==> (#[trigger] offsets[k]) + counts[k] <= pool.len(),
    ensures
        forall|k: int|
            0 <= k < n && k != k0 ==> #[trigger] pool.update(cursor[k0] as int, val).subrange(
                offsets[k] as int,
                cursor[k] as int,
            ) == pool.subrange(offsets[k] as int, cursor[k] as int),
        pool.update(cursor[k0] as int, val).subrange(
            offsets[k0] as int,
            cursor[k0] + 1,
        ) == pool.subrange(offsets[k0] as int, cursor[k0] as int).push(val),
{
    let pos = cursor[k0] as int;
    assert(pos < pool.len());
    assert forall|k: int| 0 <= k < n && k != k0 implies #[trigger] pool.update(pos, val).subrange(
        offsets[k] as int,
        cursor[k] as int,
    ) == pool.subrange(offsets[k] as int, cursor[k] as int) by {
        if k < k0 {
            // cursor[k] <= offsets[k]+counts[k] == offsets[k+1] <= offsets[k0] <= pos
            lemma_offsets_monotone(offsets, counts, n, k + 1, k0);
            assert(cursor[k] <= offsets[k] + counts[k]);
            assert(offsets[k] + counts[k] == offsets[k + 1]);
        } else {
            // offsets[k] >= offsets[k0+1] == offsets[k0]+counts[k0] > pos
            lemma_offsets_monotone(offsets, counts, n, k0 + 1, k);
            assert(offsets[k0] + counts[k0] == offsets[k0 + 1]);
        }
        lemma_update_outside(pool, offsets[k] as int, cursor[k] as int, pos, val);
    }
    lemma_update_at_end(pool, offsets[k0] as int, pos, val);
}

/// Offsets are non-decreasing (bare-sequence companion to `lemma_place_step`).
pub proof fn lemma_offsets_monotone(offsets: Seq<usize>, counts: Seq<usize>, n: int, a: int, b: int)
    requires
        0 <= n <= offsets.len(),
        n <= counts.len(),
        0 <= a <= b < n,
        forall|k: int|
            0 <= k && k + 1 < n ==> (#[trigger] offsets[k]) + counts[k] == offsets[k + 1],
    ensures
        offsets[a] <= offsets[b],
    decreases b - a,
{
    if a < b {
        lemma_offsets_monotone(offsets, counts, n, a, b - 1);
        assert(0 <= (b - 1) && (b - 1) + 1 < n);
        assert(offsets[b - 1] + counts[b - 1] == offsets[b]);
    }
}

/// Filtering preserves relative order, so it preserves sortedness under ANY
/// relation. Stated over a bare `Seq<A>` and an arbitrary relation, so the
/// container-level statement is a corollary.
///
/// The push case needs "every element of the filtered prefix came from the
/// prefix", which is vstd's `lemma_filter_contains_rev`.
pub proof fn lemma_filter_sorted<A>(s: Seq<A>, p: spec_fn(A) -> bool, r: spec_fn(A, A) -> bool)
    requires
        vstd::relations::sorted_by(s, r),
    ensures
        vstd::relations::sorted_by(s.filter(p), r),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let rest = s.drop_last();
        let last = s.last();
        assert(rest.len() == s.len() - 1);
        assert(vstd::relations::sorted_by(rest, r)) by {
            assert forall|i: int, j: int| 0 <= i < j < rest.len() implies #[trigger] r(
                rest[i],
                rest[j],
            ) by {
                assert(rest[i] == s[i]);
                assert(rest[j] == s[j]);
                assert(0 <= i < j < s.len());
            }
        }
        lemma_filter_sorted(rest, p, r);
        let fr = rest.filter(p);
        if p(last) {
            assert forall|i: int, j: int| 0 <= i < j < fr.push(last).len() implies #[trigger] r(
                fr.push(last)[i],
                fr.push(last)[j],
            ) by {
                if j < fr.len() {
                    assert(fr.push(last)[i] == fr[i]);
                    assert(fr.push(last)[j] == fr[j]);
                } else {
                    assert(fr.push(last)[j] == last);
                    assert(i < fr.len());
                    assert(fr.push(last)[i] == fr[i]);
                    // fr[i] is in fr, hence in rest, hence at some rest index,
                    // and every rest index precedes s's last position.
                    assert(fr.contains(fr[i]));
                    rest.lemma_filter_contains_rev(p, fr[i]);
                    assert(rest.contains(fr[i]));
                    let w = choose|w: int| 0 <= w < rest.len() && rest[w] == fr[i];
                    assert(rest[w] == s[w]);
                    assert(0 <= w < s.len() - 1);
                    assert(s[s.len() - 1] == last);
                    assert(r(s[w], s[s.len() - 1]));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The container
// ---------------------------------------------------------------------------
/// Build-once dense-keyed multimap.
///
/// `V: Default` supplies the pass-2 filler: the pool is sized up front and every
/// slot is then overwritten by pass 2 (the spans tile the pool exactly, so no
/// filler survives in any readable range). The filler is therefore unobservable,
/// the same argument `doc/design/07-default-impls.md` makes for restore-regrow.
pub struct DenseSpanMap<V: Copy + Default> {
    pub(crate) pool: std::vec::Vec<V>,
    pub(crate) spans: std::vec::Vec<Span>,
    /// Ghost record of the stream this map was built from. `refines()` is stated
    /// against it, so the model obligation survives past `build`'s return.
    /// (Spec-only: erased in plain builds, hence `dead_code`.)
    #[allow(dead_code)]
    pub(crate) stream: Ghost<Seq<(usize, V)>>,
}

impl<V: Copy + Default> DenseSpanMap<V> {
    /// The abstract contents: one value sequence per key.
    pub open(crate) spec fn view(&self) -> Seq<Seq<V>> {
        Seq::new(
            self.spans@.len(),
            |k: int|
                self.pool@.subrange(
                    self.spans@[k].off as int,
                    self.spans@[k].off + self.spans@[k].len,
                ),
        )
    }

    /// The stream this map was built from.
    pub open(crate) spec fn stream_view(&self) -> Seq<(usize, V)> {
        self.stream@
    }

    /// Structural well-formedness: the spans tile the pool exactly.
    ///
    /// Purely structural on purpose (playbook §4). `get` needs in-bounds-ness and
    /// nothing more; if `wf` also carried the refinement, every `get` would pull a
    /// `forall k` over filtered sequences into the solver's scope for no reason.
    pub open(crate) spec fn wf(&self) -> bool {
        spans_tile(self.spans@, self.pool@.len())
    }

    /// Refinement to the build stream: key `k`'s slice IS the stream filtered to
    /// `k`. Separate from `wf` so it is loaded only where it is used.
    pub open(crate) spec fn refines(&self) -> bool {
        forall|k: int|
            0 <= k < self.spans@.len() ==> #[trigger] self.view()[k] == key_slice(
                self.stream@,
                k as nat,
            )
    }

    /// Number of keys.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self.view().len(),
    {
        self.spans.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        ensures
            b == (self.view().len() == 0),
    {
        self.spans.len() == 0
    }

    /// Key `k`'s values, as a slice into the pool.
    ///
    /// Total, with a documented panic (same protocol as `AppendOnlyVec::get`):
    /// the two bound branches are O(1) and are exactly what carving the slice
    /// needs, so no `requires` is exposed to unverified callers. For a `wf()`
    /// map neither branch is reachable: the tiling makes both checks dead.
    ///
    /// The slice is carved with two `split_at`s rather than `&pool[a..b]`: the
    /// range-index route reaches the pool through vstd's `call_ensures`-shaped
    /// `Index` specification, whereas `split_at` carries a direct `subrange`
    /// postcondition.
    pub fn get(&self, k: usize) -> (r: &[V])
        ensures
            k < self.view().len() ==> r@ == self.view()[k as int],
    {
        if !(k < self.spans.len()) {
            crate::guard::refuse("DenseSpanMap::get: key out of range");
        }
        let span = self.spans[k];
        let n = self.pool.len();
        if !(span.off <= n && span.len <= n - span.off) {
            crate::guard::refuse("DenseSpanMap::get: span outside pool");
        }
        let (_, tail) = self.pool.as_slice().split_at(span.off);
        let (out, _) = tail.split_at(span.len);
        proof {
            assert(span == self.spans@[k as int]);
            assert(out@ =~= self.pool@.subrange(span.off as int, span.off + span.len));
        }
        out
    }

    /// Total shell: `None` rather than a panic when the key is out of range.
    pub fn try_get(&self, k: usize) -> (r: Option<&[V]>)
        ensures
            k < self.view().len() ==> (r matches Some(s) && s@ == self.view()[k as int]),
            k >= self.view().len() ==> r is None,
    {
        if k < self.spans.len() {
            Some(self.get(k))
        } else {
            None
        }
    }

    /// Number of values under key `k`. Total, same protocol as `get`.
    pub fn key_len(&self, k: usize) -> (n: usize)
        ensures
            k < self.view().len() ==> n == self.view()[k as int].len(),
    {
        if !(k < self.spans.len()) {
            crate::guard::refuse("DenseSpanMap::key_len: key out of range");
        }
        let span = self.spans[k];
        let n = self.pool.len();
        if !(span.off <= n && span.len <= n - span.off) {
            crate::guard::refuse("DenseSpanMap::key_len: span outside pool");
        }
        proof {
            assert(span == self.spans@[k as int]);
        }
        span.len
    }

    /// Pool size (spec twin of `total()`; fields are `pub(crate)`, so the public
    /// contract phrases the value count through this).
    pub open(crate) spec fn total_spec(&self) -> nat {
        self.pool@.len()
    }

    /// Total number of values across all keys.
    pub fn total(&self) -> (n: usize)
        ensures
            n == self.total_spec(),
    {
        self.pool.len()
    }

    /// Exec twin of `build`'s precondition: every key in the stream is in range.
    pub fn can_build(stream: &[(usize, V)], num_keys: usize) -> (b: bool)
        ensures
            b == (forall|i: int|
                0 <= i < stream@.len() ==> (#[trigger] stream@[i]).0 < num_keys),
    {
        let mut i: usize = 0;
        while i < stream.len()
            invariant
                i <= stream@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] stream@[j]).0 < num_keys,
            decreases stream@.len() - i,
        {
            if stream[i].0 >= num_keys {
                return false;
            }
            i = i + 1;
        }
        true
    }

    /// Two-pass counting build.
    ///
    /// Pass 1 counts each key's population and prefix-sums the counts into
    /// offsets; pass 2 walks the stream again, placing each value at its key's
    /// running cursor. The result is the order-preserving per-key filter of the
    /// stream, which is what `refines()` states.
    pub(crate) fn build(stream: &[(usize, V)], num_keys: usize) -> (r: Self)
        requires
            forall|i: int| 0 <= i < stream@.len() ==> (#[trigger] stream@[i]).0 < num_keys,
        ensures
            r.wf(),
            r.view().len() == num_keys,
            r.stream_view() == stream@,
            r.total_spec() == stream@.len(),
            r.refines(),
            forall|k: int|
                0 <= k < num_keys ==> #[trigger] r.view()[k] == key_slice(stream@, k as nat),
    {
        let ghost s = stream@;

        // ---- pass 1a: per-key counts ----
        let mut counts: std::vec::Vec<usize> = std::vec::Vec::new();
        let mut c: usize = 0;
        while c < num_keys
            invariant
                c <= num_keys,
                counts@.len() == c,
                forall|j: int| 0 <= j < c ==> #[trigger] counts@[j] == 0,
            decreases num_keys - c,
        {
            counts.push(0);
            c = c + 1;
        }

        let mut i: usize = 0;
        proof {
            assert(s.take(0int) =~= Seq::<(usize, V)>::empty());
            reveal(Seq::filter);
        }
        while i < stream.len()
            invariant
                i <= s.len(),
                stream@ == s,
                counts@.len() == num_keys,
                forall|j: int| 0 <= j < s.len() ==> (#[trigger] s[j]).0 < num_keys,
                forall|k: int|
                    0 <= k < num_keys ==> #[trigger] counts@[k] == count_key(
                        s.take(i as int),
                        k as nat,
                    ),
            decreases s.len() - i,
        {
            let key = stream[i].0;
            let ghost prefix = s.take(i as int);
            proof {
                assert(key == s[i as int].0);
                assert(s[i as int].0 < num_keys);  // fires the key-bound invariant
                assert(s.take((i + 1) as int) =~= prefix.push(s[i as int]));
                lemma_count_key_bound(prefix, key as nat);
                assert(prefix.len() == i);
                // cur == count_key(prefix, key) <= prefix.len() == i < s.len(),
                // so the increment cannot overflow.
                assert(counts@[key as int] <= i);
            }
            let cur = counts[key];
            counts[key] = cur + 1;
            proof {
                assert forall|k: int| 0 <= k < num_keys implies #[trigger] counts@[k] == count_key(
                    s.take((i + 1) as int),
                    k as nat,
                ) by {
                    prefix.lemma_filter_len_push(is_key::<V>(k as nat), s[i as int]);
                }
            }
            i = i + 1;
        }
        proof {
            assert(s.take(s.len() as int) =~= s);
        }

        // ---- pass 1b: prefix sums ----
        let mut offsets: std::vec::Vec<usize> = std::vec::Vec::new();
        let mut cursor: std::vec::Vec<usize> = std::vec::Vec::new();
        let mut acc: usize = 0;
        let mut k: usize = 0;
        proof {
            lemma_count_below_zero(s);
        }
        let stream_len: usize = stream.len();
        while k < num_keys
            invariant
                k <= num_keys,
                s.len() == stream_len,
                counts@.len() == num_keys,
                forall|j: int| 0 <= j < num_keys ==> #[trigger] counts@[j] == count_key(s, j as nat),
                offsets@.len() == k,
                cursor@ == offsets@,
                acc == count_below(s, k as nat),
                forall|j: int|
                    0 <= j < k ==> #[trigger] offsets@[j] == count_below(s, j as nat),
            decreases num_keys - k,
        {
            offsets.push(acc);
            cursor.push(acc);
            proof {
                // acc + counts[k] == count_below(s, k) + count_key(s, k)
                //                 == count_below(s, k+1) <= s.len() <= usize::MAX.
                lemma_count_below_step(s, k as nat);
                lemma_count_below_bound(s, (k + 1) as nat);
                assert(acc + counts@[k as int] == count_below(s, (k + 1) as nat));
                assert(count_below(s, (k + 1) as nat) <= s.len());
                assert(s.len() == stream_len);  // a usize, hence <= usize::MAX
            }
            acc = acc + counts[k];
            k = k + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < s.len() implies ((#[trigger] s[j]).0 as nat)
                < num_keys as nat by {
                assert(s[j].0 < num_keys);
            }
            lemma_count_below_all(s, num_keys as nat);
        }
        let total = acc;

        // The two facts pass 2 needs about the offset table: consecutive keys'
        // allocated extents abut, and none runs past the pool.
        proof {
            assert forall|j: int| 0 <= j && j + 1 < num_keys implies (#[trigger] offsets@[j])
                + counts@[j] == offsets@[j + 1] by {
                lemma_count_below_step(s, j as nat);
            }
            assert forall|j: int| 0 <= j < num_keys implies (#[trigger] offsets@[j]) + counts@[j]
                <= total by {
                lemma_count_below_step(s, j as nat);
                lemma_count_below_bound(s, (j + 1) as nat);
            }
        }

        // ---- pass 2: placement ----
        let mut pool: std::vec::Vec<V> = std::vec::Vec::new();
        pool.resize(total, V::default());

        let mut i2: usize = 0;
        proof {
            assert(s.take(0int) =~= Seq::<(usize, V)>::empty());
            assert forall|k: int| 0 <= k < num_keys implies #[trigger] pool@.subrange(
                offsets@[k] as int,
                cursor@[k] as int,
            ) == key_slice(s.take(0int), k as nat) by {
                reveal(Seq::filter);
                assert(pool@.subrange(offsets@[k] as int, cursor@[k] as int) =~= Seq::<V>::empty());
                assert(key_slice(Seq::<(usize, V)>::empty(), k as nat) =~= Seq::<V>::empty());
            }
        }
        while i2 < stream.len()
            invariant
                i2 <= s.len(),
                stream@ == s,
                pool@.len() == total,
                total == s.len(),
                counts@.len() == num_keys,
                offsets@.len() == num_keys,
                cursor@.len() == num_keys,
                forall|j: int| 0 <= j < s.len() ==> (#[trigger] s[j]).0 < num_keys,
                forall|j: int| 0 <= j < num_keys ==> #[trigger] counts@[j] == count_key(s, j as nat),
                forall|j: int|
                    0 <= j < num_keys ==> #[trigger] offsets@[j] == count_below(s, j as nat),
                forall|j: int|
                    0 <= j && j + 1 < num_keys ==> (#[trigger] offsets@[j]) + counts@[j]
                        == offsets@[j + 1],
                forall|j: int|
                    0 <= j < num_keys ==> (#[trigger] offsets@[j]) + counts@[j] <= total,
                forall|j: int|
                    0 <= j < num_keys ==> #[trigger] cursor@[j] == offsets@[j] + count_key(
                        s.take(i2 as int),
                        j as nat,
                    ),
                forall|j: int|
                    0 <= j < num_keys ==> #[trigger] pool@.subrange(
                        offsets@[j] as int,
                        cursor@[j] as int,
                    ) == key_slice(s.take(i2 as int), j as nat),
            decreases s.len() - i2,
        {
            let key = stream[i2].0;
            let val = stream[i2].1;
            let ghost prefix = s.take(i2 as int);
            proof {
                assert(key == s[i2 as int].0);
                assert(s[i2 as int].0 < num_keys);  // fires the key-bound invariant
            }
            let pos = cursor[key];
            let ghost pool0 = pool@;

            proof {
                assert(s.take((i2 + 1) as int) =~= prefix.push(s[i2 as int]));
                // key has room left: the entry at i2 is a key-`key` entry not yet
                // placed, so the prefix count is strictly below the total count.
                assert(is_key::<V>(key as nat)(s[i2 as int]));
                prefix.lemma_filter_len_push(is_key::<V>(key as nat), s[i2 as int]);
                assert(count_key(s.take((i2 + 1) as int), key as nat) == count_key(
                    prefix,
                    key as nat,
                ) + 1);
                s.lemma_filter_take_len(is_key::<V>(key as nat), (i2 + 1) as int);
                assert(count_key(s.take((i2 + 1) as int), key as nat) <= count_key(s, key as nat));
                assert(cursor@[key as int] < offsets@[key as int] + counts@[key as int]);
                // Every cursor sits inside its key's allocated extent: the prefix
                // count never exceeds the whole-stream count.
                assert forall|j: int| 0 <= j < num_keys implies offsets@[j] <= #[trigger] cursor@[j]
                    <= offsets@[j] + counts@[j] by {
                    s.lemma_filter_take_len(is_key::<V>(j as nat), i2 as int);
                }
                lemma_place_step(
                    pool@,
                    offsets@,
                    counts@,
                    cursor@,
                    num_keys as int,
                    key as int,
                    val,
                );
            }

            pool[pos] = val;
            cursor[key] = pos + 1;

            proof {
                assert(pool@ == pool0.update(pos as int, val));
                assert forall|j: int| 0 <= j < num_keys implies #[trigger] pool@.subrange(
                    offsets@[j] as int,
                    cursor@[j] as int,
                ) == key_slice(s.take((i2 + 1) as int), j as nat) by {
                    prefix.lemma_filter_push(s[i2 as int], is_key::<V>(j as nat));
                    if j != key as int {
                        // untouched region, and the filtered prefix is unchanged
                    } else {
                        assert(key_slice(prefix.push(s[i2 as int]), j as nat) =~= key_slice(
                            prefix,
                            j as nat,
                        ).push(val));
                    }
                }
                assert forall|j: int| 0 <= j < num_keys implies #[trigger] cursor@[j] == offsets@[j]
                    + count_key(s.take((i2 + 1) as int), j as nat) by {
                    prefix.lemma_filter_len_push(is_key::<V>(j as nat), s[i2 as int]);
                }
            }
            i2 = i2 + 1;
        }
        proof {
            assert(s.take(s.len() as int) =~= s);
        }

        // ---- spans ----
        let mut spans: std::vec::Vec<Span> = std::vec::Vec::new();
        let mut k2: usize = 0;
        while k2 < num_keys
            invariant
                k2 <= num_keys,
                spans@.len() == k2,
                counts@.len() == num_keys,
                offsets@.len() == num_keys,
                forall|j: int|
                    0 <= j < k2 ==> (#[trigger] spans@[j]).off == offsets@[j] && spans@[j].len
                        == counts@[j],
            decreases num_keys - k2,
        {
            spans.push(Span { off: offsets[k2], len: counts[k2] });
            k2 = k2 + 1;
        }

        let r = DenseSpanMap { pool, spans, stream: Ghost(s) };

        proof {
            assert(r.spans@.len() == num_keys);
            assert(r.pool@.len() == total);
            // tiling
            assert(r.wf()) by {
                if num_keys > 0 {
                    lemma_count_below_zero(s);
                    assert(r.spans@[0].off == offsets@[0] == 0);
                    let last = num_keys - 1;
                    lemma_count_below_step(s, last as nat);
                    assert(r.spans@[last].off + r.spans@[last].len == count_below(
                        s,
                        (last + 1) as nat,
                    ));
                    assert(count_below(s, num_keys as nat) == total);
                }
            }
            assert forall|k: int| 0 <= k < num_keys implies #[trigger] r.view()[k] == key_slice(
                s,
                k as nat,
            ) by {
                assert(r.view()[k] == r.pool@.subrange(
                    r.spans@[k].off as int,
                    r.spans@[k].off + r.spans@[k].len,
                ));
                assert(cursor@[k] == offsets@[k] + count_key(s, k as nat));
                lemma_key_slice_len(s, k as nat);
                assert(r.spans@[k].off + r.spans@[k].len == cursor@[k]);
            }
        }
        r
    }

    /// Total shell: refuses a stream carrying an out-of-range key instead of
    /// panicking in pass 1.
    pub fn try_build(stream: &[(usize, V)], num_keys: usize) -> (r: Result<
        Self,
        crate::error::ContainerError,
    >)
        ensures
            r matches Ok(m) ==> {
                &&& m.wf()
                &&& m.view().len() == num_keys
                &&& m.stream_view() == stream@
                &&& m.total_spec() == stream@.len()
                &&& m.refines()
            },
            r matches Err(e) ==> e == crate::error::ContainerError::IndexOutOfBounds,
    {
        if Self::can_build(stream, num_keys) {
            Ok(Self::build(stream, num_keys))
        } else {
            Err(crate::error::ContainerError::IndexOutOfBounds)
        }
    }
}

// ---------------------------------------------------------------------------
// Composite keys
// ---------------------------------------------------------------------------
/// Flatten a two-dimensional key `(a, b)` with `b < bcount` into one dense key.
pub open spec fn composite_key_spec(a: nat, b: nat, bcount: nat) -> nat {
    a * bcount + b
}

/// The flattening is injective on its intended domain, so a `DenseSpanMap` keyed
/// by `composite_key` never conflates two distinct `(a, b)` pairs.
pub proof fn lemma_composite_key_injective(
    a1: nat,
    b1: nat,
    a2: nat,
    b2: nat,
    bcount: nat,
)
    requires
        b1 < bcount,
        b2 < bcount,
        composite_key_spec(a1, b1, bcount) == composite_key_spec(a2, b2, bcount),
    ensures
        a1 == a2 && b1 == b2,
{
    // a1*bcount + b1 == a2*bcount + b2 with both remainders below bcount forces
    // the quotients equal; nonlinear, so it is handed to the arith solver.
    assert(a1 == a2) by (nonlinear_arith)
        requires
            b1 < bcount,
            b2 < bcount,
            a1 * bcount + b1 == a2 * bcount + b2,
    {
        if a1 < a2 {
            assert((a2 - a1) * bcount >= bcount);
        }
        if a2 < a1 {
            assert((a1 - a2) * bcount >= bcount);
        }
    }
}

impl<V: Copy + Default> DenseSpanMap<V> {
    /// Exec composite key. Total: `None` both for an out-of-range `b` (which
    /// would break injectivity) and for a product that leaves `usize`.
    pub fn composite_key(a: usize, b: usize, bcount: usize) -> (r: Option<usize>)
        ensures
            r matches Some(k) ==> b < bcount && k as nat == composite_key_spec(
                a as nat,
                b as nat,
                bcount as nat,
            ),
    {
        if !(b < bcount) {
            return None;
        }
        match a.checked_mul(bcount) {
            Some(base) => base.checked_add(b),
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Sortedness transfer
// ---------------------------------------------------------------------------
/// If the build stream is sorted by `r` (lifted to entries), every per-key slice
/// is sorted by `r` on values. Filtering preserves relative order and the map is
/// exactly a filter, so the ordering the caller established on the stream is
/// inherited by every slice without re-sorting.
pub proof fn lemma_view_sorted<V: Copy + Default>(
    m: &DenseSpanMap<V>,
    k: int,
    rel: spec_fn(V, V) -> bool,
    entry_rel: spec_fn((usize, V), (usize, V)) -> bool,
)
    requires
        m.refines(),
        0 <= k < m.view().len(),
        entry_rel == (|x: (usize, V), y: (usize, V)| rel(x.1, y.1)),
        vstd::relations::sorted_by(m.stream_view(), entry_rel),
    ensures
        vstd::relations::sorted_by(m.view()[k], rel),
{
    let s = m.stream_view();
    lemma_filter_sorted(s, is_key::<V>(k as nat), entry_rel);
    let f = s.filter(is_key::<V>(k as nat));
    assert(m.view()[k] == f.map_values(snd::<V>()));
    assert forall|i: int, j: int| 0 <= i < j < m.view()[k].len() implies #[trigger] rel(
        m.view()[k][i],
        m.view()[k][j],
    ) by {
        assert(m.view()[k].len() == f.len());
        assert(m.view()[k][i] == f[i].1);
        assert(m.view()[k][j] == f[j].1);
        assert(vstd::relations::sorted_by(f, entry_rel));
        assert(entry_rel(f[i], f[j]));  // from vstd::relations::sorted_by(f, entry_rel) at i < j
    }
}

} // verus!
