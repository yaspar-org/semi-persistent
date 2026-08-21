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
//!     [`lemma_spans_disjoint`], not the invariant, because a pairwise quantified
//!     invariant creates quadratic trigger instantiations.
//!  2. *No invented and no dropped values.* [`DenseSpanMap::refines`] pins the
//!     model against the build stream: `view()[k]` is the order-preserving filter
//!     of the stream down to key `k`. Nothing else is a legal `pool` content.
//!  3. *Sortedness transfer.* [`lemma_view_sorted`] carries any ordering of the
//!     stream into every per-key slice, because a filter preserves relative order.
//!
//! `wf()` is deliberately *structural only* and `refines()` is separate: `get`
//! needs the tiling and nothing else, so it must not drag the refinement's
//! quantifier into scope.

use vstd::prelude::*;

verus! {

use vstd::seq_lib::*;

/// A half-open run of `pool` positions, `[off, off + len)`, tagged with the
/// generation that wrote it.
///
/// `stamp` is what lets a span table be recycled: a build bumps its arena's
/// generation and writes only the keys its stream carries, so an entry left by
/// an earlier build carries an older stamp and reads as empty. Stamp 0 is
/// reserved for a never-written entry, so a live generation is always positive.
#[derive(Clone, Copy)]
pub struct Span {
    pub off: usize,
    pub len: usize,
    pub stamp: u64,
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
// loop's locals. Keeping unrelated quantified state out of scope prevents
// unnecessary trigger instantiations in exec-body proofs.
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

/// The span table read in occupancy order.
///
/// A NAMED spec function rather than an inline `map_values` closure: the closure
/// term is re-elaborated at every site that mentions it, including once per
/// iteration inside a loop invariant. One opaque symbol matches everywhere.
#[verifier::opaque]
pub open spec fn permute(spans: Seq<Span>, occ: Seq<usize>) -> Seq<Span> {
    occ.map_values(|k: usize| spans[k as int])
}

/// `permute` has the occupancy list's length.
pub proof fn lemma_permute_len(spans: Seq<Span>, occ: Seq<usize>)
    ensures
        permute(spans, occ).len() == occ.len(),
{
    reveal(permute);
}

/// `permute` reads the table at the listed key. Opaque otherwise, so the tiling
/// term in a loop invariant stays one symbol instead of unfolding to a
/// `map_values` application at every mention.
pub proof fn lemma_permute_index(spans: Seq<Span>, occ: Seq<usize>, i: int)
    requires
        0 <= i < occ.len(),
    ensures
        permute(spans, occ).len() == occ.len(),
        permute(spans, occ)[i] == spans[occ[i] as int],
{
    reveal(permute);
}

/// The tiling predicate: `spans` partitions `[0, total)` into consecutive runs.
///
/// Every clause quantifies over a *single* variable. The pairwise-disjointness
/// phrasing (`forall|i, j| ... i != j ==> ranges disjoint`) is quadratic because
/// a trigger set with two disjoint
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

/// Appending one entry extends exactly that key's slice.
pub proof fn lemma_key_slice_push<V>(s: Seq<(usize, V)>, k: usize, v: V, j: nat)
    ensures
        key_slice(s.push((k, v)), j) == if k as nat == j {
            key_slice(s, j).push(v)
        } else {
            key_slice(s, j)
        },
{
    let kp = is_key::<V>(j);
    s.lemma_filter_push((k, v), kp);
    if k as nat == j {
        assert(kp((k, v)));
        assert(s.filter(kp).push((k, v)).map_values(snd::<V>()) =~= s.filter(kp).map_values(
            snd::<V>(),
        ).push(v));
    }
}

/// A key that occurs in the stream has a positive count.
pub proof fn lemma_count_key_positive<V>(s: Seq<(usize, V)>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        count_key(s, s[i].0 as nat) > 0,
{
    s.lemma_filter_contains(is_key::<V>(s[i].0 as nat), i);
    assert(s.filter(is_key::<V>(s[i].0 as nat)).contains(s[i]));
}

/// `sum_counts` is non-decreasing in the prefix length.
pub proof fn lemma_sum_counts_monotone<V>(s: Seq<(usize, V)>, occ: Seq<usize>, a: int, b: int)
    requires
        0 <= a <= b,
    ensures
        sum_counts(s, occ, a) <= sum_counts(s, occ, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_counts_monotone::<V>(s, occ, a, b - 1);
    }
}

/// Sum of the per-key counts over the first `j` entries of an occupancy list.
///
/// The pool size is this sum over the whole list, and
/// [`lemma_sum_counts_is_len`] is the identity that makes it the stream length.
pub open spec fn sum_counts<V>(s: Seq<(usize, V)>, occ: Seq<usize>, j: int) -> nat
    decreases j,
{
    if j <= 0 {
        0
    } else {
        sum_counts(s, occ, j - 1) + count_key(s, occ[j - 1] as nat)
    }
}

/// "Key `x` appears among the first `j` entries of the occupancy list."
pub open spec fn listed_before(occ: Seq<usize>, j: int, x: usize) -> bool {
    exists|q: int| 0 <= q < j && (#[trigger] occ[q]) == x
}

/// Dropping the stream's last entry lowers the sum by one when that entry's key
/// is listed, and leaves it alone when it is not.
pub proof fn lemma_sum_counts_drop_last<V>(s: Seq<(usize, V)>, occ: Seq<usize>, j: int)
    requires
        s.len() > 0,
        0 <= j <= occ.len(),
        forall|a: int, b: int| 0 <= a < b < j ==> occ[a] != occ[b],
    ensures
        sum_counts(s, occ, j) == sum_counts(s.drop_last(), occ, j) + if listed_before(
            occ,
            j,
            s.last().0,
        ) {
            1int
        } else {
            0int
        },
    decreases j,
{
    if j > 0 {
        lemma_sum_counts_drop_last(s, occ, j - 1);
        let rest = s.drop_last();
        let last = s.last();
        assert(s =~= rest.push(last));
        rest.lemma_filter_len_push(is_key::<V>(occ[j - 1] as nat), last);
        if occ[j - 1] == last.0 {
            // listed exactly here: the prefix cannot also list it
            assert(listed_before(occ, j, last.0));
            assert(!listed_before(occ, j - 1, last.0)) by {
                assert forall|q: int| 0 <= q < j - 1 implies (#[trigger] occ[q]) != last.0 by {
                    assert(occ[q] != occ[j - 1]);
                }
            }
        } else {
            // this position does not list it, so the two agree
            assert(listed_before(occ, j, last.0) == listed_before(occ, j - 1, last.0)) by {
                if listed_before(occ, j, last.0) {
                    let w = choose|w: int| 0 <= w < j && (#[trigger] occ[w]) == last.0;
                    assert(occ[w] == last.0);
                    assert(w < j - 1);
                }
            }
        }
    }
}

/// An empty stream contributes nothing at any prefix length.
pub proof fn lemma_sum_counts_empty<V>(s: Seq<(usize, V)>, occ: Seq<usize>, j: int)
    requires
        s.len() == 0,
        0 <= j,
    ensures
        sum_counts(s, occ, j) == 0,
    decreases j,
{
    if j > 0 {
        lemma_sum_counts_empty::<V>(s, occ, j - 1);
        assert(count_key(s, occ[j - 1] as nat) == 0) by {
            reveal(Seq::filter);
        }
    }
}

/// The occupancy list's per-key counts sum to the stream length: every entry is
/// counted under exactly one key, and every key that occurs is listed once.
///
/// This is the identity that makes the pool exactly as long as the stream, and
/// with it the tiling's "the last span ends at `pool.len()`" clause. Stated over
/// bare sequences, with the pairwise injectivity hypothesis discharged by the
/// caller, so no pairwise quantifier lives in `wf()`.
pub proof fn lemma_sum_counts_is_len<V>(s: Seq<(usize, V)>, occ: Seq<usize>)
    requires
        forall|a: int, b: int| 0 <= a < b < occ.len() ==> occ[a] != occ[b],
        forall|i: int| 0 <= i < s.len() ==> occ.contains((#[trigger] s[i]).0),
    ensures
        sum_counts(s, occ, occ.len() as int) == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.drop_last();
        assert(rest.len() == s.len() - 1);
        assert forall|i: int| 0 <= i < rest.len() implies occ.contains((#[trigger] rest[i]).0) by {
            assert(0 <= i < s.len());
            assert(rest[i] == s[i]);
        }
        lemma_sum_counts_is_len(rest, occ);
        lemma_sum_counts_drop_last(s, occ, occ.len() as int);
        assert(occ.contains(s.last().0)) by {
            assert(s[s.len() - 1] == s.last());
        }
        assert(listed_before(occ, occ.len() as int, s.last().0)) by {
            let w = choose|w: int| 0 <= w < occ.len() && occ[w] == s.last().0;
            assert(occ[w] == s.last().0);
        }
        assert(sum_counts(s, occ, occ.len() as int) == sum_counts(rest, occ, occ.len() as int)
            + 1);
    } else {
        lemma_sum_counts_empty::<V>(s, occ, occ.len() as int);
    }
}

/// Extents assigned as running prefix sums over the occupancy list tile
/// `[0, total)`. This is what pass 1b establishes and pass 2 relies on.
pub proof fn lemma_extent_tiling<V>(
    s: Seq<(usize, V)>,
    occ: Seq<usize>,
    full: Seq<Span>,
    total: nat,
)
    requires
        sum_counts::<V>(s, occ, occ.len() as int) == total,
        forall|q: int|
            0 <= q < occ.len() ==> {
                &&& full[(#[trigger] occ[q]) as int].off == sum_counts::<V>(s, occ, q)
                &&& full[occ[q] as int].len == count_key(s, occ[q] as nat)
            },
    ensures
        spans_tile(permute(full, occ), total),
{
    reveal(permute);
    let ps = permute(full, occ);
    assert(ps.len() == occ.len());
    assert forall|q: int| 0 <= q < ps.len() implies #[trigger] ps[q] == full[occ[q] as int] by {
        lemma_permute_index(full, occ, q);
    }
    assert forall|q: int| 0 <= q < ps.len() implies (#[trigger] ps[q]).off + ps[q].len
        == sum_counts::<V>(s, occ, q + 1) by {
    }
    assert forall|q: int| 0 <= q < ps.len() implies (#[trigger] ps[q]).off + ps[q].len
        <= total by {
        lemma_sum_counts_monotone::<V>(s, occ, q + 1, occ.len() as int);
    }
}

/// The placement step, over bare sequences: region `k0` is extended by `val` and
/// every other region is untouched. The build loop's locals are deliberately not
/// in scope, which limits quantified context.
///
/// Regions are ordered by OCCUPANCY position, not by key, so disjointness comes
/// from `spans_tile` applied to the permuted span sequence. `pos_of[k]` is key
/// `k`'s index in `occ`; it is a ghost argument so the hypothesis the exec body
/// must supply stays single-variable, and the lemma derives the pairwise fact
/// internally.
pub proof fn lemma_place_step<V>(
    pool: Seq<V>,
    spans: Seq<Span>,
    occ: Seq<usize>,
    partial: Seq<Span>,
    pos_of: Seq<int>,
    live: Seq<bool>,
    num_keys: int,
    k0: usize,
    val: V,
)
    requires
        spans_tile(permute(spans, occ), pool.len()),
        0 <= num_keys <= spans.len(),
        num_keys <= partial.len(),
        num_keys <= pos_of.len(),
        num_keys <= live.len(),
        0 <= k0 < num_keys,
        live[k0 as int],
        // every listed key is in range, and a LIVE key's recorded position names
        // it back. Only live keys have a position: an unwritten key's entry holds
        // whatever the previous generation left there.
        forall|j: int| 0 <= j < occ.len() ==> (#[trigger] occ[j]) < num_keys,
        forall|k: int|
            0 <= k < num_keys ==> (#[trigger] live[k]) ==> {
                &&& 0 <= pos_of[k] < occ.len()
                &&& occ[pos_of[k]] as int == k
            },
        // cursors sit inside their key's extent, and k0 has room left
        forall|k: int|
            0 <= k < num_keys ==> (#[trigger] live[k]) ==> partial[k].off == spans[k].off
                && partial[k].len <= spans[k].len,
        partial[k0 as int].len < spans[k0 as int].len,
    ensures
        forall|k: int|
            0 <= k < num_keys && k != k0 as int && live[k] ==> #[trigger] pool.update(
                (partial[k0 as int].off + partial[k0 as int].len) as int,
                val,
            ).subrange(
                spans[k].off as int,
                (partial[k].off + partial[k].len) as int,
            ) == pool.subrange(spans[k].off as int, (partial[k].off + partial[k].len) as int),
        pool.update((partial[k0 as int].off + partial[k0 as int].len) as int, val).subrange(
            spans[k0 as int].off as int,
            partial[k0 as int].off + partial[k0 as int].len + 1,
        ) == pool.subrange(
            spans[k0 as int].off as int,
            (partial[k0 as int].off + partial[k0 as int].len) as int,
        ).push(val),
{
    let permuted = permute(spans, occ);
    lemma_permute_len(spans, occ);
    let p0 = pos_of[k0 as int];
    lemma_permute_index(spans, occ, p0);
    let pos = (partial[k0 as int].off + partial[k0 as int].len) as int;
    assert(occ[p0] as int == k0 as int);
    assert(permuted[p0] == spans[occ[p0] as int]);
    assert(permuted[p0] == spans[k0 as int]);
    assert(pos < pool.len());
    assert forall|k: int|
        0 <= k < num_keys && k != k0 as int && live[k] implies #[trigger] pool.update(
        pos,
        val,
    ).subrange(
        spans[k].off as int,
        (partial[k].off + partial[k].len) as int,
    ) == pool.subrange(spans[k].off as int, (partial[k].off + partial[k].len) as int) by {
        let pk = pos_of[k];
        lemma_permute_index(spans, occ, pk);
        assert(occ[pk] as int == k);
        assert(permuted[pk] == spans[occ[pk] as int]);
        assert(permuted[pk] == spans[k]);
        // distinct keys occupy distinct positions, so the tiling separates them
        assert(pk != p0);
        if pk < p0 {
            lemma_spans_disjoint(permuted, pool.len(), pk, p0);
        } else {
            lemma_spans_disjoint(permuted, pool.len(), p0, pk);
        }
        lemma_update_outside(pool, spans[k].off as int, (partial[k].off + partial[k].len) as int, pos, val);
    }
    lemma_update_at_end(pool, spans[k0 as int].off as int, pos, val);
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
/// A recycled span table.
///
/// The table outlives the map built into it: `DenseSpanMap::recycle` hands it
/// back and `DenseSpanMap::build_in` fills it again. When the retained table
/// already has at least `num_keys` slots, ordinary builds touch only the stream
/// and its occupied keys. A larger requested key space grows the table by the
/// missing slots. `stamp` is the current generation; a span carrying an older
/// stamp belongs to a previous build and reads as empty, which removes the
/// ordinary O(table length) clear. Stamp exhaustion performs one such clear
/// before restarting at generation 1.
pub struct SpanArena {
    pub(crate) spans: std::vec::Vec<Span>,
    /// The keys the current generation wrote, in first-occurrence order.
    pub(crate) occ: std::vec::Vec<usize>,
    /// The current generation. Never equals a stamp left by an earlier build.
    pub(crate) stamp: u64,
}

impl SpanArena {
    pub open(crate) spec fn spans_view(&self) -> Seq<Span> {
        self.spans@
    }

    pub open(crate) spec fn occ_view(&self) -> Seq<usize> {
        self.occ@
    }

    pub open(crate) spec fn stamp_view(&self) -> u64 {
        self.stamp
    }

    /// No entry claims a generation newer than the arena's own.
    ///
    /// This is what makes bumping the generation enough to invalidate the whole
    /// table: after the bump no existing entry can carry the new stamp. It is a
    /// TYPE invariant, not a precondition, so `build_in` needs no `requires` and
    /// the public surface stays total. It holds continuously through a build:
    /// the bump raises the arena's stamp above every entry's, and every entry a
    /// build writes gets exactly the current stamp.
    #[verifier::type_invariant]
    pub open(crate) spec fn wf(&self) -> bool {
        forall|k: int|
            0 <= k < self.spans_view().len() ==> (#[trigger] self.spans_view()[k]).stamp
                <= self.stamp_view()
    }

    /// An empty arena. Its generation is 0, the never-written stamp, so the
    /// first build advances to 1 and every entry it does not write stays stale.
    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.spans_view().len() == 0,
            r.occ_view().len() == 0,
            r.stamp_view() == 0,
    {
        SpanArena { spans: std::vec::Vec::new(), occ: std::vec::Vec::new(), stamp: 0 }
    }

    /// Number of key slots the table currently holds.
    pub fn capacity(&self) -> (n: usize)
        ensures
            n == self.spans_view().len(),
    {
        self.spans.len()
    }
}

impl Default for SpanArena {
    fn default() -> Self {
        Self::new()
    }
}

/// Build-once dense-keyed multimap.
///
/// `V: Default` supplies the pass-2 filler: the pool is sized up front and every
/// slot is then overwritten by pass 2 (the occupied spans tile the pool exactly,
/// so no filler survives in any readable range). The filler is therefore
/// unobservable, the same argument `doc/design/07-default-impls.md` makes for
/// restore-regrow.
pub struct DenseSpanMap<V: Copy + Default> {
    pub(crate) pool: std::vec::Vec<V>,
    pub(crate) arena: SpanArena,
    /// The key space. The arena's table may be longer, because it is recycled
    /// from a build over a larger key space.
    pub(crate) num_keys: usize,
    /// Ghost record of the stream this map was built from. `refines()` is stated
    /// against it, so the model obligation survives past the build's return.
    /// (Spec-only: erased in plain builds, hence `dead_code`.)
    #[allow(dead_code)]
    pub(crate) stream: Ghost<Seq<(usize, V)>>,
}

impl<V: Copy + Default> DenseSpanMap<V> {
    pub open(crate) spec fn spans_view(&self) -> Seq<Span> {
        self.arena.spans@
    }

    pub open(crate) spec fn occ_view(&self) -> Seq<usize> {
        self.arena.occ@
    }

    pub open(crate) spec fn stamp_view(&self) -> u64 {
        self.arena.stamp
    }

    /// Key `k` was written by the generation this map holds.
    pub open(crate) spec fn occupied(&self, k: int) -> bool {
        self.spans_view()[k].stamp == self.stamp_view()
    }

    /// The current generation's spans, in occupancy order.
    ///
    /// `wf` states the tiling of THIS sequence rather than of the key-ordered
    /// table, because a recycled build cannot maintain a tiling in key order: an
    /// unwritten key's entry holds whatever the previous build left there.
    pub open(crate) spec fn occ_spans(&self) -> Seq<Span> {
        permute(self.spans_view(), self.occ_view())
    }

    /// The abstract contents: one value sequence per key. A key the current
    /// generation did not write is empty.
    pub open(crate) spec fn view(&self) -> Seq<Seq<V>> {
        Seq::new(
            self.num_keys as nat,
            |k: int|
                if self.occupied(k) {
                    self.pool@.subrange(
                        self.spans_view()[k].off as int,
                        self.spans_view()[k].off + self.spans_view()[k].len,
                    )
                } else {
                    Seq::<V>::empty()
                },
        )
    }

    /// The stream this map was built from.
    pub open(crate) spec fn stream_view(&self) -> Seq<(usize, V)> {
        self.stream@
    }

    /// Structural well-formedness: the occupied spans tile the pool exactly.
    ///
    /// Every clause quantifies over a single variable. Injectivity of the
    /// occupancy list is NOT stated here: it is derived by
    /// [`lemma_occ_injective`] from the tiling plus "an occupied span is
    /// non-empty", because the pairwise phrasing creates quadratic trigger
    /// instantiations.
    ///
    /// Purely structural: the refinement is `refines()`.
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.num_keys <= self.spans_view().len()
        &&& self.stamp_view() > 0
        &&& spans_tile(self.occ_spans(), self.pool@.len())
        &&& (forall|k: int|
            0 <= k < self.spans_view().len() ==> (#[trigger] self.spans_view()[k]).stamp
                <= self.stamp_view())
        &&& (forall|j: int|
            0 <= j < self.occ_view().len() ==> {
                &&& (#[trigger] self.occ_view()[j]) < self.num_keys
                &&& self.spans_view()[self.occ_view()[j] as int].stamp == self.stamp_view()
                &&& self.spans_view()[self.occ_view()[j] as int].len > 0
            })
        &&& (forall|k: int|
            0 <= k < self.num_keys ==> (#[trigger] self.spans_view()[k]).stamp
                == self.stamp_view() ==> self.occ_view().contains(k as usize))
    }

    /// Refinement to the build stream: key `k`'s slice IS the stream filtered to
    /// `k`. Unchanged by the recycled build path: a key the stream does not
    /// carry is unoccupied, and its empty view is the empty filter.
    pub open(crate) spec fn refines(&self) -> bool {
        forall|k: int|
            0 <= k < self.num_keys ==> #[trigger] self.view()[k] == key_slice(
                self.stream@,
                k as nat,
            )
    }

    /// Number of keys.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self.view().len(),
    {
        self.num_keys
    }

    pub fn is_empty(&self) -> (b: bool)
        ensures
            b == (self.view().len() == 0),
    {
        self.num_keys == 0
    }

    /// Key `k`'s values, as a slice into the pool.
    ///
    /// Total, with a documented panic. Three O(1) branches: the key space, the
    /// generation stamp, and the span's extent. For a `wf()` map only the stamp
    /// branch is live, and it is the one that makes a recycled table correct.
    ///
    /// The slice is carved with two `split_at`s rather than `&pool[a..b]`:
    /// `split_at` carries a direct `subrange` postcondition, while the
    /// range-index route reaches the pool through vstd's `call_ensures`-shaped
    /// `Index` specification.
    pub fn get(&self, k: usize) -> (r: &[V])
        ensures
            k < self.view().len() ==> r@ == self.view()[k as int],
    {
        if !(k < self.num_keys) {
            crate::guard::refuse("DenseSpanMap::get: key out of range");
        }
        if !(k < self.arena.spans.len()) {
            crate::guard::refuse("DenseSpanMap::get: span table shorter than the key space");
        }
        let span = self.arena.spans[k];
        let n = self.pool.len();
        if span.stamp != self.arena.stamp {
            // Stale generation: this key was not written by the build that
            // produced this map, so it holds nothing.
            let (empty, _) = self.pool.as_slice().split_at(0);
            proof {
                assert(span == self.spans_view()[k as int]);
                assert(!self.occupied(k as int));
                assert(empty@ =~= Seq::<V>::empty());
            }
            return empty;
        }
        if !(span.off <= n && span.len <= n - span.off) {
            crate::guard::refuse("DenseSpanMap::get: span outside pool");
        }
        let (_, tail) = self.pool.as_slice().split_at(span.off);
        let (out, _) = tail.split_at(span.len);
        proof {
            assert(span == self.spans_view()[k as int]);
            assert(self.occupied(k as int));
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
        if k < self.num_keys {
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
        let s = self.get(k);
        s.len()
    }

    /// Pool size (spec counterpart of `total()`; fields are `pub(crate)`, so the public
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

    /// The keys the current generation wrote, in first-occurrence order.
    ///
    /// A consumer that needs to visit every non-empty key iterates this instead
    /// of scanning `0..len()`, which is the difference between work proportional
    /// to the occupied keys and work proportional to the key space.
    ///
    /// Total: the postconditions tying the slice to `occupied` are conditioned on
    /// `wf()` rather than required, so no precondition reaches an unverified
    /// caller. The list has no duplicates; that is
    /// [`lemma_occ_injective`](Self::lemma_occ_injective), on demand, because
    /// stating it here would put a pairwise quantifier in every caller's context.
    pub fn occupied_keys(&self) -> (r: &[usize])
        ensures
            r@ == self.occ_view(),
            // every listed key is in range and occupied
            self.wf() ==> (forall|j: int|
                0 <= j < r@.len() ==> (#[trigger] r@[j]) < self.view().len()
                    && self.occupied(r@[j] as int)),
            // and every occupied key is listed
            self.wf() ==> (forall|k: int|
                0 <= k < self.view().len() ==> (#[trigger] self.occupied(k))
                    ==> r@.contains(k as usize)),
    {
        self.arena.occ.as_slice()
    }

    /// The occupancy list has no duplicates, so iterating it visits each
    /// occupied key exactly once.
    ///
    /// Derived rather than asserted in `wf()`: a repeated key would put the same
    /// span at two positions, and the tiling forces a repeated span to be empty,
    /// contradicting `wf()`'s "an occupied span is non-empty". Stating it in
    /// `wf()` would put a pairwise quantifier on every consumer proof.
    pub proof fn lemma_occ_injective(&self, i: int, j: int)
        requires
            self.wf(),
            0 <= i < j < self.occ_view().len(),
        ensures
            self.occ_view()[i] != self.occ_view()[j],
    {
        lemma_permute_len(self.spans_view(), self.occ_view());
        lemma_permute_index(self.spans_view(), self.occ_view(), i);
        lemma_permute_index(self.spans_view(), self.occ_view(), j);
        lemma_spans_disjoint(self.occ_spans(), self.total_spec(), i, j);
    }

    /// Hand the span table back for the next build. O(1): it is a move.
    pub fn recycle(self) -> (r: SpanArena)
        ensures
            r.spans_view() == self.spans_view(),
            r.stamp_view() == self.stamp_view(),
    {
        self.arena
    }

    /// Exec counterpart of the build precondition: every key in the stream is in range.
    pub fn can_build(stream: &[(usize, V)], num_keys: usize) -> (b: bool)
        ensures
            b == (forall|i: int| 0 <= i < stream@.len() ==> (#[trigger] stream@[i]).0 < num_keys),
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

    /// Pass 1: count each key's population and list the keys the generation
    /// touches, in first-occurrence order.
    ///
    /// Each listed key records its own position in the occupancy list in its
    /// `off` field, which pass 1b overwrites with the real offset. That record is
    /// what makes the list's injectivity a single-variable fact.
    fn count_pass(
        spans: &mut std::vec::Vec<Span>,
        occ: &mut std::vec::Vec<usize>,
        stream: &[(usize, V)],
        num_keys: usize,
        g: u64,
    )
        requires
            num_keys <= old(spans)@.len(),
            old(occ)@.len() == 0,
            g > 0,
            forall|q: int| 0 <= q < stream@.len() ==> (#[trigger] stream@[q]).0 < num_keys,
            forall|k: int| 0 <= k < old(spans)@.len() ==> (#[trigger] old(spans)@[k]).stamp < g,
        ensures
            final(spans)@.len() == old(spans)@.len(),
            forall|k: int|
                0 <= k < final(spans)@.len() ==> (#[trigger] final(spans)@[k]).stamp <= g,
            forall|j: int|
                0 <= j < final(occ)@.len() ==> {
                    &&& (#[trigger] final(occ)@[j]) < num_keys
                    &&& final(spans)@[final(occ)@[j] as int].stamp == g
                    &&& final(spans)@[final(occ)@[j] as int].off == j
                },
            forall|k: int|
                0 <= k < num_keys ==> (((#[trigger] final(spans)@[k]).stamp == g) <==> count_key(
                    stream@,
                    k as nat,
                ) > 0),
            forall|k: int|
                0 <= k < num_keys ==> ((#[trigger] final(spans)@[k]).stamp == g
                    ==> final(spans)@[k].len == count_key(stream@, k as nat)),
            forall|k: int|
                0 <= k < num_keys ==> ((#[trigger] final(spans)@[k]).stamp == g
                    ==> final(occ)@.contains(k as usize)),
    {
        let ghost s = stream@;
        let mut i: usize = 0;
        proof {
            assert(s.take(0int) =~= Seq::<(usize, V)>::empty());
            assert forall|k: int|
                #![trigger count_key(s.take(0int), k as nat)]
                0 <= k < num_keys implies count_key(s.take(0int), k as nat) == 0 by {
                reveal(Seq::filter);
            }
        }
        while i < stream.len()
            invariant
                i <= s.len(),
                stream@ == s,
                g > 0,
                num_keys <= spans@.len(),
                spans@.len() == old(spans)@.len(),
                forall|q: int| 0 <= q < s.len() ==> (#[trigger] s[q]).0 < num_keys,
                forall|k: int| 0 <= k < spans@.len() ==> (#[trigger] spans@[k]).stamp <= g,
                forall|j: int|
                    0 <= j < occ@.len() ==> {
                        &&& (#[trigger] occ@[j]) < num_keys
                        &&& spans@[occ@[j] as int].stamp == g
                        &&& spans@[occ@[j] as int].off == j
                    },
                forall|k: int|
                    0 <= k < num_keys ==> (((#[trigger] spans@[k]).stamp == g) <==> count_key(
                        s.take(i as int),
                        k as nat,
                    ) > 0),
                forall|k: int|
                    0 <= k < num_keys ==> ((#[trigger] spans@[k]).stamp == g ==> spans@[k].len
                        == count_key(s.take(i as int), k as nat)),
                forall|k: int|
                    0 <= k < num_keys ==> ((#[trigger] spans@[k]).stamp == g ==> occ@.contains(
                        k as usize,
                    )),
            decreases s.len() - i,
        {
            let key = stream[i].0;
            let ghost prefix = s.take(i as int);
            let ghost occ_old = occ@;
            proof {
                assert(key == s[i as int].0);
                assert(s[i as int].0 < num_keys);
                assert(s.take((i + 1) as int) =~= prefix.push(s[i as int]));
                assert(prefix.len() == i);
                lemma_count_key_bound(prefix, key as nat);
                assert forall|k: int|
                    #![trigger count_key(s.take((i + 1) as int), k as nat)]
                    0 <= k < num_keys implies count_key(s.take((i + 1) as int), k as nat)
                    == count_key(prefix, k as nat) + if k == key as int {
                    1int
                } else {
                    0int
                } by {
                    prefix.lemma_filter_len_push(is_key::<V>(k as nat), s[i as int]);
                }
            }
            let sp = spans[key];
            let fresh: bool = sp.stamp != g;
            if fresh {
                let pos = occ.len();
                spans[key] = Span { off: pos, len: 1, stamp: g };
                occ.push(key);
            } else {
                spans[key] = Span { off: sp.off, len: sp.len + 1, stamp: g };
            }
            proof {
                assert forall|k: int|
                    0 <= k < num_keys && (#[trigger] spans@[k]).stamp == g implies occ@.contains(
                    k as usize,
                ) by {
                    if fresh && k == key as int {
                        assert(occ@[occ@.len() - 1] == key);
                    } else {
                        assert(occ_old.contains(k as usize));
                        let w = choose|w: int| 0 <= w < occ_old.len() && occ_old[w] == k as usize;
                        assert(occ@[w] == occ_old[w]);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(s.take(s.len() as int) =~= s);
        }
    }

    /// Pass 1b: assign each listed key its extent, over the occupancy list alone.
    ///
    /// Extents are laid out in first-occurrence order rather than key order,
    /// which the per-key refinement does not constrain. Each key's `len` is read
    /// as its count and then zeroed, so pass 2 can use it as a running cursor.
    fn extent_pass(
        spans: &mut std::vec::Vec<Span>,
        occ: &std::vec::Vec<usize>,
        num_keys: usize,
        g: u64,
        Ghost(s): Ghost<Seq<(usize, V)>>,
    ) -> (total: usize)
        requires
            num_keys <= old(spans)@.len(),
            g > 0,
            s.len() <= usize::MAX,
            sum_counts::<V>(s, occ@, occ@.len() as int) == s.len(),
            forall|x: int, y: int| 0 <= x < y < occ@.len() ==> occ@[x] != occ@[y],
            forall|j: int|
                0 <= j < occ@.len() ==> {
                    &&& (#[trigger] occ@[j]) < num_keys
                    &&& old(spans)@[occ@[j] as int].stamp == g
                    &&& old(spans)@[occ@[j] as int].len == count_key(s, occ@[j] as nat)
                },
        ensures
            final(spans)@.len() == old(spans)@.len(),
            total == s.len(),
            // stamps are untouched, so occupancy is unchanged
            forall|k: int|
                0 <= k < final(spans)@.len() ==> (#[trigger] final(spans)@[k]).stamp
                    == old(spans)@[k].stamp,
            forall|q: int|
                0 <= q < occ@.len() ==> {
                    &&& final(spans)@[(#[trigger] occ@[q]) as int].off == sum_counts::<V>(s, occ@, q)
                    &&& final(spans)@[occ@[q] as int].len == 0
                },
    {
        let mut acc: usize = 0;
        let mut j: usize = 0;
        while j < occ.len()
            invariant
                j <= occ@.len(),
                g > 0,
                s.len() <= usize::MAX,
                num_keys <= spans@.len(),
                spans@.len() == old(spans)@.len(),
                sum_counts::<V>(s, occ@, occ@.len() as int) == s.len(),
                forall|x: int, y: int| 0 <= x < y < occ@.len() ==> occ@[x] != occ@[y],
                forall|k: int|
                    0 <= k < spans@.len() ==> (#[trigger] spans@[k]).stamp == old(spans)@[k].stamp,
                forall|q: int|
                    0 <= q < occ@.len() ==> {
                        &&& (#[trigger] occ@[q]) < num_keys
                        &&& spans@[occ@[q] as int].stamp == g
                    },
                forall|q: int|
                    0 <= q < j ==> {
                        &&& spans@[(#[trigger] occ@[q]) as int].off == sum_counts::<V>(s, occ@, q)
                        &&& spans@[occ@[q] as int].len == 0
                    },
                forall|q: int|
                    j <= q < occ@.len() ==> spans@[(#[trigger] occ@[q]) as int].len == count_key(
                        s,
                        occ@[q] as nat,
                    ),
                acc == sum_counts::<V>(s, occ@, j as int),
                acc <= s.len(),
            decreases occ@.len() - j,
        {
            let k = occ[j];
            let sp = spans[k];
            let cnt = sp.len;
            proof {
                assert(k == occ@[j as int]);
                assert(sp == spans@[k as int]);
                assert(cnt == count_key(s, occ@[j as int] as nat));
                lemma_sum_counts_monotone::<V>(s, occ@, (j + 1) as int, occ@.len() as int);
                assert(sum_counts::<V>(s, occ@, (j + 1) as int) == sum_counts::<V>(s, occ@, j as int)
                    + count_key(s, occ@[j as int] as nat));
                assert(acc + cnt == sum_counts::<V>(s, occ@, (j + 1) as int));
                assert(sum_counts::<V>(s, occ@, (j + 1) as int) <= s.len());
            }
            spans[k] = Span { off: acc, len: 0, stamp: g };
            acc = acc + cnt;
            j = j + 1;
        }
        acc
    }

    /// Pass 2: place every stream value at its key's running cursor.
    ///
    /// Split out of `build_in` so its contract isolates the pool content per key;
    /// none of the other passes' quantified state is in scope here.
    ///
    /// `full` carries each key's FINAL extent: the tiling holds of `full`
    /// throughout, while `spans` grows its lengths from zero to the count.
    fn place_pass(
        spans: &mut std::vec::Vec<Span>,
        pool: &mut std::vec::Vec<V>,
        stream: &[(usize, V)],
        num_keys: usize,
        g: u64,
        total: usize,
        Ghost(occ0): Ghost<Seq<usize>>,
        Ghost(full): Ghost<Seq<Span>>,
        Ghost(pos_of): Ghost<Seq<int>>,
    )
        requires
            num_keys <= old(spans)@.len(),
            num_keys <= pos_of.len(),
            full.len() == old(spans)@.len(),
            old(pool)@.len() == total,
            total == stream@.len(),
            g > 0,
            forall|q: int| 0 <= q < stream@.len() ==> (#[trigger] stream@[q]).0 < num_keys,
            spans_tile(permute(full, occ0), total as nat),
            forall|j: int|
                0 <= j < occ0.len() ==> {
                    &&& (#[trigger] occ0[j]) < num_keys
                    &&& old(spans)@[occ0[j] as int].stamp == g
                },
            forall|k: int|
                0 <= k < num_keys ==> (((#[trigger] old(spans)@[k]).stamp == g) <==> count_key(
                    stream@,
                    k as nat,
                ) > 0),
            forall|k: int|
                0 <= k < num_keys ==> ((#[trigger] old(spans)@[k]).stamp == g ==> {
                    &&& old(spans)@[k].off == full[k].off
                    &&& full[k].stamp == g
                    &&& old(spans)@[k].len == 0
                    &&& full[k].len == count_key(stream@, k as nat)
                    &&& 0 <= pos_of[k] < occ0.len()
                    &&& occ0[pos_of[k]] as int == k
                }),
        ensures
            final(spans)@.len() == old(spans)@.len(),
            final(pool)@.len() == total,
            forall|k: int|
                0 <= k < final(spans)@.len() ==> (#[trigger] final(spans)@[k]).stamp
                    == old(spans)@[k].stamp,
            forall|k: int|
                0 <= k < num_keys ==> (#[trigger] final(spans)@[k]).off == old(spans)@[k].off,
            spans_tile(permute(final(spans)@, occ0), total as nat),
            forall|k: int|
                0 <= k < num_keys ==> ((#[trigger] final(spans)@[k]).stamp == g ==> {
                    &&& final(spans)@[k].len == count_key(stream@, k as nat)
                    &&& final(pool)@.subrange(
                        final(spans)@[k].off as int,
                        final(spans)@[k].off + final(spans)@[k].len,
                    ) == key_slice(stream@, k as nat)
                }),
    {
        let ghost s = stream@;
        let ghost live = Seq::new(num_keys as nat, |k: int| old(spans)@[k].stamp == g);
        let mut i: usize = 0;
        proof {
            assert(s.take(0int) =~= Seq::<(usize, V)>::empty());
            assert forall|k: int|
                #![trigger key_slice(s.take(0int), k as nat)]
                0 <= k < num_keys implies key_slice(s.take(0int), k as nat)
                =~= Seq::<V>::empty() by {
                // scoped: revealing `filter` for the whole body makes every
                // count_key/key_slice term unfold recursively
                reveal(Seq::filter);
            }
            assert forall|k: int|
                0 <= k < num_keys && (#[trigger] spans@[k]).stamp == g implies pool@.subrange(
                spans@[k].off as int,
                spans@[k].off + spans@[k].len,
            ) == key_slice(s.take(0int), k as nat) by {
                // the key's extent lies inside the pool, so its zero-length
                // prefix is the empty sequence
                lemma_permute_index(full, occ0, pos_of[k]);
                assert(permute(full, occ0)[pos_of[k]] == full[k]);
                assert(full[k].off + full[k].len <= total);
                assert(spans@[k].len == 0);
                assert(pool@.subrange(spans@[k].off as int, spans@[k].off + spans@[k].len)
                    =~= Seq::<V>::empty());
            }
        }
        while i < stream.len()
            invariant
                i <= s.len(),
                stream@ == s,
                g > 0,
                num_keys <= spans@.len(),
                num_keys <= pos_of.len(),
                live.len() == num_keys,
                forall|k: int| 0 <= k < num_keys ==> ((#[trigger] live[k]) <==> spans@[k].stamp == g),
                full.len() == spans@.len(),
                pool@.len() == total,
                total == s.len(),
                forall|q: int| 0 <= q < s.len() ==> (#[trigger] s[q]).0 < num_keys,
                spans_tile(permute(full, occ0), total as nat),
                forall|j: int| 0 <= j < occ0.len() ==> (#[trigger] occ0[j]) < num_keys,
                forall|k: int|
                    0 <= k < spans@.len() ==> (#[trigger] spans@[k]).stamp
                        == old(spans)@[k].stamp,
                forall|k: int|
                    0 <= k < num_keys ==> (#[trigger] spans@[k]).off == old(spans)@[k].off,
                forall|k: int|
                    0 <= k < num_keys ==> (((#[trigger] spans@[k]).stamp == g) <==> count_key(
                        s,
                        k as nat,
                    ) > 0),
                forall|k: int|
                    0 <= k < num_keys ==> ((#[trigger] spans@[k]).stamp == g ==> {
                        &&& spans@[k].off == full[k].off
                        &&& full[k].len == count_key(s, k as nat)
                        &&& spans@[k].len == count_key(s.take(i as int), k as nat)
                        &&& 0 <= pos_of[k] < occ0.len()
                        &&& occ0[pos_of[k]] as int == k
                    }),
                forall|k: int|
                    0 <= k < num_keys ==> ((#[trigger] spans@[k]).stamp == g ==> pool@.subrange(
                        spans@[k].off as int,
                        spans@[k].off + spans@[k].len,
                    ) == key_slice(s.take(i as int), k as nat)),
            decreases s.len() - i,
        {
            let key = stream[i].0;
            let val = stream[i].1;
            let ghost prefix = s.take(i as int);
            let ghost pool0 = pool@;
            proof {
                assert(key == s[i as int].0);
                assert(s[i as int].0 < num_keys);
                lemma_count_key_positive::<V>(s, i as int);
                assert(spans@[key as int].stamp == g);
                assert(s.take((i + 1) as int) =~= prefix.push(s[i as int]));
                s.lemma_filter_take_len(is_key::<V>(key as nat), (i + 1) as int);
                prefix.lemma_filter_len_push(is_key::<V>(key as nat), s[i as int]);
                // every cursor is inside its key's final extent: a prefix count
                // never exceeds the whole-stream count
                assert forall|k: int|
                    #![trigger live[k]]
                    0 <= k < num_keys && live[k] implies spans@[k].len <= full[k].len by {
                    s.lemma_filter_take_len(is_key::<V>(k as nat), i as int);
                }
                lemma_place_step::<V>(
                    pool@,
                    full,
                    occ0,
                    spans@,
                    pos_of,
                    live,
                    num_keys as int,
                    key,
                    val,
                );
            }
            let sp = spans[key];
            proof {
                // the write lands inside key's extent, which the tiling bounds
                // by the pool length
                assert(sp.off == full[key as int].off);
                assert(sp.len < full[key as int].len);
                let pk = pos_of[key as int];
                lemma_permute_index(full, occ0, pk);
                assert(full[key as int].off + full[key as int].len <= total);
            }
            let at = sp.off + sp.len;
            pool[at] = val;
            spans[key] = Span { off: sp.off, len: sp.len + 1, stamp: g };
            proof {
                assert(pool@ == pool0.update(at as int, val));
                assert forall|k: int|
                    0 <= k < num_keys && (#[trigger] spans@[k]).stamp == g implies {
                    &&& spans@[k].len == count_key(s.take((i + 1) as int), k as nat)
                    &&& pool@.subrange(spans@[k].off as int, spans@[k].off + spans@[k].len)
                        == key_slice(s.take((i + 1) as int), k as nat)
                } by {
                    prefix.lemma_filter_len_push(is_key::<V>(k as nat), s[i as int]);
                    lemma_key_slice_push::<V>(prefix, key, val, k as nat);
                }
            }
            i = i + 1;
        }
        proof {
            assert(s.take(s.len() as int) =~= s);
            // the finished table agrees with `full` on every listed key, so the
            // tiling proved of `full` is the tiling of the table itself
            lemma_permute_len(spans@, occ0);
            lemma_permute_len(full, occ0);
            assert(permute(spans@, occ0) =~= permute(full, occ0)) by {
                assert forall|q: int|
                    #![trigger permute(full, occ0)[q]]
                    0 <= q < occ0.len() implies permute(spans@, occ0)[q] == permute(
                    full,
                    occ0,
                )[q] by {
                    lemma_permute_index(spans@, occ0, q);
                    lemma_permute_index(full, occ0, q);
                    let k = occ0[q] as int;
                    assert(spans@[k].stamp == g);
                    assert(spans@[k].off == full[k].off);
                    assert(spans@[k].len == count_key(s, k as nat));
                    assert(full[k].len == count_key(s, k as nat));
                    assert(full[k].stamp == spans@[k].stamp);
                    assert(spans@[k] == full[k]);
                }
            }
        }
    }

    /// Two-pass counting build into a recycled span table.
    ///
    /// Pass 1 counts each key's population, appending the key to the occupancy
    /// list the first time the generation sees it; pass 1b assigns extents over
    /// the occupancy list alone; pass 2 places each value at its key's running
    /// cursor. With a sufficiently large retained span table, ordinary work is
    /// proportional to the stream and the keys it occupies. Growing the table
    /// adds the number of missing key slots; stamp exhaustion exceptionally
    /// clears the retained table.
    ///
    /// Extents are assigned in first-occurrence order rather than key order.
    /// `refines()` does not constrain that: a key's slice is still the stream's
    /// order-preserving filter down to that key.
    // Each pass has a separate contract. `spinoff_prover` isolates their final
    // composition from unrelated module context; no custom `rlimit` is needed.
    #[verifier::spinoff_prover]
    pub(crate) fn build_in(arena: SpanArena, stream: &[(usize, V)], num_keys: usize) -> (r: Self)
        requires
            forall|i: int| 0 <= i < stream@.len() ==> (#[trigger] stream@[i]).0 < num_keys,
        ensures
            r.wf(),
            r.view().len() == num_keys,
            r.stream_view() == stream@,
            r.total_spec() == stream@.len(),
            r.refines(),
            // Stale spans read as empty: a key the stream does not carry is
            // unoccupied, and an unoccupied key's view is the empty sequence.
            (forall|k: int|
                0 <= k < num_keys ==> ((#[trigger] r.occupied(k)) <==> count_key(
                    stream@,
                    k as nat,
                ) > 0)),
            (forall|k: int|
                0 <= k < num_keys && !(#[trigger] r.occupied(k)) ==> r.view()[k]
                    == Seq::<V>::empty()),
            r.spans_view().len() >= num_keys,
    {
        let ghost s = stream@;
        let ghost arena_spans = arena.spans@;
        let ghost arena_stamp = arena.stamp;
        proof {
            use_type_invariant(&arena);
            assert(arena.wf());
            assert forall|k: int| 0 <= k < arena_spans.len() implies (#[trigger] arena_spans[k]).stamp
                <= arena_stamp by {
                assert(arena.spans_view()[k].stamp <= arena.stamp_view());
            }
        }
        // Destructured into locals: a `&mut` borrow of a field of a type with a
        // type invariant would oblige every vstd `Vec` method the build calls to
        // be `no_unwind`, which they are not. The arena is reassembled at the
        // end, where the invariant is checked once.
        let SpanArena { mut spans, mut occ, mut stamp } = arena;
        proof {
            assert(spans@ =~= arena_spans);
            assert(stamp == arena_stamp);
            assert forall|k: int| 0 <= k < spans@.len() implies (#[trigger] spans@[k]).stamp
                <= stamp by {
                assert(arena_spans[k].stamp <= arena_stamp);
            }
        }
        occ.clear();

        // ---- generation advance, with exhaustion handled rather than assumed ----
        // Stamp 0 is the never-written stamp, so a wrap must skip it and
        // re-stamp the whole table once. At u64 and one build per nanosecond
        // that is about 585 years away, but "unreachable in practice" is not a
        // postcondition, so the path is written and proved.
        let ghost stamp0 = stamp;
        let wrapped: bool = stamp == u64::MAX;
        if wrapped {
            let mut z: usize = 0;
            while z < spans.len()
                invariant
                    z <= spans@.len(),
                    forall|q: int| 0 <= q < z ==> (#[trigger] spans@[q]).stamp == 0,
                decreases spans@.len() - z,
            {
                let mut sp = spans[z];
                sp.stamp = 0;
                spans[z] = sp;
                z = z + 1;
            }
            stamp = 1;
            proof {
                assert forall|q: int| 0 <= q < spans@.len() implies (#[trigger] spans@[q]).stamp
                    < stamp by {
                    assert(spans@[q].stamp == 0);
                }
            }
        } else {
            stamp = stamp + 1;
            proof {
                assert forall|q: int| 0 <= q < spans@.len() implies (#[trigger] spans@[q]).stamp
                    < stamp by {
                }
            }
        }
        let g: u64 = stamp;
        proof {
            assert(g > 0);
        }

        // ---- grow the table to the key space ----
        while spans.len() < num_keys
            invariant
                g == stamp,
                g > 0,
                forall|q: int|
                    0 <= q < spans@.len() ==> (#[trigger] spans@[q]).stamp < g,
            decreases num_keys - spans@.len(),
        {
            spans.push(Span { off: 0, len: 0, stamp: 0 });
        }

        // ---- pass 1: population per key, and the occupancy list ----
        Self::count_pass(&mut spans, &mut occ, stream, num_keys, g);
        let ghost spans_after_count = spans@;
        // ---- the occupancy list is injective, and its counts sum to the
        //      stream length: every entry is placed under exactly one key ----
        let ghost occ0 = occ@;
        let ghost pos_of = Seq::new(num_keys as nat, |k: int| spans@[k].off as int);
        proof {
            {
                assert forall|x: int, y: int| 0 <= x < y < occ0.len() implies occ0[x]
                    != occ0[y] by {
                    // each listed key records its own position, so two positions
                    // naming the same key would be the same position
                    assert(spans@[occ0[x] as int].off == x);
                    assert(spans@[occ0[y] as int].off == y);
                }
                assert forall|q: int| 0 <= q < s.len() implies occ0.contains(
                    (#[trigger] s[q]).0,
                ) by {
                    lemma_count_key_positive::<V>(s, q);
                    assert(s[q].0 < num_keys);
                    assert(spans@[s[q].0 as int].stamp == g);
                }
                lemma_sum_counts_is_len::<V>(s, occ0);
            }
        }

        // ---- pass 1b: extents, over the occupied keys only ----
        let stream_len: usize = stream.len();
        proof {
            assert(s.len() == stream_len);
        }
        let total = Self::extent_pass(&mut spans, &occ, num_keys, g, Ghost(s));

        // ---- pass 2: placement, each key's `len` its running cursor ----
        let ghost full_spans = Seq::new(
            spans@.len(),
            |k: int|
                Span {
                    off: spans@[k].off,
                    len: count_key(s, k as nat) as usize,
                    stamp: spans@[k].stamp,
                },
        );
        let mut pool: std::vec::Vec<V> = std::vec::Vec::new();
        pool.resize(total, V::default());
        proof {
            assert(full_spans.len() == spans@.len());
            assert forall|q: int|
                0 <= q < occ0.len() implies {
                &&& full_spans[(#[trigger] occ0[q]) as int].off == sum_counts::<V>(s, occ0, q)
                &&& full_spans[occ0[q] as int].len == count_key(s, occ0[q] as nat)
            } by {
            }
            lemma_extent_tiling::<V>(s, occ0, full_spans, total as nat);
        }
        Self::place_pass(
            &mut spans,
            &mut pool,
            stream,
            num_keys,
            g,
            total,
            Ghost(occ0),
            Ghost(full_spans),
            Ghost(pos_of),
        );

        let ghost spans_final = spans@;
        let a = SpanArena { spans, occ, stamp };
        let r = DenseSpanMap { pool, arena: a, num_keys, stream: Ghost(s) };
        proof {
            {
                assert(r.occ_view() == occ0);
                assert(r.occ_spans() == permute(spans_final, occ0));
                assert(r.stamp_view() == g);
                assert forall|k: int| 0 <= k < num_keys implies ((#[trigger] r.occupied(k))
                    <==> count_key(stream@, k as nat) > 0) by {
                    assert(r.spans_view()[k].stamp == spans_after_count[k].stamp);
                    assert(r.occupied(k) == (spans_after_count[k].stamp == g));
                    assert(count_key(s, k as nat) == count_key(stream@, k as nat));
                }
                assert(r.wf());
                assert forall|k: int| 0 <= k < num_keys implies #[trigger] r.view()[k] == key_slice(
                    s,
                    k as nat,
                ) by {
                    if !r.occupied(k) {
                        lemma_key_slice_len::<V>(s, k as nat);
                        assert(key_slice(s, k as nat) =~= Seq::<V>::empty());
                    }
                }
            }
        }
        r
    }

    /// Two-pass counting build into a fresh span table.
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
        Self::build_in(SpanArena::new(), stream, num_keys)
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

    /// Total shell for the recycled path: refuses an out-of-range key and hands
    /// the arena back rather than consuming it on failure.
    pub fn try_build_in(
        arena: SpanArena,
        stream: &[(usize, V)],
        num_keys: usize,
    ) -> (r: Result<Self, (SpanArena, crate::error::ContainerError)>)
        ensures
            r matches Ok(m) ==> {
                &&& m.wf()
                &&& m.view().len() == num_keys
                &&& m.stream_view() == stream@
                &&& m.total_spec() == stream@.len()
                &&& m.refines()
            },
            r matches Err((back, e)) ==> {
                &&& e == crate::error::ContainerError::IndexOutOfBounds
                &&& true
            },
    {
        if Self::can_build(stream, num_keys) {
            Ok(Self::build_in(arena, stream, num_keys))
        } else {
            Err((arena, crate::error::ContainerError::IndexOutOfBounds))
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
