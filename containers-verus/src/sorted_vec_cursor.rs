// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `SortedVecCursor`: a formally verified galloping seek-and-step cursor over a
//! sorted, duplicate-free slice of dense ids — the array-backed sibling of
//! [`BPlusCursor`](crate::bplus::BPlusCursor) on the same leapfrog-join surface.
//!
//! This is the verified counterpart of the e-graph's `SortedVecCursor`
//! (`egraph/src/index.rs`), the cursor every leapfrog join in production runs
//! on. Its `seek` is the one place in the join layer that does non-trivial index
//! arithmetic — a doubling ladder, a clamp, and a bisection over a *computed*
//! window — which is the one shape where an off-by-one silently drops join
//! results instead of panicking. Property tests pin four properties there
//! (`egraph/src/index.rs`, `mod seek_props`); the theorems below prove the same
//! four for all inputs:
//!
//! | property | proptest | theorem |
//! |---|---|---|
//! | lands on the first key `>= target` | `seek_lands_on_first_ge_*` | `theorem_seek_lands_on_first_ge` |
//! | `pos` never decreases | `seek_sequence_is_monotone_*` | `theorem_seek_is_monotone` |
//! | no key is skipped over | `no_keys_are_skipped_*` | `theorem_seek_never_skips` |
//! | `pos` in bounds, no overflow | `long_gallop_does_not_overflow`, `saturated_ids` | discharged by Verus for [`SortedVecCursor::seek`] |
//!
//! The last row is the one a property test can only sample: Verus proves the
//! ladder's `lo + step` and `step * 2` cannot overflow for *any* slice length
//! and *any* target, and that `pos <= data.len()` always — there is no
//! remaining input to test.
//!
//! ## Model and the shared seek vocabulary
//!
//! The cursor's model is the slice's ids projected to nats, in slice order
//! (`nat_model`). Seek's postcondition is stated with
//! `seek_target_idx` — the *same* spec function
//! `BPlusCursor::seek` uses — so both cursors on the leapfrog surface have
//! literally the same seek contract, differing only in that the B+tree's seek is
//! absolute (it descends from the root) while this one is forward-only from the
//! current position:
//!
//! ```text
//! BPlusCursor::seek:     idx' == seek_target_idx(model, t)
//! SortedVecCursor::seek:  idx' == max(idx, seek_target_idx(model, t))
//! ```
//!
//! The `max` is not slack in the proof, it is the algorithm: production's `seek`
//! returns immediately when the cursor already satisfies the target. This is
//! common when the `Difference` combinator seeks both sides to the same key, but
//! its workload frequency is a Criterion/instrumentation result, not a fixed
//! property of the cursor. A cursor positioned past the target stays put.
//! Forward-only is
//! exactly what leapfrog requires, and it is what makes
//! `theorem_seek_is_monotone` hold unconditionally.
//!
//! ## Why the gallop is the interesting part
//!
//! A plain `partition_point` over the whole remainder is `O(log rem)`. The
//! gallop doubles an offset from the cursor until it lands on or past the
//! target, then bisects the bounded window it just proved brackets the answer,
//! making the cost `O(log d)` in the distance *advanced*. Current constant-factor
//! and end-to-end effects belong in the Criterion cursor and saturation
//! benchmarks. Correctness rests on one loop invariant:
//! **`model[lo] < t`**. That is what makes the window `lo+1 .. hi`
//! sound rather than `lo .. hi` — index `lo` is already known to be below the
//! target, so excluding it cannot skip the answer. (Both spellings return the
//! same index *because* of that invariant, which is why mutating the production
//! bisection to `lo..hi` survives every test: it is a genuine equivalence, and
//! here it is a proven one.)
//!
//! ## Overflow, and one deliberate spelling difference from production
//!
//! Production writes the ladder guard as `lo + step < n`; this module writes the
//! equivalent `step < n - lo`. Both test the same thing, and neither can
//! overflow — the invariant `step <= lo + 1` bounds `lo + step` by `2n`, and a
//! Rust slice length is at most `isize::MAX`, so `2n` fits a `usize`. But that
//! last step needs the slice-length bound as an axiom, and `n - lo` (safe from
//! `lo < n` alone) needs nothing. The verified spelling is the one that is
//! overflow-free from the invariant rather than from a fact about slices, so it
//! is the one used here; `hi = (lo + step).min(n)` is rewritten the same way,
//! into the `if` that computes the identical value.

use vstd::prelude::*;

// `seek_target_idx` and the two split lemmas are SPEC/PROOF items, which the
// `verus!` macro erases entirely in a plain cargo build — a top-level `use` of
// them would not resolve there. Referenced by full path inside `verus!{}`
// instead, which is `bplus.rs`'s own convention for the same reason.
use crate::index_like::IndexLike;
use crate::opt::DenseId;

verus! {

/// A slice of ids projected to its model: the dense indices, in slice order.
///
/// Written as a free spec function rather than a method so the theorems can
/// speak about a bare `Seq<K>` (e.g. a slice the caller has not yet made a
/// cursor over).
pub open spec fn nat_model<K: DenseId>(s: Seq<K>) -> Seq<nat> {
    s.map_values(|k: K| k.id_nat())
}

/// `nat_model` is length-preserving. Split out from
/// [`lemma_nat_model_index`] because `step`'s overflow check needs the length
/// with no index in hand.
pub proof fn lemma_nat_model_len<K: DenseId>(s: Seq<K>)
    ensures
        nat_model(s).len() == s.len(),
{
}

/// `nat_model` is pointwise `id_nat` and length-preserving. Trivial from
/// `map_values`, but stated so proofs can instantiate it at an index without
/// fighting the `map_values` trigger.
pub proof fn lemma_nat_model_index<K: DenseId>(s: Seq<K>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        nat_model(s).len() == s.len(),
        nat_model(s)[i] == s[i].id_nat(),
{
}

/// Cursor over a sorted, duplicate-free slice of ids.
///
/// `pos` is both the executable position and the model index — unlike
/// `BPlusCursor`, whose `(node, pos)` pair needs a ghost `gidx` to name its
/// place in the model, an array-backed cursor's position *is* its model index.
/// That is the whole reason this cursor's proofs are short: there is no
/// arena-to-model refinement to carry, only the seek arithmetic.
///
/// `pos == data.len()` marks "exhausted". Production parity:
/// `egraph/src/index.rs`'s `SortedVecCursor { data, pos }`, field for field.
pub struct SortedVecCursor<'a, K: DenseId> {
    pub(crate) data: &'a [K],
    pub(crate) pos: usize,
}

impl<'a, K: DenseId> SortedVecCursor<'a, K> {
    /// The cursor's model: the slice's ids as nats, in order.
    pub open(crate) spec fn model(&self) -> Seq<nat> {
        nat_model(self.data@)
    }

    /// The cursor's position in the model. `== model().len()` when exhausted.
    pub open(crate) spec fn idx(&self) -> int {
        self.pos as int
    }

    /// Well-formedness: the model is strictly sorted (the representation
    /// invariant of the `SortedVec` this cursors over — `IndexStore::build_from`
    /// establishes it by sorting and deduping each bucket) and the position is
    /// in bounds, exhausted-end included.
    ///
    /// Strict sortedness, not merely non-decreasing, is what lets this module
    /// reuse `bplus`'s seek lemmas verbatim; it is also what the dedup gives.
    pub open(crate) spec fn cursor_wf(&self) -> bool {
        &&& crate::bplus_tree::strictly_sorted(self.model())
        &&& self.idx() <= self.model().len()
    }

    /// Structural well-formedness alone: the position is in bounds, exhausted
    /// end included. `new` establishes it and every method preserves it, with
    /// no assumption on the data; `cursor_wf` is exactly `pos_wf` plus the
    /// sortedness hypothesis.
    pub open(crate) spec fn pos_wf(&self) -> bool {
        self.idx() <= self.model().len()
    }

    /// Position at the start of `data`. Requires-free: any slice is accepted,
    /// and the cursor's method contracts state their characterizations under
    /// the hypothesis that the data's model is strictly sorted (`cursor_wf`).
    /// A caller that proves sortedness gets the full contracts; every caller
    /// gets the in-bounds guarantees.
    pub fn new(data: &'a [K]) -> (r: Self)
        ensures
            r.pos_wf(),
            r.idx() == 0,
            r.model() == nat_model(data@),
            crate::bplus_tree::strictly_sorted(nat_model(data@)) ==> r.cursor_wf(),
    {
        SortedVecCursor { data, pos: 0 }
    }

    /// The cursor's position, as a `usize` — the executable read of
    /// `Self::idx`, which is a spec function and so invisible to a plain build.
    ///
    /// Exists so a consumer (and the erased-build test harness) can observe the
    /// position without reaching into the private field. Nothing in the proofs
    /// needs it; the `ensures` is what makes it usable as an oracle.
    #[inline]
    pub fn pos(&self) -> (r: usize)
        ensures
            r as int == self.idx(),
    {
        self.pos
    }

    /// Is the cursor positioned on a key (rather than exhausted)?
    #[inline]
    pub fn is_valid(&self) -> (b: bool)
        ensures
            b == (self.idx() < self.model().len()),
    {
        self.pos < self.data.len()
    }

    /// The key at the cursor. Requires-free: exhaustion is refused at runtime,
    /// and the ensures needs no sortedness — it only ties the returned key to
    /// the model at the current position.
    #[inline]
    pub fn key(&self) -> (r: K)
        ensures
            self.idx() < self.model().len() ==> r.id_nat() == self.model()[self.idx()],
    {
        // Total-with-documented-panic: exhaustion is the branch.
        if !(self.pos < self.data.len()) {
            crate::guard::refuse("SortedVecCursor::key: cursor exhausted");
        }
        proof {
            lemma_nat_model_index(self.data@, self.idx());
        }
        self.data[self.pos]
    }

    /// Advance one key.
    ///
    /// Unlike `BPlusCursor::step`, which clamps at the exhausted end, this
    /// mirrors production exactly: it is `pos += 1` unconditionally, and the
    /// `requires` is what keeps it in bounds. Production's `step` is only ever
    /// called under `is_valid`, and every leapfrog combinator does so.
    #[inline]
    /// `pub(crate)` and suffixed `_unchecked`: the inherent method shadows the
    /// guarded `SortedCursor::step` impl under method resolution, and its
    /// `requires` (cursor not exhausted) is erased at runtime. External
    /// callers get only the trait impl, which tests `is_valid` first.
    pub(crate) fn step_unchecked(&mut self)
        requires
            old(self).cursor_wf(),
            old(self).idx() < old(self).model().len(),
        ensures
            final(self).cursor_wf(),
            final(self).model() == old(self).model(),
            final(self).idx() == old(self).idx() + 1,
    {
        // `pos < model.len() == data@.len()`, and a slice's length is a `usize`,
        // so the increment cannot overflow. The bridge is the only content.
        // `pos < model.len() == data@.len() == data.len()`, and a slice length is
        // a `usize`, so the increment cannot overflow. The exec `len()` read is
        // what ties the ghost `Seq` length to a `usize` bound; the lemma ties the
        // model length to the slice's.
        let n = self.data.len();
        proof { lemma_nat_model_len(self.data@); }
        assert(self.pos < n);
        self.pos = self.pos + 1;
    }

    /// Advance to the first key `>= target`, or exhaust. Forward-only: a cursor
    /// already at or past the target does not move.
    ///
    /// Galloping doubles an offset from the cursor until it lands on or past the
    /// target, then bisects the window
    /// that offset just proved brackets the answer. `O(log d)` in the distance
    /// advanced rather than `O(log rem)` in the remainder.
    ///
    /// The postcondition is the whole soundness story in one line, and every
    /// theorem below is a corollary of it: the new position is
    /// `seek_target_idx(model, target)` — the count of model keys strictly below
    /// the target, the same spec function `BPlusCursor::seek` lands on — except
    /// where the cursor was already beyond it, in which case it stays.
    ///
    /// `#[inline]` because this is the join layer's hot path -- called once per
    /// leapfrog step through a generic cursor, where inlining also permits
    /// devirtualization. Its machine effect is covered by the Criterion cursor
    /// and saturation benchmarks.
    ///
    /// The bisection below is written as an explicit loop rather than
    /// `data[lo+1..hi].partition_point(..)` (which is what `egraph` called before
    /// it adopted this cursor) because there is no way to state a loop invariant
    /// through std's `partition_point`. The explicit loop also gives the compiler
    /// the code shape used by the maintained implementation; changing it requires
    /// a Criterion comparison as well as the contract tests.
    /// Requires-free: the sortedness hypothesis lives in the ensures as an
    /// implication. On any input the gallop and the bisection stay in bounds
    /// and terminate; the position never decreases and never leaves
    /// `[0, len]` once inside it. Under `cursor_wf` the full forward-only
    /// split-point characterization holds.
    #[inline]
    pub fn seek(&mut self, target: K)
        ensures
            final(self).model() == old(self).model(),
            old(self).idx() <= final(self).idx(),
            old(self).pos_wf() ==> final(self).pos_wf(),
            old(self).cursor_wf() ==> ({
                let ti = crate::bplus::seek_target_idx(old(self).model(), target.id_nat());
                &&& final(self).cursor_wf()
                &&& final(self).idx() == if old(self).idx() >= ti { old(self).idx() } else { ti }
            }),
    {
        let ghost model = self.model();
        let ghost t = target.id_nat();
        // The sortedness hypothesis, captured at entry. Every sortedness-
        // dependent proof step below is guarded on it; the index arithmetic
        // and the loop bounds are proven without it.
        let ghost srt = self.cursor_wf();
        proof {
            if srt {
                crate::bplus::lemma_seek_target_idx_split(model, t);
            }
            // Establishes `target.as_nat() == t`, which both loops carry as an
            // invariant (see the note there).
            K::lemma_as_nat_is_id_nat(target);
        }

        let n = self.data.len();
        assert(model.len() == n);

        // The common case, checked before any bounding work: the cursor already
        // satisfies the seek. Exhausted counts — `seek_target_idx <= n` always,
        // so an exhausted cursor is trivially at or past the target.
        if self.pos >= n {
            return;
        }
        let k0 = self.data[self.pos];
        proof { lemma_nat_model_index(self.data@, self.pos as int); }
        let below = IndexLike::lt(k0, target);
        proof {
            K::lemma_order_is_as_nat(k0, target);
            K::lemma_as_nat_is_id_nat(k0);
            K::lemma_as_nat_is_id_nat(target);
        }
        if !below {
            // model[pos] >= t, and sortedness carries that to every later index,
            // so the split point is at or before pos: the cursor is already
            // satisfied and must not move (forward-only). Only the split-point
            // claim needs the sortedness hypothesis.
            assert(t <= model[self.pos as int]);
            proof {
                if srt {
                    assert(crate::bplus::seek_target_idx(model, t) <= self.pos as int) by {
                        let ti = crate::bplus::seek_target_idx(model, t);
                        if (self.pos as int) < ti {
                            // ti's left arm: every index below ti is < t — including pos.
                            assert(model[self.pos as int] < t);
                        }
                    }
                }
            }
            return;
        }
        assert(model[self.pos as int] < t);

        // Gallop: double the offset until it lands on or past the target, so
        // `lo` stays strictly below it and `hi` is the first known bound.
        //
        // `step < n - lo` rather than production's `lo + step < n`: the same
        // test, but overflow-free from `lo < n` alone (see the module comment).
        let mut step: usize = 1;
        let mut lo: usize = self.pos;
        while step < n - lo && IndexLike::lt(self.data[lo + step], target)
            invariant
                n == self.data.len(),
                model == nat_model(self.data@),
                model.len() == n,
                srt ==> crate::bplus_tree::strictly_sorted(model),
                // The exec comparisons' `ensures` speak `lt_spec` (hence `as_nat`)
                // while the model speaks `id_nat`. A loop body assumes only the
                // invariants, so the bridge law's conclusion must be one.
                target.as_nat() == t,
                self.pos <= lo < n,
                // The load-bearing invariant: `lo` is strictly below the target.
                // This is what makes the `lo+1 .. hi` window sound.
                model[lo as int] < t,
                // `step <= lo + 1` bounds the ladder: `step` starts at 1 with
                // `lo >= 0`, and each doubling moves `lo` forward by the old
                // `step`, so `2*step <= lo' + 1`. With `lo < n` it gives
                // `step <= n`, which is what discharges `step * 2`.
                1 <= step <= lo + 1,
            decreases n - lo,
        {
            // The guard's second conjunct says `data[lo + step] < target`; carry
            // it to the model so the next iteration's `model[lo] < t` holds.
            let kk = self.data[lo + step];
            proof {
                lemma_nat_model_index(self.data@, (lo + step) as int);
                K::lemma_order_is_as_nat(kk, target);
                K::lemma_as_nat_is_id_nat(kk);
                assert(model[(lo + step) as int] < t);
            }
            lo = lo + step;
            step = step * 2;
        }

        // Loop exit leaves one of two facts, and `hi` records which:
        //   - `step >= n - lo`: the ladder ran off the end, so `hi = n` and
        //     there is no upper key to appeal to.
        //   - otherwise `model[lo + step] >= t`, so `hi = lo + step` is a real
        //     upper bound.
        // Same value as production's `(lo + step).min(n)`, spelled to avoid the
        // `lo + step` sum.
        let hi: usize = if step < n - lo { lo + step } else { n };
        assert(lo < hi <= n);
        assert(hi < n ==> t <= model[hi as int]) by {
            if hi < n {
                lemma_nat_model_index(self.data@, hi as int);
                let kk = self.data@[hi as int];
                K::lemma_order_is_as_nat(kk, target);
                K::lemma_as_nat_is_id_nat(kk);
                K::lemma_as_nat_is_id_nat(target);
            }
        }

        // `lo` is known below the target and `hi` at or past it, so bisect the
        // open interval between them. Production spells this
        // `lo + 1 + data[lo + 1..hi].partition_point(|x| *x < target)`.
        let mut a: usize = lo + 1;
        let mut b: usize = hi;
        while a < b
            invariant
                n == self.data.len(),
                model == nat_model(self.data@),
                model.len() == n,
                srt ==> crate::bplus_tree::strictly_sorted(model),
                // The exec comparisons' `ensures` speak `lt_spec` (hence `as_nat`)
                // while the model speaks `id_nat`. A loop body assumes only the
                // invariants, so the bridge law's conclusion must be one.
                target.as_nat() == t,
                lo < n,
                lo + 1 <= a <= b <= hi <= n,
                model[lo as int] < t,
                hi < n ==> t <= model[hi as int],
                srt ==> forall|i: int| lo < i < a ==> #[trigger] model[i] < t,
                srt ==> forall|i: int| b <= i < hi ==> t <= #[trigger] model[i],
            decreases b - a,
        {
            let mid = a + (b - a) / 2;
            let km = self.data[mid];
            proof {
                lemma_nat_model_index(self.data@, mid as int);
                K::lemma_order_is_as_nat(km, target);
                K::lemma_as_nat_is_id_nat(km);
                K::lemma_as_nat_is_id_nat(target);
            }
            let is_lt = IndexLike::lt(km, target);
            // The pivot fact, in model terms, from which sortedness does the rest.
            assert(is_lt == (model[mid as int] < t));
            if is_lt {
                // sorted: model[mid] < t carries down to every i <= mid.
                proof {
                    if srt {
                        assert forall|i: int| lo < i <= mid implies #[trigger] model[i] < t by {
                            if i < mid {
                                assert(model[i] < model[mid as int]);
                            }
                        }
                    }
                }
                a = mid + 1;
            } else {
                // sorted: t <= model[mid] carries up to every i >= mid.
                proof {
                    if srt {
                        assert forall|i: int| mid <= i < hi implies t <= #[trigger] model[i] by {
                            if mid < i {
                                assert(model[mid as int] < model[i]);
                            }
                        }
                    }
                }
                b = mid;
            }
        }

        // `a` splits the WHOLE model at the target, so it is *the* split point:
        //   - `i < a`: below `lo` by sortedness under `model[lo] < t`, at `lo`
        //     by the invariant, and in `(lo, a)` by the bisection's left arm.
        //   - `i >= a`: in `[a, hi)` by the right arm (a == b at exit), and at
        //     or past `hi` by sortedness under `t <= model[hi]` — vacuous when
        //     `hi == n`.
        // Uniqueness of split points then equates it to `seek_target_idx`,
        // which is what the postcondition asks for. The whole argument sits
        // under the sortedness hypothesis; without it the postcondition asks
        // only for bounds and monotonicity, both structural (`pos < lo + 1 <=
        // a <= n`).
        proof {
            if srt {
                assert forall|i: int| 0 <= i < a implies #[trigger] model[i] < t by {
                    if i < (lo as int) {
                        assert(model[i] < model[lo as int]);
                    }
                }
                assert forall|i: int| a <= i < model.len() implies t <= #[trigger] model[i] by {
                    if (hi as int) <= i && hi < n {
                        if (hi as int) < i {
                            assert(model[hi as int] < model[i]);
                        }
                    }
                }
                crate::bplus::lemma_seek_target_idx_unique(model, t, a as int);
                // The entry key was strictly below the target, so the split
                // point is strictly past the entry position: the `max` in the
                // postcondition resolves to `seek_target_idx`.
                let ti = crate::bplus::seek_target_idx(model, t);
                if ti <= self.pos as int {
                    assert(t <= model[self.pos as int]);
                }
            }
        }
        self.pos = a;
    }
}

// ---------------------------------------------------------------------------
// Soundness theorems
//
// Each is a corollary of `seek`'s postcondition plus `lemma_seek_target_idx_
// split`, and each names one of the four properties the production cursor's
// property tests sample (`egraph/src/index.rs`, `mod seek_props`). They are
// stated separately because the postcondition is stated in `seek_target_idx`,
// which is a *count*: turning that count into "lands on the first key >= t" and
// "skipped nothing" is precisely the step a reader of the join code needs, and
// it should be proven once here rather than re-derived at each call site.
// ---------------------------------------------------------------------------

/// **Seek lands on the first key `>= target`.** The cursor ends either
/// positioned on a key at or above the target whose predecessor (if the seek
/// moved at all) is strictly below it, or exhausted with every key below the
/// target.
///
/// Proptest counterpart: `seek_lands_on_first_ge_31` / `_63`.
pub proof fn theorem_seek_lands_on_first_ge<K: DenseId>(
    c: &SortedVecCursor<'_, K>,
    pre_idx: int,
    t: nat,
)
    requires
        c.cursor_wf(),
        // the shape `seek` leaves behind (its postcondition, instantiated)
        0 <= pre_idx <= c.model().len(),
        c.idx() == if pre_idx >= crate::bplus::seek_target_idx(c.model(), t) {
            pre_idx
        } else {
            crate::bplus::seek_target_idx(c.model(), t)
        },
        // the cursor was not already past the target — i.e. the seek is the
        // thing that determined the position, which is the case leapfrog cares
        // about. (When it *was* already past, the position is unchanged and
        // there is nothing to state.)
        pre_idx <= crate::bplus::seek_target_idx(c.model(), t),
    ensures
        // in bounds, exhausted-end included
        0 <= c.idx() <= c.model().len(),
        // positioned: the key is at or above the target...
        c.idx() < c.model().len() ==> t <= c.model()[c.idx()],
        // ...and it is the FIRST such key: everything before is strictly below.
        forall|i: int| 0 <= i < c.idx() ==> #[trigger] c.model()[i] < t,
        // exhausted: no key reaches the target at all.
        c.idx() == c.model().len() ==> forall|i: int|
            0 <= i < c.model().len() ==> #[trigger] c.model()[i] < t,
{
    crate::bplus::lemma_seek_target_idx_split(c.model(), t);
}

/// **Seek never skips a key `>= target`.** Every index the cursor passed over
/// held a key strictly below the target — so a leapfrog join cannot lose a
/// result to a seek overshooting. This is the property the gallop could break
/// and the reason the doubling ladder needs the `model[lo] < t` invariant.
///
/// Proptest counterpart: `no_keys_are_skipped_31` / `_63`.
pub proof fn theorem_seek_never_skips<K: DenseId>(
    c: &SortedVecCursor<'_, K>,
    pre_idx: int,
    t: nat,
)
    requires
        c.cursor_wf(),
        0 <= pre_idx <= c.model().len(),
        c.idx() == if pre_idx >= crate::bplus::seek_target_idx(c.model(), t) {
            pre_idx
        } else {
            crate::bplus::seek_target_idx(c.model(), t)
        },
        pre_idx <= crate::bplus::seek_target_idx(c.model(), t),
    ensures
        // nothing in the traversed range could have matched the target
        forall|i: int| pre_idx <= i < c.idx() ==> #[trigger] c.model()[i] < t,
        // and in particular, if the target is present in the model, the cursor
        // stopped exactly on it rather than stepping past
        (exists|w: int| pre_idx <= w < c.model().len() && c.model()[w] == t) ==> {
            &&& c.idx() < c.model().len()
            &&& c.model()[c.idx()] == t
        },
{
    let model = c.model();
    crate::bplus::lemma_seek_target_idx_split(model, t);
    let r = crate::bplus::seek_target_idx(model, t);
    if exists|w: int| pre_idx <= w < model.len() && model[w] == t {
        let w = choose|w: int| pre_idx <= w < model.len() && model[w] == t;
        // `w` is not in the left part (its key is not `< t`), so `r <= w < len`;
        // and `model[r] >= t` with `model[r] <= model[w] == t` by sortedness.
        assert(r <= w) by {
            if w < r {
                assert(model[w] < t);
            }
        }
        assert(t <= model[r]);
        if r < w {
            assert(model[r] < model[w]);
        }
    }
}

/// **Seek is monotone.** The position never decreases, which is leapfrog's
/// forward-only contract — and what lets the `Difference` combinator seek its
/// delta cursor repeatedly without rewinding.
///
/// Immediate from the `max` in `seek`'s postcondition; stated because it is the
/// property a caller reasons with, not the one the postcondition spells.
///
/// Proptest counterpart: `seek_sequence_is_monotone_31` / `_63`.
pub proof fn theorem_seek_is_monotone<K: DenseId>(c: &SortedVecCursor<'_, K>, pre_idx: int, t: nat)
    requires
        c.cursor_wf(),
        0 <= pre_idx <= c.model().len(),
        c.idx() == if pre_idx >= crate::bplus::seek_target_idx(c.model(), t) {
            pre_idx
        } else {
            crate::bplus::seek_target_idx(c.model(), t)
        },
    ensures
        pre_idx <= c.idx(),
        c.idx() <= c.model().len(),
{
    crate::bplus::lemma_seek_target_idx_split(c.model(), t);
}

/// **Stepping from any position enumerates the tail in order, with nothing
/// skipped or repeated.** `step` advances the model index by exactly one, so
/// the keys a drain observes from position `p` are `model[p], model[p+1], ...`
/// — strictly increasing and covering every remaining index.
///
/// The `strictly_sorted` model plus `step`'s `idx() == old + 1` postcondition is
/// the whole content; this states it in the form the join reads it in (the
/// analogue of `BPlusCursor`'s `theorem_traversal_in_order`, which needs far
/// more work because its positions live in an arena).
///
/// Proptest counterpart: the drain phase of `no_keys_are_skipped_31` / `_63`.
pub proof fn theorem_step_enumerates_tail<K: DenseId>(c: &SortedVecCursor<'_, K>)
    requires
        c.cursor_wf(),
    ensures
        forall|i: int, j: int|
            c.idx() <= i < j < c.model().len() ==> #[trigger] c.model()[i] < #[trigger] c.model()[j],
{
}
} // verus!
