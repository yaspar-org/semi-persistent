// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A semi-persistent vector's diff log with a runtime-selectable value
//! representation (`doc/design/09-diff-stack-compression.md`).
//!
//! `DiffLog<T, I>` stores the sequence of captured `(old_value, index)` diff
//! entries. Its **abstract view is `Seq<(T, I)>`** regardless of representation,
//! so `Vec`'s mark/restore proofs — which are stated over `diff_log@` — carry
//! unchanged when the concrete storage compresses. The index column is always a
//! contiguous `Vec<I>` (the capture-flag ops need an `&[I]` slice); the value
//! column is either stored plainly or value-major compressed, chosen per instance
//! at construction (`None` for SMT speed, `ValueDict` for the union-find value
//! columns under equality saturation).
//!
//! Value-major (`Dict`) is a two-tier value column: an ordered sequence of
//! IMMUTABLE per-frame `ValFrame`s (`dict` + narrow/bit-packed codes), the cold
//! tier, followed by a plain, still-growable hot `tail`. `push` appends to `tail`
//! in O(1); `compact_tail` (called at mark) folds the closed frame's tail values
//! into one new immutable cold frame in O(frame). Packed codes never need appending
//! because each cold frame is written once. The index column stays whole, so the
//! value compression is invisible to the capture machinery's `indices()` slice.

use crate::diff_compress::CompressionMode;
use crate::diff_compress::{ColdFrame, RunCol, ValFrame, sort_frame_by_index};
use crate::index_like::IndexLike;
use vstd::prelude::*;

verus! {

/// The concatenated value sequence of the cold frames, in order (mirrors
/// `compressed_stack::decode_all` for the value-only frames). Opaque so the `Vec`
/// wf check (which reaches it through `DiffLog::wf`/`@`) does not unfold the
/// recursion; the lemmas below `reveal_with_fuel` it where they need its definition.
#[verifier::opaque]
pub open spec fn cold_vals<T: Copy>(cold: Seq<ValFrame<T>>) -> Seq<T>
    decreases cold.len(),
{
    if cold.len() == 0 {
        Seq::empty()
    } else {
        cold[0].decode() + cold_vals(cold.subrange(1, cold.len() as int))
    }
}

/// Appending a cold frame extends the concatenation by exactly that frame's decode.
pub proof fn lemma_cold_vals_snoc<T: Copy>(cold: Seq<ValFrame<T>>, f: ValFrame<T>)
    ensures cold_vals(cold.push(f)) == cold_vals(cold) + f.decode(),
    decreases cold.len(),
{
    reveal_with_fuel(cold_vals, 2);
    if cold.len() == 0 {
        assert(cold.push(f) =~= seq![f]);
        assert(cold_vals(cold) =~= Seq::<T>::empty());
        assert(cold_vals(cold.push(f)) =~= f.decode());
    } else {
        let tail = cold.subrange(1, cold.len() as int);
        lemma_cold_vals_snoc(tail, f);
        assert(cold.push(f)[0] == cold[0]);
        assert(cold.push(f).subrange(1, cold.push(f).len() as int) =~= tail.push(f));
        let a = cold[0].decode();
        let b = cold_vals(tail);
        let c = f.decode();
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// `cold_vals(cold)[i]` is the value at offset `i - base` in the frame `k` whose
/// prefix length is `base == cold_vals(cold[0..k]).len()`. The random-access bridge
/// `index()` needs to read one cold entry.
pub proof fn lemma_cold_vals_at<T: Copy>(cold: Seq<ValFrame<T>>, k: int, i: int)
    requires
        0 <= k < cold.len(),
        cold_vals(cold.subrange(0, k)).len() <= i,
        i < cold_vals(cold.subrange(0, k)).len() + cold[k].decode().len(),
    ensures
        cold_vals(cold)[i] == cold[k].decode()[i - cold_vals(cold.subrange(0, k)).len()],
    decreases cold.len(),
{
    reveal_with_fuel(cold_vals, 2);
    let head = cold[0];
    let rest = cold.subrange(1, cold.len() as int);
    if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<ValFrame<T>>::empty());
        // i < head.decode().len() (from the requires), and cold_vals(cold)
        // == head.decode() + cold_vals(rest), so index i is in the head.
        assert(i < head.decode().len());
        assert(cold_vals(cold) == head.decode() + cold_vals(rest));
        assert(cold_vals(cold)[i] == head.decode()[i]);
    } else {
        // Strip the head; recurse on `rest`, `k-1`, `i - head.decode().len()`.
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        // cold_vals(cold[0..k]) == head.decode() + cold_vals(rest[0..k-1]).
        assert(cold_vals(cold.subrange(0, k))
            =~= head.decode() + cold_vals(rest.subrange(0, k - 1)));
        let base = cold_vals(cold.subrange(0, k)).len();
        let hl = head.decode().len();
        assert(base == hl + cold_vals(rest.subrange(0, k - 1)).len());
        assert(i >= hl);
        lemma_cold_vals_at(rest, k - 1, i - hl);
        assert(rest[k - 1] == cold[k]);
        // i is in range: i < base + cold[k].decode().len() <= cold_vals(cold).len().
        lemma_cold_vals_split(cold, k);
        assert(cold.subrange(k, cold.len() as int)[0] == cold[k]);
        assert(cold_vals(cold.subrange(k, cold.len() as int))
            == cold[k].decode() + cold_vals(cold.subrange(k, cold.len() as int).subrange(1, cold.subrange(k, cold.len() as int).len() as int)));
        assert(i < cold_vals(cold).len());
        assert(cold_vals(cold) == head.decode() + cold_vals(rest));
        assert(cold_vals(cold)[i] == cold_vals(rest)[i - hl]);
    }
}

/// The value column: plain, or value-major (immutable cold frames + hot tail).
pub enum DiffVals<T> {
    Plain(Vec<T>),
    Dict { cold: Vec<ValFrame<T>>, tail: Vec<T> },
}

impl<T: Copy> DiffVals<T> {
    /// Number of values.
    pub open spec fn len_spec(self) -> nat {
        match self {
            DiffVals::Plain(v) => v@.len(),
            DiffVals::Dict { cold, tail } => cold_vals(cold@).len() + tail@.len(),
        }
    }

    /// The value at position `i`: cold-frame decode below the tail, direct read in it.
    pub open spec fn val_at(self, i: int) -> T {
        match self {
            DiffVals::Plain(v) => v@[i],
            DiffVals::Dict { cold, tail } =>
                if i < cold_vals(cold@).len() {
                    cold_vals(cold@)[i]
                } else {
                    tail@[i - cold_vals(cold@).len()]
                },
        }
    }

    /// Every cold frame is well-formed (its codes index its dictionary).
    pub open spec fn wf(self) -> bool {
        match self {
            DiffVals::Plain(_) => true,
            DiffVals::Dict { cold, .. } =>
                forall|k: int| 0 <= k < cold@.len() ==> (#[trigger] cold@[k]).wf(),
        }
    }
}

/// The index-major dual of `cold_vals`: concatenate each cold `RunCol` frame's
/// index projection (`idx_seq`). A `RunCol<(), I>` frame stores only run starts and
/// zero-size values, so its `idx_seq` is the whole reconstructed index sequence, and
/// the stored index column is dropped down to one `start` per run. Opaque so the
/// `Vec` wf check does not unfold the recursion.
#[verifier::opaque]
pub open spec fn cold_idxs<I: IndexLike>(cold: Seq<RunCol<(), I>>) -> Seq<I>
    decreases cold.len(),
{
    if cold.len() == 0 {
        Seq::empty()
    } else {
        cold[0].idx_seq() + cold_idxs(cold.subrange(1, cold.len() as int))
    }
}

/// Appending a cold frame extends the concatenation by exactly that frame's `idx_seq`.
pub proof fn lemma_cold_idxs_snoc<I: IndexLike>(cold: Seq<RunCol<(), I>>, f: RunCol<(), I>)
    ensures cold_idxs(cold.push(f)) == cold_idxs(cold) + f.idx_seq(),
    decreases cold.len(),
{
    reveal_with_fuel(cold_idxs, 2);
    if cold.len() == 0 {
        assert(cold.push(f) =~= seq![f]);
        assert(cold_idxs(cold) =~= Seq::<I>::empty());
        assert(cold_idxs(cold.push(f)) =~= f.idx_seq());
    } else {
        let tail = cold.subrange(1, cold.len() as int);
        lemma_cold_idxs_snoc(tail, f);
        assert(cold.push(f)[0] == cold[0]);
        assert(cold.push(f).subrange(1, cold.push(f).len() as int) =~= tail.push(f));
        let a = cold[0].idx_seq();
        let b = cold_idxs(tail);
        let c = f.idx_seq();
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// `cold_idxs(cold)[i]` is the index at offset `i - base` in frame `k` whose prefix
/// length is `base == cold_idxs(cold[0..k]).len()`. The random-access bridge `index`.
pub proof fn lemma_cold_idxs_at<I: IndexLike>(cold: Seq<RunCol<(), I>>, k: int, i: int)
    requires
        0 <= k < cold.len(),
        cold_idxs(cold.subrange(0, k)).len() <= i,
        i < cold_idxs(cold.subrange(0, k)).len() + cold[k].idx_seq().len(),
    ensures
        cold_idxs(cold)[i] == cold[k].idx_seq()[i - cold_idxs(cold.subrange(0, k)).len()],
    decreases cold.len(),
{
    reveal_with_fuel(cold_idxs, 2);
    let head = cold[0];
    let rest = cold.subrange(1, cold.len() as int);
    if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<RunCol<(), I>>::empty());
        assert(i < head.idx_seq().len());
        assert(cold_idxs(cold) == head.idx_seq() + cold_idxs(rest));
        assert(cold_idxs(cold)[i] == head.idx_seq()[i]);
    } else {
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold_idxs(cold.subrange(0, k))
            =~= head.idx_seq() + cold_idxs(rest.subrange(0, k - 1)));
        let base = cold_idxs(cold.subrange(0, k)).len();
        let hl = head.idx_seq().len();
        assert(base == hl + cold_idxs(rest.subrange(0, k - 1)).len());
        assert(i >= hl);
        lemma_cold_idxs_at(rest, k - 1, i - hl);
        assert(rest[k - 1] == cold[k]);
        lemma_cold_idxs_split(cold, k);
        assert(cold.subrange(k, cold.len() as int)[0] == cold[k]);
        assert(i < cold_idxs(cold).len());
        assert(cold_idxs(cold) == head.idx_seq() + cold_idxs(rest));
        assert(cold_idxs(cold)[i] == cold_idxs(rest)[i - hl]);
    }
}

/// The first `rem` indices of frame `k` are entries `[base, base+rem)` of the whole
/// concatenation, `base == cold_idxs(cold[0..k]).len()`. For the truncate partial case.
pub proof fn lemma_cold_idxs_at_prefix<I: IndexLike>(cold: Seq<RunCol<(), I>>, k: int, rem: int)
    requires
        0 <= k < cold.len(),
        0 <= rem <= cold[k].idx_seq().len(),
    ensures
        forall|t: int| 0 <= t < rem ==>
            cold_idxs(cold)[cold_idxs(cold.subrange(0, k)).len() + t] == cold[k].idx_seq()[t],
{
    let base = cold_idxs(cold.subrange(0, k)).len();
    assert forall|t: int| 0 <= t < rem implies
        cold_idxs(cold)[base + t] == cold[k].idx_seq()[t] by {
        lemma_cold_idxs_at(cold, k, base + t);
    }
}

/// `cold_idxs` splits at any frame boundary.
pub proof fn lemma_cold_idxs_split<I: IndexLike>(cold: Seq<RunCol<(), I>>, k: int)
    requires 0 <= k <= cold.len(),
    ensures
        cold_idxs(cold) == cold_idxs(cold.subrange(0, k))
            + cold_idxs(cold.subrange(k, cold.len() as int)),
    decreases cold.len(),
{
    reveal_with_fuel(cold_idxs, 2);
    if cold.len() == 0 {
        assert(cold.subrange(0, k) =~= Seq::<RunCol<(), I>>::empty());
        assert(cold.subrange(k, cold.len() as int) =~= Seq::<RunCol<(), I>>::empty());
        assert(cold_idxs(cold) =~= Seq::<I>::empty());
    } else if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<RunCol<(), I>>::empty());
        assert(cold.subrange(0, cold.len() as int) =~= cold);
    } else {
        let head = cold[0];
        let rest = cold.subrange(1, cold.len() as int);
        lemma_cold_idxs_split(rest, k - 1);
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold.subrange(0, k)[0] == head);
        assert(cold_idxs(cold.subrange(0, k))
            =~= head.idx_seq() + cold_idxs(rest.subrange(0, k - 1)));
        assert(cold.subrange(k, cold.len() as int) =~= rest.subrange(k - 1, rest.len() as int));
        let a = head.idx_seq();
        let b = cold_idxs(rest.subrange(0, k - 1));
        let c = cold_idxs(rest.subrange(k - 1, rest.len() as int));
        assert(a + (b + c) =~= (a + b) + c);
    }
}

// ===========================================================================
// cold_adaptive: the per-frame-adaptive cold tier's concatenation. Each cold frame
// is a `ColdFrame` (plain / value-major / index-major, chosen per frame), so the
// concatenation of their `decode()`s is the flat write sequence of the cold region.
// Mirrors cold_idxs/cold_vals; the four lemmas are the same shape.
// ===========================================================================

/// Flat write sequence of the adaptive cold tier: concatenate each frame's `decode()`.
#[verifier::opaque]
pub open spec fn cold_adaptive<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(cold: Seq<ColdFrame<T, I, VC>>) -> Seq<(T, I)>
    decreases cold.len(),
{
    if cold.len() == 0 {
        Seq::empty()
    } else {
        cold[0].decode() + cold_adaptive(cold.subrange(1, cold.len() as int))
    }
}

/// Appending a cold frame extends the concatenation by exactly that frame's `decode()`.
pub proof fn lemma_cold_adaptive_snoc<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    cold: Seq<ColdFrame<T, I, VC>>, f: ColdFrame<T, I, VC>,
)
    ensures cold_adaptive(cold.push(f)) == cold_adaptive(cold) + f.decode(),
    decreases cold.len(),
{
    reveal_with_fuel(cold_adaptive, 2);
    if cold.len() == 0 {
        assert(cold.push(f) =~= seq![f]);
        assert(cold_adaptive(cold) =~= Seq::<(T, I)>::empty());
        assert(cold_adaptive(cold.push(f)) =~= f.decode());
    } else {
        let tail = cold.subrange(1, cold.len() as int);
        lemma_cold_adaptive_snoc(tail, f);
        assert(cold.push(f)[0] == cold[0]);
        assert(cold.push(f).subrange(1, cold.push(f).len() as int) =~= tail.push(f));
        let a = cold[0].decode();
        let b = cold_adaptive(tail);
        let c = f.decode();
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// `cold_adaptive(cold)[i]` lands in frame `k` at offset `i - base`, where
/// `base == cold_adaptive(cold[0..k]).len()`. The random-access bridge `index` needs.
pub proof fn lemma_cold_adaptive_at<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    cold: Seq<ColdFrame<T, I, VC>>, k: int, i: int,
)
    requires
        0 <= k < cold.len(),
        cold_adaptive(cold.subrange(0, k)).len() <= i,
        i < cold_adaptive(cold.subrange(0, k)).len() + cold[k].decode().len(),
    ensures
        cold_adaptive(cold)[i] == cold[k].decode()[i - cold_adaptive(cold.subrange(0, k)).len()],
    decreases cold.len(),
{
    reveal_with_fuel(cold_adaptive, 2);
    let head = cold[0];
    let rest = cold.subrange(1, cold.len() as int);
    if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<ColdFrame<T, I, VC>>::empty());
        assert(i < head.decode().len());
        assert(cold_adaptive(cold) == head.decode() + cold_adaptive(rest));
        assert(cold_adaptive(cold)[i] == head.decode()[i]);
    } else {
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold_adaptive(cold.subrange(0, k))
            =~= head.decode() + cold_adaptive(rest.subrange(0, k - 1)));
        let base = cold_adaptive(cold.subrange(0, k)).len();
        let hl = head.decode().len();
        assert(base == hl + cold_adaptive(rest.subrange(0, k - 1)).len());
        assert(i >= hl);
        lemma_cold_adaptive_at(rest, k - 1, i - hl);
        assert(rest[k - 1] == cold[k]);
        lemma_cold_adaptive_split(cold, k);
        assert(cold.subrange(k, cold.len() as int)[0] == cold[k]);
        assert(i < cold_adaptive(cold).len());
        assert(cold_adaptive(cold) == head.decode() + cold_adaptive(rest));
        assert(cold_adaptive(cold)[i] == cold_adaptive(rest)[i - hl]);
    }
}

/// The first `rem` entries of frame `k` are entries `[base, base+rem)` of the whole
/// concatenation, `base == cold_adaptive(cold[0..k]).len()`. For truncate.
pub proof fn lemma_cold_adaptive_at_prefix<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    cold: Seq<ColdFrame<T, I, VC>>, k: int, rem: int,
)
    requires
        0 <= k < cold.len(),
        0 <= rem <= cold[k].decode().len(),
    ensures
        forall|t: int| 0 <= t < rem ==>
            cold_adaptive(cold)[cold_adaptive(cold.subrange(0, k)).len() + t] == cold[k].decode()[t],
{
    let base = cold_adaptive(cold.subrange(0, k)).len();
    assert forall|t: int| 0 <= t < rem implies
        cold_adaptive(cold)[base + t] == cold[k].decode()[t] by {
        lemma_cold_adaptive_at(cold, k, base + t);
    }
}

/// `cold_adaptive` splits at any frame boundary.
pub proof fn lemma_cold_adaptive_split<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    cold: Seq<ColdFrame<T, I, VC>>, k: int,
)
    requires 0 <= k <= cold.len(),
    ensures
        cold_adaptive(cold) == cold_adaptive(cold.subrange(0, k))
            + cold_adaptive(cold.subrange(k, cold.len() as int)),
    decreases cold.len(),
{
    reveal_with_fuel(cold_adaptive, 2);
    if cold.len() == 0 {
        assert(cold.subrange(0, k) =~= Seq::<ColdFrame<T, I, VC>>::empty());
        assert(cold.subrange(k, cold.len() as int) =~= Seq::<ColdFrame<T, I, VC>>::empty());
        assert(cold_adaptive(cold) =~= Seq::<(T, I)>::empty());
    } else if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<ColdFrame<T, I, VC>>::empty());
        assert(cold.subrange(0, cold.len() as int) =~= cold);
    } else {
        let head = cold[0];
        let rest = cold.subrange(1, cold.len() as int);
        lemma_cold_adaptive_split(rest, k - 1);
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold.subrange(0, k)[0] == head);
        assert(cold_adaptive(cold.subrange(0, k))
            =~= head.decode() + cold_adaptive(rest.subrange(0, k - 1)));
        assert(cold.subrange(k, cold.len() as int) =~= rest.subrange(k - 1, rest.len() as int));
        let a = head.decode();
        let b = cold_adaptive(rest.subrange(0, k - 1));
        let c = cold_adaptive(rest.subrange(k - 1, rest.len() as int));
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// The index column: plain (contiguous, kept whole), or index-major (immutable cold
/// `RunCol` frames that drop the stored index column to run starts + a hot tail).
pub enum DiffIdxs<I> {
    Plain(Vec<I>),
    Runs { cold: Vec<RunCol<(), I>>, tail: Vec<I> },
}

impl<I: IndexLike> DiffIdxs<I> {
    /// Number of indices.
    pub open spec fn len_spec(self) -> nat {
        match self {
            DiffIdxs::Plain(v) => v@.len(),
            DiffIdxs::Runs { cold, tail } => cold_idxs(cold@).len() + tail@.len(),
        }
    }

    /// The index at position `i`: cold-frame reconstruct below the tail, direct in it.
    pub open spec fn idx_at(self, i: int) -> I {
        match self {
            DiffIdxs::Plain(v) => v@[i],
            DiffIdxs::Runs { cold, tail } =>
                if i < cold_idxs(cold@).len() {
                    cold_idxs(cold@)[i]
                } else {
                    tail@[i - cold_idxs(cold@).len()]
                },
        }
    }

    /// Every cold frame is well-formed (its ghost pairs match its runs by `as_nat`).
    pub open spec fn wf(self) -> bool {
        match self {
            DiffIdxs::Plain(_) => true,
            DiffIdxs::Runs { cold, .. } =>
                forall|k: int| 0 <= k < cold@.len() ==> (#[trigger] cold@[k]).wf(),
        }
    }

    /// Whether this is the run-compressed variant (for variant-preservation ensures).
    pub open spec fn is_runs(self) -> bool {
        self is Runs
    }

    /// Length of the cold (already-folded) prefix: `cold_idxs(cold@).len()` for the
    /// run-compressed variant, else the whole plain length. The boundary below which a
    /// sorted tail flush leaves `@` untouched.
    pub open spec fn cold_len_spec(self) -> nat {
        match self {
            DiffIdxs::Plain(v) => v@.len(),
            DiffIdxs::Runs { cold, .. } => cold_idxs(cold@).len(),
        }
    }
}

impl<I: IndexLike> DiffIdxs<I> {
    /// The index at position `i`. Plain: direct read. Runs: reconstruct from the cold
    /// frame containing `i` (walk frames by cached length), or the hot tail. Mirrors
    /// the value cold walk in `DiffVals`/`DiffLog::index`.
    pub fn idx_at_exec(&self, i: usize) -> (r: I)
        requires self.wf(), i < self.len_spec(),
        ensures r == self.idx_at(i as int),
    {
        match self {
            DiffIdxs::Plain(v) => v[i],
            DiffIdxs::Runs { cold, tail } => {
                proof { reveal(cold_idxs); }
                // Walk cold frames carrying the within-frame offset `d == i - prefix_k`,
                // stopping at the frame that contains `i` or when cold is exhausted
                // (then `i` is in the hot tail). No total length is computed.
                let mut d: usize = i;
                let mut k: usize = 0;
                while k < cold.len() && cold[k].entry_len() <= d
                    invariant
                        0 <= k <= cold@.len(),
                        self.wf(),
                        forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                        i == d + cold_idxs(cold@.subrange(0, k as int)).len(),
                        i < self.len_spec(),
                    decreases cold@.len() - k,
                {
                    let flen = cold[k].entry_len();
                    proof {
                        assert(flen == cold@[k as int].idx_seq().len());
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_idxs_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        assert(cold_idxs(cold@.subrange(0, (k + 1) as int)).len()
                            == cold_idxs(cold@.subrange(0, k as int)).len() + flen);
                    }
                    d = d - flen;
                    k = k + 1;
                }
                if k < cold.len() {
                    // Frame k contains i: prefix_k <= i < prefix_k + len_k.
                    proof {
                        lemma_cold_idxs_split(cold@, (k + 1) as int);
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_idxs_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        // i < cold_idxs(cold@).len(), so idx_at reads the cold concatenation.
                        assert(i < cold_idxs(cold@).len());
                        lemma_cold_idxs_at(cold@, k as int, i as int);
                    }
                    cold[k].idx_at(d)
                } else {
                    // Cold exhausted: prefix_k == cold_idxs(cold@).len(), so d == i - it.
                    proof {
                        assert(cold@.subrange(0, k as int) =~= cold@);
                        // i >= cold_idxs(cold@).len(), idx_at reads tail@[i - that] == tail@[d].
                    }
                    tail[d]
                }
            }
        }
    }

    /// Append one index. Plain: push. Runs: push to the hot tail.
    pub fn push_idx(&mut self, idx: I)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).len_spec() == old(self).len_spec() + 1,
            forall|j: int| 0 <= j < old(self).len_spec()
                ==> final(self).idx_at(j) == old(self).idx_at(j),
            final(self).idx_at(old(self).len_spec() as int) == idx,
            final(self).is_runs() == old(self).is_runs(),
    {
        match self {
            DiffIdxs::Plain(v) => {
                v.push(idx);
            }
            DiffIdxs::Runs { tail, .. } => {
                tail.push(idx);
            }
        }
    }
}

/// The adaptive tier's flat length: cold frames' concatenation plus the hot pair tail.
pub open spec fn adaptive_len<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    cold: Seq<ColdFrame<T, I, VC>>, hot: Seq<(T, I)>,
) -> nat {
    cold_adaptive(cold).len() + hot.len()
}

/// Exec length of the adaptive tier: the cold frames' entry counts plus the hot pair
/// tail. Verified: the loop carries `total == adaptive_len(prefix)` via the snoc
/// lemma, and a sum past `usize` takes the crate's documented trap (`refuse`)
/// instead of threading an overflow precondition through the hierarchy.
/// Discharged from the trust ledger 2026-09: formerly `external_body` trusting
/// the running sum.
pub fn adaptive_len_exec<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    cold: &Vec<ColdFrame<T, I, VC>>, hot: &Vec<(T, I)>,
) -> (n: usize)
    requires forall|k: int| 0 <= k < cold@.len() ==> (#[trigger] cold@[k]).wf(),
    ensures n == adaptive_len(cold@, hot@),
{
    let mut total = hot.len();
    let m = cold.len();
    let mut k: usize = 0;
    proof {
        assert(cold@.subrange(0, 0) =~= Seq::<ColdFrame<T, I, VC>>::empty());
        reveal(cold_adaptive);
    }
    while k < m
        invariant
            0 <= k <= m,
            m == cold@.len(),
            forall|j: int| 0 <= j < cold@.len() ==> (#[trigger] cold@[j]).wf(),
            total == hot@.len() + cold_adaptive(cold@.subrange(0, k as int)).len(),
        decreases m - k,
    {
        let e = cold[k].entry_len();
        let next = match total.checked_add(e) {
            Some(v) => v,
            None => crate::guard::refuse("diff log length exceeds usize"),
        };
        proof {
            lemma_cold_adaptive_snoc(cold@.subrange(0, k as int), cold@[k as int]);
            assert(cold@.subrange(0, k as int + 1)
                =~= cold@.subrange(0, k as int).push(cold@[k as int]));
        }
        total = next;
        k += 1;
    }
    proof {
        assert(cold@.subrange(0, m as int) =~= cold@);
    }
    total
}

/// The adaptive tier's entry at position `i`: cold-frame decode below the tail,
/// direct read in it.
pub open spec fn adaptive_at<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    cold: Seq<ColdFrame<T, I, VC>>, hot: Seq<(T, I)>, i: int,
) -> (T, I) {
    if i < cold_adaptive(cold).len() {
        cold_adaptive(cold)[i]
    } else {
        hot[i - cold_adaptive(cold).len()]
    }
}

/// One diff log. Two representations behind one abstract view `Seq<(T, I)>`:
/// `Cols` splits into an index column (plain or index-major runs) and a value column
/// (plain or value-major dict), at most one compressed (A1/A2/A3, fixed mode);
/// `Adaptive` is a per-frame cold tier where each finalized frame independently picks
/// its mode (`ColdFrame`), with a plain hot pair tail and a cached length (A4).
pub enum DiffLog<T: Copy, I, VC: crate::value_compressor::ValueCompressor<T> = crate::value_compressor::NoValueCompression> {
    Cols { idxs: DiffIdxs<I>, vals: DiffVals<T> },
    Adaptive { cold: Vec<ColdFrame<T, I, VC>>, hot: Vec<(T, I)>, len: usize },
}

impl<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>> View for DiffLog<T, I, VC> {
    type V = Seq<(T, I)>;
    open spec fn view(&self) -> Seq<(T, I)> {
        match self {
            DiffLog::Cols { idxs, vals } =>
                Seq::new(idxs.len_spec(), |i: int| (vals.val_at(i), idxs.idx_at(i))),
            DiffLog::Adaptive { cold, hot, .. } =>
                Seq::new(adaptive_len(cold@, hot@), |i: int| adaptive_at(cold@, hot@, i)),
        }
    }
}

impl<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>> DiffLog<T, I, VC> {
    pub open spec fn wf(&self) -> bool {
        match self {
            DiffLog::Cols { idxs, vals } => {
                &&& vals.wf()
                &&& idxs.wf()
                &&& vals.len_spec() == idxs.len_spec()
                &&& (*idxs is Runs ==> *vals is Plain)
            }
            DiffLog::Adaptive { cold, hot, len } => {
                &&& (forall|k: int| 0 <= k < cold@.len() ==> (#[trigger] cold@[k]).wf())
                &&& *len == adaptive_len(cold@, hot@)
                // Every sealed frame has unique indices (first-write-wins capture;
                // compact_adaptive requires it of the folded region and every mode
                // preserves it). This is what lets the restore fast path apply a
                // frame FORWARD (`restore_to`) where the replay model applies it
                // backward: order within a unique-index frame cannot matter.
                &&& (forall|k: int| 0 <= k < cold@.len()
                        ==> crate::diff_compress::unique_idx((#[trigger] cold@[k]).decode()))
            }
        }
    }

    /// Whether the index column is run-compressed (`Cols` with index-major runs).
    /// Field-layout-independent accessor; false for the adaptive representation.
    pub open spec fn is_runs_idx(&self) -> bool {
        self is Cols && self->Cols_idxs is Runs
    }

    /// Whether this is the per-frame-adaptive representation.
    pub open spec fn is_adaptive(&self) -> bool {
        self is Adaptive
    }

    /// Length of the index column's cold (already-folded) prefix (`Cols`), or the
    /// adaptive cold tier's length.
    pub open spec fn idx_cold_len_spec(&self) -> nat {
        match self {
            DiffLog::Cols { idxs, .. } => idxs.cold_len_spec(),
            DiffLog::Adaptive { cold, .. } => cold_adaptive(cold@).len(),
        }
    }

    /// A fresh empty plain log (the `None` / SMT representation).
    pub fn new_plain() -> (r: DiffLog<T, I, VC>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog::Cols { idxs: DiffIdxs::Plain(Vec::new()), vals: DiffVals::Plain(Vec::new()) };
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// A fresh empty value-major log (the `ValueDict` representation): no cold
    /// frames yet, empty hot tail. Index column stays plain.
    pub fn new_dict() -> (r: DiffLog<T, I, VC>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog::Cols {
            idxs: DiffIdxs::Plain(Vec::new()),
            vals: DiffVals::Dict { cold: Vec::new(), tail: Vec::new() },
        };
        proof { reveal(cold_vals); }
        assert(cold_vals(Seq::<ValFrame<T>>::empty()) =~= Seq::<T>::empty());
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// A fresh empty index-major log (the `IndexRuns` representation): no cold index
    /// frames yet, empty hot index tail; value column stays plain.
    pub fn new_runs() -> (r: DiffLog<T, I, VC>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog::Cols {
            idxs: DiffIdxs::Runs { cold: Vec::new(), tail: Vec::new() },
            vals: DiffVals::Plain(Vec::new()),
        };
        proof { reveal(cold_idxs); }
        assert(cold_idxs(Seq::<RunCol<(), I>>::empty()) =~= Seq::<I>::empty());
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// A fresh empty per-frame-adaptive log (the `Auto` representation): no cold
    /// frames, empty hot pair tail, cached length 0.
    pub fn new_adaptive() -> (r: DiffLog<T, I, VC>)
        ensures r.wf(), r@ == Seq::<(T, I)>::empty(),
    {
        let r = DiffLog::Adaptive { cold: Vec::new(), hot: Vec::new(), len: 0 };
        proof { reveal(cold_adaptive); }
        assert(cold_adaptive(Seq::<ColdFrame<T, I, VC>>::empty()) =~= Seq::<(T, I)>::empty());
        assert(r@ =~= Seq::<(T, I)>::empty());
        r
    }

    /// Number of entries. Reads whichever column is plain (at most one compresses).
    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self@.len(),
    {
        match self {
            DiffLog::Cols { idxs, vals } => {
                match idxs {
                    DiffIdxs::Plain(v) => v.len(),
                    DiffIdxs::Runs { .. } => match vals {
                        DiffVals::Plain(vv) => vv.len(),
                        // Unreachable: wf gives idxs is Runs ==> vals is Plain.
                        DiffVals::Dict { .. } => { assert(false); 0 }
                    },
                }
            }
            DiffLog::Adaptive { len, .. } => *len,
        }
    }

    /// Materialize the index column of entries `[lo, hi)` as an owned `Vec<I>` (the
    /// `.1` projection of `@[lo..hi]`). The A2 plumbing: the capture machinery needs
    /// only the active/restored frame's indices, so the caller materializes that
    /// range instead of borrowing a whole contiguous `idxs` slice. That lets a future
    /// index-major representation DROP the stored index column (reconstructing it from
    /// runs here) without changing the `DiffStore` capture interface. For the current
    /// (idxs-whole) representation it is a range copy.
    /// Borrow the index column of `[lo, hi)` WITHOUT materializing it, when
    /// the representation stores indices contiguously (`Cols`/`Plain`, which
    /// is every uncompressed column). `None` when the indices are encoded
    /// (run columns, adaptive frames) and must be rebuilt, in which case the
    /// caller falls back to `index_range`.
    ///
    /// This exists because `Vec::push_frame` needs the open stratum's index
    /// column on EVERY mark to drive the sparse flag clear, and materializing
    /// it costs one allocation plus an O(stratum) copy per column per mark -
    /// measured as the dominant term of mark's cost at 46 columns, and a
    /// contributor to the allocator churn (about 10%) in the backtrack-heavy
    /// SMT profile.
    pub fn index_slice(&self, lo: usize, hi: usize) -> (r: Option<&[I]>)
        requires self.wf(), lo <= hi <= self@.len(),
        ensures
            r matches Some(sl) ==> sl@.len() == hi - lo
                && forall|k: int| 0 <= k < hi - lo ==> #[trigger] sl@[k] == self@[lo + k].1,
    {
        match self {
            DiffLog::Cols { idxs, vals } => {
                match idxs {
                    DiffIdxs::Plain(v) => {
                        proof {
                            assert(forall|k: int| 0 <= k < hi - lo
                                ==> #[trigger] v@[lo + k] == self@[lo + k].1);
                        }
                        let sl = vstd::slice::slice_subrange(v.as_slice(), lo, hi);
                        Some(sl)
                    }
                    DiffIdxs::Runs { .. } => None,
                }
            }
            DiffLog::Adaptive { .. } => None,
        }
    }

    pub fn index_range(&self, lo: usize, hi: usize) -> (r: Vec<I>)
        requires self.wf(), lo <= hi <= self@.len(),
        ensures
            r@.len() == hi - lo,
            forall|k: int| 0 <= k < hi - lo ==> #[trigger] r@[k] == self@[lo + k].1,
    {
        // Adaptive: one frame-wise pass (subrange_vec's fast path), then project.
        // Without this every entry pays an O(cold frames) locate walk.
        if let DiffLog::Adaptive { .. } = self {
            let pairs = self.subrange_vec(lo, hi);
            let mut out: Vec<I> = Vec::new();
            let n = pairs.len();
            let mut k: usize = 0;
            while k < n
                invariant
                    0 <= k <= n,
                    n == pairs@.len(),
                    pairs@ == self@.subrange(lo as int, hi as int),
                    hi <= self@.len(),
                    lo <= hi,
                    out@.len() == k,
                    forall|j: int| 0 <= j < k ==> #[trigger] out@[j] == self@[lo + j].1,
                decreases n - k,
            {
                proof {
                    assert(pairs@[k as int] == self@[lo + k]);
                }
                out.push(pairs[k].1);
                k += 1;
            }
            return out;
        }
        let mut out: Vec<I> = Vec::new();
        let mut i: usize = lo;
        while i < hi
            invariant
                lo <= i <= hi, hi <= self@.len(), self.wf(),
                out@.len() == i - lo,
                forall|k: int| 0 <= k < i - lo ==> #[trigger] out@[k] == self@[lo + k].1,
            decreases hi - i,
        {
            out.push(self.index(i).1);
            i += 1;
        }
        out
    }

    /// Diagnostic heap footprint (capacity-based; no spec content).
    #[verifier::external_body]
    pub fn heap_bytes(&self) -> usize {
        match self {
            DiffLog::Cols { idxs, vals } => {
                let vbytes = match vals {
                    DiffVals::Plain(v) => v.capacity() * core::mem::size_of::<T>(),
                    DiffVals::Dict { cold, tail } => {
                        let mut b = tail.capacity() * core::mem::size_of::<T>();
                        for f in cold.iter() {
                            b += f.byte_len();
                        }
                        b
                    }
                };
                let ibytes = match idxs {
                    DiffIdxs::Plain(v) => v.capacity() * core::mem::size_of::<I>(),
                    DiffIdxs::Runs { cold, tail } => {
                        let mut b = tail.capacity() * core::mem::size_of::<I>();
                        for f in cold.iter() {
                            b += f.byte_len();
                        }
                        b
                    }
                };
                ibytes + vbytes
            }
            DiffLog::Adaptive { cold, hot, .. } => {
                let mut b = hot.capacity() * (core::mem::size_of::<T>() + core::mem::size_of::<I>());
                for f in cold.iter() {
                    b += f.byte_len();
                }
                b
            }
        }
    }

    /// Entry `i` = `(value, index)`. Cold reads walk the frames to locate `i`
    /// (O(cold frames); a `starts` offset array would make it O(log), a noted
    /// follow-up); tail reads are O(1).
    pub fn index(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self@.len(),
        ensures e == self@[i as int],
    {
        match self {
            DiffLog::Cols { idxs, vals } => {
                let idx = idxs.idx_at_exec(i);
                let total = self.len();
                match vals {
                    DiffVals::Plain(v) => (v[i], idx),
                    DiffVals::Dict { cold, tail } => {
                        let tl = tail.len();
                        proof { reveal(cold_vals); }
                        assert(vals.len_spec() == total);
                        let cold_len = total - tl;
                        assert(cold_len == cold_vals(cold@).len());
                        if i < cold_len {
                            let clen = cold.len();
                            let mut d: usize = i;
                            let mut k: usize = 0;
                            while cold[k].len() <= d
                                invariant
                                    0 <= k <= cold@.len(),
                                    k < cold@.len(),
                                    cold@.len() == clen,
                                    forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                                    i == d + cold_vals(cold@.subrange(0, k as int)).len(),
                                    i < cold_vals(cold@).len(),
                                decreases cold@.len() - k,
                            {
                                let flen = cold[k].len();
                                proof {
                                    assert(flen == cold@[k as int].decode().len());
                                    assert(cold@.subrange(0, k + 1)
                                        =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                                    lemma_cold_vals_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                                    assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len()
                                        == cold_vals(cold@.subrange(0, k as int)).len() + flen);
                                    assert(flen <= d);
                                    assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len() <= i);
                                    assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                                    assert(k + 1 < cold@.len());
                                }
                                d = d - flen;
                                k = k + 1;
                            }
                            proof { lemma_cold_vals_at(cold@, k as int, i as int); }
                            (cold[k].decode_at(d), idx)
                        } else {
                            (tail[i - cold_len], idx)
                        }
                    }
                }
            }
            DiffLog::Adaptive { cold, hot, .. } => {
                proof { reveal(cold_adaptive); }
                let mut d: usize = i;
                let mut k: usize = 0;
                while k < cold.len() && cold[k].entry_len() <= d
                    invariant
                        0 <= k <= cold@.len(),
                        forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                        i == d + cold_adaptive(cold@.subrange(0, k as int)).len(),
                        i < adaptive_len(cold@, hot@),
                    decreases cold@.len() - k,
                {
                    let flen = cold[k].entry_len();
                    proof {
                        assert(flen == cold@[k as int].decode().len());
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_adaptive_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        assert(cold_adaptive(cold@.subrange(0, (k + 1) as int)).len()
                            == cold_adaptive(cold@.subrange(0, k as int)).len() + flen);
                    }
                    d = d - flen;
                    k = k + 1;
                }
                if k < cold.len() {
                    proof {
                        lemma_cold_adaptive_split(cold@, (k + 1) as int);
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_adaptive_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        assert(i < cold_adaptive(cold@).len());
                        lemma_cold_adaptive_at(cold@, k as int, i as int);
                    }
                    cold[k].decode_at(d)
                } else {
                    proof { assert(cold@.subrange(0, k as int) =~= cold@); }
                    hot[d]
                }
            }
        }
    }

    /// Append `(t, idx)`. Preserves the prefix, extends the view by one.
    pub fn push(&mut self, t: T, idx: I)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@.push((t, idx)),
    {
        match self {
            DiffLog::Cols { idxs, vals } => {
                idxs.push_idx(idx);
                match vals {
                    DiffVals::Plain(v) => v.push(t),
                    DiffVals::Dict { tail, .. } => tail.push(t),
                }
                assert(self@ =~= old(self)@.push((t, idx)));
            }
            DiffLog::Adaptive { cold, hot, len } => {
                hot.push((t, idx));
                // `hot` just grew by one within `usize`, and `len == cold_adaptive + hot`;
                // recompute from the fresh `hot.len()` so no separate counter overflows.
                *len = adaptive_len_exec(cold, hot);
                assert(self@ =~= old(self)@.push((t, idx)));
            }
        }
    }

    /// Fold the hot tail into one new immutable cold frame (value-major only;
    /// no-op for plain). Called at mark to finalize a frame. Preserves the view:
    /// the new cold frame decodes to exactly the old tail, so `cold_vals` grows by
    /// the tail and the tail empties. Amortized O(frame).
    pub fn compact_tail(&mut self)
        where T: IndexLike
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        match self {
            DiffLog::Cols { idxs, vals } => {
                // Index-major fold: coalesce the hot index tail into one immutable cold
                // RunCol frame, dropping the stored index column to run starts.
                match idxs {
                    DiffIdxs::Plain(_) => {}
                    DiffIdxs::Runs { cold, tail } => {
                        let ghost cold0 = cold@;
                        let ghost tail0 = tail@;
                        let mut pairs: Vec<((), I)> = Vec::new();
                        let mut j: usize = 0;
                        while j < tail.len()
                            invariant
                                0 <= j <= tail@.len(),
                                pairs@.len() == j,
                                forall|k: int| 0 <= k < j ==> #[trigger] pairs@[k] == ((), tail@[k]),
                            decreases tail@.len() - j,
                        {
                            pairs.push(((), tail[j]));
                            j += 1;
                        }
                        let f: RunCol<(), I> = RunCol::compress(&pairs);
                        let ghost fg = f;
                        proof {
                            assert(f.idx_seq() =~= tail0);
                            lemma_cold_idxs_snoc(cold0, fg);
                        }
                        cold.push(f);
                        *tail = Vec::new();
                        proof {
                            assert(cold@ =~= cold0.push(fg));
                            assert(cold_idxs(cold@) =~= cold_idxs(cold0) + tail0);
                        }
                    }
                }
                // Value-major fold: coalesce the hot value tail into one cold frame.
                match vals {
                    DiffVals::Plain(_) => {}
                    DiffVals::Dict { cold, tail } => {
                        let ghost cold0 = cold@;
                        let ghost tail0 = tail@;
                        let f = ValFrame::compress(tail);
                        let ghost fg = f;
                        proof { lemma_cold_vals_snoc(cold0, fg); }
                        cold.push(f);
                        *tail = Vec::new();
                        proof {
                            assert(cold@ =~= cold0.push(fg));
                            assert(cold_vals(cold@) =~= cold_vals(cold0) + tail0);
                        }
                    }
                }
            }
            // Adaptive: no write-order fold here (its mark path is mark_and_compact_adaptive);
            // a no-op preserves the view.
            DiffLog::Adaptive { .. } => {}
        }
        assert(self@ =~= old(self)@);
    }

    /// Sorted index-major fold (A3): sort the just-closed frame's `(value, index)`
    /// pairs by index, write the sorted values back into the plain value tail, and
    /// fold the sorted (now maximally coalescible) indices into one cold `RunCol`
    /// frame. This PERMUTES `@` within the tail region `[cold_len, n)`; that region's
    /// write multiset is preserved (sorting is a permutation), which is exactly what
    /// the Vec multiset model consumes. Requires the index column run-compressed and
    /// the value column plain (index-major keeps values plain).
    pub fn compact_tail_sorted(&mut self)
        where T: Copy
        requires
            old(self).wf(),
            old(self).is_runs_idx(),
            // The just-closed frame (the tail region) has unique indices
            // (first-write-wins), which makes the sort sound and stays true after it.
            crate::diff_compress::unique_idx(old(self)@.subrange(
                old(self).idx_cold_len_spec() as int, old(self)@.len() as int)),
        ensures
            final(self).wf(),
            final(self).is_runs_idx(),
            final(self)@.len() == old(self)@.len(),
            // Whole tail folded into cold: the cold region now covers the log.
            final(self).idx_cold_len_spec() == final(self)@.len(),
            final(self)@.subrange(0, old(self).idx_cold_len_spec() as int)
                == old(self)@.subrange(0, old(self).idx_cold_len_spec() as int),
            final(self)@.subrange(
                old(self).idx_cold_len_spec() as int, final(self)@.len() as int).to_multiset()
                == old(self)@.subrange(
                    old(self).idx_cold_len_spec() as int, old(self)@.len() as int).to_multiset(),
            // The reordered region stays unique-indexed (sort preserves it), so the
            // Vec's frame_inv_range uniqueness carries for the permuted stratum.
            crate::diff_compress::unique_idx(final(self)@.subrange(
                old(self).idx_cold_len_spec() as int, final(self)@.len() as int)),
    {
        proof { reveal(cold_idxs); }
        let ghost n: int = self@.len() as int;
        let ghost ts: int = self.idx_cold_len_spec() as int;
        match self {
            DiffLog::Cols { idxs: DiffIdxs::Runs { cold, tail }, vals: DiffVals::Plain(vals) } => {
                let ghost cold0 = cold@;
                let ghost vals0 = vals@;
                let ghost tail0 = tail@;
                let tl = tail.len();
                let base = vals.len() - tl;  // == ts == cold_idxs(cold@).len()
                assert(base == ts);
                // Gather the tail's (value, index) pairs in capture order, indexing
                // the value column absolutely (i = base + q) to avoid an overflow check.
                let mut pairs: Vec<(T, I)> = Vec::new();
                let vlen = vals.len();
                let mut i: usize = base;
                while i < vlen
                    invariant
                        base <= i <= vlen,
                        vlen == vals@.len(),
                        tl == tail@.len(),
                        base + tl == vals@.len(),
                        vals@ == vals0,
                        tail@ == tail0,
                        pairs@.len() == i - base,
                        forall|q: int| 0 <= q < i - base ==>
                            #[trigger] pairs@[q] == (vals0[base + q], tail0[q]),
                    decreases vlen - i,
                {
                    pairs.push((vals[i], tail[i - base]));
                    i += 1;
                }
                assert(pairs@ =~= Seq::new(tl as nat, |q: int| (vals0[base + q], tail0[q])));
                // Sort by index (multiset-preserving permutation).
                let sorted = sort_frame_by_index(&pairs);
                assert(sorted@.to_multiset() == pairs@.to_multiset());
                // Write sorted values back into the plain value tail (absolute index).
                let mut iw: usize = base;
                while iw < vlen
                    invariant
                        base <= iw <= vlen,
                        vlen == vals@.len(),
                        sorted@.len() == tl,
                        base + tl == vals@.len(),
                        forall|q: int| 0 <= q < iw - base ==> #[trigger] vals@[base + q] == sorted@[q].0,
                        forall|q: int| 0 <= q < base ==> #[trigger] vals@[q] == vals0[q],
                        forall|q: int| iw - base <= q < tl ==> #[trigger] vals@[base + q] == vals0[base + q],
                    decreases vlen - iw,
                {
                    vals.set(iw, sorted[iw - base].0);
                    iw += 1;
                }
                // Fold the sorted indices into one cold RunCol frame ((),index pairs).
                let mut idx_pairs: Vec<((), I)> = Vec::new();
                let mut p: usize = 0;
                while p < tl
                    invariant
                        0 <= p <= tl,
                        sorted@.len() == tl,
                        idx_pairs@.len() == p,
                        forall|q: int| 0 <= q < p ==> #[trigger] idx_pairs@[q] == ((), sorted@[q].1),
                    decreases tl - p,
                {
                    idx_pairs.push(((), sorted[p].1));
                    p += 1;
                }
                assert(idx_pairs@ =~= Seq::new(tl as nat, |q: int| ((), sorted@[q].1)));
                let f: RunCol<(), I> = RunCol::compress(&idx_pairs);
                let ghost fg = f;
                proof {
                    // f.idx_seq() == the sorted index column.
                    assert(f.idx_seq() =~= Seq::new(tl as nat, |q: int| sorted@[q].1));
                    lemma_cold_idxs_snoc(cold0, fg);
                }
                cold.push(f);
                *tail = Vec::new();
                proof {
                    assert(cold@ =~= cold0.push(fg));
                    assert(cold_idxs(cold@) =~= cold_idxs(cold0) + fg.idx_seq());
                    let idxseq = fg.idx_seq();
                    // cold_idxs is unchanged below ts and equals the sorted indices above.
                    assert forall|i: int| #![auto] 0 <= i < ts implies
                        cold_idxs(cold@)[i] == cold_idxs(cold0)[i] by {}
                    assert forall|q: int| #![auto] 0 <= q < tl implies
                        cold_idxs(cold@)[ts + q] == sorted@[q].1 by {
                        assert(cold_idxs(cold@)[ts + q] == idxseq[q]);
                    }
                    // Prefix [0, ts) of the view is untouched.
                    assert(self@.subrange(0, ts) =~= old(self)@.subrange(0, ts)) by {
                        assert forall|i: int| 0 <= i < ts implies
                            self@[i] == old(self)@[i] by {}
                    }
                    // Region [ts, n): new view == sorted, old view == pairs (capture order).
                    assert(self@.subrange(ts, n) =~= sorted@) by {
                        assert forall|q: int| 0 <= q < tl implies
                            self@[ts + q] == sorted@[q] by {}
                    }
                    assert(old(self)@.subrange(ts, n) =~= pairs@) by {
                        assert forall|q: int| 0 <= q < tl implies
                            old(self)@[ts + q] == pairs@[q] by {}
                    }
                    assert(self@.subrange(ts, n).to_multiset()
                        == old(self)@.subrange(ts, n).to_multiset());
                    // Uniqueness carries: old region == pairs (unique by requires),
                    // sort preserves unique, new region == sorted.
                    assert(crate::diff_compress::unique_idx(pairs@));
                    assert(crate::diff_compress::unique_idx(sorted@));
                    assert(crate::diff_compress::unique_idx(self@.subrange(ts, n)));
                }
            }
            _ => {
                // Unreachable: requires idxs is Runs, and wf gives vals is Plain then.
                assert(false);
            }
        }
    }

    /// Per-frame-adaptive fold (A4): fold the hot pair tail into one cold `ColdFrame`
    /// in the given per-frame mode. Every mode preserves the folded region's write
    /// multiset (and, given unique input indices, its uniqueness); sorted modes permute
    /// it. Same shape as `compact_tail_sorted` (permutes `[cold_len, n)`), so the Vec
    /// lifts it with `lemma_diff_log_rep_change_preserves_wf_multiset`.
    pub fn compact_adaptive(&mut self, mode: CompressionMode)
        where T: IndexLike
        requires
            old(self).wf(),
            old(self).is_adaptive(),
            crate::diff_compress::unique_idx(old(self)@.subrange(
                old(self).idx_cold_len_spec() as int, old(self)@.len() as int)),
        ensures
            final(self).wf(),
            final(self).is_adaptive(),
            final(self)@.len() == old(self)@.len(),
            final(self).idx_cold_len_spec() == final(self)@.len(),
            final(self)@.subrange(0, old(self).idx_cold_len_spec() as int)
                == old(self)@.subrange(0, old(self).idx_cold_len_spec() as int),
            final(self)@.subrange(
                old(self).idx_cold_len_spec() as int, final(self)@.len() as int).to_multiset()
                == old(self)@.subrange(
                    old(self).idx_cold_len_spec() as int, old(self)@.len() as int).to_multiset(),
            crate::diff_compress::unique_idx(final(self)@.subrange(
                old(self).idx_cold_len_spec() as int, final(self)@.len() as int)),
    {
        proof { reveal(cold_adaptive); }
        let key = self.shadow_key();
        let ghost cold_len = self.idx_cold_len_spec() as int;
        let ghost n = self@.len() as int;
        match self {
            DiffLog::Adaptive { cold, hot, len: lenf } => {
                let ghost cold0 = cold@;
                let ghost hot0 = hot@;
                if crate::compression_stats::shadow_enabled() {
                    crate::compression_stats::shadow_log_full::<T, I, VC>(
                        hot, key, cold.len(), crate::compression_stats::mode_name(mode));
                }
                // The hot tail IS the frame's (value, index) pairs; encode in `mode`.
                let f: ColdFrame<T, I, VC> = ColdFrame::compress_mode(hot, mode);
                let ghost fg = f;
                proof {
                    broadcast use vstd::seq_lib::group_to_multiset_ensures;
                    lemma_cold_adaptive_snoc(cold0, fg);
                }
                cold.push(f);
                *hot = Vec::new();
                *lenf = adaptive_len_exec(cold, hot);
                proof {
                    broadcast use vstd::seq_lib::group_to_multiset_ensures;
                    assert(cold@ =~= cold0.push(fg));
                    assert(cold_adaptive(cold@) =~= cold_adaptive(cold0) + fg.decode());
                    // fg.decode() has hot0's multiset ⇒ same length.
                    assert(fg.decode().to_multiset() == hot0.to_multiset());
                    assert(fg.decode().to_multiset().len() == hot0.to_multiset().len());
                    assert(fg.decode().len() == hot0.len());
                    // cold_len == cold_adaptive(cold0).len(); region [cold_len, n) is
                    // fg.decode() (new) vs hot0 (old), same multiset; prefix untouched.
                    assert(cold_len == cold_adaptive(cold0).len());
                    assert(self@.len() == n);
                    // cold_adaptive(cold@) == cold_adaptive(cold0) + fg.decode(), so its
                    // length-`cold_len` prefix is cold_adaptive(cold0) unchanged.
                    assert(self@.subrange(0, cold_len) =~= old(self)@.subrange(0, cold_len)) by {
                        assert forall|i: int| 0 <= i < cold_len implies
                            self@[i] == old(self)@[i] by {}
                    }
                    assert(self@.subrange(cold_len, n) =~= fg.decode()) by {
                        assert forall|q: int| 0 <= q < fg.decode().len() implies
                            self@[cold_len + q] == fg.decode()[q] by {}
                    }
                    assert(old(self)@.subrange(cold_len, n) =~= hot0) by {
                        assert forall|q: int| 0 <= q < hot0.len() implies
                            old(self)@[cold_len + q] == hot0[q] by {}
                    }
                }
            }
            DiffLog::Cols { .. } => { proof { assert(false); } }
        }
    }

    /// As `compact_adaptive`, but restricted to the value-opaque modes so it needs
    /// only `T: Copy`: every column (structs included) can seal per-frame with
    /// plain / index runs / sorted runs, with the encoder's self-demotion to plain
    /// when runs do not pay. The dictionary modes stay on the `T: IndexLike` entry.
    /// (Body mirrors `compact_adaptive` with the copy-bounded encoder; the shared
    /// seal-with-frame factoring is a noted follow-up.)
    pub fn compact_adaptive_copy(&mut self, mode: CompressionMode)
        requires
            old(self).wf(),
            old(self).is_adaptive(),
            crate::diff_compress::unique_idx(old(self)@.subrange(
                old(self).idx_cold_len_spec() as int, old(self)@.len() as int)),
        ensures
            final(self).wf(),
            final(self).is_adaptive(),
            final(self)@.len() == old(self)@.len(),
            final(self).idx_cold_len_spec() == final(self)@.len(),
            final(self)@.subrange(0, old(self).idx_cold_len_spec() as int)
                == old(self)@.subrange(0, old(self).idx_cold_len_spec() as int),
            final(self)@.subrange(
                old(self).idx_cold_len_spec() as int, final(self)@.len() as int).to_multiset()
                == old(self)@.subrange(
                    old(self).idx_cold_len_spec() as int, old(self)@.len() as int).to_multiset(),
            crate::diff_compress::unique_idx(final(self)@.subrange(
                old(self).idx_cold_len_spec() as int, final(self)@.len() as int)),
    {
        proof { reveal(cold_adaptive); }
        let key = self.shadow_key();
        let ghost cold_len = self.idx_cold_len_spec() as int;
        let ghost n = self@.len() as int;
        match self {
            DiffLog::Adaptive { cold, hot, len: lenf } => {
                let ghost cold0 = cold@;
                let ghost hot0 = hot@;
                if crate::compression_stats::shadow_enabled() {
                    crate::compression_stats::shadow_log_copy::<T, I, VC>(
                        hot, key, cold.len(), crate::compression_stats::mode_name(mode));
                }
                let f: ColdFrame<T, I, VC> = ColdFrame::compress_mode_copy(hot, mode);
                let ghost fg = f;
                proof {
                    broadcast use vstd::seq_lib::group_to_multiset_ensures;
                    lemma_cold_adaptive_snoc(cold0, fg);
                }
                cold.push(f);
                *hot = Vec::new();
                *lenf = adaptive_len_exec(cold, hot);
                proof {
                    broadcast use vstd::seq_lib::group_to_multiset_ensures;
                    assert(cold@ =~= cold0.push(fg));
                    assert(cold_adaptive(cold@) =~= cold_adaptive(cold0) + fg.decode());
                    assert(fg.decode().to_multiset() == hot0.to_multiset());
                    assert(fg.decode().to_multiset().len() == hot0.to_multiset().len());
                    assert(fg.decode().len() == hot0.len());
                    assert(cold_len == cold_adaptive(cold0).len());
                    assert(self@.len() == n);
                    assert(self@.subrange(0, cold_len) =~= old(self)@.subrange(0, cold_len)) by {
                        assert forall|i: int| 0 <= i < cold_len implies
                            self@[i] == old(self)@[i] by {}
                    }
                    assert(self@.subrange(cold_len, n) =~= fg.decode()) by {
                        assert forall|q: int| 0 <= q < fg.decode().len() implies
                            self@[cold_len + q] == fg.decode()[q] by {}
                    }
                    assert(old(self)@.subrange(cold_len, n) =~= hot0) by {
                        assert forall|q: int| 0 <= q < hot0.len() implies
                            old(self)@[cold_len + q] == hot0[q] by {}
                    }
                }
            }
            DiffLog::Cols { .. } => { proof { assert(false); } }
        }
    }

    /// Capacity-only shrink (production parity). Observably inert. Shrinks the
    /// mutable columns (idxs, plain values, hot tail); cold frames are already
    /// tightly sized by `compress`.
    pub fn shrink_capacity(&mut self, factor: usize, headroom: usize)
        requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@,
    {
        match self {
            DiffLog::Cols { idxs, vals } => {
                match idxs {
                    DiffIdxs::Plain(v) =>
                        crate::parallel_store::shrink_vec_capacity(v, factor, headroom),
                    DiffIdxs::Runs { tail, .. } =>
                        crate::parallel_store::shrink_vec_capacity(tail, factor, headroom),
                }
                match vals {
                    DiffVals::Plain(v) =>
                        crate::parallel_store::shrink_vec_capacity(v, factor, headroom),
                    DiffVals::Dict { tail, .. } =>
                        crate::parallel_store::shrink_vec_capacity(tail, factor, headroom),
                }
            }
            DiffLog::Adaptive { hot, .. } =>
                crate::parallel_store::shrink_vec_capacity(hot, factor, headroom),
        }
        assert(self@ =~= old(self)@);
    }

    /// Materialize entries `[lo, hi)` as a flat `Vec<(T, I)>`.
    /// Opaque column-instance key for the shadow harness (the log's address).
    #[verifier::external_body]
    pub fn shadow_key(&self) -> usize {
        self as *const _ as usize
    }

    /// Diagnostic: number of sealed (cold) frames, whichever representation.
    #[verifier::external_body]
    pub fn cold_frame_count(&self) -> usize {
        match self {
            DiffLog::Cols { idxs, vals } => {
                let a = match idxs { DiffIdxs::Runs { cold, .. } => cold.len(), _ => 0 };
                let b = match vals { DiffVals::Dict { cold, .. } => cold.len(), _ => 0 };
                if a > b { a } else { b }
            }
            DiffLog::Adaptive { cold, .. } => cold.len(),
        }
    }

    /// Exec probe for the adaptive fast-fold preconditions: is this the adaptive
    /// representation with its cold tier ending exactly at `ds` (the open frame's
    /// start)? A `seal` entry branches on this at runtime and falls back to the
    /// plain fold when it does not hold, so no caller carries the alignment as a
    /// precondition.
    pub fn adaptive_aligned(&self, ds: usize) -> (b: bool)
        requires self.wf(),
        ensures b == (self.is_adaptive() && self.idx_cold_len_spec() == ds),
    {
        match self {
            DiffLog::Cols { .. } => false,
            DiffLog::Adaptive { hot, len, .. } => {
                proof { reveal(cold_adaptive); }
                *len - hot.len() == ds
            }
        }
    }

    /// Backward scattered replay of `[lo, hi)` onto `target` (the `overlay` model,
    /// entry by entry through `index`). The generic baseline every representation
    /// can use; the fast paths in `restore_range_into` replace it frame-wise.
    pub fn restore_scatter(&self, lo: usize, hi: usize, target: &mut Vec<T>)
        requires
            self.wf(),
            lo <= hi <= self@.len(),
        ensures
            final(target)@ == crate::vec::overlay::<T, I>(
                old(target)@, self@, lo as int, hi as int),
    {
        let ghost base = target@;
        let mut i: usize = hi;
        while i > lo
            invariant
                lo <= i <= hi,
                hi <= self@.len(),
                self.wf(),
                target@.len() == base.len(),
                target@ == crate::vec::overlay::<T, I>(base, self@, i as int, hi as int),
            decreases i,
        {
            i -= 1;
            let (v, idx) = self.index(i);
            proof {
                crate::vec::lemma_overlay_len::<T, I>(base, self@, (i + 1) as int, hi as int);
            }
            let iu = idx.as_usize();
            if iu < target.len() {
                target.set(iu, v);
            }
            proof {
                assert(target@ =~= crate::vec::overlay::<T, I>(
                    base, self@, i as int, hi as int));
            }
        }
    }

    /// Apply the range `[lo, hi)` onto `target` under the `overlay` model, using the
    /// frame-wise fast path where the representation allows it: for the adaptive
    /// tier, each whole cold frame inside the range restores itself via
    /// `restore_to` (a sliced memcpy for `Runs` frames), sound because a sealed
    /// frame has unique indices so forward and backward application agree
    /// (`lemma_apply_all_eq_overlay`); the hot region and any partial frame fall
    /// back to the scattered baseline.
    pub fn restore_range_into(&self, lo: usize, hi: usize, target: &mut Vec<T>)
        requires
            self.wf(),
            lo <= hi <= self@.len(),
        ensures
            final(target)@ == crate::vec::overlay::<T, I>(
                old(target)@, self@, lo as int, hi as int),
    {
        match self {
            DiffLog::Cols { .. } => {
                self.restore_scatter(lo, hi, target);
            }
            DiffLog::Adaptive { cold, hot, len } => {
                // The fast path decomposes a SUFFIX [lo, len) frame by frame; a
                // proper sub-suffix (hi < len) only arises off the restore path, so
                // it takes the scattered baseline.
                if hi < *len {
                    self.restore_scatter(lo, hi, target);
                    return;
                }
                proof { reveal(cold_adaptive); }
                let ghost base = target@;
                let ghost d = self@;
                let cold_total = *len - hot.len();
                assert(cold_total == cold_adaptive(cold@).len());
                // 1. Hot region: scattered (small, and its uniqueness is not in wf).
                let hot_lo = if lo > cold_total { lo } else { cold_total };
                self.restore_scatter(hot_lo, hi, target);
                proof {
                    crate::vec::lemma_overlay_len::<T, I>(base, d, hot_lo as int, hi as int);
                }
                if lo >= cold_total {
                    return;
                }
                // 2. Cold frames from the last down: each whole frame inside the
                //    range applies itself (memcpy for Runs); a partial frame at the
                //    bottom falls back to scattered.
                let mut end: usize = cold_total;
                let mut k: usize = cold.len();
                proof {
                    assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                }
                while k > 0 && end > lo
                    invariant
                        self.wf(),
                        self is Adaptive,
                        base == old(target)@,
                        cold@ == self->Adaptive_cold@,
                        hot@ == self->Adaptive_hot@,
                        hi <= d.len(),
                        d == self@,
                        hi as int == d.len(),
                        0 <= k <= cold@.len(),
                        lo < cold_total,
                        cold_total == cold_adaptive(cold@).len(),
                        cold_total <= hi,
                        end as int == cold_adaptive(cold@.subrange(0, k as int)).len(),
                        end <= cold_total,
                        target@.len() == base.len(),
                        target@ == crate::vec::overlay::<T, I>(
                            base, d, if end > lo { end as int } else { lo as int }, hi as int),
                    decreases k,
                {
                    proof {
                        // Link the match binding back to self so wf's per-frame
                        // foralls (frame wf + unique indices) instantiate on it.
                        assert(self->Adaptive_cold@ == cold@);
                        assert(cold@[(k - 1) as int].wf());
                        assert(crate::diff_compress::unique_idx(
                            cold@[(k - 1) as int].decode()));
                    }
                    let flen = cold[k - 1].entry_len();
                    proof {
                        assert(cold@.subrange(0, k as int)
                            =~= cold@.subrange(0, (k - 1) as int).push(cold@[(k - 1) as int]));
                        lemma_cold_adaptive_snoc(
                            cold@.subrange(0, (k - 1) as int), cold@[(k - 1) as int]);
                    }
                    let start = end - flen;
                    if start >= lo {
                        // Whole frame inside the range: frame-wise application.
                        let ghost fr = cold@[(k - 1) as int];
                        proof {
                            // Prefix length below this frame is exactly `start`.
                            assert(cold_adaptive(cold@.subrange(0, (k - 1) as int)).len()
                                == start as nat);
                            // d[start, end) IS this frame's decode: each position maps
                            // through the view into the cold concatenation at this
                            // frame's offset.
                            assert forall|q: int| 0 <= q < flen implies
                                d[start + q] == fr.decode()[q] by {
                                lemma_cold_adaptive_at(cold@, (k - 1) as int, start + q);
                                assert(cold_adaptive(cold@)[start + q] == fr.decode()[q]);
                                assert(start + q < cold_adaptive(cold@).len());
                                assert(d[start + q]
                                    == adaptive_at(cold@, hot@, start + q));
                            }
                            assert(d.subrange(start as int, end as int) =~= fr.decode());
                            // unique indices (wf) => forward == backward application.
                            assert(crate::diff_compress::unique_idx(fr.decode()));
                            assert(crate::diff_compress::unique_idx(
                                d.subrange(start as int, end as int)));
                            crate::vec::lemma_apply_all_eq_overlay::<T, I>(
                                target@, d, start as int, end as int);
                            // Peel this frame off the overlay via the split lemma.
                            crate::vec::lemma_overlay_split::<T, I>(
                                base, d, start as int, end as int, hi as int);
                        }
                        cold[k - 1].restore_to(target);
                        proof {
                            assert(target@ == crate::vec::overlay::<T, I>(
                                base, d, start as int, hi as int));
                            crate::vec::lemma_overlay_len::<T, I>(
                                base, d, start as int, hi as int);
                        }
                        end = start;
                        k -= 1;
                    } else {
                        // Partial frame at the bottom: scattered for [lo, end), done.
                        proof {
                            crate::vec::lemma_overlay_split::<T, I>(
                                base, d, lo as int, end as int, hi as int);
                        }
                        self.restore_scatter(lo, end, target);
                        proof {
                            assert(target@ == crate::vec::overlay::<T, I>(
                                base, d, lo as int, hi as int));
                        }
                        return;
                    }
                }
                proof {
                    // Loop exit: end <= lo, and end steps on frame boundaries with
                    // start >= lo in the taken branch, so end == lo; or k == 0 with
                    // end == 0 <= lo. Either way the overlay range is [lo, hi).
                    if end > lo {
                        assert(k == 0);
                        assert(cold@.subrange(0, 0) =~= Seq::<ColdFrame<T, I, VC>>::empty());
                        assert(end == 0);
                        assert(false);
                    }
                }
            }
        }
    }

    pub fn subrange_vec(&self, lo: usize, hi: usize) -> (r: Vec<(T, I)>)
        requires self.wf(), lo <= hi <= self@.len(),
        ensures r@ == self@.subrange(lo as int, hi as int),
    {
        // Frame-wise fast path for the adaptive representation: without it every
        // entry pays an O(cold frames) locate walk, which was measured dominating
        // both the restore-side materialization and the InlineStore replay.
        if let DiffLog::Adaptive { .. } = self {
            return self.subrange_vec_adaptive(lo, hi);
        }
        let mut out: Vec<(T, I)> = Vec::new();
        let mut i: usize = lo;
        while i < hi
            invariant
                lo <= i <= hi, hi <= self@.len(), self.wf(),
                out@.len() == i - lo,
                forall|k: int| 0 <= k < i - lo ==> out@[k] == self@[lo + k],
            decreases hi - i,
        {
            out.push(self.index(i));
            i += 1;
        }
        assert(out@ =~= self@.subrange(lo as int, hi as int));
        out
    }

    /// The adaptive arm of `subrange_vec`: one forward pass over the frames. Whole
    /// cold frames inside the range decode in one `decode_exec` each; a partial
    /// leading frame decodes per-entry WITHIN that frame; the hot region reads
    /// directly. O(hi - lo + frames) total.
    #[verifier::rlimit(600)]
    #[verifier::spinoff_prover]
    fn subrange_vec_adaptive(&self, lo: usize, hi: usize) -> (r: Vec<(T, I)>)
        requires
            self.wf(),
            self is Adaptive,
            lo <= hi <= self@.len(),
        ensures r@ == self@.subrange(lo as int, hi as int),
    {
        proof { reveal(cold_adaptive); }
        match self {
            DiffLog::Adaptive { cold, hot, len } => {
                let ghost d = self@;
                let mut out: Vec<(T, I)> = Vec::new();
                // `done` is the exclusive end of the emitted range: out == d[lo, done).
                let ghost mut done: int = lo as int;
                let mut start: usize = 0;
                let mut k: usize = 0;
                let nf = cold.len();
                proof {
                    assert(cold@.subrange(0, 0) =~= Seq::<ColdFrame<T, I, VC>>::empty());
                    assert(out@ =~= d.subrange(lo as int, lo as int));
                }
                while k < nf
                    invariant
                        self.wf(),
                        self is Adaptive,
                        cold@ == self->Adaptive_cold@,
                        hot@ == self->Adaptive_hot@,
                        d == self@,
                        lo <= hi <= d.len(),
                        0 <= k <= nf,
                        nf == cold@.len(),
                        start as int == cold_adaptive(cold@.subrange(0, k as int)).len(),
                        start <= cold_adaptive(cold@).len(),
                        // done tracks the frame walk, clamped to [lo, hi].
                        done == if (start as int) < lo as int { lo as int }
                                else if (start as int) < hi as int { start as int }
                                else { hi as int },
                        out@ == d.subrange(lo as int, done),
                    decreases nf - k,
                {
                    proof {
                        assert(cold@[k as int].wf());
                    }
                    let flen = cold[k].entry_len();
                    let ghost fr = cold@[k as int];
                    proof {
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_adaptive_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        lemma_cold_adaptive_split(cold@, (k + 1) as int);
                        assert forall|q: int| 0 <= q < flen implies
                            d[start + q] == fr.decode()[q] by {
                            lemma_cold_adaptive_at(cold@, k as int, start + q);
                            assert(start + q < cold_adaptive(cold@).len());
                        }
                    }
                    let fend = start + flen;
                    if fend <= lo || start >= hi {
                        // Wholly outside the range: skip; done's clamp is unchanged
                        // or already saturated.
                    } else {
                        // Overlaps [lo, hi): emit the in-range slice [s, e) of this frame.
                        let s = lo.saturating_sub(start);
                        let e = if hi < fend { hi - start } else { flen };
                        if s == 0 && e == flen {
                            // Whole frame in range: one bulk decode.
                            let mut dec = cold[k].decode_exec_cold();
                            let ghost pre_out = out@;
                            out.append(&mut dec);
                            proof {
                                assert(out@ =~= pre_out + fr.decode());
                                assert(out@ =~= d.subrange(lo as int, fend as int));
                                done = fend as int;
                            }
                        } else {
                            let mut q: usize = s;
                            proof {
                                assert(done == (start + s) as int);
                            }
                            while q < e
                                invariant
                                    self.wf(),
                                    cold@ == self->Adaptive_cold@,
                                    d == self@,
                                    0 <= k < cold@.len(),
                                    fr == cold@[k as int],
                                    fr.wf(),
                                    s <= q <= e,
                                    lo as int <= (start + q) as int,
                                    e <= flen,
                                    (e as int) + (start as int) <= hi as int || e == flen,
                                    (start + e) as int <= hi as int,
                                    flen == fr.decode().len(),
                                    lo <= hi <= d.len(),
                                    forall|j: int| 0 <= j < flen ==> d[start + j] == fr.decode()[j],
                                    out@ == d.subrange(lo as int, (start + q) as int),
                                decreases e - q,
                            {
                                out.push(cold[k].decode_at(q));
                                proof {
                                    let x = (start + q) as int;
                                    assert(d.subrange(lo as int, x + 1)
                                        =~= d.subrange(lo as int, x).push(d[x]));
                                    assert(out@ =~= d.subrange(lo as int, (start + q + 1) as int));
                                }
                                q = q + 1;
                            }
                            proof {
                                done = (start + e) as int;
                            }
                        }
                    }
                    start = fend;
                    k = k + 1;
                }
                // Hot region: [cold_total, len).
                proof {
                    assert(cold@.subrange(0, nf as int) =~= cold@);
                }
                let cold_total = start;
                let h_lo = if lo > cold_total { lo } else { cold_total };
                proof {
                    // done == clamp(cold_total) == max(lo, min(cold_total, hi));
                    // if hi <= cold_total the range is already complete.
                    if hi as int <= cold_total as int {
                        assert(done == hi as int);
                    } else {
                        assert(done == h_lo as int);
                    }
                }
                if hi <= cold_total {
                    proof { assert(out@ =~= d.subrange(lo as int, hi as int)); }
                    return out;
                }
                let mut i: usize = h_lo;
                while i < hi
                    invariant
                        self.wf(),
                        self is Adaptive,
                        cold@ == self->Adaptive_cold@,
                        hot@ == self->Adaptive_hot@,
                        d == self@,
                        cold_total as int == cold_adaptive(cold@).len(),
                        lo <= hi <= d.len(),
                        cold_total <= h_lo,
                        h_lo <= i,
                        i <= hi || i == h_lo,
                        i >= cold_total,
                        out@ == d.subrange(lo as int, i as int),
                        lo as int <= i as int,
                    decreases hi - i,
                {
                    proof {
                        // The view's hot branch: position i is past the cold tier.
                        assert(i < d.len());
                        assert(d[i as int] == adaptive_at(cold@, hot@, i as int));
                        assert(cold_adaptive(cold@).len() <= i as int);
                        assert(d.len() == adaptive_len(cold@, hot@));
                        assert((i - cold_total) < hot@.len());
                    }
                    out.push(hot[i - cold_total]);
                    proof {
                        assert(out@ =~= d.subrange(lo as int, (i + 1) as int));
                    }
                    i = i + 1;
                }
                proof {
                    assert(out@ =~= d.subrange(lo as int, hi as int));
                }
                out
            }
            DiffLog::Cols { .. } => {
                proof { assert(false); }
                Vec::new()
            }
        }
    }

    /// Drop the first `n` entries, keeping the suffix. Not called by `Vec` (only by
    /// the two-stack's plain hot log); for the value-major variant it rebuilds the
    /// suffix as a fresh plain tail (no cold frames), which is correct and only used
    /// off the `Vec` path. `final@ == old@[n..]`.
    pub fn drop_front(&mut self, n: usize)
        requires old(self).wf(), n <= old(self)@.len(),
        ensures final(self).wf(), final(self)@ == old(self)@.subrange(n as int, old(self)@.len() as int),
    {
        let len = self.len();
        let mut new_idxs: Vec<I> = Vec::new();
        let mut new_vals: Vec<T> = Vec::new();
        let mut i: usize = n;
        while i < len
            invariant
                n <= i <= len,
                len == self@.len(),
                self.wf(),
                new_idxs@.len() == i - n,
                new_vals@.len() == i - n,
                forall|k: int| 0 <= k < i - n ==> new_idxs@[k] == self@[n + k].1,
                forall|k: int| 0 <= k < i - n ==> new_vals@[k] == self@[n + k].0,
            decreases len - i,
        {
            let (v, idx) = self.index(i);
            new_vals.push(v);
            new_idxs.push(idx);
            i += 1;
        }
        *self = DiffLog::Cols { idxs: DiffIdxs::Plain(new_idxs), vals: DiffVals::Plain(new_vals) };
        assert(self@ =~= old(self)@.subrange(n as int, old(self)@.len() as int));
    }

    /// Truncate to `n` entries. Keeps whole cold frames up to `n`; a partial frame
    /// (when `n` falls inside a cold frame) is decoded into a fresh plain tail, and
    /// the hot tail is truncated when `n` is in it. Preserves the kept prefix's view.
    pub fn truncate(&mut self, n: usize)
        requires old(self).wf(), n <= old(self)@.len(),
        ensures final(self).wf(), final(self)@ == old(self)@.subrange(0, n as int),
    {
        let len = self.len();
        match self {
        DiffLog::Cols { idxs, vals } => {
        // Index side: Plain truncates in place; Runs mirrors the value partial-frame
        // logic (keep whole cold frames, decode the split frame's kept prefix).
        match idxs {
            DiffIdxs::Plain(v) => {
                v.truncate(n);
            }
            DiffIdxs::Runs { cold, tail } => {
                proof { reveal(cold_idxs); }
                assert(cold_idxs(cold@).len() + tail@.len() == len);
                let cold_len = len - tail.len();
                assert(cold_len == cold_idxs(cold@).len());
                if n >= cold_len {
                    tail.truncate(n - cold_len);
                    proof { assert(cold_idxs(cold@).len() == cold_len); }
                } else {
                    let ghost cold_all = cold@;
                    let clen = cold.len();
                    let mut d: usize = n;
                    let mut k: usize = 0;
                    while cold[k].entry_len() <= d
                        invariant
                            0 <= k <= cold@.len(),
                            k < cold@.len(),
                            cold@.len() == clen,
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            n == d + cold_idxs(cold@.subrange(0, k as int)).len(),
                            n < cold_idxs(cold@).len(),
                        decreases cold@.len() - k,
                    {
                        let flen = cold[k].entry_len();
                        proof {
                            assert(flen == cold@[k as int].idx_seq().len());
                            assert(cold@.subrange(0, k + 1)
                                =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                            lemma_cold_idxs_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                            assert(cold_idxs(cold@.subrange(0, (k + 1) as int)).len()
                                == cold_idxs(cold@.subrange(0, k as int)).len() + flen);
                            assert(flen <= d);
                            assert(cold_idxs(cold@.subrange(0, (k + 1) as int)).len() <= n);
                            assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                            assert(k + 1 < cold@.len());
                        }
                        d = d - flen;
                        k = k + 1;
                    }
                    let ghost off = cold_idxs(cold_all.subrange(0, k as int)).len();
                    let mut new_tail: Vec<I> = Vec::new();
                    let mut j: usize = 0;
                    while j < d
                        invariant
                            0 <= j <= d,
                            k < cold_all.len(),
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            d <= cold_all[k as int].idx_seq().len(),
                            new_tail@.len() == j,
                            forall|t: int| 0 <= t < j ==>
                                #[trigger] new_tail@[t] == cold_all[k as int].idx_seq()[t],
                        decreases d - j,
                    {
                        new_tail.push(cold[k].idx_at(j));
                        j += 1;
                    }
                    cold.truncate(k);
                    *tail = new_tail;
                    proof {
                        assert(cold@ =~= cold_all.subrange(0, k as int));
                        lemma_cold_idxs_split(cold_all, k as int);
                        assert(cold_idxs(cold@).len() == off);
                        lemma_cold_idxs_at_prefix(cold_all, k as int, d as int);
                    }
                }
            }
        }
        // Value side: Plain truncates in place; Dict mirrors the same partial-frame
        // logic. At most one side is compressed (the other is a plain Vec truncate).
        match vals {
            DiffVals::Plain(v) => {
                v.truncate(n);
                assert(self@ =~= old(self)@.subrange(0, n as int));
            }
            DiffVals::Dict { cold, tail } => {
                proof { reveal(cold_vals); }
                let cold_len = len - tail.len();
                assert(cold_len == cold_vals(cold@).len());
                if n >= cold_len {
                    // `n` is in (or at the start of) the hot tail: keep all cold.
                    tail.truncate(n - cold_len);
                    proof {
                        assert(cold_vals(cold@).len() == cold_len);
                    }
                    assert(self@ =~= old(self)@.subrange(0, n as int));
                } else {
                    // `n` is within the cold region: walk to the frame containing
                    // `n`, keep whole frames before it, decode its kept prefix into a
                    // fresh plain tail, drop the rest. (Vec restores to a frame
                    // boundary, `rem == 0`, so the decode loop is usually empty; the
                    // mid-frame `rem > 0` path is correct but off the Vec path.)
                    let ghost cold_all = cold@;
                    let clen = cold.len();
                    // Carry the remaining offset `d` (subtraction only). `d == n - prefix_k`.
                    let mut d: usize = n;
                    let mut k: usize = 0;
                    while cold[k].len() <= d
                        invariant
                            0 <= k <= cold@.len(),
                            k < cold@.len(),
                            cold@.len() == clen,
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            n == d + cold_vals(cold@.subrange(0, k as int)).len(),
                            n < cold_vals(cold@).len(),
                        decreases cold@.len() - k,
                    {
                        let flen = cold[k].len();
                        proof {
                            assert(flen == cold@[k as int].decode().len());
                            assert(cold@.subrange(0, k + 1)
                                =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                            lemma_cold_vals_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                            assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len()
                                == cold_vals(cold@.subrange(0, k as int)).len() + flen);
                            assert(flen <= d);
                            assert(cold_vals(cold@.subrange(0, (k + 1) as int)).len() <= n);
                            assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                            assert(k + 1 < cold@.len());
                        }
                        d = d - flen;
                        k = k + 1;
                    }
                    // `d == n - prefix_k == rem`; decode frame k's kept prefix [0, d).
                    let ghost off = cold_vals(cold_all.subrange(0, k as int)).len();
                    let mut new_tail: Vec<T> = Vec::new();
                    let mut j: usize = 0;
                    while j < d
                        invariant
                            0 <= j <= d,
                            k < cold_all.len(),
                            cold@ == cold_all,
                            forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                            d <= cold_all[k as int].decode().len(),
                            new_tail@.len() == j,
                            forall|t: int| 0 <= t < j ==>
                                #[trigger] new_tail@[t] == cold_all[k as int].decode()[t],
                        decreases d - j,
                    {
                        new_tail.push(cold[k].decode_at(j));
                        j += 1;
                    }
                    // Keep frames [0, k) in place (no clone), set the decoded tail.
                    cold.truncate(k);
                    *tail = new_tail;
                    proof {
                        assert(cold@ =~= cold_all.subrange(0, k as int));
                        lemma_cold_vals_split(cold_all, k as int);
                        // cold_vals(cold@) is the length-`off` prefix of cold_vals(cold_all),
                        // and n == off + d.
                        assert(cold_vals(cold@).len() == off);
                        lemma_cold_vals_at_prefix(cold_all, k as int, d as int);
                    }
                    assert(self@ =~= old(self)@.subrange(0, n as int));
                }
            }
        }
        }
        DiffLog::Adaptive { cold, hot, len: lenf } => {
            proof { reveal(cold_adaptive); }
            assert(cold_adaptive(cold@).len() + hot@.len() == len);
            let cold_len = len - hot.len();
            assert(cold_len == cold_adaptive(cold@).len());
            if n >= cold_len {
                // `n` in (or at the start of) the hot tail: keep all cold frames.
                hot.truncate(n - cold_len);
                *lenf = n;
                proof { assert(cold_adaptive(cold@).len() == cold_len); }
                assert(self@ =~= old(self)@.subrange(0, n as int));
            } else {
                // `n` within the cold region: walk to the frame containing `n`, keep
                // whole frames before it, decode its kept prefix into a fresh hot tail.
                // (Restore lands on a frame boundary, so the decode loop is usually
                // empty; the mid-frame path is correct but off the Vec path.)
                let ghost cold_all = cold@;
                let clen = cold.len();
                let mut d: usize = n;
                let mut k: usize = 0;
                while cold[k].entry_len() <= d
                    invariant
                        0 <= k <= cold@.len(),
                        k < cold@.len(),
                        cold@.len() == clen,
                        cold@ == cold_all,
                        forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                        n == d + cold_adaptive(cold@.subrange(0, k as int)).len(),
                        n < cold_adaptive(cold@).len(),
                    decreases cold@.len() - k,
                {
                    let flen = cold[k].entry_len();
                    proof {
                        assert(flen == cold@[k as int].decode().len());
                        assert(cold@.subrange(0, k + 1)
                            =~= cold@.subrange(0, k as int).push(cold@[k as int]));
                        lemma_cold_adaptive_snoc(cold@.subrange(0, k as int), cold@[k as int]);
                        assert(cold_adaptive(cold@.subrange(0, (k + 1) as int)).len()
                            == cold_adaptive(cold@.subrange(0, k as int)).len() + flen);
                        assert(flen <= d);
                        assert(cold_adaptive(cold@.subrange(0, (k + 1) as int)).len() <= n);
                        assert(cold@.subrange(0, cold@.len() as int) =~= cold@);
                        assert(k + 1 < cold@.len());
                    }
                    d = d - flen;
                    k = k + 1;
                }
                let ghost off = cold_adaptive(cold_all.subrange(0, k as int)).len();
                let mut new_hot: Vec<(T, I)> = Vec::new();
                let mut j: usize = 0;
                while j < d
                    invariant
                        0 <= j <= d,
                        k < cold_all.len(),
                        cold@ == cold_all,
                        forall|kk: int| 0 <= kk < cold@.len() ==> (#[trigger] cold@[kk]).wf(),
                        d <= cold_all[k as int].decode().len(),
                        new_hot@.len() == j,
                        forall|t: int| 0 <= t < j ==>
                            #[trigger] new_hot@[t] == cold_all[k as int].decode()[t],
                    decreases d - j,
                {
                    new_hot.push(cold[k].decode_at(j));
                    j += 1;
                }
                cold.truncate(k);
                *hot = new_hot;
                *lenf = n;
                proof {
                    assert(cold@ =~= cold_all.subrange(0, k as int));
                    lemma_cold_adaptive_split(cold_all, k as int);
                    assert(cold_adaptive(cold@).len() == off);
                    lemma_cold_adaptive_at_prefix(cold_all, k as int, d as int);
                }
                assert(self@ =~= old(self)@.subrange(0, n as int));
            }
        }
        }
    }
}

/// For the truncate partial-frame case: the first `rem` entries of frame `k`
/// (`cold[k].decode()[0..rem]`) are exactly entries `[base, base+rem)` of the whole
/// concatenation, where `base == cold_vals(cold[0..k]).len()`.
pub proof fn lemma_cold_vals_at_prefix<T: Copy>(cold: Seq<ValFrame<T>>, k: int, rem: int)
    requires
        0 <= k < cold.len(),
        0 <= rem <= cold[k].decode().len(),
    ensures
        forall|t: int| 0 <= t < rem ==>
            cold_vals(cold)[cold_vals(cold.subrange(0, k)).len() + t] == cold[k].decode()[t],
{
    let base = cold_vals(cold.subrange(0, k)).len();
    assert forall|t: int| 0 <= t < rem implies
        cold_vals(cold)[base + t] == cold[k].decode()[t] by {
        lemma_cold_vals_at(cold, k, base + t);
    }
}

/// `cold_vals` splits at any frame boundary: the concatenation of all frames is the
/// concatenation of the first `k` followed by the rest. Gives the prefix agreement
/// `cold_vals(cold[0..k])[i] == cold_vals(cold)[i]` for `i < cold_vals(cold[0..k]).len()`.
pub proof fn lemma_cold_vals_split<T: Copy>(cold: Seq<ValFrame<T>>, k: int)
    requires 0 <= k <= cold.len(),
    ensures
        cold_vals(cold) == cold_vals(cold.subrange(0, k))
            + cold_vals(cold.subrange(k, cold.len() as int)),
    decreases cold.len(),
{
    reveal_with_fuel(cold_vals, 2);
    if cold.len() == 0 {
        assert(cold.subrange(0, k) =~= Seq::<ValFrame<T>>::empty());
        assert(cold.subrange(k, cold.len() as int) =~= Seq::<ValFrame<T>>::empty());
        assert(cold_vals(cold) =~= Seq::<T>::empty());
    } else if k == 0 {
        assert(cold.subrange(0, 0) =~= Seq::<ValFrame<T>>::empty());
        assert(cold.subrange(0, cold.len() as int) =~= cold);
    } else {
        let head = cold[0];
        let rest = cold.subrange(1, cold.len() as int);
        lemma_cold_vals_split(rest, k - 1);
        assert(cold.subrange(0, k).subrange(1, k) =~= rest.subrange(0, k - 1));
        assert(cold.subrange(0, k)[0] == head);
        // cold_vals(cold[0..k]) == head.decode() + cold_vals(rest[0..k-1]).
        assert(cold_vals(cold.subrange(0, k))
            =~= head.decode() + cold_vals(rest.subrange(0, k - 1)));
        assert(cold.subrange(k, cold.len() as int) =~= rest.subrange(k - 1, rest.len() as int));
        let a = head.decode();
        let b = cold_vals(rest.subrange(0, k - 1));
        let c = cold_vals(rest.subrange(k - 1, rest.len() as int));
        assert(a + (b + c) =~= (a + b) + c);
    }
}

} // verus!
