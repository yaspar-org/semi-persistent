// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Vec<T, I, S, const TRACK: bool>`: the headline semi-persistent vector.
//!
//! M3a (already landed): scaffold — push, set, get, view. No mark/restore.
//!
//! M3b (this milestone): single-frame `mark` and `restore`, plus `pop`.
//! Proves the headline correctness theorem
//!
//!     view() == snapshots[token.frame_idx]
//!
//! after restore, where `snapshots: Seq<Seq<T>>` is a ghost stack of deep
//! copies recorded at each `mark()`. M3b restricts to a single live frame
//! at a time — no nested marks. M4 will lift that.
//!
//! Branch-cut safety (M5) is not enforced yet: M3b's `restore` accepts any
//! token whose `frame_idx` is in range. M5 adds `ContainerId` + `ForkHistory`.
//!
//! ## Invariant (M3b, single frame)
//!
//! Production calls this "first-write-wins": each captured slot appears in
//! the diff log at most once, with its pre-frame value. The clean spec-side
//! statement is **pointwise**:
//!
//!   For each `j < saved_len`:
//!     if `(old, j) ∈ diff_log` for some entry, then `snapshots[0][j] == old`;
//!     otherwise                                    `snapshots[0][j] == view[j]`.
//!
//! That is: `snapshots[0]` is reconstructed by overlaying the diff entries
//! onto the current view. Recursion-free, no `replay_reverse` to chase.
//!
//! Plus two structural conditions:
//!   - every diff entry idx is `< saved_len` (no out-of-frame entries);
//!   - first-write-wins: distinct entries point at distinct indices.

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::frame::Frame;
use crate::index_like::IndexLike;

verus! {

/// Opaque token returned by `mark()`. M3b carries only `frame_idx`; M5
/// will add container_id + branch_id + depth.
#[derive(Copy, Clone)]
pub struct VecToken {
    pub frame_idx: usize,
}

/// Spec helper: there is some entry in `diffs` pointing at index `j`.
///
/// Used as the "captured" predicate in the declarative invariant.
pub open spec fn diff_has_index<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    j: nat,
) -> bool {
    exists|k: int| 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// First-write-wins: each index appears at most once across the diff log.
///
/// Without this, multiple entries could disagree about a slot's marked
/// value and the invariant would be ambiguous. Production enforces this
/// via the per-slot capture flag.
pub open spec fn diffs_unique_indices<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < diffs.len() && 0 <= j < diffs.len() && i != j
            ==> (#[trigger] diffs[i]).1.as_nat() != (#[trigger] diffs[j]).1.as_nat()
}

/// The declarative frame invariant — your formulation.
///
/// For each cell `j` in the marked region:
///   - If no diff entry points at `j` (uncaptured): `view[j] == snap[j]`.
///     The slot was never written to since mark, so the current view
///     still holds the marked value.
///   - Else (captured): some diff entry `(old, j)` has `old == snap[j]`.
///     The diff log holds the marked value; the current view holds
///     whatever scribble has been written since.
///
/// Both arms are stated as conjuncts. They are *jointly* the meaning of
/// "snap is the snapshot at mark time of this view-plus-diff-log triple."
/// First-write-wins (above) ensures the captured arm's witness is unique.
pub open spec fn frame_inv<T, I: IndexLike>(
    view: Seq<T>,
    diffs: Seq<(T, I)>,
    snap: Seq<T>,
    saved_len: nat,
) -> bool {
    &&& snap.len() == saved_len
    &&& saved_len <= view.len()
    &&& (forall|j: int| #![trigger snap[j]]
            0 <= j < saved_len as int ==> {
                if !diff_has_index::<T, I>(diffs, j as nat) {
                    // Uncaptured arm.
                    view[j] == snap[j]
                } else {
                    // Captured arm.
                    exists|k: int| 0 <= k < diffs.len()
                        && (#[trigger] diffs[k]).1.as_nat() == j as nat
                        && diffs[k].0 == snap[j]
                }
            })
}

// ---------------------------------------------------------------------------
// `overlay` — the spec model of the restore loop (M4)
// ---------------------------------------------------------------------------
//
// The restore loop walks the diff log from `n` down to `lo`, applying each
// entry `(old, idx)` via `restore_entry`. Entries with `idx < base.len()`
// overwrite `base[idx]`; entries beyond `base.len()` are no-ops (the
// production restore_entry guard). Because the loop walks *downward*, the
// entry with the SMALLEST index in `[lo, hi)` that hits a given cell is
// applied LAST and therefore wins.
//
// `overlay(base, diffs, lo, hi)` is the recursive spec for this: apply
// `diffs[lo]` on top of `overlay(base, diffs, lo+1, hi)`, so the lower
// index ends up outermost (winning). This is exactly the loop's result.

/// Replay `diffs[lo..hi]` over `base` in reverse-index-wins order.
pub open spec fn overlay<T, I: IndexLike>(
    base: Seq<T>,
    diffs: Seq<(T, I)>,
    lo: int,
    hi: int,
) -> Seq<T>
    decreases hi - lo
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
        base
    } else {
        let prev = overlay(base, diffs, lo + 1, hi);
        let d = diffs[lo];
        if d.1.as_nat() < prev.len() {
            prev.update(d.1.as_nat() as int, d.0)
        } else {
            prev
        }
    }
}

/// `overlay` preserves the base length (it only updates, never grows).
pub proof fn lemma_overlay_len<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
)
    ensures overlay::<T, I>(base, diffs, lo, hi).len() == base.len(),
    decreases hi - lo,
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    }
}

/// If no entry in `[lo, hi)` hits cell `j`, overlay leaves `base[j]` alone.
pub proof fn lemma_overlay_uncaptured<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, j: int,
)
    requires
        0 <= j < base.len(),
        forall|k: int| lo <= k < hi && 0 <= k < diffs.len()
            ==> (#[trigger] diffs[k]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == base[j],
    decreases hi - lo,
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_uncaptured::<T, I>(base, diffs, lo + 1, hi, j);
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
        // diffs[lo].1 != j, so the update at lo (if any) doesn't touch j.
    }
}

/// If `[lo, hi)` has unique indices and the entry at position `p` hits `j`,
/// then overlay sets `base[j]` to that entry's value — regardless of base,
/// because the winning entry is the unique one.
pub proof fn lemma_overlay_captured<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, p: int, j: int,
)
    requires
        0 <= j < base.len(),
        lo <= p < hi,
        0 <= p < diffs.len(),
        lo >= 0,
        hi <= diffs.len(),
        diffs[p].1.as_nat() == j as nat,
        // unique within [lo, hi)
        forall|a: int, b: int|
            lo <= a < hi && lo <= b < hi && a != b
                ==> (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat(),
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == diffs[p].0,
    decreases hi - lo,
{
    let prev = overlay::<T, I>(base, diffs, lo + 1, hi);
    lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    if p == lo {
        // Entry at lo wins (applied last/outermost). All entries in
        // [lo+1, hi) have different indices from j (uniqueness), so they
        // don't matter — the final update at lo sets j.
    } else {
        // p in [lo+1, hi). By IH, overlay(lo+1, hi)[j] == diffs[p].0.
        lemma_overlay_captured::<T, I>(base, diffs, lo + 1, hi, p, j);
        // The update at lo has index diffs[lo].1 != j (uniqueness, lo != p),
        // so it doesn't disturb j.
    }
}

/// `frame_inv_range` over `[lo, hi)` depends only on the diff entries in
/// that range. If two diff sequences agree pointwise on `[lo, hi)` (and are
/// both long enough), the predicate holds for one iff for the other.
pub proof fn lemma_frame_inv_range_local<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo <= hi <= da.len(),
        hi <= db.len(),
        forall|m: int| lo <= m < hi ==> #[trigger] da[m] == db[m],
        frame_inv_range::<T, I>(above, da, lo, hi, snap, saved_len),
    ensures
        frame_inv_range::<T, I>(above, db, lo, hi, snap, saved_len),
{
    // Structural conjuncts: index-bound and uniqueness foralls read entries
    // only in [lo, hi), where da and db agree.
    assert forall|m: int| lo <= m < hi implies
        (#[trigger] db[m]).1.as_nat() < saved_len by { assert(da[m] == db[m]); }
    assert forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b implies
        (#[trigger] db[a]).1.as_nat() != (#[trigger] db[b]).1.as_nat()
    by { assert(da[a] == db[a]); assert(da[b] == db[b]); }
    // Both the structural foralls and the two-arm forall read da[m]/db[m]
    // only for m in [lo, hi), where they agree. captured_in_range and the
    // captured-arm witness likewise quantify over [lo, hi).
    assert forall|j: int| #![trigger snap[j]] 0 <= j < saved_len as int implies {
        if !captured_in_range::<T, I>(db, lo, hi, j as nat) {
            above[j] == snap[j]
        } else {
            exists|k: int| lo <= k < hi
                && (#[trigger] db[k]).1.as_nat() == j as nat
                && db[k].0 == snap[j]
        }
    } by {
        // captured_in_range agrees because entries agree on [lo, hi).
        assert(captured_in_range::<T, I>(db, lo, hi, j as nat)
            == captured_in_range::<T, I>(da, lo, hi, j as nat)) by {
            if captured_in_range::<T, I>(db, lo, hi, j as nat) {
                let w = choose|k: int| lo <= k < hi && 0 <= k < db.len()
                    && (#[trigger] db[k]).1.as_nat() == j as nat;
                assert(da[w] == db[w]);
            }
            if captured_in_range::<T, I>(da, lo, hi, j as nat) {
                let w = choose|k: int| lo <= k < hi && 0 <= k < da.len()
                    && (#[trigger] da[k]).1.as_nat() == j as nat;
                assert(da[w] == db[w]);
            }
        }
        if captured_in_range::<T, I>(db, lo, hi, j as nat) {
            let w = choose|k: int| lo <= k < hi
                && (#[trigger] da[k]).1.as_nat() == j as nat && da[k].0 == snap[j];
            assert(da[w] == db[w]);
        }
    }
}

/// `overlay`'s value at `j < bound` depends only on `base`'s prefix
/// `[0, bound)` and on entries whose index is `< bound`. Concretely: if two
/// bases agree on `[0, bound)`, then their overlays agree on `[0, bound)`,
/// regardless of base values or entry indices `>= bound`.
///
/// This is what lets restore overlay onto the *truncated* base (length
/// saved_len) and still match `overlay` onto the full view on the marked
/// region: entries with idx >= saved_len are no-ops on `[0, saved_len)`.
pub proof fn lemma_overlay_prefix_agnostic<T, I: IndexLike>(
    base_a: Seq<T>, base_b: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, bound: int,
)
    requires
        0 <= bound <= base_a.len(),
        0 <= bound <= base_b.len(),
        forall|j: int| 0 <= j < bound ==> #[trigger] base_a[j] == base_b[j],
    ensures
        forall|j: int| 0 <= j < bound ==>
            #[trigger] overlay::<T, I>(base_a, diffs, lo, hi)[j]
                == overlay::<T, I>(base_b, diffs, lo, hi)[j],
    decreases hi - lo,
{
    lemma_overlay_len::<T, I>(base_a, diffs, lo, hi);
    lemma_overlay_len::<T, I>(base_b, diffs, lo, hi);
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_prefix_agnostic::<T, I>(base_a, base_b, diffs, lo + 1, hi, bound);
        lemma_overlay_len::<T, I>(base_a, diffs, lo + 1, hi);
        lemma_overlay_len::<T, I>(base_b, diffs, lo + 1, hi);
        // The step at lo updates index diffs[lo].1 in both. For j < bound:
        // if diffs[lo].1 == j and j < both prevs' len, both get diffs[lo].0;
        // otherwise both inherit prev[j], equal by IH.
    }
}

/// `overlay` splits at any midpoint: applying `[lo, hi)` equals applying
/// the upper part `[mid, hi)` first, then the lower part `[lo, mid)` on top.
/// This is what lets us peel strata one at a time.
pub proof fn lemma_overlay_split<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, mid: int, hi: int,
)
    requires
        0 <= lo <= mid <= hi <= diffs.len(),
    ensures
        overlay::<T, I>(base, diffs, lo, hi)
            == overlay::<T, I>(overlay::<T, I>(base, diffs, mid, hi), diffs, lo, mid),
    decreases mid - lo,
{
    if lo >= mid {
        // [lo, mid) empty: RHS inner overlay is identity, so both sides
        // are overlay(base, mid, hi) == overlay(base, lo, hi) since lo==mid.
    } else {
        // Peel lo off both sides.
        //   LHS = step(diffs[lo], overlay(base, lo+1, hi))
        //   RHS = step(diffs[lo], overlay(overlay(base, mid, hi), lo+1, mid))
        // By IH on (lo+1, mid, hi): overlay(base, lo+1, hi)
        //   == overlay(overlay(base, mid, hi), lo+1, mid).
        // So the two `step` arguments coincide and the results match.
        lemma_overlay_split::<T, I>(base, diffs, lo + 1, mid, hi);
    }
}

/// Range-based "captured": some entry in `diffs[lo..hi)` hits `j`.
pub open spec fn captured_in_range<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int, j: nat,
) -> bool {
    exists|k: int| lo <= k < hi && 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Range-form of the two-arm frame invariant for one stratum `[lo, hi)`.
/// `above` is the layer above (snapshot[k+1] or the view); `snap` is this
/// stratum's snapshot. Stated over the diff-log range directly.
pub open spec fn frame_inv_range<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
) -> bool {
    &&& snap.len() == saved_len
    &&& saved_len <= above.len()
    &&& (forall|k: int| lo <= k < hi ==>
            (#[trigger] diffs[k]).1.as_nat() < saved_len)
    &&& (forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b ==>
            (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat())
    &&& (forall|j: int| #![trigger snap[j]] 0 <= j < saved_len as int ==> {
            if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
                above[j] == snap[j]
            } else {
                exists|k: int| lo <= k < hi
                    && (#[trigger] diffs[k]).1.as_nat() == j as nat
                    && diffs[k].0 == snap[j]
            }
        })
}

/// The per-stratum bridge: if a diff-log range `[lo, hi)` satisfies the
/// two-arm `frame_inv` relative to `above` and `snap` (stated directly over
/// the range), then overlaying that range onto `above` reproduces `snap`
/// on `[0, saved_len)`.
///
/// Hypotheses mirror `frame_inv` + the structural conditions, but phrased
/// over the diff-log range rather than an extracted subrange.
pub proof fn lemma_overlay_eq_snap<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        snap.len() == saved_len,
        saved_len <= above.len(),
        // entries in range are in-bounds for the marked region
        forall|k: int| lo <= k < hi ==>
            (#[trigger] diffs[k]).1.as_nat() < saved_len,
        // unique indices within range
        forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b ==>
            (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat(),
        // two-arm frame_inv over the range
        forall|j: int| #![trigger snap[j]] 0 <= j < saved_len as int ==> {
            if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
                above[j] == snap[j]
            } else {
                exists|k: int| lo <= k < hi
                    && (#[trigger] diffs[k]).1.as_nat() == j as nat
                    && diffs[k].0 == snap[j]
            }
        },
    ensures
        forall|j: int| 0 <= j < saved_len as int ==>
            #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j],
{
    lemma_overlay_len::<T, I>(above, diffs, lo, hi);
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j]
    by {
        if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
            // Uncaptured: overlay leaves above[j], which == snap[j].
            assert forall|k: int| lo <= k < hi && 0 <= k < diffs.len() implies
                (#[trigger] diffs[k]).1.as_nat() != j as nat
            by {
                // else captured_in_range would hold
            }
            lemma_overlay_uncaptured::<T, I>(above, diffs, lo, hi, j);
        } else {
            // Captured: pick the witness entry p, show overlay sets snap[j].
            let p = choose|k: int| lo <= k < hi
                && (#[trigger] diffs[k]).1.as_nat() == j as nat
                && diffs[k].0 == snap[j];
            lemma_overlay_captured::<T, I>(above, diffs, lo, hi, p, j);
        }
    }
}

/// Semi-persistent vector parameterized by storage backend `S` and index
/// type `I`. `TRACK` compiles out all tracking when false.
pub struct Vec<T, I, S, const TRACK: bool>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub store: S,
    pub diff_log: std::vec::Vec<(T, I)>,
    pub frames: std::vec::Vec<Frame<I>>,
    pub phantom: core::marker::PhantomData<(T, I)>,
    /// Ghost stack of deep copies. `snapshots[k]` is `view()` at the
    /// moment frame `k` was pushed. Always `snapshots.len() == frames.len()`.
    pub snapshots: Ghost<Seq<Seq<T>>>,
}

impl<T, I, S, const TRACK: bool> Vec<T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// Public spec view: the abstract sequence of stored values.
    pub open spec fn view(&self) -> Seq<T> {
        self.store.data()
    }

    /// Snapshot stack (ghost).
    pub open spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Well-formedness. M3b invariants:
    ///   - snapshots.len() == frames.len()           (parallel stacks)
    ///   - frames.len() <= 1                          (single frame for now)
    ///   - frames.len() == 0 ==> diff_log is empty   (no orphan diff entries)
    ///   - if frames.len() == 1:
    ///       diff_start == 0
    ///       every diff entry idx < saved_len       (in-bounds diffs only)
    ///       first-write-wins (unique indices)
    ///       frame_inv(view, diff_log, snapshots[0], saved_len)
    /// The "layer above" frame `k`: snapshots[k+1] for inner frames, or the
    /// current view for the topmost frame.
    pub open spec fn layer_above_at(&self, k: int) -> Seq<T> {
        if k + 1 < self.frames@.len() {
            self.snapshots@[k + 1]
        } else {
            self.view()
        }
    }

    /// End of frame `k`'s stratum.
    pub open spec fn stratum_end(&self, k: int) -> int {
        if k + 1 < self.frames@.len() {
            self.frames@[k + 1].diff_start as int
        } else {
            self.diff_log@.len() as int
        }
    }

    /// Well-formedness, generalized to arbitrary stack depth (M4).
    ///
    /// Structural:
    ///   - snapshots.len() == frames.len()
    ///   - frames.len() == 0 ==> diff_log empty
    ///   - frames[0].diff_start == 0
    ///   - diff_starts monotone, last <= diff_log.len()
    ///   - saved_lens monotone, last <= view.len()
    ///   - snapshots[k].len() == frames[k].saved_len
    ///
    /// Per-frame (over each frame's stratum `[diff_start_k, stratum_end_k)`):
    ///   frame_inv_range(layer_above(k), diff_log, lo_k, hi_k,
    ///                   snapshots[k], saved_len_k)
    pub open spec fn wf(&self) -> bool {
        let frames = self.frames@;
        let diffs = self.diff_log@;
        let snaps = self.snapshots@;
        let n = diffs.len();

        &&& self.store.wf()
        &&& snaps.len() == frames.len()
        &&& (frames.len() == 0 ==> n == 0)
        &&& (frames.len() > 0 ==> frames[0].diff_start == 0)
        &&& (frames.len() > 0 ==> frames[(frames.len() - 1) as int].diff_start <= n)
        &&& (frames.len() > 0 ==>
                frames[(frames.len() - 1) as int].saved_len.as_nat() <= self.view().len())
        &&& (forall|k: int| 0 <= k && k + 1 < frames.len() ==>
                #[trigger] frames[k].diff_start <= #[trigger] frames[k + 1].diff_start)
        &&& (forall|k: int| 0 <= k && k + 1 < frames.len() ==>
                #[trigger] frames[k].saved_len.as_nat()
                    <= #[trigger] frames[k + 1].saved_len.as_nat())
        &&& (forall|k: int| 0 <= k < frames.len() ==>
                #[trigger] snaps[k].len() == #[trigger] frames[k].saved_len.as_nat())
        &&& (forall|k: int| 0 <= k < frames.len() ==>
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k),
                    diffs,
                    frames[k].diff_start as int,
                    self.stratum_end(k),
                    snaps[k],
                    frames[k].saved_len.as_nat()))
    }

    /// Every frame's diff_start is `<= diff_log.len()`. Follows from
    /// monotonicity plus the top frame's bound, by upward induction.
    pub proof fn lemma_diff_start_le_n(&self, k: int)
        requires
            self.wf(),
            0 <= k < self.frames@.len(),
        ensures
            self.frames@[k].diff_start <= self.diff_log@.len(),
        decreases self.frames@.len() - k,
    {
        let frames = self.frames@;
        if k + 1 < frames.len() {
            self.lemma_diff_start_le_n(k + 1);
            assert(frames[k].diff_start <= frames[k + 1].diff_start);
        } else {
            // top frame: bounded directly by wf.
        }
    }

    /// diff_start is monotone non-decreasing across frames: for `a <= b`,
    /// `frames[a].diff_start <= frames[b].diff_start`.
    pub proof fn lemma_diff_start_monotone(&self, a: int, b: int)
        requires
            self.wf(),
            0 <= a <= b < self.frames@.len(),
        ensures
            self.frames@[a].diff_start <= self.frames@[b].diff_start,
        decreases b - a,
    {
        let frames = self.frames@;
        if a < b {
            self.lemma_diff_start_monotone(a, b - 1);
            // wf gives the adjacent step at k = b-1 (since b < frames.len()).
            assert(0 <= b - 1 && (b - 1) + 1 < frames.len());
            assert(frames[b - 1].diff_start <= frames[(b - 1) + 1].diff_start);
        }
    }

    /// saved_len is monotone non-decreasing across frames.
    pub proof fn lemma_saved_len_monotone(&self, a: int, b: int)
        requires
            self.wf(),
            0 <= a <= b < self.frames@.len(),
        ensures
            self.frames@[a].saved_len.as_nat() <= self.frames@[b].saved_len.as_nat(),
        decreases b - a,
    {
        let frames = self.frames@;
        if a < b {
            self.lemma_saved_len_monotone(a, b - 1);
            assert(0 <= b - 1 && (b - 1) + 1 < frames.len());
            assert(frames[b - 1].saved_len.as_nat() <= frames[(b - 1) + 1].saved_len.as_nat());
        }
    }

    /// Every frame's saved_len is `<= view.len()`. By monotonicity plus
    /// the top frame's bound.
    pub proof fn lemma_saved_len_le_view(&self, k: int)
        requires
            self.wf(),
            0 <= k < self.frames@.len(),
        ensures
            self.frames@[k].saved_len.as_nat() <= self.view().len(),
        decreases self.frames@.len() - k,
    {
        let frames = self.frames@;
        if k + 1 < frames.len() {
            self.lemma_saved_len_le_view(k + 1);
            assert(frames[k].saved_len.as_nat() <= frames[k + 1].saved_len.as_nat());
        } else {
        }
    }

    /// The central M4 lemma: overlaying all strata from frame `k` up to the
    /// top, onto the current view, reconstructs `snapshots[k]` (on its
    /// `[0, saved_len_k)` domain).
    ///
    /// Proved by downward induction on `k` (from the top frame to `k`).
    /// Base case k == top: the stratum is `[diff_start_top, n)`, the layer
    /// above is the view, and `frame_inv_range` + `lemma_overlay_eq_snap`
    /// give the result. Inductive step: split the range at
    /// `frames[k+1].diff_start`; the upper part reconstructs snapshots[k+1]
    /// by IH, then stratum k overlays on top to give snapshots[k].
    pub proof fn lemma_snap_eq_overlay(&self, k: int)
        requires
            self.wf(),
            0 <= k < self.frames@.len(),
        ensures
            forall|j: int| 0 <= j < self.frames@[k].saved_len.as_nat() ==>
                #[trigger] overlay::<T, I>(
                    self.view(),
                    self.diff_log@,
                    self.frames@[k].diff_start as int,
                    self.diff_log@.len() as int)[j]
                == self.snapshots@[k][j],
        decreases self.frames@.len() - k,
    {
        let frames = self.frames@;
        let diffs = self.diff_log@;
        let snaps = self.snapshots@;
        let n = diffs.len() as int;
        let lo = frames[k].diff_start as int;
        let saved = frames[k].saved_len.as_nat();
        let mid = self.stratum_end(k);

        // frame_inv_range for stratum k is available from wf.
        assert(frame_inv_range::<T, I>(
            self.layer_above_at(k), diffs, lo, mid, snaps[k], saved));

        if k + 1 < frames.len() {
            // Inductive case. mid == frames[k+1].diff_start.
            // Bounds: lo <= mid <= n. lo <= mid by diff_start monotonicity
            // (k, k+1 adjacent); mid <= n because frames[k+1].diff_start
            // <= frames[top].diff_start <= n.
            self.lemma_diff_start_le_n(k + 1);
            assert(lo <= mid) by {
                assert(frames[k].diff_start <= frames[k + 1].diff_start);
            }
            // Upper range [mid, n) reconstructs snapshots[k+1] by IH.
            self.lemma_snap_eq_overlay(k + 1);
            let above = overlay::<T, I>(self.view(), diffs, mid, n);

            // Split overlay(view, lo, n) = overlay(overlay(view, mid, n), lo, mid).
            lemma_overlay_split::<T, I>(self.view(), diffs, lo, mid, n);

            // `above` agrees with snapshots[k+1] on [0, saved_{k+1}); and
            // saved <= saved_{k+1} (monotone), so `above` agrees with
            // snapshots[k+1] = layer_above_at(k) on [0, saved).
            lemma_overlay_len::<T, I>(self.view(), diffs, mid, n);

            // Now overlay stratum k onto `above`. frame_inv_range holds with
            // layer_above_at(k) == snapshots[k+1]; we need it to hold with
            // `above` instead. They agree on [0, saved), which is all
            // frame_inv_range's uncaptured arm reads.
            assert(self.layer_above_at(k) == snaps[k + 1]);
            assert(frames[k].saved_len.as_nat() <= frames[k + 1].saved_len.as_nat());
            assert forall|j: int| 0 <= j < saved implies
                #[trigger] above[j] == snaps[k + 1][j]
            by {
                self.lemma_snap_eq_overlay(k + 1);
            }
            // Build frame_inv_range over `above` and apply the bridge.
            // The original frame_inv_range (from wf) holds with layer
            // `snaps[k+1]`. The captured arm is layer-independent; the
            // uncaptured arm needs above[j] == snaps[k][j], which chains
            // above[j] == snaps[k+1][j] (IH) and snaps[k+1][j] == snaps[k][j]
            // (original uncaptured arm).
            assert(frame_inv_range::<T, I>(above, diffs, lo, mid, snaps[k], saved)) by {
                assert(above.len() == self.view().len());
                self.lemma_saved_len_le_view(k);
                assert(saved <= above.len());
                assert forall|j: int| #![trigger snaps[k][j]] 0 <= j < saved as int implies {
                    if !captured_in_range::<T, I>(diffs, lo, mid, j as nat) {
                        above[j] == snaps[k][j]
                    } else {
                        exists|p: int| lo <= p < mid
                            && (#[trigger] diffs[p]).1.as_nat() == j as nat
                            && diffs[p].0 == snaps[k][j]
                    }
                } by {
                    // The original frame_inv_range over snaps[k+1] layer.
                    assert(frame_inv_range::<T, I>(
                        snaps[k + 1], diffs, lo, mid, snaps[k], saved));
                    if !captured_in_range::<T, I>(diffs, lo, mid, j as nat) {
                        // original uncaptured arm: snaps[k+1][j] == snaps[k][j]
                        // IH: above[j] == snaps[k+1][j]
                        assert(above[j] == snaps[k + 1][j]);
                        assert(snaps[k + 1][j] == snaps[k][j]);
                    } else {
                        // captured arm carries over verbatim (no layer dep).
                    }
                }
            }
            lemma_overlay_eq_snap::<T, I>(above, diffs, lo, mid, snaps[k], saved);
        } else {
            // Base case: top frame. mid == n, layer above == view.
            assert(mid == n);
            assert(self.layer_above_at(k) == self.view());
            lemma_overlay_eq_snap::<T, I>(self.view(), diffs, lo, mid, snaps[k], saved);
        }
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
            self.snapshots_view() == old(self).snapshots_view(),
    {
        // Pull the top-frame bound from wf BEFORE mutating (wf holds now).
        proof {
            let frames = self.frames@;
            if frames.len() > 0 {
                self.lemma_saved_len_le_view((frames.len() - 1) as int);
            }
        }
        let ghost old_view = self.view();
        let ghost old_self = *self;
        self.store.push(value);
        // diff_log, frames, snapshots all unchanged. Only `view` changed,
        // by appending one element. Inner frames' frame_inv_range references
        // snapshots (unchanged) as `above`. The TOP frame references `view`;
        // re-establish its frame_inv_range explicitly.
        proof {
            assert(self.view() == old_view.push(value));
            assert(self.frames@ == old_self.frames@);
            assert(self.diff_log@ == old_self.diff_log@);
            assert(self.snapshots@ == old_self.snapshots@);
            let frames = self.frames@;
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k),
                    self.diff_log@,
                    frames[k].diff_start as int,
                    self.stratum_end(k),
                    self.snapshots@[k],
                    frames[k].saved_len.as_nat())
            by {
                // old frame_inv_range held for old_self with same args except
                // possibly layer_above_at (which equals view for top frame).
                assert(old_self.frame_inv_range_holds(k));
                if k + 1 < frames.len() {
                    // inner frame: layer_above unchanged (snapshot).
                    assert(self.layer_above_at(k) == old_self.layer_above_at(k));
                } else {
                    // top frame: layer is view, changed by push but prefix
                    // preserved; saved_len <= old_view.len().
                    self.lemma_saved_len_le_view_from(old_self, k);
                }
            }
        }
    }

    /// Helper used in proofs: assert frame_inv_range for frame k from wf.
    pub open spec fn frame_inv_range_holds(&self, k: int) -> bool {
        frame_inv_range::<T, I>(
            self.layer_above_at(k),
            self.diff_log@,
            self.frames@[k].diff_start as int,
            self.stratum_end(k),
            self.snapshots@[k],
            self.frames@[k].saved_len.as_nat())
    }

    /// Carry the saved_len <= view bound for the top frame across a push
    /// (old_self had wf; new view is longer).
    pub proof fn lemma_saved_len_le_view_from(&self, old_self: Self, k: int)
        requires
            old_self.wf(),
            self.frames@ == old_self.frames@,
            self.snapshots@ == old_self.snapshots@,
            self.diff_log@ == old_self.diff_log@,
            old_self.view().len() <= self.view().len(),
            (forall|j: int| 0 <= j < old_self.view().len() ==>
                #[trigger] self.view()[j] == old_self.view()[j]),
            0 <= k < self.frames@.len(),
            k + 1 == self.frames@.len(),
        ensures
            self.frame_inv_range_holds(k),
    {
        old_self.lemma_saved_len_le_view(k);
        assert(old_self.frame_inv_range_holds(k));
        // top frame: layer_above is view in both; agree on old prefix; the
        // uncaptured arm only reads view[j] for j < saved_len <= old view len.
    }

    pub fn pop(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
            // No live frames: pop in tracked mode after a mark would need
            // force_capture, which lives behind the M3b precondition that
            // pop is only callable when the frame stack is empty (or the
            // popped slot is beyond saved_len). For M3b, simplest is to
            // require no live frames.
            old(self).frames@.len() == 0,
        ensures
            self.wf(),
            old(self).view().len() == 0 ==> r is None && self.view() == old(self).view(),
            old(self).view().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).view()[old(self).view().len() - 1]
                &&& self.view() == old(self).view().drop_last()
            },
            self.snapshots_view() == old(self).snapshots_view(),
    {
        self.store.pop()
    }

    pub fn set(&mut self, i: I, value: T)
        requires
            old(self).wf(),
            i.as_nat() < old(self).view().len(),
            // M3b: `set` only modifies untracked slots or those already
            // captured. To keep the proof simple, restrict to the no-live-
            // frame case for now. A capturing set lands in M4.
            old(self).frames@.len() == 0,
        ensures
            self.wf(),
            self.view() == old(self).view().update(i.as_nat() as int, value),
            self.snapshots_view() == old(self).snapshots_view(),
    {
        self.store.set_raw(i, value);
    }

    /// Mark a snapshot point. Returns a token that can be passed to
    /// `restore` to roll back to the current state.
    ///
    /// M3b: only one live mark at a time. The precondition rejects nested
    /// marks; M4 will lift that.
    /// Mark a snapshot point, possibly nested. The new frame's stratum
    /// starts empty (diff_start == current diff_log.len()), so its
    /// frame_inv_range holds with the view as both layer and snapshot.
    /// The previously-top frame's stratum is unchanged (its upper bound
    /// was the diff log's end, which equals the new frame's diff_start),
    /// and its layer flips from `view` to the new `snapshots[top]`, which
    /// equals the view — so its frame_inv_range transfers.
    pub fn mark(&mut self) -> (token: VecToken)
        requires
            old(self).wf(),
            old(self).view().len() < I::max_nat(),
        ensures
            self.wf(),
            self.view() == old(self).view(),
            token.frame_idx == old(self).frames@.len(),
            self.frames@.len() == old(self).frames@.len() + 1,
            self.snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        proof {
            // saved_len <= view.len() for prepare_mark's precondition.
            if self.frames@.len() > 0 {
                self.lemma_saved_len_le_view((self.frames@.len() - 1) as int);
                self.lemma_diff_start_le_n((self.frames@.len() - 1) as int);
            }
        }

        let saved_len = self.store.len();
        let diff_start = self.diff_log.len();

        let ghost old_frames = self.frames@;
        let ghost old_snaps = self.snapshots@;
        let ghost old_view = self.view();

        self.store.prepare_mark(saved_len, self.diff_log.as_slice());

        self.snapshots = Ghost(self.snapshots@.push(old_view));
        self.frames.push(Frame { saved_len, diff_start });

        proof {
            let frames = self.frames@;
            let diffs = self.diff_log@;
            let snaps = self.snapshots@;
            let new_top = (frames.len() - 1) as int;  // == old_frames.len()

            // prepare_mark preserves view/diff_log/frames/snapshots (we set
            // snapshots & frames explicitly after); only the store's internal
            // capture flags changed, which the Vec invariant doesn't read.
            assert(self.view() == old_view);
            assert(diffs == old(self).diff_log@);
            assert(diff_start == diffs.len());

            // Re-establish the per-frame frame_inv_range for the new stack.
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), diffs, frames[k].diff_start as int,
                    self.stratum_end(k), snaps[k], frames[k].saved_len.as_nat())
            by {
                if k == new_top {
                    // New frame: stratum [diff_start, diff_start) is empty,
                    // layer == snapshot == view. All cells uncaptured ⇒
                    // view[j] == snap[j] trivially.
                    assert(self.stratum_end(k) == diffs.len());
                    assert(frames[k].diff_start == diffs.len());
                    assert(self.layer_above_at(k) == self.view());
                    assert(snaps[k] == old_view);
                } else if k + 1 == new_top {
                    // Previous top frame: stratum unchanged; layer flips from
                    // old view to snaps[new_top] == old_view. Equal, so the
                    // old frame_inv_range transfers.
                    assert(old(self).frame_inv_range_holds(k));
                    assert(old_frames[k] == frames[k]);
                    assert(old_snaps[k] == snaps[k]);
                    assert(self.stratum_end(k) == diffs.len());
                    assert(old(self).stratum_end(k) == diffs.len());
                    assert(self.layer_above_at(k) == snaps[k + 1]);
                    assert(snaps[k + 1] == old_view);
                    assert(old(self).layer_above_at(k) == old_view);
                } else {
                    // Deeper frames: stratum and layer (a surviving snapshot)
                    // unchanged.
                    assert(old(self).frame_inv_range_holds(k));
                    assert(old_frames[k] == frames[k]);
                    assert(old_snaps[k] == snaps[k]);
                    assert(self.layer_above_at(k) == snaps[k + 1]);
                    assert(old(self).layer_above_at(k) == old_snaps[k + 1]);
                    assert(self.stratum_end(k) == old(self).stratum_end(k));
                }
            }
        }

        VecToken { frame_idx: self.frames.len() - 1 }
    }

    /// Restore the vector to the state captured by `token`.
    ///
    /// M4 restore — to any frame_idx in range, across nested strata.
    ///
    /// The loop walks the diff log from `n` down to `frames[target].diff_start`,
    /// replaying each entry. By the `overlay` model, the result on the
    /// marked region `[0, saved_len_target)` equals
    /// `overlay(pre_view, diff_log, diff_start, n)`, which by the central
    /// lemma `lemma_snap_eq_overlay` equals `snapshots[target]`.
    pub fn restore(&mut self, token: VecToken)
        requires
            old(self).wf(),
            token.frame_idx < old(self).frames@.len(),
        ensures
            self.wf(),
            self.view() == old(self).snapshots_view()[token.frame_idx as int],
            self.frames@.len() == token.frame_idx as nat,
            self.snapshots_view() == old(self).snapshots_view().subrange(0, token.frame_idx as int),
    {
        let target_index = token.frame_idx;
        let target_frame = self.frames[target_index];
        let saved_len = target_frame.saved_len;
        let diff_start = target_frame.diff_start;

        let ghost pre_view = self.view();
        let ghost pre_diffs = self.diff_log@;
        let ghost snap_target = self.snapshots@[target_index as int];

        // The central lemma: overlay all strata [diff_start, n) onto the
        // pre-restore view reconstructs snap_target on its marked region.
        proof {
            self.lemma_snap_eq_overlay(target_index as int);
            self.lemma_saved_len_le_view(target_index as int);
            self.lemma_diff_start_le_n(target_index as int);
        }

        self.store.truncate(saved_len);

        // Loop invariant: data agrees, on [0, saved_len), with overlaying
        // the unapplied range [i, n) onto the truncated base. (The truncated
        // base equals pre_view's prefix [0, saved_len); entries with index
        // >= saved_len are no-ops there, by lemma_overlay_prefix_agnostic.)
        let ghost trunc_base = self.store.data();
        let n = self.diff_log.len();
        let mut i: usize = n;
        while i > diff_start
            invariant
                self.store.wf(),
                self.diff_log@ == pre_diffs,
                self.diff_log@.len() == n,
                self.frames@ == old(self).frames@,
                self.snapshots@ == old(self).snapshots@,
                diff_start <= i <= n,
                self.store.data().len() == saved_len.as_nat(),
                saved_len.as_nat() <= pre_view.len(),
                trunc_base.len() == saved_len.as_nat(),
                forall|j: int| 0 <= j < saved_len.as_nat() ==>
                    #[trigger] trunc_base[j] == pre_view[j],
                // The work done so far == overlay of the applied suffix.
                forall|j: int| 0 <= j < saved_len.as_nat() ==>
                    #[trigger] self.store.data()[j]
                        == overlay::<T, I>(trunc_base, pre_diffs, i as int, n as int)[j],
            decreases i,
        {
            i -= 1;
            let (old_val, idx) = self.diff_log[i];
            proof {
                lemma_overlay_len::<T, I>(trunc_base, pre_diffs, (i + 1) as int, n as int);
            }
            self.store.restore_entry(idx, &old_val, saved_len);
        }

        proof {
            // After loop: i == diff_start. data agrees with
            // overlay(trunc_base, diff_log, diff_start, n) on [0, saved_len).
            // trunc_base agrees with pre_view on [0, saved_len), so by
            // prefix-agnosticism overlay(trunc_base,..) agrees with
            // overlay(pre_view,..) there. And that equals snap_target by
            // the central lemma.
            lemma_overlay_prefix_agnostic::<T, I>(
                trunc_base, pre_view, pre_diffs,
                diff_start as int, n as int, saved_len.as_nat() as int);
            assert forall|j: int| 0 <= j < saved_len.as_nat() implies
                #[trigger] self.store.data()[j] == snap_target[j] by {}
        }

        let ghost old_frames = self.frames@;
        let ghost old_diffs = self.diff_log@;
        let ghost old_snaps = self.snapshots@;

        self.diff_log.truncate(diff_start);
        self.frames.truncate(target_index);
        self.snapshots = Ghost(self.snapshots@.subrange(0, target_index as int));

        proof {
            // view() now has length saved_len and agrees with snap_target
            // pointwise, so they're equal by extensionality.
            assert(self.view() =~= snap_target);

            // Re-establish wf for the truncated stack [0, target_index).
            let frames = self.frames@;
            let diffs = self.diff_log@;
            let snaps = self.snapshots@;

            assert(frames =~= old_frames.subrange(0, target_index as int));
            assert(snaps =~= old_snaps.subrange(0, target_index as int));
            assert(diffs =~= old_diffs.subrange(0, diff_start as int));
            assert(frames.len() == target_index as nat);
            assert(diffs.len() == diff_start as nat);

            // Each surviving frame's stratum and layer_above is preserved:
            //  - For k < target_index - 1: stratum [ds_k, ds_{k+1}) lies
            //    entirely below diff_start, so truncating the diff log to
            //    diff_start doesn't change it; layer_above is snaps[k+1],
            //    a surviving snapshot, unchanged.
            //  - For k == target_index - 1 (new top): its stratum upper
            //    bound was old frames[target].diff_start == diff_start ==
            //    new diff_log.len(), so stratum_end(k) is unchanged; its
            //    layer_above flips from old snaps[target] to the new view,
            //    but view == snap_target == old snaps[target], so the
            //    frame_inv_range content is identical.
            // Entries below diff_start are identical in old and new diff log.
            assert forall|m: int| 0 <= m < diff_start as int implies
                #[trigger] diffs[m] == old_diffs[m] by {}

            // Structural conjuncts for the new top frame (target_index - 1),
            // if the truncated stack is non-empty.
            if frames.len() > 0 {
                let top = (frames.len() - 1) as int;
                assert(top == target_index as int - 1);
                // new top diff_start <= new n (== diff_start):
                old(self).lemma_diff_start_monotone(top, target_index as int);
                assert(old_frames[top].diff_start <= old_frames[target_index as int].diff_start);
                // new top saved_len <= new view.len() (== saved_len_target):
                old(self).lemma_saved_len_monotone(top, target_index as int);
                assert(self.view().len() == saved_len.as_nat());
                assert(old_frames[target_index as int].saved_len.as_nat() == saved_len.as_nat());
            }

            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), diffs, frames[k].diff_start as int,
                    self.stratum_end(k), snaps[k], frames[k].saved_len.as_nat())
            by {
                // The old vec satisfied frame_inv_range for frame k (wf).
                assert(old(self).frame_inv_range_holds(k));
                assert(old_frames[k] == frames[k]);
                assert(old_snaps[k] == snaps[k]);
                let lo = frames[k].diff_start as int;
                // For surviving frames, stratum upper bound:
                //   k < top:  frames[k+1].diff_start (same as old, < diff_start)
                //   k == top: new diff_log.len() == diff_start
                //             == old frames[target].diff_start
                //             == old stratum_end(target_index - 1)
                let hi_new = self.stratum_end(k);
                let hi_old = old(self).stratum_end(k);
                if k + 1 < frames.len() {
                    assert(hi_new == frames[k + 1].diff_start as int);
                    assert(hi_old == old_frames[k + 1].diff_start as int);
                    assert(hi_new == hi_old);
                    assert(self.layer_above_at(k) == snaps[k + 1]);
                    assert(old(self).layer_above_at(k) == old_snaps[k + 1]);
                } else {
                    // new top frame: hi_new == new diff_log.len() == diff_start.
                    assert(hi_new == diff_start as int);
                    // old stratum_end(target_index - 1) == old frames[target].diff_start.
                    assert(hi_old == old_frames[(k + 1) as int].diff_start as int);
                    assert(hi_old == diff_start as int);
                    assert(self.layer_above_at(k) == self.view());
                    assert(self.view() == snap_target);
                    assert(snap_target == old_snaps[target_index as int]);
                    assert(old(self).layer_above_at(k) == old_snaps[k + 1]);
                }
                // Transfer frame_inv_range from old_diffs to new diffs:
                // they agree on [lo, hi_new) (which is below diff_start),
                // and layer + snap + saved_len coincide.
                assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                assert(hi_new == hi_old);
                // hi_old <= diff_start: it's old stratum_end(k) for a frame
                // k < target_index. For k+1 < target_index, monotonicity of
                // old diff_starts gives frames[k+1].diff_start <=
                // frames[target].diff_start == diff_start. For k+1 ==
                // target_index, hi_old == frames[target].diff_start == diff_start.
                assert(hi_old <= diff_start as int) by {
                    old(self).lemma_diff_start_le_n(target_index as int);
                    if k + 1 < frames.len() {
                        old(self).lemma_diff_start_monotone(k + 1, target_index as int);
                    }
                }
                assert(hi_new <= diff_start as int);
                lemma_frame_inv_range_local::<T, I>(
                    self.layer_above_at(k), old_diffs, diffs,
                    lo, hi_new, snaps[k], frames[k].saved_len.as_nat());
                // Surface the inline form wf's forall triggers on.
                assert(frame_inv_range::<T, I>(
                    self.layer_above_at(k), diffs, frames[k].diff_start as int,
                    self.stratum_end(k), snaps[k], frames[k].saved_len.as_nat()));
            }
        }
    }
}


} // verus!
