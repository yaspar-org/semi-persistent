// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Vec<T, I, S, const TRACK: bool>`: the headline semi-persistent vector.
//!
//! The full vector — `push`, `pop` (including into a marked region), `set`,
//! `get`, `mark`, `restore` — is verified at arbitrary mark-nesting depth,
//! with fork-history branch-cut safety. After `restore(token)`,
//! `view() == snapshots[token.frame_idx]`, where `snapshots` is a ghost stack
//! of deep copies recorded at each `mark()` and reconstructed on restore from
//! the sparse diff log (it is never stored at runtime).
//!
//! The well-formedness invariant is the declarative, pointwise `frame_cell_inv`
//! (see [`frame_cell_inv`]): for each marked cell `j`, its snapshot value lives
//! in exactly one place — the live view if untouched since the mark, or the
//! diff log if overwritten/popped — with first-write-wins giving at most one
//! diff entry per cell per frame.
//!
//! Full narrative, theorems, and proof architecture:
//! `doc/design/01-verification-design.md`.

use vstd::prelude::*;

verus! {

use crate::container_id::ContainerId;
use crate::diff_store::DiffStore;
use crate::fork_history::ForkHistory;
use crate::frame::Frame;
use crate::index_like::IndexLike;

/// Capacity-reclamation policy applied at `mark` time (parity with
/// production). The verus model treats both variants as observationally
/// inert: shrinking is a capacity hint that never changes `view()` or any
/// tracked sequence, so it carries no spec content.
#[derive(Copy, Clone)]
pub enum ShrinkPolicy {
    Never,
    IfOverallocated { factor: usize, headroom: usize },
}

/// Opaque token returned by `mark()`.
///
/// `frame_idx` is the reconstruction coordinate (which frame `restore` rolls
/// back to). `branch_id`/`depth` are the validity coordinates consumed by the
/// fork-history check (design doc §0.6): `branch_id` is the branch live at
/// mark time, `depth` the token's position along it. `container_id` rejects
/// cross-container use. `frame_idx` and `depth` are numerically equal at mark
/// but are DIFFERENT quantities (reconstruction index vs. validity depth) —
/// see 02-fork-history.md §0.5.
#[derive(Copy, Clone)]
pub struct VecToken {
    pub(crate) frame_idx: usize,
    pub(crate) branch_id: u32,
    pub(crate) depth: u32,
    pub(crate) container_id: ContainerId,
}

impl VecToken {
    /// The reconstruction coordinate (spec view; the exec field is
    /// `pub(crate)` — privacy closeout). Public contracts phrase frame
    /// positions through this.
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.frame_idx as nat
    }
}

/// Spec helper: there is some entry in `diffs` pointing at index `j`.
///
/// Used as the "captured" predicate in the declarative invariant.
pub open(crate) spec fn diff_has_index<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    j: nat,
) -> bool {
    exists|k: int| 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Some entry of `diffs` in `[lo, hi)` points at index `j` (range-scoped
/// `diff_has_index`; the replay loop's flag bookkeeping).
pub open(crate) spec fn diff_has_index_in<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    lo: int,
    hi: int,
    j: nat,
) -> bool {
    exists|k: int| lo <= k < hi
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// First-write-wins: each index appears at most once across the diff log.
///
/// Without this, multiple entries could disagree about a slot's marked
/// value and the invariant would be ambiguous. Production enforces this
/// via the per-slot capture flag.
pub open(crate) spec fn diffs_unique_indices<T, I: IndexLike>(
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
pub open(crate) spec fn frame_inv<T, I: IndexLike>(
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
pub open(crate) spec fn overlay<T, I: IndexLike>(
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
pub(crate) proof fn lemma_overlay_len<T, I: IndexLike>(
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
pub(crate) proof fn lemma_overlay_uncaptured<T, I: IndexLike>(
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
pub(crate) proof fn lemma_overlay_captured<T, I: IndexLike>(
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

/// Lowest-position-in-range wins. If `p` is the LOWEST position in `[lo, hi)`
/// whose entry hits `j` (entries before `p` miss `j`), then overlay sets
/// `base[j]` to `diffs[p].0` — even if higher positions in `[lo, hi)` also
/// hit `j`. This generalizes `lemma_overlay_captured` (which needs global
/// uniqueness in the range) to the cross-stratum case where the same index
/// recurs in different strata: the deepest (= lowest-position) stratum's
/// entry wins, which is exactly what reverse-replay computes.
pub(crate) proof fn lemma_overlay_lowest<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, p: int, j: int,
)
    requires
        0 <= j < base.len(),
        lo <= p < hi,
        0 <= p < diffs.len(),
        lo >= 0,
        hi <= diffs.len(),
        diffs[p].1.as_nat() == j as nat,
        // p is the LOWEST hitter of j in [lo, hi): earlier positions miss j.
        forall|q: int| lo <= q < p ==> (#[trigger] diffs[q]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == diffs[p].0,
    decreases hi - lo,
{
    let prev = overlay::<T, I>(base, diffs, lo + 1, hi);
    lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    if p == lo {
        // diffs[lo] hits j; it is applied OUTERMOST (last), so its value is
        // the final value at j regardless of what [lo+1, hi) did to prev[j].
    } else {
        // diffs[lo] does not hit j (lo < p and p is the lowest hitter).
        // p is still the lowest hitter in [lo+1, hi). By IH overlay(lo+1,hi)[j]
        // == diffs[p].0, and the outermost update at lo (index != j) leaves j.
        lemma_overlay_lowest::<T, I>(base, diffs, lo + 1, hi, p, j);
    }
}

/// If no entry in the lower part `[lo, mid)` hits `j`, then overlaying the
/// whole `[lo, hi)` agrees at `j` with overlaying just the upper part
/// `[mid, hi)`. (The lower-part replay, applied outermost, leaves `j` alone.)
/// Used by the flat central lemma's uncaptured/recurse step.
pub(crate) proof fn lemma_overlay_uncaptured_prefix<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, mid: int, hi: int, j: int,
)
    requires
        0 <= lo <= mid <= hi <= diffs.len(),
        0 <= j < base.len(),
        forall|q: int| lo <= q < mid ==> (#[trigger] diffs[q]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j]
            == overlay::<T, I>(base, diffs, mid, hi)[j],
    decreases mid - lo,
{
    lemma_overlay_len::<T, I>(base, diffs, mid, hi);
    if lo >= mid {
        // [lo, mid) empty ⇒ both sides identical.
    } else {
        // Peel lo: overlay(lo,hi) = step(diffs[lo], overlay(lo+1,hi)). By IH
        // overlay(lo+1,hi)[j] == overlay(mid,hi)[j]; diffs[lo] misses j so the
        // outermost step leaves j.
        lemma_overlay_uncaptured_prefix::<T, I>(base, diffs, lo + 1, mid, hi, j);
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    }
}

/// Bridge between subrange-position existential and absolute-range
/// `captured_in_range`. If `sub == diffs.subrange(lo, hi)`, then
/// "some sub[kk] hits j" iff "some diffs[k] in [lo, hi) hits j".
pub(crate) proof fn lemma_captured_subrange<T, I: IndexLike>(
    diffs: Seq<(T, I)>, sub: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        sub == diffs.subrange(lo, hi),
    ensures
        (exists|kk: int| 0 <= kk < sub.len()
            && (#[trigger] sub[kk]).1.as_nat() == j)
        == captured_in_range::<T, I>(diffs, lo, hi, j),
{
    if exists|kk: int| 0 <= kk < sub.len() && (#[trigger] sub[kk]).1.as_nat() == j {
        let kk = choose|kk: int| 0 <= kk < sub.len() && (#[trigger] sub[kk]).1.as_nat() == j;
        // sub[kk] == diffs[lo + kk], and lo <= lo+kk < hi.
        assert(sub[kk] == diffs[lo + kk]);
        assert(lo <= lo + kk < hi);
    }
    if captured_in_range::<T, I>(diffs, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < diffs.len()
            && (#[trigger] diffs[k]).1.as_nat() == j;
        // diffs[k] == sub[k - lo], and 0 <= k-lo < sub.len().
        assert(sub[k - lo] == diffs[k]);
        assert(0 <= k - lo < sub.len());
    }
}

/// Appending at most one entry whose index is `bound` (the popped slot) to
/// the top stratum doesn't change captured-status of any OTHER index `j`
/// (`j != bound`). Used by `pop` into the marked region: the capture append hits only the
/// popped index, so every surviving cell's bridge/captured arm is preserved.
/// `diffs` is either `old_diffs` (no-op capture) or `old_diffs.push(e)` with
/// `e.1.as_nat() == bound`.
pub(crate) proof fn lemma_captured_in_range_append_other<T, I: IndexLike>(
    old_diffs: Seq<(T, I)>, diffs: Seq<(T, I)>, lo: int, j: nat, bound: nat,
)
    requires
        j != bound,
        lo <= old_diffs.len(),
        diffs == old_diffs
            || (diffs.len() == old_diffs.len() + 1
                && diffs.subrange(0, old_diffs.len() as int) == old_diffs
                && (#[trigger] diffs[old_diffs.len() as int]).1.as_nat() == bound),
    ensures
        captured_in_range::<T, I>(diffs, lo, diffs.len() as int, j)
            == captured_in_range::<T, I>(old_diffs, lo, old_diffs.len() as int, j),
{
    if diffs == old_diffs {
        return;
    }
    let n = old_diffs.len() as int;
    // forward: a hitter in diffs is at some position p; if p == n it has
    // index bound != j, contradiction; else p < n and diffs[p]==old_diffs[p].
    if captured_in_range::<T, I>(diffs, lo, diffs.len() as int, j) {
        let p = choose|p: int| lo <= p < diffs.len() && 0 <= p < diffs.len()
            && (#[trigger] diffs[p]).1.as_nat() == j;
        if p < n {
            assert(diffs[p] == old_diffs[p]) by {
                assert(diffs.subrange(0, n)[p] == old_diffs[p]);
            }
        } else {
            assert(p == n);
            assert(diffs[p].1.as_nat() == bound);  // contradicts == j
        }
    }
    // backward: an old hitter at p < n survives at the same position.
    if captured_in_range::<T, I>(old_diffs, lo, n, j) {
        let p = choose|p: int| lo <= p < n && 0 <= p < old_diffs.len()
            && (#[trigger] old_diffs[p]).1.as_nat() == j;
        assert(diffs[p] == old_diffs[p]) by {
            assert(diffs.subrange(0, n)[p] == old_diffs[p]);
        }
    }
}

/// `frame_inv_range` over `[lo, hi)` depends only on the diff entries in
/// that range. If two diff sequences agree pointwise on `[lo, hi)` (and are
/// both long enough), the predicate holds for one iff for the other.
pub(crate) proof fn lemma_frame_inv_range_local<T, I: IndexLike>(
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
    // Per-cell two-arm: frame_cell_inv reads only entries in [lo, hi) plus
    // `above`/`snap` (shared). The named predicate gives a clean function-
    // application trigger that re-assembles into frame_inv_range's forall.
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, db, lo, hi, snap, j)
    by {
        lemma_frame_cell_inv_local::<T, I>(above, da, db, lo, hi, snap, j);
    }
}

/// `frame_cell_inv` for cell `j` depends only on entries in `[lo, hi)`. If
/// `da`/`db` agree there, the per-cell invariant transfers. Isolated so the
/// quantifier instantiation is local and the equality is by function
/// congruence on `captured_in_range` + the witness entry.
pub(crate) proof fn lemma_frame_cell_inv_local<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, j: int,
)
    requires
        0 <= lo <= hi <= da.len(),
        hi <= db.len(),
        forall|m: int| lo <= m < hi ==> #[trigger] da[m] == db[m],
        frame_cell_inv::<T, I>(above, da, lo, hi, snap, j),
    ensures
        frame_cell_inv::<T, I>(above, db, lo, hi, snap, j),
{
    // captured_in_range agrees across da/db (reads entries in [lo, hi)).
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
        // carry the witness entry from da to db (same position, equal entry).
        let w = choose|k: int| lo <= k < hi
            && (#[trigger] da[k]).1.as_nat() == j as nat && da[k].0 == snap[j];
        assert(da[w] == db[w]);
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
pub(crate) proof fn lemma_overlay_prefix_agnostic<T, I: IndexLike>(
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
pub(crate) proof fn lemma_overlay_split<T, I: IndexLike>(
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
pub open(crate) spec fn captured_in_range<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int, j: nat,
) -> bool {
    exists|k: int| lo <= k < hi && 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Per-cell two-arm invariant for cell `j` of stratum `[lo, hi)`.
///
/// Factored into a named predicate (rather than inlined in the forall) so
/// the `forall|j|` in `frame_inv_range` has a clean function-application
/// trigger that Verus can re-assemble reliably across diff-log changes.
///
/// Coverage-aware uncaptured arm: an uncaptured cell `j` must be *present*
/// in `above` (`j < above.len()`) and hold the snapshot value. Equivalently,
/// every cell `j` in `[above.len(), saved_len)` — popped out of `above` —
/// must be captured. That's what lets `restore` regrow the popped region with
/// `resize_default` and overwrite every filler back to `snap[j]`.
pub open(crate) spec fn frame_cell_inv<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, j: int,
) -> bool {
    if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
        &&& (j as nat) < above.len()
        &&& above[j] == snap[j]
    } else {
        exists|k: int| lo <= k < hi
            && (#[trigger] diffs[k]).1.as_nat() == j as nat
            && diffs[k].0 == snap[j]
    }
}

/// Range-form of the two-arm frame invariant for one stratum `[lo, hi)`.
/// `above` is the layer above (snapshot[k+1] or the view); `snap` is this
/// stratum's snapshot. Stated over the diff-log range directly.
///
/// Note: no `saved_len <= above.len()` requirement — `above` (the view, for
/// the top frame) may be shorter than `saved_len` in the post-pop state. The
/// coverage clause inside `frame_cell_inv` handles the popped cells.
pub open(crate) spec fn frame_inv_range<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
) -> bool {
    &&& snap.len() == saved_len
    &&& (forall|k: int| lo <= k < hi ==>
            (#[trigger] diffs[k]).1.as_nat() < saved_len)
    &&& (forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b ==>
            (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat())
    &&& (forall|j: int| 0 <= j < saved_len as int ==>
            #[trigger] frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j))
}

/// Instantiate `frame_inv_range`'s per-cell forall at one cell `j`. The
/// forall's trigger is `frame_cell_inv(...)`, so this is just an explicit
/// hook for call sites that need the per-cell fact in hand.
pub(crate) proof fn lemma_frame_inv_arm_at<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat, j: int,
)
    requires
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
        0 <= j < saved_len as int,
    ensures
        frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j),
{
}

/// The per-stratum bridge: if a diff-log range `[lo, hi)` satisfies the
/// two-arm `frame_inv` relative to `above` and `snap` (stated directly over
/// the range), then overlaying that range onto `above` reproduces `snap`
/// on `[0, saved_len)`.
///
/// Hypotheses mirror `frame_inv` + the structural conditions, but phrased
/// over the diff-log range rather than an extracted subrange.
pub(crate) proof fn lemma_overlay_eq_snap<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        // The base is already full-length (restore resizes to saved_len
        // before replay), so the overwrite-only overlay reaches every cell.
        saved_len <= above.len(),
        // Full frame_inv_range bundles snap.len, index-bound, uniqueness, and
        // the per-cell two-arm — all needed below.
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
    ensures
        forall|j: int| 0 <= j < saved_len as int ==>
            #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j],
{
    lemma_overlay_len::<T, I>(above, diffs, lo, hi);
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j]
    by {
        assert(frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j));
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
            assert(captured_in_range::<T, I>(diffs, lo, hi, j as nat));
            assert((j as nat) < above.len());  // from saved_len <= above.len()
            let p = choose|k: int| lo <= k < hi
                && (#[trigger] diffs[k]).1.as_nat() == j as nat
                && diffs[k].0 == snap[j];
            lemma_overlay_captured::<T, I>(above, diffs, lo, hi, p, j);
        }
    }
}

/// Semi-persistent vector parameterized by storage backend `S` and index
/// type `I`. `TRACK` compiles out all tracking when false.
pub struct Vec<T, I, S, const TRACK: bool = true>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub(crate) store: S,
    pub(crate) diff_log: std::vec::Vec<(T, I)>,
    pub(crate) frames: std::vec::Vec<Frame<I>>,
    /// The saved_len of the topmost (active) frame, cached for the hot path.
    /// `I::min()` when the stack is empty. Mirrors production.
    pub(crate) active_saved_len: I,
    /// Branching genealogy for token-validity / branch-cut safety (M5).
    pub(crate) forks: ForkHistory,
    /// Per-container identity; rejects cross-container token use.
    pub(crate) id: ContainerId,
    pub(crate) phantom: core::marker::PhantomData<(T, I)>,
    /// Ghost stack of deep copies. `snapshots[k]` is `view()` at the
    /// moment frame `k` was pushed. Always `snapshots.len() == frames.len()`.
    pub(crate) snapshots: Ghost<Seq<Seq<T>>>,
}

impl<T, I, S, const TRACK: bool> Vec<T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// Public spec view: the abstract sequence of stored values.
    pub open(crate) spec fn view(&self) -> Seq<T> {
        self.store.data()
    }

    /// Snapshot stack (ghost).
    pub open(crate) spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Frame-stack depth (spec twin of `depth()`). Public contracts phrase
    /// frame counts through this — the `frames` field is `pub(crate)`
    /// (privacy closeout).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.frames@.len()
    }

    /// Diff-log length (spec twin of `diff_log_len()`).
    pub open(crate) spec fn diff_log_len_spec(&self) -> nat {
        self.diff_log@.len()
    }

    /// Lifetime restore count (fork-history origins length). Public contracts
    /// phrase the `u32` fork headroom through this.
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.forks.origins@.len()
    }

    /// Token validity (design doc §0.6): same container AND on the live branch
    /// path at a depth within that branch's bound. This is the M5 precondition
    /// of `restore` — separate from the structural `frame_idx < frames.len()`
    /// reconstruction precondition (design §0.5). `current_depth` is the live
    /// depth `frames.len()`.
    pub open(crate) spec fn is_token_valid_spec(&self, token: VecToken) -> bool {
        &&& token.container_id.id() == self.id.id()
        &&& crate::fork_history::fork_valid(
                self.forks.origins@,
                self.forks.current_branch_id as nat,
                self.frames@.len() as nat,
                token.branch_id as nat,
                token.depth as nat)
    }

    /// "Restorable now" (migration plan 2.2): the FULL runtime-checkable
    /// precondition of `restore`. This is what the public `is_valid_token`
    /// answers — one public notion of validity: "would `restore(token)`
    /// succeed right now?". Strictly stronger than `is_token_valid_spec`
    /// (identity + genealogy), adding frame liveness (the consumed-token
    /// case: a restored token's branch can remain on-path while its frame is
    /// gone), the TRACK gate, and both counter headrooms.
    pub open(crate) spec fn is_restorable_spec(&self, token: VecToken) -> bool {
        &&& TRACK
        &&& self.is_token_valid_spec(token)
        &&& token.frame_idx < self.frames@.len()
        &&& self.frames@.len() < u32::MAX
        &&& self.forks.origins@.len() + 1 <= u32::MAX
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
    pub open(crate) spec fn layer_above_at(&self, k: int) -> Seq<T> {
        if k + 1 < self.frames@.len() {
            self.snapshots@[k + 1]
        } else {
            self.view()
        }
    }

    /// End of frame `k`'s stratum.
    pub open(crate) spec fn stratum_end(&self, k: int) -> int {
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
    /// The snapshot-reconstruction core of `wf`: store well-formedness,
    /// parallel stack lengths, frame bookkeeping (diff_start/saved_len
    /// monotone, snapshot lengths), and the per-frame `frame_inv_range`.
    ///
    /// Crucially this does NOT include the capture-flag bridge or the
    /// `store.captured().len() == view.len()` tie. `resize_default` (used by
    /// restore to regrow a popped view) PRESERVES `wf_for_snap` — growing the
    /// view with default fillers only touches captured cells (which the
    /// frame_inv_range captured arm ignores) — but breaks the bridge. So the
    /// central reconstruction lemma is stated over `wf_for_snap`, lettng
    /// restore invoke it on the resized (non-`wf`, but `wf_for_snap`) state.
    pub open(crate) spec fn wf_for_snap(&self) -> bool {
        let frames = self.frames@;
        let diffs = self.diff_log@;
        let snaps = self.snapshots@;
        let n = diffs.len();

        &&& self.store.wf()
        &&& snaps.len() == frames.len()
        // TRACK=false ⟹ no frames, ever: `mark` (the only frame-pusher)
        // requires TRACK. Carrying it in wf lets the exec hot paths gate
        // their tracking work on `TRACK &&` — a const-generic the compiler
        // folds away at monomorphization (production-parity erasure).
        &&& (!TRACK ==> frames.len() == 0)
        &&& (frames.len() == 0 ==> n == 0)
        &&& (frames.len() > 0 ==> frames[0].diff_start == 0)
        &&& (frames.len() > 0 ==> frames[(frames.len() - 1) as int].diff_start <= n)
        // NOTE (pop into marked region): the top-frame "view is full"
        // (`frames[top].saved_len <= view.len()`) and `saved_len` monotonicity
        // clauses are DELIBERATELY ABSENT. After a pop into the marked region
        // the view is shorter than saved_len; and `mark` after a deep pop
        // records a short length, so a newer frame can have a SMALLER
        // saved_len than its parent. Both facts are replaced by the per-frame
        // COVERAGE encoded in `frame_cell_inv`'s uncaptured arm
        // (uncaptured j ==> j < layer_above.len()), which is all the
        // reconstruction proof needs. `diff_start` monotonicity DOES still
        // hold (the diff log only grows) and is kept.
        &&& (forall|k: int| 0 <= k && k + 1 < frames.len() ==>
                #[trigger] frames[k].diff_start <= #[trigger] frames[k + 1].diff_start)
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

    pub open(crate) spec fn wf(&self) -> bool {
        let frames = self.frames@;
        let diffs = self.diff_log@;

        &&& self.wf_for_snap()
        // active_saved_len caches the top frame's saved_len.
        &&& (frames.len() == 0 ==> self.active_saved_len == I::min_spec())
        &&& (frames.len() > 0 ==>
                self.active_saved_len == frames[(frames.len() - 1) as int].saved_len)
        // Capture-flag bridge: store.captured()[j] is set iff j has been
        // captured in the TOP stratum. Only meaningful when a frame is live.
        // Restricted to j < min(active_saved_len, view.len()): the store only
        // tracks flags for *present* cells. Cells popped out of the marked
        // region (j in [view.len(), active)) have no store flag — their
        // captured-ness lives in the diff log and is enforced by the coverage
        // clause inside frame_cell_inv.
        &&& self.store.captured().len() == self.view().len()
        &&& (frames.len() > 0 ==>
                forall|j: int|
                    0 <= j < self.active_saved_len.as_nat() && j < self.view().len() ==>
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(
                            diffs,
                            frames[(frames.len() - 1) as int].diff_start as int,
                            diffs.len() as int,
                            j as nat))
        // NO STRAY FLAGS (the sparse-clear enabler, production's implicit
        // invariant): every set capture flag lies in the trackable region —
        // below the active saved length with a live frame — where the bridge
        // above ties it to a diff-log entry. Flags never survive outside it:
        // capture/force_capture guard on i < saved_len, mark_captured fires
        // only for reentered (in-marked) slots, prepare_mark/finish_restore
        // (re)build from diff entries, push appends false, pop/truncate
        // retire. This is what lets `prepare_mark` clear O(diffs) slots
        // instead of sweeping O(len).
        &&& (TRACK ==> forall|j: int| 0 <= j < self.view().len()
                && #[trigger] self.store.captured()[j]
                ==> frames.len() > 0 && j < self.active_saved_len.as_nat())
        // Fork history is well-formed (parent-decreasing; current branch a real
        // branch). Independent of the snapshot stack — validity is a separate
        // predicate, not a structural snapshot invariant (design §0.5).
        &&& self.forks.wf()
    }

    /// Every frame's diff_start is `<= diff_log.len()`. Follows from
    /// monotonicity plus the top frame's bound, by upward induction.
    pub(crate) proof fn lemma_diff_start_le_n(&self, k: int)
        requires
            self.wf_for_snap(),
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
    pub(crate) proof fn lemma_diff_start_monotone(&self, a: int, b: int)
        requires
            self.wf_for_snap(),
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

    // NOTE (pop into marked region): `lemma_saved_len_le_active` ("top frame is the
    // longest"), `lemma_saved_len_monotone` ("saved_len non-decreasing"), and
    // `lemma_saved_len_le_view` ("every saved_len <= view.len()") were DELETED
    // here. All three are FALSE once pop can shrink the view into the marked
    // region and `mark` can record a short length. They are replaced
    // everywhere by the per-frame coverage in `frame_cell_inv`'s uncaptured
    // arm (uncaptured j ==> j < layer_above.len()), which is exactly the bound
    // those lemmas used to supply and which holds unconditionally.

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
    /// FLAT central lemma (per-cell, base-parametric, target-clamped).
    ///
    /// For a single cell `j < saved_k`, overlaying the whole tail range
    /// `[diff_start_k, n)` onto `base` reconstructs `snapshots[k][j]`. Unlike
    /// the layered `lemma_snap_eq_overlay`, this never builds intermediate
    /// snapshot sequences and never needs `saved_len` monotonicity: a cell
    /// captured at some level is pinned by `lemma_overlay_lowest` (base-
    /// independent, lowest-in-range = deepest stratum wins); an uncaptured
    /// cell recurses one frame up (coverage gives `j < layer_above.len()`),
    /// terminating at the top frame where `layer_above == view` and the base
    /// agrees with the view on `j`.
    ///
    /// `base` requirements: long enough (`j < base.len()`) and agreeing with
    /// the view on the shared prefix — exactly what `resize_default` gives
    /// restore.
    pub(crate) proof fn lemma_cell_eq_overlay(&self, base: Seq<T>, k: int, j: int)
        requires
            self.wf_for_snap(),
            0 <= k < self.frames@.len(),
            0 <= j < self.frames@[k].saved_len.as_nat(),
            (j as nat) < base.len(),
            // base agrees with the view on the shared prefix
            forall|m: int| 0 <= m < base.len() && m < self.view().len()
                ==> #[trigger] base[m] == self.view()[m],
        ensures
            overlay::<T, I>(
                base, self.diff_log@,
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
        let mid = self.stratum_end(k);
        let saved = frames[k].saved_len.as_nat();
        self.lemma_diff_start_le_n(k);
        // Bounds: lo <= mid <= n.
        if k + 1 < frames.len() {
            self.lemma_diff_start_le_n(k + 1);
            assert(frames[k].diff_start <= frames[k + 1].diff_start);  // monotone (adjacent)
            assert(mid == frames[k + 1].diff_start as int);
        } else {
            assert(mid == n);
        }
        assert(lo <= mid <= n);
        // stratum k's per-cell invariant at j (from wf_for_snap).
        lemma_frame_inv_arm_at::<T, I>(
            self.layer_above_at(k), diffs, lo, mid, snaps[k], saved, j);

        // frame_inv_range for stratum k (incl. its uniqueness conjunct).
        assert(frame_inv_range::<T, I>(self.layer_above_at(k), diffs, lo, mid, snaps[k], saved));
        if captured_in_range::<T, I>(diffs, lo, mid, j as nat) {
            // Captured in stratum k. The captured arm gives an entry p in
            // [lo, mid) holding snap_k[j]. By stratum-k uniqueness, p is the
            // ONLY hitter of j in [lo, mid), hence the lowest hitter in the
            // whole tail [lo, n) (stratum k = [lo, mid) is the lowest part;
            // deeper strata [mid, n) sit above). lemma_overlay_lowest pins it.
            let p = choose|q: int| lo <= q < mid
                && (#[trigger] diffs[q]).1.as_nat() == j as nat
                && diffs[q].0 == snaps[k][j];
            assert(lo <= p < mid && diffs[p].1.as_nat() == j as nat);
            assert(forall|q: int| lo <= q < p ==> (#[trigger] diffs[q]).1.as_nat() != j as nat) by {
                // uniqueness in [lo, mid): a second hitter q != p contradicts.
                assert forall|q: int| lo <= q < p implies (#[trigger] diffs[q]).1.as_nat() != j as nat by {
                    if diffs[q].1.as_nat() == j as nat {
                        // q, p both in [lo, mid), q != p, same index ⇒ violates
                        // frame_inv_range's uniqueness conjunct.
                        assert(q != p);
                    }
                }
            }
            lemma_overlay_lowest::<T, I>(base, diffs, lo, n, p, j);
        } else {
            // Uncaptured in stratum k. Coverage ⇒ j < layer_above.len() and
            // layer_above[j] == snap_k[j]. Recurse / terminate.
            if k + 1 < frames.len() {
                // layer_above == snaps[k+1]; recurse at k+1 over [mid, n).
                assert(self.layer_above_at(k) == snaps[k + 1]);
                assert((j as nat) < snaps[k + 1].len());
                assert(snaps[k + 1][j as int] == snaps[k][j as int]);
                assert(mid == frames[k + 1].diff_start as int);
                self.lemma_cell_eq_overlay(base, k + 1, j);
                // overlay over [mid, n) gives snap_{k+1}[j] == snap_k[j].
                // Extend to [lo, n): !captured_in_range(lo,mid,j) is exactly
                // "no q in [lo,mid) hits j", so the [lo,mid) prefix leaves j.
                assert forall|q: int| lo <= q < mid implies
                    (#[trigger] diffs[q]).1.as_nat() != j as nat by {
                    if diffs[q].1.as_nat() == j as nat {
                        assert(0 <= q < diffs.len());  // q < mid <= n
                        assert(captured_in_range::<T, I>(diffs, lo, mid, j as nat));
                    }
                }
                lemma_overlay_uncaptured_prefix::<T, I>(base, diffs, lo, mid, n, j);
            } else {
                // Top frame: layer_above == view, j < view.len(), and
                // base[j] == view[j] == snap_k[j]. No entry in [lo, n) hits j.
                assert(self.layer_above_at(k) == self.view());
                assert((j as nat) < self.view().len());
                assert(self.view()[j as int] == snaps[k][j as int]);
                assert(mid == n);
                lemma_overlay_uncaptured::<T, I>(base, diffs, lo, n, j);
            }
        }
    }


    /// "Untracked" state: no marks are live. Production compiles out tracking
    /// when `TRACK == false`; the verus model instead proves that whenever the
    /// frame stack is empty there is ZERO tracking storage and operations are
    /// pure `std::Vec` operations on the view. (`mark` is the only way to make
    /// the stack non-empty, so a vector that is never marked stays untracked.)
    pub open(crate) spec fn untracked(&self) -> bool {
        self.frames@.len() == 0
    }

    /// No tracking overhead while untracked: `wf` already forces an empty diff
    /// log when the frame stack is empty, so an unmarked vector carries no
    /// diff entries. This is the TRACK=false guarantee at the model level.
    pub(crate) proof fn lemma_untracked_no_overhead(&self)
        requires self.wf(), self.untracked(),
        ensures self.diff_log@.len() == 0,
    {
        // Directly from wf_for_snap's `frames.len()==0 ==> diff_log.len()==0`.
    }

    /// Observational equivalence to `std::Vec` while untracked: push appends,
    /// set updates, pop drops the last element — exactly the std operations on
    /// the view — AND the vector stays untracked with no diff log. These are
    /// thin wrappers asserting the equivalence explicitly; the heavy lifting is
    /// in push/set/pop's own contracts, which hold for ALL states.
    pub fn push_untracked(&mut self, value: T)
        requires
            old(self).wf(), old(self).untracked(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(), final(self).untracked(),
            final(self).view() == old(self).view().push(value),   // std::Vec::push
            final(self).diff_log_len_spec() == 0,                   // no overhead
    {
        self.push(value);
        proof { self.lemma_untracked_no_overhead(); }
    }

    pub fn pop_untracked(&mut self) -> (r: Option<T>)
        requires old(self).wf(), old(self).untracked(),
        ensures
            final(self).wf(), final(self).untracked(),
            old(self).view().len() == 0 ==> r is None && final(self).view() == old(self).view(),
            old(self).view().len() > 0 ==> r == Some(old(self).view().last())
                && final(self).view() == old(self).view().drop_last(),   // std::Vec::pop
            final(self).diff_log_len_spec() == 0,                         // no overhead
    {
        let r = self.pop();
        proof { self.lemma_untracked_no_overhead(); }
        r
    }

    pub fn set_untracked(&mut self, i: I, value: T)
        requires
            old(self).wf(), old(self).untracked(),
            i.as_nat() < old(self).view().len(),
        ensures
            final(self).wf(), final(self).untracked(),
            final(self).view() == old(self).view().update(i.as_nat() as int, value),  // std update
            final(self).diff_log_len_spec() == 0,                                      // no overhead
    {
        self.set_index(i, value);
        proof { self.lemma_untracked_no_overhead(); }
    }

    #[inline(always)]
    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        self.store.len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() == 0),
    {
        self.store.is_empty()
    }

    #[inline(always)]
    pub fn get_index(&self, i: I) -> (v: T)
        requires
            self.wf(),
            i.as_nat() < self.view().len(),
        ensures v == self.view()[i.as_nat() as int],
    {
        self.store.get(i)
    }

    /// Build an empty tracked vector over a freshly-empty store. Mirrors
    /// production's `with_store`. The store must be well-formed and empty
    /// (no data, no capture flags) — the concrete `new()` of each backend
    /// supplies that.
    pub fn with_store(store: S) -> (v: Self)
        requires
            store.wf(),
            store.data().len() == 0,
        ensures
            v.wf(),
            v.view().len() == 0,
            v.snapshots_view().len() == 0,
    {
        proof { store.lemma_wf_captured_len(); }  // captured().len() == 0
        let v = Vec {
            store,
            diff_log: std::vec::Vec::new(),
            frames: std::vec::Vec::new(),
            active_saved_len: <I as IndexLike>::min(),
            forks: ForkHistory::new(),
            id: ContainerId::new(),
            phantom: core::marker::PhantomData,
            snapshots: Ghost(Seq::empty()),
        };
        proof {
            I::lemma_min_as_nat();
            assert(v.active_saved_len == I::min_spec());
            assert(v.frames@.len() == 0);
            assert(v.snapshots@.len() == 0);
        }
        v
    }

    /// Capacity reclamation (production parity). `Never` is a no-op;
    /// `IfOverallocated` asks the store to shrink its backing capacity. Both
    /// are observationally inert: `shrink_if` preserves `data()`/`captured()`,
    /// so `view()`, `wf`, and all tracked sequences are unchanged. (The
    /// production diff_log capacity hint is omitted — it's a pure allocator
    /// hint with no effect on `diff_log@`.)
    fn maybe_shrink(&mut self, policy: ShrinkPolicy)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).diff_log@ == old(self).diff_log@,
            final(self).frames@ == old(self).frames@,
            final(self).snapshots@ == old(self).snapshots@,
            final(self).active_saved_len == old(self).active_saved_len,
            final(self).forks == old(self).forks,
    {
        match policy {
            ShrinkPolicy::Never => {}
            ShrinkPolicy::IfOverallocated { factor, headroom } => {
                self.store.shrink_if(factor, headroom);
                // Production parity: the same overallocation check applies to
                // the diff log at mark time (shrink-at-mark ratcheting).
                // Observably inert (contract: element sequence unchanged).
                crate::parallel_store::shrink_vec_capacity(
                    &mut self.diff_log, factor, headroom);
            }
        }
        proof {
            // shrink_if preserves data()/captured-under-TRACK; all other
            // fields untouched. Every wf conjunct that reads captured() is
            // TRACK-guarded (frames empty otherwise), so wf transfers.
            assert(self.view() == old(self).view());
            if TRACK {
                assert(self.store.captured() == old(self).store.captured());
                // no-stray-flags transfers pointwise (same flags, same frames).
                assert forall|j: int| 0 <= j < self.view().len()
                    && #[trigger] self.store.captured()[j]
                    implies self.frames@.len() > 0
                        && j < self.active_saved_len.as_nat() by {
                    assert(old(self).store.captured()[j]);
                }
            } else {
                // TRACK=false: frames pinned empty by wf, so every
                // frame-quantified conjunct is vacuous; the one
                // unconditional captured() fact (its length) comes from the
                // trait's wf lemma, not from pointwise preservation.
                assert(self.frames@.len() == 0);
                self.store.lemma_wf_captured_len();
            }
            assert(self.diff_log@ == old(self).diff_log@);
            assert(self.frames@ == old(self).frames@);
            assert(self.snapshots@ == old(self).snapshots@);
            assert forall|k: int| 0 <= k < self.frames@.len() implies
                self.layer_above_at(k) == old(self).layer_above_at(k)
                && self.stratum_end(k) == old(self).stratum_end(k) by {}
        }
    }

    /// Current frame-stack depth (number of live marks). Mirrors production.
    pub fn depth(&self) -> (d: usize)
        requires self.wf(),
        ensures d == self.depth_spec(),
    {
        self.frames.len()
    }

    /// Number of entries in the diff log (production parity). The bounded-pop
    /// contract is observable through this: within a frame, first-write-wins
    /// keeps the log at most one entry per captured index, so a pop/push loop
    /// cannot grow it (see tests/compat_bounded_pop.rs).
    pub fn diff_log_len(&self) -> (n: usize)
        ensures n == self.diff_log_len_spec(),
    {
        self.diff_log.len()
    }

    /// Contiguous read access to the raw values when the backend stores them
    /// contiguously: `Some` for `ParallelStore`, `None` for `InlineStore`
    /// (production parity — the backend-specific fast path).
    pub fn as_slice(&self) -> (r: Option<&[T]>)
        ensures r matches Some(s) ==> s@ == self.view(),
    {
        self.store.as_slice()
    }

    /// How many more `restore`s this container can accept before the
    /// fork-history branch counter saturates `u32`.
    ///
    /// Each `restore` appends one (never-reclaimed) fork-history origin, so the
    /// lifetime restore count is `forks.origins.len()`, capped at `u32::MAX`.
    /// This returns the remaining headroom (saturating at 0); while it is `> 0`,
    /// `restore`'s `origins.len() + 1 <= u32::MAX` precondition holds.
    /// (`u32::MAX ~ 4.29e9`, so this is not a practical concern, but the query
    /// lets a caller check.)
    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.fork_count_spec() < u32::MAX ==>
                r as nat == (u32::MAX - self.fork_count_spec()) as nat,
            self.fork_count_spec() >= u32::MAX ==> r == 0,
    {
        let used = self.forks.origins.len();
        (u32::MAX as usize).saturating_sub(used)
    }

    /// A read-only view over the current contents (parity with production).
    pub fn view_handle(&self) -> (v: VecView<'_, T, I, S, TRACK>)
        ensures v.vec_ref() == self,
    {
        VecView { vec: self }
    }

    /// Bytes consumed by diff tracking only: diff_log + frames + fork history.
    /// Diagnostic; no spec content (capacity measurement, external_body).
    /// Production formula (containers/src/vec.rs): CAPACITY-based, not
    /// len-based — this reports the actual allocation footprint.
    #[verifier::external_body]
    pub fn tracking_bytes(&self) -> usize {
        self.diff_log.capacity() * core::mem::size_of::<(T, I)>()
            + self.frames.capacity() * core::mem::size_of::<Frame<I>>()
            + self.forks.heap_bytes()
    }

    /// Total bytes used by this Vec: struct + store backing + tracking.
    /// Diagnostic; no spec content. Production formula:
    /// `size_of::<Self>() + store.heap_bytes() + tracking_bytes()`.
    #[verifier::external_body]
    pub fn total_bytes(&self) -> usize {
        core::mem::size_of::<Self>() + self.store.heap_bytes() + self.tracking_bytes()
    }

    /// THE public token-validity check: "restorable now" (migration plan 2.2).
    /// Returns exactly `is_restorable_spec(token)` — true iff `restore(token)`
    /// would succeed at this moment: TRACK on, same container, frame still
    /// live (rejects consumed tokens), on the live branch path within its
    /// depth bound, and both counter headrooms hold. Borrows the token
    /// (production parity). The genealogy-only walk that older revisions
    /// exposed under this name is the private `is_on_current_branch`.
    // ------------------------------------------------------------------
    // Total shell (total-API plan phase 2): no `requires` beyond wf; every
    // precondition of the partial core is evaluated by a verified exec twin
    // and the branch discharges the core's contract as a proof obligation,
    // so the check and the contract cannot drift.
    // ------------------------------------------------------------------

    /// Exec twin of `push`'s capacity precondition.
    pub fn can_push(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() + 1 < I::max_nat()),
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        n < cap
    }

    /// Total push: refuses at the index word's capacity instead of the
    /// partial core's deferred trap-at-next-`len()` protocol.
    pub fn try_push(&mut self, value: T) -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view() == old(self).view().push(value)
                && final(self).snapshots_view() == old(self).snapshots_view(),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        if self.can_push() {
            self.push(value);
            Ok(())
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total batch push: ONE capacity check licenses the whole slice, the
    /// loop invariant carries the bound to each core `push` — the amortized
    /// form of `try_push` for hot loops (one branch per batch, none per
    /// element).
    pub fn try_extend(&mut self, values: &[T]) -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view() == old(self).view() + values@,
            r is Err ==> final(self).view() == old(self).view(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        // `n <= cap` first so `cap - n` cannot underflow; then the batch must
        // fit strictly under the word (`< max_nat` after every push).
        if n > cap || values.len() > cap - n {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        let ghost old_view = self.view();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                self.wf(),
                i <= values@.len(),
                self.view() == old_view + values@.subrange(0, i as int),
                self.snapshots_view() == old(self).snapshots_view(),
                old_view.len() + values@.len() < I::max_nat(),
            decreases values@.len() - i,
        {
            proof {
                assert(self.view().len() + 1 < I::max_nat());
            }
            self.push(values[i]);
            proof {
                assert(self.view() =~= old_view + values@.subrange(0, i as int + 1));
            }
            i += 1;
        }
        proof {
            assert(values@.subrange(0, values@.len() as int) =~= values@);
        }
        Ok(())
    }

    /// Exec twin of `mark`'s preconditions (TRACK, depth headroom, length
    /// representable in the token's saved_len).
    pub fn can_mark(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (TRACK && self.depth_spec() < u32::MAX
            && self.view().len() < I::max_nat()),
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        TRACK && self.frames.len() < (u32::MAX as usize) && n <= cap
    }

    /// Total mark: the error names which precondition failed.
    pub fn try_mark(&mut self, shrink: ShrinkPolicy)
        -> (r: Result<VecToken, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(token) ==> {
                &&& final(self).view() == old(self).view()
                &&& token.frame_idx_spec() == old(self).depth_spec()
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& final(self).snapshots_view()
                    == old(self).snapshots_view().push(old(self).view())
            },
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        if !(self.frames.len() < (u32::MAX as usize)) {
            return Err(crate::error::ContainerError::DepthLimit);
        }
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.store.raw_len() <= <I as crate::index_like::IndexLike>::max().as_usize()) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        Ok(self.mark(shrink))
    }

    /// Total restore: `is_valid_token` already answers exactly "would
    /// `restore` succeed right now" (`is_restorable_spec` is the FULL
    /// runtime-checkable precondition), so the wrapper is the check.
    pub fn try_restore(&mut self, token: VecToken)
        -> (r: Result<(), crate::error::ContainerError>)
        where T: core::default::Default
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view()
                == old(self).snapshots_view()[token.frame_idx_spec() as int]
                && final(self).depth_spec() == token.frame_idx_spec()
                && final(self).snapshots_view()
                    == old(self).snapshots_view().subrange(0, token.frame_idx_spec() as int),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if self.is_valid_token(&token) {
            self.restore(token);
            Ok(())
        } else {
            Err(crate::error::ContainerError::InvalidToken)
        }
    }

    pub fn is_valid_token(&self, token: &VecToken) -> (b: bool)
        requires
            self.wf(),
        ensures
            b == self.is_restorable_spec(*token),
    {
        if !TRACK {
            return false;
        }
        let same_container = token.container_id.eq(self.id);
        if !same_container {
            return false;
        }
        // Frame liveness before the genealogy walk: a consumed token's branch
        // can still be on-path, but its frame is gone (design doc 08).
        if token.frame_idx >= self.frames.len() {
            return false;
        }
        // Headrooms (frames.len() < u32::MAX also lets is_on_current_branch's
        // `as u32` cast be exact).
        if self.frames.len() >= u32::MAX as usize {
            return false;
        }
        if self.forks.origins.len() >= u32::MAX as usize {
            return false;
        }
        self.is_on_current_branch(token)
    }

    /// Genealogy-only validity (identity assumed checked): the token's branch
    /// is on the current fork path within its depth bound. Private — the one
    /// public validity notion is `is_valid_token` ("restorable now").
    fn is_on_current_branch(&self, token: &VecToken) -> (b: bool)
        requires
            self.wf(),
            self.frames@.len() < u32::MAX,
        ensures
            b == crate::fork_history::fork_valid(
                self.forks.origins@,
                self.forks.current_branch_id as nat,
                self.frames@.len() as nat,
                token.branch_id as nat,
                token.depth as nat),
    {
        let cur_depth = self.frames.len() as u32;
        self.forks.is_valid(token.branch_id, token.depth, cur_depth)
    }

    #[inline(always)]
    pub fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let ghost old_view = self.view();
        let ghost old_self = *self;
        let old_len = self.store.len();
        // Overflow protocol (production parity, fix-2 follow-up): push itself
        // carries NO runtime check — the verified `requires` still obliges
        // every verified caller to prove `view().len() + 1 < I::max_nat()`,
        // and an UNVERIFIED caller who pushes past the index capacity is
        // trapped at the next `len()` read (`"len overflow"`), exactly
        // production's `try_from_usize(..).expect` protocol. The wf invariant
        // (`data().len() < I::max_nat()`) is what the requires protects; the
        // len()-read trap is the unverified-caller backstop.
        self.store.push(value);

        // Pop-into-marked-region bookkeeping: if we are pushing back into a slot that
        // lies inside the active frame's marked region (old_len < active),
        // that slot was popped out of the marked region earlier and the pop
        // already captured snap[old_len] into the top stratum. The fresh slot
        // must therefore INHERIT the captured flag, both to keep the bridge
        // (captured() must match captured_in_range, which is true for that
        // index) and to keep the diff log bounded (a later `set` here must
        // not re-capture). When old_len >= active (the normal transient push)
        // this branch is skipped and the new slot stays uncaptured.
        // Compare via as_usize (whose spec relation to as_nat is concrete),
        // not via lt() — lt_spec is a default trait method whose body is not
        // transparent at the generic `I: IndexLike` use-site.
        // Short-circuit order matches production exactly: TRACK (const,
        // folds) → frames non-empty → the index compare. Under TRACK=false
        // the whole computation erases.
        let reentered = TRACK
            && self.frames.len() > 0
            && old_len.as_usize() < self.active_saved_len.as_usize();
        let ghost has_frame = TRACK && self.frames@.len() > 0;
        let ghost in_marked = old_len.as_nat() < self.active_saved_len.as_nat();
        proof {
            // TRACK=false: wf pins frames empty, so has_frame is false either way.
            if !TRACK {
                assert(self.frames@.len() == 0);
            }
        }
        proof {
            assert(in_marked == (old_len.as_nat() < self.active_saved_len.as_nat()));
            assert(has_frame == (self.frames@.len() > 0));
            assert(reentered == (self.frames@.len() > 0
                && old_len.as_nat() < self.active_saved_len.as_nat()));
        }
        // push appended captured()[old_len] == false (TRACK-conditional:
        // the flag facts only feed the frame invariants, which are vacuous
        // for TRACK=false since wf pins frames empty).
        proof {
            if TRACK {
                assert(self.store.captured()[old_len.as_nat() as int] == false);
            }
        }
        if reentered {
            // data().len() == old_len + 1 after push, so old_len is in bounds.
            self.store.mark_captured(old_len);
        }
        proof {
            if TRACK {
                // Merged: captured()[old_len] is exactly `reentered`; prefix
                // [0, old_len) unchanged (push appends at old_len;
                // mark_captured, if it ran, updates only old_len).
                assert(self.store.captured()[old_len.as_nat() as int] == reentered);
                assert forall|j: int| 0 <= j < old_len.as_nat() implies
                    #[trigger] self.store.captured()[j] == old_self.store.captured()[j] by {}
                // no-stray-flags: prefix flags carry the old invariant; the
                // new slot's flag is `reentered`, which by construction means
                // a live frame and old_len < active.
                assert forall|j: int| 0 <= j < self.view().len()
                    && #[trigger] self.store.captured()[j]
                    implies self.frames@.len() > 0
                        && j < self.active_saved_len.as_nat() by {
                    if j < old_len.as_nat() as int {
                        assert(old_self.store.captured()[j]);
                    } else {
                        assert(j == old_len.as_nat() as int);
                        assert(reentered);
                    }
                }
            }
        }
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
            let diffs = self.diff_log@;
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
                    // preserved. Coverage-based (no saved_len <= view bound).
                    self.lemma_saved_len_le_view_from(old_self, k);
                }
            }
            // Bridge: store.push appended captured()[old_len]==false; if we
            // then mark_captured(old_len) it's true. For j < old_len the flag
            // and the diffs are unchanged, so the old bridge transfers; for
            // j == old_len (only relevant when old_len < active) the
            // mark_captured set it true, matching captured_in_range (snap was
            // captured by the earlier pop — coverage).
            self.store.lemma_wf_captured_len();
            if frames.len() > 0 {
                let top = (frames.len() - 1) as int;
                let ds_top = frames[top].diff_start as int;
                assert(self.active_saved_len == frames[top].saved_len);
                assert forall|j: int|
                    0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(diffs, ds_top, diffs.len() as int, j as nat)
                by {
                    if j < old_len.as_nat() {
                        // unchanged flag, unchanged diffs ⇒ old bridge applies.
                        assert(self.store.captured()[j] == old_self.store.captured()[j]);
                        assert(j < old_self.view().len());
                        assert(old_self.store.captured()[j]
                            == captured_in_range::<T, I>(
                                old_self.diff_log@, ds_top, old_self.diff_log@.len() as int, j as nat));
                    } else {
                        // j == old_len: only present when old_len < view.len(),
                        // i.e. old_len < active (the mark_captured branch ran).
                        // captured()[old_len] == true; and the top frame's
                        // coverage arm (j < active, uncaptured ⇒ j < view.len)
                        // forces this popped cell to be captured_in_range.
                        assert(j == old_len.as_nat());
                        assert(j < self.active_saved_len.as_nat());
                        // The exec branch `old_len.lt(active)` ran (its spec is
                        // old_len.as_nat() < active.as_nat()), so mark_captured
                        // set captured()[old_len] = true.
                        assert(old_len.as_nat() < self.active_saved_len.as_nat());
                        assert(in_marked);
                        assert(has_frame);  // frames.len() > 0 (outer if)
                        assert(reentered);  // ⇒ captured()[old_len] == true
                        // old_self top frame_cell_inv at j: j < active == saved_top,
                        // and j >= old_view.len() (popped) ⇒ captured arm.
                        assert(old_self.frame_inv_range_holds(top));
                        lemma_frame_inv_arm_at::<T, I>(
                            old_self.layer_above_at(top), old_self.diff_log@, ds_top,
                            old_self.stratum_end(top), old_self.snapshots@[top],
                            frames[top].saved_len.as_nat(), j);
                        assert(old_self.layer_above_at(top) == old_view);
                        assert(j >= old_view.len());  // old_len == old_view.len()
                        // uncaptured arm would need j < old_view.len(): false.
                        // So captured_in_range(old_diffs, ds_top, |old_diffs|, j).
                        assert(captured_in_range::<T, I>(
                            old_self.diff_log@, ds_top, old_self.diff_log@.len() as int, j as nat));
                        assert(self.store.captured()[j] == true);
                    }
                }
            }
        }
    }

    /// Helper used in proofs: assert frame_inv_range for frame k from wf.
    pub open(crate) spec fn frame_inv_range_holds(&self, k: int) -> bool {
        frame_inv_range::<T, I>(
            self.layer_above_at(k),
            self.diff_log@,
            self.frames@[k].diff_start as int,
            self.stratum_end(k),
            self.snapshots@[k],
            self.frames@[k].saved_len.as_nat())
    }

    /// Carry the top frame's `frame_inv_range` across a push (old_self had wf;
    /// the new view is the old view plus appended elements). Coverage-based:
    /// no `saved_len <= view.len()` needed — the per-cell uncaptured arm itself
    /// supplies `j < above_old.len()`, and the appended view agrees on the old
    /// prefix, so the arm transfers cell-by-cell.
    pub(crate) proof fn lemma_saved_len_le_view_from(&self, old_self: Self, k: int)
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
        assert(old_self.frame_inv_range_holds(k));
        let above_old = old_self.view();
        let above_new = self.view();
        let diffs = self.diff_log@;
        let lo = self.frames@[k].diff_start as int;
        let hi = self.stratum_end(k);
        let snap = self.snapshots@[k];
        let sl = self.frames@[k].saved_len.as_nat();
        assert(self.layer_above_at(k) == above_new);
        assert(old_self.layer_above_at(k) == above_old);
        assert(self.stratum_end(k) == old_self.stratum_end(k));
        // Per-cell transfer: same diffs/snap; view prefix preserved & longer.
        assert forall|j: int| 0 <= j < sl as int implies
            #[trigger] frame_cell_inv::<T, I>(above_new, diffs, lo, hi, snap, j)
        by {
            lemma_frame_inv_arm_at::<T, I>(above_old, diffs, lo, hi, snap, sl, j);
            // captured arm is layer-independent; uncaptured arm: old gave
            // j < above_old.len() && above_old[j]==snap[j], and above_new is
            // longer and agrees on the old prefix — so j < above_new.len()
            // and above_new[j]==snap[j]. No saved_len<=view bound required.
        }
    }

    /// Pop the last element (FAITHFUL: may pop into a frame's marked region).
    ///
    /// If the removed slot lies inside the active frame's marked region
    /// (`old_len - 1 < active_saved_len`), it is first CAPTURED into the top
    /// stratum (first-write-wins), so the now-absent cell still satisfies the
    /// frame invariant via the captured arm — this is exactly the coverage
    /// obligation. Conditional capture (not production's unconditional
    /// force_capture) keeps the diff log bounded: at most one entry per index
    /// per stratum. `restore` later regrows the popped region with
    /// `resize_default` and overwrites each filler back from these captures.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    #[inline(always)]
    pub fn pop(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).view().len() == 0 ==> r is None && final(self).view() == old(self).view(),
            old(self).view().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).view()[old(self).view().len() - 1]
                &&& final(self).view() == old(self).view().drop_last()
            },
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let ghost old_view = self.view();
        let ghost old_diffs = self.diff_log@;
        let ghost old_frames = self.frames@;

        // Capture the cell we are about to remove, if it falls inside the
        // active marked region. Must happen BEFORE store.pop while data[last]
        // is still readable; capture's first-write-wins logs (data[last], last)
        // == (snap[last], last) only if it was uncaptured, else no-ops.
        let len = self.store.len();
        let ghost old_store_captured = self.store.captured();
        let ghost captured_marked = false;
        let ghost last_g: int = 0;
        // data_last == value of the slot being removed (defined when nonempty).
        let ghost data_last: T = old(self).store.data()[
            if old_view.len() > 0 { old_view.len() - 1 } else { 0 } as int];
        if TRACK && self.frames.len() > 0 && len.as_usize() > 0
            && len.as_usize() - 1 < self.active_saved_len.as_usize()
        {
            let last = len.as_usize() - 1;
            proof { len.lemma_as_nat_bounded(); }  // last < len.as_nat() < max_nat
            let last_i = match I::try_from_usize(last) {
                Some(x) => x,
                None => { assert(false); return None; },
            };
            let active = self.active_saved_len;
            proof {
                captured_marked = true;
                last_g = last as int;
                assert(last_i.as_nat() == last as nat);
                assert(last_i.as_nat() < active.as_nat());
                assert(self.store.data()[last as int] == data_last);
            }
            self.store.capture(last_i, active, &mut self.diff_log);
            proof {
                // capture's first-write-wins outcome at index `last`:
                //  - if !old.captured[last]: appended (data_last, last_i);
                //  - else: no-op. Both ways the result diff log relates to
                //    old_diffs by "append-one-at-index-last or identity".
                if !old_store_captured[last as int] {
                    assert(self.diff_log@ == old_diffs.push((data_last, last_i)));
                    assert(self.diff_log@[old_diffs.len() as int].1.as_nat() == last as nat);
                } else {
                    assert(self.diff_log@ == old_diffs);
                }
                // capture changes the flag only at `last == len-1`; surface
                // the SAME-shaped fact both branches will share post-if.
                assert(last as int == len.as_nat() - 1);
                // capture preserves data() ⇒ captured() length unchanged
                // (both equal data().len(), which capture leaves intact).
                self.store.lemma_wf_captured_len();
                old(self).store.lemma_wf_captured_len();
                assert(self.store.data() == old(self).store.data());
                assert(self.store.captured().len() == old_store_captured.len());
                assert forall|j: int| 0 <= j < len.as_nat() - 1
                    implies #[trigger] self.store.captured()[j] == old_store_captured[j] by {
                    // capture's ensures: either first-write-wins (forall
                    // k != last_i.as_nat() preserved) or no-op (captured()
                    // unchanged). Either way j (!= last == last_i.as_nat()) is
                    // preserved.
                    assert(j != last_i.as_nat());
                    assert(j < self.store.captured().len());
                }
            }
        } else {
            // No capture: the store is entirely unchanged — same shape.
            proof {
                assert(self.store.captured() =~= old_store_captured);
                assert forall|j: int| 0 <= j < len.as_nat() - 1
                    implies #[trigger] self.store.captured()[j] == old_store_captured[j] by {}
            }
        }
        // mid state (after the optional capture, before pop): both branches
        // established flags below `len-1` match old_store_captured.
        let ghost mid_captured = self.store.captured();

        let ghost mid_diffs = self.diff_log@;
        // diffs is old_diffs, or old_diffs.push(e) with e.1 == last_g (== new_len).
        let r = self.store.pop();

        proof {
            let frames = self.frames@;
            let diffs = self.diff_log@;
            let snaps = self.snapshots@;
            // capture/pop leave frames & snapshots unchanged. diff_log is
            // either old_diffs (no capture) or old_diffs.push((snap[last],last)).
            assert(frames == old_frames);
            assert(snaps == old(self).snapshots@);
            assert(diffs == mid_diffs);
            if !TRACK {
                // frames pinned empty: every captured()-reading wf conjunct
                // is frame-quantified, hence vacuous; captured().len() comes
                // from the trait's wf lemma.
                assert(frames.len() == 0);
                self.store.lemma_wf_captured_len();
            }

            if old_frames.len() > 0 && old_view.len() > 0 {
                let top = (frames.len() - 1) as int;
                let new_len = (old_view.len() - 1) as int;  // == self.view().len()
                let ds_top = frames[top].diff_start as int;
                let active_n = self.active_saved_len.as_nat() as int;
                assert(self.view() == old_view.drop_last());
                assert(frames[top].saved_len == self.active_saved_len);  // wf
                // last == new_len == old_view.len()-1; captured_marked iff
                // new_len < active.
                assert(captured_marked == (new_len < active_n));

                // Unified relation between diffs and old_diffs: either equal
                // (no capture, or capture no-op'd on an already-captured slot)
                // or old_diffs with ONE entry appended whose index is new_len.
                // This is exactly the hypothesis lemma_captured_in_range_append_
                // other needs, for every j != new_len.
                assert(diffs == old_diffs
                    || (diffs.len() == old_diffs.len() + 1
                        && diffs.subrange(0, old_diffs.len() as int) == old_diffs
                        && diffs[old_diffs.len() as int].1.as_nat() == new_len as nat)) by {
                    if captured_marked && !old_store_captured[new_len] {
                        assert(diffs == old_diffs.push((data_last, diffs[old_diffs.len() as int].1)));
                        assert(diffs.subrange(0, old_diffs.len() as int) == old_diffs);
                    }
                }

                // What capture did to the diff log & flags. Let last = new_len.
                // If captured_marked: capture saw i=last < active. First-write-
                // wins: if !old.captured[last] it appended (snap[last], last)
                // and set the flag; else no-op. Either way after capture the
                // top stratum HITS last with value snap[last], and for all
                // j != last the flags/entries are unchanged.
                self.store.lemma_wf_captured_len();

                // --- frame_inv_range for every frame ---
                assert forall|k: int| 0 <= k < frames.len() implies
                    #[trigger] frame_inv_range::<T, I>(
                        self.layer_above_at(k), diffs, frames[k].diff_start as int,
                        self.stratum_end(k), snaps[k], frames[k].saved_len.as_nat())
                by {
                    assert(old(self).frame_inv_range_holds(k));
                    let lo = frames[k].diff_start as int;
                    let hi = self.stratum_end(k);
                    let snap = snaps[k];
                    let sl = frames[k].saved_len.as_nat();
                    if k < top {
                        // Inner frame: layer is an unchanged snapshot; its
                        // stratum [ds_k, ds_{k+1}) lies below the top stratum,
                        // so a capture append at the end doesn't touch it.
                        assert(self.layer_above_at(k) == snaps[k + 1]);
                        assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                        assert(hi == old(self).stratum_end(k));
                        assert(hi == old_frames[k + 1].diff_start as int);
                        old(self).lemma_diff_start_le_n(k + 1);
                        old(self).lemma_diff_start_monotone(k + 1, top);
                        assert(hi <= old_diffs.len() as int);
                        lemma_frame_inv_range_local::<T, I>(
                            self.layer_above_at(k), old_diffs, diffs, lo, hi, snap, sl);
                    } else {
                        // Top frame. Layer is the (shortened) view; stratum
                        // [ds_top, n) possibly extended by the capture append
                        // at index `last == new_len`. Per cell j < sl:
                        //   j < new_len  : present, value & captured-status
                        //                  preserved ⇒ old arm transfers;
                        //   j == new_len : now ABSENT. If captured_marked the
                        //                  capture put (snap[last],last) in the
                        //                  stratum (captured arm); coverage.
                        //   j > new_len  : was already absent in old state, so
                        //                  old captured arm held; entry survives.
                        assert(self.layer_above_at(k) == self.view());
                        assert(old(self).layer_above_at(k) == old_view);
                        assert(sl == active_n);
                        // old top stratum ended at old_diffs.len().
                        old(self).lemma_diff_start_le_n(top);
                        assert(old(self).stratum_end(top) == old_diffs.len() as int);
                        assert(frame_inv_range::<T, I>(
                            old_view, old_diffs, lo, old_diffs.len() as int, snap, sl));
                        assert forall|j: int| 0 <= j < sl as int implies
                            #[trigger] frame_cell_inv::<T, I>(self.view(), diffs, lo, hi, snap, j)
                        by {
                            lemma_frame_inv_arm_at::<T, I>(
                                old_view, old_diffs, lo, old_diffs.len() as int, snap, sl, j);
                            if j < new_len {
                                // present & preserved by drop_last; capture
                                // append (if any) is at index last != j.
                                assert(self.view()[j] == old_view[j]);
                                lemma_captured_in_range_append_other::<T, I>(
                                    old_diffs, diffs, lo, j as nat, new_len as nat);
                            } else if j == new_len {
                                // The cell just removed. It was inside the
                                // marked region (j < active == sl), so the
                                // capture ran (captured_marked). The capture
                                // arm holds: there is an entry in [lo, hi) with
                                // index j == new_len and value snap[j].
                                assert(j < active_n);
                                assert(captured_marked);
                                assert(hi == diffs.len());  // top stratum end
                                // old cell_inv at j (from lemma_frame_inv_arm_at
                                // above): j == new_len == old_view.len()-1, so
                                // j < old_view.len() ⇒ if old-uncaptured then
                                // old_view[j] == snap[j]; if old-captured the
                                // old entry already holds snap[j].
                                // The cell_inv for j must be the CAPTURED arm:
                                // exhibit p in [lo,hi) with index j, value snap[j].
                                if old_store_captured[j] {
                                    // already captured: capture no-op'd, so
                                    // diffs == old_diffs and the old captured
                                    // arm's witness survives.
                                    assert(j < old_view.len());
                                    assert(old(self).store.captured()[j]);  // == old_store_captured[j]
                                    assert(captured_in_range::<T, I>(
                                        old_diffs, lo, old_diffs.len() as int, j as nat)) by {
                                        assert(old(self).store.captured()[j]
                                            == captured_in_range::<T, I>(
                                                old_diffs, lo, old_diffs.len() as int, j as nat));
                                    }
                                    // old captured arm gives the value witness.
                                    assert(frame_cell_inv::<T, I>(
                                        old_view, old_diffs, lo, old_diffs.len() as int, snap, j));
                                    assert(diffs == old_diffs);
                                    let p = choose|p: int| lo <= p < old_diffs.len() as int
                                        && (#[trigger] old_diffs[p]).1.as_nat() == j as nat
                                        && old_diffs[p].0 == snap[j];
                                    assert(lo <= p < hi && 0 <= p < diffs.len()
                                        && diffs[p].1.as_nat() == j as nat
                                        && diffs[p].0 == snap[j]);
                                    assert(captured_in_range::<T, I>(diffs, lo, hi, j as nat));
                                    assert(frame_cell_inv::<T, I>(self.view(), diffs, lo, hi, snap, j));
                                } else {
                                    // uncaptured: capture appended (data_last, last_i)
                                    // at position old_diffs.len(); data_last ==
                                    // old.data[j] == old_view[j] == snap[j] (old
                                    // uncaptured arm).
                                    assert(!captured_in_range::<T, I>(
                                        old_diffs, lo, old_diffs.len() as int, j as nat)) by {
                                        assert(j < old_view.len());
                                        assert(old(self).store.captured()[j] == false);
                                        assert(old(self).store.captured()[j]
                                            == captured_in_range::<T, I>(
                                                old_diffs, lo, old_diffs.len() as int, j as nat));
                                    }
                                    assert(frame_cell_inv::<T, I>(
                                        old_view, old_diffs, lo, old_diffs.len() as int, snap, j));
                                    assert(old_view[j] == snap[j]);  // old uncaptured arm
                                    assert(data_last == old_view[j]);
                                    let p = old_diffs.len() as int;
                                    assert(diffs.subrange(0, p) == old_diffs);
                                    assert(diffs[p].1.as_nat() == j as nat);
                                    assert(diffs[p].0 == data_last);
                                    assert(diffs[p].0 == snap[j]);
                                    assert(lo <= p < hi && 0 <= p < diffs.len());
                                    assert(captured_in_range::<T, I>(diffs, lo, hi, j as nat));
                                    assert(frame_cell_inv::<T, I>(self.view(), diffs, lo, hi, snap, j));
                                }
                            } else {
                                // j > new_len: this cell was ALREADY absent
                                // before this pop (j >= old_view.len()-... it
                                // was popped earlier). The old uncaptured arm
                                // would need j < old_view.len(): j > new_len ==
                                // old_view.len()-1 ⇒ j >= old_view.len(), so the
                                // old cell_inv took the CAPTURED arm. That entry
                                // is below old_diffs.len() <= diffs.len() and is
                                // preserved by the capture append.
                                assert(j >= old_view.len());
                                assert(captured_in_range::<T, I>(
                                    old_diffs, lo, old_diffs.len() as int, j as nat));
                                lemma_captured_in_range_append_other::<T, I>(
                                    old_diffs, diffs, lo, j as nat, new_len as nat);
                            }
                        }
                        assert(frame_inv_range::<T, I>(self.view(), diffs, lo, hi, snap, sl));
                    }
                }

                // --- bridge (gated by j < active && j < view.len()) ---
                assert forall|j: int|
                    0 <= j < active_n && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(diffs, ds_top, diffs.len() as int, j as nat)
                by {
                    // j < view.len() == new_len, so j != last (== new_len). The
                    // capture append (if any) is at index last != j, and pop's
                    // drop_last removes the flag at last (>= new_len > j). So
                    // both captured()[j] and captured_in_range(j) are unchanged
                    // from the old top-stratum bridge.
                    assert(j < new_len);
                    assert(j < old_view.len());
                    // pop's drop_last: captured()[j] == mid_captured[j] for
                    // j < new_len; and mid_captured[j] == old flag (capture
                    // only touched index new_len != j).
                    assert(self.store.captured()[j] == mid_captured[j]);
                    assert(mid_captured[j] == old(self).store.captured()[j]);
                    assert(old(self).store.captured()[j]
                        == captured_in_range::<T, I>(
                            old_diffs, ds_top, old_diffs.len() as int, j as nat));
                    lemma_captured_in_range_append_other::<T, I>(
                        old_diffs, diffs, ds_top, j as nat, new_len as nat);
                }
            } else if old_frames.len() > 0 {
                // old_view empty (so view stays empty): store.pop is a no-op
                // and the capture branch can't have run (len == 0). So the
                // entire state equals old(self), and old wf transfers directly.
                assert(old_view.len() == 0);
                assert(self.view() == old_view);
                assert(diffs == old_diffs);
                assert(self.store.captured() == old(self).store.captured());
                assert forall|k: int| 0 <= k < frames.len() implies
                    #[trigger] frame_inv_range::<T, I>(
                        self.layer_above_at(k), diffs, frames[k].diff_start as int,
                        self.stratum_end(k), snaps[k], frames[k].saved_len.as_nat())
                by {
                    assert(old(self).frame_inv_range_holds(k));
                    assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                }
            }
        }
        r
    }

    /// Write `value` at index `i`, capturing the old value into the active
    /// frame's stratum (first-write-wins) when a frame is live. Works at any
    /// stack depth.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    #[inline(always)]
    pub fn set_index(&mut self, i: I, value: T)
        requires
            old(self).wf(),
            i.as_nat() < old(self).view().len(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().update(i.as_nat() as int, value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let ghost old_view = self.view();
        let ghost old_diffs = self.diff_log@;
        let ghost old_frames = self.frames@;
        let ghost n = old_diffs.len() as int;

        let ghost active_n = self.active_saved_len.as_nat();
        let ghost iu = i.as_nat() as int;
        let ghost was_captured0 = self.store.captured()[iu];
        if TRACK && self.frames.len() > 0 {
            let active = self.active_saved_len;
            self.store.capture(i, active, &mut self.diff_log);
            proof {
                // Surface capture's first-write-wins outcome explicitly.
                if iu < active_n as int && !was_captured0 {
                    assert(self.diff_log@ == old_diffs.push((old_view[iu], i)));
                    assert(self.store.captured()[iu] == true);
                } else {
                    assert(self.diff_log@ == old_diffs);
                }
            }
        }
        let ghost mid_diffs = self.diff_log@;
        self.store.set_raw(i, value);

        proof {
            let frames = self.frames@;
            let diffs = self.diff_log@;
            let snaps = self.snapshots@;

            // set_raw leaves diff_log unchanged and (when TRACK) the store's
            // captured() too; it only updates view[iu]. capture left view
            // unchanged. So overall: view == old_view.update(iu, value), and
            // diffs == mid_diffs (whatever capture produced).
            assert(self.view() == old_view.update(iu, value));
            assert(diffs == mid_diffs);
            assert(frames == old_frames);

            // wf's `captured().len() == view().len()` is UNCONDITIONAL, but
            // `set_raw` now preserves captured() only when TRACK (it skips the
            // dead flag maintenance otherwise — see its postcondition). Get the
            // length from the store's own wf instead of from flag preservation,
            // so the untracked case is covered too.
            self.store.lemma_wf_captured_len();

            if old_frames.len() == 0 {
                assert(diffs.len() == 0);
            } else {
                let top = (frames.len() - 1) as int;
                let was_captured = was_captured0;
                let appended = iu < active_n as int && !was_captured0;
                assert(old(self).store.captured()[iu] == was_captured0);

                // capture either no-ops or appends one entry at the end.
                // In both cases the prefix [0, old_diffs.len()) is preserved
                // and diffs.len() >= old_diffs.len().
                assert(old_diffs.len() <= diffs.len());
                assert(forall|m: int| 0 <= m < old_diffs.len() ==>
                    #[trigger] diffs[m] == old_diffs[m]);
                // The top frame's diff_start <= old_diffs.len() (= n).
                old(self).lemma_diff_start_le_n(top);
                assert(frames[top].diff_start <= old_diffs.len());

                // capture's effect on diffs:
                //   - if iu < active && !was_captured: diffs == old_diffs.push((old_view[iu], i))
                //   - else: diffs == old_diffs.
                // Either way, for every k, the stratum of frame k changes only
                // possibly at the top frame (an append extends [top.ds, n)).

                // Frame_inv_range for every k.
                assert forall|k: int| 0 <= k < frames.len() implies
                    #[trigger] frame_inv_range::<T, I>(
                        self.layer_above_at(k), diffs, frames[k].diff_start as int,
                        self.stratum_end(k), snaps[k], frames[k].saved_len.as_nat())
                by {
                    assert(old(self).frame_inv_range_holds(k));
                    assert(frames[k] == old_frames[k]);
                    assert(snaps[k] == old(self).snapshots@[k]);
                    if k < top {
                        // Inner frame: layer is snaps[k+1] (unchanged), and
                        // its stratum [ds_k, ds_{k+1}) lies entirely below the
                        // top stratum, so the capture append (at the end of
                        // diffs) doesn't touch it.
                        assert(self.layer_above_at(k) == snaps[k + 1]);
                        assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                        let hi = self.stratum_end(k);
                        assert(hi == old(self).stratum_end(k));
                        assert(hi == old_frames[k + 1].diff_start as int);
                        old(self).lemma_diff_start_le_n(k + 1);
                        old(self).lemma_diff_start_monotone(k + 1, top);
                        // hi <= top.diff_start <= old_diffs.len(): inner
                        // stratum entirely within the preserved prefix.
                        assert(hi <= old_diffs.len() as int);
                        lemma_frame_inv_range_local::<T, I>(
                            self.layer_above_at(k), old_diffs, diffs,
                            frames[k].diff_start as int, hi, snaps[k],
                            frames[k].saved_len.as_nat());
                    } else {
                        // Top frame: layer is the view (changed at iu); stratum
                        // [ds_top, diffs.len()) possibly extended by capture.
                        let ds = frames[top].diff_start as int;
                        let hi = self.stratum_end(k);
                        let sl = frames[top].saved_len.as_nat();
                        assert(hi == diffs.len() as int);
                        assert(frames[top].saved_len == self.active_saved_len);
                        assert(sl == active_n);
                        assert(self.layer_above_at(k) == self.view());
                        assert(old(self).layer_above_at(k) == old_view);
                        assert(old(self).frame_inv_range_holds(top));
                        old(self).lemma_diff_start_le_n(top);
                        let new_view = self.view();
                        let snap = snaps[top];

                        // The capture step gives us (from its postcondition):
                        //   if iu < active_n && !was_captured:
                        //     diffs == old_diffs.push((old_view[iu], i))
                        //   else: diffs == old_diffs.
                        // In `set` we always have iu < view.len(); the active
                        // marked region is [0, active_n) == [0, sl).

                        // Structural conjuncts. (No `sl <= view.len()`: that
                        // top-fullness fact is gone; frame_inv_range's per-cell
                        // uncaptured arm carries the only presence bound needed.)
                        assert(snap.len() == sl);
                        assert(new_view.len() == old_view.len());
                        assert forall|m: int| ds <= m < hi implies
                            (#[trigger] diffs[m]).1.as_nat() < sl by {
                            if m < old_diffs.len() {
                                assert(diffs[m] == old_diffs[m]);
                            } else {
                                assert(appended);
                                assert(diffs[m] == (old_view[iu], i));
                            }
                        }
                        // uniqueness over [ds, hi).
                        assert forall|a: int, b: int|
                            ds <= a < hi && ds <= b < hi && a != b implies
                            (#[trigger] diffs[a]).1.as_nat()
                                != (#[trigger] diffs[b]).1.as_nat() by {
                            if a < old_diffs.len() && b < old_diffs.len() {
                                assert(diffs[a] == old_diffs[a] && diffs[b] == old_diffs[b]);
                            } else {
                                // one of them is the new entry at old_diffs.len()
                                // with index iu; the other is an old entry. The
                                // bridge says iu was NOT captured ⇒ no old top
                                // entry has index iu.
                                assert(appended);
                                let newpos = old_diffs.len() as int;
                                assert(diffs[newpos] == (old_view[iu], i));
                                // old entry at the other position has index != iu
                                let other = if a == newpos { b } else { a };
                                assert(ds <= other < old_diffs.len());
                                assert(diffs[other] == old_diffs[other]);
                                // bridge: !was_captured ⇒ iu not in old top stratum
                                assert(!captured_in_range::<T, I>(
                                    old_diffs, ds, old_diffs.len() as int, iu as nat)) by {
                                    assert(old(self).store.captured()[iu] == was_captured);
                                    assert(iu < active_n as int);
                                }
                                assert(old_diffs[other].1.as_nat() != iu as nat);
                            }
                        }
                        // two-arm, per-cell via frame_cell_inv.
                        assert forall|j: int| 0 <= j < sl as int implies
                            #[trigger] frame_cell_inv::<T, I>(new_view, diffs, ds, hi, snap, j)
                        by {
                            assert(old(self).frame_inv_range_holds(top));
                            lemma_frame_inv_arm_at::<T, I>(
                                old_view, old_diffs, ds, old_diffs.len() as int, snap, sl, j);
                            // bridge at j: old captured()[j] iff j in old top stratum.
                            if j == iu {
                                // j is captured now; find a witness with value snap[iu].
                                if appended {
                                    // old uncaptured arm: old_view[iu] == snap[iu]
                                    // (iu was uncaptured ⇒ not in old top stratum).
                                    assert(!captured_in_range::<T, I>(
                                        old_diffs, ds, old_diffs.len() as int, iu as nat)) by {
                                        assert(old(self).store.captured()[iu] == false);
                                    }
                                    assert(old_view[iu] == snap[iu]);
                                    let newpos = old_diffs.len() as int;
                                    assert(ds <= newpos < hi);
                                    assert(diffs[newpos].1.as_nat() == iu as nat);
                                    assert(diffs[newpos].0 == old_view[iu]);
                                    assert(diffs[newpos].0 == snap[iu]);
                                } else {
                                    // was_captured: old top stratum has an entry
                                    // (old, iu) with old == snap[iu]; still present
                                    // (prefix preserved, diffs == old_diffs).
                                    assert(was_captured);
                                    assert(old(self).store.captured()[iu] == true);
                                    assert(captured_in_range::<T, I>(
                                        old_diffs, ds, old_diffs.len() as int, iu as nat));
                                    let p = choose|p: int| ds <= p < old_diffs.len() as int
                                        && (#[trigger] old_diffs[p]).1.as_nat() == iu as nat
                                        && old_diffs[p].0 == snap[iu];
                                    assert(diffs[p] == old_diffs[p]);
                                }
                            } else {
                                // j != iu: capture only may add index iu != j,
                                // so j's captured-status is unchanged between
                                // old_diffs and diffs. (We DON'T assert
                                // new_view[j]==old_view[j] up front: for popped
                                // cells j >= view.len() that index is out of
                                // range — but coverage puts those in the
                                // captured arm, so the uncaptured sub-branch
                                // below only runs when j < view.len().)
                                assert(captured_in_range::<T, I>(diffs, ds, hi, j as nat)
                                    == captured_in_range::<T, I>(
                                        old_diffs, ds, old_diffs.len() as int, j as nat)) by {
                                    if captured_in_range::<T, I>(diffs, ds, hi, j as nat) {
                                        let p = choose|p: int| ds <= p < hi && 0 <= p < diffs.len()
                                            && (#[trigger] diffs[p]).1.as_nat() == j as nat;
                                        if p < old_diffs.len() {
                                            assert(diffs[p] == old_diffs[p]);
                                        } else {
                                            // p is the new entry with index iu != j
                                            assert(appended);
                                            assert(diffs[p].1.as_nat() == iu as nat);
                                        }
                                    }
                                    if captured_in_range::<T, I>(
                                        old_diffs, ds, old_diffs.len() as int, j as nat) {
                                        let p = choose|p: int|
                                            ds <= p < old_diffs.len() as int && 0 <= p < old_diffs.len()
                                            && (#[trigger] old_diffs[p]).1.as_nat() == j as nat;
                                        assert(diffs[p] == old_diffs[p]);
                                    }
                                }
                                // carry the old arm's witness/value for j.
                                if captured_in_range::<T, I>(diffs, ds, hi, j as nat) {
                                    let p = choose|p: int|
                                        ds <= p < old_diffs.len() as int && 0 <= p < old_diffs.len()
                                        && (#[trigger] old_diffs[p]).1.as_nat() == j as nat
                                        && old_diffs[p].0 == snap[j];
                                    assert(diffs[p] == old_diffs[p]);
                                } else {
                                    // uncaptured: the old uncaptured arm gives
                                    // j < old_view.len() && old_view[j]==snap[j].
                                    // set_raw preserves length and changes only
                                    // iu != j, so j < new_view.len() and
                                    // new_view[j] == old_view[j] == snap[j].
                                    assert((j as nat) < old_view.len());
                                    assert(new_view[j] == old_view[j]);
                                    assert((j as nat) < new_view.len());
                                }
                            }
                        }
                        assert(frame_inv_range::<T, I>(new_view, diffs, ds, hi, snap, sl));
                    }
                }
                self.store.lemma_wf_captured_len();
                assert(self.store.captured().len() == self.view().len());

                let ds_top = frames[top].diff_start as int;
                // Bridge gated by j < view.len() (matches the wf clause): the
                // store only tracks flags for present cells. set_raw preserves
                // length, so view.len() == old_view.len().
                assert forall|j: int|
                    0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(
                            diffs, ds_top, diffs.len() as int, j as nat)
                by {
                    // old bridge for j (j < view.len() == old_view.len()).
                    assert(j < old(self).view().len());
                    assert(old(self).store.captured()[j]
                        == captured_in_range::<T, I>(
                            old_diffs, ds_top, old_diffs.len() as int, j as nat));
                    if j == iu {
                        if appended {
                            // capture set captured[iu] true and appended (.,iu).
                            assert(self.store.captured()[iu] == true);
                            let newpos = old_diffs.len() as int;
                            assert(ds_top <= newpos < diffs.len() as int);
                            assert(diffs[newpos].1.as_nat() == iu as nat);
                        } else {
                            // not appended: captured()[iu] unchanged; was true
                            // (was_captured) and stratum entry preserved, OR
                            // iu >= active_n (excluded since j < active_n).
                            assert(self.store.captured()[iu] == was_captured);
                            assert(diffs == old_diffs);
                        }
                    } else {
                        // j != iu: captured()[j] unchanged by capture/set_raw,
                        // and captured_in_range(j) unchanged (only iu added).
                        assert(self.store.captured()[j] == old(self).store.captured()[j]);
                        if captured_in_range::<T, I>(diffs, ds_top, diffs.len() as int, j as nat) {
                            let p = choose|p: int| ds_top <= p < diffs.len() as int
                                && 0 <= p < diffs.len()
                                && (#[trigger] diffs[p]).1.as_nat() == j as nat;
                            if p < old_diffs.len() {
                                assert(diffs[p] == old_diffs[p]);
                            } else {
                                assert(appended);
                                assert(diffs[p].1.as_nat() == iu as nat);
                            }
                        }
                        if captured_in_range::<T, I>(
                            old_diffs, ds_top, old_diffs.len() as int, j as nat) {
                            let p = choose|p: int| ds_top <= p < old_diffs.len() as int
                                && 0 <= p < old_diffs.len()
                                && (#[trigger] old_diffs[p]).1.as_nat() == j as nat;
                            assert(diffs[p] == old_diffs[p]);
                        }
                    }
                }
            }
        }
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
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            // TRACK gate (production parity, plan 2.4): mark is uncallable on
            // an untracked vec — production panics, and so do we (guard in
            // body). The TRACK=false observational-equivalence theorem
            // (untracked ⇒ plain std::Vec) is about push/pop/set/get only.
            TRACK,
            // The token's `depth` is `frames.len() as u32`: the cast must be
            // exact or the token's validity coordinates are silently wrong.
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            token.frame_idx_spec() == old(self).depth_spec(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        // Runtime guards (plan 2.3/2.4), BEFORE maybe_shrink so a rejected
        // mark does not change capacity: TRACK parity, and the u32 depth cast.
        crate::guard::check_precondition(TRACK, "mark() called on untracked vec");
        crate::guard::check_precondition(
            self.frames.len() < u32::MAX as usize,
            "Vec::mark: frame-stack depth would overflow u32",
        );

        // Capacity reclamation (production parity). Observationally inert:
        // preserves view(), diff_log@, frames@, snapshots@, and wf.
        self.maybe_shrink(shrink);

        let saved_len = self.store.len();
        let diff_start = self.diff_log.len();

        // Parent-frame diff suffix (production parity): the only slots that
        // can carry a set capture flag are those the CURRENT top frame
        // captured, i.e. diff entries in [parent.diff_start, len). Pass that
        // suffix to prepare_mark so its sparse clear is O(top-frame diffs),
        // not O(whole log). The no-stray-flags wf invariant pins every set
        // flag to exactly this stratum.
        let parent_diff_start = if self.frames.len() > 0 {
            self.frames[self.frames.len() - 1].diff_start
        } else {
            0
        };

        // Token validity coordinates, captured BEFORE the frame push (so
        // `depth` is the count of frames below this one — its own frame index,
        // matching production). `branch_id` is the branch live at mark time.
        let token_branch = self.forks.current_branch();
        let token_depth = self.frames.len() as u32;
        let token_container = self.id;

        let ghost old_frames = self.frames@;
        let ghost old_snaps = self.snapshots@;
        let ghost old_view = self.view();

        let prev_suffix = vstd::slice::slice_subrange(
            self.diff_log.as_slice(), parent_diff_start, self.diff_log.len());
        proof {
            // Discharge prepare_mark's sparse-clear requires: every set flag
            // is named by a suffix entry. From wf: a set flag j is (no-stray)
            // below active with a live frame, hence (bridge) captured_in_range
            // over [top.diff_start, len) == [parent_diff_start, |diffs|) — the
            // suffix. captured_in_range unfolds to exactly the existential
            // prepare_mark wants.
            if TRACK {
                // At depth 0 no-stray gives no set flags (requires vacuous);
                // when a flag IS set, no-stray forces frames>0, so `top` is a
                // real index inside the by-block.
                assert forall|j: int| 0 <= j < self.store.captured().len()
                    && #[trigger] self.store.captured()[j]
                    implies exists|k: int| 0 <= k < prev_suffix@.len()
                        && (#[trigger] prev_suffix@[k]).1.as_nat() == j as nat by {
                    // no-stray: live frame and j < active.
                    assert(self.frames@.len() > 0 && j < self.active_saved_len.as_nat());
                    let top = (self.frames@.len() - 1) as int;
                    self.store.lemma_wf_captured_len();
                    assert(j < self.view().len());
                    // bridge: captured_in_range(diffs, top.diff_start, |diffs|, j).
                    assert(self.active_saved_len == self.frames@[top].saved_len);
                    assert(captured_in_range::<T, I>(
                        self.diff_log@,
                        self.frames@[top].diff_start as int,
                        self.diff_log@.len() as int, j as nat));
                    // captured_in_range == exists entry in [ds, |diffs|) naming j.
                    let k0 = choose|k: int| #![trigger (self.diff_log@[k])]
                        self.frames@[top].diff_start as int <= k < self.diff_log@.len()
                        && (self.diff_log@[k]).1.as_nat() == j as nat;
                    // prev_suffix == diffs[parent_diff_start..]; parent_diff_start
                    // == top.diff_start, so k0 maps to suffix index k0 - ds.
                    assert(parent_diff_start == self.frames@[top].diff_start);
                    assert(prev_suffix@[k0 - parent_diff_start as int]
                        == self.diff_log@[k0]);
                }
            }
        }
        self.store.prepare_mark(saved_len, prev_suffix);

        self.snapshots = Ghost(self.snapshots@.push(old_view));
        self.frames.push(Frame { saved_len, diff_start });
        self.active_saved_len = saved_len;

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

            // saved_len monotonicity is NO LONGER a wf clause (pop into marked region:
            // mark-after-deep-pop can record a SMALLER saved_len than the
            // parent). So nothing to prove here for saved_len.
            assert(frames.len() == old_frames.len() + 1);
            assert(new_top == old_frames.len());
            assert(frames[new_top].saved_len == saved_len);
            assert(forall|k: int| 0 <= k < old_frames.len() ==> frames[k] == old_frames[k]);
            assert(old_view.len() == saved_len.as_nat());
            // diff_start monotone: new adjacency (old_top, new) has
            // old_top.diff_start <= n == new.diff_start.
            assert forall|k: int| 0 <= k && k + 1 < frames.len() implies
                #[trigger] frames[k].diff_start <= #[trigger] frames[k + 1].diff_start
            by {
                assert(frames[k] == old_frames[k]);
                if k + 1 < new_top {
                    assert(frames[k + 1] == old_frames[k + 1]);
                    old(self).lemma_diff_start_monotone(k, k + 1);
                } else {
                    assert(k == old_frames.len() - 1);
                    assert(frames[k + 1].diff_start == diff_start);
                    old(self).lemma_diff_start_le_n(k);
                }
            }
            // snapshot length & active_saved_len for the new top frame.
            assert(snaps[new_top] == old_view);
            assert(snaps[new_top].len() == saved_len.as_nat());
            assert(frames[new_top].saved_len == saved_len);
            assert(self.active_saved_len == saved_len);

            // Bridge: the new top stratum [diff_start, n) == [n, n) is empty,
            // so captured_in_range is false everywhere; prepare_mark made
            // store.captured()[j] == false for all j < saved_len == active.
            self.store.lemma_wf_captured_len();
            assert(self.store.captured().len() == self.view().len());
            assert forall|j: int| 0 <= j < self.active_saved_len.as_nat() implies
                #[trigger] self.store.captured()[j]
                    == captured_in_range::<T, I>(
                        diffs, frames[new_top].diff_start as int, diffs.len() as int, j as nat)
            by {
                // stratum empty ⇒ RHS false; prepare_mark ⇒ LHS false.
                assert(frames[new_top].diff_start == diffs.len());
            }

            // Re-establish the per-frame frame_inv_range for the new stack.
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), diffs, frames[k].diff_start as int,
                    self.stratum_end(k), snaps[k], frames[k].saved_len.as_nat())
            by {
                let lo = frames[k].diff_start as int;
                let hi = self.stratum_end(k);
                if k == new_top {
                    // New frame: stratum [diff_start, diff_start) is empty,
                    // layer == snapshot == view. All cells uncaptured ⇒
                    // view[j] == snap[j] trivially.
                    assert(hi == diffs.len());
                    assert(lo == diffs.len());
                    assert(self.layer_above_at(k) == self.view());
                    assert(snaps[k] == old_view);
                    // Empty stratum: prove frame_inv_range from scratch.
                    assert forall|j: int| #![trigger snaps[k][j]]
                        0 <= j < frames[k].saved_len.as_nat() as int implies
                        snaps[k][j] == self.layer_above_at(k)[j]
                    by {
                        // no entry in [lo, hi) since the range is empty
                    }
                } else if k + 1 == new_top {
                    // Previous top frame: stratum unchanged; layer flips from
                    // old view to snaps[new_top] == old_view. Equal, so the
                    // old frame_inv_range transfers.
                    assert(old(self).frame_inv_range_holds(k));
                    assert(old_frames[k] == frames[k]);
                    assert(old_snaps[k] == snaps[k]);
                    assert(hi == diffs.len());
                    assert(old(self).stratum_end(k) == diffs.len());
                    assert(self.layer_above_at(k) == snaps[k + 1]);
                    assert(snaps[k + 1] == old_view);
                    assert(old(self).layer_above_at(k) == old_view);
                    assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                    old(self).lemma_diff_start_le_n(k);
                    lemma_frame_inv_range_local::<T, I>(
                        self.layer_above_at(k), diffs, diffs,
                        lo, hi, snaps[k], frames[k].saved_len.as_nat());
                } else {
                    // Deeper frames: stratum and layer (a surviving snapshot)
                    // unchanged.
                    assert(old(self).frame_inv_range_holds(k));
                    assert(old_frames[k] == frames[k]);
                    assert(old_snaps[k] == snaps[k]);
                    assert(self.layer_above_at(k) == snaps[k + 1]);
                    assert(old(self).layer_above_at(k) == old_snaps[k + 1]);
                    assert(self.layer_above_at(k) == old(self).layer_above_at(k));
                    assert(hi == old(self).stratum_end(k));
                    assert(hi == old_frames[k + 1].diff_start as int);
                    old(self).lemma_diff_start_le_n(k + 1);
                    old(self).lemma_diff_start_monotone(k, k + 1);
                    lemma_frame_inv_range_local::<T, I>(
                        self.layer_above_at(k), diffs, diffs,
                        lo, hi, snaps[k], frames[k].saved_len.as_nat());
                }
                assert(frame_inv_range::<T, I>(
                    self.layer_above_at(k), diffs, lo, hi, snaps[k],
                    frames[k].saved_len.as_nat()));
            }
        }

        VecToken {
            frame_idx: self.frames.len() - 1,
            branch_id: token_branch,
            depth: token_depth,
            container_id: token_container,
        }
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
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    pub fn restore(&mut self, token: VecToken)
        where T: core::default::Default
        requires
            old(self).wf(),
            // TRACK gate (production parity, plan 2.4): restore is uncallable
            // on an untracked vec.
            TRACK,
            // M5 validity precondition (the formal form of production's
            // is_valid + container asserts). Rejects stale/cross-container
            // tokens. Parallel to — not a substitute for — the structural
            // frame_idx-in-range precondition (design §0.5).
            old(self).is_token_valid_spec(token),
            // Structural reconstruction precondition (mechanism, not validity).
            token.frame_idx_spec() < old(self).depth_spec(),
            // Depths fit in u32 (token.depth and frames.len() are u32 in the
            // exec API); needed for fork's u32 push.
            old(self).depth_spec() < u32::MAX,
            old(self).fork_count_spec() + 1 <= u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[token.frame_idx_spec() as int],
            final(self).depth_spec() == token.frame_idx_spec(),
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, token.frame_idx_spec() as int),
    {
        // Runtime guards (plan 2.3): a verified caller has proven every
        // `requires` clause, so these are provably-true no-ops for them. An
        // unverified caller's build erases `requires`; production asserts the
        // same conditions at runtime, and so do we — the FULL restorable
        // predicate, BEFORE reading frames[token.frame_idx] or mutating
        // anything. Message parity with production for the cases its tests
        // pin ("token belongs to a different container", "abandoned future",
        // "token points beyond frame stack").
        crate::guard::check_precondition(TRACK, "restore() called on untracked vec");
        crate::guard::check_precondition(
            token.container_id.eq(self.id),
            "token belongs to a different container",
        );
        crate::guard::check_precondition(
            token.frame_idx < self.frames.len(),
            "token points beyond frame stack",
        );
        // Overflow headrooms next: `fork`'s `as u32` casts on the fork-history
        // counters must not wrap, and the genealogy walk below casts
        // frames.len() to u32. The fork-history origin list grows by one per
        // restore and is never reclaimed, so `origins.len()` is the lifetime
        // restore count: this is the ~4.29e9-restores ceiling.
        crate::guard::check_precondition(
            self.frames.len() < u32::MAX as usize,
            "Vec::restore: frame-stack depth would overflow u32",
        );
        crate::guard::check_precondition(
            self.forks.origins.len() < u32::MAX as usize,
            "Vec::restore: fork history exhausted (too many restores)",
        );
        crate::guard::check_precondition(
            self.is_on_current_branch(&token),
            "invalid restore token (abandoned future)",
        );

        let target_index = token.frame_idx;
        let target_frame = self.frames[target_index];
        let saved_len = target_frame.saved_len;
        let diff_start = target_frame.diff_start;

        let ghost pre_view = self.view();
        let ghost pre_diffs = self.diff_log@;
        let ghost snap_target = self.snapshots@[target_index as int];
        // forks is untouched by reconstruction. Establish the fork() precondition
        // facts NOW, while self == old(self) and validity holds, and carry them
        // as scalar ghosts (Verus loses whole-struct field tracking across the
        // many reconstruction mutations + the `*self` snapshot below).
        let ghost forks_origins0 = self.forks.origins@;
        let ghost forks_branch0 = self.forks.current_branch_id;
        proof {
            crate::fork_history::lemma_fork_valid_characterization(
                self.forks.origins@,
                self.forks.current_branch_id as nat,
                self.frames@.len() as nat,
                token.branch_id as nat,
                token.depth as nat);
            crate::fork_history::lemma_reaches_in_range(
                self.forks.origins@,
                self.forks.current_branch_id as nat,
                token.branch_id as nat);
            assert(token.branch_id as nat <= forks_origins0.len());
        }

        // Resize the view to EXACTLY the target's saved_len (truncate, or grow
        // with `T::default()` fillers). After this the base length is
        // saved_len throughout, so the replay below is pure overwrite-or-drop
        // (restore_entry's regrow push branch never fires) — matching the
        // overwrite-only `overlay` model. Snapshot the pre-resize state to run
        // the flat central lemma against: `wf_for_snap` holds *before* resize,
        // not after (default fillers break the top frame's uncaptured arm),
        // and the lemma is base-parametric so it accepts the resized base.
        let ghost old_self = *self;
        proof {
            saved_len.lemma_as_nat_bounded();
            // Confirm the *self read didn't disturb forks tracking.
            assert(self.forks.origins@ == forks_origins0);
            assert(self.forks.current_branch_id == forks_branch0);
        }
        self.store.resize_default(saved_len);
        // Pre-replay flag reset (production's wholesale zero / sparse
        // tag-clear, hoisted): its requires — every set flag is named by a
        // replayed entry — chains from the resize flag contract + old wf
        // (no-stray + bridge): a post-resize flag was set pre-restore, hence
        // named in the old top stratum [old_top.ds, n) ⊆ [diff_start, n).
        proof {
            // diff_start <= diff_log.len(): the target frame's stratum start
            // is within the log (wf_for_snap's diff_start bound on old_self).
            old_self.lemma_diff_start_le_n(target_index as int);
        }
        let replayed_pre = vstd::slice::slice_subrange(
            self.diff_log.as_slice(), diff_start, self.diff_log.len());

        let ghost base = self.store.data();
        let ghost base_flags = self.store.captured();
        proof {
            if TRACK {
                // Materialize resize_default's flag contract onto the ghost
                // snapshot (trigger bridge: the ensures quantifies over the
                // resized store's captured()[j]; base_flags IS that sequence).
                assert forall|j: int| 0 <= j < saved_len.as_nat() implies
                    #[trigger] base_flags[j]
                        == (j < old(self).store.captured().len()
                            && old(self).store.captured()[j]) by {
                    assert(self.store.captured()[j]
                        == (j < old(self).store.captured().len()
                            && old(self).store.captured()[j]));
                }
                // begin_restore's requires: every post-resize flag is named
                // by a replayed entry. Chain: post-resize flag ⟹ pre-restore
                // flag ⟹ (old no-stray) below old active with a live frame ⟹
                // (old bridge) captured_in_range over the old top stratum
                // [old_top.ds, n) ⊆ [diff_start, n) (diff_start monotone) —
                // the replayed slice.
                self.store.lemma_wf_captured_len();
                assert forall|j: int| 0 <= j < self.store.captured().len()
                    && #[trigger] self.store.captured()[j]
                    implies exists|k: int| 0 <= k < replayed_pre@.len()
                        && (#[trigger] replayed_pre@[k]).1.as_nat() == j as nat by {
                    assert(base_flags[j]);
                    assert(0 <= j < saved_len.as_nat());
                    assert(j < old(self).store.captured().len()
                        && old(self).store.captured()[j]);
                    assert(old(self).frames@.len() > 0
                        && j < old(self).active_saved_len.as_nat());
                    let old_top = (old(self).frames@.len() - 1) as int;
                    assert(j < old(self).view().len());
                    assert(captured_in_range::<T, I>(
                        pre_diffs,
                        old(self).frames@[old_top].diff_start as int,
                        pre_diffs.len() as int, j as nat));
                    old(self).lemma_diff_start_monotone(
                        target_index as int, old_top);
                    let k0 = choose|k: int| #![trigger (pre_diffs[k])]
                        old(self).frames@[old_top].diff_start as int <= k
                            < pre_diffs.len() as int
                        && (pre_diffs[k]).1.as_nat() == j as nat;
                    assert(diff_start as int <= k0);
                    assert(replayed_pre@[k0 - diff_start as int] == pre_diffs[k0]);
                }
            }
        }
        self.store.begin_restore(replayed_pre);
        let n = self.diff_log.len();

        // Flat central lemma: overlaying the whole tail [diff_start, n) onto
        // the resized base reconstructs snap_target on [0, saved_len). Run on
        // old_self (which satisfies wf_for_snap); its diff_log/frames/snapshots
        // match self's (resize only touched the store), and resize_default's
        // prefix-preservation gives base == old_self.view() on the shared
        // prefix — exactly the lemma's base-agreement hypothesis.
        proof {
            assert(self.diff_log@ == pre_diffs);
            assert(base.len() == saved_len.as_nat());
            assert(old_self.view() == pre_view);
            // diff_start <= n (== diff_log.len()), for the replay loop bounds.
            old_self.lemma_diff_start_le_n(target_index as int);
            assert(diff_start <= n);
            // snap_target has length saved_len (wf_for_snap: snaps[k].len() ==
            // frames[k].saved_len). Needed later for view() =~= snap_target.
            assert(snap_target == old_self.snapshots@[target_index as int]);
            assert(snap_target.len() == saved_len.as_nat());
            assert forall|j: int| 0 <= j < saved_len.as_nat() implies
                #[trigger] overlay::<T, I>(base, pre_diffs, diff_start as int, n as int)[j]
                    == snap_target[j]
            by {
                // base agrees with old_self.view() on the shared prefix.
                assert forall|m: int| 0 <= m < base.len() && m < old_self.view().len()
                    implies #[trigger] base[m] == old_self.view()[m] by {}
                old_self.lemma_cell_eq_overlay(base, target_index as int, j);
            }
        }

        // Replay [diff_start, n) backward over the resized base. Each
        // restore_entry overwrites in-range / drops out-of-range; the push
        // (regrow) branch is dead because data().len() == saved_len throughout
        // and every in-range idx (< saved_len) is < data().len().
        let mut i: usize = n;
        while i > diff_start
            invariant
                self.store.wf(),
                self.diff_log@ == pre_diffs,
                self.diff_log@.len() == n,
                self.frames@ == old(self).frames@,
                self.snapshots@ == old(self).snapshots@,
                // forks is untouched by the replay loop (needed for fork()'s
                // precondition after the loop).
                self.forks.origins@ == forks_origins0,
                self.forks.current_branch_id == forks_branch0,
                diff_start <= i <= n,
                self.store.data().len() == saved_len.as_nat(),
                base.len() == saved_len.as_nat(),
                // Work done so far == overlay of the applied suffix [i, n).
                forall|j: int| 0 <= j < saved_len.as_nat() ==>
                    #[trigger] self.store.data()[j]
                        == overlay::<T, I>(base, pre_diffs, i as int, n as int)[j],
                // All flags clear through the replay: begin_restore's
                // all-clear start, preserved by restore_entry's
                // decrease-only clause.
                TRACK ==> forall|j: int| 0 <= j < self.store.captured().len()
                    ==> !(#[trigger] self.store.captured()[j]),
            decreases i,
        {
            i -= 1;
            let (old_val, idx) = self.diff_log[i];
            proof {
                lemma_overlay_len::<T, I>(base, pre_diffs, (i + 1) as int, n as int);
            }
            self.store.restore_entry(idx, &old_val, saved_len);
            proof {
                if TRACK {
                    // all-clear preserved: decrease-only from an all-false
                    // state leaves all-false.
                    assert forall|j: int| 0 <= j < self.store.captured().len()
                        implies !(#[trigger] self.store.captured()[j]) by {
                        if self.store.captured()[j] {
                            // decrease-only: flag implies pre-entry flag —
                            // contradicting the invariant.
                            assert(false);
                        }
                    }
                }
            }
        }

        proof {
            // After loop: i == diff_start, so data == overlay(base, diffs,
            // diff_start, n) on [0, saved_len), which == snap_target by the
            // flat lemma above.
            assert forall|j: int| 0 <= j < saved_len.as_nat() implies
                #[trigger] self.store.data()[j] == snap_target[j] by {}
        }

        let ghost old_frames = self.frames@;
        let ghost old_diffs = self.diff_log@;
        let ghost old_snaps = self.snapshots@;
        // Pin the replay loop's flag bookkeeping before the truncates (the
        // store is untouched below, but binding the fact to a ghost makes it
        // robust to the heap mutations in between).
        let ghost post_replay_flags = self.store.captured();
        proof {
            if TRACK {
                self.store.lemma_wf_captured_len();
                assert(post_replay_flags.len() == saved_len.as_nat());
                assert forall|j: int| 0 <= j < post_replay_flags.len()
                    && #[trigger] post_replay_flags[j]
                    implies base_flags[j]
                        && !diff_has_index_in::<T, I>(
                            pre_diffs, diff_start as int, n as int, j as nat) by {
                    // bridge the trigger: post_replay_flags IS the current
                    // captured sequence, so the loop-exit fact fires.
                    assert(self.store.captured()[j]);
                }
            }
        }

        self.diff_log.truncate(diff_start);
        self.frames.truncate(target_index);
        self.snapshots = Ghost(self.snapshots@.subrange(0, target_index as int));

        // Set active_saved_len and rebuild the store's capture flags so the
        // bridge invariant holds for the new top frame. When the stack is
        // empty, no bridge is needed and active is reset to min.
        proof {
            // data().len() == saved_len_target after the restore loop.
            assert(self.store.data().len() == saved_len.as_nat());
            if target_index > 0 {
                // new top frame is target_index - 1; its diff_start <= old
                // target.diff_start == diff_start == new diff_log.len().
                old(self).lemma_diff_start_monotone(target_index as int - 1, target_index as int);
                // NOTE: we no longer derive "new_top.saved_len <= data().len()"
                // via saved_len monotonicity (gone, and false under pop-into-marked-region
                // pop — the parent can have a LARGER saved_len than the
                // restore target). Instead finish_restore is told to rebuild
                // capture flags over [0, data().len()) only, which is exactly
                // the range the wf bridge reads (it's gated by j < view.len()).
            }
        }
        // data().len() == target's saved_len; this is the present-cell range
        // the bridge cares about, regardless of the new top frame's saved_len.
        let present_len = self.store.len();
        let ghost surviving_view: Seq<(T, I)> = Seq::empty();
        let ghost new_top_ds_ghost: int = 0;
        if target_index > 0 {
            let new_top_frame = self.frames[target_index - 1];
            self.active_saved_len = new_top_frame.saved_len;
            let new_top_ds = new_top_frame.diff_start;
            let surviving = vstd::slice::slice_subrange(
                self.diff_log.as_slice(), new_top_ds, self.diff_log.len());
            proof {
                surviving_view = surviving@;
                new_top_ds_ghost = new_top_ds as int;
                // finish_restore's all-clear requires. Loop-exit bookkeeping:
                // a surviving flag needs base_flags[j] AND no diff entry in
                // [diff_start, n) naming j. But base_flags is the post-resize
                // state whose flags came from the PRE-restore wf (no-stray +
                // bridge): every set flag was named in [old_top.ds, n), and
                // diff_start <= old_top.ds (monotone), so every flagged slot
                // WAS named in the replayed range — contradiction. No flag
                // survives.
                assert(self.store.captured() == post_replay_flags);
                assert forall|j: int| 0 <= j < saved_len.as_nat()
                    implies !(#[trigger] self.store.captured()[j]) by {
                    if self.store.captured()[j] {
                        // route through the ghost pin (immune to the later
                        // heap mutations): trigger with range.
                        assert(j < post_replay_flags.len());
                        assert(post_replay_flags[j]);
                        assert(base_flags[j]
                            && !diff_has_index_in::<T, I>(
                                pre_diffs, diff_start as int, n as int, j as nat));
                        // base flag (post-resize) ⟹ pre-resize flag at j via
                        // resize_default's flag contract (prefix-preserving,
                        // grown region clear). base_flags was snapshotted
                        // immediately after resize, so its contract clause
                        // applies verbatim at index j < saved_len.
                        assert(0 <= j < saved_len.as_nat());
                        assert(base_flags[j]
                            == (j < old(self).store.captured().len()
                                && old(self).store.captured()[j]));
                        assert(j < old(self).store.captured().len()
                            && old(self).store.captured()[j]);
                        // ...⟹ old no-stray puts j below the old active
                        // length with a live frame, where the old bridge
                        // names it in the old top stratum ⊆ replayed range.
                        assert(old(self).frames@.len() > 0
                            && j < old(self).active_saved_len.as_nat());
                        let old_top = (old(self).frames@.len() - 1) as int;
                        assert(j < old(self).view().len());
                        assert(old(self).store.captured()[j] ==>
                            captured_in_range::<T, I>(
                                pre_diffs,
                                old(self).frames@[old_top].diff_start as int,
                                n as int, j as nat));
                        old(self).lemma_diff_start_monotone(
                            target_index as int, old_top);
                        assert(diff_has_index_in::<T, I>(
                            pre_diffs, diff_start as int, n as int, j as nat));
                        assert(false);
                    }
                }
            }
            self.store.finish_restore(surviving, present_len);
        } else {
            self.active_saved_len = <I as IndexLike>::min();
        }

        // Record the branch cut (design §0.6): fork off the token's branch at
        // the token's depth. Only `self.forks` is mutated — the store,
        // diff_log, frames, snapshots (hence the reconstruction result) are
        // untouched. `fork`'s precondition `token.branch_id <= origins.len()`
        // is discharged by the validity precondition: a valid token's branch
        // is reachable, hence a real branch id.
        proof {
            // forks untouched since entry; the fork() precondition
            // `token.branch_id <= origins.len()` was established at the top
            // (over the then-pristine forks) and carries because forks is
            // unchanged by reconstruction.
            assert(self.forks.origins@ == forks_origins0);
            assert(self.forks.current_branch_id == forks_branch0);
            assert(token.branch_id as nat <= self.forks.origins@.len());
        }
        self.forks.fork(token.branch_id, token.depth);

        proof {
            // view() now has length saved_len and agrees with snap_target
            // pointwise, so they're equal by extensionality.
            assert(self.view() =~= snap_target);
            assert(self.forks.wf());  // fork maintains fh_wf

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
                // (top-fullness "new top saved_len <= view.len()" is no longer
                // a wf clause; nothing to prove here.)
                assert(self.view().len() == saved_len.as_nat());
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

            // active_saved_len + capture-flag bridge.
            self.store.lemma_wf_captured_len();
            if frames.len() == 0 {
                // active_saved_len was set to I::min(), which == min_spec().
            } else {
                let top = (frames.len() - 1) as int;
                assert(frames[top] == old_frames[top]);
                assert(self.active_saved_len == frames[top].saved_len);
                // finish_restore rebuilt store.captured() from the surviving
                // top stratum [top.diff_start, n). Its postcondition says for
                // i < new_top.saved_len, captured()[i] iff some surviving diff
                // entry points at i. The surviving diffs slice IS the top
                // stratum, so captured_in_range matches.
                assert(frames[top].diff_start as int == new_top_ds_ghost);
                assert(surviving_view == diffs.subrange(new_top_ds_ghost, diffs.len() as int));
                // The wf bridge is gated by j < view.len(); finish_restore
                // rebuilt captured() over exactly [0, present_len) ==
                // [0, view.len()), so we prove it on that range (NOT on
                // [0, active), which may exceed view.len() after a pop into the marked region).
                assert(present_len.as_nat() == self.view().len());
                assert forall|j: int|
                    0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(
                            diffs, frames[top].diff_start as int, diffs.len() as int, j as nat)
                by {
                    // finish_restore: captured()[j] == exists kk, surviving_view[kk].1 == j.
                    // lemma_captured_subrange: that == captured_in_range over the range.
                    lemma_captured_subrange::<T, I>(
                        diffs, surviving_view, new_top_ds_ghost, diffs.len() as int, j as nat);
                }
                // NO-STRAY: a post-restore flag means a surviving diff entry
                // names j, and the new top's frame_inv_range (in-bounds
                // clause, from OLD wf's per-frame invariant preserved through
                // the truncation) bounds every such index below the new top's
                // saved_len == the restored active_saved_len.
                assert forall|j: int| 0 <= j < self.view().len()
                    && #[trigger] self.store.captured()[j]
                    implies self.frames@.len() > 0
                        && j < self.active_saved_len.as_nat() by {
                    // finish_restore's iff: pull the surviving witness.
                    assert(exists|kk: int| 0 <= kk < surviving_view.len()
                        && (#[trigger] surviving_view[kk]).1.as_nat() == j as nat);
                    let kk = choose|kk: int| 0 <= kk < surviving_view.len()
                        && (#[trigger] surviving_view[kk]).1.as_nat() == j as nat;
                    // surviving_view == diffs[new_top_ds..n): index into diffs.
                    assert(surviving_view[kk] == diffs[new_top_ds_ghost + kk]);
                    // OLD wf: frame_inv_range holds for the (old) frame at
                    // top (== target_index - 1 survives truncation), whose
                    // in-bounds clause bounds the entry's index.
                    assert(old(self).frame_inv_range_holds(top));
                    assert(diffs[new_top_ds_ghost + kk].1.as_nat()
                        < frames[top].saved_len.as_nat());
                    assert(j < self.active_saved_len.as_nat() as int);
                }
            }
            // saved_len monotonicity is no longer a wf clause — nothing to
            // re-establish for the truncated stack.
        }
    }
}

// ---------------------------------------------------------------------------
// View / VecViewIter — read-only iteration over the current contents (parity with
// production's `view()`). A `View` is a thin borrow exposing `len`/`get`; a
// `VecViewIter` walks `[0, len)`. Both carry verified contracts tying results to
// the underlying `view()` sequence.
// ---------------------------------------------------------------------------

/// Read-only handle over a `Vec`'s current contents.
pub struct VecView<'a, T, I, S, const TRACK: bool>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub(crate) vec: &'a Vec<T, I, S, TRACK>,
}

impl<'a, T, I, S, const TRACK: bool> VecView<'a, T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The abstract sequence this view exposes (the vec's current contents).
    pub open(crate) spec fn seq(&self) -> Seq<T> {
        self.vec.view()
    }

    /// The underlying vec (spec twin; the field is `pub(crate)` — privacy
    /// closeout).
    pub open(crate) spec fn vec_ref(&self) -> &Vec<T, I, S, TRACK> {
        self.vec
    }

    pub fn len(&self) -> (n: I)
        requires self.vec_ref().wf(),
        ensures n.as_nat() == self.seq().len(),
    {
        self.vec.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.vec_ref().wf(),
        ensures b == (self.seq().len() == 0),
    {
        self.vec.is_empty()
    }

    pub fn get(&self, i: I) -> (v: T)
        requires self.vec_ref().wf(), i.as_nat() < self.seq().len(),
        ensures v == self.seq()[i.as_nat() as int],
    {
        self.vec.get_index(i)
    }

    /// Iterator over `[0, len)` in order.
    pub fn iter(&self) -> (it: VecViewIter<'a, T, I, S, TRACK>)
        requires self.vec_ref().wf(),
        ensures it.vec_ref() == self.vec_ref(), it.pos_spec() == 0,
    {
        VecViewIter { vec: self.vec, pos: 0 }
    }
}

/// Forward index iterator over a `Vec`'s contents.
pub struct VecViewIter<'a, T, I, S, const TRACK: bool>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub(crate) vec: &'a Vec<T, I, S, TRACK>,
    pub(crate) pos: usize,
}

impl<'a, T, I, S, const TRACK: bool> VecViewIter<'a, T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The underlying vec (spec twin; the field is `pub(crate)`).
    pub open(crate) spec fn vec_ref(&self) -> &Vec<T, I, S, TRACK> {
        self.vec
    }

    /// The cursor position (spec twin; the field is `pub(crate)`).
    pub open(crate) spec fn pos_spec(&self) -> nat {
        self.pos as nat
    }

    /// Advance one step. Yields `Some(view[pos])` and increments `pos` while
    /// in range; `None` (leaving `pos` unchanged) at the end. Mirrors
    /// production's `VecViewIter::next`. (Inherent method with an explicit
    /// contract — the `Iterator` trait spec plumbing isn't needed for the
    /// correctness property.)
    pub fn next(&mut self) -> (r: Option<T>)
        requires
            old(self).vec_ref().wf(),
            old(self).pos_spec() <= old(self).vec_ref().view().len(),
            old(self).vec_ref().view().len() < I::max_nat(),
        ensures
            final(self).vec_ref() == old(self).vec_ref(),
            old(self).pos_spec() < old(self).vec_ref().view().len() ==> {
                &&& r == Some(old(self).vec_ref().view()[old(self).pos_spec() as int])
                &&& final(self).pos_spec() == old(self).pos_spec() + 1
            },
            old(self).pos_spec() >= old(self).vec_ref().view().len() ==> {
                &&& r is None
                &&& final(self).pos_spec() == old(self).pos_spec()
            },
    {
        let len = self.vec.len();
        if self.pos >= len.as_usize() {
            return None;
        }
        let i = match I::try_from_usize(self.pos) {
            Some(x) => x,
            None => { assert(false); return None; },
        };
        let v = self.vec.get_index(i);
        self.pos = self.pos + 1;
        Some(v)
    }
}

// Concrete constructors, mirroring production's two `new()` impls.

impl<T, I, const TRACK: bool> Vec<T, I, crate::parallel_store::ParallelStore<T, I>, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// Empty tracked vector backed by a `ParallelStore` (flag vector).
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::parallel_store::ParallelStore::new())
    }
}

impl<T, I, const TRACK: bool> Vec<T, I, crate::inline_store::InlineStore<T, I>, TRACK>
where
    T: crate::tagged::Tagged,
    I: IndexLike,
{
    /// Empty tracked vector backed by an `InlineStore` (tag bit stolen from
    /// the value's repr).
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::inline_store::InlineStore::new())
    }
}


} // verus!

// prod-parity: production derives `Debug` on `VecToken` (`token.rs`); the
// consumer needs it (structs holding tokens derive `Debug`, and the caches'
// method bounds require `Debug` transitively). Manual because deriving inside
// `verus!{}` is unsupported. Mirrors production's field layout.
impl core::fmt::Debug for VecToken {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("VecToken")
            .field("frame_idx", &self.frame_idx)
            .field("branch_id", &self.branch_id)
            .field("depth", &self.depth)
            .field("container_id", &self.container_id)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Production-shaped trusted glue (migration plan Phase 4, trust group E).
//
// A generic `impl Into<I>` bound carries no Verus-visible relation between
// the input and the converted index, so the conversion cannot live inside a
// verified body. These wrappers are one-line delegations to the verified
// `get_index`/`set_index` cores: the conversion happens here (trusted, just
// `Into::into`), and every safety property — bounds panic, capture protocol,
// snapshot fidelity — is enforced by the verified core they call.
// Enumerated in doc/design/02-trust-boundary.md group E.
// ---------------------------------------------------------------------------

impl<T, I, S, const TRACK: bool> Vec<T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    /// Production-shaped `get`: accepts anything convertible to the index
    /// type (macro-generated ids implement `Into<Index>`). Delegates to the
    /// verified `get_index`.
    #[inline(always)]
    pub fn get(&self, index: impl Into<I>) -> T {
        self.get_index(index.into())
    }

    /// Production-shaped `set`. Delegates to the verified `set_index`.
    #[inline(always)]
    pub fn set(&mut self, index: impl Into<I>, value: T) {
        self.set_index(index.into(), value)
    }
}

/// std `Iterator` for `VecViewIter` — trusted 1-line delegation to the
/// verified inherent `next` (trust group E). Enables `for x in
/// vec.view_handle().iter()`; every yielded element comes from the verified
/// method, whose contract proves in-order enumeration of `view()`.
impl<'a, T, I, S, const TRACK: bool> Iterator for VecViewIter<'a, T, I, S, TRACK>
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    type Item = T;

    #[inline(always)]
    fn next(&mut self) -> Option<T> {
        // Inherent verified `next` (same name resolves to the inherent method
        // on the concrete type inside its own impl; here we must call it
        // explicitly to avoid trait-method recursion).
        VecViewIter::next(self)
    }
}

// ---------------------------------------------------------------------------
// Forged-state unit tests (migration plan 2.5, in-module half). These
// construct token states unreachable through the public API — possible here
// because the module sees the token fields — and check the runtime guards
// reject them BEFORE mutation. They complement tests/misuse.rs (public-API
// misuse) and stay valid after the Phase 5 privacy closeout (in-module code
// keeps field access).
// ---------------------------------------------------------------------------

#[cfg(test)]
mod forged_token_tests {
    use super::{ShrinkPolicy, Vec, VecToken};
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    /// A token with a forged out-of-range frame index: rejected by the
    /// frame-liveness guard before any state change.
    #[test]
    fn forged_frame_index_rejected_before_mutation() {
        let mut v = V::new();
        for i in 0..8 {
            v.push(i);
        }
        let genuine = v.mark(ShrinkPolicy::Never);
        v.push(100);

        let forged = VecToken {
            frame_idx: 999,
            ..genuine
        };
        assert!(
            !v.is_valid_token(&forged),
            "forged frame index must be invalid"
        );

        let before = read_back(&v);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            v.restore(forged);
        }));
        assert!(r.is_err(), "forged frame index must panic");
        assert_eq!(before, read_back(&v), "rejected restore must not mutate");

        // The genuine token still restores.
        v.restore(genuine);
        assert_eq!(v.len(), 8);
    }

    /// A token with a forged branch id (a branch that never existed): rejected
    /// by the genealogy walk.
    #[test]
    fn forged_branch_id_rejected() {
        let mut v = V::new();
        v.push(1);
        let genuine = v.mark(ShrinkPolicy::Never);
        v.push(2);
        let forged = VecToken {
            branch_id: genuine.branch_id + 7,
            ..genuine
        };
        assert!(
            !v.is_valid_token(&forged),
            "forged branch id must be invalid"
        );
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            v.restore(forged);
        }));
        assert!(r.is_err());
        assert_eq!(v.len(), 2, "rejected restore must not mutate");
    }

    /// A token with a forged depth beyond the branch bound: rejected by the
    /// genealogy walk even though the frame index is live.
    #[test]
    fn forged_depth_rejected() {
        let mut v = V::new();
        v.push(1);
        let genuine = v.mark(ShrinkPolicy::Never);
        v.push(2);
        let forged = VecToken {
            depth: genuine.depth + 100,
            ..genuine
        };
        assert!(!v.is_valid_token(&forged), "forged depth must be invalid");
    }
}

#[cfg(test)]
mod mixed_component_token_tests {
    use super::ShrinkPolicy;
    use crate::dense_id::DenseId31;
    use crate::inline_store::InlineStore;
    use crate::parallel_store::ParallelStore;
    use crate::sparse_set::{SparseSet, SparseSetToken};
    use crate::vec::Vec as SpVec;

    type Set = SparseSet<u32, DenseId31, ParallelStore<u32, DenseId31>, true>;

    fn empty_set() -> Set {
        SparseSet {
            dense: SpVec::<u32, DenseId31, ParallelStore<u32, DenseId31>, true>::new(),
            sparse: SpVec::<DenseId31, DenseId31, InlineStore<DenseId31, DenseId31>, true>::new(),
            indices: SpVec::<DenseId31, DenseId31, InlineStore<DenseId31, DenseId31>, true>::new(),
        }
    }

    /// A compound token whose components come from DIFFERENT marks (dense
    /// from mark 1, sparse/indices from mark 2): the atomic prevalidation
    /// must reject it before restoring any component. (Frankentokens are
    /// constructible here because the module sees the token fields.)
    #[test]
    fn mixed_mark_compound_token_rejected_atomically() {
        let mut s = empty_set();
        let id1 = s.add(10);
        let tok1 = s.mark(ShrinkPolicy::Never);
        let id2 = s.add(20);
        let tok2 = s.mark(ShrinkPolicy::Never);
        let id3 = s.add(30);

        // Consume tok2's frame entirely on the dense component only... no —
        // build the frankentoken directly: dense from tok1, rest from tok2.
        let franken = SparseSetToken {
            dense: tok1.dense,
            sparse: tok2.sparse,
            indices: tok2.indices,
        };
        // Restore with tok2 first, consuming tok2's frames (and cutting
        // tok1's branch? No: tok1 is an ancestor, still valid). After this,
        // franken.dense (tok1, live ancestor frame) is valid but
        // franken.sparse/indices (tok2, just consumed) are not.
        s.restore(tok2);
        assert!(
            !s.is_valid_token(&franken),
            "mixed/consumed compound must be invalid"
        );

        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            s.restore(franken);
        }));
        assert!(r.is_err(), "mixed compound restore must panic");
        // Atomicity: the set is exactly the tok2 state — dense was NOT
        // restored to tok1's snapshot before the panic.
        assert!(s.contains(id1));
        assert!(s.contains(id2));
        assert!(!s.contains(id3));
        assert_eq!(s.get(id1), 10);
        assert_eq!(s.get(id2), 20);
    }
}
