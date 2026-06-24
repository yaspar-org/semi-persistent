# The flat / target-clamped central lemma

The reconstruction proof uses a **flat** central lemma: it reconstructs only the
*target* snapshot, clamped to the target's `saved_len`, directly from the whole
replayed diff range. This is what lets `wf` drop `saved_len` monotonicity. The
alternative, a **layered** lemma (reconstruct each `snapshots[k]` on
`[0, saved_k)` by overlaying stratum k onto `snapshots[k+1]`), needs overlay to
write *past the end* of an intermediate `snapshots[k+1]` when saved_lens are
non-monotone (a snapshot-level regrow); the flat lemma never reconstructs
intermediates, so that problem does not arise. This chapter is the per-cell
argument behind it.

---

## 0. Worked scenario (non-monotone saved_lens)

The recipe: **set length to `saved_target` (chop if longer, grow+pad with
default if shorter), then replay `[diff_start_target, n)` backward: overwrite
in-range, drop `idx ≥ saved_target`.** Traced on a non-monotone stack:

```
 push A,B,C,D ; mark→f0 (saved0=4, ds0=0)            snap0=[A,B,C,D]
 set(1,X)            log (B,1)                         view=[A,X,C,D]
 pop j=3             log (D,3); pop                    view=[A,X,C]
 pop j=2             log (C,2); pop                    view=[A,X]
 mark→f1 (saved1=2, ds1=3)   ← saved1(2) < saved0(4), NON-MONOTONE   snap1=[A,X]
 set(0,Y)            log (A,0)                          view=[Y,X]
 push Z                                                 view=[Y,X,Z]

 diff_log:   pos0    pos1    pos2  │  pos3        n=4
            (B,1)   (D,3)   (C,2)  │ (A,0)
            └──── stratum 0 ──────┘└ stratum 1 ┘
                                          j=0  j=1  j=2  j=3
 str1   │(A,0)│                      grid: str1 hits col 0
 str0   │     │(B,1)│(C,2)│(D,3)│           str0 hits cols 1,2,3
 view = [ Y     X     Z ]
 snap1= [ A     X ]
 snap0= [ A     B     C     D ]
```

**Restore to f1** (saved1=2): chop view→`[Y,X]`; replay `[3,4)` backward:
`(A,0)` overwrite → `[A,X]` == snap1 ✓. (Stratum-0 entries at pos0–2 are
*outside* `[ds1,n)=[3,4)`, never applied; correct, since f1's value at col 0
is A regardless.)

**Restore to f0** (saved0=4): grow+pad view→`[Y,X,Z,d]`; replay `[0,4)`
backward:
```
 (A,0) idx0<4 overwrite → [A,X,Z,d]
 (C,2) idx2<4 overwrite → [A,X,C,d]
 (D,3) idx3<4 overwrite → [A,X,C,D]
 (B,1) idx1<4 overwrite → [A,B,C,D]   == snap0 ✓
```
The padded default `d` (col 3) and transient `Z` (col 2) are both overwritten
by stratum-0 diffs; **coverage** held. No snapshot-level regrow: we never
built snap1 to get snap0; we flatly replayed both strata onto the padded base,
clamped to saved0. Lowest-position-in-range wins per cell.

**Double-hit check** (same cell in two strata): if col 0 is captured in both
f0 (pos0) and f1 (pos1), restoring to f0 replays `[0,n)` and the **lowest**
position (pos0, f0's entry) wins = f0's value; restoring to f1 replays `[1,n)`,
excluding pos0, so f1's entry wins. "Lowest-position-*within-the-replayed-
range* wins" is exactly `lemma_overlay_lowest` (§3).

---

## 1. Why the layered lemma forces snapshot-level regrow (the thing we avoid)

Layered induction reconstructs `snapshots[k]` by `overlay(snapshots[k+1],
stratum_k)`. If `saved_k > saved_{k+1}` (legal once monotonicity is dropped,
`mark` after a deep pop), then `snapshots[k]` has cells `[saved_{k+1},
saved_k)` that lie *beyond* `snapshots[k+1]`. The overlay would have to *grow*
`snapshots[k+1]` to write them, a push/regrow at the snapshot level, needing a
3-way `overlay` and new lemmas. We want to avoid that.

## 2. The flat statement

Reconstruct the target directly from the **whole** replayed range
`[diff_start_target, n)`, against a base that is already `saved_target` long:

```
lemma_snap_eq_overlay_flat(target):
  requires
    wf_for_snap(),
    0 <= target < frames.len(),
    base.len() == saved_target,                       // restore pads/chops first
    forall j < saved_target: base[j] == snapshots[target][j]
        OR  j is captured somewhere in [diff_start_target, n)   // see §4 (coverage)
  ensures
    forall j < saved_target:
        overlay(base, diff_log, diff_start_target, n)[j] == snapshots[target][j]
```

Key: `overlay` here is the **existing overwrite-only** one. Because
`base.len() == saved_target` and every entry with `idx >= saved_target` is
skipped (`idx >= prev.len()` since `prev.len() == saved_target` throughout,
overwrite-only overlay preserves length), out-of-range entries vanish exactly
as production's `restore_entry` drops them. No regrow branch.

Actually the clean base to feed it is **`snapshots[target]` itself padded
isn't needed**; see §4: we feed the *resized view* and show it equals
`snapshots[target]` cell-by-cell via the two cases.

## 3. The winning entry: "lowest-position-wins"

Across `[diff_start_target, n)` the same index `j` may appear in multiple
strata (target's, target+1's, ...). Uniqueness holds only *within* a stratum,
not across. So `lemma_overlay_captured` (which requires global uniqueness in
the range) does NOT apply. We need:

```
lemma_overlay_lowest(base, diffs, lo, hi, p, j):
  requires
    0 <= j < base.len(),
    lo <= p < hi <= diffs.len(),
    diffs[p].1 == j,                          // p hits j
    forall q: lo <= q < p ==> diffs[q].1 != j // p is the LOWEST hitter of j in [lo,hi)
  ensures
    overlay(base, diffs, lo, hi)[j] == diffs[p].0
```

Proof: induction on `hi - lo`. At the outermost step `lo`:
- if `diffs[lo].1 == j` then `p == lo` (p is the lowest, and lo hits j) and the
  final update writes `diffs[lo].0`. Entries in `[lo+1,hi)` may also hit j but
  they're applied *inside* (overwritten by the lo update). ✓
- if `diffs[lo].1 != j` then `p > lo`; by IH `overlay(lo+1,hi)[j] ==
  diffs[p].0`, and the lo update (different index) doesn't disturb j. ✓

This is strictly more general than `lemma_overlay_captured` (which requires
global uniqueness in the range) and is what the flat proof uses.

## 4. Connecting lowest-position-wins to `snapshots[target]`

Claim: for `j < saved_target`, the lowest-position entry in
`[diff_start_target, n)` hitting `j` (if any) holds `snapshots[target][j]`;
if no entry hits `j`, then `view[j] == snapshots[target][j]` (uncaptured at the
target level, base holds it).

This is exactly the **target frame's own `frame_inv_range`**, lifted to the
whole range:
- The target's stratum is `[diff_start_target, stratum_end(target))`, the
  *lowest* sub-range of `[diff_start_target, n)`. So the lowest hitter of `j`
  in the *whole* range, if it lies in the target's stratum, is the target's
  own captured entry → holds `snapshots[target][j]` by target's frame_inv
  captured case. ✓
- If the target's stratum does NOT hit `j`: target's frame_inv *uncaptured*
  case gives `j < layer_above(target).len()` and `layer_above(target)[j] ==
  snapshots[target][j]`, where `layer_above(target) == snapshots[target+1]`
  (or the view if target is top). Now recurse the SAME argument at `target+1`:
  the lowest hitter of `j` in `[diff_start_{target+1}, n)` holds
  `snapshots[target+1][j] == snapshots[target][j]`. Composing down the stack,
  the lowest hitter of `j` in the whole `[diff_start_target, n)` holds
  `snapshots[target][j]`; and if none hits, `view[j] == snapshots[target][j]`.

So the flat lemma's core is a **downward induction that establishes a single
per-cell fact**, "lowest hitter in `[diff_start_target,n)` holds
`snap_target[j]`, or none hits and `view[j] == snap_target[j]`", rather than
reconstructing each intermediate snapshot as a full sequence. The induction
carries a *scalar* per-cell equality, never a "this snapshot equals that
sequence on its whole domain" obligation, so non-monotone saved_lens never
force a snapshot-level regrow: cell `j` of the target with
`j >= saved_{target+1}` simply must be captured in the target's own stratum
(coverage at the target level: uncaptured ⟹ `j < layer_above.len() ==
saved_{target+1}`), so it falls in the captured case and the recursion stops at
the target's stratum.

### The crisp restatement (what to actually prove)

Define a spec helper:
```
target_cell(view, diffs, frames, snaps, target, j) -> T :=
    if  some entry in [diff_start_target, n) hits j:
            (lowest such entry).0
    else
            view[j]
```
Then the flat central lemma is:
```
forall j < saved_target:  target_cell(...) == snapshots[target][j]
```
proved by downward induction on the frame index using each frame's
`frame_inv_range` (captured case gives the entry's value; uncaptured case steps
to the next frame and shrinks `[diff_start, n)` to `[diff_start_{k+1}, n)`).

And separately, `lemma_overlay_lowest` (§3) connects `target_cell` to the
actual `overlay` result on the resized base. Two clean pieces.

## 5. What this buys

- **Drops `saved_len` monotonicity** cleanly: nowhere does the flat proof need
  `saved_k <= saved_{k+1}`. Coverage (uncaptured ⟹ `j < layer_above.len()`)
  does all the work and is already in `frame_cell_inv`.
- **Keeps overwrite-only `overlay`**: no regrow branch, no `saved_len` param,
  no 3-way regrow overlay (which would need five lemmas reproved).
- The two pieces are `lemma_overlay_lowest` (§3, standalone) and the
  `target_cell` downward induction (§4). The per-cell scalar carry is simpler
  than a sequence-level induction: every step is a direct `frame_inv_range`
  case application (via `lemma_frame_inv_arm_at`), under the named
  `frame_cell_inv` trigger.
- `restore` (see [04-pop](04-pop.md) §3) then composes them:
  `resize_default(saved_target)` gives a base of length `saved_target` agreeing
  with `snap_target` on uncaptured cells, and `lemma_overlay_lowest` + the flat
  lemma give `view == snap_target`.

---
[← Table of Contents](00-table-of-contents.md)
