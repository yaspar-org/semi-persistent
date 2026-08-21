# Design alternatives: restore regrow & capture-flag representation

Two independent design axes, each with the chosen point and the rejected
alternatives recorded with their trade-offs. **Part 1** is how `restore`
regrows a popped region (the value to place in a resurrected cell). **Part 2**
is how the per-cell "already captured in this frame" flag is represented, which
sets the time cost of `mark` and `restore`'s tag-rebuild. They are orthogonal:
any Part-1 choice composes with any Part-2 choice.

---

# Part 1: Restore regrow

When `restore` rolls back to a frame whose `saved_len` is larger than the
current `view().len()`, i.e. the program popped cells *out of the marked
region* after the mark, restore must **regrow** the vector back to
`saved_len`. A pop, played in reverse, becomes a push, and that push needs a
real value of type `T` to place at the regrown slot. There are three ways to
supply it; the crate uses the first.

## A. Default + resize (chosen)

`restore` calls `resize_default(saved_len)` before the replay: truncate if the
view is longer, else extend with `T::default()` fillers. The fillers are
immediately overwritten by the overwrite-only replay (every popped marked cell
has a capture entry holding the marked value, by the coverage invariant).

- **Cost on the Part-1 axis:** regrow plus replay stays **O(k)** (k = diff
  entries replayed). `resize_default` is O(Δlen) where Δlen ≤ k, then one
  replay pass. Part 2 adds the chosen backend's parent/bitmap capture-state
  work. Δlen redundant *writes* of cheap default values.
- **Bound:** each frame's diff stratum is ≤ that frame's `saved_len`.
  `pop` uses conditional first-write-wins `capture` (not force-record), and
  `push` calls `mark_captured` when re-entering a popped marked index, so each
  index has ≤ 1 entry per frame. Across nested frames, the total log is bounded
  by the sum of their saved lengths.
- **Requires:** `T: Default`. Free for the e-graph domain (dense ids default
  to 0). Excludes non-defaultable `T`.

### Soundness: fabricated defaults are never observable

`T::default()` is fabricated in exactly one place, `resize_default`'s regrow
fillers, and **no such filler ever survives into `view()`**. Every filler
occupies a popped marked cell `j in [old_len, saved_len)`, and the coverage
invariant guarantees that cell has a capture entry holding `snap[j]`; the
replay overwrites the filler with it. This is not a separate proof obligation:
it is *entailed by the headline theorem* `view() == snapshots[token.frame_idx]`.
The snapshot is the deep copy of what the user saw at mark time; a fabricated
filler was never a user value, so if one survived, `view() != snapshot` and the
theorem would fail. Hence the theorem already rules it out.

Consequently `T::default()`'s *value* is never constrained, the store-layer
`resize_default` contract places no axiom on it, because the value is never
read into a result. A default that *does* appear in a restored view is one the
user deliberately pushed/set; it is captured and restored as the genuine
marked value, not as a fabrication. Default-the-filler and default-the-user-
value are never conflated.

## B. No Default: scan/sort regrow by index

Drop the `Default` bound. Coverage guarantees at least one replay-range entry
for every index in `[final_len, saved_len)`, but an index can occur once in
each of several nested strata. Because reverse replay makes the
**lowest-position** entry in the replay range win, a scan-based regrow must
select that entry for each index. It can build an index-to-lowest-position map
and then push winners in increasing index order, or sort/group entries while
preserving the same winner rule.

- **Cost:** an additional O(k) scan plus O(k) temporary map space, or
  O(k log k) sorting. The constant-factor effect has not been measured in this
  repository; it needs Criterion evidence before making a runtime claim.
- **Bound:** same per-frame bound as A, using conditional capture.
- **Requires:** no `Default`, but still the copy/clone capability needed to
  materialize selected log values. `Clone` and `Default` are independent trait
  requirements; neither is generally weaker than the other.

## C. Force-record pops (retired predecessor): UNBOUNDED

An earlier implementation called `force_capture` unconditionally: it logged the
popped cell every time, ignoring the capture bit. On restore the
highest-position filler entry supplied the regrow push value (overwritten by the
lower first-write-wins entry), so it was *correct*.

- **Cost on the Part-1 axis:** O(k), simplest regrow/replay code; Part 2 still
  adds capture-state rebuilding.
- **Additional diff bound: none in terms of `saved_len`.** A `push`/`pop` loop on one index logs an entry every
  iteration (push resets the capture bit; force_capture ignores it). An
  adversary controlling push/pop can exhaust memory. This is why the design was
  replaced in both production and the verified crate. `force_capture` remains
  in the verified backend trait but has no vector call site.

## Summary

| | regrow + replay time | diff bound | `T` bound |
|---|---|---|---|
| A. Default + resize | O(k) | each frame ≤ its saved length | `Default` |
| B. scan/sort regrow | O(k) extra scan or O(k log k) sort | each frame ≤ its saved length | existing copy/clone bound; no `Default` |
| C. force-record (retired) | O(k) | no saved-length bound | existing copy/clone bound; no `Default` |

The `frame_cell_inv` / coverage-invariant foundation in `vec.rs` is shared by
A and B, only the regrow mechanism in `restore` and the `T` bound differ, so
switching A↔B later is localized to `restore` + the store's resize method.

---

# Part 2: Capture-flag representation

The per-cell capture flag answers "has this cell already been logged in the
*current* frame?", the test that enforces first-write-wins. Its representation
fixes the cost of three operations:

- `mark` must reset the flag so the new frame starts with nothing captured;
- `restore` lands back in the **parent** frame and must rebuild the flag to
  mean "captured in the parent" (the replay clears every tag it overwrites via
  `into_repr`, so without a rebuild a later `set` to a parent-captured cell
  would double-log and break the bound);
- `capture`/`set`/`pop` read and set it.

Write `n` = vector length, `r` = entries in the restored strata (replayed),
`p` = entries in the parent stratum, and `w` = materialized packed-bitmap words.
The replay itself is **O(r)** and irreducible (it is the work of undoing). The
question is the *extra* cost of flag bookkeeping on top of that.

## D. One stolen bit + rescan (CHOSEN)

The flag is a single bit: for `InlineStore`, the niche bit stolen from the
value's repr (zero extra memory); for `ParallelStore`, one bit in a packed
`u64` bitset. `mark` resets it: `InlineStore` clears only the parent stratum's
captured slots (O(parent diff)); `ParallelStore` zeroes all `w` materialized
words. The bitmap can retain a prior high-water allocation, so `w` is not
necessarily the current `ceil(n/64)`. Restore clears current flags, replays,
then scans the parent stratum to re-set its bits.

- **Cost:** inline restore is O(r+p); parallel restore is O(r+p+w).
  Inline mark is O(parent diff), and parallel mark is O(w); neither copies
  values. The `+p` is the price of recovering "captured in parent" from the
  parent's diff slice.
- **Memory:** **1 bit/cell**, and for `InlineStore`, *zero* extra bytes (the
  bit is niched into the value). This is the design's headline property.
- **Flag representation:** no capture-depth counter to overflow. The containing
  vector still has independent `u32` limits on open frame depth and fork
  history.

The `+p` rescan is the accepted cost. It is not a hidden blow-up: `p` is the
size of the frame you are returning into, so `restore` is O(work-unwound +
work-in-parent), proportional to the relevant frames, never to total history.
(A micro-optimization shrinks it to O(r): replay only clears the `r` restored
indices, so only cells in `p ∩ r` need re-setting, but testing membership in
`p` in O(1) needs a per-cell "captured-in-which-frame" structure, i.e. it just
relocates the cost to option E. Not worth it.)

## E. Per-cell capture-depth (alternative)

No implementation or benchmark of this alternative is retained in this
repository. The following is an algorithmic comparison, not evidence about a
named predecessor or measured workload.

Store a per-cell **capture-depth** `capture_depths[i]: C` (`C = u8`/`u16`) =
"the frame *depth* that last captured cell `i`", in a **separate** array (not
inline). With a frame at depth `d`, a first write to cell `i` is
`capture_depths[i] < d` → capture `(i, old, old_capture_depth)` and set
`capture_depths[i] = d`; a repeat is `≥ d` → skip. The diff entry carries the
*old capture-depth*, and backtrack restores it during the **same reverse
replay** that restores values. Crucially:

- **`mark` is O(1)**: bump the depth counter; no per-cell touch, no bitset
  zero, no allocation. (Our chosen design's `mark` is O(parent diffs) inline
  or O(w) for `w` materialized parallel-bitmap words.)
- **No parent rescan on backtrack.** Because each diff entry stores the
  `old_capture_depth`, the O(r) reverse replay that restores values *also*
  restores the capture-depths; there is no separate `finish_restore` scan, so
  backtrack is a clean **O(r)**. The `+p` term disappears.
- **The cap is on NESTING DEPTH, not total marks.** Depth *decreases* on
  backtrack (it is restored, not monotone), so `C` bounds *simultaneous nested*
  marks: `u16` ⇒ 65 535 nested, `u8` ⇒ 255, far past any real search depth. The
  depth is rolled back with the diff, so it never accumulates over the run; the
  ceiling is on concurrent nesting, not on the total number of marks ever taken.
- **Memory: `N × sizeof(C)` per vector in a separate array**, unless depth is
  stored inline with each value. The repository has no representative
  end-to-end measurement establishing which layout is preferable.

So E has a strictly lower asymptotic flag-maintenance profile than our chosen D, O(1)
mark, rescan-free O(r) backtrack, at the cost of `N × sizeof(C)` memory and a
nesting-depth ceiling.

### Why this crate currently uses D

For inline identifiers, D reuses a representation bit and therefore adds no
separate resident capture array or wider cell. Reads still mask the
representation bit. E can preserve value-read density by keeping depths in a
separate array; in that layout ordinary reads need not touch the depth array,
while captured writes do touch a second memory stream. Storing depth inline
would widen cells instead. These are concrete layout differences, but claims
about cache misses, hot-loop dominance, or end-to-end speed require Criterion
measurements and are not established here.

D consequently trades the extra O(p) restore rescan and bridge-invariant proof
for a one-bit inline flag with no separate capture array. E has O(1) flag reset
at mark and restores depths during the O(r) replay, at the cost of
`N * sizeof(C)` separate memory (or wider cells) and a nesting-depth ceiling.

## Summary (Part 2)

| | read density & access cost | tracking memory | `mark` | backtrack flag | cap |
|---|---|---|---|---|---|
| D. one-bit flag (chosen) | inline ID cells stay one word; reads mask the tag | 1 bit; no separate inline allocation | O(parent diffs) inline / O(w) parallel | +O(p), plus O(w) parallel clear | no flag-specific depth cap |
| E. capture-depths | separate layout leaves ordinary value reads unchanged but adds a stream on captures; inline layout widens cells | `N * sizeof(C)`/vec if separate | O(1) | restored during O(r) replay | nesting depth (`u16`: at most 65,535 nonzero depth values, depending on encoding) |

Switching to E would be a backend-and-proof change: the store's flag type,
`mark`, replay contracts, and bridge invariant all change. Choosing it on
performance grounds requires a representative Criterion comparison.

---
[← Table of Contents](00-table-of-contents.md)
