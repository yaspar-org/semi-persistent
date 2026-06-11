# Design alternatives: restore regrow & capture-flag representation

Two independent design axes where we chose one point and want the rejected
ones on record. **Part 1** is how `restore` regrows a popped region (the value
to place in a resurrected cell). **Part 2** is how the per-cell "already
captured in this frame" flag is represented, which sets the time cost of
`mark` and `restore`'s tag-rebuild. They are orthogonal: any Part-1 choice
composes with any Part-2 choice.

---

# Part 1 — Restore regrow

When `restore` rolls back to a frame whose `saved_len` is larger than the
current `view().len()` — i.e. the program popped cells *out of the marked
region* after the mark — restore must **regrow** the vector back to
`saved_len`. A pop, played in reverse, becomes a push, and that push needs a
real value of type `T` to place at the regrown slot. There are three ways to
supply it. We chose the first; the others are recorded here for the record.

## A. Default + resize (CHOSEN, being verified)

`restore` calls `resize_default(saved_len)` before the replay: truncate if the
view is longer, else extend with `T::default()` fillers. The fillers are
immediately overwritten by the overwrite-only replay (every popped marked cell
has a capture entry holding the marked value, by the coverage invariant).

- **Cost:** restore stays **O(k)** (k = diff entries replayed). `resize_default`
  is O(Δlen) where Δlen ≤ k, then one replay pass. Δlen redundant *writes* of
  cheap default values.
- **Bound:** diff log ≤ `saved_len`. `pop` uses conditional first-write-wins
  `capture` (not force-record), and `push` calls `mark_captured` when
  re-entering a popped marked index, so each index has ≤ 1 entry per frame.
- **Requires:** `T: Default`. Free for the e-graph domain (dense ids default
  to 0). Excludes non-defaultable `T`.

### Soundness: fabricated defaults are never observable

`T::default()` is fabricated in exactly one place — `resize_default`'s regrow
fillers — and **no such filler ever survives into `view()`**. Every filler
occupies a popped marked cell `j in [old_len, saved_len)`, and the coverage
invariant guarantees that cell has a capture entry holding `snap[j]`; the
replay overwrites the filler with it. This is not a separate proof obligation:
it is *entailed by the headline theorem* `view() == snapshots[token.frame_idx]`.
The snapshot is the deep copy of what the user saw at mark time; a fabricated
filler was never a user value, so if one survived, `view() != snapshot` and the
theorem would fail. Hence the theorem already rules it out.

Consequently `T::default()`'s *value* is never constrained — the store-layer
`resize_default` contract places no axiom on it — because the value is never
read into a result. A default that *does* appear in a restored view is one the
user deliberately pushed/set; it is captured and restored as the genuine
marked value, not as a fabrication. Default-the-filler and default-the-user-
value are never conflated.

## B. No Default — scan/sort regrow by index

Drop the `Default` bound. Because uniqueness + coverage guarantee every index
in `[final_len, saved_len)` has exactly one entry holding `snap[j]`, restore
can regrow by locating each target index's entry: either a second pass building
an index→entry map, or sorting the regrow slice by index, then pushing in
increasing-index order.

- **Cost:** restore becomes **2×k** (extra pass) or **O(k log k)** (sort) —
  redundant *reads/searches* instead of writes. This is the main reason we
  did not pick it: it roughly doubles restore time.
- **Bound:** same as A (≤ saved_len), uses conditional capture.
- **Requires:** only `T: Clone` (strictly weaker than `Default`: every `Copy`
  is `Clone`, not every type is `Default`). Worth revisiting if `T` is ever
  large/expensive-to-construct, where A's filler writes would dominate.

## C. Force-record pops (production today) — UNBOUNDED, do not adopt

Production's `pop` calls `force_capture` unconditionally — it logs the popped
cell every time, ignoring the capture bit. On restore the highest-position
filler entry supplies the regrow push value (overwritten by the lower
first-write-wins entry), so it is *correct*.

- **Cost:** restore O(k), simplest code.
- **Bound: NONE.** A `push`/`pop` loop on one index logs an entry every
  iteration (push resets the capture bit; force_capture ignores it). An
  adversary controlling push/pop exhausts memory. **This is a latent DoS in
  production.** It is the reason we diverged: if the Default version verifies,
  propagate the bounded design back to production.

## Summary

| | restore time | diff bound | `T` bound |
|---|---|---|---|
| A. Default + resize | O(k) | ≤ saved_len | `Default` |
| B. scan/sort regrow | 2k or k·log k | ≤ saved_len | `Clone` |
| C. force-record (prod) | O(k) | **unbounded (DoS)** | none |

The `frame_cell_inv` / coverage-invariant foundation in `vec.rs` is shared by
A and B — only the regrow mechanism in `restore` and the `T` bound differ — so
switching A↔B later is localized to `restore` + the store's resize method.

---

# Part 2 — Capture-flag representation

The per-cell capture flag answers "has this cell already been logged in the
*current* frame?" — the test that enforces first-write-wins. Its representation
fixes the cost of three operations:

- `mark` must reset the flag so the new frame starts with nothing captured;
- `restore` lands back in the **parent** frame and must rebuild the flag to
  mean "captured in the parent" (the replay clears every tag it overwrites via
  `into_repr`, so without a rebuild a later `set` to a parent-captured cell
  would double-log and break the bound);
- `capture`/`set`/`pop` read and set it.

Write `n` = vector length, `r` = entries in the restored strata (replayed),
`p` = entries in the parent stratum. The replay itself is **O(r)** and
irreducible (it is the work of undoing). The question is the *extra* cost of
flag bookkeeping on top of that.

## D. One stolen bit + rescan (CHOSEN)

The flag is a single bit — for `InlineStore`, the niche bit stolen from the
value's repr (zero extra memory); for `ParallelStore`, one bit in a packed
`u64` bitset. `mark` resets it: `InlineStore` clears only the parent stratum's
captured slots (O(parent diff)); `ParallelStore` zeroes the packed bitset
(O(n/64)). `restore`'s `finish_restore` rebuilds the parent flags by scanning
the parent stratum and re-setting those bits — **O(p)**.

- **Cost:** `restore` = O(r) replay **+ O(p) parent rescan**; `mark` sublinear,
  never a copy. The `+p` is exactly the price of a boolean flag: after replay
  clears tags, the only way to recover "captured in parent" is to re-derive it
  from the parent's diff slice.
- **Memory:** **1 bit/cell** — and for `InlineStore`, *zero* extra bytes (the
  bit is niched into the value). This is the design's headline property.
- **Marks:** **unbounded** — no counter to overflow.

The `+p` rescan is the accepted cost. It is not a hidden blow-up: `p` is the
size of the frame you are returning into, so `restore` is O(work-unwound +
work-in-parent) — proportional to the relevant frames, never to total history.
(A micro-optimization shrinks it to O(r): replay only clears the `r` restored
indices, so only cells in `p ∩ r` need re-setting — but testing membership in
`p` in O(1) needs a per-cell "captured-in-which-frame" structure, i.e. it just
relocates the cost to option E. Not worth it.)

## E. Per-cell capture-depth (the predecessor `semper` design)

> This is **not** a hypothetical: the predecessor research vehicle, `semper`
> (`~/projects/semper_overview.md` §4), shipped exactly this. The earlier
> analysis here dismissed it on two grounds that, on review of `semper`, are
> *wrong* — recorded honestly below.

Store a per-cell **capture-depth** `capture_depths[i]: C` (`C = u8`/`u16`) =
"the frame *depth* that last captured cell `i`", in a **separate** array (not
inline). With a frame at depth `d`, a first write to cell `i` is
`capture_depths[i] < d` → capture `(i, old, old_capture_depth)` and set
`capture_depths[i] = d`; a repeat is `≥ d` → skip. The diff entry carries the
*old capture-depth*, and backtrack restores it during the **same reverse
replay** that restores values. Crucially:

- **`mark` is O(1)** — bump the depth counter; no per-cell touch, no bitset
  zero, no allocation. (Our chosen design's `mark` is O(parent)/O(n/64).)
- **No parent rescan on backtrack.** Because each diff entry stores the
  `old_capture_depth`, the O(r) reverse replay that restores values *also*
  restores the capture-depths — there is no separate `finish_restore` scan, so
  backtrack is a clean **O(r)**. The `+p` term disappears.
- **The cap is on NESTING DEPTH, not total marks.** Depth *decreases* on
  backtrack (it is restored, not monotone), so `C` bounds *simultaneous nested*
  marks: `u16` ⇒ 65 535 nested, `u8` ⇒ 255 — far past any real search depth.
  (This is the correction: the depth is rolled back with the diff, so it never
  accumulates over the run. The "256 marks *ever*" objection was simply wrong;
  it confused depth with a never-reused generation id.)
- **Memory: `N × sizeof(C)` per vec, separate array.** `semper` §4.2 argues
  this is actually *cheaper* than per-frame bitsets (`5 × 1.25 MB × 50 frames ≈
  312 MB` of bitsets vs `~100 MB` for `u16` depths at 10⁷ nodes) — and keeps
  the depth out of the value's cache line, which matters because the e-graph is
  read-dominated (`find()` chases pointers): inline `(u32,u32)` halves cache
  density on the hottest loop, so `semper` deliberately keeps depths separate.

So E is a real, coherent point with a *better time profile* than our chosen D
(O(1) mark, O(r) backtrack, no rescan). Its costs are (i) `N × sizeof(C)`
permanent memory per vector and (ii) a hard ceiling on nesting depth.

### Why this crate chose D (the stolen bit) instead

The current `containers`/`containers-verus` design takes the opposite point on
the same axis, for reasons specific to *this* codebase rather than a flaw in E:

- **Zero per-cell tracking memory on the hot backend.** `InlineStore` niches
  the capture flag into a spare bit of the value's repr (`DenseId` ids reserve
  the MSB anyway), so tracking costs *0* extra bytes — vs E's `N × sizeof(C)`.
  For an e-graph storing several 10⁷-element id vectors, that difference is the
  10–100 MB of `semper`'s table.
- **No depth ceiling.** D imposes no bound on nesting (the bit has no width to
  overflow). Minor in practice, but free.
- **Simpler niche story to verify.** A 1-bit flag with the `Tagged`
  `into_repr`/`repr_wf` contract (§3, §6) is a small, self-contained
  obligation; a separate depth array threaded through every store op and proved
  consistent across nested frames is a larger surface. D's bridge invariant
  (`captured()[j] ⟺ j in top stratum`) is the price, and it is what makes the
  O(p) rescan necessary on restore.

The trade is therefore **read cache-density + zero tracking memory + no depth
cap + a tighter verification surface (D)** against **O(1) mark + rescan-free
O(r) backtrack + a depth cap + `N·sizeof(C)` memory (E)**. For the inline,
read-dominated, deeply-nested-but-not-65k e-graph workload, D's memory and
cache wins dominate; `semper`'s own §4.2 reaches the same read-density
conclusion from the other side (it keeps depths in a separate array precisely
to protect read density). A *time-critical, write-heavy, memory-rich* workload
could prefer E — the axis is genuinely two-sided.

## Summary (Part 2)

| | `mark` flag cost | backtrack flag cost | tracking memory | cap |
|---|---|---|---|---|
| D. stolen bit + rescan (chosen) | O(parent) / O(n/64) | **+O(p) rescan** | **1 bit; 0 inline** | none |
| E. capture-depths (`semper`) | **O(1)** | **none (folded into O(r))** | `N · sizeof(C)`/vec | **nesting depth** (`u16`=65k) |

Net: the O(p) parent rescan is **not** intrinsic to semi-persistence — `semper`
avoids it by storing+restoring a per-cell depth. It *is* intrinsic to the
**1-bit, zero-inline-memory** flag this crate chose: with only a boolean, the
parent's "captured" set can only be recovered by re-deriving it from the diff,
hence the rescan. We accept that O(p) (proportional to the frame returned into,
not total history) to keep tracking memory at zero on the inline backend and to
keep the verification surface small. Switching to E later is possible but
changes the store's flag type, `mark`, backtrack, and the bridge invariant — a
backend-level change, not a `restore`-local one.

---
[← Table of Contents](00-table-of-contents.md)
