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

## E. Generation / epoch counter (rejected)

Replace the bit with a per-cell **epoch**: "this cell was last captured in
frame-generation `g`." A monotone `current_gen` is bumped on every `mark`;
`capture` compares `cell.gen == current_gen` (already captured) vs `<`
(capture, then `cell.gen := current_gen`). Then `mark` and `restore` touch
**no cells at all** — they only change `current_gen` — so flag bookkeeping
drops to **O(1)** and `restore` becomes a clean O(r).

Why we rejected it:

- **The epoch is not the stack depth — it is a never-reused mark id.** It must
  be unique per `mark` (like `branch_id`): after a restore the parent
  re-becomes current, and a re-marked frame landing at the *same depth* as a
  discarded one must not alias its captured cells. So `current_gen` grows with
  the **total number of marks over the whole run**, not the backtracking depth.
- **A fixed-width epoch caps total marks, not depth.** 8 bits ⇒ 256 marks
  *ever*; 16 bits ⇒ 65 536 marks ever. Equality saturation marks on every
  speculative trial, so it blows the cap almost immediately. The cap is on
  cumulative history — strictly worse than "max nesting levels".
- **It defeats the inline design.** An epoch needs ≥ a byte of real per-cell
  storage that cannot be niched into the value, so `InlineStore` loses its
  zero-extra-memory property (e.g. a `u32` id cell grows from 4 to 5–8 bytes).
  For `ParallelStore` it replaces an `n/64`-word bitset with an `n`-word epoch
  array — 32–64× more tracking memory.
- **Lifting the cap reintroduces O(n).** The textbook fix for narrow epochs is
  an O(n) sweep (reset all cells to gen 0, reset the counter) once per `2^width`
  marks — amortized cheap, but it is an occasional linear pass, the very thing
  the epoch was meant to avoid, and the sweep must itself be made
  semi-persistent or a restore across a sweep boundary corrupts the flags.

## Summary (Part 2)

| | `mark` flag cost | `restore` flag cost | memory / cell | marks |
|---|---|---|---|---|
| D. stolen bit + rescan (chosen) | O(parent) / O(n/64) | **O(p)** | **1 bit (0 inline)** | **unbounded** |
| E. epoch counter | O(1) | O(1) | ≥ 1 word | **capped** (or amortized O(n) sweep) |

Net: the O(p) parent rescan is the price of an **unbounded-marks, 1-bit,
zero-extra-memory** capture flag — three properties the design deliberately
keeps. An epoch buys O(1) bookkeeping but pays in per-cell memory and a hard
mark cap, fatal for the inline backend and for a long-running saturation. The
only place E could win cleanly is `ParallelStore` *if* tracking memory were
free and the mark cap acceptable — not the case for the e-graph (inline, LIFO,
long-lived), so D stands.

---
[← Table of Contents](00-table-of-contents.md)
