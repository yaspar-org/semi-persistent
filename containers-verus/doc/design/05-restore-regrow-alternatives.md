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

## C. Force-record pops — UNBOUNDED, do not adopt

An earlier production `pop` called `force_capture` unconditionally — it logged
the popped cell every time, ignoring the capture bit. On restore the
highest-position filler entry supplied the regrow push value (overwritten by
the lower first-write-wins entry), so it was *correct*.

- **Cost:** restore O(k), simplest code.
- **Bound: NONE.** A `push`/`pop` loop on one index logs an entry every
  iteration (push resets the capture bit; force_capture ignores it). An
  adversary controlling push/pop exhausts memory — a memory-exhaustion DoS.
  This is why this approach is rejected in favor of A.

> **Status:** production has adopted design A (bounded). `pop` now uses
> first-write-wins `capture`, `push` re-marks re-entered slots, and `restore`
> regrows with `resize_default` before an overwrite-only replay. `force_capture`
> has been removed. See `containers/doc/design/02-semi-persistent-vectors.md`.

## Summary

| | restore time | diff bound | `T` bound |
|---|---|---|---|
| A. Default + resize (verus **and** production) | O(k) | ≤ saved_len | `Default` |
| B. scan/sort regrow | 2k or k·log k | ≤ saved_len | `Clone` |
| C. force-record (old prod) | O(k) | **unbounded (DoS)** | none |

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

So E has a strictly *better backtracking profile* than our chosen D — O(1)
mark, rescan-free O(r) backtrack — at the cost of `N × sizeof(C)` memory and a
nesting-depth ceiling.

### Why this crate chose D (the stolen bit) — for cache density and access cost, NOT backtracking

The deciding factor is **raw cache density and per-access (read/write) cost on
the hot loops — not backtracking performance**, where E is in fact faster. The
e-graph is overwhelmingly read-dominated: `find()` and canonicalization chase
id pointers, each step reading one word and nothing else. The capture flag has
to live *somewhere*, and the only representation that doesn't degrade that
read path is a bit stolen from the value's own word:

- **D keeps full read density and adds nothing to an access.** `InlineStore`
  niches the flag into a spare bit of the value's repr (`DenseId` ids already
  reserve the MSB), so a `Vec<u32>` of ids stays at **16 per cache line** and a
  read is a single load + mask — no second array, no second stream, no extra
  cache line touched. The capture state rides *for free* in bytes that already
  exist.
- **E perturbs every access, however it is laid out.** Inline `(value, depth)`
  pairs double the footprint and **halve read density** (8 per line) — fatal on
  the hottest loop. A *separate* `capture_depths` array (what `semper` chose,
  §4.2, precisely to protect read density) avoids that but makes every captured
  write touch a **second cache line / second memory stream**, and costs
  `N × sizeof(C)` resident memory (10–100 MB across the e-graph's id vectors).
  Either way the *steady-state read and write access cost* is worse than D's
  ride-along bit.

In short: D is chosen because the flag must not cost a cache line or an extra
load on the read-dominated hot path — the stolen bit is the only zero-density-
cost option. The O(p) restore rescan and the bridge-invariant proof burden are
**accepted consequences** of that choice, not themselves reasons for it; on the
backtracking axis alone, E (the `semper` capture-depth design) wins. The trade
is genuinely two-sided, decided here by access-path performance and memory:

- **D (stolen bit):** full read density, zero-cost accesses, zero tracking
  memory, no depth cap — paying an O(p) rescan on restore and a niche/bridge
  proof obligation.
- **E (capture-depths):** O(1) mark, rescan-free O(r) backtrack — paying read
  density / an extra access stream and `N·sizeof(C)` memory, with a
  nesting-depth ceiling.

A write-heavy, backtrack-bound, memory-rich workload that does *not* live or
die by read density could rationally prefer E.

## Summary (Part 2)

The **deciding column is read density / access cost** — everything else is a
consequence. D wins it; E wins the backtracking columns.

| | read density & access cost | tracking memory | `mark` | backtrack flag | cap |
|---|---|---|---|---|---|
| D. stolen bit (chosen) | **full (16 u32/line), single load+mask** | **1 bit; 0 inline** | O(parent)/O(n/64) | +O(p) rescan | none |
| E. capture-depths (`semper`) | extra stream (separate) / ½ density (inline) | `N · sizeof(C)`/vec | **O(1)** | **none (in O(r))** | **nesting depth** (`u16`=65k) |

Net: D is chosen for **raw cache density and read/write access cost on the
hot, read-dominated loops** — the stolen bit is the only representation that
costs neither a cache line nor an extra load per access, and zero resident
tracking memory. It is explicitly **not** chosen for backtracking speed: there
E (the predecessor `semper` capture-depth design) is faster (O(1) mark,
rescan-free O(r) backtrack). The O(p) restore rescan and the bridge-invariant
proof obligation are the *accepted price* of the access-path win, not reasons
for it. Switching to E later is a backend-level change (the store's flag type,
`mark`, backtrack, and the bridge invariant), not a `restore`-local one.

---
[← Table of Contents](00-table-of-contents.md)
