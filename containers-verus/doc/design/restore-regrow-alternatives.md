# Restore regrow: design alternatives

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
[← Table of Contents](00-table-of-contents.md)
