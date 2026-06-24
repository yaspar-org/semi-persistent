# Pop into a marked region, with `T: Copy + Default`

`pop` may remove cells that were live at a mark, i.e. pop *into* the marked
region. Played in reverse on `restore`, such a pop becomes a push that must
regrow the vector, and that push needs a value to place in the resurrected slot.
This chapter is how the crate does it: the `Copy + Default` bound, the
default-resize regrow, the relaxed `wf`, and the `pop`/`push` capture rules.

## 1. How production regrows, and why this crate diverges

Production saves a per-frame `saved_len = store.len()` at each `mark` (per-frame,
so non-monotone across frames is possible). On `restore` it `truncate`s to the
target's `saved_len` (a no-op if already shorter), then replays
`[diff_start_target, n)`; `restore_entry(idx, old, saved_len_target)`:

- `idx >= saved_len_target` → **drop**;
- `idx >= data.len()` → **push** `old_value.clone()` (regrow), with a
  contiguity `debug_assert_eq!(idx, data.len())`;
- else → **overwrite**.

So production regrows via the push branch in the replay, taking the value from
the diff entry itself (`old_value.clone()`), which is why production needs only
`T: Clone` and no `Default`. Contiguity of the regrow pushes holds because
production's `pop` uses `force_capture`: it logs *every* popped marked cell, so
the replay hits the regrow indices in increasing order with no gaps. That is
exactly the property this crate's conditional (bounded) capture gives up, and the
reason it reaches for `Default` instead (see
[06-restore-regrow-alternatives](06-restore-regrow-alternatives.md) for the full
trade, including why the unbounded `force_capture` is a latent DoS).

This crate diverges on both bound and mechanism:

- **Bound is `Copy + Default`.** `Copy` is stricter than production's `Clone`
  (the crate models the `Copy` subset, fine for e-graph ids, and avoids vstd's
  clone-spec plumbing). `+ Default` is an extra requirement that buys the
  bounded log; `Tagged` is already `Copy`.
- **Regrow is resize-with-default, not push-from-diff.** `restore` pads or chops
  the view to *exactly* `saved_len` via `resize_default` *before* the replay, so
  the base length is `saved_len` throughout and the replay is pure
  overwrite-or-drop. Conditional capture breaks production's contiguity
  guarantee, so push-from-diff would not work here; padding with default
  sidesteps the ordering entirely. The default fillers are never observable
  (the backward replay overwrites every regrown cell with its captured value;
  see [07-default-impls](07-default-impls.md) §1).

A consequence is that the `overlay` spec stays **overwrite-only**: because the
base is already `saved_len` long, every in-range entry (`idx < saved_len`) hits
`idx < base.len()` and overwrites, while `idx >= saved_len` is dropped. No
push/regrow branch, no `saved_len` overlay parameter; `restore_entry`'s push
branch is dead-but-harmless under this design.

## 2. The relaxed `wf`

Popping into the marked region relaxes two `wf_for_snap` clauses, both subsumed
by the per-frame **coverage** that `frame_cell_inv` already encodes (uncaptured
⟹ `j < layer_above.len()`):

1. **Dropped** `frames[top].saved_len <= view.len()` (the "view is full"
   clause): after a pop into the marked region the view is shorter than
   `saved_len`.
2. **Dropped** `saved_len` monotonicity (`saved_len[k] <= saved_len[k+1]`):
   `mark` after a deep pop records the current short length, so saved_lens are
   not monotone.

Dropping monotonicity is what forces the central reconstruction lemma to be
**flat / target-clamped** rather than layered, reconstructing only the target
snapshot clamped to its own `saved_len`; that lemma and its per-cell
"lowest-position-wins" argument are [Chapter 5](05-flat-central-lemma.md).
`lemma_saved_len_le_view` survives by *taking* "view full" as an explicit
hypothesis (supplied by push/set/mark on full views, and restore after resize);
the "top is the longest" and monotonicity lemmas are gone (they were only ever
used to derive the two dropped clauses).

## 3. The `restore` body

```
target = token.frame_idx;  saved_len = frames[target].saved_len
resize_default(saved_len)                 // truncate-or-grow to EXACTLY target
                                          //   (NOT max — production drops idx>=saved_len)
prove wf_for_snap holds on the resized state
lemma_snap_eq_overlay(target)             // overlay(view,...) == snap_target
replay loop over [diff_start_target, n)   // imperative overlay; restore_entry gated by saved_len
prove view == snap_target                 // from the lemma + loop invariant
truncate frames/snapshots/diff_log to target
finish_restore(...) to rebuild the bridge for the new top frame
re-establish full wf (bridge + active_saved_len)
```

The delicate step is proving `wf_for_snap` of the resized state: the default
fillers sit in the gap `[old_len, saved_len)`, and coverage says exactly those
cells are captured, so the captured case of `frame_cell_inv` holds and the
uncaptured case never reads a filler. The `wf_for_snap` split is what makes this
expressible. `restore` carries `T: Default` (transitively wherever
`resize_default` is reachable).

## 4. `pop` and `push`

- **`pop`** has no `active_saved_len < view.len()` precondition. If the popped
  index `i < active_saved_len`, it calls `capture(i, ...)` (conditional
  first-write-wins) before `store.pop()`. The popped cell becomes captured
  (either it already was, or capture just logged it), which maintains coverage,
  and the bridge is re-established in the two-step entry→mid→self form.
- **`push`**, when the pushed index `old_len < active_saved_len` (re-entering a
  popped marked region), calls `store.mark_captured(old_len)`. This prevents the
  pop→push→set sequence from re-capturing and duplicating entries, keeping the
  diff log `<= saved_len` (the bound that makes the log, and hence `restore`,
  linear in the modified cells).

---
[← Table of Contents](00-table-of-contents.md)
