# Pop into a marked region, with `T: Copy + Default`

`pop` may remove cells that were live at a mark, i.e. pop *into* the marked
region. Played in reverse on `restore`, such a pop becomes a push that must
regrow the vector, and that push needs a value to place in the resurrected slot.
This chapter is how the crate does it: the `Copy + Default` bound, the
default-resize regrow, the relaxed `wf`, and the `pop`/`push` capture rules.

## 1. Current production and verified mechanism

Both implementations save a per-frame `saved_len = store.len()` at each mark;
lengths need not be monotone across nested frames. `pop` conditionally captures
a marked cell with the same first-write-wins operation as `set`, so each index
has at most one diff entry per frame. `restore` then resizes the store to exactly
the target `saved_len` with `T::default()` before replaying
`[diff_start_target, n)`:

- `idx >= saved_len_target` → **drop**;
- otherwise → **overwrite** the already present slot.

The backend contract still permits a push when `idx == data.len()`, but the
pre-replay resize makes that branch unreachable in the vector restore path.
This is the bounded replacement for the retired force-record design described
in [Chapter 6](06-restore-regrow-alternatives.md).

The verified crate models `T: Copy + Default`; production accepts `Clone` for
ordinary storage operations and requires `Default` when restore can regrow.
`Copy` is the verified crate's intentionally narrower value domain, used to
avoid unmodeled clone plumbing. Both use resize-with-default, and both rely on
the same argument that every filler is overwritten before restored state is
observable (see [Chapter 7](07-default-impls.md) §1).

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
snapshot the pre-resize self, which satisfies wf_for_snap
resize_default(saved_len)                 // truncate-or-grow to EXACTLY target
                                          //   (NOT max — production drops idx>=saved_len)
lemma_snap_eq_overlay(target, resized_base)
                                          // old invariant + shared-prefix base
replay loop over [diff_start_target, n)   // imperative overlay; restore_entry gated by saved_len
prove view == snap_target                 // from the lemma + loop invariant
truncate frames/snapshots/diff_log to target
finish_restore(...) to rebuild the bridge for the new top frame
re-establish full wf (bridge + active_saved_len)
```

The resized state need not satisfy the whole vector's `wf_for_snap`: default
fillers can break the top frame's uncaptured arm. The proof therefore snapshots
the pre-resize self, whose invariant is known, and applies the flat central
lemma to a resized base that agrees with the old view on their shared prefix.
Coverage handles the grown gap. `restore` carries `T: Default` (transitively
wherever `resize_default` is reachable).

## 4. `pop` and `push`

- **`pop`** has no `active_saved_len < view.len()` precondition. If the popped
  index `i < active_saved_len`, it calls `capture(i, ...)` (conditional
  first-write-wins) before `store.pop()`. The popped cell becomes captured
  (either it already was, or capture just logged it), which maintains coverage,
  and the bridge is re-established in the two-step entry→mid→self form.
- **`push`**, when the pushed index `old_len < active_saved_len` (re-entering a
  popped marked region), calls `store.mark_captured(old_len)`. This prevents the
  pop→push→set sequence from re-capturing and duplicating entries, keeping each
  frame's stratum at most its `saved_len` (and the whole log at most the sum of
  retained frame lengths).

---
[← Table of Contents](00-table-of-contents.md)
