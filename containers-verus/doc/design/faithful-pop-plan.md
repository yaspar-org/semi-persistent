# Implementation Plan — Faithful pop with `T: Copy + Default`

Status: DECISIONS LOCKED (see §0), ready to execute. Tree is green at HEAD
(142 verified, 0 errors). This plan lifts the transient-only `pop` restriction
to full production behavior (pop into the marked region), using the
Default-resize regrow strategy.

## How production ACTUALLY saves & restores length (re-read 2026-06-09)

- **Save** (`mark`, vec.rs:105,117): each frame stores `saved_len =
  store.len()` at *its* mark time. Independent per frame; non-monotone across
  frames is possible.
- **Restore** (`restore`, vec.rs:143-151): `truncate(saved_len_target)` —
  `std::Vec::truncate` only **shrinks** (no-op if already shorter). Then the
  replay loop over `[diff_start_target, n)` calls
  `restore_entry(idx, old, saved_len_target)` which (diff_store.rs:143-154):
  - `idx >= saved_len_target` → **drop**;
  - `idx >= data.len()` → **push** `old_value.clone()` (REGROW), with
    `debug_assert_eq!(idx, data.len())` — pushes must be contiguous;
  - else → **overwrite**.
- So production **regrows via the push branch in the replay**, taking the value
  from the **diff entry itself** (`old_value.clone()`), NOT from any default.
  That is why production needs only **`T: Clone`** and **no `Default`**.
- Contiguity of the regrow pushes is guaranteed because production's `pop` uses
  `force_capture` — it logs *every* popped marked cell, so the replay hits the
  regrow indices in increasing order with no gaps. **This is exactly the
  property our conditional-capture (bounded-log) design gives up**, which is the
  original reason we reach for Default.

## Decisions locked (2026-06-09)

- **Bound = `Copy + Default`.** Production = `T: Clone`, no `Default`. Ours uses
  `Copy + Default`: `Copy` is *stricter* than `Clone` (we model the `Copy`
  subset — fine for e-graph ids, avoids vstd clone-spec plumbing). `+ Default`
  is an *extra* requirement production lacks; it buys the **DoS-free** regrow
  (bounded log) — a deliberate, documented divergence. `Tagged: Copy` already.
- **Our regrow = resize-with-default, NOT production's push-from-diff.** This is
  a real divergence in *mechanism* (not just bound): restore pads/chops the
  view to *exactly* `saved_len` via `resize_default` BEFORE replay, so the base
  length is `saved_len` throughout and the replay is pure overwrite-or-drop.
  Production instead pushes-from-diff during replay. We diverge because
  conditional capture (our bounded-log choice) breaks production's contiguity
  guarantee, so push-from-diff wouldn't work for us; pad-with-default sidesteps
  the ordering entirely.
- **No `overlay` regrow branch needed (for OUR design).** Because the base is
  `saved_len`-length before replay, the existing overwrite-only `overlay`
  (`idx < prev.len()` → overwrite, else skip) already overwrites in-range and
  **drops** out-of-range entries (`idx >= prev.len() ⟺ idx >= saved_len`). No
  `saved_len` param, no push branch, no new overlay lemmas → step 2 is small.
  (`restore_entry`'s push branch becomes dead-but-harmless under our design.)

References: `00-verification-design.md` §8 (faithful pop), §6 (invariant),
`restore-regrow-alternatives.md`, `proof-attempts-log.md`.

---

## 0. Decision to confirm before starting: `Copy` → `Clone + Default`?

The current stack is `T: Sized + Copy` everywhere (vec.rs, diff_store.rs,
parallel_store.rs; `Tagged: Copy` for inline). You asked for `T: Clone +
Default`. Two sub-questions for you:

**(a) Do we actually want to drop `Copy`, or add `Default` on top of `Copy`?**
- `Copy + Default` is a *much* smaller change: every existing body keeps its
  implicit copies; we only add `Default` where `resize_default` needs it.
  Covers the e-graph domain fully (all ids are `Copy` and `Default`).
- `Clone + Default` (dropping `Copy`) is the more general bound but forces:
  - explicit `.clone()` at ~8 sites in each store (data indexing, `*old_value`,
    diff-log pushes) and in vec.rs;
  - threading vstd's clone spec (`cloned::<T>(a,b)` / `a.clone()` ensures
    `res == a` only for the spec-cloneable types) through every postcondition
    that today says `data() == old.data().push(value)` — clone's spec is
    weaker than `==` for general `T`, so those contracts get more verbose;
  - `InlineStore` is unaffected (it's `Tagged`, which stays `Copy`); only the
    `ParallelStore` path and the generic `Vec`/`DiffStore` bounds change.

**Recommendation:** do **`Copy + Default`** for the faithful-pop proof (keeps
the diff small and the contracts crisp), then, if you still want the broader
bound, relax `Copy → Clone` as a *separate, mechanical* follow-up commit. That
sequencing means the hard invariant work isn't entangled with clone-spec
plumbing. **If you'd rather go straight to `Clone + Default`, say so and I'll
fold the clone plumbing into steps 1–2 below.**

The rest of this plan assumes whichever bound we pick; the proof structure is
identical. I write `T: Default` for the new requirement and leave the
copy/clone axis to your call.

---

## 1. Invariant changes (vec.rs `wf_for_snap`) — the core

Per §8 of the design doc, faithful pop requires relaxing **two** wf clauses,
both replaced by the per-frame **coverage** that `frame_cell_inv` already
encodes (uncaptured ⟹ `j < layer_above.len()`):

1. **Drop** `frames[top].saved_len <= view.len()` (the "view is full" clause).
   After a pop into the marked region the view is shorter than `saved_len`.
2. **Drop** `saved_len` monotonicity (`saved_len[k] <= saved_len[k+1]`).
   `mark` after a deep pop records the current short length, so saved_lens are
   not monotone.

Dependent lemma changes:
- `lemma_saved_len_le_view(k)` — currently derives `saved_k <= view.len()` via
  monotonicity + clause 6. Becomes: *takes* "view full" (`frames[top].saved_len
  <= view.len()`) as an explicit hypothesis, derives the rest. Callers that
  have a full view (push/set/mark on non-popped states, and restore *after
  resize*) supply it.
- `lemma_saved_len_le_active` ("top is the longest") — **delete** (false now);
  replace its uses with per-frame coverage reasoning.
- `lemma_saved_len_monotone` — **delete** (false now); its only legitimate uses
  were deriving the two dropped clauses.

Risk: these lemmas are referenced from push/pop/set/mark/restore proofs. Each
reference must be re-justified via coverage. This is the bulk of the proof
churn. Estimate: the largest single step.

---

## 2. Central lemma restated: flat + target-clamped (vec.rs)

`lemma_snap_eq_overlay` currently reconstructs each `snapshots[k]` fully on
`[0, saved_k)`, which spuriously needs `saved_k <= view.len()` for intermediate
k (false under non-monotone saved_lens). Production's restore is **target-
bounded**: `restore_entry` drops `idx >= target_saved_len`. So:

- Extend `overlay` to the three-way branch with a `saved_len` parameter:
  `idx >= saved_len` → skip; `idx < prev.len()` → overwrite; `idx ==
  prev.len()` → push (regrow). Re-prove its lemmas
  (`lemma_overlay_len` becomes a bound, `_uncaptured`, a new `_captured`/lowest,
  `_split`, `_prefix_agnostic`). NOTE: with the Default-resize approach the
  base handed to `overlay` is already length `target_saved_len`, so the push
  branch may not even be exercised — *to verify*: if the resized base is
  full-length, overlay stays overwrite-only and we may keep the current 2-way
  `overlay` and only add the `saved_len` skip guard. **Open question to settle
  first (see step 5).**
- Restate the central lemma to prove
  `overlay(base_len_target, diffs, diff_start_target, n, target_saved_len)[j]
  == snapshots[target][j]` for `j < target_saved_len`, with the inductive step
  handling cells `j ∈ [saved_{k+1}, saved_k)` via the **captured** arm (frame
  k's own diff) instead of the layer-above. Coverage gives "uncaptured ⟹ j <
  saved_{k+1}" for free, so no monotonicity needed.
- The lemma runs on `wf_for_snap` (not full `wf`), so restore can call it on
  the resized scratch state.

---

## 3. `restore` body (vec.rs)

New shape:
```
target = token.frame_idx;  saved_len = frames[target].saved_len
resize_default(saved_len)                 // truncate-or-grow to EXACTLY target
                                          //   (NOT max — production drops idx>=saved_len)
prove wf_for_snap holds on the resized state   // resize preserves it (captured
                                          //   arm layer-independent; coverage
                                          //   keeps uncaptured cells present)
lemma_snap_eq_overlay(target)             // overlay(view,...) == snap_target
replay loop over [diff_start_target, n)   // imperative overlay; each restore_entry
                                          //   gated by saved_len
prove view == snap_target                 // from the lemma + loop invariant
truncate frames/snapshots/diff_log to target
finish_restore(...) to rebuild the bridge for the new top frame
re-establish full wf (bridge + active_saved_len)
```
The delicate part is proving `wf_for_snap` of the resized state (default
fillers in the gap; coverage says those cells are captured so the captured arm
holds and the uncaptured arm never reads a filler). This was prototyped before;
the `wf_for_snap` split (already landed) is what makes it expressible.

Requires `T: Default` on `restore` (and transitively wherever `resize_default`
is reachable).

---

## 4. `pop` and `push` (vec.rs)

- **`pop`**: drop the `active_saved_len < view.len()` precondition. Body: if
  the popped index `i < active_saved_len`, call `capture(i, ...)` (conditional
  first-write-wins) before `store.pop()`. Prove coverage is maintained (the
  popped cell becomes captured: either it already was, or capture just logged
  it) and the bridge two-step (entry→mid→self). Largely prototyped before
  (commit history shows it nearly proved); should re-land once §1–2 are in.
- **`push`**: when the pushed index `old_len < active_saved_len` (re-entering a
  popped marked region), call `store.mark_captured(old_len)`. Prevents the
  pop→push→set re-capture that would duplicate entries and unbound the log.
  Keeps the diff log ≤ saved_len. Prove frame_inv + bridge maintained.

---

## 5. Open question to settle BEFORE coding (cheap, do first)

Does the Default-resize approach need the **regrow push branch** in `overlay`
at all? Hypothesis: no — because `resize_default(saved_len)` makes the base
exactly `saved_len` long *before* replay, so every in-range entry
(`idx < saved_len`) hits `idx < base.len()` → pure overwrite; entries with
`idx >= saved_len` are skipped by the guard. If that holds, we keep the
existing 2-way `overlay` and only add a `saved_len` skip guard (much less
work than the full 3-way regrow lemmas). I'll confirm this with a small
spec-level check (overlay onto a `saved_len`-length base never pushes) before
committing to step 2's lemma rework. **This determines whether step 2 is small
or large.**

---

## 6. Proposed commit sequence (each leaves the tree green)

1. **(if Clone) Copy→Clone plumbing** — mechanical, isolated. [only if you pick
   Clone over Copy+Default]
2. **`overlay` skip-guard / regrow** — settle step 5, then either add the
   `saved_len` guard (small) or the 3-way branch (large) + reprove its lemmas.
   Verifies standalone (pure spec lemmas).
3. **Central lemma flat/target-clamped** — restate + reprove
   `lemma_snap_eq_overlay`; keep old `restore` working by adapting its call.
4. **Drop monotonicity + clause 6; fix dependent lemmas** — the invariant
   relaxation; re-prove push/set/mark/pop(transient)/restore against the
   weakened `wf_for_snap`. (This is the big churn step; may merge with 3.)
5. **Faithful `pop`** — conditional capture into marked region; drop the
   precondition.
6. **`push` mark_captured** — close the re-capture / unbounded-log hole.
7. **(optional) Copy→Clone** if deferred from step 1.

After each: `./verify-all.sh` clean, no admits/assumes, commit.

---

## 7. What this does NOT cover

- Fork history / branch-cut safety (M5) — separate, after pop.
- `TRACK=false` equivalence.
- Other containers.

---

## Summary of what I need from you to start

1. **Copy+Default** (recommended, smaller) or **Clone+Default** (your literal
   ask, more plumbing)? 
2. OK to spend the first action on the step-5 open question (does resize-first
   let us avoid the regrow push branch)? It decides whether step 2 is small.
3. Any objection to the commit sequence in §6?
