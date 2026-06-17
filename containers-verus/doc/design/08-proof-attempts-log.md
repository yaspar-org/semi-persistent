# Proof Attempts Log — what we tried, what stuck, what we backed out of

A chronological narrative of the verification effort: the milestones that
landed, the *weakened* versions of the theorem we proved along the way, the
approaches we tried and reverted, and the dead ends. Read alongside
`01-verification-design.md` (the design) and `05-restore-regrow-alternatives.md`
(the pop/regrow option analysis).

Convention: ✅ landed & committed (verifies, no admits) · ⚠️ landed but
restricted/weakened · 🔁 tried then reverted · ❌ dead end.

---

## The ladder of weakened theorems we actually proved

We never proved the full thing in one shot. Each milestone proved a strictly
weaker version, then we relaxed a restriction:

1. **No tracking at all** (M3a): `view()` behaves like `std::Vec` for
   push/set/get. No mark/restore.
2. **Single frame, no mutation under a mark** (M3b): one `mark()` at a time;
   `set`/`pop` only callable with an *empty* frame stack. Proved
   `view() == snapshots[0]` after restore.
3. **Arbitrary nesting, still no mutation under a mark** (M4 core): N nested
   marks; restore across multiple strata. `set`/`pop` still gated to empty
   stack.
4. **Mutation under a mark** (M4 set/pop): `set` and `pop` callable with live
   frames — but `pop` restricted to **transient** elements only
   (`active_saved_len < view.len()`), i.e. never pop into a marked region.
5. **Pop into the marked region**. **LANDED** —
   the invariant was relaxed twice (top-fullness + saved_len monotonicity both
   dropped for per-frame coverage) and the central lemma restated flat/target-
   clamped. See the "Pop into the marked region — how it landed" section below.

Each rung is a real theorem with a real restriction encoded as a `requires`.
Nothing was faked: when we couldn't prove a rung we either weakened the
`requires` honestly or backed out.

---

## Chronological log

### M1 — trait specs ✅
`Tagged`, `IndexLike`, `DiffStore` as Verus traits. Notable: the **niche
obligation** on `Tagged` (`repr_wf` + `lemma_repr_extensional`) was added after
a critic flagged that without it a bit-stealing impl could verify vacuously.
Also caught: `u64::as_usize` truncation on 32-bit hosts (gated to 64-bit).

### M2 — storage impls ✅
`ParallelStore` (`Vec<bool>` flag) and `InlineStore` (tag in `T::Repr`) both
satisfy `DiffStore`. Sanity-checked by deliberately deleting a `diff_log.push`
and confirming the verifier rejects it — i.e. the contract isn't vacuous.

### Production bug fix ✅
`Frame.saved_len` was `u32` in production → silent wrap past 4 G slots for
`I = u64`. Changed to `Frame<I> { saved_len: I, diff_start: usize }` in both
production and the verus model.

### M3a — Vec scaffold ✅
push/set/get/view refine to `std::Vec`. No mark/restore.

### M3b — single-frame mark/restore ✅
First real correctness theorem: `view() == snapshots[0]` after restore.

🔁 **The `replay_reverse` dead-end (within M3b).** First attempt modeled
restore with a recursive `replay_reverse` spec (mirroring the imperative
backward loop). Proving the loop ↔ spec correspondence needed a gnarly
structural-induction lemma (`lemma_replay_reverse_*`) that wouldn't close; left
`admit()`s. **The user's intervention fixed it**: switch from the *operational*
"replay" spec to a *declarative, pointwise* invariant —
`snap[j] = diff entry if captured else view[j]`. That collapsed the proof and
removed the admits. This pointwise/declarative framing became the backbone of
everything after.

### Declarative refactor ✅
Rewrote the invariant into the two-case per-cell form (`frame_inv`). Same
theorem, simpler proofs — `push`/`mark` lost their proof hints entirely.

### M4 core — arbitrary nesting + nested restore ✅
The big one. Introduced:
- `overlay(base, diffs, lo, hi)` — spec model of the restore loop, **lowest-
  index entry wins** (applied outermost).
- **Stratification**: each frame owns a diff-log slice; `frame_inv_range` per
  frame, `layer_above` = next snapshot or the view.
- `lemma_snap_eq_overlay` — central downward-induction lemma reconstructing
  `snapshots[k]` from `snapshots[k+1]` + stratum k.
Proved restore across N strata. This was ~M4-sized effort; the `overlay`
split/uncaptured/captured lemmas are the foundation.

### Nested mark ✅; capture-flag bridge ✅
`mark` allows nesting. Added the **bridge**: `store.captured()[j] ⟺ j ∈ top
stratum`, tying the runtime flag to the ghost diff log — needed so `set`/`pop`
can reason about `capture`'s first-write-wins branch.

### set under a frame ✅; pop (transient) ✅
Capturing `set` at any depth. `pop` at any depth **but transient-only**
(`active_saved_len < view.len()`). Rung 4 of the ladder.

---

## Pop into the marked region — the hard frontier (multiple attempts)

Goal: lift the transient-only `pop` restriction to match production (pop into
the marked region). This is where most of the reverted work lives.

### 🔁 Attempt A — regrow `overlay` with a push branch (reverted)
First idea: model the pop→push-on-restore by giving `overlay` a third "push
when `idx == prev.len()`" branch (regrow), and switch `frame_inv`'s captured
case to **lowest-position-wins** (dropping uniqueness, since production's
`force_capture` logs duplicates). Drafted the regrow `overlay` + its five
lemmas. **Reverted** because:
- it forced a "regrow reachability / contiguous coverage" obligation that's
  genuinely new and heavy, and
- separately we realized production's `force_capture` is **unbounded** — a
  push/pop loop on one index grows the diff log without limit (a latent **DoS**).

### Key user-driven design pivot — Default instead of force_capture
Rather than faithfully reproduce the unbounded `force_capture`, we chose:
`pop` uses **conditional** capture (bounded log, ≤ saved_len), and `restore`
regrows the popped region with `resize_default` (`T::default()` fillers that
the replay overwrites). Required `T: Default`. We documented the three options
(Default / Clone-scan / force-record) and why Default wins for the e-graph
domain (`05-restore-regrow-alternatives.md`). The user's DoS observation is what
made us *diverge from* production here rather than match it.

We also established **filler soundness**: a fabricated default is never
observable — it's *entailed by the headline theorem* (`view()==snapshot`), so
`T::default()`'s value is never constrained.

### ✅ Default groundwork that LANDED
- `mark_captured` + `resize_default` added to `DiffStore` + both stores
.
- `frame_cell_inv` refactor + **coverage-aware uncaptured case**
  (uncaptured ⟹ `j < above.len()`). This *also* cracked a nasty
  Verus blocker (below).
- bridge restricted to *present* cells.
- `wf` split into `wf_for_snap` (+ bridge) so reconstruction lemmas run on the
  bridge-free core, which `resize_default` preserves.

### 🔁 The Verus "forall won't re-assemble" blocker (cracked)
While weakening `frame_inv_range`, `lemma_frame_inv_range_local` stopped
verifying: a per-cell `assert forall ... by {}` proved each cell but Verus
wouldn't re-assemble it into the goal `forall` (classic "proved-forall ≠
goal-forall" trigger mismatch). Tried: `&&&` vs `&&`, `spinoff_prover` +
`rlimit(300)`, explicit `snap[j]` mentions — none worked. **Fix**: extract the
per-cell body into a *named* spec fn `frame_cell_inv`, giving the `forall` a
clean function-application trigger (`#[trigger] frame_cell_inv(...)`). This is
why the invariant is factored that way.

### 🔁 Marked-region pop body — proved then reverted (twice)
Wrote the full marked-region `pop` (conditional capture into the marked region) and
got its body **essentially proving** — per-frame `frame_cell_inv` transfer,
the appended-entry extension lemmas (`lemma_cell_inv_extend_top`,
`lemma_captured_in_range_extend`), and the two-step `entry→mid→self` captured()
bridge chain. Reverted to keep the tree green because the cascade into `restore`
wasn't closed.

### ❌→💡 The deeper findings that reshaped the plan
Two things we *learned the hard way*, each of which invalidated an assumption
baked into the existing proof:

1. **Removing `frames[top].saved_len <= view.len()` (clause 6) isn't enough —
   `saved_len` MONOTONICITY also breaks.** `mark` after a deep pop records the
   *current short* view length, so a newer frame can have a *smaller*
   `saved_len`. The wf clause "saved_len monotone" and
   `lemma_saved_len_le_active` ("top is the longest") are both **false** in
   that state. Replacement: per-frame **coverage** (already in
   `frame_cell_inv`) — `j ∈ [saved_{k+1}, saved_k) ⟹ captured in stratum k`.
   The user confirmed: drop monotonicity, use coverage (fully general).

2. **Restore is TARGET-bounded — no "resize to max".** I briefly concluded the
   view must be resized to `max(saved_len over frames)`. **The user pushed back
   ("consult the production code")** and it was right: production's
   `restore_entry` early-returns on `idx >= target_saved_len`, so out-of-range
   diffs are simply **dropped**. Restore only resizes to the *target's*
   saved_len; the central lemma should be **flat and target-clamped**, not a
   per-frame full reconstruction. The current layered lemma *over-reconstructs*
   intermediates (needs `saved_k <= view.len()` for inner k) — that's the
   spurious requirement to remove.

### 🔁 resize-then-call-central-lemma — found the blocker, recorded
Tried: in `restore`, `resize_default` the view full, then call the central
lemma. **Fails**: right after resize the view holds default fillers, so
`self.wf()` is broken (uncaptured case wants `view[j]==snap[j]`). The central
lemma is a method requiring `self.wf()`, so it can't run on the scratch state.
**Resolution identified**: the `wf_for_snap` split (landed) is step one; the
central lemma must be restated to run on `wf_for_snap` of the resized state
(captured case is layer-independent; coverage handles the gap). This is the next
concrete step.

---

## Current state of the tree

The tree verifies clean (0 errors, no admits/assumes). Proved = ladder
rungs 1–5 (**pop into the marked region**) PLUS **M5 fork-history / branch-cut safety** PLUS
**production API parity**. The full vector supports pop into a frame's marked
region, arbitrary nesting, the headline restore theorem
(`view() == snapshots[token]`) across non-monotone saved_lens, AND stale-token
rejection (branch-cut safety).

### M5 fork history / branch-cut safety — LANDED (6 commits)
- ContainerId (external_body u32 + ghost id) + ForkHistory port +
  `is_valid` while-loop ⟺ `fork_valid` refinement + `fh_wf`.
- GENERAL branch-safety theorem `lemma_fork_valid_characterization`:
  `fork_valid` ⟺ `reaches(current, tb)` ∧ `td ≤ walk_bound(current, cd, tb)`
  (all cases: current branch, ancestors, off-path rejection). Induction on
  `branch` under `fh_wf`.
- wired into `Vec`: `forks`/`id` fields (wf carries `forks.wf()`),
  `VecToken` + branch_id/depth/container_id, `mark` stamps, `restore` requires
  `is_token_valid_spec` + records the cut via `forks.fork(...)`. Reconstruction
  theorem UNCHANGED (validity is a parallel precondition, not coupled to it).
- `is_valid_token`/`depth` exec methods + `with_store`/`new`.
- `VecView`/`VecViewIter` iteration; `ShrinkPolicy`+`mark`,
  byte-accounting.
  Verus gotcha: a struct named `View` collides with vstd's `@`-desugaring
  (`.view()`) and breaks `@` on std Vec — use `VecView`. Also: the replay loop
  havocs unmentioned fields, so `forks` had to be pinned in the loop invariant.

### Pop into the marked region — how it landed (5 commits, each green)
1. `lemma_overlay_lowest` — lowest-position-in-range wins (cross-
   stratum), replacing the uniqueness-only `lemma_overlay_captured` for the
   flat proof.
2. `lemma_cell_eq_overlay` — the **flat, base-parametric, target-
   clamped** central lemma. Reconstructs a single `snapshots[k][j]` by
   overlaying the whole tail `[diff_start_k, n)` onto a base, via downward
   induction; captured cells pinned by `lemma_overlay_lowest`, uncaptured
   cells recurse one frame up (coverage gives `j < layer_above.len()`),
   terminating at the top frame. Uses NO saved_len monotonicity.
3. `restore` reworked: `resize_default(saved_len)` → base of length
   exactly the target's saved_len → flat lemma on the pre-resize `old_self`
   (it's base-parametric, so the resized data is the base) → overwrite-only
   replay. Adds `T: Default` on `restore`.
4. dropped the two now-false `wf_for_snap` clauses (top-fullness +
   saved_len monotonicity), replaced by per-frame coverage. Deleted the dead
   layered `lemma_snap_eq_overlay` and the three false lemmas
   `lemma_saved_len_{monotone,le_active,le_view}`. `push` now REQUIRED to call
   `store.mark_captured(old_len)` on re-entry (bridge would break otherwise).
5. marked-region `pop`: dropped the transient-only precondition;
   conditionally captures the popped cell when it's inside the marked region.
   New free lemma `lemma_captured_in_range_append_other` (a one-entry append at
   the popped index doesn't change any other cell's captured-status).

Key Verus gotcha hit in steps 4–5: `IndexLike::lt_spec`/`le_spec` are DEFAULT
trait-method bodies and are NOT transparent at a generic `I: IndexLike` use
site — `lt()`'s ensures won't unfold to `as_nat() < as_nat()`. Compare via
`as_usize()` (whose spec relation to `as_nat` is concrete) instead.

## What's left
- `TRACK = false` observational-equivalence theorem (compile-out-tracking).
- Other containers (AppendOnlyVec, Map, SparseSet, BPlusTreeSet, ListArena).
- Optional: `as_slice` (omitted — backend-specific fast path); upgrade the
  ContainerId distinctness from assumed to a proved tracked-counter property.

## Recurring lessons
- Declarative/pointwise invariants beat operational/replay ones for these
  proofs (the M3b pivot).
- Named spec fns for stable `forall` triggers (the `frame_cell_inv` fix).
- When all wf sub-conjuncts verify but the aggregate fails: `spinoff_prover` +
  `rlimit` (solver budget, not soundness).
- Consult production before inventing requirements (the target-clamped restore
  correction).
- One milestone per commit; always leave the tree verifying; never commit a
  broken half-migration. Several marked-region-pop attempts were reverted precisely
  to honor this.
- Recursive ghost datatype with `Seq<Self>` children (the B+tree's ghost `Tree`):
  the `Tree` ↔ `Seq<Tree>` mutual recursion must have *type-compatible* decreases
  clauses. Use `decreases t` for the node fn and `decreases kids` (the
  `Seq<Tree>` value itself — Verus orders it by element height) for the forest
  fn; using `decreases kids.len()` (an `int`) gives "decreases clauses must have
  compatible types". And the recursion must be *explicit cons* (`f(kids[0]) +
  forest(kids.drop_first())`) — a closure `Seq::new(len, |i| f(kids[i]))` hides
  `kids[i] < t` from the termination checker and fails. One-step unfolding of the
  forest fn needs a small `lemma_*_cons` (ensures `forest(kids) == f(kids[0]) ∪
  forest(kids.drop_first())` for non-empty `kids`). Validated in a 40-line probe
  before the module reshape.
- Default-bodied trait spec methods are pruning-fragile *crate-wide*. A
  `lemma_order_is_as_nat {}` whose empty body relied on Verus auto-unfolding the
  `open` default `lt_spec`/`le_spec` bodies verified fine for a year, then broke
  (only the `usize` impl) the moment unrelated spec surface was added in
  `bplus_layout` (the leaf-split mutators). The added definitions changed which
  facts the pruner pulled into the SMT context for `index_like`, an upstream
  module that wasn't even edited. Fix: state the unfold explicitly —
  `assert(a.lt_spec(b) == (a.as_nat() < b.as_nat()))` inside the lemma body — so
  the proof no longer depends on the pruner's choices. Lesson: don't leave an
  empty proof body whose discharge silently depends on auto-unfolding a default
  trait body; make the unfold explicit, especially for foundational lemmas every
  other module consumes.
- Same fragility, second instance, *worse* trigger: a **heavy default-bodied
  trait method**. Adding `internal_insert_at` to `NodeLayout` with a full default
  body (a child-shift loop + two helper calls) destabilized previously-green
  *sibling* methods in the same trait impl — the `child` accessor and
  `set_internal_child` started failing their postconditions, though their bodies
  were unchanged. The heavy body bloated the per-impl proof context enough that
  the pruner dropped facts the lean methods had relied on. Fix: move the generic
  composite *out of the trait* into a free `fn internal_insert_at<L: NodeLayout>`
  — the trait keeps only the small per-layout primitives (`set_internal_child`,
  `internal_key_insert`), and the composition lives in a free function with its
  own proof context. Rule of thumb: trait bodies stay small and per-layout;
  multi-step generic logic goes in free functions over `L`.

---
[← Table of Contents](00-table-of-contents.md)
