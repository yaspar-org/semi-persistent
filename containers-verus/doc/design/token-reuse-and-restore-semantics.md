# Token reuse, restore semantics, and the capture-tag recompute

Status: DESIGN NOTE (findings + options). Captures a subtle correctness/API
question raised in review: what exactly happens to a token after you `restore`
to it, why re-using it is caught, how the capture tag bits are reconstructed,
and whether an alternative "restore-without-pop / reusable token" semantics is
desirable. Grounded in the production code (`containers/src/vec.rs`,
`diff_store.rs`, `token.rs`) and an empirical probe.

## 0. TL;DR

- **There is no correctness bug.** Restore correctly recomputes the capture
  tags of the frame it lands in; first-write-wins is preserved. Verified by
  probe (§3).
- **Restoring to a token `t` invalidates `t`** — but via the structural
  `frame_index < frames.len()` precondition, NOT via fork-history validity
  (which still returns `true` for the just-restored token). §2–3.
- The reuse-safety is enforced by a **runtime `assert`**, where Rust's type
  system could enforce it statically by consuming a non-`Copy` token. §4.
- The **actual consumer (the e-graph interpreter) uses strict LIFO Push/Pop**
  and never re-restores or mutates-then-re-restores a token (§5). So the
  current "restore consumes the mark" semantics is correct for the real use;
  a "reusable token" is a genuine *extension*, not a fix. §6.

## 1. What `restore(t)` actually does to the frame stack

`mark()` at frame-stack depth `d` creates frame index `d` and returns a token
with `frame_index == d`. `restore(t)` (production `vec.rs:125`):

1. assert same container;
2. assert `forks.is_valid(t, frames.len())`  — fork-history (branch-cut) guard;
3. assert `t.frame_index < frames.len()`      — structural in-range guard;
4. truncate store to `frames[t.frame_index].saved_len`, replay the diff;
5. `diff_log.truncate(diff_start)`; **`frames.truncate(t.frame_index)`**;
6. `finish_restore(parent_stratum_diffs, …)` — recompute tags (§2);
7. `forks.fork(t, frames.len())` — record the branch cut.

The critical line is step 5: `frames.truncate(t.frame_index)` removes frame
`t.frame_index` ITSELF. The surviving top is `t.frame_index − 1` — the
**parent**. So:

> `restore(t)` undoes everything since `t` was created, *including the `mark()`
> that created it*. You land in the parent frame, exactly as you were the
> instant BEFORE calling `mark()`. The view equals `snapshots[t.frame_index]`
> (mark and the moment before it share a view), but the active frame is the
> parent, mid-stratum.

## 2. How the capture tags are reconstructed (NOT stored)

The diff log stores **clean values** (`from_repr` strips the tag at capture
time, `diff_store.rs:274`). `restore_entry` writes them back via `into_repr`,
which sets the tag CLEAR (`diff_store.rs:300`). So the tag is never recovered
from the diff — and must not be, because the tag is **frame-relative
bookkeeping**: "has slot `i` been captured in the *currently active* frame yet"
(first-write-wins, `capture` only logs if the tag is clear).

Restore recomputes the tags for the frame it lands in, in three steps:
- `restore_entry` clears every tag it touches (via `into_repr`);
- **`finish_restore`** walks the surviving **parent stratum's diff indices**
  and sets exactly those tags (`diff_store.rs:308`):
  `for (_, idx) in current_frame_diffs { set_tag(idx) }`.
  This re-establishes "captured-in-the-now-top(parent)-frame ⟺ appears in the
  parent's diff slice".
- (symmetric: `prepare_mark` clears the parent's tags when a child is marked,
  so the child starts fresh — which is why they must be *put back* on restore.)

This `finish_restore` rescan is **O(parent stratum)** on top of the O(replayed
diff) of the rollback. The `+p` term is *not* intrinsic to semi-persistence —
the predecessor `semper` design avoids it with a per-cell capture-depth (O(1)
mark, rescan-free backtrack) at the cost of `N·sizeof(C)` memory and a
nesting-depth cap. It *is* intrinsic to the 1-bit, zero-inline-memory flag this
crate chose. The full two-sided trade is in
[Design Alternatives, Part 2](restore-regrow-alternatives.md#e-per-cell-capture-depth-the-predecessor-semper-design).

**Why the parent's tags must be SET, not left at zero** (a tempting wrong
intuition): you land in the parent mid-stratum; the parent already captured
some slots before you marked `t`; those slots are genuinely captured-in-parent,
so a later `set` to one of them must NOT re-log. `prepare_mark` had cleared
them to 0 while the child was alive, so the correct value (1) must be restored.
Leaving them at 0 would double-capture. `finish_restore` does exactly this.

The one case where "all tags zero" IS correct: `t.frame_index == 0` (restoring
to the very first frame pops the whole stack). Then there is no parent, the
diff log truncates to empty, `finish_restore([])` sets nothing, and the bridge
invariant is vacuous (gated on `frames.len() > 0`). This is the degenerate end
of the general rule.

## 3. Empirical probe (the reuse question, answered)

```rust
let mut v: VecI<Id,u32,true> = VecI::new();
v.push(10); v.push(20);
let t = v.mark(Never);          // frame index 1, view [10,20]
v.set(0, 99);                   // capture slot 0 in frame 1
v.restore(t);                   // → [10,20], lands in PARENT (frame 0), frames.len()==1
assert!(v.is_valid_token(&t));  // ← TRUE: fork-history does NOT reject it
v.set(0, 77);                   // → [77,20], correctly logged in frame 0 (no double-capture)
v.restore(t);                   // ← PANIC: "token points beyond frame stack"
```

Observations:
- After the first restore, `set(0,77)` produced `[77,20]` and a later restore
  put `10` back — **first-write-wins intact, no tag bug** (§2 works).
- `is_valid_token(t)` returned **true** post-restore — fork-validity alone does
  not reject reuse (`t.depth=1 ≤ fork_depth=1`, inclusive boundary in
  `token.rs:85`).
- The second `restore(t)` panicked on the **structural** assert
  (`vec.rs:137`): after the first restore `frames.len()==1`, but
  `t.frame_index==1`, so `t.frame_index < frames.len()` is false.

### Answer to "can we restore to a token only once?"
Effectively yes — restoring to `t` truncates the frame stack *at* `t`'s index,
so `t.frame_index` is now out of range and any re-restore traps. This is the
same mechanism as "restoring past a token invalidates it": restoring *to* `t`
removes `t`'s own frame. There is no separate single-use flag — the frame-index
bound does it.

### Why the two guards are complementary (not redundant)
- The **structural** guard catches reuse / stale indices *on the same vec*
  (indices get reused after truncation, but the just-restored token's index is
  past the new end).
- The **fork-history** guard catches the *cross-branch* "abandoned future"
  case: restore to t1, then try to restore to t2 that lived in the now-cut
  branch — t2's `frame_index` might still be in range, so only the branch-cut
  check rejects it.

So "is `t` still restorable?" is the **conjunction** of both. A caller that
checks only `is_valid_token` gets a misleadingly optimistic answer for a
just-restored token. (Doc/ergonomics gap, not a soundness gap.)

## 4. Why we never "found" this, and the ergonomics gap

There is no correctness bug to find — restore is sound and reuse is trapped. The
real gap is **API ergonomics**: reuse-safety is a runtime panic where the type
system could make it a compile error. `restore(self, token: VecToken)` takes
the token by value, but `VecToken: Copy`, so the caller keeps a usable copy.

**Recommendation (experiment (a), tracked separately):** drop `Copy` from
`VecToken` and take it by move in `restore`, turning "panic on reuse" into
"compile error on reuse". Caveat: legitimate "restore to an ancestor later"
patterns keep *different* tokens around (e.g. proptest `snapshots[idx].clone()`
restoring to shallower marks) — those still typecheck; only reusing the *same*
token breaks, which is the goal. Needs an audit of egraph + proptests.

## 5. What the real consumer needs (LIFO Push/Pop)

`egraph/src/interpret.rs:229-250` is the only top-level driver:
```
Push(shrink) => self.marks.push(Mark { token: eg.mark(policy), … })
Pop          => let mark = self.marks.pop()?; eg.restore(mark.token); …
```
Strict LIFO: `Push` marks and stacks the token; `Pop` restores and discards it.
The e-graph **never re-restores a token and never mutates-then-re-restores**.
So the current "restore consumes the mark" semantics exactly matches the
consumer; nothing in production wants token reuse today.

## 6. The alternative: "restore-without-pop" (reusable checkpoint)

The review question: could `restore(t)` instead keep frame `t` live with an
**empty stratum and all its capture bits zero** — i.e. re-enter the marked
frame fresh — so the *same* `t` can be restored to repeatedly?

### What it would mean semantically
- After `restore(t)`: active frame is `t` itself (not the parent); its stratum
  is empty; view == `snapshots[t]`. Subsequent mutations log into frame `t`'s
  (fresh) stratum, and `restore(t)` again rolls them back. `t` stays valid.
- This is a **"reset to checkpoint" / reusable savepoint** semantics, vs the
  current **"pop the scope"** semantics.

### What it would take
1. `restore` truncates to `t.frame_index + 1` (keep frame `t`), not
   `t.frame_index`. Its stratum becomes `[t.diff_start, t.diff_start)` (empty).
2. `prepare_mark`-style tag clear over `[0, saved_len)` so frame `t` starts
   with zero capture bits (the bridge then holds with an empty top stratum:
   `captured()[j] ⟺ false`).
3. `finish_restore` would target frame `t`'s (empty) stratum — i.e. set NO
   tags. So this is actually *simpler* on the tag front (your "all zero"
   intuition is exactly right for THIS semantics — because here the top frame
   really is freshly marked).
4. Fork-history: `restore` must NOT pop `t`'s branch the same way — reusability
   means `t` survives, so either no `fork()` cut, or a cut that still admits
   `t`. Needs rethinking the branch-cut model (currently `fork` records a cut
   that, combined with the frame-index pop, invalidates `t`).

### The catch you spotted ("mutations after restore keep recording in the
### previous frame") — is it a problem?
Under the CURRENT (pop) semantics: after `restore(t)` you're in the parent, so
further mutations record into the **parent's** stratum. That is CORRECT for
LIFO scoping — you popped scope `t`, you're back in the enclosing scope, and
edits belong there. It is only "surprising" if you expected to still be inside
`t`. So it's not a bug; it's the pop semantics being literal.

Under the proposed (reusable) semantics, mutations would record into the
re-entered frame `t` — which is what you'd want for a "retry from checkpoint"
loop (speculative execution: checkpoint, try, reset, try again).

### Recommendation
Keep the current pop semantics as the default (it matches the LIFO consumer and
is already verified). If a reusable-checkpoint API is wanted, add it as a
SEPARATE operation — e.g. `reset_to(&t)` (by-ref, non-consuming) distinct from
`restore(t)` (by-move, consuming) — rather than changing `restore`'s meaning.
`reset_to` is arguably *easier* to verify (empty top stratum ⇒ trivial bridge),
but needs the fork-history model extended to keep `t` valid across repeated
resets. Prototype only if a consumer needs it; the e-graph does not today.

## 7. Verus tie-in

The tag-recompute mechanism (§2) is exactly the **capture-flag bridge** clause
of `wf`: `store.captured()[j] ⟺ captured_in_range(diffs, top.diff_start, n, j)`.
`finish_restore`'s verified postcondition re-derives the tags from the parent
stratum's diff slice; `restore`'s proof re-establishes the bridge via
`lemma_captured_subrange`. The reusable-checkpoint variant (§6) would make the
top stratum empty, so the bridge degenerates to `captured()[j] ⟺ false` over
`[0, saved_len)` — a strictly simpler obligation — but the fork-history
validity theorem (`lemma_fork_valid_characterization`) would need an analogue
for "t survives its own restore".

---
[← Table of Contents](00-table-of-contents.md)
