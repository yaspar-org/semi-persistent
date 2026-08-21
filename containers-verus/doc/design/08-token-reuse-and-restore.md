# Token reuse, restore semantics, and the capture-tag recompute

What `restore` does to the frame stack, why reusing a token is caught, how the
capture-tag bits are reconstructed, and how a reusable-checkpoint variant would
differ. Grounded in production (`vec.rs`, `diff_store.rs`, `token.rs`) and the
verified port.

## 1. What `restore(t)` does to the frame stack

`mark()` at frame-stack depth `d` creates frame index `d` and returns a token
with `frame_idx == d`. With no outstanding mark, the first token therefore
has frame index 0. `restore(t)`:

1. assert same container;
2. assert `t.frame_idx < frames.len()` (the frame is still live);
3. assert counter headroom and `forks.is_valid(t, frames.len())`;
4. resize the store to `frames[t.frame_idx].saved_len`, then replay the diff;
5. `diff_log.truncate(diff_start)`; **`frames.truncate(t.frame_idx)`**;
6. `finish_restore(parent_stratum_diffs, …)` recomputes tags (§2);
7. `forks.fork(t, frames.len())` records the branch cut.

Step 5 removes frame `t.frame_idx` *itself*. If the index is nonzero, the
surviving top is `t.frame_idx - 1`, the parent. If it is zero, the frame stack
becomes empty. Thus `restore(t)` undoes everything since `t` was created,
including that mark. The view equals `snapshots[t.frame_idx]` (the mark and
the instant before it share a view), while subsequent mutations belong to the
surviving parent frame, if any.

## 2. How the capture tags are reconstructed (not stored)

The diff log stores **clean values**: `from_repr` strips the tag at capture
time. `restore_entry` writes them back via `into_repr`, which sets the tag
clear. The tag is never recovered from the diff, and must not be, because the
tag is **frame-relative bookkeeping**: "has slot `i` been captured in the
*currently active* frame yet" (first-write-wins; `capture` only logs if the tag
is clear).

Restore recomputes the tags for the frame it lands in, in three steps:

- `restore_entry` clears every tag it touches (via `into_repr`);
- **`finish_restore`** walks the surviving parent stratum's diff indices and
  sets exactly those tags (`for (_, idx) in current_frame_diffs { set_tag(idx) }`),
  re-establishing "captured-in-the-now-top(parent)-frame ⟺ appears in the
  parent's diff slice";
- (symmetric: `prepare_mark` clears the parent's tags when a child is marked,
  so the child starts fresh, which is why they must be put back on restore).

This `finish_restore` rescan is O(parent stratum) on top of the O(replayed
diff) of the rollback. The `+p` term is not intrinsic to semi-persistence: the
per-cell capture-depth alternative restores old depths during replay and
avoids the rescan. It is a consequence of this crate's one-bit flag protocol,
which derives parent flags from the surviving diff. The architectural trade,
including what remains unbenchmarked, is in
[Design Alternatives, Part 2](06-restore-regrow-alternatives.md#e-per-cell-capture-depth-alternative).

The parent's tags must be *set*, not left at zero. You land in the parent
mid-stratum; the parent already captured some slots before `t` was marked;
those slots are genuinely captured-in-parent, so a later `set` to one of them
must not re-log. `prepare_mark` had cleared them to 0 while the child was
alive, so the correct value (1) must be restored; leaving them at 0 would
double-capture. `finish_restore` does exactly this.

The one case where "all tags zero" is correct is `t.frame_idx == 0`
(restoring to the very first frame pops the whole stack): there is no parent,
the diff log truncates to empty, `finish_restore([])` sets nothing, and the
bridge invariant is vacuous (gated on `frames.len() > 0`). This is the
degenerate end of the general rule.

## 3. Why reusing a token is rejected

Restoring to a token `t` invalidates it because truncation removes its own
frame. The verified crate's public `is_valid_token` means "restorable now": it
checks tracking, container identity, frame liveness, branch genealogy, and
counter headroom. It therefore returns `false` for a consumed token, and
`try_restore` rejects that token without mutation. Direct `restore` retains the
panic-shaped compatibility contract.

The retained unverified reference implementation's `is_valid_token` is
genealogy-only and can still answer `true` for a consumed token whose frame is
gone; its direct `restore` catches reuse with the separate frame-bound assert.
That is a documented API difference, not a difference in accepted restores.

```rust
let mut v: VecI<Id,u32,true> = VecI::new();
v.push(10); v.push(20);
let parent = v.mark(Never);     // frame index 0
v.set(1, 21);                   // parent-frame diff
let child = v.mark(Never);      // frame index 1
v.set(0, 99);                   // child-frame diff
v.restore(child);               // → [10,21], lands in parent frame 0
assert!(!v.is_valid_token(&child));
assert!(v.is_valid_token(&parent));
```

The two guards are complementary, not redundant:

- The **frame-liveness** guard catches reuse and stale indices on the same vec:
  after truncation `t.frame_idx` is at or past the new end.
- The **fork-history** guard catches the cross-branch "abandoned future" case:
  restore to `t1`, then try to restore to `t2` that lived in the now-cut
  branch; `t2`'s `frame_idx` might still be in range, so only the branch-cut
  check rejects it.

So "is `t` still restorable?" is the conjunction of liveness, identity,
headroom, and genealogy in the verified public API.

## 4. Runtime rather than affine token consumption

`restore(self, token: VecToken)` takes the token by value, but `VecToken: Copy`,
so the caller keeps a usable copy. Reuse returns an error through `try_restore`
or panics through direct `restore`; it is not a compile error. Dropping `Copy`
from `VecToken` and taking it by move would make the direct API affine. The
caveat is that legitimate "restore to an ancestor later"
patterns keep *different* tokens around (proptest restores to shallower marks
via cloned tokens); those still typecheck, only reusing the *same* token
breaks, which is the goal. Adopting that API requires checking all e-graph and
property-test token retention sites.

## 5. What the real consumer needs (LIFO Push/Pop)

The e-graph interpreter is the only top-level driver, and it is strict LIFO:
`Push` marks and stacks the token, `Pop` restores and discards it. It never
re-restores a token and never mutates-then-re-restores. So the current "restore
consumes the mark" semantics exactly matches the consumer; nothing in
production wants token reuse today.

## 6. The alternative: "restore-without-pop" (reusable checkpoint)

`restore(t)` could instead keep frame `t` live with an empty stratum and all its
capture bits zero (re-enter the marked frame fresh), so the *same* `t` can be
restored to repeatedly. After such a `restore(t)` the active frame is `t` itself
(not the parent), its stratum is empty, and `view() == snapshots[t]`; subsequent
mutations log into frame `t`'s fresh stratum, and `restore(t)` again rolls them
back. This is a "reset to checkpoint" / reusable savepoint semantics, versus the
current "pop the scope" semantics.

It would take:

1. `restore` truncates to `t.frame_idx + 1` (keep frame `t`), not
   `t.frame_idx`; its stratum becomes empty.
2. A `prepare_mark`-style tag clear over `[0, saved_len)` so frame `t` starts
   with zero capture bits (the bridge then holds with an empty top stratum,
   `captured()[j] ⟺ false`).
3. `finish_restore` then sets no tags. So this is actually *simpler* on the tag
   front: "all zero" is exactly right for this semantics, because here the top
   frame really is freshly marked.
4. Fork-history must not pop `t`'s branch: reusability means `t` survives, so
   either no `fork()` cut or a cut that still admits `t`. This needs the
   branch-cut model rethought (currently `fork` plus the frame-index pop is
   what invalidates `t`).

Under the current pop semantics, mutations after `restore(t)` record into the
parent's stratum. That is correct for LIFO scoping: you popped scope `t`, you
are back in the enclosing scope, and edits belong there. Under the reusable
semantics they would record into the re-entered frame `t`, which is what a
"retry from checkpoint" loop (speculative execution) wants.

The recommendation is to keep the pop semantics as the default (it matches the
LIFO consumer and is verified) and, if a reusable checkpoint is ever wanted, add
it as a separate `reset_to(&t)` (by-ref, non-consuming) distinct from
`restore(t)` (by-move, consuming), rather than changing `restore`'s meaning.
`reset_to` is arguably easier to verify (empty top stratum ⇒ trivial bridge) but
needs the fork-history model extended to keep `t` valid across repeated resets.

## 7. Verus tie-in

The tag-recompute mechanism (§2) is exactly the **capture-flag bridge** clause
of `wf`: `store.captured()[j] ⟺ captured_in_range(diffs, top.diff_start, n, j)`.
`finish_restore`'s verified postcondition re-derives the tags from the parent
stratum's diff slice; `restore`'s proof re-establishes the bridge via
`lemma_captured_subrange`. The reusable-checkpoint variant (§6) would make the
top stratum empty, so the bridge degenerates to `captured()[j] ⟺ false` over
`[0, saved_len)`, a strictly simpler obligation, but the fork-history validity
theorem (`lemma_fork_valid_characterization`) would need an analogue for "t
survives its own restore".

---
[← Table of Contents](00-table-of-contents.md)
