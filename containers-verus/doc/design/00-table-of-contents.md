# Verified Semi-Persistent Containers — Design & Proof Notes

A Verus port of the [`semi-persistent-containers`](../../../containers) crate,
built to formally verify the semi-persistent protocol — memory-cheap snapshots
(a sparse negative diff, never a full copy) and O(k) `restore` — and the
headline correctness theorem

> after `restore(token)`, `view() == snapshots[token.frame_idx]`

proved with **no `admit`s or `assume`s**. Run `./verify-all.sh` from the
`containers-verus/` package root for the current per-module tally.

These documents are organized in two layers. The **reference** layer
(Chapter 0–1) is the durable description of the data-structure layout,
invariants, and proved theorems. The **method** layer (Chapter 2–) records the
proof techniques, the ladder of progressively-stronger theorems we proved, and
the design alternatives we weighed — the "how we got here", kept because the
same patterns recur as more containers are verified.

## Reference

0. **[Master Verification Design](00-verification-design.md)**
   The data-structure layout, the declarative two-arm frame invariant, the
   `overlay` reconstruction model, stratification across nested frames, the
   capture-flag bridge, and fork-history / branch-cut safety. 2-D diagrams of
   every invariant. Start here.

1. **[Fork History / Branch-Cut Safety](m5-fork-history-design.md)**
   How tokens are validated: the fork tree, how a restore records a cut, the
   precise definition of "on the current path", and the branch-safety theorem
   (`fork_valid` ⟺ reachable-on-path ∧ depth ≤ bound).

## Method & techniques

2. **[Faithful Pop — Plan & Decisions](faithful-pop-plan.md)**
   Lifting `pop` to remove cells from inside a marked region. The locked
   decisions (`Copy + Default`, resize-default regrow vs production's
   push-from-diff), and the commit sequence.

3. **[Flat / Target-Clamped Central Lemma](flat-central-lemma-design.md)**
   The reconstruction lemma restated per-cell and base-parametric, so it needs
   no `saved_len` monotonicity — what made dropping that invariant clean.

4. **[Restore Regrow — Design Alternatives](restore-regrow-alternatives.md)**
   Default-pad vs Clone-scan vs force-record (and why production's unbounded
   `force_capture` is a latent DoS we deliberately diverge from).

5. **[Default Implementations & `Tagged` Niche Safety](default-impls-design.md)**
   Why every container element type needs `Default`, why a fabricated filler is
   sound (never observable), and how a `Tagged` type's stolen niche bit stays
   safe — with a per-type recipe table for the whole production codebase.

6. **[Token Reuse & Restore Semantics](token-reuse-and-restore-semantics.md)**
   What `restore(t)` does to the frame stack, how capture tags are *recomputed*
   (not stored), why re-using a token is trapped, and the "reusable checkpoint"
   alternative semantics.

7. **[Proof Attempts Log](proof-attempts-log.md)**
   The chronological narrative: the ladder of weakened theorems we proved in
   sequence, the dead-ends we reverted, and the recurring Verus lessons.

## Relationship to the production design docs

The production crate's design docs (one chapter per container) live in
[`containers/doc/design`](../../../containers/doc/design/00-table-of-contents.md)
and describe the *data structures*. These docs describe the *proofs* of the
same structures. Where the two disagree on a detail, the code — and the Verus
contract that is checked against it — governs.
