# Verified Semi-Persistent Containers — Design & Proof Notes

A Verus port of the [`semi-persistent-containers`](../../../containers) crate,
built to formally verify the semi-persistent protocol — memory-cheap snapshots
(a sparse negative diff, never a full copy) and O(k) `restore` — and the
headline correctness theorem

> after `restore(token)`, `view() == snapshots[token.frame_idx]`

proved with **no `admit`s or `assume`s**. Run `./verify-all.sh` from the
`containers-verus/` package root for the current per-module tally.

These documents are organized in two layers. The **reference** layer
(chapters 01–02) is the durable description of the data-structure layout,
invariants, and proved theorems. The **method** layer (chapters 03–08) records the
proof techniques, the ladder of progressively-stronger theorems we proved, and
the design alternatives we weighed — the "how we got here", kept because the
same patterns recur as more containers are verified.

## Reference

01. **[Master Verification Design](01-verification-design.md)**
   The data-structure layout, the declarative two-case frame invariant, the
   `overlay` reconstruction model, stratification across nested frames, the
   capture-flag bridge, and fork-history / branch-cut safety. 2-D diagrams of
   every invariant. Start here.

02. **[Fork History / Branch-Cut Safety](02-fork-history.md)**
   How tokens are validated: the fork tree, how a restore records a cut, the
   precise definition of "on the current path", and the branch-safety theorem
   (`fork_valid` ⟺ reachable-on-path ∧ depth ≤ bound).

## Method & techniques

03. **[Pop into a Marked Region — Plan & Decisions](03-pop.md)**
   Lifting `pop` to remove cells from inside a marked region. The locked
   decisions (`Copy + Default`, resize-default regrow vs production's
   push-from-diff), and the commit sequence.

04. **[Flat / Target-Clamped Central Lemma](04-flat-central-lemma.md)**
   The reconstruction lemma restated per-cell and base-parametric, so it needs
   no `saved_len` monotonicity — what made dropping that invariant clean.

05. **[Design Alternatives: Regrow & Capture-Flag Representation](05-restore-regrow-alternatives.md)**
   Two design axes, with the rejected/predecessor options on record. Regrow:
   Default-pad vs Clone-scan vs force-record (and why production's unbounded
   `force_capture` is a latent DoS). Capture flag: the chosen inline 1-bit —
   picked for raw cache density and read/write access cost on the hot loops,
   *not* backtracking speed — vs the predecessor `semper`'s per-cell
   capture-depth array, which is actually faster to mark/backtrack but pays in
   read density and `N·sizeof(C)` memory. A genuinely two-sided trade.

06. **[Default Implementations & `Tagged` Niche Safety](06-default-impls.md)**
   Why every container element type needs `Default`, why a fabricated filler is
   sound (never observable), and how a `Tagged` type's stolen niche bit stays
   safe — with a per-type recipe table for the whole production codebase.

07. **[Token Reuse & Restore Semantics](07-token-reuse-and-restore.md)**
   What `restore(t)` does to the frame stack, how capture tags are *recomputed*
   (not stored), why re-using a token is trapped, and the "reusable checkpoint"
   alternative semantics.

08. **[Proof Attempts Log](08-proof-attempts-log.md)**
   The chronological narrative: the ladder of weakened theorems we proved in
   sequence, the dead-ends we reverted, and the recurring Verus lessons.

09. **[Arena Aliasing and the Ghost-Id-Set Proof Style](09-arena-aliasing-dynamic-frames.md)**
   Why arena-backed containers (SparseSet, ListArena, CircularList) encode
   references as integer ids — bypassing Rust ownership to get aliased/cyclic
   structures — and why that makes Verus their only well-formedness guarantee.
   The ghost-id-set invariant as explicit *dynamic frames*; separation and
   non-aliasing as proved predicates; the frame/anti-frame (bi-abduction) shape
   of the operation proofs. Companion to [Ch 1 §10](01-verification-design.md).

## Future work

- **[B+Tree Set — Design and a Bi-Abductive Proof Plan](future/bplus-tree-design.md)**
  Scoping for the one container not yet verified: the data structure, the
  recursive/balanced `wf` invariant, and how an insert-with-split proof
  decomposes under the dynamic-frames discipline. Proof not yet attempted;
  insert-only (production has no `remove`).

## Relationship to the production design docs

The production crate's design docs (one chapter per container) live in
[`containers/doc/design`](../../../containers/doc/design/00-table-of-contents.md)
and describe the *data structures*. These docs describe the *proofs* of the
same structures. Where the two disagree on a detail, the code — and the Verus
contract that is checked against it — governs.
