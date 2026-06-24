# Verified Semi-Persistent Containers: Design & Proof Notes

A Verus port of [`semi-persistent-containers`](../../../containers).

## Semi-persistence

Each container is semi-persistent: it supports `mark()` and `restore(token)`,
where `mark` records the current state and `restore` returns the container to a
previously marked state, discarding all states marked after it. The
externally-observable specification is a stack of deep copies: `mark` is `push`
(deep-copy the current contents onto the stack), `restore` is `pop` to the marked
level (discarding the entries above it). Maintaining that specification by
actually deep-copying on each `mark` would cost O(state) time and memory per mark
and O(N · state) for N nested marks.

The implementation avoids it by storing a **sparse negative diff** instead of the
copies. On the first write to a cell after a mark, it records that cell's old
value in a diff log; subsequent writes to the same cell record nothing
(first-write-wins). `restore` truncates the log to the mark and replays the
recorded old values in reverse, restoring each first-written cell to its
mark-time value; untouched cells were never logged. No deep copy is ever
materialized: a marked state is represented implicitly as the current contents
minus the diffs recorded since. Memory is proportional to the number of modified
cells, and `restore` runs in time proportional to the diff.

## What is verified

The risk in the diff representation is a faulty replay (a dropped entry, a
wrong replay order, a cell restored from the wrong mark) silently producing a
state that differs from the deep-copy specification. The proof rules this out by
carrying the specification explicitly. The container holds a **ghost field**
`snapshots`: the stack of deep copies, defined in ghost code (erased before
compilation, so the compiled container retains only the diff). The headline
theorem is the equivalence between the diff engine and the deep-copy
specification:

> after `restore(token)`, `view() == snapshots[token.frame_idx]`

This holds per cell, at arbitrary mark-nesting depth, under any interleaving of
`push`, `set`, and `pop`. A companion result constrains which tokens `restore`
will accept: each `mark` opens a branch in a fork history, each `restore` cuts the
branches it discards, and a token naming a discarded state is rejected. The
development uses no `admit`s or `assume`s; run `./verify-all.sh` for the
per-module tally. (That does not mean nothing is trusted; the trust boundary is
7 `external_body` items, enumerated in [Chapter 2](02-trust-boundary.md).)

## Reference: what is in the crate (chapters 01–02, 09–10)

01. **[Master Verification Design](01-verification-design.md)**: the layout,
    the `wf` invariant, the `overlay` reconstruction model, and branch-cut safety.
    Start here.
02. **[The Trust Boundary](02-trust-boundary.md)**: exactly what is
    `external_body` and why; frames how to read every "verified" claim.
09. **[Arena Aliasing & the Ghost-Id-Set Style](09-arena-aliasing-dynamic-frames.md)**:
    how the arena-backed containers express aliased/cyclic structure as ghost
    id-sets and prove separation as explicit dynamic frames.
10. **[The B+Tree Set](10-bplus-tree.md)**: the one recursive container: node
    layout, the ghost-`Tree` invariant, arena-never-overflows, insert with split
    propagation, the cursor soundness theorems, `mark`/`restore`, proof status.

## Techniques: reusable lessons (chapters 03–08)

03. **[Fork History / Branch-Cut Safety](03-fork-history.md)**: token validity:
    the fork tree, and `fork_valid` ⟺ reachable-on-path ∧ depth ≤ bound.
04. **[Pop into a Marked Region](04-pop.md)**: the `Copy + Default` /
    resize-default decisions behind popping inside a marked region.
05. **[The Flat Central Lemma](05-flat-central-lemma.md)**: the reconstruction
    lemma stated per-cell, so it needs no `saved_len` monotonicity.
06. **[Regrow & Capture-Flag Alternatives](06-restore-regrow-alternatives.md)**:
    the two representation choices, and why production's unbounded `force_capture`
    is not adopted.
07. **[Default Impls & `Tagged` Niche Safety](07-default-impls.md)**: why a
    fabricated `Default` filler is never observable, and the niche-bit recipe.
08. **[Token Reuse & Restore Semantics](08-token-reuse-and-restore.md)**: what
    `restore` does to the frame stack and why a reused token is trapped.

## Side notes: unnumbered

Not part of the chapter sequence: a chronological log and a maintenance playbook.

- **[Proof Attempts Log](proof-attempts-log.md)**: the dead-ends and the
  recurring Verus lessons that came out of them.
- **[Proof-Performance Playbook](proof-performance-playbook.md)**:
  diagnosing slow/hanging/flaky proofs (maintenance reference).

## Future work

- **[Feature-Parity Audit](../future/parity-audit-and-plan.md)**: method-by-method
  coverage vs. production; what has no verus counterpart.
- **[Byte-Accounting Diagnostics (Group B)](../future/verify-byte-accounting.md)**:
  the plan to verify `tracking_bytes`/`total_bytes`/`heap_bytes`, removing the last
  spec-free `external_body`.

## Relationship to the production docs

Production's design docs ([`containers/doc/design`](../../../containers/doc/design/00-table-of-contents.md))
describe the *data structures*; these describe the *proofs*. Where they disagree,
the code and its checked Verus contract govern.
