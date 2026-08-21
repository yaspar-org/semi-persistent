# Verified Semi-Persistent Containers: Design & Proof Notes

The verified semi-persistent containers: the container layer the e-graph
engine runs on. The unverified reference implementation is
[`containers/`](../../../containers).

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
plus O(1) frame metadata and the diffs recorded since. Runtime memory also
includes the live value store, diff/frame capacities, container identity, and
fork history, which grows by O(1) per restore. If `b` fork-history links are
walked during token validation, `k` entries are replayed, `r` cells are
regrown, `p` entries belong to the surviving parent frame, and `w`
parallel-bitmap words are materialized, restore is O(b+k+r+p) for inline
capture and O(b+k+r+p+w) for parallel capture.

## What is verified

The risk in the diff representation is a faulty replay (a dropped entry, a
wrong replay order, a cell restored from the wrong mark) silently producing a
state that differs from the deep-copy specification. The proof rules this out by
carrying the specification explicitly. The container holds a **ghost field**
`snapshots`: the stack of deep copies, defined in ghost code and erased before
compilation. The compiled container retains its ordinary value store, sparse
diff log, frame metadata, fork history, identity, and capture-state fields, but
not the ghost deep copies. The headline
theorem is the equivalence between the diff engine and the deep-copy
specification:

> after `restore(token)`, `view() == snapshots[token.frame_idx]`

This holds per cell, at arbitrary mark-nesting depth, under any interleaving of
`push`, `set`, and `pop`. A companion result constrains which tokens `restore`
will accept: each `mark` opens a branch in a fork history, each `restore` cuts the
branches it discards, and a token naming a discarded state is rejected. The
development uses no `admit`s or `assume`s; run `cargo verus verify` for the
per-module tally. (That does not mean nothing is trusted; the trust boundary is
27 `external_body` items in the default build, 32 with `literal-types`,
enumerated in [Chapter 2](02-trust-boundary.md).)

## Reference: what is in the crate

Filename numbers are stable ids, not the reading sequence; follow this
listing's order.

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
12. **[The Sorted-Vec Cursor](12-sorted-vec-cursor.md)**: the galloping seek,
    verified. A proof whose subject is a query-engine algorithm
    rather than a container; reuses the B+tree's `seek_target_idx` unchanged.
15. **[The Dense-Span Multimap](15-dense-span-map.md)**: the build-once index
    behind the e-graph's per-round index families: a two-pass counting build
    refined to the per-key filter of its input stream, plus the
    generation-stamped arena-reuse build path.
16. **[The Layered Span Map](16-layered-span-map.md)**: incremental maintenance
    over chapter 15: a base generation, one delta generation, per-key
    invalidation, and the cross-generation sortedness lemma with the caller
    obligation it rests on. Verified; the engine does not enable it.

## The class layer

The verified aggregate `EClasses` (rings, union-find, class keys, use-lists,
min-monomial pool) carries invariants W1..W7 as its `wf()`; the invariant
table is the `eclasses.rs` module header. Three documents cover it (where
a filename keeps a number, the number is a stable id, not a position in
the reading sequence above):

- **[E-Graph Class-Layer Integration](egraph-class-layer.md)**: the
  engine's `EClasses`/`UnionFind` are type aliases of the verified kernel; the
  legacy comparisons are explicitly historical.
- **[Conformance baseline](../../../containers-conformance/BASELINE.md)**:
  finite differential, layout, and Criterion evidence against the retained
  reference implementation.

## Techniques: reusable lessons (chapters 03–08)

03. **[Fork History / Branch-Cut Safety](03-fork-history.md)**: token validity:
    the fork tree, and `fork_valid` ⟺ reachable-on-path ∧ depth ≤ bound.
04. **[Pop into a Marked Region](04-pop.md)**: the `Copy + Default` /
    resize-default decisions behind popping inside a marked region.
05. **[The Flat Central Lemma](05-flat-central-lemma.md)**: the reconstruction
    lemma stated per-cell, so it needs no `saved_len` monotonicity.
06. **[Regrow & Capture-Flag Alternatives](06-restore-regrow-alternatives.md)**:
    the two representation choices, and why the retired unbounded
    `force_capture` design was replaced by conditional capture.
07. **[Default Impls & `Tagged` Niche Safety](07-default-impls.md)**: why a
    fabricated `Default` filler is never observable, and the niche-bit recipe.
08. **[Token Reuse & Restore Semantics](08-token-reuse-and-restore.md)**: what
    `restore` does to the frame stack and why a reused token is trapped.

## Future work

- **[Byte-Accounting Diagnostics (Group B)](../future/verify-byte-accounting.md)**:
  the plan to verify `tracking_bytes`/`total_bytes`/`heap_bytes`, removing the last
  spec-free `external_body`.
- **[Conformance and Release Work](../future/conformance-and-release.md)**:
  consumer `Tagged` law tests, B+ header-history integration, package/reference
  cutover, reduced Miri coverage, remaining Criterion rows, the supported
  compatibility surface, proof-forest verification, and const-generic tracking
  refinement.

## Relationship to the production docs

Production's design docs ([`containers/doc/design`](../../../containers/doc/design/00-table-of-contents.md))
describe the *data structures*; these describe the *proofs*. Where they disagree,
the code and its checked Verus contract govern.
