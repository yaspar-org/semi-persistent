# Verified Semi-Persistent Containers: Design & Proof Notes

The verified semi-persistent containers: the container layer the e-graph
engine runs on. The unverified reference implementation is
[`containers/`](../../../containers).

## Semi-persistence

Each container is semi-persistent: a version is marked and restored through an
externally provided history — `group::ForkHistory<M>` owns one `History` and one
typed member, and a standalone container is a group of one
(`ForkHistory::new(Vec::new())`). A mark records the current state and a restore
returns the member to a previously marked state, discarding the states marked
after it while keeping the checkpoint's own frame open, so its token can be
restored to again (semantics B; `restore_and_pop` is the SMT-LIB `pop`). No
container carries a token API, a token type or a genealogy of its own: doc 10 is
the shipped shape, doc 08 the token rules. The
externally-observable specification is a stack of deep copies: `mark` is `push`
(deep-copy the current contents onto the stack), `restore` is `pop` to the marked
level (discarding the entries above it). Maintaining that specification by
actually deep-copying on each `mark` would cost O(state) time and memory per mark
and O(N · state) for N nested marks.

The implementation avoids it by storing a **sparse negative diff** instead of the
copies. Hot capture records a cell's old value on its first write after a mark;
subsequent writes need no additional capture. Trail capture can retain
duplicate writes, and Cold history compresses closed frames. Chapter 17
describes these representations and their common reconstruction model. `restore` truncates the log to the mark and replays the
recorded old values in reverse, restoring each first-written cell to its
mark-time value; untouched cells were never logged. No deep copy is ever
materialized: a marked state is represented implicitly as the current contents
plus O(1) frame metadata and the diffs recorded since. Runtime memory also
includes the live value store, diff/frame capacities and the history's stamp
table, which is O(deepest depth ever reached) rather than O(restores).

Token validation is O(1): one generation-stamp read, not a walk. If `k` entries
are replayed, `r` cells are regrown, `p` entries belong to the surviving parent
frame, and `w` parallel-bitmap words are materialized, a restore is O(k+r+p) for
inline capture and O(k+r+p+w) for parallel capture.

## What is verified

The risk in the diff representation is a faulty replay (a dropped entry, a
wrong replay order, a cell restored from the wrong mark) silently producing a
state that differs from the deep-copy specification. The proof rules this out by
carrying the specification explicitly. The container holds a **ghost field**
`snapshots`: the stack of deep copies, defined in ghost code and erased before
compilation. The compiled column retains its live value store, tiered history pools, frame
metadata, policy and capture state, but not the ghost deep copies. Fork history
and identity belong to the external manager. The headline
theorem is the equivalence between the diff engine and the deep-copy
specification:

> after `restore(token)`, `view() == snapshots[token.depth]`

This holds per cell, at arbitrary mark-nesting depth, under any interleaving of
`push`, `set`, and `pop`. A companion result constrains which tokens `restore`
will accept: each `mark` opens a branch in a fork history, each `restore` cuts the
branches it discards, and a token naming a discarded state is rejected. The
development uses no `admit`s or `assume`s; run `cargo verus verify` for the
per-module tally. (That does not mean nothing is trusted; the current
implementation has 12 default-build `external_body` markers, 17 with
`literal-types`, enumerated in [Chapter 2](02-trust-boundary.md).)

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
17. **[The Three-Tier Frame Grid](17-three-tier-frame-grid.md)**: the geometric
    proof model for non-monotone saved lengths, Trail duplicate columns, Hot
    unique captures, Cold runs, cross-tier replay, the inductive lemmas
    suggested by horizontal, vertical, and representation changes, and
    rollover: when a mark, a tier limit, or an explicit pass converts a frame.
18. **[Store Policy for the Composite Containers](18-store-policy.md)**: the
    policy type parameter every composite takes, the two column families it is
    consulted through, `HotFirst` (the default) versus `TrailFirst`, and the
    two facts the abstract store made explicit in the proofs.
19. **[Verified Node Caches](19-verified-node-caches.md)**: design sketch. The
    hint index as a lower bound: the completeness invariant, the hash-consing
    theorem in the presence of collisions, restore with no index work, the
    two droppability rules, and the public contracts of the three e-graph
    caches derived by bi-abduction. Not yet implemented beyond `hinted_arena`.
20. **[Hot-Path Discipline](20-hot-path-discipline.md)**: writing verified
    code the optimizer can optimize. Each optimization hint from the 2026-09
    performance work confirmed or refuted against the code with its
    measurement; the rules that follow (inline the per-element entry points;
    check once at the public boundary, `requires` on internal cores; const
    generics tested before any read; one executable write path); the list
    append peel; the second-pass review table; the validation protocol.

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
    `restore` does to the frame stack (it resets to the checkpoint and keeps
    its frame open; `pop_scope` drops it), which tokens stay valid, and why.

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
