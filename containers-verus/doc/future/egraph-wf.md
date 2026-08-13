# The e-graph's global well-formedness invariant

This document defines the well-formedness invariant of the assembled e-graph
(the `EClasses` aggregate: class ring, union-find, repr set, use-lists,
min-monomial pool) and stages the work of proving that every mutation
preserves it. It is a work plan, not a status page: what is proved today is
what `cargo verus verify` accepts, and what is monitored today is what the
debug builds assert.

The motivating gap: each container is verified in isolation, but the
invariants that make the aggregate an e-graph are *agreement* properties
between containers, and no machine checks them. The `splice_absorb` entry in
`partial-api-allowlist.txt` (class WITNESS-PENDING) records one instance: the
call is safe because two union-find roots always sit on distinct rings, and
that argument lives in a comment. This plan turns those arguments into specs.

## The state

`EClasses<T, L, N>` (egraph/src/classes.rs) holds five components. Three are
verified containers with specification-level views this plan builds on:

- `entries: CircularList<Opt<T::Index>, T>`, the class ring. Verified. Its
  `wf()` already proves the rings partition the allocated cells and that
  `splice` merges exactly two distinct rings.
- `reprs: SparseSet<ClassData<L, T>, T::Index>`, one slot per live class.
  Verified; exposes the live-key set as a spec view.
- `uses: ListArena<T, L, N>`, per-class parent lists. Verified; its ghost
  model gives each list as a `Seq` and proves the lists are disjoint.
- `uf: UnionFind<T>`, two `VecI` columns (`parent_fast`, `rank`). Production
  code, no specification. This is the one unverified component.
- `min_pool: VecP<Opt<T>>` with per-class `min_row` numbers in `ClassData`.
  Verified storage, unspecified geometry.

## The invariant

Over a ghost view `classes(x) = { y | uf_find(y) == uf_find(x) }`, where
`uf_find` is the spec-level root function of the parent column:

- **W1, forest.** The parent column is acyclic: following `parent_fast` from
  any allocated id reaches a fixed point, and `rank` strictly decreases along
  no edge (rank bounds height, which gives `find` its termination measure).
- **W2, roots are the live classes.** `x` is a union-find root iff the ring
  cell `x` carries a present payload iff that payload is a live key in
  `reprs`. Absorbed ids have absent payloads and are not roots.
- **W3, rings realize the union-find partition.** `y` lies on `x`'s ring iff
  `uf_find(y) == uf_find(x)`. The ring side of the partition is already
  proved inside `CircularList`; W3 is the agreement of that partition with
  the union-find's, and it is what discharges `splice_absorb`'s
  distinct-rings precondition: distinct roots imply distinct classes imply
  distinct rings.
- **W4, use-list ownership.** The `use_list` keys of live classes are
  pairwise distinct, and every non-empty `ListArena` list is owned by exactly
  one live class. With `ListArena`'s proved disjointness this makes
  `splice_uses(survivor, absorbed)` hit two distinct lists.
- **W5, use-list contents (up to staleness).** Every entry of class `c`'s use
  list is a node that had a child in `c` when the entry was appended. Entries
  go stale between a merge and the rebuild that recanonicalizes them; W5
  deliberately does not claim freshness. Freshness after rebuild is W7.
- **W6, pool geometry.** `min_pool.len() == allocated_rows * min_width`;
  every live `min_row` is below `allocated_rows`; live `min_row` values are
  pairwise distinct. Rows are never freed, so `allocated_rows` only grows.
- **W7, congruence at the rebuild fixpoint.** When the dirty set is empty, the
  hash-cons maps each live node's canonical form to its id, and no two live
  nodes share a canonical form. W7 is the correctness theorem of `rebuild`,
  not a step invariant; stages 0 through 3 do not touch it.

## Stages

**Stage 0: monitor W2, W3 and W6 in debug builds.** Extend the runtime-monitor
pattern from commit 0e74a91 (debug monitors on `external_body` assumptions) to
the aggregate: after `merge`, walk the survivor's ring and assert every member
finds the survivor (W3, bounded by ring length); assert the absorbed id lost
its payload and its repr key (W2); assert the pool arithmetic (W6). This is
assertion code, not proof, but it runs under the existing differential and
property suites, which exercise merge orders the arguments in comments were
never tested against. Costs nothing in release builds.

**Stage 1: a verified union-find.** The missing component. Specify the parent
column as a ghost forest with `uf_find` as its root function; prove
`make_set`, `find` (with path compression), `union`, `union_directed`
preserve W1 and that `union` returns the two prior roots. Termination of
`find` comes from the rank bound, the same argument the production comment
makes informally (max rank 63 at 2^63 ids). Mark/restore archives the ghost
forest the way `ListArena` archives its model (list.rs, Phase 7). This is a
known-shape verification; the effort estimate is an inference from the
`ListArena` and `CircularList` proofs, not a measurement.

**Stage 2: a verified `EClasses` kernel.** Move the aggregate into
containers-verus with W1 through W6 as its `wf()`, and prove `add_singleton`,
`add_use`, `merge` (all variants), `splice_uses`, `mark`, `restore` preserve
it. The container views make every clause stateable today; the proofs get
`splice_absorb`'s precondition from W2 + W3 instead of from a comment, which
removes the last WITNESS-PENDING entries from the allowlist. The consumer
migration is mechanical, as the container migrations were.

**Stage 3: the dirty-set discipline.** `EGraph::merge` breaks W5-freshness on
purpose and repairs it at rebuild. State that honestly as
`wf_except(dirty)`: W1 through W4 and W6 hold unconditionally; the nodes
whose freshness is suspended are exactly the dirty set. This makes the
deferred-repair convention a checked object and gives rebuild its loop
invariant: each iteration shrinks the dirty set, W-full holds when it is
empty.

**Stage 4: rebuild restores W7.** The congruence-closure fixpoint theorem.
Postponed, not planned: egg's rebuild has a paper proof and congruence
closure has mechanizations in other provers, but no Verus mechanization
exists to calibrate against, so any effort number here would be invented.
Revisit when stage 3's dirty-set invariant is in place, because W7's
statement needs it.

## Order of work and what would change it

Stages 0 and 1 are independent and can land in either order; stage 0 first,
because it is days of work and it converts the two arguments this plan exists
to check (W2, W3) from comments into assertions that run on every CI test.
Stage 2 requires stage 1 (W2 and W3 quantify over `uf_find`). Stage 3
requires stage 2. If stage 0's monitors ever fire on the existing suites, fix
first and re-plan: a violated W2 or W3 means the informal argument was wrong,
and stage 2's proofs would be attempting to prove a falsehood.
