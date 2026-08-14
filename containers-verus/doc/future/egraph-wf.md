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

The seven clauses, as first planned. W1 through W6 are now implemented and
proved in `containers-verus` (see the status note below); where the proved
form differs from the first sketch, the text states the proved form.

- **W1, forest.** The union-find's ghost root map is canonical
  (`roots[roots[i]] == roots[i]`) and self-parented; a parent step preserves
  the root; a self-parent is a root; and a ghost distance measure is 0
  exactly at roots and strictly decreases along every parent edge. The
  distance clause is acyclicity in the form a `decreases` clause consumes,
  and it is `find`'s termination measure. Rank is stored but no clause reads
  it: it is a survivor-selection heuristic, and its bump saturates rather
  than carrying the `rank <= log2(n)` argument.
- **W2, roots are the live classes.** `x` is a union-find root iff the ring
  cell `x` carries a present payload; each root's key is live in `reprs`;
  keys are injective across roots; and every live key is some root's key. A
  bijection between roots and live classes, stated as four clauses.
- **W3, rings realize the union-find partition.** Same ring iff same root,
  stated in both directions over ring-model coordinates. The ring side of
  the partition is proved inside `CircularList`; W3 is the agreement of that
  partition with the union-find's, and it is what discharges
  `splice_absorb`'s distinct-rings precondition inside `merge`: distinct
  roots imply distinct rings.
- **W4, use-list ownership.** Live classes own pairwise-distinct, allocated
  use-lists, so `splice_uses(survivor, absorbed)` hits two distinct lists.
- **W5, use-list entries are allocated.** Every entry of every use-list
  names an allocated node id. This is deliberately the weak form: it does
  NOT claim the entry is canonical or fresh, because merges stale entries on
  purpose and rebuild repairs them. The strong form, freshness outside a
  dirty set, is stage 3.
- **W6, pool geometry.** The pool length is a whole number of `min_width`
  rows; every live class's row number points at an allocated row; no two
  live classes share a row. Which node a pool cell names is data, not
  invariant: W6 is geometry.
- **W7, congruence at the rebuild fixpoint.** When the dirty set is empty,
  the hash-cons maps each live node's canonical form to its id, and no two
  live nodes share a canonical form. W7 is the correctness theorem of
  `rebuild`, not a step invariant; stages 0 through 3 do not touch it.

## What `wf` states, and what it does not

The aggregate's `wf()` (`eclasses.rs`) is three layers, all machine-checked:
every public mutator carries `requires old(self).wf(), ensures
final(self).wf()`, and the verifier rejects the build unless each body
re-establishes every clause.

**Layer 1: each component's own invariant.** The ring's model partitions the
allocated cells with correct successor structure; the repr set's index
column is a permutation inverting the sparse column on the live region; the
union-find is W1; the use-list arena's ghost lists are disjoint and its
head/tail/next/length caches agree with them; the pool vector's
store/diff-log/frame invariants hold.

**Layer 2: the agreement between components.** W2 through W6 above, plus the
glue bounds: one ring cell and one union-find slot per node, repr capacity
at most the node count, and every payload and pool cell decodes (niche
encodings are well-formed, so reads round-trip).

**Layer 3: the archive.** At every outstanding mark, the five components'
archived snapshots jointly satisfy layers 1 and 2; the archived repr triple
is a valid sparse-set state (which is how the aggregate's `restore`
discharges `SparseSet::restore`'s snapshot-wellformedness precondition);
and archived pool lengths are monotone and bounded by the live pool.

What `wf` does NOT state, by design: congruence and the hash-cons (there is
no hash-cons in the class layer; that is EGraph state, and its invariant is
W7, rebuild's theorem); freshness of use-list entries under merges (stage
3's `wf_except(dirty)`); the meaning of pool cells (caller data); and rank
values (unread heuristic). The one-line summary: `wf` says the five
structures are each internally valid and tell one consistent story about
the partition, and every archived snapshot tells the same kind of story; it
says nothing about terms. The semantic layer, which nodes are congruent and
which entries are stale, starts at stage 3.

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

**Status 2026-08-13 (branch egraph-wf).** Stages 0 through 2 are done.
Stage 0: debug monitors on W2/W3/W6 in production's classes.rs (landed
before this branch froze production; every later change is confined to
containers-verus). Stage 1: containers-verus/src/union_find.rs, W1 as the
ghost root map plus a strictly-decreasing path measure; find compresses by
path halving; the public surface is total. Stage 2:
containers-verus/src/eclasses.rs, the verified aggregate with W1-W6 as its
wf: ClassData with its Tagged laws, eg_model_wf over the five components'
views (pool cell view included), add_singleton, merge and merge_directed
(splice_absorb's distinct-rings precondition is discharged from W2+W3
inside merge_with - the WITNESS-PENDING argument as a theorem), add_use,
splice_uses, the min-monomial pool family, set_atomic, verified ring and
use-list iterators, and Phase-7 mark/restore whose joint archive also
discharges SparseSet::restore's snapshot-wellformedness precondition.
Behavioral and misuse tests in tests/eclasses_behavior.rs.
THE SWAP IS DONE: egraph/src/classes.rs is now an adapter over the verified
aggregate. The adapter adds only the proof forest (merge_justified/explain:
the same two semi-persistent columns and re-rooting algorithm as before,
verbatim), keeps production's signatures and pinned panic messages, and
retires the stage-0 debug monitor - what it asserted per merge, the
verifier now rejects at build time. Node caches and the routing table are
untouched. Layout is compile-time asserted unchanged (12-byte ring cell,
12-byte class slot at 31-bit ids); the kernel's find was aligned to
production's two-pass full compression and its rank maintenance to the
height-bound rule after the first benchmark comparison showed the halving
variant 3-5% slower on merge-heavy saturation. Final numbers
(saturate_bench, criterion save-baseline/baseline protocol per its module
doc, two comparison runs): plain7 -1.0 to -1.7%, ac6/ac10 +0.8 to +1.6%,
completion rows within +/-0.6% - inside the +/-3% environmental band
BASELINE.md documents for this machine class, with both signs represented.
The full egraph suite (917 tests: saturation, congruence proofs, restore)
passes unchanged. The crate
verifies clean with the aggregate included; the partial-api gate is
unchanged at 35 (every new public fn is total). The public allowlist
entries for splice_absorb and SparseSet::restore remain: they guard
EXTERNAL callers of the components; inside the aggregate both preconditions
are proof obligations, discharged. Consumer migration (egraph's EClasses
onto this kernel) is deliberately out of scope here - production is frozen
by the goal - and follows the container-migration pattern when scheduled.

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
