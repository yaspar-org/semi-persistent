<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Parity audit 2: interface, safe use, behavior, algorithms, performance, features

Second full audit of every drop-in replacement against its production
counterpart, run after the first matrix (`13-parity-matrix.md`) and the fixes it
produced (per-family capacity guards, search dispatch through `S`,
branch-free `Branchless`). Five independent auditors, one per dimension;
the algorithmic auditor's brief was adversarial: re-derive the first
audit's EQUAL verdicts from source and try to refute them. Production
class-layer baselines: `git show 'd14fd17^:egraph/src/classes.rs'`,
`git show 'b1f1683^:egraph/src/union_find.rs'`; the retired hand-rolled
ring is at `585d240^`. The class-layer rows are a frozen record of the
swap against those pinned baselines, not a live parity claim about the
tree; the container rows remain checkable against `containers/src`.

## 1. Interface and feature surface

Reader's summary: every prod-instantiable configuration (layout x
search x id family x TRACK/PROOFS) exists on the verus side; the
differences are renames, visibility splits (panicking cores pub(crate),
try_ forms public), richer verus-only surface, and a systematic loss of
derive impls.

### Findings, ranked

1. **Systematic derive losses.** Missing on the verus side, present in
   production: `Debug` on `ShrinkPolicy`, `ForkHistory` (also loses
   `Clone`), `Frame`, `BoolTagged`, `Opt` (prod prints `Some(..)/None`);
   `Default` on `Vec` (both backends), `SpMap`, `AppendOnlyVec`,
   `SparseSet` (ParallelStore variant), `ListArena`, `BPlusTreeSet`,
   `EClasses`, `UnionFind`; `PartialEq/Eq` on `VecToken` and
   `ContainerId` (verus equality only via inherent `eq`). One
   restoration pass over these is mechanical.
2. **Root-surface renames and moves.** `Map` -> `SpMap`, `View` ->
   `VecView`, `ViewIter` -> `VecViewIter`, no compatibility aliases;
   the `BPlusNode*`/`Layout*` names and `ListIter` are root exports in
   production but module-scoped on the verus side; `SparseSetId`
   /`UseListId`/`UseNodeId` move from `containers::id` to the root.
3. **Type-level incompatibilities.** `ListIter` gains a generic
   parameter (`<'a, T, L, N, TRACK>` vs production's four); primitive
   `Tagged::Repr` changes type (`(bool, T)` tuple -> `BoolTagged<T>`);
   B+ node value and repr types split (production nodes are their own
   `Repr`); `SearchKind::find_ge` bound narrows `Copy + Ord` ->
   `IndexLike`; native tuples are not `Tagged` (named `Pair` replaces
   the `(A, B)` impl); `UnionFind` loses both const-generic defaults
   and gains the `J` parameter.
4. **Checked arithmetic moved off the trait.** Production's
   `IndexLike::checked_add/sub/mul/incr/decr/add_usize` are trait
   methods; verus provides free functions in `index_like`, so
   method-call syntax does not port.
5. **Missing compile-time node-size asserts.** Production pins
   `size_of::<Node>() == align` for all six B+ node types at compile
   time; the verus side has the align attr only. Worth restoring: the
   asserts are free and pin the layout contract.
6. **`SparseSet` has `restore` but no `try_restore`** (production has
   both); the verus omission is deliberate pending the snapshot-wf
   archival (total-api-plan.md), recorded here as the one asymmetric
   restore surface.
7. **Feature flags.** Production has none; verus: `hasher-random-seed`
   (production-parity randomized hashing; parity requires ENABLING
   it), `strict-id-exhaustion` (production wraps silently),
   `literal-types` (verus-only key wrappers), `compat-*` (test-only).
   Deterministic-by-default hashing is the one default that changes
   observable cross-process behavior.
8. **Verus-only surface with no production counterpart:** `CircularList`
   family, `SortedVecCursor`, `CaptureBits`, `ContainerError`,
   `guard`, `hasher_spec`, `DenseUsize`/`DenseId31`/`DenseId63`,
   `NoJust`, `contains` on the B+ tree (production has no membership
   test), `try_*` families throughout, white-box test oracles, id
   witnesses. Additions, not breaks.

## 2. Adversarial re-check of the first audit's EQUAL verdicts

Twenty-nine claims re-derived at statement granularity; 23 confirmed, 6
refuted. The confirmations cover the load-bearing hot paths: push
capture re-entry, backward replay, finish_restore survivor pass, fork
genealogy walk (no operand swap at ties), SparseSet's full
recycle/mint/swap-remove/parking protocol, all six B+ layout geometries
recomputed numerically, split points and separator placement, find's
two-pass full compression, union tie-breaking (else-of-`<` is exactly
`>=`), prefer_a_by_uses, mark/restore component order both directions.

### Refutations

1. **Grow-only capture bitmap (performance, hot path).** Production's
   prepare_mark zeroes then resizes the bitmap to the CURRENT length,
   shrinking after a vec shrink; the verus `CaptureBits` is grow-only
   and `zero_all` zeroes every materialized word. After growing to n
   and shrinking to m << n, each mark costs O(n/64) on the verus side
   vs production's O(m/64). Distinguishing workload: grow to 1M, pop
   to 10, mark repeatedly (15,625 words zeroed per mark vs 1). API
   state equal; per-mark cost is not. Candidate fix: zero and
   materialize only up to the needed word count, or truncate on
   prepare_mark.
2. **`try_push` at exact capacity, TRACK=false.** At `I::MAX` stored
   elements production's `try_push` is an unconditional `push;
   Ok(())` that traps later at `len()`; the verus form refuses
   `CapacityExhausted` without pushing. Stricter-safe, observable.
   Related: the verus untracked path is not branch-free (capacity and
   frames checks production does not run), so "TRACK=false erasure is
   zero-cost" is wrong as stated; the checks are O(1) compares.
3. **ParallelStore pop retires capture bits.** Production's pop is a
   bare `data.pop()`; the verus pop clears the popped slot's capture
   bit under TRACK. States reconverge through the public API; the
   exec bodies differ (one load/and/store per tracked pop).
4. **Capture write order.** Production ParallelStore sets the capture
   bit then pushes the diff entry; verus pushes then sets. Production's
   own InlineStore uses push-then-tag, so production is internally
   inconsistent and the verus order matches one of its two. No
   single-threaded distinguishing input.
5. **Absorbed-key clear in `merge_with`** (two readers independently).
   Production preserves the absorbed cell's key bits (`set_none`, with
   a comment relying on the value staying readable through
   `repr_id_unchecked`); the kernel writes `Opt::none()` (value bits
   zero). Already recorded in doc 12 as UNOBSERVABLE (no live
   post-merge reader of the absorbed value bits, re-confirmed); the
   first matrix's "merge sequence EQUAL" wording overstated - the
   sequence is equal, the written payload is not.
6. **Ring same-ring guard, debug builds.** The retired production ring
   spliced with no same-ring check (silently splitting the ring); the
   verus splice walks the ring in debug builds and panics
   ("CircularList::splice: s and a are in the same ring"). Release
   identical; unreachable through the class layer (union returns None
   for same-class arguments first). Also: `iter_class` on an
   out-of-range id refuses at construction where production panicked
   on first `next()`.

## 3. Behavioral parity

Reader's summary: conventions first. Counterpart panics carry the
`containers-verus: ` guard prefix, production `try_*` (where it exists)
is an always-Ok shim around a panicking core while counterpart `try_*` returns
typed `ContainerError` without mutating, and the counterpart's panicking cores
are pub(crate) where production's are pub. Beyond those, the reader
confirmed every previously recorded divergence and found the following.

### Findings, ranked

1. **Production's cursor `seek` is wrong for backward targets.** Its
   fast path answers from the current leaf whenever
   `target <= leaf's last key`, so a backward target below the leaf's
   first key returns the leaf's first key instead of the true global
   position (containers/src/bplus.rs:855-857). The counterpart always
   descends from the root and is correct; `seek_first` on a reused
   cursor hits the same clamp. Concrete case (Layout64U32,
   from_sorted 0..28): `seek(20); seek(3)` answers key 14 in
   production, key 3 in the counterpart. No existing test constructs a
   backward seek on a positioned cursor. PRODUCTION BUG; the correct
   fast-path condition needs the leaf's first key as a lower bound.
2. **Rank 255 boundary: wrap vs skip.** Production's rank bump is
   unsaturated u8 arithmetic: at rank 255 a tie-bump panics in debug
   and WRAPS THE SURVIVOR'S RANK TO 0 in release, after which
   survivor selection diverges observably (returned survivor pair,
   MergeInfo, all subsequent finds). The counterpart skips the bump. Rank
   255 is reachable through 255 chained directed unions. The counterpart's
   behavior is the defensible one; recorded in doc 12/13 as accepted,
   now with the reachability argument.
3. **Capacity-guard verdict at HEAD: parity holds.** The per-family
   guards reduce to exactly `n < id_bound` for every bit-stealing
   family; boundaries 0, id_bound-1, id_bound, and the usize ceilings
   all agree with production (panic vs refuse channel aside).
   Residual: the pub(crate) `new_list` core's runtime guard omits the
   full-range successor clause: unreachable externally, vacuous for
   every shared family.
4. **Ceiling over-admission inverted (Vec/SparseSet).** At an index
   word's ceiling, production admits the element and poisons the
   container (every later len() panics "len overflow"); the counterpart
   refuses up front and stays usable. SparseSet at u8/255: production
   add succeeds then every read panics; counterpart Err(CapacityExhausted).
5. **Restore validation collapsed and reordered.** Production
   distinguishes four restore-failure causes by message and checks
   genealogy before frame bound; the counterpart checks frame bound first
   and try_restore collapses everything to Err(InvalidToken).
   DepthLimit/ForkLimit are never produced by restore; ForkLimit is
   produced by no counterpart code path at all.
6. **Construction-time env dependence (counterpart-only).** SpMap::new reads
   SP_HASHER_SEED once per process, panics on a malformed value, and
   seals the seed; production reads no env. The seed stays
   unobservable through the API on both sides (index is lookup-only,
   iteration is log-ordered).
7. **Message drift table** (same condition, different text): sparse
   set "id not present" vs "is not live"; AOV genealogy and untracked
   texts; per-method attribution on all std-index panics; interpolated
   production texts (set_min_width) vs the counterpart's static refuse
   strings; make_set/PROOFS texts identical modulo the guard prefix.
   The drifts that were pure regressions are FIXED in the parity batch
   (sparse-set texts, both AOV texts, SpMap Debug shape, IdRangeError
   Display); the guard prefix and static-string constraints remain and
   are documented conventions.
8. **Inherent-vs-trait shadowing (counterpart).** SortedVecCursor's inherent
   `key` returns bare K and panics on exhaustion; the SortedCursor
   trait impl returns Option. Callers on the concrete type get the
   panicking form where the trait contract says None.
9. **Debug output**: token field renames/order (frame_idx first,
   parent vs parent_fast, min_pool -> pool after uses), ContainerId
   tuple form, counterpart AOV/SpMap Debug restored to production's counter
   shape in the parity batch.
10. **Determinism confirmed everywhere**: all iteration surfaces are
    index/pointer ordered on both sides; the only survivor-selection
    boundary is rank 255 (finding 2); the hash-seed difference leaks
    only through the counterpart's construction-time parse panic.

## 4. Safe use and soundness

Reader's summary: every public requires-carrying fn classifies as
RECHECKED (runtime guard mirrors the erased requires) or INVARIANT-ONLY
(wf-class requires that unverified code cannot violate: constructors
establish it, mutators preserve it, fields are pub(crate), no Clone, no
&mut leaks), with the exceptions below. 124 guard sites; three unsafe
expression sites in the whole crate, all in bplus_layout, all
external_body pub(crate) with verified bounds at internal call sites
and debug monitors.

### Findings, ranked

1. **The one UB-class hole: the bplus_layout public surface.** The
   node structs export ALL-PUB fields (count, data, is_leaf) and the
   public NodeLayout exec methods plus `internal_insert_at` route
   through the bounds-elided primitives with no release check:
   external safe code forging `count` or passing an out-of-range
   index reaches `get_unchecked` out of bounds: UB in release, panic
   in debug. Production has zero unsafe (misuse panics on checked
   indexing). FIX PLANNED (total-api-plan.md): the requires-carrying
   operations and the node fields go pub(crate); the public trait
   keeps types and consts only.
2. **Release-silent wrong answers, both known and accepted-shared:**
   CircularList::splice's different-rings clause is debug-checked
   only (release: silent ring split; shared with production's ring,
   unreachable through the class layer whose union gates same-class
   first; O(1) witness planned); SortedVecCursor::new/seek and
   SearchKind::find_ge/find_gt trust sortedness (silent wrong index,
   no UB; production identical; conditional-contract conversion
   planned).
3. **Open spec-carrying traits.** IndexLike, DenseId, Tagged,
   NodeLayout, SearchKind, DiffStore, OptElem are publicly
   implementable; a law-breaking foreign impl voids invariants
   (wrong answers, corrupted rollback) without UB: same open-trait
   posture as production, which fails by panic instead. Recorded as
   the trait-law trust item beside the key model.
4. **Masking from_usize: all call sites guarded.** Every
   containers-verus site is dominated by a verified precondition or
   release guard; every non-test egraph site (20+) is guarded
   (try_new mints, range-checked scans, documented capacity
   arguments). The masking semantics stay a hazard only for FUTURE
   unguarded call sites; production's panicking form fails closed.
5. **Production release-mode holes the counterpart closed, confirmed from
   source:** unsorted from_sorted builds a silently wrong tree;
   diff_store restore_entry appends at the wrong index on a violated
   debug_assert (silently corrupted rollback); SparseSet composite
   restore is non-atomic with no cross-component mark check (torn
   state observable under catch_unwind); pre-swap min_monomial
   cross-row pool reads and writes; the Director word-truncation
   family (since hardened in egraph). Production's u32 ContainerId
   also wraps silently at 2^32 constructions, after which foreign
   tokens alias; the counterpart is u64 + debug assert + optional release
   trap.
6. **Token defense is closed.** All token fields pub(crate) both
   crates, no public constructors; every counterpart restore path
   revalidates container id, frame liveness, genealogy, and (for
   aggregates) all-component frame agreement before mutating;
   BPlusToken's header copies are inert. The counterpart's SparseSet is the
   one aggregate without a cross-component same-mark check, defended
   by per-component genealogy plus external unconstructibility.
7. **Miri.** Viable on this crate and adopted as a probe: the misuse
   suite (the guard paths, including the new NodeLayout mirrors) runs
   under `cargo +nightly miri test` clean - 21/21, no undefined
   behavior, 3.9s interpreted. The contract-fuzz suite is impractical
   under interpretation at its native iteration counts and needs an
   env-reduced mode before it can join a scheduled miri job; recorded
   as the follow-up.
8. **Monitor inventory.** Debug-only: layout primitive bounds, ring
   same-ring walk, std-Vec capacity assumption, ContainerId wrap.
   Release-checked: all 124 guards, token validation, from_sorted
   ascent, egraph Director asserts. Silently trusted in release:
   items 1-3 above plus trait laws, key model, seed-seal ordering,
   and the 2^64 ContainerId non-wrap (~584k years at 1M ids/s).

## 5. Performance

Reader's summary: within-run prod/verus ratios are the only comparable
quantity (unchanged code moved 49% in absolute microseconds between
quiet windows); the interleaved perf_gate rows are the confound-free
evidence, and criterion pairs carry a documented arm-order penalty.
Two passes, quiet windows, ratios reproducing within about one point.

### Regressions at HEAD (verus slower than production beyond +3%)

1. **vec/try_extend: RECLASSIFIED, not a regression.** The bisection
   found no first bad commit: the function body is byte-identical
   across the candidate range, no in-range commit touches Cargo.lock,
   and on a genuinely quiet machine the tip measures mean +0.7% over
   six runs - indistinguishable from the row's original +1.6%
   recording - while the ceiling-setting commit itself trips its own
   +9.0% ceiling in 4 of 16 runs under contention. The audit's two
   "quiet sessions" shared contaminated machine state (real-time
   audio threads, and this session's own background miri
   interpreter at 100% CPU); single-run ratios under that state span
   -39% to +64%. Consequences adopted: the row's PROVISIONAL
   single-run baseline needs a spread-based re-record, the ledger's
   absolute columns are non-reproducible (already noted), and every
   sub-10-point delta measured in those sessions (tracked_veci +4-6%,
   the +86% from_sorted magnitude - the guard MECHANISM stands, the
   magnitude needs a controlled re-measure) carries the same caveat.
2. **bplus/from_sorted_then_scan +86% (ledger +74%).** The ~13-point
   worsening is attributed to the NodeLayout release guards: the
   bulk build pays a guard per leaf_push and the scan a guard per
   cursor key read. Mitigation identified: pub(crate) unguarded counterparts
   for VERIFIED internal callers (the cursor and loader prove the
   requires), guards stay on the public boundary.
3. **bplus/insert_shuffled +12.5%** (known, ledgered at +13.7%,
   stable through dispatch + guards).
4. **bplus/insert_shuffled_branchless +6%** (new row; smaller gap
   than the BinarySearch arm).
5. **tracked_veci mark-churn +4-6%**, flat in n, reproduced at three
   sizes twice; no ledger row; near the layout-noise floor but
   consistent.

### Moves in the verus favor and stable rows

map/intern moved 25-33 points to verus-faster (-24.7%/-33.1% vs the
ledger's parity; hasher seeding and dependency drift on the production
arm are the suspected cause - the arms use different table
implementations by design). cursor_seek improved to near parity after
the dispatch commit and the production fast-path fix. The class-ring
rows (-20%), list rows, sparse churn, aov, bitset: stable or
verus-faster. mark_set_restore's criterion arm-order artifact (+8.2%
then -2.9%) resolves to verus-faster on the interleaved gate
(-16 to -36%).

### Coverage gaps (no bench pair exists)

B+ tree TRACK=true mark/restore; SpMap miss-heavy lookup; tracked
ListArena; SortedVecCursor prod-vs-verus A/B; use-list-heavy EClasses
group; Vec iteration pair (relevant to the size_hint restoration); and
NO allocation-parity harness for any container pair - the parity
matrix's claim that the counterpart's splits are allocation-free against
production's per-split to_vec is directly checkable with a counting
allocator and currently is not checked.

### Bench-validity findings

The criterion arm-order confound (~+18% second-arm penalty) applies to
every pair without an interleaved counterpart; cursor_seek's
fresh-cursor-per-probe shape suppresses production's locality fast
path entirely; from_sorted_then_scan conflates the deliberate
all-builds sortedness check with build-shape differences; every verus
arm pays a Result discriminant per op (`try_*().expect()`) - the real
total-API cost, present systematically; the ledger's absolute columns
are not reproducible across machine states and should be re-recorded
ratio-first. incremental_vs_rebuild was skipped (over the time
budget); its one prod-vs-verus pair remains unmeasured at HEAD.
