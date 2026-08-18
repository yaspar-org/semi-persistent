<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Full parity matrix: every drop-in replacement, type by type

Method-by-method comparison of every verified container against its
production counterpart, recording each place where control-flow conditions,
algorithms, or data-structure layout differ, plus the production-vs-verus
benchmark evidence per pair. Compiled from independent side-by-side
readings of both crates (four readers, one per area, findings verified
against the definitions). The class layer's own assessment is
`12-egraph-class-layer-parity.md`; this document covers the container
tier and aggregates the benchmark ledger.

Baseline conventions, stated once: spec/proof code erases at runtime and
is not a divergence; `try_`-prefixed total wrappers and refuse-with-message
guards replacing implicit panics with IDENTICAL conditions are the
total-API design, flagged only where the condition, order, or message
differs; visibility flips (partial cores now `pub(crate)`) are the
allowlist-driven surface and listed once per type.

## Benchmark ledger (prod vs verus, this machine, 2026-08-14)

| pair | benchmark | prod | verus | delta |
|---|---|---|---|---|
| Vec (VecP) | vec/mark_set_restore | 522 µs | 562 µs | +7.6% (recorded, gated) |
| Vec (VecP) | vec/push_pop_untracked | 102 µs | 90.6 µs | −11% |
| Vec | vec/try_extend (gated) | 154 µs | 126 µs | −18.5% |
| Vec | mark_set_restore (gated) | 308 µs | 262 µs | −15.0% |
| Vec | restore_replay (gated) | 310 µs | 322 µs | +3.9%, inside ceiling |
| ListArena | list/append_iter | 304 µs | 242 µs | −20% |
| ListArena | list/splice | 38.6 µs | 35.4 µs | −8% |
| SpMap | map/intern, intern_string, intern_composite | — | — | parity ±1.2% |
| SparseSet | sparse_set/churn | 469 µs | 384 µs | −18% |
| AppendOnlyVec | aov/log | 90.1 µs | 95.4 µs | +5.8% |
| CircularList (vs the retired hand-rolled ring) | class_splice / class_walk / class_merge_restore (gated) | — | — | −20.7% / +0.0% / −20.7% |
| B+ tree | bplus/insert_shuffled | 1.063 ms | 1.209 ms | **+13.7%** |
| B+ tree cursor | bplus/cursor_seek | 562 µs | 592 µs | +5.3% |
| B+ tree | bplus/from_sorted_then_scan | 8.4 µs | 14.7 µs | **+74%** |
| BitSet | bitset/set_test_churn | 24.0 µs | 24.2 µs | +0.7% |
| EClasses/UnionFind | no in-tree production counterpart; end-to-end evidence is the saturate_bench pre/post protocol (criterion save-baseline/baseline, its module doc) | | | −1.7% to +1.6% at the swap |

Open performance items from this ledger: the three B+ tree deltas.
The vec/try_extend gate scare resolved as machine-state contamination
(bisection: no first bad commit, byte-identical body across the range,
mean +0.7% on a quiet machine; 14-parity-audit-2.md section 5); the
row's single-run baseline needs a spread-based re-record. from_sorted_then_scan moved +74% to +86% when the
NodeLayout release guards landed: one guard per leaf_push during the
bulk build and one per cursor key read during the scan, about 50ps per
call, visible only on this microsecond-scale microbench (insert and
seek held). ACCEPTED as the totality price after the second audit
showed the unguarded surface was undefined-behavior-reachable from
safe code; revisit only if a workload is MEASURED to be
from_sorted-heavy, and then via verified-internal unguarded counterparts, not
by reopening the public boundary. The remaining attribution notes:
`from_sorted_then_scan` +74%: the counterpart validates strict ascent in all
builds where production only debug_asserts (one O(n) compare pass per
build), and its balanced-partition leaf fill produces evenly-filled
leaves where production packs full chunks (same leaf count on this
input, different fill). `insert_shuffled` +13.7%: the counterpart recomputes
`last_leaf` by an O(height) descent after every non-append insert
(production updates it O(1) only when the split leaf was last), and
inserts recursively where production uses an iterative path array; per
contra, the counterpart's splits build fresh nodes without production's
per-split heap allocations. `cursor_seek` +5.3%: the counterpart descends from
the root with hand-rolled compare-and-move-conditionally bisection
loops where production calls `partition_point`; the counterpart also lacks
production's current-leaf locality fast path, which this benchmark's
fresh-cursor-per-probe shape cannot fire anyway.

## 1. Vec family (`Vec`/`VecI`/`VecP`, stores, tokens, fork history)

Reader's summary: algorithms are the same design point for point; the
divergences are guard placement, widths, and two total-shell semantic
choices.

### Interesting findings, ranked

1. **`is_valid_token` answers a different question.** Production checks
   `TRACK`, container id, and genealogy but NOT frame liveness: a
   just-consumed token reports valid while `restore` would panic; it can
   also panic inside at the u32 ceilings. The verus form answers
   "restorable now" — adds `frame_idx < frames.len()`, returns false at
   the ceilings, never panics. Different answers on consumed tokens.
   STRICTER-SAFE, and it is what makes `try_restore` total.
2. **Token and id widths.** `VecToken.frame_index` u32 (prod) vs
   `frame_idx: usize` (verus); `ContainerId` u32 vs u64; field order
   differs; 16 vs 24 bytes; verus token lacks `PartialEq`. LAYOUT.
3. **Guard ordering.** Verus checks every restore/mark precondition
   before any mutation and frame-liveness before genealogy; production
   can shrink and prepare-mark before panicking, and reports "abandoned
   future" where verus reports "token points beyond frame stack" for a
   doubly-invalid token. CONTROL-FLOW, message divergences included.
4. **Shrink arithmetic.** Production multiplies `factor * len` plain
   (overflow-capable at extremes); verus saturates, at all three shrink
   sites. ALGORITHM at the extremes only.
5. **Element bound.** Production `Vec<T: Clone>` holds heap types;
   verus requires `T: Copy`. A data-model restriction, load-bearing for
   the stores' repr mechanics.
6. **Restore flag protocol.** Verus hoists a `begin_restore` reset pass
   (ParallelStore whole-bitmap zero; InlineStore sparse tag-clear) that
   production folds into `finish_restore` or skips; ParallelStore
   `pop`/`truncate` retire capture bits production leaves stale. Same
   observable state, different work placement per op.
7. **Iterator regression (verus).** `VecViewIter` lacks `size_hint` and
   `ExactSizeIterator`; production has both. MISSING — worth fixing.
8. **`Default` impls and token `PartialEq` missing on the verus side**;
   `is_empty` reads `store.len()` in production (trap-capable on an
   overflowed store) vs an untrapped emptiness check in verus.
9. **Container-id exhaustion**: verus debug-asserts and optionally
   panics under a feature; production wraps silently (at a 2^32 range vs
   verus's 2^64).

Everything else — push/pop/set/get capture mechanics including the
first-write-wins condition and short-circuit order, prepare_mark's
stratum handling, the backward replay, finish_restore's survivor pass,
fork genealogy walk (same three exits), InlineStore's tag-preservation
guard, TRACK=false erasure — reads EQUAL at the condition level, with
panic-site/message differences only.

## 2. AppendOnlyVec, SpMap, SparseSet

Reader's summary: algorithms equal point for point (including SparseSet's
LIFO recycling positions, bit-for-bit); the divergences are hashing
reproducibility, token semantics, restore atomicity, and API shape.

### Interesting findings, ranked

1. **Hash seeding (SpMap).** Same hash function (foldhash-fast) on both
   sides, but production seeds randomly per process via hashbrown's
   default builder, while verus defaults to DETERMINISTIC seed 0
   (overridable: SP_HASHER_SEED env, set_default_seed with
   seal-on-first-use, with_seed, or the hasher-random-seed feature). The
   table is std's HashMap vs the hashbrown crate — both SwissTable, not
   guaranteed the same probe internals. Unobservable through the map API
   (the index is lookup-only; iteration walks the log); it IS observable
   as cross-process reproducibility, which the verus side chose
   deliberately.
2. **`is_valid_token` semantics again** (AppendOnlyVec, inherited by
   SpMap): production returns true for a just-consumed token whose
   restore would panic; verus answers "restorable now" (frame bound +
   headrooms). Same finding as the vec family's #1.
3. **SparseSet restore atomicity.** Production restores its three columns
   in sequence, each validating its own token — an invalid second token
   panics AFTER the first column rolled back, leaving an observable
   invariant-violating state if caught. Verus prevalidates all three
   tokens before mutating anything. STRICTER-SAFE, and the reason
   `SparseSet::try_restore` is deliberately absent on the verus side
   (the snapshot-wf clause `is_valid_token` cannot answer; production
   HAS a `try_restore` that is an always-Ok panicking stub).
4. **u32 ceilings, off by one.** Production's `narrow_count` permits a
   count of exactly `u32::MAX`; verus refuses at `>= u32::MAX`. The two
   sides diverge only at exactly 2^32-1 frames or forks.
5. **`remove_value`:** production returns `()` and panics when the value
   is absent; verus returns `bool` and never panics. Interface change.
6. **API renames and gaps:** production `Map::get -> &V` is verus
   `get_val` (verus `get` returns the `&(K, V)` pair); no `get_mut`
   anywhere on the verus side (Map or AppendOnlyVec); no `Default`
   impls; verus `Debug` for the map prints entries (shadows included,
   so an overwritten key appears twice) where production prints
   counters.
7. **Stricter capacity on the recycle path:** at `cap == Idx::MAX - 1`
   with a non-empty free pool, production's `add` succeeds (the sparse
   columns don't grow on recycle) where verus `try_add` refuses — its
   three-column headroom check is conservative.
8. **`insert`'s clone destination is swapped** (production clones the
   key into the log, verus into the index) — indistinguishable for
   well-behaved `Clone`.
9. **Verus-only key wrappers** (`CanonicalF64`, `BitsF64`,
   `CanonicalRational` in canonical_keys.rs) exist to make the key-model
   axioms true by construction; production uses foreign key types raw.

Everything else — the three-step liveness test in the same order, add's
recycle/mint mechanics, remove's swap-remove write order, the freed id's
parking slot, mark/restore delegation, index rebuild order after
restore — reads EQUAL at the condition level.

## 3. ListArena, B+ tree, sorted cursor, id/value types

Reader's summary: the ListArena and sorted cursor are the same
algorithms with guard-placement differences; the B+ tree is the one
container whose counterpart diverges algorithmically (recursive insert,
balanced bulk build, no seek locality path); the id layer swaps a
panicking narrowing for a masking one and compensates at call sites.

### Interesting findings, ranked

1. **`DenseId::from_usize` narrows differently.** Production
   range-checks in `usize` then panics out of range; the verus macro
   and the hand-written DenseId31/63 truncate-then-mask
   (`(n as int) & MASK`), so an out-of-range argument silently aliases.
   The counterpart compensates with explicit `try_new` guards at call sites.
   ALGORITHM, and the root of finding 2.
2. **ListArena capacity is `id_bound - 1` in the counterpart, `id_bound` in
   production.** The prepend/append guard is `N::try_new(len + 1)`,
   refusing the final id slot production fills (production's own test
   fills all 128 of a 7-bit arena). Same off-by-one on `try_new_list`.
   The only capacity-boundary divergence found in any container.
   FIXED — the blanket `len + 1 < id_bound` precondition split per id
   family, the same split `UnionFind::try_make_set` already had: a
   bit-stealing id holds its full range (the storage word has a spare
   bit, so the word bound follows from `len < id_bound` alone); only
   the verus-only full-range family (`DenseUsize`, word exactly as
   wide as the id space) still needs the successor representable.
   Applied to the list arena's two push-fits lemmas, five core
   preconditions, two monitored guards, and three total guards, and to
   the ring (`CircularList::add_singleton`), which had the same
   blanket guard and would otherwise have kept the aggregate
   `EClasses` capacity at `id_bound - 1`. Verify 1632/0 in both
   feature configurations. Pinned by
   `bits7_capacity_holds_the_full_id_range` (list arena, prod-vs-verus
   differential) and `bits7_add_singleton_fills_the_full_id_range`
   (aggregate, all component ceilings at once).
3. **`from_sorted` builds a differently-shaped tree.** Production
   packs full leaf chunks (last leaf can hold one key); the counterpart
   balances (`ceil(n/cap)` groups of near-equal size, non-root leaves
   at least half full). Same key set, same leaf count on uniform
   input, different fill. Separator collection and materialization
   also differ (child-0 descents plus per-level heap vectors vs a
   carried `firsts` array, inline conversion). ALGORITHM.
4. **Release-build checking trades places.** Sortedness: the counterpart
   checks strict ascent in all builds and refuses; production only
   debug_asserts, and a release build given unsorted input silently
   builds a wrong tree. Arena exhaustion: production asserts on every
   allocation in release; the counterpart has no runtime check (proved
   unreachable from the bit-stealing bound).
   The all-builds sortedness check is deliberate and stays: the only
   build path with a sortedness `requires` (`bulk_load`) is private,
   so `from_sorted`/`try_from_sorted` are the whole public surface and
   both re-check the erased precondition at runtime — unverified
   callers cannot violate it. The check becomes removable when the
   callers are themselves verified against `bulk_load`'s requires; the
   O(n) cost against the build's O(n log n) is priced in the
   `from_sorted_then_scan` ledger entry above.
5. **Insert control flow.** Production descends iteratively with a
   24-entry path array and propagates splits in an upward loop; the
   counterpart recurses, returning the separator pair. Split points and the
   fast-append condition are EQUAL; split mechanics differ (production
   heap-allocates per split via `to_vec`/scratch vectors, the counterpart
   builds fresh nodes allocation-free); `last_leaf` maintenance is
   production O(1)-conditional vs counterpart O(height)-always on the slow
   path.
6. **The `Branchless` search counterpart is branchy and never dispatched.**
   Production's `Branchless` strategy is genuinely branch-free; the
   counterpart's is a branching linear scan, and the verified tree never
   calls the strategy trait at all — `S` is phantom and every descent
   uses hardwired compare-and-select bisection. Instantiating with
   `Branchless` still binary-searches. ALGORITHM (dispatch), plus a
   misleading type parameter.
7. **Cursor seek locality.** Production tries the current leaf, then
   the linked next leaf, before falling back to a root descent; the
   counterpart always descends from the root. EQUAL `step` protocol.
8. **`Opt::get` name collision.** Production `get() -> Option<T>`;
   verus `get() -> T` refusing on None (production's behavior is the
   counterpart's `to_option`). Same niche encoding on both sides. API hazard
   for anyone porting call sites by name.
9. **Empty-source `splice` writes.** Production early-returns with
   zero writes; the counterpart unconditionally rewrites the source header,
   an extra tracked write observable through diff-log growth and
   `tracking_bytes`.
10. **Sorted cursor: both sides gallop.** The gallop-vs-bisect premise
    was false — production's concrete cursor (pre-swap, in the egraph
    crate) used the identical doubling probe and final bisect. The one
    behavioral difference: the counterpart's trait `step` guards against
    advancing an exhausted cursor (true no-op) where production
    incremented `pos` past the end, unobservably. The unguarded form
    survives as `pub(crate) step_unchecked`.
11. **Nominal-type substitutions, bit-identical:** tuple `Tagged`
    reprs become named structs (`ListNodeRepr`, `BoolTagged`,
    `PairRepr`) because Verus rejects trait impls on tuples; the
    `$Stored` companion newtype is gone (bare backing integer as
    `Repr`); `ListHead` stores the tail as a bare id instead of a raw
    repr word; node structs split value form from repr form with
    identical stored bits and flag constants. `IndexLike` MIN/MAX
    consts become `min()`/`max()` fns, its checked arithmetic moves to
    free functions guarding against the id MAX (u128-widening mul),
    and the u64 impl gains a 64-bit-target gate.
12. **Iterator cost (ListArena).** The counterpart's `ListIter` borrows the
    whole arena and pays a per-call stale-handle bounds refuse plus a
    position increment production's nodes-only iterator does not have.
    Same traversal order and yields.
13. **Missing across sides:** production `Default` for ListArena and
    `MAX_RAW`/`from_raw_unchecked` (test-only) have no counterpart;
    counterpart-only additions are `is_valid_token`, `pos()` on the cursor,
    `contains`/`first_key`/`restores_remaining` on the tree,
    `DenseUsize`, the witness id types, and the white-box test
    oracles. BitSet is EQUAL on every method (documented verbatim
    port, contracts absent by design).

Everything else — geometry constants across all six layouts, NIL
sentinels, leaf and internal split points, separator placement, parent
absorb order, `Opt` niche mechanics, id mask/cap constants and
comparison/hash semantics, the `new` range condition with its message,
IdFactory conditions (messages differ), mark/restore validation
posture (same classes as sections 1 and 2) — reads EQUAL at the
condition level.

## 4. Class layer findings

The audited divergences of the shipped class layer, each with its
classification and resolution. The parity statement itself is
`12-egraph-class-layer-parity.md`; the confirmed-equal surface (the dual
in-struct forest, production's messages on make_set/add_singleton and the
PROOFS refusals, two-pass find, verbatim reroot_proof/explain/walk_to_root,
merge's sequence and the UNOBSERVABLE set_none argument, prefer_a_by_uses,
mark/restore component order, the trust classification) is not repeated
here.

### Findings, ranked

1. **Proof-edge recording order in `merge_justified`.** Production
   records the proof edge inside `uf.union_justified` BEFORE the ring
   splice and repr removal; the kernel records it AFTER `merge_with`
   completes both. The two touch disjoint state, so no caller can
   observe the difference in a completed call, but a panic between
   splice and record leaves a different intermediate state, and
   document 12's "same order"/"verbatim ordering" wording is not
   literally true of the shipped code. UNOBSERVABLE-completed /
   CONTROL-FLOW-mid-panic.
   RESOLVED — the kernel order is kept, deliberately: `merge_with`
   refuses only at its prevalidation boundary before any mutation, its
   verified union-and-splice body has no panic path (every assert is
   static), and `record_proof_edge`'s glue has no explicit panic site
   over the already-validated ids — so no execution can stop between
   the union and the record, and the intermediate state production's
   record-first order protected against is unreachable. Production
   needed record-first because its splice could panic mid-merge; the
   verified core removed that panic, which removes the reason. Same
   work either way, so no cost.
2. **The accepted rank divergence is skip, not saturate.** At
   `rank_ab == 255` the kernel SKIPS the bump (survivor keeps its own
   rank) rather than clamping to 255 as document 12 says; identical
   below 255 either way. On the by-rank path a bump implies equal
   ranks, so skip and clamp coincide; on the forced-survivor path they
   do not (survivor rank stays at e.g. 3 instead of 255). Same
   accepted-divergence verdict, corrected mechanism.
3. **Guard-order inversion in `min_monomial`/`min_monomial_at_row`.**
   Production early-returns `None` on a no-row query BEFORE its
   debug-only column check, so no-row plus out-of-range column returns
   `None` in both build profiles; the kernel checks the column bound
   first and refuses on the same inputs. Also, with a live row,
   production release builds silently read ANOTHER CLASS'S pool cell
   when `col >= min_width` but the flat pool index stays in range —
   the kernel refuses. Stricter-safe, but a caller relying on the
   `None` path changes behavior.
4. **Dropped `Default` impls** on `UnionFind` and `EClasses`
   (production had both; no in-tree caller uses them) — the same gap
   the vec and map families show.
5. **`UnionFind::mark`/`restore` are `pub(crate)` now** (production:
   `pub`); only `try_mark`/`try_restore` are public, and
   `egraph/src/union_find.rs` still documents the token against the
   uncallable pair. In-tree only `EClasses` marks the union-find.
6. **Message divergences on refuse paths document 12 does not list:**
   mark-family ("EClasses::mark: untracked aggregate" and
   per-component texts vs production's asserts/expects), capacity
   exhaustion ("id range exhausted" vs "push: within index word"),
   `set_min_width` (unformatted vs production's formatted width pair).
   Same conditions throughout; the texts differ.
7. **New public surface, superset not break:** `try_add_singleton`,
   `merge_directed_with`, `is_valid_token`/`try_restore` on
   `EClasses`, the `try_` family public on `UnionFind`, `NoJust`.
8. **Token `Debug` differences** (field order, `parent` vs
   `parent_fast`) and **stale kernel module docs** (union_find.rs
   still says "path halving"; eclasses.rs says the kernel "does not
   replace production" — it does). Doc-only; the module comments
   should be fixed.
9. **Panic identity on misuse:** `merge_directed` on a PROOFS instance
   refuses with the PROOFS message before computing
   `prefer_a_by_uses`; production computed it first, so a misuse with
   an out-of-range id could see the other panic. Unobservable for
   correct callers.
