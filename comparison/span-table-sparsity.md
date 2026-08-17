<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# The span table is dense over a key space the data does not fill

This document measures the `O(num_keys)` term in the per-round index build,
prices three ways of removing it, and states the design the verified landing
should take. It also retracts one cost claim in
`containers-verus/doc/design/16-layered-span-map.md` §4 and drafts the
correction; the correction is not applied here.

It is not a status page. The measurement harness is
`comparison/run-span-table.py` and the per-phase accounting it reads is
`egraph/src/phase_timing.rs`, both landed with this document.

**Landed.** Section 11 records the verified landing and its numbers, and
supersedes section 3's prototype measurements. The two alternative span tables
were unverified prototypes in `egraph/src/span_proto.rs` under `--features
span-proto-sorted` and `--features span-proto-reuse`; they were measurement
instruments, neither was the landing, and both are now deleted. Sections 1
through 10 are the diagnosis that chose the design and are left as they were
written.

All numbers are on an Apple M4 Pro (14 cores), macOS 26.6.1, release profile
(`lto = "fat"`, `codegen-units = 1`), at commit e2ccf05 plus this document's
changes. Wall times are the minimum of five timed runs after one warmup, the
same statistic `run-semipersistence.py` reports and the same registered
divergence from `methodology.md` §2.

## 1. What an E6 round costs, by phase

The E6 semi-persistence cycle at S = 1e6
(`comparison/semi-persistence/sp-t100000.cycles.native.egg`, 20 cycles of
`push; 10 terms; 2 unions; run 1; check; pop`) runs 23 saturation rounds: three
for the base program's `(run 10)` and one per cycle. Per round, from
`EGRAPH_PHASE=1`:

| phase | ms/round |
|---|---|
| rebuild | 1.97 |
| index build (full) | **65.38** |
| - walk that writes the four streams | 14.58 |
| - span build, `by_op` | 4.87 |
| - span build, `by_repr` | 15.52 |
| - span build, `by_child_pos` | 20.24 |
| - span build, `by_contains` | 0.00 |
| - fan-out measurement | 8.19 |
| matching and rule application | **113.61** |

The index build is 36% of the round, and 40.6 of its 65.4 ms is the container's
two-pass counting build. The walk that produces the streams those builds consume
is 14.6 ms, so the build costs 2.8x what producing its input costs.

## 2. The term, and why it is there

`DenseSpanMap::build` allocates and fills four arrays of length `num_keys`: a
`counts: Vec<usize>`, an `offsets: Vec<usize>`, a `cursor: Vec<usize>` and the
final `spans: Vec<Span>` at 16 bytes each. That is 40 bytes per key written in
four separate loops, whatever the stream carries. The value-proportional work is
two passes over the stream.

`by_child_pos` at S = 1e6, per round: 1,925,698 keys addressing 787,960 values,
of which 688,935 keys are occupied. The composite key is
`pos * node_bound + class` (`egraph/doc/design/06-index.md` §6), so the key space
is the node bound times the deepest position in use, while the occupied keys are
the distinct `(position, class)` pairs that actually appear. 2.80 keys of span
table per occupied key, 2.44 per value. `by_repr` is keyed by class
representative and so sized at the node bound, 1,001,932 keys for the same
787,960 values.

Multiply out: 77 MB of arrays allocated, written and freed per round for
`by_child_pos` alone, to address a 3.2 MB pool. The 20.24 ms is 3.8 GB/s of
memory traffic, which is what that costs.

The term is worse on a delta index, where the stream is small and the key space
is not. Section 3 measures it.

## 3. The delta install, measured

The E6 cycle as generated never builds a delta index. Each cycle runs `(run 1)`,
`saturate_semi_spec` runs its round 0 naive by construction (`let delta = if i ==
0 { None }`), and the loop ends there: over the 20 cycles, `EGRAPH_PHASE`
counts 23 rounds and 2 delta builds, both belonging to the base program's
`(run 10)`. Semi-naive evaluation is not exercised by the E6 cycle at all.

To price a delta install on a small delta, this document uses a two-round
variant, `(run 1)` rewritten to `(run 2)` in the cycle bodies only:

```
sed 's/^(run 1)$/(run 2)/' sp-t100000.cycles.native.egg > /tmp/sp-t100000.cycles2.native.egg
```

Under semi-naive that gives 20 delta rounds whose delta is one cycle's
production: 46 touched nodes and 23 `by_child_pos` entries, against a key bound
of 1,002,009. The second round of each cycle, mean of the 20, from
`EGRAPH_PHASE=rounds`:

| phase of the delta round | ms |
|---|---|
| index build (full, rebuilt from scratch) | 66.54 |
| **delta install** | **19.57** |
| - sort and deduplicate the touched log | 0.001 |
| - walk that writes the four streams | 0.003 |
| - span build, `by_op` | 0.004 |
| - span build, `by_repr` | 9.793 |
| - span build, `by_child_pos` | 8.573 |
| matching and rule application | 0.071 |

The install costs 19.57 ms to make 23 values addressable, and the round it feeds
spends 0.071 ms matching against them: the install is 276x the work it enables.
Inside the install, the walk over the 46 touched nodes costs 3 microseconds and
the two span tables over their key space cost 18.37 ms, a factor of 6,100. Both
are dense over the full index's key space, because the delta is built at the same
node bound as the full index it refines.

That is the term this document exists to remove, and it is the claim
`16-layered-span-map.md` §4 omits (section 6).

## 4. Three span tables, measured

Same program, same 23 rounds, three builds of the same binary.

**Dense** is the verified `DenseSpanMap`, unchanged.

**Sorted** derives spans from run boundaries: pack each `(key, value)` into one
`u64`, LSD radix sort by key in 11-bit digits, then one scan for the runs. The
span table becomes a list of occupied keys plus their run starts, and a probe
becomes a binary search over that list. Nothing is proportional to the key space.

**Reuse** keeps the dense key indexing and the `O(1)` probe, and removes the
`O(num_keys)` term a different way: the span table is a buffer recycled across
rounds, each entry carries the build that wrote it, and a build touches only the
keys its stream mentions. A key whose stamp is not the current build's reads as
empty, so a build starts by incrementing a counter instead of zeroing the table;
the offsets are assigned by one pass over the occupied-key list rather than by a
prefix sum over the key space; and no array is allocated or freed per round.

| ms/round | dense | sorted | reuse |
|---|---|---|---|
| walk | 14.58 | 14.53 | 16.01 |
| span build, `by_op` | 4.87 | 7.92 | 4.21 |
| span build, `by_repr` | 15.52 | 9.94 | 4.33 |
| span build, `by_child_pos` | 20.24 | 7.39 | 4.09 |
| fan-out measurement | 8.19 | 6.66 | 7.24 |
| **index build** | **65.38** | **46.95** | **36.47** |
| **matching and application** | **113.61** | **149.07** | **111.75** |
| process wall (ms), instrumented | 4 491 | 4 855 | 3 755 |

**Sorted is rejected: the probe costs more than the build saves.** It takes
18.4 ms off the index build and puts 35.5 ms onto matching, for a net 8% loss on
wall time, and it loses on every corpus program above 100 ms (section 5). The
trade is the one the design predicted and the direction is now measured rather
than argued: a leapfrog join probes far more often than the index is built, so
`O(log D)` per probe is the wrong side of the exchange. Revisit only if a
workload is measured whose rounds are index-build-bound rather than
matching-bound. Section 5's table already contains one: on the two-round variant
under semi-naive, sorted beats dense at 0.93, because a delta round spends
0.07 ms matching against an index that cost 19.6 ms to install. That is the
condition, and it is narrow.

**Reuse is accepted: 28.9 ms off the index build, nothing onto the probe.** The
three span builds fall from 40.6 to 12.6 ms and matching is unchanged within
noise. The residual 16.0 ms walk and 7.2 ms fan-out pass are proportional to
nodes and to occupied keys, not to the key space.

The walk is 1.4 ms slower under reuse than under dense on identical code. It is
not attributed: the two builds differ in allocator behaviour (dense allocates and
frees 77 MB per round, reuse allocates none), and 1.4 ms is inside the
round-to-round spread of the walk.

The delta install, on the two-round variant:

| ms, mean of the 20 delta rounds | dense | reuse |
|---|---|---|
| delta install | 19.57 | **0.010** |
| index build (full) in the same round | 66.54 | 33.24 |
| matching in the same round | 0.071 | 0.055 |

A factor of 1,960 on the install, because its cost is now proportional to the 23
values the delta carries and not to the 1,002,009 keys they could have carried.

## 5. Wall time, corpus and E6

Both prototypes are byte-identical to the dense build on the comparison corpus
and on the E6 programs, under naive and semi-naive evaluation: same stdout, same
`nodes`, `classes`, `iterations`, `match_steps`, `saturated`, `goal_met` on every
program (`run-span-table.py --corpus --semi`). The full test suite passes under
all three configurations, which includes the debug assertion that every bucket is
strictly ascending in node id.

Wall time, minimum of five, as a ratio to the dense build:

| program | dense (ms) | sorted | reuse |
|---|---|---|---|
| `math-microbenchmark.native` | 463.4 | 1.05 | 0.99 |
| `math-microbenchmark.rules` | 520.0 | 1.04 | 1.00 |
| `sp-t8900.cycles.native` | 305.2 | 1.04 | **0.86** |
| `sp-t8900.base.native` | 65.6 | 1.06 | 0.94 |
| `sp-t100000.base.native` | 767.9 | 1.09 | 0.93 |
| `sp-t100000.cycles.native` | 4 396.9 | 1.09 | **0.85** |
| `sp-t100000.cycles2.native`, semi-naive | 6 031.0 | 0.93 | **0.72** |

Programs below 20 ms are all within noise of each other and are omitted; the
full listing is what `run-span-table.py --wall` prints.

`math-microbenchmark` gains 1% where the E6 programs gain 14-15%, for two
reasons that compound.

Its rounds are matching-bound. The index build is 2.76 ms of a 40.8 ms round,
6.8%, against the E6 cycle's 65.4 of 181.0, 36%. The span builds fall by the same
factor on both workloads (`by_child_pos` 0.709 to 0.250 ms per round on
`math-microbenchmark`, 20.24 to 4.09 on E6), so the same 2.8x is worth 1.9% of
one run and 16% of the other.

Its key space is also better filled. Occupancy is comparable, 38.7% against
35.8%, but keys per *value* is 1.00 against 2.44: the key space is twice the
node bound on both, and `math-microbenchmark` files 2.00 `by_child_pos` values
per indexed node where E6 files 0.81, because 401,000 of E6's 976,000 indexed
nodes are interned `i64` literals with no children. Sparsity is a property of
the workload, not of the container, and this is what predicts the size of the
win.

Per-cycle cost at S = 1e6, `(cycles − base) / 20`:

| | naive | semi-naive |
|---|---|---|
| dense, `(run 1)` | 181.45 | 184.68 |
| reuse, `(run 1)` | 152.01 | 152.45 |
| dense, `(run 2)` | 362.77 | 263.69 |
| reuse, `(run 2)` | 296.60 | 183.17 |

## 6. Does semi-naive un-invert?

There is no inversion at this commit, and there was never one for the delta
index build to have caused.

`semi-persistence.md` §5 reports 366.14 ms per cycle naive against 390.94
semi-naive at S = 1e6. Those numbers were measured at dd20d36, three commits
before the index families moved onto `DenseSpanMap` (5f64e48) and two before
restore stopped rebuilding the hashcons index (a8a4187). At e2ccf05 the same
cycle costs 181.45 ms naive and 184.68 semi-naive: the round is 2.0x cheaper and
the difference is 3.2 ms, 1.8%.

The 3.2 ms is not the delta index. As section 3 establishes, an E6 cycle builds
no delta index: `(run 1)` executes only round 0, which `saturate_semi_spec` runs
naive. Naive and semi-naive execute the same rounds over the same indices, and
the per-cycle difference is what two subtractions of ~4.4 s wall times can
resolve, which is a few milliseconds. Under reuse the same difference is 0.4 ms.

On a cycle that does reach a delta round, semi-naive wins and the fix widens the
margin: at `(run 2)` semi-naive is 0.727 of naive on the dense build and 0.618
on the recycled build, 99 and 113 ms per cycle respectively. `math-microbenchmark`
runs 10 delta rounds and semi-naive is faster there too, 435.4 ms against 463.4
on the dense build and 418.8 against 458.7 on the recycled one.

**§5's semi-naive column should not be cited.** The correction belongs in
`semi-persistence.md`, re-measured at the current commit; this document does not
apply it, because the whole §5 table needs re-running on both engines and that is
a separate measurement.

## 7. The design for the verified landing

The landing is a second build path on `DenseSpanMap`, not a new sibling
container. `SortedSpanMap` is what candidate 1 would have needed and candidate 1
lost on measurement.

**A caller-owned span arena, threaded through the round loop.** The recycled
buffer must outlive the map built into it and be handed back when the map is
dropped, and both must be visible to the verifier. The prototype uses a
thread-local free list, which is a stand-in and must not land. The landing owns
the arena in `IndexScratch`, which is already the round loop's home for
per-family scratch, and takes it by value:

```rust
pub struct SpanArena { spans: Vec<Span>, occ: Vec<usize>, stamp: usize }
impl<V: Copy + Default> DenseSpanMap<V> {
    pub fn build_in(arena: SpanArena, stream: &[(usize, V)], num_keys: usize) -> Self;
    pub fn recycle(self) -> SpanArena;
}
```

A round has a full and a delta map of each family alive at once, so
`IndexScratch` holds eight arenas.

**`Span` gains the stamp, and `wf()` moves the tiling onto the occupancy order.**
Today `wf()` is `spans_tile(spans@, pool.len())`: the spans partition `[0, total)`
in key order. A build that writes only the occupied keys cannot maintain that,
because an unoccupied key's entry holds whatever the previous build left there.
The replacement keeps the same predicate and applies it to the permuted
sequence:

```
wf() ==
    spans_tile(occ@.map_values(|k| spans@[k]), pool@.len())
 && occ@ has no duplicates
 && forall|k| 0 <= k < spans@.len() ==> (spans@[k].stamp == stamp@ <==> occ@.contains(k))
```

`lemma_spans_monotone` and `lemma_spans_disjoint` apply verbatim to the permuted
sequence, so the no-wrong-slice-reads property is derived from the same two
lemmas and no pairwise-quantified clause enters `wf()`. That matters: playbook §9
records the pairwise phrasing at 223,553 ms in `list::splice_raw`, and
`15-dense-span-map.md` §4 chose the single-variable form from that measurement.
Injectivity of `occ@` is the new obligation, and the build establishes it from
the same test that appends to `occ`: a key is appended exactly when its stamp is
not yet current, and appending sets the stamp.

`get(k)` gains one branch: a key whose stamp is not current returns the empty
slice. Its in-bounds obligation comes from the permuted tiling through
`occ@.contains(k)`.

**`refines()` is unchanged, and the pool order changes.** Key `k`'s slice is
still the stream's order-preserving filter down to `k`. What changes is the order
of keys within the pool: extents are assigned in first-occurrence order rather
than key order. `refines()` does not constrain that, and `lemma_view_sorted`
carries the stream's ascending node ids into each bucket exactly as before, which
the debug assertion in `index.rs` confirms on the whole corpus.

**Stamp wraparound is an obligation, not an assumption.** The stamp is a counter
per arena. On wrap it must re-stamp the whole table once, `O(num_keys)` every
`2^w` builds, and the zero stamp must be reserved for a never-written entry. A
`usize` stamp makes the wrap path unreachable in practice but it must still be
written and proved, because "unreachable in practice" is not a postcondition.

**Width is an open decision with a memory consequence.** The prototype uses
`{off: u32, len: u32, stamp: u32}`, 12 bytes, which fits the 31-bit id family and
not the 63-bit one. A `usize` triple is 24 bytes and holds 46 MB resident for
`by_child_pos` at S = 1e6, against the 77 MB the dense build allocates and frees
every round. The arena is resident where the dense build's arrays were transient,
so peak memory does not rise and resident steady-state does; measure both before
choosing, on the largest corpus program.

**`LayeredSpanMap::replace_delta` takes an arena too.** It builds the delta
generation with `DenseSpanMap::build` and so pays the full `num_keys` term per
install, which is the 19.6 ms of section 3. Its contract is unaffected: the
change is which build path fills the delta generation.

**What is left after this lands.** The index build falls from 65.4 to 36.5 ms per
round at S = 1e6, of which 16.0 ms is the walk that writes the streams
(proportional to nodes and total arity), 12.6 ms is the span builds (proportional
to values and occupied keys) and 7.2 ms is the fan-out measurement (proportional
to occupied keys). The next term is not in the container: a semi-naive delta
round still rebuilds the entire full index from scratch, 66.5 ms in section 3's
table, which is what `LayeredSpanMap` exists to remove and what its own §1 states
the number for.

## 8. Correction to `16-layered-span-map.md` §4, drafted

Not applied here. The paragraph to correct is "**What this costs per round,
stated honestly.**" in §4, which reads "Installing a generation is O(delta +
invalid): the base is not read." Proposed insertion immediately after that
paragraph:

> **Correction, 2026-08-16: the cost above omits the span-table term.**
> Installing a generation is O(delta + invalid + num_keys), not O(delta +
> invalid). `replace_delta` builds the delta generation with
> `DenseSpanMap::build`, whose span table is dense over the whole key space: a
> build writes `num_keys` counts, `num_keys` offsets, `num_keys` cursors and
> `num_keys` spans however few values the stream carries. On the E6 two-round
> cycle at S = 1e6 the delta carries 46 touched nodes and 23 `by_child_pos`
> entries against a key bound of 1,002,009, and the install costs 19.6 ms
> against 0.07 ms of matching in the round it feeds
> (`comparison/span-table-sparsity.md` §3). The omitted term is three orders of
> magnitude larger than the one that was stated, so the sentence "installing a
> generation is O(delta + invalid)" must not be cited. The remedy is a build
> path proportional to the occupied keys, measured at 0.010 ms for the same
> install; §7 of that document states the container change it needs.

`15-dense-span-map.md` §1 describes the two-pass counting build without a cost
claim, so it needs no correction. `16-layered-span-map.md` §5, "In-place refresh
of one `DenseSpanMap`, rejected", also stands: it rejects mutating a built map,
which is not what §7 proposes. Rebuilding into a recycled buffer keeps the
build-once contract and changes only where the span table's memory comes from.

## 9. Reproducing

From the workspace root, build the three binaries:

```
cargo build --release -p semi-persistent-egraph --bin semi-persistent \
    --features phase-timing                     # dense, instrumented
cargo build --release -p semi-persistent-egraph --bin semi-persistent \
    --features phase-timing,span-proto-reuse
cargo build --release -p semi-persistent-egraph --bin semi-persistent \
    --features phase-timing,span-proto-sorted
```

Copy each `target/release/semi-persistent` aside between builds, then:

```
cd comparison
python3 run-span-table.py --corpus --semi --bin dense=... --bin reuse=...
python3 run-span-table.py --phases --prog "$PWD/semi-persistence/sp-t100000.cycles.native.egg" \
    --bin dense=... --bin reuse=... --bin sorted=...
python3 run-span-table.py --wall --runs 5 --bin dense=... --bin reuse=... --bin sorted=...
```

`--detail rounds` gives one line per saturation round instead of the totals,
which is what section 3's table reads. Wall-time comparisons use binaries built
*without* `phase-timing`, since the feature adds a clock read per timed phase.

The two-round variant is generated by the `sed` in section 3 and is not
committed: it is 100,337 lines of generated program that differs from the
committed one at 20 lines.

## 10. How the prototypes are left, and what the default path pays

The two alternatives are a cfg-gated module, `egraph/src/span_proto.rs`, rather
than a patch file in this directory. A patch would go stale on the first commit
that touches `index.rs`: it has to reach `build_family`, `measure_fanouts`,
`debug_assert_id_sorted`, the four field types of `IndexStore` and the four
accessors. The prototypes are the instrument that decides the container design,
so they have to stay runnable until that design is verified and landed.

The default path pays the indirection: `IndexStore`'s four families are typed
`span_proto::Family<Cfg::G>`, which is `DenseSpanMap<Cfg::G>` when no prototype
feature is on, and the accessors and the fan-out pass go through `span_proto`'s
inline free functions. Measured against an untouched e2ccf05 binary, the corpus
is byte-identical and wall time is inside the noise on every program:
`math-microbenchmark.native` 459.1 to 461.3 ms, `sp-t8900.cycles.native` 301.8 to
304.4, `math-add-ac.rules` 10.3 to 10.3.

**Delete condition.** When the container change of §7 lands, `span_proto.rs` and
both prototypes go, and `index.rs` names `DenseSpanMap` directly again.
`phase_timing.rs` and `run-span-table.py` stay: the phase split is what turned a
25 ms discrepancy that did not exist into a 19.6 ms install that did.

## 11. Landed as: the verified stamped-reuse build path

The design of §7 is verified in `containers-verus` as `DenseSpanMap::build_in`
over a caller-owned `SpanArena` (commit 3779a56, whole-crate verification 1698
to 1716 conditions, 0 errors), and the e-graph builds through it. This section
records what that measured. It supersedes §3's prototype numbers: those were an
unverified instrument and are kept only as the prediction this checks.

`span_proto.rs` and both `span-proto-*` features are deleted, satisfying §10's
delete condition. `index.rs` names `DenseSpanMap` directly again.
`phase_timing.rs` and `run-span-table.py` stay, and `run-span-table.py` gains
`--extra`, which passes an engine flag through to every program so the corpus
comparison covers the scheduling modes as well as the two strategies.

**Where the arenas live.** `IndexScratch` holds eight of them, four for the full
index and four for the round's delta, because semi-naive keeps both stores alive
at once and a family's key space is stable across rounds. `IndexStore::build_from`
takes them and `IndexStore::recycle_into` gives them back. The scratch moved out
of the saturation call and into the `Interpreter`: `(run 1)` is a single round,
and the E6 cycle is twenty of them over one base, so a scratch allocated per call
would be dropped before it was ever reused. Reuse across calls needs no
invalidation from the caller, including across `(push)` and `(pop)`: a build
bumps the generation stamp and writes only the keys its own stream carries, so
whatever an earlier call left in the table reads as empty. That is the property
`build_in` states in its ensures, and `egraph/tests/index_arena_reuse.rs` checks
the consumer gets it, on a second build whose key space is smaller than the
first's so the stale keys are in range.

### 11.1 E6 cycle, per round, by phase

Milliseconds per round, 23 rounds per run, one run per column. Before is 3779a56
with the dense build; after is this change.

| phase | 1e4 before | 1e4 after | 1e5 before | 1e5 after | 1e6 before | 1e6 after |
|---|---|---|---|---|---|---|
| index.full | 0.435 | **0.336** | 4.427 | **2.877** | 57.613 | **32.644** |
| walk | 0.132 | 0.114 | 1.154 | 1.022 | 14.450 | 12.105 |
| span.by_op | 0.040 | 0.039 | 0.347 | 0.344 | 4.824 | 3.715 |
| span.by_repr | 0.070 | 0.038 | 0.633 | 0.340 | 13.101 | 4.251 |
| span.by_child_pos | 0.097 | 0.036 | 1.483 | 0.343 | 16.465 | 3.561 |
| fanouts | 0.084 | 0.091 | 0.701 | 0.687 | 7.602 | 7.685 |
| match+apply | 0.669 | 0.696 | 7.104 | 7.617 | 111.231 | 116.934 |

The span builds carry the change: `by_child_pos` at 1e6 goes 16.465 to 3.561 ms,
`by_repr` 13.101 to 4.251, and the index build as a whole 57.613 to 32.644, which
is 0.57 of what it was. §3 predicted 65.4 to 36.5 from the prototype; the
verified path lands at the same ratio on a base that three cheap rounds pull
down.

**The fan-out pass does not improve, because it cannot yet.** It reads every key
of `by_child_pos`, `by_contains` and `by_repr` to find the occupied ones, which
is the `O(num_keys)` scan this change removes everywhere else. The verified map
holds its occupied-key list, and the build maintains it, but the list is
`pub(crate)`: there is no exported iterator, so `index.rs` scans the key space
instead. At 1e6 that is 7.685 ms of a 32.644 ms index build, and it is now the
largest single term in it. Exporting the occupancy list is the next reduction,
and it is a container change, not an e-graph one.

**Matching costs 5% more, measured, and the net is still favorable.** Three
repeated runs at 1e5 give 7.056, 7.127 and 7.244 ms per round before against
7.427, 7.498 and 7.567 after, so the increase is reproducible and not run
variance. The cause is on the probe path: a stamped span is 24 bytes against the
old 16, so the span table a probe reads is 1.5 times wider, and `get` compares
the stamp before returning the slice. The round total still falls, from 11.53 to
10.37 ms at 1e5, because the index build gives up more than the probes take
back. A workload whose rounds are dominated by probing rather than by building
would come out the other way; that is a measurement, not an inference, and
`--wall` on the corpus is how to take it.

### 11.2 End-to-end wall

Minimum of five timed runs after two warmups, binaries built without
`phase-timing`.

| program | before (ms) | after (ms) | ratio |
|---|---|---|---|
| sp-t880.cycles.native | 32.6 | 30.1 | 0.92 |
| sp-t8900.cycles.native | 293.0 | 262.3 | 0.89 |
| sp-t100000.cycles.native | 4 090.6 | 3 635.0 | 0.89 |
| math-microbenchmark.native | 458.1 | 454.2 | 0.99 |
| math-microbenchmark.native, semi | 430.9 | 428.5 | 0.99 |
| math-microbenchmark.rules | 517.3 | 516.3 | 1.00 |
| math-microbenchmark.rules, semi | 542.5 | 540.5 | 1.00 |

Batch saturation is unchanged, which is what §3 predicted and for the reason it
gave: `math-microbenchmark` more than doubles its node count every round, so
every round rebuilds a key space it has never seen and there is nothing to reuse.
The reuse pays where a round's key space repeats, which is the incremental cycle.

### 11.3 The delta build

The two-round variant of §3, `(run 1)` rewritten to `(run 2)` in the cycle bodies
only, under semi-naive at S = 1e6. 22 rounds build a delta.

| phase | before (ms/round) | after (ms/round) |
|---|---|---|
| index.delta | 12.751 | **1.375** |
| delta.walk | 0.170 | 0.168 |
| delta.span.by_repr | 5.673 | **0.226** |
| delta.span.by_child_pos | 5.343 | **0.189** |

This is the headline the sparsity has been costing all along. A delta round files
9 100 values into a key space of 1.02 M keys, and the dense build charged 11.0 ms
per round to make them addressable against 0.168 ms to walk them. The stamped
build charges 0.415 ms, which is 0.038 of what it was. End-to-end the two-round
variant goes 5 633.9 to 4 281.3 ms, 0.76.

### 11.4 Memory

Peak resident set size, `/usr/bin/time -l`, S = 1e6 E6 cycle:

| | before | after |
|---|---|---|
| peak RSS | 1 047.3 MiB | **608.2 MiB** |
| system time | 0.43 s | **0.07 s** |

The 24-byte stamped span was expected to cost memory and does not: it saves 42%.
The dense build allocated a fresh span table per family per round and freed it at
the end of the round, so the peak held a table being built alongside the one
still being read, and the allocator faulted in tens of megabytes 23 times. The
arena holds one table per family for the whole run and never reallocates it in
the steady state, which `arena_capacity_is_retained_across_rounds` asserts. The
system time falls with it, from 0.43 s to 0.07 s, which is the page faulting that
is no longer happening. At S = 1e5 the same comparison is 79.3 and 83.5 MiB
before against 70.8 and 69.2 after.

### 11.5 Conditions checked

The corpus is byte-identical on 26 programs against the 3779a56 binary, under
both strategies and under each of the default scheduling, `--runtime-scheduling`
and `--sampled-selectivity`, comparing stdout and the run-invariant statistics
`nodes`, `classes`, `iterations`, `match_steps`, `saturated` and `goal_met`:

```
python3 run-span-table.py --corpus --semi \
    --bin before=/tmp/sp-before --bin after=/tmp/sp-after
python3 run-span-table.py --corpus --semi --extra=--runtime-scheduling ...
python3 run-span-table.py --corpus --semi --extra=--sampled-selectivity ...
```

102 test binaries pass, including the anti-unification differential, the egg
fixtures, the AC completion conditions, and the hub, heterogeneous, runtime
scheduling and sampled selectivity comparisons. `cargo clippy --workspace
--all-targets -- -D warnings` and `cargo fmt --all` are clean.
