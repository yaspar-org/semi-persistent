# Chapter 8 — Indexes and Leapfrog Triejoin

[← Ch 7: Rules and Pattern Matching](07-rules-and-pattern-matching.md) · [Table of Contents](00-table-of-contents.md) · [Ch 9: Saturation →](09-saturation.md)

## 8.1 Index Construction

### Why Indices?

Pattern matching in an e-graph is a relational join problem. A pattern
like `(Mul (Num x) (Num y))` asks: "find all Mul nodes whose children
are Num nodes." Answering this efficiently requires sorted indices that
the leapfrog join (§8.2) can seek into.

The indices are derived structures, not semi-persistent, rebuilt
from scratch each saturation iteration. Rebuilding from scratch is deliberate:
merges change canonical representatives, invalidating all index entries.
Let `N` be indexed nodes, `E` child occurrences, `K` occupied keys, `B` the
largest logical key bound requested, and `H` the retained span-table length.
Stream construction is O(N + E). With sufficiently large recycled arenas, the
four stamped builds are O(N + E + K). Growing an arena adds
O(max(0, B - H)); a fresh build therefore includes O(B). Generation-stamp
exhaustion exceptionally clears O(H) entries. The fan-out pass visits occupied
buckets and their entries. The result has sorted buckets with no tombstones or
readable stale entries.

### `IndexStore`

```rust
pub struct IndexStore<Cfg: EGraphConfig> {
    pub by_op: DenseSpanMap<Cfg::G>,
    pub by_repr: DenseSpanMap<Cfg::G>,
    pub by_child_pos: DenseSpanMap<Cfg::G>,
    pub by_contains: DenseSpanMap<Cfg::G>,
    pub child_pos_stride: usize,
    pub repr: Vec<Cfg::G>,   // build-time representative of each node
    pub op: Vec<Cfg::O>,     // build-time operator of each node
    pub fanouts: FanOuts<Cfg::O>,
}
```

Each family is a `DenseSpanMap` from `containers-verus`: one flat pool holding
every value and a span table saying where each key's run starts and how long it
is (`containers-verus/doc/design/15-dense-span-map.md`). Every key is a dense
integer, so a probe is an array index into the span table and a slice of the
pool, not a hash and a pointer chase into a per-key `Vec`. The container's
`refines()` states that key `k`'s slice is the order-preserving filter of the
build stream down to `k`, which is the property that makes the two-pass counting
build substitutable for the per-key push it replaced.

No index family hashes anything. `FanOuts` still uses `FastMap`, a `HashMap` with the `foldhash` hasher, for
per-operator aggregate statistics; this section makes no fixed performance
claim for their hasher.

Four index families, each answering a different query:

| Index | Key | Answers | Example |
|-------|-----|---------|---------|
| `by_op` | `OpId` | "all nodes with this op" | all Add nodes |
| `by_repr` | canonical `G` | "all nodes in this e-class" | all nodes equivalent to e5 |
| `by_child_pos` | `pos * stride + canonical G` | "parent nodes with this child at this position" | nodes whose child 0 is e3 |
| `by_contains` | canonical `G` | "variadic parent nodes containing this child anywhere" | A/AC/ACI/PlainN/SPair nodes containing e3 |

All index keys annotated "canonical" must be post-rebuild representative
ids. This invariant holds because indices are built after rebuild.

`by_contains` is populated for all variadic node kinds: `A`, `AC`,
`ACI`, and `PlainN` (arity > 3). It is NOT limited to AC/ACI; every
node whose children are stored in the pool gets containment indexing. It also
covers the commutative pair `SPair`, a fixed-arity node: a `:comm` pair is matched
as a two-element multiset (`RAtom::Comm`), so it is joined through `by_contains` as
AC is.

### The composite `by_child_pos` key

`by_child_pos` is keyed by a `(position, class)` pair, and the pair is flattened
into one integer by `DenseSpanMap::composite_key` as `pos * stride + class`,
where `stride` is the node bound the index was built at.
`lemma_composite_key_injective` establishes that the flattening is injective for
a class below the stride, so a parent filed at one position never appears in
another position's bucket. `IndexStore::nodes_by_child_pos` returns the empty
slice for a class at or above the stride and for a position deeper than any node
in this build has, which is what the hash map returned for a key it had never
inserted.

The layout is position-major rather than class-major for two reasons. One
pattern position's keys are then one contiguous run of the span table. And the
key is computable as each child is visited: the stride is known before the walk,
whereas the deepest position is only known after it.

The logical key bound is the largest composite key encountered plus one, which
can be proportional to the node bound times the deepest indexed position.
`SpanArena` uses generation stamps and occupied-key tracking, so a build writes
only occupied entries, but arena capacity can retain a previously reached high
key. A workload combining a large id space with high-arity variadic nodes can
therefore have a large retained span table; splitting the key space remains a
possible response if Criterion and memory measurements show this case matters.

### Cursors

The cursor over a bucket slice is `SortedVecCursor` from `containers-verus`,
re-exported here. It exposes three operations:

```rust
seek(target: G)    // galloping search: O(log(d + 1)) for advance distance d
key() → Option<G>  // current element
step()             // advance position: O(1)
```

The `seek` operation is what makes leapfrog join efficient: instead of
scanning linearly, it gallops from the current position and bisects the
resulting bounded window in the contiguous slice.

#### Why bulk-rebuilt flat arrays?

The implementation uses bulk-rebuilt flat arrays. A `BPlusTreeSet`
alternative exists in the codebase, but it is not wired into `IndexStore`.
Any statement that one is faster must come from the maintained Criterion
benchmark at the revision and workload being evaluated; older isolated
timings are not retained as a design invariant.

The right choice depends in part on how large the delta is between
iterations. Large deltas can favor bulk rebuild; sufficiently small deltas can
make incremental maintenance attractive. Saturation does not guarantee either
trajectory. A future optimization could switch representations dynamically,
but for now every family is bulk-rebuilt. The `BPlusTreeSet` implementation
exists in the codebase (`bplus.rs`).

### Build

```
build(eg):
    stride = eg.node_count()
    for each e-node id in 0..eg.node_count():
        let repr = eg.class_repr(id)
        if subsumed: skip
        if !eg.is_repr_matchable(repr): skip   // class-level matching shield
        stream[by_op].push((eg.node_op(id), id))
        stream[by_repr].push((repr, id))
        for (pos, child) in eg.children(id):
            stream[by_child_pos].push((pos * stride + eg.class_repr(child), id))
        if arity > 3 or node is Seq, MSet, Set, PlainN, or SPair:
            for child in eg.variadic_children(id):
                stream[by_contains].push((eg.class_repr(child), id))  // deduped per node
    for each family: DenseSpanMap::try_build_in(arena, stream, largest key + 1)
```

Ids are visited in ascending order, so each family's stream is ascending in its
value, and `lemma_view_sorted` carries that order into every bucket: the bucket
is the stream's order-preserving filter. No per-bucket sort runs, and no
per-bucket `dedup`, because a node is filed under any one key at most once. A
debug assertion re-checks strict ascent per bucket.

The streams are owned by an `IndexScratch`, so the tens of megabytes they occupy
are faulted in once rather than per round.

### The span arena

`IndexScratch` owns the **span arenas**. A plain `DenseSpanMap::try_build`
initializes a table through its key bound. `try_build_in` instead reuses an
arena with generation stamps and an occupied-key list, so the current build
writes the keys its stream occupies rather than clearing the whole logical key
space.

`try_build_in` takes a caller-owned `SpanArena` that outlives the map. The arena
holds the span table, the list of keys the current build occupied, and a
generation stamp. A normal build bumps the stamp and writes only the keys its
stream carries, so a key an earlier build wrote carries an older stamp and
`get` returns the empty slice for it. It does not clear the retained table.
Table growth writes the missing slots, and `u64` stamp exhaustion performs one
full clear before restarting at generation 1.

The arenas are held in two sets of four, because semi-naive keeps the full index
and the round's delta alive at the same time and a family's key space is stable
across rounds. `IndexStore::recycle_into` hands a store's four arenas back to the
scratch; a caller that does not call it loses the reuse and stays correct,
because the next build allocates a fresh arena.

The scratch is owned by the `Interpreter`, not by the saturation call. `(run 1)`
is a single round, so a scratch allocated per call would be dropped before it was
ever reused, and the E6 incremental cycle is twenty `(run 1)`s over one base.
Reuse across calls, and across `(push)` and `(pop)`, needs no invalidation from
the caller: the stamp is what makes an earlier call's content unreadable, and
that is stated in `build_in`'s postcondition rather than assumed.
`egraph/tests/index_arena_reuse.rs` checks the consumer gets it, on a second
build whose key space is smaller than the first's so the stale keys are in range.

`measure_fanouts` also consumes the occupied-key list through
`for_each_occupied`; it no longer scans `0..len()`. A stamped span is wider
than an unstamped span and each probe checks the generation, while sparse
rebuilds avoid full-table clearing. The net tradeoff is workload-dependent and
must be evaluated with Criterion confidence intervals and memory counters.

### `IndexStats`

```rust
pub struct IndexStats<O> {
    pub op_card: HashMap<O, usize>,
    pub fanouts: FanOuts<O>,
    pub atom_card: HashMap<usize, usize>,  // per-atom override (semi-naive)
}
```

`op_card` records each occupied `by_op` cardinality. The scheduler (§7.3)
uses that, measured access-path fan-outs, and optional sampling to estimate
candidate counts, then chooses the lowest estimate. `atom_card` overrides
`op_card` per query atom; it is empty for naive matching and filled per
semi-naive flavor, where two atoms sharing an op can have different driver-scan
sizes because they read different index slices (§9.2).

### Delta Index for Semi-Naive Evaluation

`IndexStore::build_delta(eg, touched)` builds the same four families
restricted to the `touched` node set. During semi-naive saturation that log
contains fresh nodes, recanonicalized nodes, newly subsumed nodes, and members of an
absorbed class
whose class assignment changed even when their node representation did not; it
may contain duplicates, which `build_delta` removes. Semi-naive evaluation
pairs a full index with a delta index in a `VariantIndex`, which selects, per
query atom, whether that atom scans the full index, the delta, or
`full ∖ delta`. See §9.2.

## 8.2 Leapfrog Triejoin

### The Join Problem

Pattern matching in an e-graph is a multi-way join. The pattern
`(f (g x) (h x))` produces three constraints:

1. `by_op(f)`: all f-nodes
2. `by_child_pos(class_of_g_node, 0)`: parents with this child at pos 0
3. `by_child_pos(class_of_h_node, 1)`: parents with this child at pos 1

The answer is the intersection of these sorted sets. A naive nested
loop can be O(n²) for a 2-way join. The leapfrog step computes a
one-dimensional sorted intersection with monotone seeks. This is the
worst-case-optimal intersection primitive used by the matcher; the full query
also includes scheduling, e-class re-joins, variadic decomposition, guards, and
backtracking, so this section does not assign the whole matcher the AGM bound.

### The Algorithm

Leapfrog maintains a vector of sorted iterators (cursors), all
seeking to agree on the same key.

```rust
pub struct LeapfrogJoin<C: SortedCursor> {
    iters: CursorVec<C>,  // SmallVec<[C; 4]>
    p: usize,
    at_end: bool,
}
```

Generic over the cursor, not tied to `SortedVec`: the same join drives a
`SortedVecCursor`, a `BPlusCursor`, or a `Difference` combinator.

#### Initialization

If any iterator starts exhausted, the join is empty and `new` returns before
sorting. Otherwise it sorts the iterators by current key and runs leapfrog-search:
search seeks the minimum-key cursor to the current maximum key, takes the landed
key as the new maximum, and moves round the ring until all keys agree or one
cursor is exhausted.

#### Finding the Next Match

Instead of checking every element, the algorithm uses `seek` to
skip directly to the next candidate.

```
Iterators (sorted by current key):
  A: [2, 5, 8, 12, 15]   cursor at 2
  B: [3, 5, 9, 12, 20]   cursor at 3
  C: [1, 5, 7, 12, 18]   cursor at 5

Round 1: max = 5 (from C)
  A.seek(5) → 5    B.seek(5) → 5    C already at 5
  All agree on 5 → MATCH

Round 2: advance past 5
  C.step() → 7     (search stopped on C, so next() steps C)
  max = 7
  A.seek(7) → 8    B.seek(8) → 9    C.seek(9) → 12
  max = 12
  A.seek(12) → 12  B.seek(12) → 12  C already at 12
  All agree on 12 → MATCH
```

Each `seek` **gallops**: it doubles an offset from the cursor's current position
until it lands on or past the target, then bisects the bounded window that
doubling produced. Cost is O(log(*d* + 1)) in the distance actually advanced
rather than O(log *n*) in the list length, with the
zero-distance/current-key case handled directly. Total work also depends on
failed candidate alignments and cursor advancement, not only on output size.
Galloping changes the seek cost; it does not turn the surrounding
decomposition/backtracking engine into a worst-case-optimal general join.

Alternatives include full bisection and beginning the gallop at an estimated
stride derived from remaining cursor lengths. The implementation currently
starts at one. Relative performance depends on bucket lengths and the advance
distribution; it is a benchmark question, not a correctness property. Current
comparisons must use the maintained Criterion benchmark and its confidence
intervals rather than the historical point estimates formerly recorded here.

The seek is verified, and it is the verified code that runs: `index.rs`
re-exports `containers-verus`'s `SortedVecCursor` rather than defining one, so
the proof (it lands on the first key ≥ the target and skips no present key, for
every list and every target) covers what ships. Re-exporting the verified cursor
does not itself establish a performance result, and
[containers-verus Ch. 12](../../../containers-verus/doc/design/12-sorted-vec-cursor.md)
(§7, "Scope") lists a machine-level cost theorem as not proved.
`SortedCursor for SortedVecCursor` is therefore implemented in that crate, not
here; `leapfrog.rs` carries no cursor impl of its own.

#### Measuring the seek distribution

`leapfrog::seek_stats` records, for every seek the push-based matcher issues, the
distance it advanced against the run remaining in front of it. It is behind the
`seek-stats` feature and prints under `EGRAPH_SEEK=1`; with the feature off its
cursor wrapper is a type alias for `SortedVecCursor`, so the statistics wrapper
is absent from that path. The first histogram records `⌊log₂ d⌋` against
`⌊log₂ rem⌋`, the remaining run length; the second records `⌊log₂ d⌋` against the log of
the cursor's running mean advance (`JOINT` and `HINT`, `seek_stats.rs`); they support, but do not replace, end-to-end Criterion measurements of
candidate search policies.

#### Usage in Pattern Matching

Each `Join` step in the query plan creates a `LeapfrogJoin` over
the relevant index iterators:

```
Join { target: n0, lookups: [ByOp { op: Add }, ByChildPos { child: x, pos: 0 }], atom_id: 0 }
```

Here `x` is a pattern variable already bound to class e3. This intersects `by_op[Add]` with `by_child_pos[(e3, 0)]`, yielding
Add nodes whose first child is in class e3. For each result, `n0` is
bound and execution continues to the next step.

### The `Difference` Combinator

`LeapfrogJoin` is generic over any `SortedCursor`. Semi-naive
evaluation (§9.2) exploits this with `Difference<A, B>`, a
two-cursor combinator that is *itself* a `SortedCursor`: it yields the
keys of `A` (a full-index cursor) that are absent from `B` (the
delta-index cursor), i.e. `full ∖ delta`. Because it satisfies the
same monotonic-forward seek contract, it drops into a `LeapfrogJoin`
anywhere a base cursor would, with no change to the join algorithm.

## 8.3 Index Selectivity and Adaptive Matching

This section describes how the matcher estimates index selectivity, when it can
adapt atom order to a concrete binding, and how those choices compose with the
semi-naive full/delta index modes. It records current behavior and correctness
boundaries; historical performance investigations are not part of this design
contract.

Companion sections: [indexes](#81-index-construction),
[leapfrog join](#82-leapfrog-triejoin),
[query compilation](07-rules-and-pattern-matching.md#73-query-compilation-and-scheduling),
[pattern matching](07-rules-and-pattern-matching.md#74-pattern-matching-execution), and
[semi-naive evaluation](09-saturation.md#92-semi-naive-evaluation).

### Selectivity Inputs

The scheduler chooses the next atom from a base relation cardinality and the
access paths available for already-bound keys. `IndexStore::measure_fanouts`
records three kinds of expected probe size for each round:

- `by_repr`: expected size of the class bucket reached by a class probe.
- `by_child_pos[(op, position)]`: expected number of `op` nodes in the parent
  bucket reached by a bound child at that position.
- `by_contains[op]`: expected number of variadic `op` nodes containing a bound
  element class.

Child-position and containment measurements are operator-restricted because a
join intersects those buckets with `by_op[op]`. A global bucket average would
mix unrelated operators and price a path the executor never opens.

For bucket sizes `b_i`, the estimator uses the size-biased mean

```text
sum(b_i^2) / sum(b_i)
```

rather than `sum(b_i) / bucket_count`. A key encountered while scanning index
entries lands in a bucket with probability proportional to that bucket's size.
The same pass records skew as

```text
(sum(b_i^2) * bucket_count) / sum(b_i)^2
```

which is `1` for a flat distribution and grows when a few hub buckets dominate.

These values are expectations, not per-binding facts. The runtime and sampled
modes below address that limitation at different points.

### Semi-Naive Cardinalities

A semi-naive variant assigns each join atom one of three modes:

| Atom position relative to the variant's delta atom | Mode | Base cardinality |
|---|---|---:|
| lower | `FullMinusDelta` | `|full.by_op| - |delta.by_op|` |
| equal | `Delta` | `|delta.by_op|` |
| higher | `Full` | `|full.by_op|` |

`variant_stats` stores this cardinality per atom, not per operator, because two
atoms with the same operator can have different modes in one variant.
`VariantIndex` applies the corresponding mode to every lookup emitted for that
atom. `FullMinusDelta` is a cursor difference over the full and delta buckets;
it is not materialized as a third index.

### Operator Restriction

A join with both `ByOp(op)` and a narrower bound-key lookup can enforce the
operator condition in either of two equivalent ways:

1. Keep `ByOp(op)` as a leapfrog intersection cursor.
2. Iterate candidates from the other lookup and test `op[candidate] == op`.

Both return the same set because all index families are built from the same
node stream. Their costs differ with the live bucket lengths, so the default
`OpFilterPolicy::Adaptive` decides per binding. Let `m` be the smallest other
bucket and `n = |by_op[op]|`; the implementation uses the candidate test when

```text
n >= min(512 * m, 131072) && m <= 2 * n
```

`AlwaysFilter` and `AlwaysLeapfrog` exist for conformance testing. The policy is
read once per query, and release execution carries no decision log.

### Atom Scheduling Modes

`SchedulingMode` has three values:

- `Static` is the default. The scheduler produces one step array from the
  round's cardinalities and fan-out estimates.
- `Runtime` re-runs the eager/choice loop at each binding and selects the unused
  atom whose first join opens the shortest live bucket. For
  `FullMinusDelta`, it reads the full-side bucket length as an upper bound; it
  does not traverse the difference merely to price it.
- `Auto` selects runtime ordering per rule per round when the rule's worst
  child-position or containment skew exceeds `8`; otherwise it uses the static
  plan. The selection runs only in semi-naive saturation (`run_rule_variant`); naive
  saturation does not read the mode, so `--auto-scheduling` has an effect only with
  `--use-semi-naive`.

Runtime scheduling represents bound variables and used atoms as `u64` masks.
Queries wider than 64 atoms or variables fall back to the static plan, as do queries
with a sequence-pattern `Collect` atom and flattened queries, whose steps only the
static scheduler lowers. Lowered
segments are memoized by atom and the two masks, so repeated binding states do
not recompile the same block.

The runtime choice is a performance choice only. It lowers the same resolved
atoms against the same `VariantIndex`; ties use the lowest atom index for
determinism.

CLI controls:

- `--runtime-scheduling`
- `--auto-scheduling`

The two modes are mutually exclusive.

### Sampled Cross-Index Selectivity

The size-biased mean assumes that keys produced by one atom follow the marginal
distribution of the index probed by the next atom. That need not hold. Optional
plan-time sampling estimates the joint distribution directly:

1. Draw up to `k` evenly spaced nodes from the emitter atom's driver relation.
   `Delta` samples delta; `Full` samples full; `FullMinusDelta` deliberately
   samples full as an upper-bound proxy rather than paying to materialize or
   count the difference.
2. Extract the classes exposed at the relevant node, child, or variadic-element
   site.
3. Read the operator-restricted target bucket lengths for those classes.
4. Replace the mean fan-out with the mean of those sampled lengths.

The draw is deterministic. Long target buckets are inspected through an
even-stride sample capped at 256 entries, then scaled to the bucket length.
Estimates and emitter draws are memoized for one scheduling call.

`SamplerConfig` defaults to `k = 32`, no bootstrap, and a coefficient-of-
variation threshold of `1.0`. When bootstrap resampling is enabled, an unstable
estimate is discarded and the scheduler falls back to the size-biased mean.
The fixed-seed resampler keeps plan selection reproducible.

Sampling is off by default. CLI controls are:

- `--sampled-selectivity`
- `--sampler-k`
- `--sampler-bootstrap`
- `--sampler-cv`

Sampling affects construction of the static plan. Runtime scheduling records
which atoms have already run and which node variables are already bound in two
`u64` bit sets. When a query has at most 64 atoms and at most 64 node
variables, per-binding `Runtime` scheduling does not consult the static plan or
the sampler. If either count exceeds 64, or the query has a `Collect` atom or is flattened, the
matcher uses the static plan
instead. Under `Auto`, sampled estimates affect rules that stay on the static
path and this width fallback for rules otherwise selected for runtime
scheduling.

### Correctness Boundary

The planner and runtime scheduler may reorder conjunction atoms, but they do not
change the atom set, index snapshot, or per-atom semi-naive mode. The relevant
invariants are:

- all index families in a `VariantIndex` describe one snapshot;
- operator filtering and `ByOp` intersection denote the same candidate set;
- every semi-naive variant preserves its `Delta`/`FullMinusDelta`/`Full` mode by
  atom id, independent of execution order;
- static, runtime, and sampled plans evaluate the same conjunction.

The implementation validates these with deterministic tests:

- `ematch::tests::op_restriction_*` checks the policy and set equivalence;
- `tests/ematch_op_filter.rs` compares all restriction policies on hub-shaped
  inputs;
- `tests/ematch_runtime_schedule.rs` compares match sets and candidate-step
  counts for static and runtime ordering;
- `tests/ematch_sampled_selectivity.rs` checks sampled plans, fallback, and
  match-set equality;
- `saturate::variants_disjoint_and_complete` checks semi-naive decomposition
  under both scheduling modes;
- the `.egg` corpus runs with both static and runtime ordering.

Candidate-step assertions are deterministic correctness/performance-structure
checks. Wall-clock claims belong in Criterion benchmarks such as
`saturate_bench`, `leapfrog_bench`, and `index_bench`; tests do not fail on
host-sensitive timing ratios.

### Deferred Alternatives

**Watermark delta suffixes are not implemented.** Dense allocation-ordered node
ids could let a sorted bucket represent `delta` as the suffix at a round
watermark. The current engine instead builds separate full and delta indexes and
derives `FullMinusDelta` with a difference cursor. A suffix design would need to
preserve bucket id order and prove that the watermark exactly characterizes all
new-or-changed tuples, including class-growth events.

**Whole-stage re-sorting is not implemented.** Runtime mode chooses which atom
to lower next but preserves each atom's compiled variable order. A free-join
executor that reorders stages inside an atom would require a different execution
model and a separate correctness argument.

**Cross-round learned profiles are not implemented.** All estimates come from
the current immutable index snapshot. No execution history is fed into later
rounds.

---
[← Ch 7: Rules and Pattern Matching](07-rules-and-pattern-matching.md) · [Table of Contents](00-table-of-contents.md) · [Ch 9: Saturation →](09-saturation.md)
