# Chapter 18 — Semi-Naive Evaluation

[← Ch 17: Interpreter and Saturation Loop](17-interpreter.md) · [Table of Contents](00-table-of-contents.md) · [Ch 19: Anti-Unification →](19-anti-unification.md)

**Status**: implemented. Select with `saturate_semi` / the
`SaturationStrategy::SemiNaive` interpreter strategy / `--use-semi-naive`
on the CLI. The default remains naive; there is no
automatic fallback. Deferred: delta-size fallback, trigger pre-filter,
and the pluggable B+tree full-index backend (see Open Questions).

The delta index is built through the arena in Chapter 6, so its construction
work is proportional to the delta stream rather than the full index's key
space. Older hand-timed dense-span and single-round results are historical and
do not establish current end-to-end performance. Current naive/semi-naive
comparisons belong in the `saturate_bench` Criterion harness and must use the
same revision and workload.
**Scope**: e-matching loop and `IndexStore`.
**Depends on**: [Ch 6: Index](06-index.md), [Ch 7: Leapfrog Triejoin](07-leapfrog.md), [Ch 8: Query Compilation](08-query-compilation.md), [Ch 9: Pattern Matching](09-pattern-matching.md).

## Motivation

The naive saturation loop (Chapter 17) can rediscover the same matches every
round.

Each round:

1. Rebuild the e-graph.
2. Build an `IndexStore` snapshot from the full e-graph.
3. For every rule, match against that snapshot and apply every emitted
   match.

There is no cross-round set of previously applied matches in the naive
driver. A match that remains present can therefore be found and applied
again. Nodes and merges created while applying rules are not added to the
frozen index; they become visible after the next rebuild and index build.

In a simple model where match sets only grow, the total discovery work over
N rounds is `sum |M_K|`, which can approach `O(N * |M_N|)` even though
only the increments are new. Production match sets are not generally
monotone: subsumption removes nodes from indices, and recanonicalization can
change which tuples a snapshot contains. The model illustrates repeated
discovery; it is not a general invariant of the engine.

For example, a simple linear-growth model with 100 rounds and 1M final
matches attributes about 98% of its modeled outer-loop work to rediscovery.
That is an illustration of the recurrence, not a workload measurement.

For eligible rule shapes, semi-naive evaluation instead runs the matches
that involve a conservatively tracked changed tuple. This can shrink a
driver scan from `full` to `delta`, where `delta` contains nodes added,
recanonicalized, or exposed through class growth. Rules whose enabling
events cannot be represented by that delta use the full matcher every
round.

## The Key Invariant and Its Scope

For a rule accepted by the delta path, every match that becomes available
across two round snapshots has at least one scanning atom whose node is in
`delta`. The touched log is conservative, so the converse need not hold:
a tuple involving a touched node can already have matched in the previous
round.

Call the conservatively tracked set `delta`, and the full set of indexed
nodes `full` (which contains `delta`). For a k-atom eligible rule, the set
the variant decomposition enumerates is:

```
delta_matches = { (n_1, …, n_k) ∈ full^k that satisfy the rule's pattern
                  AND at least one n_i ∈ delta }
```

A naive way to compute `delta_matches` would be "compute all matches,
filter for the ∃ condition." Semi-naive decomposes it into a disjoint
union of k restricted joins, one per atom position.

## The K-Variant Decomposition

For a rule with k atoms, semi-naive runs k variants of the rule's
query plan each round. Variant `i` (for `i ∈ 0..k`) restricts atoms
by position:

| Atom position `j` | Restriction in variant `i`  |
|-------------------|-----------------------------|
| `j < i`           | `full \ delta` (old only)   |
| `j == i`          | `delta`                     |
| `j > i`           | `full` (unrestricted)       |

**Why this partitions the selected set.** Every delta-involving match has a
well-defined "first delta atom": the smallest position `i` such that
atom `i` is in `delta`. By construction, atoms `< i` are not in
`delta` (they're in `full \ delta`). Variant `i` is the unique
variant that matches this match:

- Variant `i'` with `i' < i`: atom `i'` must be in `delta`, but by
  definition of "first delta atom," atom `i'` is not in `delta`. Fails.
- Variant `i`: atom `i` is in `delta` (match ✓), atoms `< i` are not
  in `delta` (the `full \ delta` restriction holds), atoms `> i`
  unrestricted. Matches.
- Variant `i'` with `i' > i`: atom `i` must be in `full \ delta`, but
  atom `i` is in `delta` (that's what made `i` the first delta atom).
  Fails.

Every match with at least one delta atom is found by exactly one variant.
Matches with zero delta atoms (all atoms in `full \ delta`) are omitted.
For an eligible rule, the enabling-event invariant says such a match was
not newly enabled by the current transition. The fallback rules described
below do not rely on this premise.

The `full \ delta` restriction on atoms `< i` is non-negotiable.
Without it, a match with multiple delta atoms (at positions
`i < j`) would be found by variant `i` *and* variant `j`, producing
duplicate emissions.

### Which Atoms Count as Positions

The "k atoms" above are the **join-producing atoms**: those that
scan an index to generate candidate nodes. In our `RAtom` enum these
are `Plain`, `AExact`, `APrefix`, `ASuffix`, `ABoth`, `ACExact`,
`ACSub`, `ACIExact`, `ACISub`, `Lit`, and `LitBind`. The built-in
constraint atoms `Eq`, `EqGlobal` and `Pred` are **excluded** from the
variant count: they do not scan a relation, they only check or
propagate bindings between already-bound variables. They have no
`delta` because they are not extensional indices.

This mirrors textbook semi-naive Datalog, where only IDB/EDB body
atoms participate in the decomposition and built-in predicates
(arithmetic, equality) are evaluated directly without a delta. The
delta-path premise is: every way a match can become available shows
up in some join atom's delta. Three event kinds make a match
available, and the touched log records all three: a node is created; a
node is recanonicalized (a child's stored representative died in a
merge); a class's membership grows without any node changing shape.
The third kind exists because the union can keep the representative
the parents already store: nothing recanonicalizes, yet joins through
that class gain tuples. `merge_in_classes` therefore records the
absorbed class's member nodes in the touched log on every merge (the
class-growth delta), and `--union-by size` keeps that recording
amortized by absorbing the smaller side. Constraint atoms are applied as
filters uniformly across variants. Rules with constraint/global shapes
that violate the premise bypass the variants.

**Two rule shapes have no delta to read and match the whole graph
every round** (`saturate::needs_naive_match`):

- A constraint between two atoms' *node* variables, which the
  root-binding form `(= v pat)` produces. The match becomes available
  when the two classes merge, and neither atom's relation gains a
  tuple it scans for. The `matrix` translation exposed this correctness
  failure: its
  conditional Kron/MMul rewrite guards on
  `(= p (ncols a)) (= p (nrows c))`: under delta restriction that
  rule never fires at any budget.
  `egraph/tests/egg/root_binding_merge_during_run.egg` pins it under
  both strategies.
- A rule referencing a let-bound global in a child or element
  position. The global's class can grow by absorbing another class,
  and no atom of the rule scans that class, so not even the
  class-growth delta reaches it.
  `egraph/tests/egg/semi_recanon_parent_delta.egg` pins it; the
  companion `semi_merge_membership_delta.egg` pins the class-growth
  delta itself, where a scanning atom exists and the delta suffices.

## Worked Example: Nested Patterns and Flattening

The invariant above talks about k atoms in abstract. For our e-graph,
atoms come from flattening nested patterns, so it's worth walking
through a concrete case to see how nesting interacts with the
k-variant partition.

### Pattern

Consider a rule with a nested LHS:

```
R:  mul(add(?x, ?y), mul(?z, ?y))  →  ...
```

This is a three-node pattern tree: an outer `mul`, with its first
child being an `add(?x, ?y)` and its second child being another
`mul(?z, ?y)`. The `?y` variable is shared between the two inner
atoms.

### Flattening (Ch 11)

The flattening pass (`flatten_surface`) emits child applications
left-to-right before their parent, and the resolver preserves that order.
The resulting `ResolvedQuery` has one atom per pattern e-node:

- **Atom 0**: `?lhs = add(?x, ?y)`
- **Atom 1**: `?rhs = mul(?z, ?y)`
- **Atom 2**: `?root = mul(?lhs, ?rhs)` (the outer mul)

The nesting has become **join constraints between atoms** via shared
pattern variables:

- Atom 2's `?lhs` is atom 0's binding target (parent-child link).
- Atom 2's `?rhs` is atom 1's binding target.
- Atom 0's `?y` equals atom 1's `?y` (non-linear join).

After flattening, there is no "nested" atom anymore: there are three
atoms sitting in a flat list, joined by shared variables. **Semi-naive
operates on this flat list**; it never sees the pattern tree.

### Matches are Node-Tuples

A match of R is a 3-tuple of nodes `(n_0, n_1, n_2)` such that:

- `n_0` is an `add` node.
- `n_1` is the inner `mul` node.
- `n_2` is the outer `mul` node whose first and second child e-classes
  equal the classes of `n_0` and `n_1`, respectively.
- `n_0`'s second child e-class equals `n_1`'s second child e-class
  (the `?y` constraint).

"Atom `i` is in delta" means `n_i` was added, recanonicalized, or
logged because its class was absorbed during the transition.

### The Three Variants

For this 3-atom rule, semi-naive runs three plan variants. In each,
one atom is delta-restricted (all index lookups for that atom read from
`delta`) and the lower-indexed atoms are restricted to `full \ delta`.
The scheduler may nevertheless choose another atom as the first driver when
its bound-key fanout or sampled selectivity makes that access path cheaper.

**Variant 0**: inner add is in delta.

| Atom     | Restriction   |
|----------|---------------|
| 0 (add)  | **delta**     |
| 1 (inner mul) | full     |
| 2 (outer mul) | full     |

When its cost is smallest, the scheduler drives from
`delta_by_op[add]` (atom 0's index). The bound `?lhs` then narrows the
outer-mul atom through `by_child_pos[(?lhs, 0)]`; atom 1 remains a
full-view probe.

**Variant 1**: inner mul is in delta, inner add is outside delta.

| Atom     | Restriction       |
|----------|-------------------|
| 0 (add)  | **full \ delta**  |
| 1 (inner mul) | **delta**    |
| 2 (outer mul) | full         |

Now the scheduler can drive from atom 1's delta `mul` bucket. Atom 0
uses `FullMinusDelta`; the outer-mul atom remains unrestricted and can
be narrowed through its already-bound second child.

**Variant 2**: outer mul is in delta, both inner nodes are outside delta.

| Atom     | Restriction       |
|----------|-------------------|
| 0 (add)  | **full \ delta**  |
| 1 (inner mul) | **full \ delta** |
| 2 (outer mul) | **delta**    |

The outer-mul join reads its delta bucket. Extracting its children binds
the two inner node variables; their re-joins both use
`FullMinusDelta` cursors.

### Why This Partitions Matches Correctly

Consider a match where **all three** nodes happen to be in delta
this round: `(n_0 ∈ delta, n_1 ∈ delta, n_2 ∈ delta)`. This can
happen if the round added several fresh nodes that happen to align.

- **Variant 0** finds it: atom 0 ∈ delta ✓, atoms 1 and 2 unrestricted
  (both in full, trivially true since delta ⊆ full) ✓. ✅
- **Variant 1** rejects it: atom 0 must be in `full \ delta`, but
  `n_0 ∈ delta`. ✗
- **Variant 2** rejects it: atom 0 must be in `full \ delta`, but
  `n_0 ∈ delta`. ✗

The match is found exactly once, by variant 0, the variant associated
with its leftmost delta atom (position 0).

Now consider a mixed match where only atom 1 is in delta:
`(n_0 ∈ full \ delta, n_1 ∈ delta, n_2 ∈ full \ delta)`.

- **Variant 0** rejects it: atom 0 must be in delta, but
  `n_0 ∉ delta`. ✗
- **Variant 1** finds it: atom 0 ∈ full\delta ✓, atom 1 ∈ delta ✓,
  atom 2 unrestricted ✓. ✅
- **Variant 2** rejects it: atom 1 must be in full\delta, but
  `n_1 ∈ delta`. ✗

Again, found exactly once.

### Why the Upper Half Stays Unrestricted

Why not symmetric: why not restrict *both* halves (lower and upper)
to `full \ delta` around the one delta atom?

Consider `(n_0 ∈ full\delta, n_1 ∈ delta, n_2 ∈ delta)`: two delta
atoms, both at positions ≥ 1.

With upper-half restriction (atom 2 forced to `full \ delta`):

- Variant 1 would require atom 2 ∈ full\delta, but `n_2 ∈ delta`. ✗

With our actual rule (upper half unrestricted):

- Variant 1: atom 0 ∈ full\delta ✓, atom 1 ∈ delta ✓, atom 2 any ✓. ✅
- Variant 2: atom 0 ∈ full\delta ✓, atom 1 ∈ full\delta? `n_1 ∈ delta`. ✗

So variant 1 correctly finds the match. Symmetric restriction would
miss it entirely: no variant would catch it.

The asymmetry exists because the partition is defined by
**leftmost delta atom**. Variant `i` owns matches whose leftmost delta
atom is at position `i`. For such a match:

- Atoms at positions `< i` must be outside delta (otherwise the leftmost
  delta atom would be at some `j < i`, and the match belongs to variant
  `j`, not `i`).
- Atom at position `i` is in delta by definition.
- Atoms at positions `> i` can be anything: their delta membership is
  *irrelevant to which bin this match falls into*, because they
  don't change what the leftmost delta atom's position is.

Restricting positions `> i` would further split each bin into
sub-bins keyed on which higher positions are also new: that's
`2^k` variants instead of `k`. Linearity is what makes the algorithm
tractable.

### Atom Numbering vs Execution Order

A subtle but important point: **atom numbering** (used to define
"position `i`", variant `i`, lower-vs-upper) is separate from
**execution order** (chosen by the scheduler per variant).

The scheduler in Ch 8 picks atom order by selectivity. Within a
variant, the delta-restricted atom has its delta-bucket base cardinality, but
fanout and sampled-selectivity terms can still make another atom the first
driver regardless of where either atom sits in the numbering.
Atom numbering is a stable reference for partitioning matches;
execution order is an implementation detail of how each variant is
evaluated.

Under the default `Static` scheduling mode, the scheduler emits one fixed
step sequence per variant per round from that round's cardinalities. Under
`Runtime`, and under `Auto` for a rule whose measured skew crosses the
threshold, the matcher instead chooses the next atom per partial binding
(falling back to the static plan for queries wider than 64 atoms or node
variables). Chapter 20 describes those modes. In every case the stable atom
number, not execution position, selects the semi-naive index mode, so
reordering changes cost rather than the variant's result set.

Concretely, in variant 1 of the example above, the static scheduler drives
from atom 1 first if its delta cardinality makes it the cheapest estimate,
even though atom 1 is "in the middle" of the pattern tree. It then follows join constraints
upward to atom 0 and across to atom 2. The `FullMinusDelta`
restriction on atom 0 applies regardless of whether the scheduler
probed it first or last: it's a filter on atom 0's index, not an
ordering constraint.

### The Payoff

For this rule, naive matching each round sees only full-index modes.
Semi-naive runs three variants, each with one atom restricted to its delta
index and earlier atoms restricted to `full \ delta`. When the scheduler
chooses the delta atom as the driver, the outer-loop ratio follows the actual
full/delta cardinalities. Irrespective of driver choice, the decomposition
still emits each delta-involving match tuple exactly once.

The flattener did the hard work of turning the pattern tree into a
flat join problem. Once that's done, semi-naive is *oblivious to
nesting*: it just picks which atom is delta-driven, using the same
k-variant machinery that would apply to a non-nested rule with k
independent atoms.

## Where the Savings Come From

The following model isolates outer-loop discovery work: iterate the driver
atom's index and probe the remaining atoms for each element. Current
`SortedVecCursor` seeks are logarithmic after the galloping bound; iteration
is linear in driver size. Whether this component dominates a workload is a
Criterion measurement, not an invariant.

The scheduler (Ch 8) already picks the driver by selectivity. When the
delta-restricted atom is the smallest in its variant, the scheduler drives from
it.

- If atom `i` is selected as variant `i`'s driver, its outer loop is
  restricted to that atom's delta bucket.
- Total modeled outer-loop work is the sum of those k delta-bucket
  cardinalities, rather than one selected full bucket.
- Under the uniform-bucket model below, that becomes
  `k · |delta_driver|` versus `|full_driver|`.

Note: the scheduler doesn't need to know about "delta" as a concept.
It sees a mode-specific base cardinality for every atom via
`IndexStats::atom_card`, combines it with fanout/selectivity estimates, and
picks the cheapest. Semi-naive falls out of providing the right per-atom stats
for each variant.

## Illustrative Cost Model: 4-Atom Pattern, 100K Full, 1K Delta

The following arithmetic makes the asymptotic argument concrete. It is a model,
not benchmark evidence. Setup:

- `|full| = 100,000` nodes
- `|delta| = 1,000` nodes
- Pattern with k = 4 atoms
- Uniformly distributed ops: each atom's op has ~20,000 full nodes,
  ~200 delta nodes
- Join constraints: each inner probe narrows to ~1% of the driver
  (typical for `by_child_pos` with one bound variable)

### Outer-Loop Iteration Count (Dominant Cost)

| Approach       | Per-variant outer size | Variants | Total outer iters |
|----------------|------------------------|----------|-------------------|
| Naive          | 20,000                 | 1        | 20,000            |
| Semi-naive     | 200                    | 4        | 800               |

**Modeled outer-loop ratio: 25×.**

### Probe and `Difference` Cost

The 25× figure above models driver iterations only. It cannot be converted to
a comparison-count ratio from the relation sizes alone. A
`SortedVecCursor::seek(target)` uses a forward gallop and bisection and costs
`O(log d)` in the distance advanced by that particular seek. A
`Difference(full, delta)` advances both sub-cursors monotonically and, over a
complete sequential scan, advances through at most `|full| + |delta|` entries.
Inside leapfrog, however, the cursor can receive a sequence of non-unit seeks;
their comparison cost depends on the actual key gaps and intersections, not
just `|delta|`.

Under the same uniform-bucket assumption, and conditional on the scheduler
choosing each variant's delta atom first, the work shape is:

| Variant | Delta-driver entries | Earlier atoms in `full \ delta` | Probe/filter cost |
|---------|----------------------|---------------------------------|-------------------|
| 0       | 200                  | 0                               | key-gap dependent |
| 1       | 200                  | 1                               | key-gap dependent |
| 2       | 200                  | 2                               | key-gap dependent |
| 3       | 200                  | 3                               | key-gap dependent |
| **Sum** | **800**              | **6 atom-modes**                | not derivable from cardinalities alone |
| Naive   | 20,000               | 0                               | key-gap dependent |

Later variants open more `Difference` cursors, so they can pay more filtering
work. The size-only model therefore supports only the conditional outer-loop
ratio. Wall-clock and comparison-count ratios require the Criterion saturation
harness (and seek instrumentation) because probe gaps, cache behavior,
scheduling, deduplication, and match application do not scale by that count
alone.

### Sensitivity to Delta Size

Fix `|full| = 100K`, k = 4. Vary `|delta|`:

| delta        | Semi-naive outer | Naive outer | Raw ratio |
|--------------|------------------|-------------|-----------|
| 100          | 80               | 20,000      | 250×      |
| 1,000        | 800              | 20,000      | 25×       |
| 10,000       | 8,000            | 20,000      | 2.5×      |
| 25,000       | 20,000           | 20,000      | 1.0×      |
| 50,000       | 40,000           | 20,000      | **0.5× (slower)** |

**Outer-loop threshold in this model**: `k · |delta| < |full|`, i.e.,
`|delta| / |full| < 1/k`. For 4 atoms, that's 25%. Above that, the
k-variant overhead exceeds the savings, at which point falling back
to the naive path is the right move (see Open Questions).

Actual crossover also includes index construction, scheduling, filtering,
deduplication, and match application, so it must be measured.

### Sensitivity to Pattern Size

Fix `|full| = 100K`, `|delta| = 1K`. Vary k:

| k  | Semi-naive outer | Naive outer | Raw ratio |
|----|------------------|-------------|-----------|
| 1  | 200              | 20,000      | 100×      |
| 2  | 400              | 20,000      | 50×       |
| 3  | 600              | 20,000      | 33×       |
| 4  | 800              | 20,000      | 25×       |
| 6  | 1,200            | 20,000      | 17×       |
| 10 | 2,000            | 20,000      | 10×       |

The modeled ratio decays as
`|full_driver| / (k × |delta_driver|)`; the last row is 10× under
the table's uniform-selectivity assumptions.

### Saturation Where It Wins Asymmetrically

The model gives semi-naive its largest ratio when a saturation does most of its
growth early and then converges slowly. Example: round 1 adds 100K nodes;
rounds 2–100 add 10 nodes to each of the five uniform operator buckets
(50 total).

- Naive: round 1 does 100K × 3 probes, rounds 2–100 each rescan the
  full (now-static) 100K. Work ∝ 100 × 20,000 = 2M outer iterations.
- Semi-naive: round 1 is degenerate (delta ≈ full, semi-naive should
  fall back to naive). Rounds 2–100 each do 4 × 10 = 40 outer
  iterations. Work ∝ 20,000 + 99 × 40 ≈ 24,000 outer iterations.
- **Modeled saturation-level ratio: ~80×.**

In the outer-loop model, tail rounds become cheap when delta is tiny, while
naive still pays a full scan. Criterion must determine how much of that
asymmetry survives the fixed and non-matching costs.

### Caveats

These modeled numbers assume **uniform selectivity across atoms**. Real
patterns have bottleneck atoms: one very rare op can drive the join
to near-linear in that atom's size, making naive already cheap and
cutting semi-naive's advantage.

The numbers also ignore match-application cost. The naive driver has no
cross-round applied-match deduplication, so it can reapply persistent old
matches while the eligible semi-naive path omits them. Both use the same
action implementation for a match they do emit, but they need not emit the
same number of applications per round.

## The Three Index Flavors

Semi-naive requires three logical index flavors per index family
(`by_op`, `by_repr`, `by_child_pos`, `by_contains`):

| Flavor            | Content                       | Lifecycle                                       |
|-------------------|-------------------------------|-------------------------------------------------|
| `full`            | all indexed nodes at the round snapshot | rebuilt and dropped every round        |
| `delta`           | touched nodes present at that same snapshot | rebuilt in rounds after round 0   |
| `full \ delta`    | snapshot nodes not in the touched set | **derived view**; never materialized      |

`full \ delta` is a **derived view**: never materialized. It is
computed lazily by a `Difference` cursor *combinator* that is generic
over any two `SortedCursor`s (so it works for `SortedVecCursor` today
and `BPlusCursor` later, with no backend coupling) and itself implements
`SortedCursor`, so leapfrog consumes it like any other cursor:

```rust
pub struct Difference<A, B> { full: A, delta: B }

impl<K, A, B> SortedCursor for Difference<A, B>
where A: SortedCursor<Key = K>, B: SortedCursor<Key = K>
{
    type Key = K;
    // skip routine, run on every access:
    //   loop { k = full.key()?; delta.seek(k);
    //          if delta.key() == Some(k) { full.step() } else { break } }
    //   key()  = skip(); full.key()
    //   step() = full.step(); skip()
    //   seek(t)= full.seek(t); delta.seek(t); skip()
}
```

Both sub-cursors index the *same key* in their respective stores (e.g.
for `by_op[mul]`: `full.by_op[mul]` and `delta.by_op[mul]`). The
combinator yields exactly the full keys absent from delta. It is
correct because leapfrog only ever seeks **monotonically forward**, so
the delta sub-cursor sweeps forward in lockstep and never rewinds; the
whole difference costs `O(|full| + |delta|)` across a scan. No third
index is materialized, and the base cursors stay untouched: exclusion
is layered on as a combinator, not baked into the cursor trait.

It is built **only** for `full \ delta` atoms (`j < i`); full and delta
atoms use bare base cursors. See "How a Variant Executes" for how the
two cursor types coexist without an enum or trait object.

### The Delta Index

The delta index exists for exactly one round. It's built from a
**touched log**: an append-only list of node ids that were created,
recanonicalized, or members of a class absorbed by a merge during the
round (the class-growth delta). (The same
log has a second consumer: AC completion's incremental superposition
watermarks it to superpose only critical pairs with a changed endpoint,
so completion-materialized nodes flow into the matcher's next delta,
and matcher-created nodes into completion's, through one mechanism.) At the
start of each match phase after round 0:

1. Rebuild the e-graph, then build `full` from the rebuilt state.
2. Sort and dedup the touched log while streaming it into the same four
   families as `full`, under the same keys, to build `delta`.
3. Clear the touched log and run e-matching with the k-variant fan-out.
4. After all rules have matched, discard both index snapshots and recycle
   their span arenas. Nodes created by match application stay in the newly
   populated touched log and enter both appropriate snapshots after the next
   rebuild.

`delta` is built in the same instant as `full`, from the same e-graph, so
the two agree on every key and `delta ⊆ full` per key holds for the whole
round. The canonicalization behind those keys is stored once, on `full`
(`IndexStore::repr`), and every canonicalization the matcher performs reads
it rather than the live union-find, including the ones inside a variant's
`Difference` cursors, which would otherwise subtract a delta bucket from a
full bucket that a mid-round merge had moved. Chapter 09, "Which Snapshot",
states the contract and why it is what makes a variant's match count
comparable across variants and across rounds.

The touched log is a single `Vec<Cfg::G>` field on `EGraph`,
populated during rebuild via an out-param threaded through
`recanonize_node` (one push per genuinely-changed node) and in
`register_if_fresh` (one push per freshly-created node). It is
round-local scratch, cleared after each round's snapshots are built. Duplicates are
removed by the sort-dedup in step 1, so no separate hash set is
needed.

**The delta index has the same representation as the full index, a
`DenseSpanMap` per family.** No backend flexibility needed: it is built once,
read once, discarded. The access pattern is pure outer-loop iteration, which
favors contiguous memory.

### Global, Not Per-Cache

The delta is stored **globally**: one delta `IndexStore` for the whole
e-graph, mirroring the global full `IndexStore`. It is *not* partitioned
per node cache. This falls directly out of how indexing works today:

- The full `IndexStore` is global and keyed by **crosscutting
  attributes**: `by_op[op]`, `by_repr[repr]`, `by_child_pos[(repr,
  pos)]`, `by_contains[repr]`. It is built by scanning every node id
  `0..node_count` once. It is not organized by arity-class.
- The node **caches** (`FixedArityCache` for arity 0–3 / commutative,
  `VariableArityCache` for A/AC/ACI, `LitCache`) partition nodes by
  arity-class for storage and hash-consing. One registered operator has
  one fixed kind, so a particular `by_op[op]` bucket comes from one
  cache. The index family as a whole spans all caches, while
  `by_repr`, `by_child_pos`, and `by_contains` buckets can cross cache
  boundaries.

So even though the touched *events* originate inside per-cache
`recanonize_node` calls, a per-cache delta would have to be re-bucketed
into the global crosscutting keys before matching could use it, buying
nothing. Instead:

- **Origin (per-cache + global)**: each cache's `recanonize_node` pushes
  changed node ids through the `&mut Vec<G>` out-param;
  `register_if_fresh` pushes new node ids. Both land in the single
  `EGraph::touched` vector.
- **Storage (global)**: `IndexStore::build_delta(eg, &touched)` scans
  just the touched ids and buckets them into one global delta
  `IndexStore` with the same four crosscutting maps as `full`.

The touched *log* is global scratch; the delta *index* is global; only
the change-*detection* is per-cache, because that is simply where
recanonicalization physically happens.

### The Full Index

The full index is the performance-sensitive half. Its access patterns
are different from delta's:

- **Read-heavy, seek-driven**: atoms in `Full` mode probe the full index;
  atoms in `Delta` mode probe the delta index; and atoms in
  `FullMinusDelta` mode probe paired full/delta buckets through
  `Difference`. Each atom applies one mode consistently to all of its lookups.
- **Round snapshot**: bulk-rebuilt from scratch and dropped each round today;
  only scratch-buffer and span-arena capacity is recycled. An incrementally
  maintained backend is a deferred alternative.
- **Not persistent state**: `mark`/`restore` operates on the e-graph; the
  next round constructs a new full index from the restored graph.

This is where the backend choice becomes interesting.

## Backend Choice for the Full Index

Today the full index is **Option A below**: four `DenseSpanMap<G>`
families bulk-built each round; each bucket is a contiguous sorted slice
read by `SortedVecCursor`. It is the same index the naive loop uses.
Semi-naive's match-work
savings are independent of this choice. Making the backend configurable
(so the full index could instead be maintained incrementally) is
**deferred**; the analysis here records the three candidates and why
choosing between them is an empirical, workload-dependent question that
microbenchmarks alone cannot settle.

| Option | Status | Per-round maintenance | `restore` behavior | Main tradeoff |
|--------|--------|-----------------------|--------------------|---------------|
| A: `DenseSpanMap` + `SortedVecCursor` | implemented | bulk-build every snapshot | build the next snapshot from the restored graph | contiguous reads, full rebuild cost |
| B: untracked B+tree | design candidate | incremental add/remove/re-key required | full rebuild | sparse updates without diff-log cost |
| C: tracked B+tree | design candidate | incremental add/remove/re-key plus capture logging | replay retained diffs and rebuild capture state | cheaper restore only when tracking pays for itself |

The table states implementation shape, not a speed ranking. A ranking requires
same-revision Criterion measurements over representative multi-round workloads.

### Option A: `DenseSpanMap<G>`, bulk-rebuilt each round

What the current `IndexStore` does. It pays work proportional to the
generated index streams plus occupied keys each round. Those streams include
one entry per node for some families and child/containment entries for
others, so `O(|full|)` is only shorthand when total arity is also linear.

- **Pro**: simplest to implement: no new machinery; regression path
  against the existing naive loop.
- **Pro**: perfectly sorted arrays with no tombstones, great constants
  for leapfrog outer iteration.
- **Con**: rebuild cost scales with total node count, not delta size.
  Semi-naive's win on *match* work is partially offset by per-round
  *rebuild* cost.
- **Con**: a seek is still worst-case O(log n), although the verified
  galloping cursor reduces short forward seeks.
- **When it wins**: small graphs, or saturations where per-round work
  is match-bound rather than rebuild-bound.

### Option B: `BPlusTreeSet<G, TRACK=false>`, incremental

B+tree with semi-persistence disabled. This is a candidate, not an
implemented backend. A correct incremental index needs more than `insert`:
recanonicalization and subsumption can remove or re-key old entries, so the
design must supply deletion/tombstone handling as well as additions. It
would be rebuilt from the e-graph after `restore`.

- **Potential pro**: when changes are sparse and re-key/removal is supported,
  maintenance can scale with changed entries (plus tree-operation costs)
  rather than every full-index entry.
- **Pro**: the cursor fast path reduces comparison work for small skips, and
  leapfrog is seek-heavy.
- **Con**: `restore` triggers a full rebuild from the e-graph. Only
  costly if workloads backtrack often.
- **When it may win**: large graphs with many sparse-change rounds and rare
  `restore`; this requires end-to-end Criterion evidence.

### Option C: `BPlusTreeSet<G, TRACK=true>`, semi-persistent

Same as B, plus diff-log tracking. `restore` rolls the tree back by replaying
the relevant diffs and rebuilding capture state rather than rebuilding the
whole index.

- **Potential pro**: restore is proportional to diff replay, regrowth, and
  capture-state rebuilding rather than a full index rebuild.
- **Con**: every first write to a captured tree cell pays diff logging and
  stores the old cell value. For a tree that is never restored, that execution
  and memory cost provides no benefit.
- **Con**: memory grows with the distinct captured cells and retained old
  values between marks.
- **When it wins**: workloads with frequent `mark` / `restore` and a
  non-trivial full-index state that would otherwise be expensive to
  rebuild.

### Why This Is an Empirical Question

The choice is **workload-dependent** and cannot be resolved from
microbenchmarks alone. The three axes that matter are:

1. **Graph size at steady state.** Larger snapshots increase bulk-build
   work, while trees add pointer/layout and update costs.
2. **Round change rate.** Sparse changes can favor an incremental backend
   only after additions, removals, and re-keying are all counted. Bursty
   changes favor bulk construction.
3. **Backtracking frequency.** Favours C when `mark`/`restore` is
   called often and the full index is large. Favours A or B when
   backtracking is rare: the diff-log overhead doesn't pay for
   itself.

Microbenchmarks answer parts of (1) but nothing about (2) or (3).
Those need a full saturation loop with representative rulesets.

### Status

Option A is what ships: `DenseSpanMap` families with sorted bucket slices,
bulk-rebuilt each round. The `saturate_bench` and corpus Criterion harnesses
provide end-to-end measurement; implementing a mutable backend contract
(including removal/re-key semantics) and optionally exposing a choice remain
deferred and tracked in
[`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md).

## Interaction with the Existing Scheduler

Semi-naive keeps the scheduler's eager-pass + pick-cheapest structure. Its
additional input is a per-atom cardinality override (`atom_card`), because
two same-op atoms can have different full/delta modes in one variant.
Fan-out statistics and optional sampled selectivity are otherwise shared
with naive matching.

### Scheduling Modes

No plan is cached across rounds. Every rule is scheduled from the current
index statistics:

- **Naive** builds one fallback/static plan per rule and round.
- **Semi-naive round 0** does the same over the full view.
- **Semi-naive later rounds** build one fallback/static plan per eligible
  variant. `variant_stats` supplies each atom's mode-specific base
  cardinality.

With `SchedulingMode::Static` (the default), that plan fixes atom order for
the query. With `Runtime`, the matcher runs the same eager lowering but
chooses each next atom from concrete cursor lengths under the current
partial binding. `Auto` enables that runtime path per rule/round when
measured access-path skew exceeds 8. Queries with more than 64 atoms or
node variables use the static fallback.

Static greedy scheduling is O(k²) in atom count. Runtime scheduling memoizes
lowered blocks by atom/bound/used masks within one query execution, but
neither mode caches plans across rounds or variants.

The static cost model combines base relation cardinality, measured fan-outs,
and optional cross-index samples. Runtime mode instead reads concrete cursor
lengths per binding. Chapter 20 is the maintained design reference for these
selectivity mechanisms.

### How the Static Scheduler Works

The scheduler is not a simple "order atoms by selectivity." It's a
plan compiler that emits a flat sequence of `Step`s via an
interleaved two-phase loop:

**Phase 1: Eager propagation.** Repeatedly scan all unused atoms
looking for ones that are already satisfiable given the current set
of bound variables:

- `RAtom::Eq(a, b)` with one or both sides bound → emit `CheckEq`
  or `CopyBinding`. No index access.
- `RAtom::Plain { node, .. }` where `node` is already bound → the
  node variable was bound by a previous step's child extraction.
  Emit `Join { ByRepr(node) ∩ ByOp(op) }` (intersect within the
  known class) + `ExtractChild` / `CheckChildEq` for each child.
  This resolves the atom **without scanning `by_op` at full size**.
- `RAtom::Lit` / `LitBind` whose node variable is already bound →
  re-join within that class.

These steps are forced by the current bindings rather than selected by the
cost model. The eager pass fires them until nothing more can be resolved.

**Phase 2: Pick one expensive atom.** When the eager pass stalls,
pick the single cheapest remaining atom via `estimate_cost` (which
reads the atom's cardinality from `IndexStats`: `atom_card[atom_id]`
if set for this flavor, else `op_card[op]`; see "Why This Composes").
Emit its `Join` step (leapfrog over `ByOp ∩ ByChildPos` for any
already-bound children), then `ExtractChild` for each unbound child.
This binds new variables, which may unlock more atoms in the next
eager pass.

Then loop back to Phase 1.

**Example.** Pattern `mul(add(?x, ?y), ?z)` is flattened in postorder to:

- Atom 0: `?lhs = add(?x, ?y)`
- Atom 1: `?root = mul(?lhs, ?z)`

With `|by_op[mul]| = 5000`, `|by_op[add]| = 20000`:

1. Phase 2 picks atom 1 (cheaper). Emits:
   - `Join { target: ?root, lookups: [ByOp(mul)] }`
   - `ExtractChild(?lhs, ?root, 0)`
   - `ExtractChild(?z, ?root, 1)`

   Now `?root`, `?lhs`, and `?z` are bound.

2. Phase 1 fires: atom 0 matches the `Plain { node: ?lhs } if
   bound[?lhs]` case. Emits:
   - `Join { target: ?lhs, lookups: [ByRepr(?lhs), ByOp(add)] }`
   - `ExtractChild(?x, ?lhs, 0)`
   - `ExtractChild(?y, ?lhs, 1)`

Atom 0 never scans `by_op[add]` at full size: it only intersects
within `?lhs`'s class. The eager pass caught it because `?lhs` was
bound by atom 1's child extraction.

### Why This Composes with Semi-Naive

For variant `i`, we pass stats where each atom carries its own
driver-scan cardinality *for this flavor*, set by its mode: atom `i`
gets its delta-bucket size (tiny), atoms `< i` get `full − delta`, and
atoms `> i` get full. This lets the static cost model prefer atom `i`
when the remaining selectivity terms do not make another atom cheaper.
Runtime scheduling can instead choose from concrete cursor lengths for
each partial binding.

This is necessarily **per-atom, not per-op**: two atoms sharing an op
can have different modes in one flavor (e.g. `(f (f x y) z)`, variant 1:
atom 0 is `full − delta`, atom 1 is `delta`, both op `f`). A per-op
cardinality map cannot represent that: one number for `f` would mis-size
one of the two atoms. So `IndexStats` carries a per-atom override
(`atom_card[atom_id]`) that `variant_stats` fills for every join atom;
`estimate_cost` reads it, falling back to `op_card` (the naive default,
where every atom of an op reads the same full bucket).

The per-atom override answers only the base relation-size part of the
cost. The static scheduler also uses fan-out statistics and optional
cross-index samples. Runtime mode reads concrete bucket lengths while a
partial match is live. Semi-naive mode composes with all three because
`VariantIndex::mode(atom_id)` selects the same full/delta slice regardless
of when that atom is chosen.

### Mode Lives on the Index, Not the Plan

The plan says *what* to look up (`ByOp(add)`, `ByChildPos(?x, 0)`).
It does not say *where* to look. The variant context decides that.

The matcher is given a small bundle instead of the raw `IndexStore`:

```rust
struct VariantIndex<'a, Cfg: EGraphConfig> {
    full:       &'a IndexStore<Cfg>,
    delta:      &'a IndexStore<Cfg>,
    delta_atom: Option<usize>,   // None = naive (everything full)
}
```

This is **not a new abstraction**. It is exactly the context one
variant needs: the two indexes and which atom is the delta atom.
Equivalent to passing `run_variant(plan, full, delta, i)`.

When the matcher reaches an atom's `Join` step, it computes that
atom's mode by comparing the step's `atom_id` to `delta_atom`:

- `atom_id == delta_atom` → **delta**: cursors read delta slices.
- `atom_id <  delta_atom` → **full ∖ delta**: cursors are `Difference`
  combinators (full slice minus delta slice).
- `atom_id >  delta_atom` (or `None`) → **full**: cursors read full
  slices.

The plan is immutable and mode-agnostic. `LeapfrogJoin` is unchanged.
The mode is realized purely in *which cursors get built* for that
join: see "How a Variant Executes".

### `atom_id` on `Step::Join`

`Step::Join` carries a stable
`atom_id: usize`, the atom's position in the compile-time numbering
(left-to-right, bottom-up pattern traversal). The scheduler stamps it
during planning (it knows which `RAtom` it's emitting). It is the bridge
between the **fixed numbering** that defines the variants and the
**execution order** the scheduler chooses per variant per round (next
section). At execution it selects each atom's index mode (delta / full /
full ∖ delta). At planning it also keys the per-atom cardinality
(`atom_card[atom_id]`) that `estimate_cost` reads, so two same-op atoms
in one flavor are costed independently. (It does *not* alter the shape of
the steps emitted for an atom: only their cost and, at run time, their
cursor flavor.)

Note: when the eager pass resolves an atom whose node is already bound
(the `ByRepr ∩ ByOp` case), that step still carries the atom's id, so
its mode is determined the same way. This applies to **variadic** atoms
(A/AC/ACI) too: when a variant drives from an enclosing atom and binds a
variadic child via `ExtractChild`, `emit_variadic_join` must still emit a
`ByRepr ∩ ByOp` re-join carrying the atom's id: otherwise the atom has
no `Step::Join` and its variant mode (notably `full ∖ delta`) is never
applied, and the parent-driven variant re-discovers matches the
delta-driven variants already own. That breaks the disjoint-partition
contract and can change operational change counts; direct disjointness
tests therefore pin it even when repeated equality merges happen to be
semantically idempotent.

### Per-Variant Scheduling

At match time (rounds ≥ 1), for each rule, one variant per join atom
(`saturate_semi` / `run_rule_variant`):

```
for di in join_atom_indices(&rule.query) {
    let stats = variant_stats(&rule.query, di, &full, &delta);
    let plan  = schedule_with_stats_sampled(&rule.query, &stats, &sampler);
    let view  = VariantIndex::variant(&full, &delta, di);
    run_query_scheduled(&rule.query, &plan, eg, &view, globals);
}
```

`join_atom_indices` is the join (relation-scanning) atoms only:
`Eq`/`EqGlobal`/`Pred` are excluded (no delta); `Lit` and `LitBind` are
included because they scan the literal relation. A rule with no join atoms
falls back to a single naive-view run so its matches are never missed.

Re-scheduling per variant is O(k²) in atom count. Different variants can
produce different plans: `variant_stats` gives atom `di` its delta
cardinality, while the other atoms keep their full / full ∖ delta sizes.

### What Changes, What Doesn't

Unchanged:

- The static scheduler's eager/pick-cheapest algorithm. It is invoked per
  variant with different base cardinalities.
- `LeapfrogJoin`: unchanged. Generic over `SortedCursor`; instantiated
  with `Base` or `Difference<Base, Base>` per join.
- The base cursor interface and `SortedVecCursor`: unchanged.
  Exclusion is a separate `Difference` combinator, never baked in.
- The step shapes `emit_atom` produces for an atom: unchanged.

Changed (small, localized):

- `IndexStats` has `atom_card: HashMap<atom_id, usize>` beside
  `op_card`; `estimate_cost` takes `atom_id` and reads `atom_card` first,
  falling back to `op_card`. This is the one cost-model difference from
  naive: see "Why This Composes with Semi-Naive".
- `Step::Join` carries `atom_id`.
- `run_join` has a mode-branch (it builds full / delta / `Difference`
  cursors for this atom, then runs the generic leapfrog).
- The pull-based `MatchIterator` stays full-only (naive); semi-naive
  runs on the push path (`run_query`).

## How a Variant Executes

This section pins down three things the design depends on: how the
fixed atom numbering survives dynamic scheduling, why a whole atom
shares one mode, and how `full ∖ delta` cardinality is known without
traversal.

### Fixed Numbering vs Dynamic Execution Order

Two orderings coexist and must not be conflated:

- **Atom numbering** `0..k-1`: fixed at compile time by the pattern
  traversal. The variant decomposition is defined *over this
  numbering*: variant `i` makes atom `i` delta, atoms `[0, i)` full ∖
  delta, atoms `(i, k)` full.
- **Execution order**: fixed by the per-round plan in `Static`, or chosen
  at decision points per partial binding in `Runtime`/selected `Auto`.

These are independent. The bridge is `Step::Join.atom_id`, the atom's
*stable number*. When execution reaches a join, its mode is computed as
`compare(atom_id, i)`: a pure function of the number and the variant,
**independent of where that join sits in execution order**.

Why this is correct regardless of order: a variant is a conjunctive
query with a per-atom membership restriction (`n_i ∈ Δ`, `n_{j<i} ∉ Δ`,
`n_{j>i} ∈` full). The *result set* of a conjunctive query is
invariant under join-execution order: reordering changes speed, not
the set. So mode-by-number is sound for any order the scheduler picks.

Execution order matters only for discovery cost. Feeding the scheduler
delta cardinality for atom `i` makes that small base relation visible to
the cost model, but fan-out/selectivity can still make another atom the
cheaper driver. Either order produces the same variant result set.

### Why a Whole Atom Shares One Mode

An atom binds **one** node `n`: the leapfrog *intersection* of its
lookups (`by_op[f] ∩ by_child_pos[(c,0)] ∩ …`). The mode restricts
that one node: delta (`n` is tracked), full∖delta (`n` is not tracked),
or full.

Restricting the *intersection* to/from `Δ` distributes over the
operands. With `A = by_op[f]`, `B = by_child_pos[(c,0)]`:

- delta: `(A∩Δ) ∩ B = (A∩B) ∩ Δ = (A∩Δ) ∩ (B∩Δ)`. Restricting **one**
  operand or **all** gives the same set.
- full∖delta: `(A∖Δ) ∩ B = (A∩B) ∖ Δ = (A∖Δ) ∩ (B∖Δ)`, likewise.

So the mode is semantically a **property of the atom (its node)**, and
applying it to one cursor would suffice. We apply it **uniformly to all
of the atom's cursors** for one reason: `LeapfrogJoin` holds a
`Vec<C>` of a single cursor type, so an atom's join must be all-`Base`
or all-`Difference`. The set identities above show that applying the
restriction to every operand preserves the intersection. Its runtime cost
still depends on the relevant delta buckets.

### Sizing `full ∖ delta` Without Traversal

The scheduler needs each atom's cardinality up front (`estimate_cost`
reads the per-atom `atom_card`, which `variant_stats` fills). For a
`full ∖ delta` atom (executed via a `Difference` cursor that filters on
the fly), this looks problematic, but its size is known **analytically**,
no scan:

For every index key `k`, `delta[k] ⊆ full[k]`. Both indexes are built
from the same post-rebuild e-graph, both skip `FLAG_SUBSUMED`, both are
deduped, so every delta entry also appears in full. Therefore:

```
|full ∖ delta|[k]  =  |full[k]|  −  |delta[k]|
```

an `O(1)` subtraction of two known bucket lengths. The `Difference`
combinator filters during *iteration*, but its *cardinality* is exact
without a cursor traversal. `variant_stats(rule, i, full, delta)` uses this directly:

| atom position | per-atom card (`atom_card[j]`) fed to scheduler |
|---|---|
| `== i` (delta)        | `|delta.by_op[op]|`                       |
| `<  i` (full ∖ delta) | `|full.by_op[op]| − |delta.by_op[op]|`    |
| `>  i` (full)         | `|full.by_op[op]|`                        |

So the scheduler sees the measured delta base cardinality and an exact
base cardinality for full ∖ delta atoms, all from length arithmetic.
Other selectivity terms still participate in the driver choice. The value is keyed by **atom**
(`atom_card[j]`), not by op, so same-op atoms in one flavor are sized
independently.

## Interaction with Rebuild

The existing `EGraph::rebuild()` already walks changed nodes and
recanonicalizes them. Semi-naive reads three log points, all pushing
into the `EGraph::touched` vector:

- **Fresh nodes**: `register_if_fresh` fires exactly once per
  newly-created node and pushes the node id there.
- **Recanonicalized nodes**: the cache `recanonize_node` methods
  detect when a node's canonical `(op, children)` form changes (the
  `new_hash != old_hash` / children-changed early-return) and push the
  node id immediately after that check, so unchanged nodes are not
  logged. The id is threaded out via a `&mut Vec<G>` out-param, the
  same mechanism by which `collisions` is passed through.
- **Absorbed class members**: `merge_in_classes` pushes the absorbed
  side's member nodes on every merge while the semi-naive driver has
  merge tracking enabled, so class growth that recanonicalizes nothing
  still reaches the next round's delta.

The touched log is append-only per round, cleared at round
boundaries, and materialized into delta `DenseSpanMap` buckets at the start of
each match phase. Mechanically it is a scratch `Vec<Cfg::G>` field on
`EGraph`, exactly like the existing `collisions`, `g_buf`, and
`mset_buf` fields: cleared at the start of a round and threaded by
`&mut` into `recanonize_node`.

### Not To Be Confused With `has_history` (Proofs)

The cache `recanonize_node` methods already do a copy-on-first-
recanonicalize **for proof reconstruction**, unrelated to semi-naive.
The touched-log push co-locates with it (both sit right after the
no-change early-return) but the two are independent and behave
differently:

| | `has_history` / history-save | touched-log push |
|---|---|---|
| purpose | save original node for proof reconstruction | record change for the delta index |
| store | `self.history` (per-cache, `Option`, `PROOFS` only) | `EGraph::touched` (global scratch `Vec`) |
| marker | `has_history()` per-node tag bit | none |
| condition | `PROOFS && !has_history()` | unconditional |
| frequency | once while the history bit remains set; restore can roll it back | every round the node's canonical form changes |

The touched-log push is **not** conditioned on `has_history()`: a node
that changes in three different rounds must appear in the delta three
times, once per round, whereas its original is saved only on the first
recanonicalization in the current retained history. They share only the
change-detection location.

## Correctness Invariant

> For delta-eligible rules, the log covers every tuple-level or
> class-membership event needed to expose a newly available match.

Formally: for every node N in the e-graph after the round's rebuild:

- If N was freshly created this round → N ∈ delta.
- If N existed before but its canonical form changed due to a merge
  → N ∈ delta.
- If N belongs to the class absorbed by a merge while merge-member tracking
  is enabled → N ∈ delta, even when its canonical form is unchanged.
- Otherwise there is no requirement that N be absent: the log may be a
  conservative superset.

For rule shapes accepted by the delta path (`needs_naive_match == false`),
these conditions are the
implementation's coverage argument that every newly enabled match appears
in at least one variant. Node-equality and fixed-global shapes do not satisfy
that argument and run against the full view instead. Differential and direct
variant tests provide finite evidence; there is no machine-checked transition
theorem.

A superset preserves coverage and the k variants still partition the
delta-involving tuples, but it can re-emit a tuple that matched in an earlier
round and therefore add work or operational change counts. Missing an enabling
event is a semi-naive completeness/equivalence failure, not an equality-
soundness failure.

### Where Spurious Entries Come From

The recanonicalization log-push must be conditioned on **actual
canonical-form change**, not just visitation. In the current rebuild
pass, a node is visited whenever one of its e-classes participates in
a merge, but if the merge preserves its canonical form (e.g., both
endpoints were already in the same class), no change occurred. The
existing `new_hash == old_hash` short-circuit in the cache
`recanonize_node` methods is the right point for the log-push.

## Interaction with Semi-Persistence

The touched log is round-local scratch, not part of the persistent
e-graph state. It is a plain `Vec<Cfg::G>` (no `TRACK` parameter):
cleared after each round's snapshots are built and on `restore`. Because matching
for a round happens entirely between rebuild and the next round
boundary, the log never needs to survive a `mark`/`restore`: after a
restore, the loop simply starts the next round with an empty log and
repopulates it during the following rebuild. No semi-persistent
coordination is required.

## Implementation Status

This design is **implemented**: `saturate_semi` in `egraph/src/saturate.rs`,
selectable via `Interpreter::set_strategy(SaturationStrategy::SemiNaive)` and
the `--use-semi-naive` CLI flag (the default is naive).

This chapter is the **rationale and correctness** reference (why the
decomposition is sound, how it composes with flattening and the
scheduler, where the savings come from). Work intentionally left for
later (the configurable mutable index backend, the delta-size fallback,
the trigger pre-filter, and current comparative Criterion campaigns) is
tracked in
[`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md).

## Open Questions

1. **Which full-index backend wins?** Decision deferred until the
   end-to-end Criterion comparison is current. There is no supported backend
   recommendation from probe microbenchmarks alone.

2. **Cost model for `FullMinusDelta`.** Each filter operation performs a
   forward seek in the paired delta cursor: `O(log d)` for the distance that
   particular seek advances, while a full sequential scan advances through at
   most `|full| + |delta|` entries. The scheduler currently prices the exact
   base cardinality `|full| - |delta|` but not this gap-dependent filtering
   work. Whether modeling it changes atom order usefully requires seek
   instrumentation and the end-to-end Criterion harness.

3. **Per-variant plan caching.** With k variants per rule, should the
   k scheduled plans be cached and reused across rounds, or
   re-scheduled each round? The current implementation re-schedules; caching
   would save scheduler cost but risks stale estimates. Add it only with
   comparative Criterion evidence.

4. **Trigger filtering.** A `root_ops: HashSet<O>` per `PreparedRule`
   could skip rules whose join atoms' ops have no delta this round: a
   cheap pre-filter that avoids the entire variant loop for many rules
   when the delta is sparse. Worth implementing as a hardening step now
   that the core fan-out is validated; see
   [`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md).

5. **Delta size bounds.** If a single round's merge cascade
   recanonicalizes a large fraction of the e-graph, `|delta|`
   approaches `|full|` and the semi-naive savings vanish. Should the
   loop fall back to the naive path in that case? Probably, with a
   threshold like `|delta| > α · |full|` for some α ∈ (0, 1).
   Design TBD.

6. **`ByContains` driver-narrowing for variadic atoms (IMPLEMENTED).**
   `IndexStore` builds a `by_contains[child_repr] → parents` index every round.
   A variadic atom (A/AC/ACI) whose *element* is already bound but whose *node*
   is not (e.g. `(g x)` then a side condition `(add x ..rest)`) is now compiled
   to drive from `by_op[op] ∩ by_contains[e]` for each already-bound element
   `e`, instead of scanning the full `by_op` bucket and filtering in the
   decompose step. This is the variadic analogue of the fixed-arity
   `ByChildPos` intersection that `Plain` already does, and it is a sound
   membership-only filter (the subsequent `DecomposeAC`/`ExpandA`/`DecomposeACI`
   still does the precise multiplicity/position check). `emit_variadic_join`
   takes the atom's element `PatVar`s and adds one `ByContains { child }`
   lookup per bound element. This removes unrelated variadic nodes from the
   candidate bucket; work still scales with parents that actually contain the
   bound class. `by_contains_narrows_variadic_driver` tests independence from
   unrelated distractors, and the differential suite exercises A/AC/ACI under
   both strategies (including `PROOFS=true`).

   `estimate_cost` accounts for the narrowing with measured fan-out and,
   when enabled, cross-index sampling. Runtime scheduling can read the concrete
   cursor length for the current binding. These are estimates/measurements used
   for ordering, not a guarantee that a fully bound variadic atom always drives.
   Tests:
   `bound_element_discounts_variadic_cost`,
   `scheduler_drives_variadic_from_bound_element`.

## Testing Strategy

Correctness is supported by **differential testing** against the
naive path: the same rules and input run both ways, with semi-naive
required to reach the same observed result. This is finite validation, not
a universal proof. As built:

- **Observational equivalence** (the core check): build two `EGraph`s
  identically, saturate one naively and one semi-naive, and assert the
  equivalence partition over the original node ids is identical. Used
  in the targeted scenarios (commute, multi-rule, constant fold,
  two-level fold, AC, ACI) and in the randomized proptest.
- **Randomized proptest**: a random input term + a random subset of a
  rule pool, naive vs semi-naive, asserting the partition agrees
  (512 configured cases).
- **Whole-corpus differential**: every `.egg` integration test runs
  under *both* strategies and must reach the same `EXPECT` outcome, so
  semi-naive is checked against naive across the entire program corpus
  (arithmetic, AC multiplicity, ACI, extraction, folding, subsumption,
  globals, push/pop).
- **Disjointness** (the property final-state equivalence may not see):
  in one round, the variant
  match sets must be pairwise disjoint and their union must equal the
  naive matches involving a delta node. Tested directly; this also protects
  operational change counts for actions that are not reported idempotently.
- **Building blocks**: the `Difference` cursor (proptest), touched ⊇
  changed-set, delta == full ∩ touched.
- **Restore-safety and empty-delta**: `mark`/`restore` clears the
  touched log; a saturated graph re-saturates as a one-round no-op.
- **Same-op / variadic ordering** (the cases generic ordering can break):
  same-op disjointness at 2 and 3 atoms; AC same-op; nested-variadic
  saturation; sibling shared-var; A-sequence (nested and top-level);
  congruent-duplicate survivors; subsumption mid-round; `PROOFS=true`
  differential. All assert the partition still matches naive.
- **Dynamic-scheduling stats**: `variant_stats` gives two same-op atoms
  *distinct* per-atom cardinalities in one flavor
  (`variant_stats_per_atom_cardinality`); a bound element discounts a
  variadic atom's cost; the scheduler drives a high-cardinality variadic
  atom from a bound element via `ByContains`.
- **Match-work instrumentation**: `SatResult.match_steps` (one count per
  partial-match extension) lets tests assert semi-naive explores fewer
  steps than naive on a focused fixture, and that `ByContains` keeps work
  independent of unrelated distractor count in its fixture.

Note: a strict *structural isomorphism* check is **not** used as the
differential oracle. Node count and per-class node multiset are
order-dependent (the append-only node store and merge-representative
choice cause two equivalent runs to materialize different numbers of
congruent transient nodes), so the valid invariant is the equivalence
*partition*, not structural identity. (The randomized proptest
surfaced exactly this.)

The end-to-end `saturate_bench` and corpus Criterion harnesses exist.
Current backend or speed claims still require a same-revision campaign with
confidence intervals.

## References

- Abiteboul, Hull, Vianu, *Foundations of Databases* (1995), Chapter
  13: the canonical treatment of semi-naive evaluation in Datalog,
  including why built-in predicates are excluded from the
  decomposition.
- Zhang, Z. et al. "Better Together: Unifying Datalog and Equality
  Saturation" (PLDI 2023): modern application to e-graph engines.
- [`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md): the remaining,
  intentionally-deferred work (configurable index backend, delta-size
  fallback, trigger pre-filter, and performance campaigns).

---
[← Ch 17: Interpreter and Saturation Loop](17-interpreter.md) · [Table of Contents](00-table-of-contents.md) · [Ch 19: Anti-Unification →](19-anti-unification.md)
