# Chapter 18 — Semi-Naive Evaluation

[← Ch 17: Interpreter and Saturation Loop](17-interpreter.md) · [Table of Contents](00-table-of-contents.md)

**Status**: implemented. Select with `saturate_semi` / the
`SaturationStrategy::SemiNaive` interpreter strategy / `--strategy
semi-naive` on the CLI. The default remains naive; there is no
automatic fallback. Deferred: delta-size fallback, trigger pre-filter,
and the pluggable B+tree full-index backend (see Open Questions).
**Scope**: e-matching loop and `IndexStore`.
**Depends on**: [Ch 6: Index](06-index.md), [Ch 7: Leapfrog Triejoin](07-leapfrog.md), [Ch 8: Query Compilation](08-query-compilation.md), [Ch 9: Pattern Matching](09-pattern-matching.md).

## Motivation

The naive saturation loop (Chapter 17) rediscovers the same matches every round.

Each round:

1. Apply all accepted rewrites from the previous round's matches.
2. Rebuild the `IndexStore` from the full e-graph.
3. For every rule, run its compiled query plan over the entire
   `IndexStore`, producing every match that exists in the e-graph.
4. Dedup against matches we've already applied. Keep the rest for
   next round.

Step 3 is the bottleneck. In a converging saturation over N rounds,
the graph grows roughly monotonically: if round K has |M_K| matches,
then |M_0| ≤ |M_1| ≤ … ≤ |M_N|. The total match-discovery work is
∑ |M_K| ≈ O(N · |M_N|), even though the union of all *new* matches
across rounds is just |M_N|.

On a saturation with 100 rounds and 1M final matches, that's ~98%
wasted work in the outer loop of e-matching — rediscovering matches
the engine has already applied.

Semi-naive evaluation fixes this by running, each round, only the
matches that could not have existed before that round. In steady state
this shrinks per-round match work from O(|full|) to O(|delta|), where
`delta` is the set of nodes that were added or changed this round.

## The Key Invariant

A match is *new this round* iff **at least one of its atoms is new
this round**. Contrapositive: if every atom of a match was present in
the previous round's full graph, the match already existed last round
and was already discovered.

Call the set of new-or-changed nodes `delta`, and the full set of
nodes `full` (which contains `delta`). For a k-atom rule, the set of
new matches is precisely:

```
new_matches = { (n_1, …, n_k) ∈ full^k that satisfy the rule's pattern
                AND at least one n_i ∈ delta }
```

A naive way to compute `new_matches` would be "compute all matches,
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

**Why this partitioning is sound and complete.** Every match has a
well-defined "first new atom" — the smallest position `i` such that
atom `i` is in `delta`. By construction, atoms `< i` are not in
`delta` (they're in `full \ delta`). Variant `i` is the unique
variant that matches this match:

- Variant `i'` with `i' < i`: atom `i'` must be in `delta`, but by
  definition of "first new atom," atom `i'` is not in `delta`. Fails.
- Variant `i`: atom `i` is in `delta` (match ✓), atoms `< i` are not
  in `delta` (the `full \ delta` restriction holds), atoms `> i`
  unrestricted. Matches.
- Variant `i'` with `i' > i`: atom `i` must be in `full \ delta`, but
  atom `i` is in `delta` (that's what made `i` the first new atom).
  Fails.

Every match with at least one new atom is found by exactly one
variant. Matches with zero new atoms — i.e., all atoms in
`full \ delta` — are never found, which is correct: these are old
matches already emitted in prior rounds.

The `full \ delta` restriction on atoms `< i` is non-negotiable.
Without it, a match with multiple new atoms (new atoms at positions
`i < j`) would be found by variant `i` *and* variant `j`, producing
duplicate emissions.

### Which Atoms Count as Positions

The "k atoms" above are the **join-producing atoms** — those that
scan an index to generate candidate nodes. In our `RAtom` enum these
are `Plain`, `AExact`, `APrefix`, `ASuffix`, `ABoth`, `ACExact`,
`ACSub`, `ACIExact`, `ACISub`, `Lit`, and `LitBind`. The built-in
constraint atoms `Eq` and `EqGlobal` are **excluded** from the
variant count: they do not scan a relation, they only check or
propagate bindings between already-bound variables. They have no
`delta` because they are not extensional indices.

This mirrors textbook semi-naive Datalog, where only IDB/EDB body
atoms participate in the decomposition and built-in predicates
(arithmetic, equality) are evaluated directly without a delta. The
soundness argument is unchanged: every new match must involve at
least one new *node*, every node is generated by a join atom, so
ranging the variant loop over join atoms alone still catches every
new match. Constraint atoms are applied as filters uniformly across
all variants — excluding them changes nothing about which matches a
variant finds, only how many redundant variants we would otherwise
run.

## Worked Example: Nested Patterns and Flattening

The invariant above talks about k atoms in abstract. For our e-graph,
atoms come from flattening nested patterns — so it's worth walking
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

The flattening pass (`flatten_surface`) and resolver together produce
a `ResolvedQuery` with one atom per pattern enode:

- **Atom 0**: `?root = mul(?lhs, ?rhs)` (the outer mul)
- **Atom 1**: `?lhs = add(?x, ?y)`
- **Atom 2**: `?rhs = mul(?z, ?y)`

The nesting has become **join constraints between atoms** via shared
pattern variables:

- Atom 0's `?lhs` ≡ atom 1's binding target (parent-child link).
- Atom 0's `?rhs` ≡ atom 2's binding target.
- Atom 1's `?y` ≡ atom 2's `?y` (non-linear join).

After flattening, there is no "nested" atom anymore — there are three
atoms sitting in a flat list, joined by shared variables. **Semi-naive
operates on this flat list**; it never sees the pattern tree.

### Matches are Node-Tuples

A match of R is a 3-tuple of nodes `(n_0, n_1, n_2)` such that:

- `n_0` is a `mul` node.
- `n_1` is an `add` node whose e-class equals `n_0`'s first child.
- `n_2` is a `mul` node whose e-class equals `n_0`'s second child.
- `n_1`'s second child e-class equals `n_2`'s second child e-class
  (the `?y` constraint).

"Atom `i` is new this round" means the node `n_i` was added or
recanonicalized during the current round.

### The Three Variants

For this 3-atom rule, semi-naive runs three plan variants. In each,
one atom is delta-restricted (its driving index reads from `delta`)
and the lower-indexed atoms are restricted to `full \ delta`.

**Variant 0**: outer mul is new.

| Atom     | Restriction   |
|----------|---------------|
| 0 (mul)  | **delta**     |
| 1 (add)  | full          |
| 2 (mul)  | full          |

The scheduler drives from `delta_by_op[mul]` (atom 0's index,
delta-restricted) because its cardinality is tiny. For each new
outer-mul, it probes atom 1 and atom 2 using the
`by_child_pos` lookups on their respective full indices.

**Variant 1**: inner add is new, outer mul is old.

| Atom     | Restriction       |
|----------|-------------------|
| 0 (mul)  | **full \ delta**  |
| 1 (add)  | **delta**         |
| 2 (mul)  | full              |

Now the scheduler drives from `delta_by_op[add]` (atom 1's delta-
restricted index). For each new add-node, it looks up its parents via
`by_child_pos[(c, 0)]` — but with mode `FullMinusDelta`, so any
parent mul that is itself in the current round's delta is skipped.
Atom 2 is probed normally from full.

**Variant 2**: inner mul is new, everything above is old.

| Atom     | Restriction       |
|----------|-------------------|
| 0 (mul)  | **full \ delta**  |
| 1 (add)  | **full \ delta**  |
| 2 (mul)  | **delta**         |

Drive from `delta_by_op[mul]` restricted to the inner-mul position.
Probes to the outer mul (atom 0) and the add (atom 1) both use
`FullMinusDelta` cursors.

### Why This Partitions Matches Correctly

Consider a new match where **all three** nodes happen to be in delta
this round: `(n_0 ∈ delta, n_1 ∈ delta, n_2 ∈ delta)`. This can
happen if the round added several fresh nodes that happen to align.

- **Variant 0** finds it: atom 0 ∈ delta ✓, atoms 1 and 2 unrestricted
  (both in full, trivially true since delta ⊆ full) ✓. ✅
- **Variant 1** rejects it: atom 0 must be in `full \ delta`, but
  `n_0 ∈ delta`. ✗
- **Variant 2** rejects it: atom 0 must be in `full \ delta`, but
  `n_0 ∈ delta`. ✗

The match is found exactly once, by variant 0 — the variant associated
with its leftmost new atom (position 0).

Now consider a mixed match where only atom 1 is new:
`(n_0 ∈ full \ delta, n_1 ∈ delta, n_2 ∈ full \ delta)`.

- **Variant 0** rejects it: atom 0 must be in delta, but
  `n_0 ∉ delta`. ✗
- **Variant 1** finds it: atom 0 ∈ full\delta ✓, atom 1 ∈ delta ✓,
  atom 2 unrestricted ✓. ✅
- **Variant 2** rejects it: atom 1 must be in full\delta, but
  `n_1 ∈ delta`. ✗

Again, found exactly once.

### Why the Upper Half Stays Unrestricted

Why not symmetric — why not restrict *both* halves (lower and upper)
to `full \ delta` around the one delta atom?

Consider `(n_0 ∈ full\delta, n_1 ∈ delta, n_2 ∈ delta)` — two new
atoms, both at positions ≥ 1.

With upper-half restriction (atom 2 forced to `full \ delta`):

- Variant 1 would require atom 2 ∈ full\delta, but `n_2 ∈ delta`. ✗

With our actual rule (upper half unrestricted):

- Variant 1: atom 0 ∈ full\delta ✓, atom 1 ∈ delta ✓, atom 2 any ✓. ✅
- Variant 2: atom 0 ∈ full\delta ✓, atom 1 ∈ full\delta? `n_1 ∈ delta`. ✗

So variant 1 correctly finds the match. Symmetric restriction would
miss it entirely — no variant would catch it.

The asymmetry exists because the partition is defined by
**leftmost new atom**. Variant `i` owns matches whose leftmost new
atom is at position `i`. For such a match:

- Atoms at positions `< i` must be old (otherwise the leftmost new
  atom would be at some `j < i`, and the match belongs to variant
  `j`, not `i`).
- Atom at position `i` is new by definition.
- Atoms at positions `> i` can be anything — their newness is
  *irrelevant to which bin this match falls into*, because they
  don't change what the leftmost new atom's position is.

Restricting positions `> i` would further split each bin into
sub-bins keyed on which higher positions are also new — that's
`2^k` variants instead of `k`. Linearity is what makes the algorithm
tractable.

### Atom Numbering vs Execution Order

A subtle but important point: **atom numbering** (used to define
"position `i`", variant `i`, lower-vs-upper) is separate from
**execution order** (chosen by the scheduler per variant).

The scheduler in Ch 8 picks atom order by selectivity. Within a
variant, it usually drives from the delta-restricted atom (smallest
cardinality) regardless of where that atom sits in the numbering.
Atom numbering is a stable reference for partitioning matches;
execution order is an implementation detail of how each variant is
evaluated.

What "execution order" means here precisely: the scheduler emits a
**fixed step sequence per variant per round**, chosen from that round's
runtime cardinalities. It is *dynamic across rounds and variants* (each
is scheduled afresh — see "Scheduling Is Dynamic, Every Round"), but it
is *not* re-decided mid-traversal per partial match. It does not need to
be: reordering atoms cannot change *which* matches a conjunctive query
yields (the result set is order-invariant), only the cost of finding
them — and within a chosen order, leapfrog already adapts to the actual
data per binding. So a single order picked from per-atom driver
cardinalities captures the win; nothing is gained by re-deciding the
order for each partial match.

Concretely, in variant 1 of the example above, the scheduler drives
from atom 1 (delta, tiny) first, even though atom 1 is "in the
middle" of the pattern tree. It then follows join constraints
upward to atom 0 and across to atom 2. The `FullMinusDelta`
restriction on atom 0 applies regardless of whether the scheduler
probed it first or last — it's a filter on atom 0's index, not an
ordering constraint.

### The Payoff

For this rule, naive matching each round scans `by_op[mul]` and
`by_op[add]` at their full sizes. Semi-naive runs three variants,
each with its driver restricted to that atom's delta index —
typically 1000× smaller than full. The total work per round drops
proportionally, while still finding every new match exactly once.

The flattener did the hard work of turning the pattern tree into a
flat join problem. Once that's done, semi-naive is *oblivious to
nesting* — it just picks which atom is delta-driven, using the same
k-variant machinery that would apply to a non-nested rule with k
independent atoms.

## Where the Savings Come From

In a leapfrog join, outer-loop cost dominates: you iterate the driver
atom's index, and for each element you probe the remaining atoms.
Probes are logarithmic (or near-constant with the B+tree cursor fast
path); iteration is linear in driver size.

The scheduler (Ch 8) already picks the driver by selectivity. With
semi-naive and typical round growth `|delta| / |full| ≈ 10⁻³` to
`10⁻²`, the delta-restricted atom is always the smallest in its
variant, and the scheduler drives from it.

- Variant `i`'s driver: atom `i`, restricted to delta. Outer loop
  size `|delta|`.
- Total outer-loop work per round: `k · |delta|` instead of `|full|`.
- Savings factor per round: `|full| / (k · |delta|)` — typically
  100×–1000× on converging saturations.

Note: the scheduler doesn't need to know about "delta" as a concept.
It sees smaller cardinalities for certain ops via `IndexStats` and
greedily picks the cheapest. Semi-naive falls out of providing the
right stats per variant.

## Worked Numbers: 4-Atom Pattern, 100K Full, 1K Delta

Concrete numbers grounded in the `seek_microbench` results make the
asymptotic argument concrete. Setup:

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

**Raw outer-loop speedup: 25×.**

### Comparison-Op Count (Including Inner Probes)

Each inner probe is a leapfrog seek into a ~200-entry slice after
the 100× join filter. Probe cost ≈ log₂(200) ≈ 8 comparisons. The
`FullMinusDelta` cursor wrapper adds O(log |delta|) ≈ 10 per
filtered step, applied only on atoms at positions `< i`.

| Variant | Driver | Inner probes | FullMinusDelta overhead | Total work |
|---------|--------|--------------|-------------------------|------------|
| 0       | 200    | 3 × 8 = 24   | 0 lower atoms           | ~4,800     |
| 1       | 200    | 3 × 8 = 24   | 1 lower × 10 × 200      | ~6,800     |
| 2       | 200    | 3 × 8 = 24   | 2 lower × 10 × 200      | ~8,800     |
| 3       | 200    | 3 × 8 = 24   | 3 lower × 10 × 200      | ~10,800    |
| **Sum** |        |              |                         | **~31,400**|
| Naive   | 20,000 | 3 × 8 = 24   | -                       | ~480,000   |

**Effective speedup: ~15×.** Lower than the 25× raw outer-loop
ratio because later variants pay more `FullMinusDelta` overhead —
but still a dominant win.

### Wall-Clock Estimates

Using the `seek_microbench` timings (per-seek cost at 100K entries:
~5 ns for B+tree with cursor fast path, ~30 ns for SortedVec):

| Backend        | Naive (per rule/round) | Semi-naive (per rule/round) | Speedup |
|----------------|------------------------|-----------------------------|---------|
| SortedVec      | ~1.8 ms                | ~72 μs                      | 25×     |
| B+tree (bulk)  | ~300 μs                | ~12 μs                      | 25×     |

The backend choice affects the absolute numbers (B+tree is ~6×
faster per probe) but **does not change the semi-naive speedup
ratio**, because both naive and semi-naive benefit proportionally
from cheaper probes. Backend selection and semi-naive are
independent optimizations.

### Sensitivity to Delta Size

Fix `|full| = 100K`, k = 4. Vary `|delta|`:

| delta        | Semi-naive outer | Naive outer | Raw ratio |
|--------------|------------------|-------------|-----------|
| 100          | 400              | 20,000      | 50×       |
| 1,000        | 800              | 20,000      | 25×       |
| 10,000       | 8,000            | 20,000      | 2.5×      |
| 25,000       | 20,000           | 20,000      | 1.0×      |
| 50,000       | 40,000           | 20,000      | **0.5× (slower)** |

**Threshold for semi-naive to help**: `k · |delta| < |full|`, i.e.,
`|delta| / |full| < 1/k`. For 4 atoms, that's 25%. Above that, the
k-variant overhead exceeds the savings — at which point falling back
to the naive path is the right move (see Open Questions).

For converging saturations where rounds add 0.1–1% new nodes,
`|delta| / |full| ≈ 0.001–0.01`, deep in the semi-naive win zone.

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

Speedup decays as `|full_driver| / (k × |delta_driver|)`. Even
10-atom patterns still see 10× speedup at this delta ratio.

### Saturation-Level Scaling

For a 100-round saturation with roughly uniform delta per round:

- Naive: each round rescans full at its current size. Work roughly
  `∑ round × |full_round| ≈ 2,000,000` outer iterations total.
- Semi-naive: each round does 800 outer iters. Over 100 rounds:
  80,000 outer iterations total.
- **Saturation-level speedup: 25×.** Matches the per-round ratio.

### Saturation Where It Wins Asymmetrically

Semi-naive wins hardest on saturations that do most of their growth
early and then converge slowly. Example: round 1 adds 100K nodes;
rounds 2–100 each add just 10.

- Naive: round 1 does 100K × 3 probes, rounds 2–100 each rescan the
  full (now-static) 100K. Work ∝ 100 × 20,000 = 2M outer iterations.
- Semi-naive: round 1 is degenerate (delta ≈ full, semi-naive should
  fall back to naive). Rounds 2–100 each do 4 × 10 = 40 outer
  iterations. Work ∝ 20,000 + 99 × 40 ≈ 24,000 outer iterations.
- **Saturation-level speedup: ~80×.**

The "tail rounds" cost almost nothing in semi-naive because delta is
tiny, but cost full scan in naive because the graph hasn't changed
shape. This asymmetry is why semi-naive is especially valuable for
saturations that reach a near-fixpoint long before converging fully.

### Caveats

These numbers assume **uniform selectivity across atoms**. Real
patterns have bottleneck atoms — one very rare op can drive the join
to near-linear in that atom's size, making naive already cheap and
cutting semi-naive's advantage. Typical real workloads see 10–50×
speedup in practice, not the theoretical 100×+ from uniform models.

The numbers also ignore dedup and match-application cost, which both
paths pay equally. Semi-naive changes the *discovery* cost; applying
matches and updating the e-graph is identical in both paths.

## The Three Index Flavors

Semi-naive requires three logical index flavors per index family
(`by_op`, `by_repr`, `by_child_pos`, `by_contains`):

| Flavor            | Content                       | Lifecycle                                       |
|-------------------|-------------------------------|-------------------------------------------------|
| `full`            | all nodes in the e-graph      | grows across rounds; rebuilt on `restore`       |
| `delta`           | nodes new/changed this round  | rebuilt each round from the touched log         |
| `full \ delta`    | old nodes only                | **derived view**; never materialized            |

`full \ delta` is a **derived view** — never materialized. It is
computed lazily by a `Difference` cursor *combinator* that is generic
over any two `SortedCursor`s (so it works for `SortedVecCursor` today
and `BPlusCursor` later — no backend coupling) and itself implements
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
index is materialized, and the base cursors stay untouched — exclusion
is layered on as a combinator, not baked into the cursor trait.

It is built **only** for `full \ delta` atoms (`j < i`); full and delta
atoms use bare base cursors. See "How a Variant Executes" for how the
two cursor types coexist without an enum or trait object.

### The Delta Index

The delta index exists for exactly one round. It's built from a
**touched log** — an append-only list of node ids that were either
created or recanonicalized during the round's rebuild phase. At the
end of each round:

1. Sort and dedup the touched log into `SortedVec<G>` values, keyed
   by the same hash-map keys as `full`.
2. Run e-matching with the k-variant fan-out.
3. After all rules have matched, discard `delta` (the entries merge
   into `full` naturally since `full` already contains these nodes by
   the time we reach matching).

The touched log is a single `Vec<Cfg::G>` field on `EGraph`,
populated during rebuild via an out-param threaded through
`recanonize_node` (one push per genuinely-changed node) and in
`register_if_fresh` (one push per freshly-created node). It is
round-local scratch, cleared at each round boundary. Duplicates are
removed by the sort-dedup in step 1, so no separate hash set is
needed.

**The delta index is always `SortedVec<G>`.** No backend flexibility
needed — it's built once, read once, discarded. The access pattern is
pure outer-loop iteration, which favors contiguous memory.

### Global, Not Per-Cache

The delta is stored **globally** — one delta `IndexStore` for the whole
e-graph, mirroring the global full `IndexStore`. It is *not* partitioned
per node cache. This falls directly out of how indexing works today:

- The full `IndexStore` is global and keyed by **crosscutting
  attributes** — `by_op[op]`, `by_repr[repr]`, `by_child_pos[(repr,
  pos)]`, `by_contains[repr]`. It is built by scanning every node id
  `0..node_count` once. It is not organized by arity-class.
- The node **caches** (`FixedArityCache` for arity 0–3 / commutative,
  `VariableArityCache` for A/AC/ACI, `LitCache`) partition nodes by
  arity-class for storage and hash-consing. That partitioning is
  **orthogonal** to the index keys: a single `by_op[mul]` bucket can
  draw nodes from `Plain2` and `C` caches; a `by_child_pos` bucket
  crosscuts every cache.

So even though the touched *events* originate inside per-cache
`recanonize_node` calls, a per-cache delta would have to be re-bucketed
into the global crosscutting keys before matching could use it — buying
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

- **Read-heavy, seek-driven**: every probe in the k-variant join hits
  the full index at a specific key (`seek` + `step`, not scan).
- **Grows across rounds**: bulk-rebuilt from scratch each round today;
  an incrementally-maintained backend (via `insert`) is the deferred
  alternative.
- **Occasionally rolled back**: if the user calls `mark`/`restore`,
  the full index must return to its earlier state — either by diff-log
  replay or by bulk rebuild from the e-graph.

This is where the backend choice becomes interesting.

## Backend Choice for the Full Index

Today the full index is **Option A below**: `SortedVec<G>`, bulk-rebuilt
each round — the same index the naive loop uses. Semi-naive's match-work
savings are independent of this choice. Making the backend configurable
(so the full index could instead be maintained incrementally) is
**deferred**; the analysis here records the three candidates and why
choosing between them is an empirical, workload-dependent question that
microbenchmarks alone cannot settle.

### Option A: `SortedVec<G>`, bulk-rebuilt each round

What the current `IndexStore` does. Zero incremental-maintenance cost,
zero semi-persistence overhead. Pays O(|full|) per round to rebuild.

- **Pro**: simplest to implement — no new machinery; regression path
  against the existing naive loop.
- **Pro**: perfectly sorted arrays with no tombstones, great constants
  for leapfrog outer iteration.
- **Con**: rebuild cost scales with total node count, not delta size.
  Semi-naive's win on *match* work is partially offset by per-round
  *rebuild* cost.
- **Con**: per-seek cost is O(log n) with no fast path; binary search
  on 1M entries is ~40 ns per seek in the microbenchmark, mostly cache
  misses.
- **When it wins**: small graphs, or saturations where per-round work
  is match-bound rather than rebuild-bound.

### Option B: `BPlusTreeSet<G, TRACK=false>`, incremental

B+tree with semi-persistence disabled. Incremental `insert` maintained
across rounds via the same touched-node log points that feed the delta
index (`register_if_fresh` + the `recanonize_node` change check).
Rebuilt from scratch on `restore` (no diff log to replay).

- **Pro**: amortizes index maintenance across rounds — per-round cost
  is O(|delta|) instead of O(|full|). Matches the match-work savings
  from semi-naive on the rebuild side too.
- **Pro**: cursor fast-path makes probes constant-time for small
  skips (~5 ns/seek in `seek_microbench`, ~8× faster than SortedVec at
  1M entries) — and leapfrog is seek-heavy.
- **Con**: `restore` triggers a full rebuild from the e-graph. Only
  costly if workloads backtrack often.
- **Con**: slightly higher constant factor than SortedVec for tiny
  indices (<100 entries).
- **When it wins**: large graphs with many rounds and rare `restore`.

### Option C: `BPlusTreeSet<G, TRACK=true>`, semi-persistent

Same as B, plus diff-log tracking. `restore` rolls the tree back in
O(k) where k is the number of mutations since the mark — no rebuild
needed.

- **Pro**: `restore` is O(k) where k is mutations since mark, not
  O(|full|). The right choice if backtracking is frequent.
- **Con**: every mutation pays a diff-log cost (one u32 per captured
  node per frame, plus one 256-byte node copy on first capture per
  frame). For a tree that doesn't get rolled back, this is pure waste.
- **Con**: memory grows with mutation count between marks.
- **When it wins**: workloads with frequent `mark` / `restore` and a
  non-trivial full-index state that would otherwise be expensive to
  rebuild.

### Why This Is an Empirical Question

The choice is **workload-dependent** and cannot be resolved from
microbenchmarks alone. The three axes that matter are:

1. **Graph size at steady state.** Favours B/C at large sizes (log-n
   seek beats linear rebuild); favours A at small sizes (constant-
   factor overhead of tree structure).
2. **Round growth rate.** Favours B/C when `|delta| / |full|` is
   small, because incremental insertion is `O(|delta|)` while bulk
   rebuild stays `O(|full|)`. Favours A when growth is bursty and
   each round roughly doubles the graph.
3. **Backtracking frequency.** Favours C when `mark`/`restore` is
   called often and the full index is large. Favours A or B when
   backtracking is rare — the diff-log overhead doesn't pay for
   itself.

Microbenchmarks answer parts of (1) but nothing about (2) or (3).
Those need a full saturation loop with representative rulesets.

### Status

Option A is what ships: the full index is `SortedVec`, bulk-rebuilt each
round. Making the backend a type parameter of `IndexStore` (a small
`IndexBackend<G>` trait — `from_sorted`, `insert`, `cursor`, `len`),
building the end-to-end harness needed to choose between A/B/C honestly,
and optionally exposing the choice as a user config are deferred and
tracked in
[`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md).

## Interaction with the Existing Scheduler

Semi-naive needs **no change to the scheduling *algorithm*** (the
eager-pass + pick-cheapest loop in `schedule.rs`). The only stats change
is how cardinality is keyed: per-atom (`atom_card`) instead of per-op, so
each variant can feed the same scheduler its own per-flavor numbers and
get back a plan ordered for that flavor. The algorithm that consumes
those numbers is identical for naive and semi-naive (see "What Changes,
What Doesn't").

### Scheduling Is Dynamic, Every Round, in Both Evaluators

Atom order is **never precomputed and cached**. It is recomputed from
the *current* index cardinalities at the point of use, in both the naive
and the semi-naive loop. Concretely (see `saturate.rs`):

- **Naive** (`saturate`): each round calls `eg.rebuild()`, rebuilds the
  index with `IndexStore::build(eg)`, derives fresh stats with
  `IndexStats::from_index(&index)`, and `apply_rule` calls
  `schedule_with_stats(&rule.query, &stats)` per rule. The plan for a
  rule in round N is built from round N's cardinalities — a rule whose
  ops grew or shrank since round N−1 may get a different atom order.

- **Semi-naive** (`saturate_semi`): each round rebuilds `full` (and, for
  rounds ≥ 1, `delta`). Round 0 schedules naively. Rounds ≥ 1 run, per
  rule, **one independently-scheduled plan per variant**: for each join
  atom `i`, `variant_stats(rule, i, &full, &delta)` computes that
  flavor's per-atom cardinalities and `schedule_with_stats` produces a
  plan from them. So the K variants of one rule may each order their
  atoms differently, and all of them may differ from the previous round.

Nothing is memoized across rounds or across variants — re-scheduling is
O(k²) in atom count (k typically 2–6), microseconds, and re-running it is
strictly better than reusing a stale order as cardinalities shift. (Plan
*caching* is an explicit non-goal; see Open Question 3.)

The runtime information the scheduler consumes is the **driver-scan
cardinality** of each atom — how many nodes that atom would iterate if it
drove the join — read from the freshly-built index. That is the only
input the atom-ordering decision needs, and it is fully known at
index-build time. (The complementary "how much does a *bound* element
narrow a probe" quantity — `|by_contains[x]|` for a specific runtime `x` —
is *not* a scheduling input; it varies per match and is handled inside
leapfrog at execution. See "Why This Composes with Semi-Naive".)

### How the Scheduler Actually Works

The scheduler is not a simple "order atoms by selectivity." It's a
plan compiler that emits a flat sequence of `Step`s via an
interleaved two-phase loop:

**Phase 1 — Eager propagation.** Repeatedly scan all unused atoms
looking for ones that are already satisfiable given the current set
of bound variables:

- `RAtom::Eq(a, b)` with one or both sides bound → emit `CheckEq`
  or `CopyBinding`. No index access.
- `RAtom::Plain { node, .. }` where `node` is already bound → the
  node variable was bound by a previous step's child extraction.
  Emit `Join { ByRepr(node) ∩ ByOp(op) }` (intersect within the
  known class) + `ExtractChild` / `CheckChildEq` for each child.
  This resolves the atom **without scanning `by_op` at full size**.
- `RAtom::Lit` → always free.

These are zero-cost or near-zero-cost steps. The eager pass fires
them greedily until nothing more can be resolved.

**Phase 2 — Pick one expensive atom.** When the eager pass stalls,
pick the single cheapest remaining atom via `estimate_cost` (which
reads the atom's cardinality from `IndexStats` — `atom_card[atom_id]`
if set for this flavor, else `op_card[op]`; see "Why This Composes").
Emit its `Join` step (leapfrog over `ByOp ∩ ByChildPos` for any
already-bound children), then `ExtractChild` for each unbound child.
This binds new variables, which may unlock more atoms in the next
eager pass.

Then loop back to Phase 1.

**Example.** Pattern `mul(add(?x, ?y), ?z)` flattened to:

- Atom 0: `?root = mul(?lhs, ?rhs)`
- Atom 1: `?lhs = add(?x, ?y)`

With `|by_op[mul]| = 5000`, `|by_op[add]| = 20000`:

1. Phase 2 picks atom 0 (cheaper). Emits:
   - `Join { target: ?root, lookups: [ByOp(mul)] }`
   - `ExtractChild(?lhs, ?root, 0)`
   - `ExtractChild(?rhs, ?root, 1)`

   Now `?root`, `?lhs`, `?rhs` are bound.

2. Phase 1 fires: atom 1 matches the `Plain { node: ?lhs } if
   bound[?lhs]` case. Emits:
   - `Join { target: ?lhs, lookups: [ByRepr(?lhs), ByOp(add)] }`
   - `ExtractChild(?x, ?lhs, 0)`
   - `ExtractChild(?y, ?lhs, 1)`

Atom 1 never scans `by_op[add]` at full size — it only intersects
within `?lhs`'s class. The eager pass caught it because `?lhs` was
bound by atom 0's child extraction.

### Why This Composes with Semi-Naive

For variant `i`, we pass stats where each atom carries its own
driver-scan cardinality *for this flavor*, set by its mode: atom `i`
gets its delta-bucket size (tiny), atoms `< i` get `full − delta`, and
atoms `> i` get full. The scheduler naturally picks atom `i` first,
emits its join, extracts children, and the eager pass handles the rest.
The plan comes out optimized for "drive from the delta atom" without any
semi-naive-specific logic in the scheduler.

This is necessarily **per-atom, not per-op**: two atoms sharing an op
can have different modes in one flavor (e.g. `(f (f x y) z)`, variant 1:
atom 0 is `full − delta`, atom 1 is `delta`, both op `f`). A per-op
cardinality map cannot represent that — one number for `f` would mis-size
one of the two atoms. So `IndexStats` carries a per-atom override
(`atom_card[atom_id]`) that `variant_stats` fills for every join atom;
`estimate_cost` reads it, falling back to `op_card` (the naive default,
where every atom of an op reads the same full bucket).

Note this answers "schedule each flavor from *actual* index cardinality"
without any runtime/per-match machinery. The atom-ordering decision needs
only the **driver-scan** cardinality (`|by_op[op]|` in the atom's flavor),
which is known the moment the indexes are built. The *other* cardinality —
how much a bound element narrows a probe, e.g. `|by_contains[x]|` for a
specific runtime `x` — varies per match and is **not** a scheduling input:
leapfrog already drives from the smaller cursor at execution, for free, per
binding. So flavor-aware ordering is a plan-time decision over per-atom
driver cardinalities; nothing needs to be deferred into the matcher.

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

This is **not a new abstraction** — it is exactly the context one
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
join — see "How a Variant Executes".

### `atom_id` on `Step::Join`

`Step::Join` carries a stable
`atom_id: usize` — the atom's position in the compile-time numbering
(left-to-right, bottom-up pattern traversal). The scheduler stamps it
during planning (it knows which `RAtom` it's emitting). It is the bridge
between the **fixed numbering** that defines the variants and the
**execution order** the scheduler chooses per variant per round (next
section). At execution it selects each atom's index mode (delta / full /
full ∖ delta). At planning it also keys the per-atom cardinality
(`atom_card[atom_id]`) that `estimate_cost` reads — so two same-op atoms
in one flavor are costed independently. (It does *not* alter the shape of
the steps emitted for an atom — only their cost and, at run time, their
cursor flavor.)

Note: when the eager pass resolves an atom whose node is already bound
(the `ByRepr ∩ ByOp` case), that step still carries the atom's id, so
its mode is determined the same way. This applies to **variadic** atoms
(A/AC/ACI) too: when a variant drives from an enclosing atom and binds a
variadic child via `ExtractChild`, `emit_variadic_join` must still emit a
`ByRepr ∩ ByOp` re-join carrying the atom's id — otherwise the atom has
no `Step::Join` and its variant mode (notably `full ∖ delta`) is never
applied, and the parent-driven variant re-discovers matches the
delta-driven variants already own (a disjointness/efficiency regression,
not a soundness bug, since the union stays complete and application is
idempotent).

### Per-Variant Scheduling

At match time (rounds ≥ 1), for each rule, one variant per join atom
(`saturate_semi` / `run_rule_variant`):

```
for di in join_atom_indices(&rule.query) {
    let stats = variant_stats(&rule.query, di, &full, &delta);
    let plan  = schedule_with_stats(&rule.query, &stats);
    let view  = VariantIndex::variant(&full, &delta, di);
    run_query(&plan, eg, &view, globals);   // apply actions to each match
}
```

`join_atom_indices` is the join (relation-scanning) atoms only —
`Eq`/`EqGlobal`/`Lit` are excluded (no delta). A rule with no join atoms
falls back to a single naive-view run so its matches are never missed.

Re-scheduling per variant is cheap (the scheduler is O(k²) in atom
count, k typically 2–6, microseconds). It's worth it because different
variants genuinely produce different plans: `variant_stats` gives atom
`di` its tiny delta cardinality, so the scheduler drives from it, while
the other atoms keep their full / full ∖ delta sizes.

### What Changes, What Doesn't

Unchanged:

- `schedule_with_stats` — same algorithm. Sees stats, picks cheapest,
  emits steps. It is simply *called more often* (per variant per round),
  not modified.
- `LeapfrogJoin` — unchanged. Generic over `SortedCursor`; instantiated
  with `Base` or `Difference<Base, Base>` per join.
- The base cursors (`SortedVecCursor`, `BPlusCursor`) — unchanged.
  Exclusion is a separate `Difference` combinator, never baked in.
- The step shapes `emit_atom` produces for an atom — unchanged.

Changed (small, localized):

- `IndexStats` has `atom_card: HashMap<atom_id, usize>` beside
  `op_card`; `estimate_cost` takes `atom_id` and reads `atom_card` first,
  falling back to `op_card`. This is the one cost-model difference from
  naive — see "Why This Composes with Semi-Naive".
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

- **Atom numbering** `0..k-1` — fixed at compile time by the pattern
  traversal. The variant decomposition is defined *over this
  numbering*: variant `i` makes atom `i` delta, atoms `[0, i)` full ∖
  delta, atoms `(i, k)` full.
- **Execution order** — chosen dynamically per variant by the
  scheduler from selectivity stats. May visit atoms in any order.

These are independent. The bridge is `Step::Join.atom_id`, the atom's
*stable number*. When execution reaches a join, its mode is computed as
`compare(atom_id, i)` — a pure function of the number and the variant,
**independent of where that join sits in execution order**.

Why this is correct regardless of order: a variant is a conjunctive
query with a per-atom membership restriction (`n_i ∈ Δ`, `n_{j<i} ∉ Δ`,
`n_{j>i} ∈` full). The *result set* of a conjunctive query is
invariant under join-execution order — reordering changes speed, not
the set. So mode-by-number is sound for any order the scheduler picks.

Execution order matters only for **speed**: we want to drive from the
small (delta) cursor. We get that for free by feeding the scheduler
delta cardinality for atom `i` (next subsections) — it then chooses to
drive from atom `i`. But even if it drove from elsewhere, the variant
would still produce exactly its slice of matches. Correctness rests on
numbering; the scheduler only optimizes.

### Why a Whole Atom Shares One Mode

An atom binds **one** node `n` — the leapfrog *intersection* of its
lookups (`by_op[f] ∩ by_child_pos[(c,0)] ∩ …`). The mode restricts
that one node: delta (`n` new), full∖delta (`n` old), or full.

Restricting the *intersection* to/from `Δ` distributes over the
operands. With `A = by_op[f]`, `B = by_child_pos[(c,0)]`:

- delta: `(A∩Δ) ∩ B = (A∩B) ∩ Δ = (A∩Δ) ∩ (B∩Δ)` — restricting **one**
  operand or **all** gives the same set.
- full∖delta: `(A∖Δ) ∩ B = (A∩B) ∖ Δ = (A∖Δ) ∩ (B∖Δ)` — likewise.

So the mode is semantically a **property of the atom (its node)**, and
applying it to one cursor would suffice. We apply it **uniformly to all
of the atom's cursors** for one reason: `LeapfrogJoin` holds a
`Vec<C>` of a single cursor type, so an atom's join must be all-`Base`
or all-`Difference`. The redundant exclusions on the non-driver cursors
are provably harmless (the identities above) and cheap (each touches a
small delta slice). This is the only reason mode is realized
per-cursor rather than per-atom.

### Sizing `full ∖ delta` Without Traversal

The scheduler needs each atom's cardinality up front (`estimate_cost`
reads the per-atom `atom_card`, which `variant_stats` fills). For a
`full ∖ delta` atom — executed via a `Difference` cursor that filters on
the fly — this looks problematic, but its size is known **analytically**,
no scan:

For every index key `k`, `delta[k] ⊆ full[k]`. Both indexes are built
from the same post-rebuild e-graph, both skip `FLAG_SUBSUMED`, both are
deduped — so every delta entry also appears in full. Therefore:

```
|full ∖ delta|[k]  =  |full[k]|  −  |delta[k]|
```

an `O(1)` subtraction of two known `SortedVec` lengths. The `Difference`
combinator filters during *iteration*, but its *cardinality* is exact
and free. `variant_stats(rule, i, full, delta)` uses this directly:

| atom position | per-atom card (`atom_card[j]`) fed to scheduler |
|---|---|
| `== i` (delta)        | `|delta.by_op[op]|`                       |
| `<  i` (full ∖ delta) | `|full.by_op[op]| − |delta.by_op[op]|`    |
| `>  i` (full)         | `|full.by_op[op]|`                        |

So the scheduler sees a tiny number for the delta atom and drives from
it, and an accurate (smaller) number for full ∖ delta atoms — all from
length arithmetic, never touching a cursor. The value is keyed by **atom**
(`atom_card[j]`), not by op, so same-op atoms in one flavor are sized
independently.

## Interaction with Rebuild

The existing `EGraph::rebuild()` already walks changed nodes and
recanonicalizes them. Semi-naive adds two log points, both pushing
into the `EGraph::touched` vector:

- **Fresh nodes**: `register_if_fresh` already fires exactly once per
  newly-created node. Push the node id there.
- **Recanonicalized nodes**: the cache `recanonize_node` methods
  already detect when a node's canonical `(op, children)` form
  changes (the `new_hash != old_hash` / children-changed early-return).
  Push the node id immediately after that check, so unchanged nodes are
  not logged. The id is threaded out via a `&mut Vec<G>` out-param — the
  same mechanism by which `collisions` is already passed through.

The touched log is append-only per round, cleared at round
boundaries, and materialized into delta sorted-vecs at the start of
each match phase. Mechanically it is a scratch `Vec<Cfg::G>` field on
`EGraph`, exactly like the existing `collisions`, `g_buf`, and
`mset_buf` fields — cleared at the start of a round and threaded by
`&mut` into `recanonize_node`.

### Not To Be Confused With `has_history` (Proofs)

The cache `recanonize_node` methods already do a copy-on-first-
recanonicalize **for proof reconstruction** — unrelated to semi-naive.
The touched-log push co-locates with it (both sit right after the
no-change early-return) but the two are independent and behave
differently:

| | `has_history` / history-save | touched-log push |
|---|---|---|
| purpose | save original node for proof reconstruction | record change for the delta index |
| store | `self.history` (per-cache, `Option`, `PROOFS` only) | `EGraph::touched` (global scratch `Vec`) |
| marker | `has_history()` per-node tag bit | none |
| condition | `PROOFS && !has_history()` | unconditional |
| frequency | **once per node, ever** (first recanonicalize) | **every round** the node's canonical form changes |

The touched-log push is **not** conditioned on `has_history()` — a node
that changes in three different rounds must appear in the delta three
times, once per round, whereas its original is saved to the proof
history only on the first recanonicalize. They share only the
change-detection location.

## Correctness Invariant

> The delta is a superset of all nodes whose canonical `(op, children)`
> changed since the round boundary.

Formally: for every node N in the e-graph after the round's rebuild:

- If N was freshly created this round → N ∈ delta.
- If N existed before but its canonical form changed due to a merge
  → N ∈ delta.
- Otherwise (N unchanged) → N ∉ delta (may be, but need not be).

The first two conditions are sufficient for correctness: the semi-
naive join enumerates all matches involving at least one "new this
round" atom, where "new" means "in delta." Any match discoverable
this round but not last round must involve at least one node whose
canonical form differs from last round — and that node is captured
by one of the two conditions.

Being a *superset* is fine (finding false-positive deltas causes
no re-emission issue because of the `full \ delta` staging) but being
a *subset* is a soundness failure. The hooks must log every actual
change; spurious entries are just wasted work.

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
cleared at every round boundary and on `restore`. Because matching
for a round happens entirely between rebuild and the next round
boundary, the log never needs to survive a `mark`/`restore` — after a
restore, the loop simply starts the next round with an empty log and
repopulates it during the following rebuild. No semi-persistent
coordination is required.

`RoundBoundary` (the snapshot of cache lengths) is a value type. The
saturation loop owns it. It doesn't need to be semi-persistent because
after a restore, the loop would recompute it from the restored cache
lengths anyway.

## Implementation Status

This design is **implemented**: `saturate_semi` in `egraph/src/saturate.rs`,
selectable via `Interpreter::set_strategy(SaturationStrategy::SemiNaive)` and
the `--strategy semi-naive` CLI flag (default is naive — no behavior change for
existing callers). The phased build history (ordered tasks, the required
soundness tests, and how they were sequenced) is preserved in the branch's
commit log.

This chapter is the **rationale and correctness** reference (why the
decomposition is sound, how it composes with flattening and the
scheduler, where the savings come from). Work intentionally left for
later — the configurable B+tree index backend, the delta-size fallback,
the trigger pre-filter, and the end-to-end performance harness — is
tracked in
[`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md).

## Open Questions

1. **Which full-index backend wins?** Decision deferred until the
   end-to-end harness exists. Current leaning: `BPlusTreeSet<TRACK=false>`
   as the default based on microbenchmark evidence, but this must be
   validated against real saturation workloads.

2. **Cost model for `FullMinusDelta`.** The filter adds an
   `O(log |delta|)` check per step. Does the scheduler need to account
   for this when estimating costs? Probably not at first — delta is
   small enough that the filter cost is dominated by the underlying
   full-cursor cost. Revisit if profiling says otherwise.

3. **Per-variant plan caching.** With k variants per rule, should the
   k scheduled plans be cached and reused across rounds, or
   re-scheduled each round? Re-scheduling gives better plans as
   delta sizes shift; caching saves scheduler cost. Start with
   re-scheduling; add caching only if measurement justifies it.

4. **Trigger filtering.** A `root_ops: HashSet<O>` per `PreparedRule`
   could skip rules whose join atoms' ops have no delta this round — a
   cheap pre-filter that avoids the entire variant loop for many rules
   when the delta is sparse. Worth implementing as a hardening step now
   that the core fan-out is validated; see
   [`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md).

5. **Delta size bounds.** If a single round's merge cascade
   recanonicalizes a large fraction of the e-graph, `|delta|`
   approaches `|full|` and the semi-naive savings vanish. Should the
   loop fall back to the naive path in that case? Probably — with a
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
   lookup per bound element. Match work is now independent of the variadic op's
   total node count — witnessed by `by_contains_narrows_variadic_driver`
   (match-step instrumentation), and soundness across A/AC/ACI under both
   strategies (incl. `PROOFS=true`) by the differential suite.

   `estimate_cost` accounts for the narrowing: a variadic atom is discounted
   by one halving per bound element (`cost_discounted`), the same heuristic
   `Plain`/`AExact` use for bound children via `by_child_pos`. So the scheduler
   sees a fully-bound variadic atom as cheap and drives from it, instead of
   mis-costing it as a full `by_op` scan. The discount is a plan-time heuristic
   — it cannot read the true runtime `by_contains[e]` slice size (which depends
   on `e`'s class-rep), but it correctly orders bound vs. unbound atoms. Tests:
   `bound_element_discounts_variadic_cost`,
   `scheduler_drives_variadic_from_bound_element`.

## Testing Strategy

Correctness is established by **differential testing** against the
naive path — the same rules and input run both ways, with semi-naive
required to reach the same result. As built:

- **Observational equivalence** (the core check): build two `EGraph`s
  identically, saturate one naively and one semi-naive, and assert the
  equivalence partition over the original node ids is identical. Used
  in the targeted scenarios (commute, multi-rule, constant fold,
  two-level fold, AC, ACI) and in the randomized proptest.
- **Randomized proptest**: a random input term + a random subset of a
  rule pool, naive vs semi-naive, asserting the partition agrees
  (default 512 cases; verified to 5000).
- **Whole-corpus differential**: every `.egg` integration test runs
  under *both* strategies and must reach the same `EXPECT` outcome — so
  semi-naive is checked against naive across the entire program corpus
  (arithmetic, AC multiplicity, ACI, extraction, folding, subsumption,
  globals, push/pop) for free.
- **Disjointness** (the property final-state equivalence cannot see,
  since rewrite application is idempotent): in one round, the variant
  match sets must be pairwise disjoint and their union must equal the
  naive matches involving a new node. Tested directly.
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
  steps than naive, and that the `ByContains` driver-narrowing keeps work
  independent of distractor count.

Note: a strict *structural isomorphism* check is **not** used as the
differential oracle. Node count and per-class node multiset are
order-dependent — the append-only node store and merge-representative
choice cause two equivalent runs to materialize different numbers of
congruent transient nodes — so the valid invariant is the equivalence
*partition*, not structural identity. (The randomized proptest
surfaced exactly this.)

Still open: an end-to-end saturation **performance** harness, which is
also the prerequisite for the backend-selection sweep above.

## References

- Abiteboul, Hull, Vianu, *Foundations of Databases* (1995), Chapter
  13 — the canonical treatment of semi-naive evaluation in Datalog,
  including why built-in predicates are excluded from the
  decomposition.
- Zhang, Z. et al. "Better Together: Unifying Datalog and Equality
  Saturation" (PLDI 2023) — modern application to e-graph engines.
- [`../future/semi-naive-deferred-work.md`](../future/semi-naive-deferred-work.md) — the remaining,
  intentionally-deferred work (configurable index backend, delta-size
  fallback, trigger pre-filter, performance harness).

---
[← Ch 17: Interpreter and Saturation Loop](17-interpreter.md) · [Table of Contents](00-table-of-contents.md)
