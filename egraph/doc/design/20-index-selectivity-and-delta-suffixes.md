# Index selectivity and delta suffixes: the matching-throughput plan

Proposes the indexing and planning changes that close the measured
rules-encoding gap against egglog and make semi-naive deltas usable at any
position of a join. Grounded entirely in the measurements of
`comparison/throughput-gap-ours.md`, `comparison/throughput-gap-egglog.md`,
and `comparison/throughput-gap-synthesis.md`; every number below is from
those documents. It is a work plan, not a status page. Companion chapters:
06 (indexes), 07 (leapfrog), 08 (query compilation), 18 (semi-naive).

## The two facts the design answers

**Fact 1: our planner's selectivity constants are wrong by three orders of
magnitude on one access path.** The scheduler prices every bound child as a
fixed halving of an atom's `by_op` cardinality. Measured fan-outs on the
math-microbenchmark iteration-8 e-graph: `ByRepr` (enumerate nodes of a
bound class) 2.51; `ByChildPos` (enumerate parents of a bound child) 1,239.
The mispricing made the planner drive the benchmark's only 3-atom rule from
a `Mul` atom, underestimating the join by 2,479x; that one order was 95.3%
of the 11.6 s run, and pinning the right first atom measured
13.57 s -> 0.89 s, within 1.75x of egglog.

**Fact 2: schema-level statistics, however fresh, cannot see skew.** Our
indexes are rebuilt every iteration, so their aggregate cardinalities are
faithful to the round. The 1,239 is nonetheless an average over a skewed
distribution: hub classes have enormous parent buckets, leaves have tiny
ones. egglog's plans are frozen at declaration time on an empty database
(their static planner uses no cardinalities at all); their orders emerge at
runtime from two mechanisms: remaining stages re-sorted by live candidate
size before the join and every third stage, and each binary intersect
iterating whichever side's prober is smaller for the currently bound
values. The information source is the concrete bucket size for the actual
binding, which no precomputed aggregate summarizes.

A third measured fact scopes the delta work honestly: on
math-microbenchmark, deltas are 62-90% of the relations and both engines'
semi-naive machinery is worthless there (egglog's own `--naive` is
marginally faster than their semi-naive on that file). The delta design
below wins on incremental workloads: small edits, re-saturation after
mark/restore, which is this system's home ground and a workload shape a
batch engine does not serve.

## S1. Selectivity constants from measured fan-outs (the fix)

Replace the fixed halving in the scheduler's cost model with
per-access-path selectivity read from the indexes the planner already
holds: for `ByRepr`, `nodes_of_class_total / classes` (mean class member
count); for `ByChildPos`, `parents_total / distinct_children` per (op,
position) bucket set. Both are one division over numbers the per-iteration
index build already computes; no new structures. The estimate for an atom
with k bound children multiplies the matching per-path factors instead of
shifting right k times.

Prerequisite, from the synthesis doc: the two orderings returned match
counts 2.9% apart on the same e-graph (69,312 vs 67,293), inferred to come
from `ExtractChild` reading the live e-graph while `Join` reads the
iteration's index snapshot. Characterize, pin with a test, and resolve (or
prove benign and document) before the planner change lands, because an
ordering change must not silently change the match set.

Acceptance: math-microbenchmark rules encoding under 1 s with no
hand-pinned orders (measured headroom says ~0.89 s); the full egg fixture
suite green; the benchmark equivalence check of `comparison/` reproduced.

## S2. Watermark delta suffixes: deltas on every access path

Nodes have dense allocation-ordered ids, and an iteration's delta is
exactly `id >= watermark`. Keep every index bucket sorted by node id, and
the delta restriction becomes a binary-searched suffix of whatever bucket a
join is already probing, at any position in the variable order. This is
egglog's timestamp-suffix trick obtained from a property we already have,
with no separate delta structures, no duplication, and no maintenance
beyond the sort discipline the per-iteration rebuild can enforce for free
(nodes are appended in id order; a bucket filled in scan order is already
id-sorted unless the build reorders it - verify and pin).

What it buys: today a delta-restricted atom is only cheap as the scan
driver; with suffix buckets the planner may place the delta atom anywhere
and still touch only new tuples, and the semi-naive variant costs stop
depending on the variant's atom being schedulable first. The per-variant
planner then prices the delta atom by its true (suffix) cardinality, which
S1's constants make meaningful.

## S3. Per-binding driver selection in the leapfrog seek

Leapfrog fixes the variable order, but at each trie level the choice of
which atom's iterator leads the seek can be made per binding: compare the
live range sizes of the participating iterators (sorted buckets; a range
size is two bounds and a subtraction) and let the smallest drive. This is
egglog's smaller-side probing transplanted into LFTJ, and it is the
mechanism that neutralizes skew: hub bindings and leaf bindings get
different drivers automatically, per binding, with no cost model at all.
S1 fixes the average; S3 fixes the variance.

## S4. Postponed: stage-level re-sorting (free-join style)

Re-sorting whole join stages by live candidate size, as egglog does before
the join and every third stage, requires moving from LFTJ's fixed variable
order to stage-structured execution: a real engine change. Postponed until
S1+S3 have a measured residual that justifies it; the measured ceiling of
the whole rules path today is 1.75x of egglog with only the order fixed,
so the expected value of S4 is bounded and small.

## Order and gates

S1 first (with its prerequisite characterization), then S2 and S3 in
either order (S2 is storage discipline + planner input; S3 is executor
local). Every step gates on: the egg fixture suite, the AU differential
fixture (byte-identical - the AU solvers do not run the matcher, so this
is a no-regression check, not the primary gate), the comparison
equivalence protocol, and a before/after on math-microbenchmark plus one
delta-heavy incremental workload (to be added beside the comparison
pilots: repeated small-edit re-saturation under mark/restore, the shape
S2 exists for).
