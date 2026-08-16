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

**Done (2026-08-15).** `IndexStore::fanouts` measures the three access
paths per round and `schedule::estimate_cost` multiplies one measured
fraction per bound key. Match steps on math-microbenchmark, the
load-independent measure, over the same eleven iterations:

| encoding, strategy | before | after | ratio |
|---|---|---|---|
| rules, naive | 218,567,542 | 7,284,276 | 30.0x |
| rules, semi-naive | 216,654,595 | 7,191,713 | 30.1x |
| native, naive | 3,074,117 | 3,074,106 | 1.00x |
| native, semi-naive | 198,571,597 | 3,167,101 | 62.7x |

The rules encoding runs in 0.89 s against 10.7 s measured on this change
alone, and the comparison pilot re-run after `registry: memoize
completion_column` landed puts it at 747.8 ms against egglog's 523.9 ms in
the same run, 1.4x from 22.7x. Semi-naive under native AC was the second
defect the constants fixed: it cost 64.6x naive's match steps on that
encoding and now costs 1.03x, from the same mispricing on `by_contains`
rather than `by_child_pos`.

The backward-distributivity rule no longer drives from a `Mul` atom into a
`Mul`-`Mul` join, which is what the acceptance asked for, but it does not
drive from the `Add` atom either. It scans `Mul`, the smaller relation, and
joins `Add` second through `by_child_pos`, which leaves the second `Mul` a
`by_repr` re-join within the class the `Add` bound:

```
Join(a0 v0<-[op104])                     scan every Mul
Extract(v1<-v0.0) Extract(v2<-v0.1)      bind a, b
Join(a2 v5<-[op102&pos0=v0])             Add nodes over that Mul
CheckChild(v5.0==v0) Extract(v3<-v5.1)   bind the sibling class
Join(a1 v3<-[repr=v3&op104])             Mul nodes in that class
CheckChild(v3.0==v1) Extract(v4<-v3.1)   check the shared a, bind c
```

That order measures 7,284,276 steps over the whole run against the
hand-pinned `Add`-first counterfactual's 7,395,846, so the plan the
constants choose is the better of the two and the acceptance's plan shape
was the wrong target: what mattered was ending the 66.98 M intermediate,
not which atom drives.

Three departures from the plan above, all measured.

**Size-biased means, not plain means.** The estimator is
`sum(b^2) / sum(b)` over a path's buckets, not `sum(b) / count(b)`. A
probe key is a variable the join bound from the data, so it lands in a
bucket with probability proportional to that bucket's size; the plain mean
answers a question no probe asks, and on a distribution with one hub bucket
of size H among K singletons it reports about 1 where the size-biased mean
reports about H. The two agree on the four measurements above to within
0.1% except under the delta-seeding experiment below, where the plain mean
costs 49.5 M match steps against the size-biased mean's 10.0 M. Chapter 20's
Fact 2 is unchanged: one number per path prices the expected probe, not the
individual one, and S3 is what prices the individual one.

**A third path, `by_contains`, is measured too.** The plan named `ByRepr`
and `ByChildPos`; the variadic atoms (A/AC/ACI) drive from `by_contains`
per bound element, and that is the path the native encoding's factoring
rule `(Add (Mul a ..p) (Mul a ..q) ..rest)` mispriced into a Mul-Mul
self-join on a shared factor.

**The plain mean cannot be read off the existing aggregates, and neither
can the size-biased one.** `by_child_pos` and `by_contains` are keyed by
child class alone while every join intersects them with `by_op[op]`, so the
quantity the scheduler needs is a bucket restricted to one operator, which
no total the build already keeps can produce. It is one pass over the two
finished maps, tallying each bucket's parents into an array indexed by the
operator's dense id.

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

**Rejected on measurement: pinning the delta atom to the front of the
order.** The shortcut S2 would make unnecessary is to seed each variant's
plan from its delta atom, so that "match over the delta and propagate
outward" is an invariant rather than a property that emerges when the delta
happens to be the cheapest relation. Implemented and measured on
math-microbenchmark, it costs match steps in both encodings: rules
semi-naive 7,191,713 -> 10,011,574, native semi-naive 3,167,101 ->
5,852,891. The delta atom is not the same choice as the cheapest *first*
atom: pinning it fixes the driver but leaves the rest of the order to be
built from a worse prefix, and on this workload the driver's fan-out
matters more than its base size. The cost model already reaches the
intended behaviour where it pays, because `variant_stats` gives the delta
atom the delta's cardinality: when the delta is small the delta atom is the
cheapest atom and wins on cost, and when it is large (62-90% here) driving
from it is measurably worse. Revisit under S2, where a delta atom placed
anywhere in the order costs its suffix rather than its bucket, or on a
workload measured to keep `|delta|/|full|` small for several consecutive
rounds.

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

## Convergence target (2026-08-15)

The program's acceptance is now: (a) within 10% of egglog wall clock on
non-canonizing workloads, i.e. the shared rules encoding, on the
intersection benchmarks; (b) demonstrated separation under native AC
canonization, as a width-scaling sweep of the add-ac block (n = 7..20):
the rules encoding and egglog grow super-linearly in the sum width while
native AC stays flat. Budget arithmetic for (a) on math-microbenchmark:
egglog's 508 ms includes 218 ms rebuild; their matching+apply is ~300 ms.
The hot-path audit (comparison/hotpath-audit.md, measured with validated
hardware counters) settled the lever list. Verdict: compute-bound, not
memory-bound - IPC 3.65 vs egglog's 4.16, but 19.6x more instructions
retired; only instruction removal closes the gap, and re-layout does not.
Revised levers, prototype-measured: (1) S1 selectivity (prototype: 112.8 G
-> 9.6 G instructions, 11.8 s -> 879 ms); (2) memoize
`OpRegistry::completion_column`, which allocates and rescans the op map
once per fresh node (~1,800 instructions per node; 23.7% of the
order-corrected run; 879 -> 769 ms); (3) after those, the residual 1.31x
is term construction (ListArena::try_append, FixedArityCache::probe,
rehashing), 24% of the corrected run - the next frontier, untouched by
matching work. Rejected by measurement: specializing LeapfrogJoin::new's
sort (instructions +2.4%); the TLS counter is 1.85% and only if flag and
counter move together. The semi-naive access-path audit (delta indexes
correct; middle-out ordering absent; per-key ByContains skew) gates any
semi-naive claim and extends S1's scope.

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

## Convergence target met (2026-08-16)

Acceptance (a) is met on the rules encoding: 566.7 ms against egglog's
523.8 ms, 8.2%, medians of seven interleaved runs on the machine and
under the placement `comparison/hotpath-audit.md` describes. The nine
changes that took it there are recorded with per-commit numbers in that
file's 2026-08-16 addendum; the summary is 6.89 G to 5.54 G instructions
and 1.96 G to 1.47 G cycles from `5289140`, with match steps and final
node counts identical on all twenty programs under `comparison/`.

The lever list above needs two corrections.

**Lever (3), dropping `ByOp` from a join that has a bound-child lookup,
was priced at nothing post-S1 and is worth 19% of cycles.** The
prediction came from measuring it against the `P5` root-driven
counterfactual, whose remaining joins intersect `by_repr` buckets of 2.51
entries. The order S1's constants actually choose is the one printed
above: two of its three joins intersect a bound-child bucket with a whole
relation, and the whole-relation cursor is a doubling gallop plus a
bisection per partial match. Landed as `790ba05`.

**Lever (3)'s premise, that the residual is instruction count, no longer
holds.** The audit's verdict was compute-bound at 19.6x instructions, and
it was right about that configuration. We now retire 5.54 G instructions
against egglog's 5.74 G, 0.965x, and take 1.082x their wall time: the
whole residual is IPC, 3.78 against 4.25. From here the levers that can
still pay are the re-layouts the audit listed and did not implement (R2,
arena-backed index buckets; R3, a class-indexed `by_child_pos`), plus the
class use-list, which is 14% of the profile and whose append does two
random memory accesses where a prepend does one. The prepend is measured
at 552 ms, 1.054 of egglog, and is blocked on re-verifying
`EClasses::add_use`, whose proof body asserts the appended list shape.

S3 (per-binding driver selection inside the leapfrog seek) is still
unmeasured and still the right next matching change, but it now attacks a
smaller target: after `790ba05` the leapfrog seek is 5.2% of the profile
where the audit measured it at 26.3%.
