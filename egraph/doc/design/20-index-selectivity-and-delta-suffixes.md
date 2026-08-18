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
individual one. S3 prices the individual one at execution; S5 prices the
expected probe of a *particular* driver at plan time, which is the other
half of what one number cannot say.

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

**Landed 2026-08-16: the operator restriction is chosen per binding.** The
first per-binding choice in the seek is not which iterator drives but whether
a `ByOp` lookup joins the ring at all. `790ba05` demoted it to a per-candidate
operator test whenever the atom had another lookup, unconditionally, and
measured 19% of cycles on math-microbenchmark. The demotion is right when the
candidate set is small and wrong when the operator relation is: the test costs
`m` loads into the round's `op` table whatever the intersection turns out to
be, while the operand costs `min(m, n)` leapfrog iterations, so a hub class
with 262 144 parents read against a 26-node relation runs 600x slower under
the test than under the operand. `run_join` now reads both lengths before it
opens either cursor: `m`, the smallest of the atom's other buckets, and
`n = |by_op[op]|`. Both are `len` calls on buckets the join is opening anyway.
It takes the test when

```
n >= min(512 * m, 131_072)   and   m <= 2 * n
```

`egraph/tests/ematch_op_filter.rs::sweep` regenerates the measurement. It
builds `hubs` child classes with `m` parents each spread over eight operators,
holds `hubs * m` at 262 144 so that the test's cost per query is the same
262 144 loads in every case, and varies the `f0` relation `n` against it.
Median wall per query, release, Apple M4 Pro, empty intersection so that no
match construction is in either column; entries are leapfrog over filter, so
below 1 means the operand won.

| m | n = 2 621 | 16 384 | 53 710 | 131 072 | 262 144 |
|---|---|---|---|---|---|
| 8 | 0.75 | 0.96 | 1.34 | 1.67 | 1.98 |
| 16 | 0.52 | 0.73 | 1.05 | 1.43 | 1.71 |
| 64 | 0.20 | 0.35 | 0.61 | 1.12 | 1.57 |
| 4 096 | 0.04 | 0.13 | 0.43 | 0.99 | 1.52 |
| 262 144 | 0.03 | 0.13 | 0.44 | 0.99 | 1.49 |

The filter column is flat at 2.3 ms across the whole table, 8.8 ns per
candidate for a random load into a table of `4 * node_count` bytes, so every
movement is the operand's. An iteration costs 0.5 to 2 ns against a relation
that fits in cache and 13 to 17 ns against one that does not, and there are
`min(m, n)` of them rather than `m`: both effects favour the operand as `n`
falls, and past 131 072 neither rescues it at any bucket size. That is the
ceiling in the rule. The same shape at the intersection densities the bucket
sizes admit, `n` set to the hub-parent population scaled by the density:

| m | n = 262 144 (dense) | n = 2 621 (1%) | n = 26 (0.01%) |
|---|---|---|---|
| 16 | 1.08 | 0.51 | 0.46 |
| 256 | 1.07 | 0.12 | 0.04 |
| 4 096 | 1.04 | 0.09 | 0.003 |
| 65 536 | 1.05 | 0.09 | 0.002 |
| 262 144 | 1.06 | 0.08 | 0.002 |

**The slope and the ceiling come from different instruments, because the two
disagree.** Fitting the rows above gives a threshold that climbs with `m` at
about 4 096 per candidate: a small bucket cannot amortize the operand's
start-up, which is a sort of the ring plus a gallop to the bucket's first key
and does not depend on `m`. math-microbenchmark says otherwise. Its joins run
with `m` between 2 and 128 against relations of 8 k to 131 k, which is exactly
the window the fit governs, and the whole-benchmark wall against the slope
constant is

| per candidate | 0 | 64 | 128 | 256 | 512 | 1 024 | 4 096 |
|---|---|---|---|---|---|---|---|
| rules encoding, ms | 562.0 | 565.4 | 559.1 | 568.7 | 565.1 | 582.1 | 636.3 |

against 562.0 ms for the unconditional demotion, medians of nine interleaved
runs. Anything at or below 512 is inside the run-to-run spread and 4 096 costs
13%. The sweep is the optimistic instrument in that window: one of its queries
probes a single `by_op` vector 16 384 times with nothing else touching memory
in between, so the operand's seeks run against a cache-resident relation,
where real matching interleaves several relations, the `op` table, the child
pool and match construction between joins. The slope is therefore set from the
workload at 512 and the ceiling from the sweep at 131 072. The price is paid in
the sweep's `m = 16` to `m = 64` rows just above the threshold, where the rule
takes the test and the operand was up to 2.0x better; whether a workload exists
that spends its time there is a measurement nobody has made.

Three conditions fence the policy. `ematch::tests::op_restriction_rule_reads_both_lengths`
states the rule against the two lengths directly, including the corners no
e-graph test can reach at a reasonable size.
`ematch::tests::op_restriction_policy_is_taken_per_binding` asserts which
mechanism ran on two bindings of one join, and
`ematch::tests::op_restriction_mechanisms_agree_on_the_match_set` asserts that
pinning either mechanism returns the same matches; both are timing-free and run
in every build profile. `ematch_op_filter::adaptive_policy_is_within_1_2x_of_the_better_mechanism`
holds the policy to within 1.2x of the better mechanism at both extremes and
runs only under release codegen, following the binary-search canary in
`containers-conformance`. Match steps and final node counts are identical to
`e2eb260` on all twenty programs under `comparison/` in both the naive and the
semi-naive driver.

## S4. Per-binding atom scheduling

Re-sorting whole join stages by live candidate size, as egglog does before
the join and every third stage, was postponed on the argument that it
requires moving from LFTJ's fixed variable order to stage-structured
execution. That argument is right about stages and wrong about atoms. An
atom's join binds one variable, and which atom binds next is a choice the
executor can make as cheaply at depth 5 as the planner makes it at compile
time — the state it needs is which atoms are used and which variables are
bound, two masks. The atom order is also the part of the plan every
measurement in this chapter is about.

**Flag-guarded, default off, with a per-rule automatic mode.**
`ematch::set_runtime_scheduling`, or `--runtime-scheduling` on the CLI. With
the flag off the matcher runs the precompiled step array and every corpus
number below is unchanged to the digit. `--auto-scheduling` selects the mode
per rule per round: the index's fan-out measurement records each access
path's skew (the size-biased mean bucket size over the plain mean, the
`FanOuts` skew maps; 1 on a flat distribution, large in the presence of a
hub bucket), `run_rule_variant` takes the worst skew over the rule's
scan-atom operators, and the rule runs per-binding above a threshold of 8,
calibrated between the flat corpus (below 4) and the hub-shape condition in
`ematch_op_filter.rs` (orders of magnitude above). `by_repr`'s skew is
excluded because it is graph-global and would switch every rule together.
The match set is identical in all three modes.

**What it does.** With the flag on there is no precompiled step array. The
executor runs the two phases of the scheduling loop (chapter 08) at each
depth, against the environment rather than against the round's averages:
the eager pass to fixpoint, then the unused atom whose join opens the
shortest bucket under the current bindings. The price is a `len` on each of
the atom's lookups — `by_repr[env[node]]`, `by_child_pos[(env[child], pos)]`,
`by_contains[env[elem]]`, `by_op[op]` — resolved in the slice the atom's
semi-naive mode reads, and it is a bound on the candidates the leapfrog
intersection can propose, exact when the join has one lookup. Ties keep the
lowest atom index, so the choice is a function of the bindings and the atom
numbering. Nothing else changes: each atom still lowers through `emit_atom`,
so an AC atom's `ExpandA`/`DecomposeAC` sequence stays one block, and the
delta restriction is still per atom and position-independent
(`VariantIndex::mode` reads the compile-time numbering), which
`saturate::variants_disjoint_and_complete` now asserts under both modes.

Two implementation decisions worth recording. **Lowering is memoized per
`(atom, bound-mask, used-mask)`**, because `emit_atom`'s output is a
function of exactly those and a run reaches few of them — a handful for a
three-atom rule — so the blocks are lowered once and re-entered by refcount
thereafter; the memo is a linear-scanned vector, since comparing three words
over a few entries beats hashing one on the per-partial-match path. **The
choice is re-made per binding, not batched.** Batching every B bindings was
the fallback if the decision showed up in the wall clock; it does show up
(below), but re-deciding is what the flag is for, and the residual is better
spent on the double bucket resolution the decision and `run_join` currently
do than on deciding less often.

**Where it wins.** The workload the postponement did not have:
`tests/ematch_runtime_schedule.rs` builds `(f x y) (p w x) (q y v)` over an
e-graph where each `f` node has exactly one of its two probe buckets
populated, half on `x` and half on `y`. Both schedulers drive from `f`; a
plan-time order then commits to one probe atom and walks its `fan` nodes on
the half of the bindings where the other atom's bucket is empty. Match steps
and median wall per query, release, Apple M4 Pro, 1 024 `f` nodes:

| fan | steps off | steps on | ratio | wall off | wall on | ratio |
|---|---|---|---|---|---|---|
| 1 | 3 121 | 3 121 | 1.00 | 0.075 ms | 0.108 ms | 0.69 |
| 4 | 9 217 | 3 121 | 2.95 | 0.213 ms | 0.119 ms | 1.79 |
| 16 | 27 505 | 3 121 | 8.81 | 0.568 ms | 0.121 ms | 4.69 |
| 64 | 100 657 | 3 121 | 32.25 | 1.987 ms | 0.122 ms | 16.28 |
| 256 | 393 265 | 3 121 | 126.01 | 7.850 ms | 0.126 ms | 62.45 |

The steps-on column is flat because the per-binding order opens the empty
bucket first at every binding, whatever the other one holds. The gate is the
step count at `fan = 64`, stated at 10x so that it fails on a regression
rather than on noise; the wall figure is a release-only canary, following the
operator-restriction canary above.

**Where it does not.** The `fan = 1` row is the honest one: the two orders
cost the same steps, the choice is made 1 024 times for nothing, and the run
is 1.4x slower. The same shows on the workload S1 was fitted to, where the
plan-time order is already good — math-microbenchmark, medians of fifteen
interleaved runs, ranges in brackets:

| encoding | steps off | steps on | wall off | wall on |
|---|---|---|---|---|
| rules | 7 284 276 | 6 759 733 | 626.0 ms [612.5-632.7] | 629.0 ms [615.9-642.6] |
| native | 3 074 106 | 3 077 307 | 596.0 ms [578.0-604.8] | 614.8 ms [600.8-629.6] |

The rules encoding finds 7.2% fewer steps and gives them straight back to the
decision, landing inside the run-to-run spread; the native encoding has
nothing to find and pays 3.2%. Both are consistent with the reading that the
per-binding decision costs about what one avoided partial match saves, and
with the audit's verdict that this path is compute-bound: the decision
resolves each candidate atom's buckets and `run_join` then resolves the
winner's again, which is the obvious thing to remove before per-binding
ordering is worth running unconditionally. `--auto-scheduling` is the
shipped middle ground: flat rules keep the static plan and skip the
per-binding price, skewed rules pay it where the fan-out table says it
buys steps.

The flag changes no match set. Node counts are identical to `9e3da18` on all
twenty programs under `comparison/` in the naive driver, the hundred and
seven files of `tests/egg/` run under both scheduling modes and both
evaluation strategies, and `ematch::match_keys` — the differential helper
behind the snapshot-semantics tests — now runs the adaptive push engine
against the static pull engine, which share neither a control structure nor
an atom order. Under semi-naive the corpus node counts move on six of twenty
programs; so do naive's against semi-naive's with the flag off (addac-n7:
501 against 531), because a `:until` goal stops the run as soon as it holds
and a different application order reaches it at a different point. What is
invariant there is the match set, and that is what
`variants_disjoint_and_complete` asserts directly.

What is still not implemented is what S4 originally named: egglog's
re-sorting of whole stages, which would reorder the variables inside an
atom's join and not just the atoms. Nothing measured so far asks for it.

## S5. Sampled cross-index selectivity

S1 prices a bound key by one number per access path, and Fact 2 is the
limit on what one number can say. The size-biased mean is the bucket a
probe lands in when the probe's key is drawn from that index's own
marginal, and a join does not draw its keys that way: the key is a class
the previous atom bound out of its own relation, so what decides the
probe is the joint distribution over (emitter node, probe bucket). The
two disagree whenever the emitter's nodes avoid the hub classes that set
the mean, and then the mean over-prices the probe by the hub's size.

**Implemented 2026-08-16, flag-guarded, default off.**
`schedule::set_sampled_selectivity`, or `--sampled-selectivity` on the
CLI, with `--sampler-k`, `--sampler-bootstrap` and `--sampler-cv` for the
three fields of `SamplerConfig`. With the flag off,
`schedule_with_stats_sampled` is `schedule_with_stats`, the sampler is
never consulted (`schedule::tests::the_flag_off_path_never_samples`), and
every corpus number below is unchanged to the digit.

**What it does.** The greedy loop already tracks which variables are
bound. It now also tracks which atom bound each one and where in that
atom's node the variable sits: `KeySite` is the node's own class, a child
position, or an element of a variadic node, which is what the runtime
extraction reads. Costing a candidate atom on a bound key, the loop draws
`k` nodes (default 32) from the emitter atom's relation, computes from
each the class the candidate would probe with, and reads the candidate's
bucket for that class. The mean of those lengths replaces the path's
size-biased fan-out in the same cost expression, and the remaining
unbound keys keep their mean factors, so the estimate is the mean model
with one number substituted. A key no scheduled atom bound, a global or a
variable an eager `CopyBinding` propagated from one, has no emitter and
keeps the mean.

Three implementation decisions worth recording.

**The draw is an even stride over the sorted bucket, not a random
sample.** A plan has to be a function of the e-graph and the rule and
nothing else, so that a run reproduces and the differential tests can put
two engines on one order. The stride runs over node id, which is
allocation order, so it samples across the graph's construction history.

**The bucket length is restricted to the candidate's operator, by a scan
capped at 256 entries.** `by_child_pos` and `by_contains` are keyed by
child class alone while every join intersects them with `by_op[op]`, so
the length the scheduler needs is the bucket restricted to one operator:
the quantity `measure_fanouts` already tallies once per round, for the
reason S1 gives, that the two operators of one query differ in it by
three orders of magnitude. Counting it exactly is a pass over the bucket,
which on a hub class is hundreds of thousands of loads for one sampled
key. Past the cap the count is taken over a strided subsample of the
bucket and scaled to its length, which is the estimator the draw already
is, applied once more.

**The emitter's draw comes from the slice its semi-naive mode reads; the
probe's bucket comes from the full index in every mode.** The emitter
enumerates its mode's slice, so those are the keys that arise. The
probe's mode is already priced into the candidate's base cardinality
through `variant_stats`, and reading its delta bucket as well would
charge the restriction twice. `FullMinusDelta` draws from the full side,
an upper bound on `full ∖ delta`, for the reason `ematch::cursor_len`
gives.

**The bootstrap guard.** With `bootstrap = B > 0` the estimator resamples
the `k` draws with replacement `B` times and discards the estimate when
the standard deviation of the resampled means exceeds `cv_threshold`
times the estimate, leaving the size-biased mean in place. The stride is
deterministic but arbitrary with respect to the key distribution, so a
draw can miss a mode that carries the true mean, and the bootstrap prices
that risk out of the draw itself; the generator is a fixed-seed
SplitMix64, so the verdict stays a function of the draw.
`ematch_sampled_selectivity::the_bootstrap_guard_rejects_a_draw_one_sample_decides`
states it on a draw where one of the 32 samples sets the estimate. It is
off by default, and on the corpus it is close to inert: at `B = 200,
cv_threshold = 1.0` it fires once in the whole corpus, on one of the 382
estimates math-microbenchmark's native semi-naive run takes, and the step
counts are identical to `B = 0` on all forty configurations including
that one. That is a measurement of this corpus rather than of the guard,
and it says the same thing the corpus table below says: these drivers'
keys select buckets of nearly uniform size, which is why the mean was
already right on them.

**Where it wins.** The workload the mean cannot price:
`tests/ematch_sampled_selectivity.rs` builds `(d v) (pr v z) (alt v w)`
over 1 024 classes. The selective atom `pr` has one node over each of the
first 32 classes and nothing over the rest, plus 4 096 nodes hanging off
one hub class the driver `d` never points at. Those 4 096 never take part
in a match, and they are what the size-biased mean of `pr`'s
`by_child_pos` measures, so the mean prices `pr`'s probe at 4 088 where
its value from this driver is 0.031. The unselective atom `alt` is priced
honestly at `fan`. The mean therefore takes `alt` second and walks `fan`
of its nodes on each of the 992 bindings that cannot match; sampling
takes `pr` second and opens an empty bucket. Match steps, 32 matches in
every case:

| fan | steps, mean | steps, sampled | ratio |
|---|---|---|---|
| 1 | 5 217 | 2 241 | 2.33 |
| 4 | 14 145 | 2 241 | 6.31 |
| 16 | 49 857 | 2 241 | 22.25 |
| 64 | 192 705 | 2 241 | 85.99 |
| 256 | 764 097 | 2 241 | 340.96 |

The sampled column is flat because the order it picks does not depend on
`alt`'s size. The condition asserted is the step count at `fan = 64`,
stated at 3x against the measured 86x so that it fails on a regression
rather than on noise; it is timing-free and runs in every build profile,
following S4's. The sweep regenerates the table.

**Where it does not.** The corpus, which is what S1's constants were
fitted to. Final node counts are identical to `dd20d36` on all twenty
programs under `comparison/` in both the naive and the semi-naive driver,
and match steps are identical on thirty-four of the forty (program,
driver) configurations. The six that move all move down:

| program, encoding, driver | steps, mean | steps, sampled |
|---|---|---|
| eqsat-basic, native, naive | 195 | 143 |
| eqsat-basic, rules, naive | 255 | 203 |
| math-microbenchmark, native, naive | 3 074 106 | 3 074 017 |
| math-microbenchmark, native, semi-naive | 3 167 101 | 3 166 994 |
| math-microbenchmark, rules, naive | 7 284 276 | 7 284 249 |
| math-microbenchmark, rules, semi-naive | 7 191 713 | 7 182 477 |

The largest of those is 0.13%. Wall clock on math-microbenchmark, medians
of seven interleaved runs, follows the steps into the run-to-run spread:
rules naive 590.0 ms against 594.5, rules semi-naive 637.8 against 641.7,
native naive 563.3 against 560.8, native semi-naive 576.7 against 583.2.

The reading is that S1's mean was already the right number on this
corpus, which is the case the size-biased estimator was derived for: a
probe key lands in a bucket with probability proportional to that
bucket's size, and on math-microbenchmark the drivers' keys do land that
way. The mispricing S5 removes needs an emitter whose keys are drawn from
a different distribution than the probed index's marginal, and no rule in
the corpus has one. Whether a real workload does is a measurement nobody
has made; the synthetic one above shows what it would cost if it did.

**Plan-time cost.** Scheduling is not on the per-binding path, so the
sampler's price is bounded by the number of estimates a run takes, and
that number is small: 217 to 416 for a whole math-microbenchmark run,
because a query costs each candidate atom once per pass and the estimates
are memoized per (emitter, site, probe). Total time inside
`schedule_inner` over the whole run, eleven rounds, medians of five:

| encoding, driver | mean | sampled | estimates |
|---|---|---|---|
| rules, naive | 241.5 µs | 541.8 µs | 246 |
| rules, semi-naive | 459.7 µs | 999.5 µs | 416 |
| native, naive | 251.1 µs | 397.6 µs | 217 |
| native, semi-naive | 467.6 µs | 1 109.1 µs | 382 |

That is 13 to 58 µs per round of added scheduling against a 560 to 640 ms
run, under 0.1%, which is why the wall-clock column above is spread and
not cost. Per query on the three-atom synthetic shape, medians of 201:
0.709 µs for the mean model against 2.125 µs at `k = 8`, 5.500 µs at
`k = 32` and 19.417 µs at `k = 128`, so the cost is linear in `k` as the
draw is. The numbers were taken with `schedule_inner` wrapped in an
`Instant` pair, which is not in the committed code.

**The flag changes no match set.** An atom order is a permutation of the
same conjunction evaluated against the same index snapshot, which is the
property chapter 09's snapshot contract states and
`saturate::variants_disjoint_and_complete` asserts under both scheduling
modes; S4 relies on the same thing for a stronger reason, because it
re-permutes per binding. Node counts identical on all twenty corpus
programs in both drivers is the end-to-end check.

## S6. Feedback from execution, and profiles that outlive a round

Neither is implemented, and S5 supersedes part of what motivated them.

The motivation S5 answers is that the planner's inputs are aggregates,
one number per access path per round, and cannot express which keys a
particular driver produces. Feeding back the join sizes a round actually
observed, or carrying a trained per-rule profile across rounds, were the
two ways to get that information without sampling. Sampling gets it
directly and at plan time, from the joint distribution rather than from a
record of past runs, so it does not need a round of history to be right
on the first round and it does not need the workload to be stationary.

What remains for S6 is the part sampling cannot reach. A sampled estimate
prices the candidates a probe proposes, not the partial matches the
intersection survives: it reads one side of the join, and the other side
is the leapfrog, whose output is what the next atom's cost depends on.
Nothing at plan time reads that, and both of the mechanisms above would.
The same holds downstream of matching: the cost of applying a rule's
actions is not in any index, and a plan that minimized match steps is not
the same plan as one that minimized the round.

Postponed rather than closed, on both counts. Revisit online feedback on
a workload measured to spend a large fraction of a round in one rule
whose intersections are far smaller than either side, which is the case
where the probe estimate and the join output diverge; revisit trained
profiles on a workload measured to run the same ruleset over many
similar e-graphs, which is the case where a profile amortizes. Neither
condition holds on the twenty programs under `comparison/`.

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

S3's first half is now measured and landed: the operator restriction is
chosen per binding from the two bucket lengths, which corrects `790ba05`'s
unconditional demotion without giving back its 19% (math-microbenchmark
rules 565.1 ms against 562.0 ms, inside the run-to-run spread). S3's second
half, per-binding selection of which iterator drives the seek, is still
unmeasured, and it attacks a smaller target than the audit's: after `790ba05`
the leapfrog seek is 5.2% of the profile where the audit measured it at 26.3%.

## R2 and R3 landed together (2026-08-16)

**R2 (arena-backed index buckets) and R3 (a class-indexed `by_child_pos`) are
implemented, as one change, on the verified `DenseSpanMap`.** The two proposals
are the two halves of the same container: R2 is the flat value pool with
`(offset, length)` spans replacing one heap allocation per key, and R3 is the
dense integer key replacing the hash probe. Splitting them would have meant
building an intermediate structure that was neither, so the four families moved
onto `DenseSpanMap` in one step and the hash-map families were deleted rather
than kept behind a flag. `containers-verus/doc/design/15-dense-span-map.md`
states what the container proves; chapter 6 states how the index uses it,
including the position-major composite key `pos * stride + class` that R3 needs
and the space it costs.

Measured on `math-microbenchmark`, medians of seven interleaved runs, the same
machine and efficiency-core placement `comparison/hotpath-audit.md` describes:

| program | instructions | cycles | IPC | wall |
|---|---|---|---|---|
| rules, naive, before | 5.581 G | 1.484 G | 3.76 | 574.4 ms |
| rules, naive, after | 5.484 G | 1.389 G | 3.95 | 537.4 ms |
| rules, semi-naive, before | 5.731 G | 1.600 G | 3.58 | 620.0 ms |
| rules, semi-naive, after | 5.551 G | 1.448 G | 3.83 | 560.3 ms |
| native, naive, before | 6.056 G | 1.403 G | 4.32 | 542.2 ms |
| native, naive, after | 5.748 G | 1.232 G | 4.67 | 477.2 ms |
| native, semi-naive, before | 5.945 G | 1.454 G | 4.09 | 562.9 ms |
| native, semi-naive, after | 5.371 G | 1.155 G | 4.65 | 448.1 ms |

**The prediction that the residual is IPC holds, and the re-layout moves it.**
Instructions fall 1.7% on the rules encoding and 5.1% on the native one, while
cycles fall 6.4% and 12.2%: the cycle reduction is three to four times the
instruction reduction, which is the signature of a layout change rather than a
work reduction. IPC on the rules encoding goes 3.76 to 3.95 against egglog's
4.25 recorded in the previous session, closing 39% of that gap. egglog was not
re-measured in this session, so the 537.4 ms is comparable to this file's own
before-number and not to a same-session egglog run.

**The index build got cheaper, not more expensive.** The concern was that a
counting sort touches one span slot per key whether or not the key has values,
which the hash map did not, and that this would cost most on the delta index,
whose stream is short against the same key space. Timed around every
`IndexStore::build*` call over a whole saturation:

| program | before | after |
|---|---|---|
| rules, naive | 25.9 ms | 17.9 ms |
| rules, semi-naive (full + delta) | 25.0 + 20.3 ms | 15.6 + 12.2 ms |
| native, naive | 66.4 ms | 30.5 ms |
| native, semi-naive (full + delta) | 65.6 + 41.5 ms | 29.9 + 19.0 ms |

The counting build wins even where the key space is widest, because what it
replaced was one hash insert and one `Vec` push per entry into roughly 2.4 M
separately allocated buckets per round. Peak resident memory rises 3.2%, 247 to
255 MB on the rules encoding.

Every one of the twenty comparison programs was checked under both scheduling
strategies: node counts, class counts, iteration counts and match steps are
identical to the values before the change.

**R1 (folding the operator into the `by_child_pos` key) is still not
implemented, and R3 makes its cost concrete.** R1 multiplies the key count by
the number of operators, and the key count is now the length of a span table
that is allocated per round. The measurement to make before attempting it is the
span table's occupancy: R1 is worth its memory only if the buckets it splits are
long enough that the split removes more probe work than the wider table costs.

## The span table stopped being written per round (2026-08-16)

**The `O(num_keys)` term in the index build is gone, and the fan-out pass is now
the largest term left in the build.** R2 gave every family a span table dense
over its key space, and chapter 6 recorded the space that costs. What it did not
record is that the build *writes* that table every round whether or not the keys
occur. `comparison/span-table-sparsity.md` measures the consequence at S = 1e6 on
the E6 cycle: `by_child_pos` addresses 801 008 values with 2 003 967 keys, and
the four builds spend 40.6 ms per round on span tables for a 3.2 MB pool.

The families now build through `DenseSpanMap::build_in` over a caller-owned
`SpanArena` that outlives the map (`containers-verus` commit 3779a56). A build
bumps a generation stamp and writes only the keys its stream carries; a key an
earlier build wrote reads as empty. Chapter 6 states how the arenas are owned and
recycled. Per round at S = 1e6:

| phase | before | after |
|---|---|---|
| index build | 57.61 ms | 32.64 ms |
| span table, `by_child_pos` | 16.47 ms | 3.56 ms |
| span table, `by_repr` | 13.10 ms | 4.25 ms |
| `measure_fanouts` | 7.60 ms | 7.69 ms |
| matching and apply | 111.23 ms | 116.93 ms |

**`measure_fanouts` does not improve, and the reason is a missing accessor.** It
needs the occupied keys of `by_child_pos`, `by_contains` and `by_repr`. The arena
maintains exactly that list and the build keeps it current, but it is
`pub(crate)`, so `index.rs` scans `0..len()` and skips empty buckets. That scan
is the `O(num_keys)` term this change removed from every other phase, and at
7.69 ms it is now 24% of the index build. Exporting the occupancy list from
`containers-verus` is the next reduction and needs no e-graph change beyond
calling it. S5's sampler reads the same tally, so it would benefit too.

**S1's constants cost 5% more to serve.** A stamped span is 24 bytes against 16,
so a probe reads a span table 1.5 times wider and compares the stamp before
returning the slice, and matching measures 5% slower over three repeated runs.
The round total falls anyway, 170.5 ms to 151.2 ms. The trade reverses on a
workload whose rounds probe much more than they build; which one applies is a
measurement, not an inference.

## Seek strategy closed, and one lever with it (2026-08-16)

**Galloping is the right search on the arena layout, and the stride estimate the
join could compute does not improve it.** The lever list above prices the
leapfrog seek at 5.2% of the profile after `790ba05` and leaves the search itself
unexamined; `doc/perf-results/E18-seek-strategy.md` examines it. Bisecting the
remaining run loses every point of a sweep over bucket-sized spans (64 to
262 144 keys, advances 1 to 1024), by 3.5% at its closest and 32x at its
furthest. Starting the ladder at an expected stride is worth 9 to 14% for
advances between 4 and 64, loses 19 to 44% past 256, and costs 6.4x at an advance
of 1 when the estimate is 8x too large.

**The reason is the advance distribution, and it constrains more than this
lever.** `leapfrog::seek_stats` puts 30% to 95% of seeks at an advance of at most
one element and spreads the remainder almost flat out to `2^12`: on
`math-microbenchmark.rules` naive, every bucket from `log₂ d = 2` to 10 holds
between 3.2% and 5.5%. A per-cursor scalar cannot serve mass at both ends. The
same instrumentation measures the estimator directly, as the cursor's running
mean advance, which is `n/m` observed rather than predicted: on the naive
strategy it is within one octave on 8.6% to 40.6% of seeks and overshoots by 8x
or more on 34.8% to 66.9%, and the overshoot concentrates on the short advances
where it costs most. A prototype ran 0.4 to 1.4% slower end to end than its own
control on `math-microbenchmark`, both encodings, both strategies, medians of
seven.

**S3's second half is narrower than it was.** Choosing per binding which iterator
drives the seek was already attacking 5.2% of the profile; the sweep now says the
search inside that 5.2% is within 12% to 41% of the best any distance-aware
strategy could do, and that the remaining margin is not reachable from a
plan-time length ratio. What is left of S3's second half is the ordering
question, not the search question.

The instrumentation lands and the searches do not: `seek-stats` is off by default
and measured at −0.31% to +0.28% end to end when off. It is the reusable part,
because it prices any search whose cost is a function of the advance distance and
the remaining length without a run per candidate.
