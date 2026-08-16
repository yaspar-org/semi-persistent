# Our execution path on `math-microbenchmark.rules.egg`

This file records where our engine spends the 11.6 seconds it takes to run
`comparison/math-microbenchmark.rules.egg`, against egglog's 508ms on the same
rules to the same eleven iterations. It sits beside `throughput-gap-egglog.md`,
which records the same for egglog. It is a measurement record of one engine on
one program: it does not generalize to other rule sets, and the counterfactual
it measures is a diagnostic, not a proposed patch.

The dominant cause is one rule. The query planner drives
`(rewrite (Add (Mul a b) (Mul a c)) (Mul a (Add b c)))` from a `Mul` atom instead
of the `Add` atom, which turns a three-atom join whose answer is 69,312 matches
into 66,981,473 intermediate partial matches. That rule is 95.3% of all matching
and apply time and 97.8% of all e-matching steps. Pinning the `Add` atom first
takes the whole program from 13.57s to 0.89s on the same machine at the same
moment, and takes total e-matching steps from 220,704,279 to 7,395,846.

## Base and protocol

Engine at `8daa1f0`, release profile (`lto = "fat"`, `codegen-units = 1`) with
`CARGO_PROFILE_RELEASE_DEBUG=1`, run as
`semi-persistent math-microbenchmark.rules.egg --types machine`, naive strategy
unless stated. Match-step counts come from `--count-match-steps`.

The machine carried concurrent load from another job during these runs. Absolute
wall times below are 15 to 20% above the pilot's 11,561.8ms median for the same
program, and one unloaded repetition of the same binary measured 11.54s. Step
counts, match counts, and cardinalities are exact and load-independent, and every
A/B pair below was measured back to back or inside a single process, so the
ratios are unaffected. Where a number is a share of a total, both terms come from
the same run.

**The instrumentation is temporary and is not committed.** To regenerate, add to
`egraph/src/saturate.rs`: a `std::time::Instant` around `eg.rebuild()`, around
`IndexStore::build` plus `IndexStats::from_index`, and around the per-rule loop;
and a copy of `run_rule_variant` that separately times
`schedule::schedule_with_stats`, `ematch::run_query_into`, and the
`apply::apply_action` loop, printing `rule.rule_id.to_usize()`, `pool.len()`, and
the `ematch::match_steps()` delta. Add to `egraph/src/ematch.rs` a `[u64; 24]`
thread-local bumped by `step_idx` at the top of `run_step`, under the same
`COUNTING` flag `bump_match_steps` already reads: that array is the size of the
intermediate relation entering each plan step. The counterfactual in Q2 needs no
planner change: `IndexStats::atom_card` already overrides the per-op cardinality
per atom, so inserting `atom_card[j] = 0` makes `schedule_with_stats` pick atom
`j` first.

Rules are identified by `PreparedRule::rule_id`, which `interpret.rs:277` assigns
in declaration order. Each identification below is also confirmed structurally
from the atom operators in the dumped plan. Operator ids resolve as `op100` Diff,
`op101` Integral, `op102` Add, `op103` Sub, `op104` Mul: `op102` and `op104` are
confirmed by the two commutativity rules, whose single-atom queries return exactly
the `by_op` cardinality of the operator they scan.

## Q1: where the 11.6 seconds go

### Per iteration

Times in ms. `rules` is match plus apply summed over all 24 rules. `nodes` is
`eg.len()` after the iteration's applies.

| iter | rebuild | index build | rules | nodes |
|---|---|---|---|---|
| 0 | 0.0 | 0.1 | 1.6 | 79 |
| 1 | 0.0 | 0.0 | 1.4 | 128 |
| 2 | 0.0 | 0.0 | 1.4 | 218 |
| 3 | 0.0 | 0.0 | 1.5 | 417 |
| 4 | 0.0 | 0.1 | 1.3 | 827 |
| 5 | 0.1 | 0.1 | 2.3 | 1,694 |
| 6 | 0.1 | 0.2 | 4.9 | 3,523 |
| 7 | 0.3 | 0.4 | 15.6 | 8,805 |
| 8 | 0.7 | 0.9 | 15.5 | 30,278 |
| 9 | 2.7 | 3.1 | 802.1 | 154,824 |
| 10 | 21.3 | 16.6 | 12,924.3 | 1,234,680 |
| total | 25.2 | 21.5 | 13,771.9 | |

Iteration 10 is 93.8% of the matching and apply work and iteration 9 is 5.8%; the
first nine iterations together are 0.4%. Rebuild and index construction together
are 46.7ms, 0.34% of the run.

**We do rebuild every index from scratch every iteration.** `saturate.rs` calls
`IndexStore::build(eg)` at the top of each round, with no incremental path. At
1.2M nodes that costs 16.6ms, which is 0.13% of that iteration. It is not a cost
worth attacking on this workload; egglog's incremental column indexes
(`throughput-gap-egglog.md`) buy it nothing here.

### Per rule

Summed over all eleven iterations. Rules with under 4ms total are omitted; they
sum to 7.2ms.

| match | apply | total | share | matches | steps | rule |
|---|---|---|---|---|---|---|
| 12,951.5 | 18.1 | 12,969.5 | 95.3% | 80,095 | 215,808,821 | `(rewrite (Add (Mul a b) (Mul a c)) (Mul a (Add b c)))` |
| 52.3 | 186.7 | 239.0 | 1.8% | 409,456 | 1,445,126 | `(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))` |
| 68.5 | 162.2 | 230.7 | 1.7% | 557,290 | 1,990,214 | `(rewrite (Add a (Add b c)) (Add (Add a b) c))` |
| 28.0 | 30.7 | 58.7 | 0.4% | 104,488 | 530,495 | `(rewrite (Mul a (Mul b c)) (Mul (Mul a b) c))` |
| 6.0 | 19.0 | 24.9 | 0.2% | 106,111 | 318,344 | `(rewrite (Add a b) (Add b a))` |
| 4.6 | 18.9 | 23.4 | 0.2% | 18,451 | 88,364 | `(rewrite (Integral (Mul a b) x) ...)` |
| 5.9 | 14.0 | 19.9 | 0.1% | 32,427 | 130,292 | `(rewrite (Integral (Add f g) x) ...)` |
| 4.1 | 14.1 | 18.2 | 0.1% | 72,340 | 217,031 | `(rewrite (Mul a b) (Mul b a))` |
| 3.6 | 9.3 | 12.9 | 0.1% | 21,836 | 79,505 | `(rewrite (Diff x (Add a b)) ...)` |
| 2.0 | 4.1 | 6.1 | 0.0% | 6,123 | 32,366 | `(rewrite (Diff x (Mul a b)) ...)` |
| 13,131.0 | 479.4 | 13,610.4 | | 1,418,980 | 220,704,279 | total, 24 rules |

The top three by total time are the backward distributivity rule, forward
distributivity, and `Add` associativity. The first of those is 95.3% of the time
for 5.6% of the matches, at 2,694 e-matching steps per match; every other rule in
the file is between 3.0 and 5.3 steps per match. Query planning itself is below
the timer's resolution: `schedule_with_stats` measured 0.006ms per call at
iteration 10 and 0.26ms summed over the whole run.

Match and apply split 13,131.0ms to 479.4ms. Outside the one bad rule, apply
costs 2.8x what matching costs, which is the ordinary shape: the rules that fire
most are the cheapest to match.

## Q2: the planner picks a bad variable order on one shape

`egraph/src/schedule.rs` schedules greedily. It repeatedly picks the unprocessed
atom of least `estimate_cost`, which is the atom's `by_op` cardinality shifted
right once per already-bound child (`cost_discounted`, `schedule.rs:207`). The
estimate is an absolute size, not a fan-out per bound prefix, and the discount is
a fixed halving rather than a measured selectivity.

### The plan it chooses

Dumped at iteration 10, whose e-graph holds 86,061 `Add` nodes and 54,051 `Mul`
nodes. The resolved query has atoms `a0 = Mul(v1, v2) -> v0`,
`a1 = Mul(v1, v4) -> v3`, `a2 = Add(v0, v3) -> v5`.

```
Join(a0 v0<-[op104])                     scan every Mul
Extract(v1<-v0.0) Extract(v2<-v0.1)      bind a, b
Join(a1 v3<-[op104&pos0=v1])             Mul nodes whose first child is a
CheckChild(v3.0==v1) Extract(v4<-v3.1)   bind c
Join(a2 v5<-[op102&pos0=v0&pos1=v3])     Add nodes over those two Muls
```

The cost the planner charged each atom when it chose it, against the
partial-match relation that atom's join actually produced, read from the
per-plan-step counter:

| join | planner cost at the moment of choice | partial matches produced | error |
|---|---|---|---|
| a0, `by_op` Mul | 54,051 | 54,051 | exact |
| a1, `by_child_pos` Mul on `a` | 27,025 | 66,981,473 | 2,479x low |
| a2, `by_child_pos` Add on both Muls | 43,030, not chosen at that point | 69,312 | |

The planner compared 27,025 for `a1` against 43,030 for `a2` and took `a1`. The
comparison is between two absolute cardinalities, so it never sees that joining
`a1` multiplies the intermediate by 1,239 while joining `a2` would have divided
it. The last join then discards 99.9% of what `a1` produced: 69,312 survivors
out of 66,981,473.

### The counterfactual

Same process, same iteration, same e-graph, matching only, result discarded: pin
`a2` first by setting its `atom_card` to 0 and let the greedy scheduler continue
from there.

```
Join(a2 v5<-[op102])                     scan every Add
Extract(v0<-v5.0) Extract(v3<-v5.1)      bind the two child classes
Join(a0 v0<-[repr=v0&op104])             Mul nodes in the first class
Extract(v1<-v0.0) Extract(v2<-v0.1)      bind a, b
Join(a1 v3<-[repr=v3&op104])             Mul nodes in the second class
CheckChild(v3.0==v1) Extract(v4<-v3.1)   check the shared a, bind c
```

| | chosen order | `Add` pinned first | ratio |
|---|---|---|---|
| match time, iteration 10 | 12,193.1ms | 147.7ms | 82.6x |
| e-matching steps, iteration 10 | 201,314,509 | 2,285,279 | 88.1x |
| peak intermediate | 66,981,473 | 1,244,326 | 53.8x |
| matches | 69,312 | 67,293 | |

The mechanism is one measured ratio. Binding a `Mul` node from an already-bound
class through `ByRepr` has fan-out 216,061/86,061 = 2.51. Binding a `Mul` node
from an already-bound child through `ByChildPos` has fan-out
66,981,473/54,051 = 1,239. Probing for parents that share a child is 494x wider
than probing for nodes in a class, and the cost model charges both the same fixed
halving. Driving from the outermost atom of a rooted pattern makes every other
atom a `ByRepr` lookup; driving from an inner atom does not.

Over the whole program, with the same pin applied at every iteration:

| | chosen order | `Add` pinned first |
|---|---|---|
| wall, 3 runs back to back | 13.56s, 13.57s, 13.66s | 0.88s, 0.89s, 0.89s |
| total e-matching steps | 220,704,279 | 7,395,846 |
| that rule, match time | 12,951.5ms | 162.6ms |
| that rule, steps | 215,808,821 | 2,546,941 |
| final nodes, 11 iterations | 1,234,182 | 1,233,096 |

0.89s against egglog's 508.3ms median is 1.75x, from 22.7x. Iteration 10 then
splits 720.8ms of rules against 19.6ms rebuild and 16.8ms index build, and the
top rules by time become forward distributivity and `Add` associativity, both
dominated by apply rather than match.

**Is the chosen order bad only on this shape?** On this file, yes. It is the only
three-atom rule, and one of only two whose atoms share a variable (`a`) without
either being a child of the other: they are joined only through their common
parent. The other, `(rewrite (Mul (Pow a b) (Pow a c)) (Pow a (Add b c)))`, gets
the identical plan shape, driving from a `Pow` atom, which is also the right
choice there because its `Pow` relation holds 2 nodes against `Mul`'s 54,051: it
costs 209 e-matching steps and finds nothing over the whole run. The shape is
expensive only when the sibling atoms range over a large relation. Every
remaining multi-atom rule here is a rooted chain, where the inner
atom's node variable is a child of the outer, so whichever end the planner starts
from the other becomes a `ByRepr` or a single `ByChildPos` lookup and the plan is
within a small factor of optimal. Rule `(Mul a (Add b c))` drives from `Mul` and
reaches `Add` by `ByRepr` at 3.5 steps per match; rule `(Add a (Add b c))` drives
from the inner `Add` and reaches the outer by `ByChildPos` at 3.6 steps per
match. Both are fine. Whether the same defect costs anything on rule sets with
more sibling atoms is a measurement, not an inference, and this file cannot make
it.

**A 2.9% match-count difference between the two orders on the same e-graph is
unexplained.** 69,312 against 67,293. Inferred, not measured: `ExtractChild`
reads children live from the e-graph through `EGraph::child_at` while `Join`
reads the `IndexStore` snapshot built at the top of the iteration, and by the
time this rule runs, nine earlier rules have already merged classes in the same
iteration, so the two orders mix live and snapshot reads differently. The two
whole-program runs end 0.09% apart in nodes after the same eleven iterations,
so nothing large is being lost, but the discrepancy should be characterized
before any planner change lands.

## Q3: semi-naive is working and the workload defeats it

Semi-naive costs 216,067,723 steps against naive's 220,704,279, a 2.1%
reduction, and the pilot measures it at 11,299.2ms against 11,561.8ms. The
restriction is applied correctly. The deltas are legitimately almost the whole
relation.

`|delta|` against `|full|` per operator at the two iterations that matter, read
from `IndexStore::build_delta` at the top of each round:

| iter | Diff | Integral | Add | Sub | Mul |
|---|---|---|---|---|---|
| 9 | 563/904, 62.3% | 1,431/2,214, 64.6% | 10,498/13,462, 78.0% | 858/1,312, 65.4% | 8,466/11,798, 71.8% |
| 10 | 2,190/3,079, 71.1% | 5,246/7,396, 70.9% | 74,833/86,123, 86.9% | 2,791/4,008, 69.6% | 41,854/53,359, 78.4% |

The e-graph grows about 8x per iteration at the end of the run, so almost
everything in the final iteration is new. This agrees with the egglog-side
finding that 89% of its final e-graph is new.

That the restriction reaches each atom separately, and not only the first, is
visible in the variant split. The backward distributivity rule expands into three
variants at iteration 10, with `|delta|/|full|` of 0.784 for `Mul` and 0.869 for
`Add`:

| variant | delta atom | steps | measured share | share predicted from cardinalities |
|---|---|---|---|---|
| 0 | `a0` (Mul) | 146,179,294 | 72.6% | 78.4% |
| 1 | `a1` (Mul) | 37,321,954 | 18.5% | 16.9% |
| 2 | `a2` (Add) | 13,196,014 | 6.6% | 4.1% |
| sum | | 196,697,262 | 97.7% of naive | 99.4% of naive |

Predicted shares are the triangular decomposition evaluated on the measured
cardinalities: `d`, `(1-d)d`, `(1-d)^2 a` for `d = 0.784`, `a = 0.869`. Measured
and predicted agree to within 1.7 points on the total and rank the variants
identically, which is what a correct per-atom restriction looks like: variant 2
costs 6.6% of the naive join where the cardinalities predict 4.1%, because it is
the variant whose two `Mul` atoms are both restricted to `full` minus `delta`. If
the restriction reached only the first atom, all three variants would cost what
variant 0 costs.

`egraph/tests/semi_naive_delta.rs` already pins the two static facts this rests
on: the touched set is a superset of what changed, and `delta` equals `full`
restricted to the touched set, checked separately for `by_op`, `by_repr`,
`by_child_pos` and `by_contains`. Nothing here contradicts them.

**Semi-naive stays unprofitable after the order is corrected.** It costs 4.9%
more e-matching steps than naive on the corrected order, 7,758,391 against
7,395,846, and 1.09s against 0.89s: it plans and executes one query per body atom
per rule, and deltas this large save nothing to pay for that. Revisit only if a
workload is measured where the delta is a small fraction of the relation for
several consecutive iterations; this one never falls below 62%.

## Sample profile

`sample <pid> 10 1` on a naive run with the instrumentation compiled in but
disabled (`SP_PROF` unset, no `--count-match-steps`), so the only difference from
the base engine inside `run_step` is one short-circuited flag read. 6,866 samples
on the main thread, release build with debug symbols. Self time, symbols
demangled and truncated:

| samples | share | symbol |
|---|---|---|
| 3,569 | 52.0% | `leapfrog::LeapfrogJoin::search` |
| 1,197 | 17.4% | `ematch::run_step` |
| 780 | 11.4% | `ematch::cursor_in` |
| 228 | 3.3% | `leapfrog::LeapfrogJoin::new` |
| 198 | 2.9% | `EGraph::child_at` |
| 165 | 2.4% | `ematch::leapfrog_join` |
| 155 | 2.3% | `_tlv_get_addr` |
| 127 | 1.8% | `insertion_sort_shift_left`, inside `LeapfrogJoin::new` |
| 88 | 1.3% | `LeapfrogJoin::next` |
| 85 | 1.2% | `OpRegistry::completion_column` |
| 41 | 0.6% | `ListArena::try_append` |
| 33 | 0.5% | `UnionFind::find` |
| 28 | 0.4% | `apply::eval` |
| 27 | 0.4% | `FixedArityCache::probe` |

The join machinery is 89.6% of self time and `child_at` adds 2.9%. Nothing
outside matching is visible: hash-consing, rebuild, and allocation are each below
0.4%, and `IndexStore::build` does not clear the profiler's 5-sample reporting
threshold at all, consistent with the 21.5ms it takes over the whole run. This
confirms from a second direction that the cost is the join and not the
surrounding machinery.

Two smaller observations from the same profile.

**`_tlv_get_addr` is 2.3% of self time in a run that did not pass
`--count-match-steps`.** `ematch.rs:30-34` states that when counting is disabled the
hot path pays a single thread-local bool load "and nothing else; the counter is
never touched, so its cost is zero in production runs". The first half is
accurate and the conclusion is not: on this target a thread-local read is an
out-of-line call to `_tlv_get_addr`, once per `run_step` entry. The counter, its
flag, and the temporary per-step histogram are the crate's only thread-locals and
all three sit behind that one read, so the attribution is inferred but has no
competing candidate. The comment should be corrected, and if the 2.3%
matters the flag should be hoisted out of `run_step` into the caller.

**`LeapfrogJoin::new` plus its `insertion_sort_shift_left` is 5.1%.** Every join
step constructs its cursor set and sorts it. That is a per-partial-match cost,
so it scales with the intermediate size and mostly disappears with the ordering
fix; it is not worth attacking first.

## What this establishes

The 22.7x is not a per-match throughput result. Our per-match cost, once the join
order is right, is within 1.75x of egglog's on the same program: 0.89s against
508.3ms, with 1,418,980 matches found against their 943,092 applied. The pilot's
reading of this benchmark as a matching-throughput gap should be treated as
superseded by this file for the rules encoding; `README.md` states it as the
pilot's main negative finding, and that sentence needs revisiting once a planner
change lands.

What the gap actually measures is that our scheduler commits to a variable order
from static per-operator cardinalities, once per rule per iteration, and cannot
revise it. egglog re-sorts its remaining join stages by live subset size before
running and again every third stage, and chooses which side of each two-way
intersection to iterate by comparing the two built indexes
(`throughput-gap-egglog.md`, "How the associativity rule compiles"). On the
rooted chains that make up most of this file the difference does not show. On the
one query with two sibling atoms it is 88x in e-matching steps.

Three things follow, none of them done here. The cost model should charge a join
by fan-out per bound prefix rather than by a fixed halving of an absolute
cardinality, since the two probe kinds it treats identically differ by 494x on
this e-graph. A rooted pattern should prefer to drive from an atom that binds
other atoms' node variables, which is available statically from the query and
needs no cardinalities at all. And the 2.9% match-count difference between join
orders on one e-graph needs an explanation before either lands.
