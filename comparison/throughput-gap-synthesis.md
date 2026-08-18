# The 22.7x rules-encoding gap: side-by-side verdict

The gap is closed: the work items this synthesis opens are delivered
(design chapter 20, S1; `methodology.md` section 6) and the current campaign
has the rules encoding at parity on this benchmark. The file remains as the
measurement record of the diagnosis.

Synthesizes `throughput-gap-ours.md` (cb2170b) and
`throughput-gap-egglog.md` (8daa1f0) on
`comparison/math-microbenchmark.rules.egg`: same rules, same 11 iterations,
egglog 508 ms vs our 11.6 s. Every number below is measured in one of the
two companion docs.

## The decomposition

**95.3% of our 11.6 s is one rule under one bad join order.** Backward
distributivity `(Add (Mul a b) (Mul a c)) -> (Mul a (Add b c))`, the
benchmark's only 3-atom query, costs us 12,969 ms and 215.8 M e-matching
steps for 80,095 matches: 2,694 steps per match against 3.0-5.3 for every
other rule. The planner drives the join from a `Mul` atom; forcing the
`Add` atom first gives 82.6x on that rule and takes the whole program from
13.57 s to 0.89 s, total steps 220.7 M to 7.4 M. The residual gap to
egglog is 1.75x.

**The cost-model defect, precisely.** `schedule.rs` picks the cheapest
atom by `by_op` cardinality shifted right once per bound child: a fixed
halving per binding. Measured fan-outs on the iteration-8 e-graph:
`ByRepr` (node in a bound class) 2.51, `ByChildPos` (parents of a bound
child) 1,239. Charging both a halving underestimated the chosen join by
2,479x (estimated 27,025 intermediate matches, actual 66.98 M). Middle-out
selection is fine as a strategy; the per-index selectivity constants are
wrong by three orders of magnitude on parent-of-child probes.

**Semi-naive is exonerated on both engines.** Ours: the per-atom delta
restriction demonstrably reaches every atom (the three delta variants cost
72.6/18.5/6.6% of the naive join where cardinalities predict
78.4/16.9/4.1%), and `|delta|/|full|` never drops below 62%, reaching
86.9% (Add) at iteration 10. Theirs: `--naive` is marginally *faster*
(0.51 vs 0.52 s); their delta removes 11.9% of matches and pays 0.4% more
search doing it. The workload's last iteration grows `Add` 9.1x, so ~89%
of the table is new when the rules run: there is nothing for a delta to
exclude, in either engine. Semi-naive is not the differentiator here and
was not our defect.

## What the residual 1.75x is made of

- egglog's plans are frozen at declaration time but re-sorted at runtime
  by live subset size before the join and every third stage, and their
  2-way intersect iterates the smaller side: good orders emerge
  dynamically with no cardinality model to be wrong.
- Their column indexes are cached at the table level and refreshed
  incrementally from `updates_since`; we build indexes from scratch each
  iteration - but that costs us only 21.5 ms total here, so it is not the
  residual either. The remainder lives in join inner-loop constants
  (`LeapfrogJoin::search` is 52% of our profile) and per-partial-match
  setup (`LeapfrogJoin::new` + its insertion sort, 5.1%).
- Counterweight worth recording: our rebuild is 25 ms (0.34%) at 1.2 M
  nodes; egglog's rebuild is 218 ms, 42% of their run. Our maintenance
  path is substantially cheaper; their matching path is substantially
  cheaper. The two engines' costs live in different places.

## Blockers before the planner fix lands

The two orderings return match counts 2.9% apart on the same e-graph
(69,312 vs 67,293), inferred to come from `ExtractChild` reading the
e-graph live while `Join` reads the iteration's index snapshot.
Order-dependent match sets are a semantics wobble, not just a perf
question; characterize and fix (or prove benign) before any ordering
change ships. Second, smaller: the disabled match-step counter costs a
real 2.3% via an out-of-line TLS read per step, contradicting its
zero-cost comment.

## Work items this opens

1. Characterize the ExtractChild-vs-Join snapshot discrepancy; pin with a
   test; then fix the planner's selectivity constants: per-index-kind
   measured fan-outs (ByRepr vs ByChildPos) instead of fixed halving.
   Acceptance: math-microbenchmark rules encoding under 1 s without
   hand-pinned orders; differential fixture byte-identical (planner
   changes which matches are found first, so verify the fixture holds or
   review per protocol).
2. Move the match-step counter behind a compile-time flag or cached
   thread-local (2.3%).
3. Optional after 1: revisit index caching across iterations only if a
   post-fix profile still shows it; today it is 0.3%.
