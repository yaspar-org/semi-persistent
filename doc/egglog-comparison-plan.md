# Egglog comparison: constructor support, translation, and the AC benchmark

Plans the cross-engine comparison against egglog (surveyed at 7b1adf2). It is
a work plan, not a status page. Companion surveys: egglog's constructor
semantics and benchmark inventory (2026-08-15, recorded below in condensed
form), and our surface-language inventory
(`doc/design/A1-language-guide.md` holds the grammar).

## What the comparison is

Three configurations per benchmark, same machine, release builds:

1. egglog, release CLI, `-j 1`, `--mode no-messages` (their only
   nondeterminism source is threading; hashing is deterministic).
2. our engine, AC modelled as explicit commutativity/associativity rewrite
   rules (their encoding).
3. our engine, AC/ACI via native canonization (`:assoc-comm` attributes,
   the A/C rules deleted).

Metrics per run: wall time, node count, class count, iterations to
fixpoint or to goal. Their `(run N)` stops at fixpoint early, so report
both iterations-to-fixpoint and time at the declared budget; on `:until`
files report time-to-goal, the fair metric across engines with different
canonical forms. Never compare against their proof or term-encoding modes.

## Why egglog distinguishes constructors (condensed survey)

`constructor` is a term-former into an eqsort: lookup miss mints a fresh
e-class id, functional-dependency collisions resolve by union, extraction
eligible with `:cost` (default 1), subsumable. `function` is a partial map:
miss fails, mandatory `:merge` lattice or `:no-merge` assert-equal,
unextractable, no cost, and its lookup is banned on rule RHS because merge
expressions run as action-side writes where a live table read would be
invisible to semi-naive tracking. Split landed in their 0.4.0 (#461, #485).
In the pure-eqsat intersection every declared operator is a constructor.

## The intersection benchmark set (ranked)

1. `math-microbenchmark.egg`: purest AC stress, no primitives, ends in
   print-size/print-stats. Their own harness excludes it from proof mode as
   too heavy.
2. `web-demo/math.egg` lines 138-160: the isolated `add-ac` ruleset block,
   their one scoped AC experiment.
3. `web-demo/herbie.egg` (183 rewrites, BigRat) and
4. `repro-herbie-vanilla.egg` (471 rewrites): exercise our unbounded
   rationals; strip the two-function interval lattice and document the
   delta.
5. `integer_math.egg`: i64 shifts/division; strip the 13 universe-relation
   rules (their groundedness workaround, not part of the problem).
6. `calc.egg` / `until.egg`: associativity-only group theory with `:until`
   goals.
7. `web-demo/matrix.egg`: mixed AC and A-only operators in one signature.
8. `web-demo/eqsat-basic.egg`: calibration smoke test.
9. `web-demo/bdd.egg`: commutative-without-associative.
10. `web-demo/eqsolve.egg`: extraction-path coverage.

Qualitative companions, not timed: `eqsat-basic-multiset.egg` and
`factoring-multisets.egg` are egglog's multiset workaround for missing
native AC, with in-file comments noting they cannot match inside multisets.
Honest scoping fact for the write-up: egglog's own perf suite
(`scripts/bench.py`, 12 programs) is entirely container/lattice/subsume
workloads, disjoint from this intersection; the comparison covers their
test corpus's eqsat core, not their headline benchmarks, and conversely
those workloads exercise datalog/lattice/container machinery we lack.

## Work items

**E1. Constructor support in our engine.** The hooks exist unused:
`FLAG_CONSTRUCTOR` (`node_types.rs:35`, never read) and
`OpInfo.is_constructor` (`registry.rs`, hardcoded false);
`doc/design/16-extraction.md` lists weighted cost and constructor
preference as unimplemented. Add: `(constructor Name (Args) Ret tags)`
declaration form (and datatype variants declared as constructors), the
flag/OpInfo wired, per-op `:cost` (extraction currently hardcodes cost 1
per node) and `:unextractable` (either a new flag bit, 5 free, or an
extract-loop filter; note a subsumed node is extractable today, so
subsumption cannot fake it). Extraction respects cost and skips
unextractable ops.

**E2. Benchmark-support surface.** Rulesets (`:ruleset` on rewrite/rule,
`(run ruleset N)`), `:until` on run (goal facts, checked between
iterations), `birewrite` sugar, `print-size` and `print-stats` (nodes,
classes, iterations, match steps, wall time; machine-readable variant for
the harness). Our stats are today a single stderr line; the comparison
needs real output.

**E3. Translator.** Mechanical `.egg`(egglog) to `.egg`(ours):
function-to-constructor for term formers, bare literal ops to
sort-qualified (`+` to `IBig::+` or `i64::+` per benchmark type profile),
fact-form checks to `=`/`!=` forms, schedules to run budgets with
documented deviations, universe-relation boilerplate dropped with a note.
Per benchmark, also emit the native-AC dual (A/C rules deleted, operators
tagged). Every deviation goes in a per-benchmark ledger; a benchmark whose
deviations change the problem is dropped, not fudged. Reverse direction
where translation fails: emit egglog programs from our metamorphic and AC
families (`ac_vs_rules.rs` already generates the two-encoding pair from
one instance and is the precedent).

**E4. Harness.** Process-level timing (their protocol: release CLI, 15
runs, 3 warmups, hyperfine-style), matched budgets, JSON/CSV rows
(benchmark, config, time, nodes, classes, iterations), three configurations
per benchmark. Their machine-readable stats via `print-stats :file`; ours
via E2's stats output.

**E5. Quantify the value of AC canonization.** Already partially done:
the width sweep (flat 4n-3 nodes and one iteration against staircase
growth, 199x wall at n=28) and the mixed-workload deltas
(native vs our rules: 10.3x wall, 72x match steps on
math-microbenchmark). Remaining: re-run the mixed-workload comparison at
the post-fix engine commit so the native-vs-fixed-rules delta is honest,
and state the qualitative exhibit (their multiset emulation cannot match
inside multisets) with citations to their files.

**E6. Quantify the value of semi-persistence.** Not yet measured at all.
Design: (i) survey how egglog implements push/pop (snapshot copy?
rebuild? journal?) - the mechanism determines the expected separation
shape; (ii) micro-benchmark: base e-graph of S nodes (S in 1e4..1e6),
then N rounds of push, small assertion batch, run, check, pop; ours via
mark/restore (O(touched) by design) vs egglog's push/pop; report cost per
round vs S; (iii) macro: herbie.egg's fifteen push/run/check/pop blocks,
timed per block on both engines; (iv) internal baseline without egglog:
restore-to-mark vs re-running the program prefix from scratch, which is
the honest "what would you do without semi-persistence" comparison.
Deviation rules of methodology.md apply throughout.

Order: E1 and E2 (our-side features, one agent, two commits), then E3, then
E4 with a pilot on benchmarks 1, 2, 8 before the full set; E5/E6 after the
in-flight engine fixes land, at one pinned commit.

Status: every work item is delivered. E1 and E2 (constructor support and the
benchmark-support surface) are in the engine. E3 and E4 cover the full
ten-benchmark intersection set in `comparison/`, every benchmark with rules
and native encodings and a per-benchmark deviation ledger; eqsolve's native
encoding is validated under `--lazy-ac-eqs` and excluded from timed tables
on its measured completion cost, and `repro-herbie-vanilla` (ranked 4) is
dropped: at 7b1adf2 it is a typed-lowering unsoundness reproduction with no
checks, not the simplify layer at 2.9x
(`comparison/repro-herbie-vanilla.deviations.md`). E5 is answered by the
add-ac width sweep (`comparison/addac-sweep.md`: native AC flat at 4n-3
nodes and one iteration while the rules encoding reaches 37 902 nodes at
n = 20) and by the campaign's native columns. E6 is measured in
`comparison/semi-persistence/`: egglog's push deep-copies the e-graph, our
restore is O(touched), and at S = 1e6 the assume/derive/retract cycle costs
us 12.6 ms against their 33.0 ms while restoring to a mark beats re-running
the base 102x. The current campaign is `comparison/final/final-r3-tables.md`
(rules encoding at parity with egglog on solver-dominated workloads, native
2.4-2.8x faster); `comparison/methodology.md` is the divergence registry.
