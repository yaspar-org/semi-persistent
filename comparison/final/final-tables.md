# FINAL comparison tables

> Archived campaign (r1). The current campaign is `final-r3-tables.md`; the
> numbers here predate the engine changes recorded in `../methodology.md`
> section 6.

**Campaign record.** Every number here is measured in one campaign, on one
quiet machine, at one pinned commit of each engine, on 2026-08-17. The protocol, the divergence registry and the per-benchmark ledgers it
depends on are in `../methodology.md` section "Final campaign"; the caveats
that registry attaches to individual benchmarks are restated inline below, so
that a table is never read without the qualification that governs it.

Raw data: `final-results.csv`, 460 timed runs, every run kept.

## What was measured

Ten benchmarks, the ranked intersection set. Each runs in up to five
configurations: egglog, and our two encodings (rules, which writes AC as
explicit rewrites, and native, which declares the operator AC) under each of
our two strategies (naive, our shipped default, and semi-naive). Two
benchmarks ship no native encoding at this campaign's commit: `herbie`'s and
`eqsolve`'s native programs postdate it. 46 configurations,
2 warmups and 10 timed runs each, medians reported.

## Headline

| comparison | all ten benchmarks | six solver-dominated benchmarks |
|---|---|---|
| egglog / ours, rules, naive | 1.85 | 0.95 |
| egglog / ours, rules, semi-naive | 2.15 | 1.95 |
| egglog / ours, native, naive | 2.03 (n=8) | 1.81 (n=4) |
| egglog / ours, native, semi-naive | 2.73 (n=8) | 3.31 (n=4) |

Median across benchmarks of the per-benchmark median wall time ratio, greater
than 1 meaning ours is faster.

**The two columns differ because process startup dominates four of the ten
benchmarks, and the paper must quote the right one.** An empty program costs
2.88 ms on our binary and 3.58 ms on egglog's, measured the same way as every
table here. On `eqsat-basic`, `calc`, `until` and `integer_math` our median is
under 4 ms, which leaves under 1 ms attributable to the solver, so those
ratios measure the 0.7 ms difference in process startup more than they measure
throughput. The right column restricts to the six benchmarks whose
solver-attributable time exceeds 5 ms, and it is the throughput claim: the
native encoding is 1.81x under naive and 3.31x under semi-naive, while the
rules encoding is at parity under naive (0.95x) and 1.95x under semi-naive.
The left column is the honest process-level number and is reported because it
is what the stated protocol measures, not because it is the stronger claim.

Single-benchmark ratios do not generalize, and the spread here shows why: the
two engines concentrate their cost in different places (methodology section
7), so the set deliberately spans AC-dominated, mixed and non-AC workloads.
The extremes are `eqsolve` at 0.20 and `herbie` at 4.21 in the same column.

## Median wall time, all configurations

Milliseconds, median of 10 timed runs after 2 warmups. Empty where the
benchmark ships no native dual. A dagger marks the four benchmarks whose
every one of our configurations lands under 4 ms, leaving under 1 ms
attributable to the solver: the startup qualification above governs their
ratios, and they are the four the restricted median excludes. math-add-ac's
native column is startup-dominated for the same reason while its rules column
is not, which is the collapse that benchmark exists to show.

| benchmark | egglog | rules, naive | rules, semi | native, naive | native, semi |
|---|---|---|---|---|---|
| eqsat-basic † | 5.9 | 3.3 | 3.3 | 3.3 | 3.2 |
| math-add-ac | 9.5 | 10.4 | 9.3 | 3.0 | 3.1 |
| math-microbenchmark | 507.0 | 518.6 | 540.0 | 456.5 | 428.8 |
| calc † | 8.3 | 3.4 | 3.4 | 3.4 | 3.5 |
| until † | 6.5 | 3.2 | 3.5 | 3.1 | 3.1 |
| integer_math † | 11.6 | 3.5 | 3.8 | 3.4 | 3.7 |
| matrix | 23.7 | 12.3 | 6.9 | 12.2 | 6.8 |
| bdd | 21.8 | 34.3 | 7.6 | 13.0 | 5.5 |
| herbie | 120.3 | 28.6 | 37.0 |  |  |
| eqsolve | 24.9 | 122.4 | 100.7 |  |  |

## Node counts are not comparable across engines

This qualification governs every table below and is not repeated in each one.
egglog prints post-rebuild table cardinality, which is congruence-deduplicated;
we count stored nodes, including nodes made duplicate by later congruence and
one node per interned literal. The verified probe is that after merging f(a)
with f(b), egglog prints `f: 1` and we print `f: 2`. The bias favors egglog in
any "smaller e-graph" reading, so we make no node-count claim against them:
the node columns support within-engine comparisons, rules against native and
naive against semi-naive, where the counting is consistent. egglog reports no
class count at all, so that column is empty for it.

Iteration counts are at-most-N with early exit on both engines, so an
iteration count below the program's budget means the run saturated and a count
equal to it means the budget truncated the run.

**The truncated-budget qualification.** Where the budget truncates the run,
the node and class counts are order-sensitive: the run stops mid-closure, so
what has been derived at that point depends on the order matches were found,
and two sound partitions can differ. This governs `math-add-ac`,
`math-microbenchmark`, `eqsolve`, and `matrix` under naive, whose iteration
counts equal their budgets in the tables below. It is why the two strategies
report different counts on the same program, and why methodology section 6
requires every table to be re-run at one pinned commit, which is what this
campaign is. Counts on saturating programs carry no such qualification.

## Per-benchmark results

### eqsat-basic

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 5.9 | 11 |  | 3 |
| ours, rules, naive | 3.3 | 17 | 11 | 3 |
| ours, rules, semi-naive | 3.3 | 17 | 11 | 3 |
| ours, native, naive | 3.3 | 14 | 11 | 3 |
| ours, native, semi-naive | 3.2 | 14 | 11 | 3 |

Its native dual declares `:comm` only, because the original has commutativity and no associativity rewrite; declaring AC would compare against a strictly stronger system. The native column is therefore not an AC measurement.

### math-add-ac

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 9.5 | 1939 |  | 7 |
| ours, rules, naive | 10.4 | 3317 | 159 | 7 |
| ours, rules, semi-naive | 9.3 | 3359 | 136 | 7 |
| ours, native, naive | 3.0 | 25 | 25 | 1 |
| ours, native, semi-naive | 3.1 | 25 | 25 | 1 |

The native column saturates at 25 nodes in one iteration because the AC operator canonizes what the rewrites otherwise enumerate: that collapse is the property the benchmark isolates, not a truncated run. Our two strategies materialize different node and class counts in the rules encoding (3 317 nodes / 159 classes naive against 3 359 / 136 semi-naive) because `(run add_ac 7)` reaches its budget along different paths; the ledger records that neither strategy has saturated.

**These counts supersede `math-add-ac.deviations.md`, which records 3 256 nodes / 148 classes naive and 3 304 / 134 semi-naive.** Those numbers were measured on 2026-08-15 in commit 0c5f9ee; roughly twenty ematch and scheduling commits landed between that date and the pin, several of which change which matches are found in which round (`90e2d5f` per-access-path selectivity, `5d85c53` canonicalization against the round's index snapshot, `ca2088b` the semi-naive root-binding join). On a program that does not saturate within its budget, the count at the budget depends on that order, so the movement is the order-sensitivity methodology section 4 records, and superseding the older number is the reason section 6 requires every table to be re-run at one pinned commit. The pinned counts are deterministic: five consecutive naive runs and three semi-naive runs report the same figures. The egglog column did not move (1 939 nodes / 7 iterations, unchanged), and the benchmark's check passes in all four of our configurations, so the divergence is in how much work the budget buys and not in what the run concludes.

The registry's caveat needs one widening, recorded in methodology section 4: it was written for class counts, on the evidence that the add_use prepend left node counts identical and moved only classes by 6 ppm. Here node counts move too, by 61 nodes (1.9%), so the caveat is restated to cover both counts on non-saturating programs.

### math-microbenchmark

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 507.0 | 1047896 |  | 11 |
| ours, rules, naive | 518.6 | 1233013 | 507995 | 11 |
| ours, rules, semi-naive | 540.0 | 1254903 | 518063 | 11 |
| ours, native, naive | 456.5 | 755926 | 446915 | 11 |
| ours, native, semi-naive | 428.8 | 755917 | 446915 | 11 |

`(run 11)` reaches its cap in every configuration, so the run stops mid-closure and the class counts are order-sensitive: methodology section 4 records the add_use prepend moving this count 507 992 -> 507 995 (+3, 6 ppm) with both partitions sound. The native column restates eleven rules in n-ary rest-variable form, which is the same mathematics and not the same program, because binary patterns are exact against flattened variadic nodes.

### calc

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 8.3 | 5 |  | 4 |
| ours, rules, naive | 3.4 | 8 | 8 | 1 |
| ours, rules, semi-naive | 3.4 | 8 | 8 | 1 |
| ours, native, naive | 3.4 | 8 | 8 | 1 |
| ours, native, semi-naive | 3.5 | 8 | 8 | 1 |

**Multi-block: wall time is the metric.** The work happens inside four `push`/`run`/`check`/`pop` blocks and the counts print after the last `(pop)`, so they describe the base state and reflect none of the work. The node and iteration columns are reported only to show the runs happened.

### until

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 6.5 | 7 |  | 3 |
| ours, rules, naive | 3.2 | 52 | 15 | 3 |
| ours, rules, semi-naive | 3.5 | 75 | 22 | 4 |
| ours, native, naive | 3.1 | 22 | 9 | 2 |
| ours, native, semi-naive | 3.1 | 17 | 9 | 2 |

**Goal-terminated: the node column is not an e-graph size comparison.** The run halts on a `:until` goal while a non-terminating rule generates, so the size at the moment the goal is noticed depends on encoding and strategy: 52 nodes naive against 75 semi-naive, both correct. Its `allgs` datalog relation is re-encoded as a constructor in all three configurations, so relation entries count as nodes on both engines.

### integer_math

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 11.6 | 100 |  | 4 |
| ours, rules, naive | 3.5 | 116 | 49 | 4 |
| ours, rules, semi-naive | 3.8 | 117 | 50 | 4 |
| ours, native, naive | 3.4 | 34 | 24 | 4 |
| ours, native, semi-naive | 3.7 | 34 | 24 | 4 |

**Scoped column: not comparable to upstream integer_math.** Thirteen universe-relation rules that exist as egglog's groundedness workaround are dropped, which takes term nodes from 537 to 100 at `(run 4)`, an 81% reduction. The same reduced program runs in all three configurations. Ledger: `integer_math.deviations.md`.

### matrix

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 23.7 | 53 |  | 13 |
| ours, rules, naive | 12.3 | 92 | 25 | 10 |
| ours, rules, semi-naive | 6.9 | 91 | 25 | 4 |
| ours, native, naive | 12.2 | 91 | 25 | 10 |
| ours, native, semi-naive | 6.8 | 90 | 25 | 4 |

The program has two `(run ...)` blocks and the iteration column reports the second only: naive reaches that block's cap of 10 while semi-naive saturates at 4. Its native column carries native AC on `Times` only, because restating the eight `MMul`/`Kron` rules n-ary drives the matcher to read an unbound variable and panic (methodology section 6, 2026-08-17). The A-only comparison this benchmark was selected for is postponed, not delivered.

### bdd

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 21.8 | 99 |  | 9 |
| ours, rules, naive | 34.3 | 337 | 16 | 9 |
| ours, rules, semi-naive | 7.6 | 241 | 16 | 7 |
| ours, native, naive | 13.0 | 206 | 16 | 10 |
| ours, native, semi-naive | 5.5 | 136 | 16 | 8 |

Selected as the commutative-without-associative case, so its native dual declares `:comm` and deletes three commutativity rewrites; nothing else changes. Unlike `calc`, the counts print before the single `(pop)` and describe the saturated graph. Our two strategies differ in nodes (337 against 241 rules, 206 against 136 native) for the reason `math-add-ac` records.

### herbie

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 120.3 | 6 |  | 24 |
| ours, rules, naive | 28.6 | 11 | 11 | 1 |
| ours, rules, semi-naive | 37.0 | 11 | 11 | 1 |

**Scoped column, and multi-block: wall time is the metric.** The 2-function interval lattice, the `non-zero` relation it feeds, and five rational constant folds are stripped from the egglog program as well as ours, leaving 163 of 180 rewrites and 12 of 14 blocks, on which both engines agree. The iteration columns are not comparable: egglog's stats accumulate one entry per iteration across all twelve `(run ...)` commands while ours reports the last only, which is the 24 against 1 that methodology section 3 records. Its native encoding postdates this campaign's commit. Ledger: `herbie.deviations.md`.

### eqsolve

| configuration | median wall (ms) | nodes | classes | iterations |
|---|---|---|---|---|
| egglog | 24.9 | 2110 |  | 6 |
| ours, rules, naive | 122.4 | 9583 | 1567 | 6 |
| ours, rules, semi-naive | 100.7 | 9085 | 1534 | 6 |

The set's only extraction-path benchmark. Both engines take a budget of 6 rather than the original 5, because at 5 our engine has not yet joined `(Var "x")` to `(Num 5)`, and the three extracted answers are asserted rather than only printed. The budget is reached in every configuration, so its counts carry the truncated-budget qualification above. Its native-AC dual is postponed on a measured cause: `--derive-ac-eqs` does not terminate within 120 s on this program.

## Reproducing

```
cd comparison && python3 run-full.py --label final --runs 10 --warmups 2
```

Per-benchmark invocation with `--benchmark NAME` produced the campaign, so
that a failure would lose one benchmark and not the run; the ten resulting
files were concatenated into `final-results.csv` with the label unchanged.
Every configuration reproduced the node, class and iteration counts its
committed ledger records, to the digit, which is the check that the campaign
measured the same programs the ledgers describe. The one exception is
math-add-ac's rules encoding, whose counts moved because the program does not
saturate within its budget and the engine's match order changed after the
ledger was written: its section above gives the numbers and the cause, and
methodology section 4 records the widened caveat.
