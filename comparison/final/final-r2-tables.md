# Final campaign, second run (final-r2)

One measurement pass at one commit (the engine after the semi-naive
class-growth fix, the coincidence twins, RHS multiplicity expressions, and the
herbie native dual; methodology section 6 entries dated 2026-08-17). Protocol
as in `final-tables.md`: process-level wall time, 2 warmups + 10 runs, medians,
egglog release CLI with `-j 1 --mode no-messages`. Raw rows:
`final-r2-results.csv`. This run supersedes `final-tables.md` where the two
differ; the first run remains the pre-fix record and its budget-capped
semi-naive rows must not be cited as complete derivations (methodology
section 6).

What changed since the first run:

- **herbie has a native column** (hand-derived dual, `herbie.deviations.md`):
  14.3 ms naive / 20.4 ms semi against egglog's 129.2 ms and our own rules
  encoding's 28.6 ms. The largest AC rule set in the intersection is also the
  clearest native win: 9.0x over egglog, 2.0x over our rules encoding.
- **Semi-naive derives completely** (the class-growth fix): its node counts on
  budget-capped programs moved (eqsolve.rules 9 085 -> 9 398,
  math-microbenchmark.rules 1 254 903 -> 1 248 629 at different class counts),
  and math-microbenchmark's rules-semi wall went 540 ms -> 1 639 ms. That cost
  is real: recording class-membership growth inflates the per-round deltas on
  merge-heavy workloads, and the pre-fix number was cheaper because the
  strategy silently skipped derivations. The follow-up (a per-round
  merged-class set consulted by the delta variants, instead of member nodes
  pushed into the touched log per merge) is recorded in the task list.
- **The twin-carrying native files are byte-identical in counts** to the first
  run: the coincidence twins and distributivity twins fire zero times on the
  shipped workloads.

## Headline: wall-time ratios egglog / ours (geometric means over benchmarks)

| configuration | all (n) | solver-dominated (n) |
|---|---|---|
| egglog / ours, rules, naive | 1.45 (10) | 1.03 (6) |
| egglog / ours, rules, semi-naive | 1.40 (10) | 1.00 (6) |
| egglog / ours, native, naive | 2.48 (9) | 2.53 (5) |
| egglog / ours, native, semi-naive | 2.65 (9) | 2.93 (5) |

Above 1 means we are faster. Solver-dominated excludes the four
startup-dominated programs (eqsat-basic, calc, until, integer_math, all under
13 ms on both engines). The rules encoding is at parity with egglog on
solver-dominated workloads; native AC canonization is the separation, now
carried by five benchmarks including the largest rule set (herbie).

## Per-benchmark medians (ms)

| benchmark | egglog | rules, naive | rules, semi | native, naive | native, semi |
|---|---|---|---|---|---|
| eqsat-basic | 6.1 | 3.4 | 3.4 | 3.2 | 3.3 |
| math-add-ac | 10.0 | 10.5 | 11.3 | 3.4 | 3.1 |
| math-microbenchmark | 511.8 | 525.0 | 1638.6 | 487.7 | 490.3 |
| calc | 8.5 | 3.4 | 3.5 | 3.3 | 3.5 |
| until | 6.7 | 3.2 | 3.3 | 3.2 | 3.2 |
| integer_math | 12.9 | 3.6 | 3.9 | 3.7 | 4.0 |
| matrix | 25.7 | 12.8 | 6.9 | 12.6 | 6.9 |
| bdd | 23.5 | 33.9 | 19.7 | 13.2 | 8.6 |
| herbie | 129.2 | 28.6 | 35.4 | 14.3 | 20.4 |
| eqsolve | 25.9 | 123.6 | 119.1 |  |  |

matrix additionally ships its native-A column: 6.1 ms naive / 4.3 ms semi
(62 nodes, 23 classes), the first timing for that configuration (it landed
after the first campaign). eqsolve's native column stays postponed on
completion cost; its ledger (same date) records the measured verdicts of all
three completion modes on the experimental dual. Node counts and their
comparability caveats are unchanged from `final-tables.md` sections 3-4; the
only moved counts are the two semi-naive rows named above.
