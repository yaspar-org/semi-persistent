# Final campaign, third run (final-r3)

One measurement pass at one commit (the engine after the `--union-by` survivor
policy with the W7-verified class-size counter, the integer-to-rational lift
with herbie's k-generic twins, and the eqsolve extraction-attribution
correction; methodology section 6 entries dated 2026-08-18). Protocol as in
`final-tables.md`. Raw rows: `final-r3-results.csv`.

**This run is a reproduction: every row matches `final-r2-tables.md` within
noise, and every node, class and iteration count is identical.** That is the
predicted outcome — the survivor-policy win sits behind a non-default flag
(the campaign measures the shipped default, `rank`), the new herbie twins are
verified latent on the shipped inputs, and the extractor rewrite was dropped
after profiling refuted its premise (`eqsolve.deviations.md`, same date).

## Headline: wall-time ratios egglog / ours (geometric means)

| configuration | all (n) | solver-dominated (n) |
|---|---|---|
| egglog / ours, rules, naive | 1.38 (10) | 0.98 (6) |
| egglog / ours, rules, semi-naive | 1.33 (10) | 0.94 (6) |
| egglog / ours, native, naive | 2.39 (9) | 2.43 (5) |
| egglog / ours, native, semi-naive | 2.54 (9) | 2.77 (5) |

Same reading as r2: rules encoding at parity on solver-dominated workloads,
native AC canonization the separation. The r2-vs-r3 headline drift (2.53 to
2.43 on native-naive, and siblings) is run-to-run noise on the small
denominators, not a code effect: no engine path a default-flag run exercises
changed between the two commits.

## Per-benchmark medians (ms)

| benchmark | egglog | rules, naive | rules, semi | native, naive | native, semi |
|---|---|---|---|---|---|
| eqsat-basic | 6.1 | 3.2 | 3.3 | 3.3 | 3.3 |
| math-add-ac | 9.7 | 10.4 | 11.1 | 3.1 | 3.1 |
| math-microbenchmark | 511.6 | 534.8 | 1665.1 | 480.4 | 486.8 |
| calc | 8.3 | 3.5 | 3.6 | 3.4 | 3.4 |
| until | 6.6 | 3.4 | 3.3 | 3.2 | 3.2 |
| integer_math | 11.6 | 3.6 | 3.8 | 3.6 | 4.0 |
| matrix | 23.4 | 12.5 | 6.9 | 12.5 | 7.0 |
| bdd | 21.7 | 33.6 | 19.4 | 13.3 | 8.6 |
| herbie | 120.2 | 28.9 | 37.1 | 14.1 | 20.6 |
| eqsolve | 24.9 | 127.7 | 118.0 |  |  |

matrix native-A: 6.1 / 4.3 ms, matching r2.

## Supplementary: the survivor policy on the merge-heavy row

math-microbenchmark's rules-semi cell is the one row `--union-by` changes
(measured at this commit, 3 runs each, not part of the default-flag campaign):
1.69 s under `rank` (the row above), 0.60 s under `size`, `uses` and `sum`,
with the identical complete derivation. The policy is opt-in; if a later
campaign adopts a directed default, its rows re-measure under that default
and say so.
