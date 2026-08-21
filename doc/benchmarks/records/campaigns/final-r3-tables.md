# Campaign r3 (archived)

An archived campaign record; `final-r6-tables.md` is the newest retained
historical campaign, not a measurement of the current implementation.
One campaign at one engine commit, protocol as in `final-tables.md`. Raw
rows: `final-r3-results.csv`.

- **Pinned commit** b0c6dbb (branch egraph-wf: the engine with the
  `--union-by` survivor policy on the W7-verified class-size counter, the
  integer-to-rational lift with herbie's k-generic multiplicity variants,
  and the eqsolve match-volume measurement; methodology section 6).
- **Machine** the r1 machine (`final-tables.md`, pinning block).
- **Binaries** built at the pinned commit and egglog 7b1adf2 at its pinned
  1.91.0; md5s were not recorded for this campaign.
- **Statistic** the headline here and in r2 is a geometric mean of
  per-benchmark ratios; r1's headline is a median of ratios. The two
  statistics are not comparable across files.

**This campaign is a reproduction: every median matches `final-r2-tables.md`
within noise, and every node, class and iteration count is identical.** The
survivor policy sits behind a non-default flag and the campaign measures the
shipped default (`rank`); herbie's k-generic multiplicity variants are
verified latent on the shipped inputs; and extraction was measured at zero
share of eqsolve's wall time (`eqsolve.deviations.md`), so no timed
configuration exercises a changed code path.

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
