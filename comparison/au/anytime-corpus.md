# AU anytime and regret corpus

Records what the anti-unification corpus of plan item B3 measures, how to
regenerate it, and what the four curves show. It is not a status page for the
solvers: what the solvers do is what `egraph/tests/au_differential.rs` and the
rest of the AU suite assert.

The corpus answers how far MCGS is from the optimum as a function of its
budget, on both budget axes (playouts, and wall clock relative to the exact
solver), and how much budget a completion certificate costs against B1's
prediction that certification needs about `sum A(v)` playouts.

Three runs, 2026-08-16 and 2026-08-17, release build on Apple Silicon. The main
run is 673 instances, 10095 rows, 1854 s wall; the deep-ladder run repeats the
`dec` and `mixed` families to 2^18 playouts (438 instances, 8322 rows, 1317 s)
to see whether the budget, rather than the algorithm, was what stopped
certification; the closed-bit run repeats the same two families on the main
run's ladder with plan item A8's selection rule on (438 instances, 6570 rows,
612 s). Every spec of all three was measured: no exact timeout, no MCGS
timeout, no ladder cut on the per-instance budget, no instance past the wall
budget. Tables (a) to (d) are the main run, whose ladder is 2^0 to 2^14; table
(e) is the deep-ladder run; table (f) is the closed-bit run and is the only
one whose MCGS runs are not the default configuration. The exact solver runs
with `exact_pruning` and `context_subsumption` on in all three.

## Regenerating

```text
AU_BENCH_DIR=comparison/au AU_CORPUS_SECS=5400 \
  cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  -- --ignored --nocapture
python3 comparison/au/analyze.py comparison/au/corpus.csv
```

The deep-ladder run is the same harness with three knobs:

```text
AU_BENCH_DIR=comparison/au AU_CSV_NAME=corpus-deep.csv AU_FAMILIES=dec,mixed \
  AU_LADDER_TOP=262144 AU_CORPUS_SECS=7200 \
  cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  -- --ignored --nocapture
python3 comparison/au/analyze.py comparison/au/corpus-deep.csv
```

The closed-bit run of section (f) is the same harness with the flag on, in its
own CSV because it is a different solver configuration:

```text
AU_BENCH_DIR=comparison/au AU_CSV_NAME=corpus-closed.csv AU_FAMILIES=dec,mixed \
  AU_CLOSED_BIT=1 AU_CORPUS_SECS=1800 \
  cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  -- --ignored --nocapture
python3 comparison/au/analyze.py comparison/au/corpus-closed.csv
```

`AU_CORPUS_SECS` is the wall budget after which no new instance starts; the
CSV is flushed per line, so a killed run leaves usable data. `AU_MIN_EXACT_MS`
reinstates a hardness floor. Extending the corpus means widening the parameter
grids in `corpus()` and raising `AU_CORPUS_SECS` in proportion. This run spent
1854 s on 673 instances, of which 599 s is solver time (518 s of that on the
70 `wide`, `width`, and `ac` instances) and the rest is instance construction,
which every guarded run repeats on its worker thread, plus the census walks.

The generators are `egraph/tests/au_deceptive.rs` (the deceptive family, its
mixing into random cyclic backbones, and the wide variant) and the family
builders in `egraph/tests/au_corpus_bench.rs`. The certification budget comes
from `egraph/src/au/census.rs`, which enumerates the search graph without
solving it, so `sum A(v)` is measured independently of the runs it predicts.

## Caveats

**The corpus is selected, and the selection is not the plan's.** Ground truth
is the exact solver under a 60 s guard; an instance that does not finish is
dropped, and none was. The plan also called for a 10 ms hardness floor. The
calibration sweep (`calibrate_hardness` in the harness) shows why this run
does not apply one: with A2 and A6 on, the cyclic families solve in
microseconds, the crossover family at `cycles=20` in 0.3 ms and the mixed
family at `cycles=24` in 0.4 ms, so a 10 ms floor selects the `width` and `ac`
families and nothing else. The floor is reported rather than applied: every
instance carries its `exact_ms`, 45 of the 673 are at or above 10 ms, and the
wall-clock tables are computed on that subset.

**MCGS is deterministic**, so one run per (instance, budget) is the complete
picture, and no distribution over repetitions exists. All per-instance
variation comes from the generation seeds.

**Wall-clock numbers were measured on a shared machine**, concurrently with
another agent's builds on the same host. The wall-clock tables carry that
noise; the playout-axis tables do not, because the answer at a given budget is
a deterministic function of the instance.

**The ladder is coarse.** Budgets double, so a knee reported at budget b means
the certificate appeared in `(b/2, b]`, and every knee ratio carries that
factor-2 granularity.

**The census counts the unpruned budget.** `sum A(v)` is cycle-filtered but
not dominance-filtered, which is what the prediction is stated over and what
the measured runs do (`dominance_pruning` is off by default). A5 records how
much smaller the pruned budget is on cycle-heavy shapes. 38 of 673 instances
hit the census cap (4e6 OR states or 20 s); their `sum A(v)` is a lower bound
and they are excluded from the knee tables.

**MCGS does not stop when the search graph closes.** On a `dec` instance with
`sum A(v) = 6`, the certificate is available at 16 playouts and the run at
16384 playouts still takes 10.8 ms against 0.03 ms at 16, growing linearly in
the budget. Wall-clock costs above the knee are therefore the cost of playouts
that realize nothing, not of the certificate. This holds for the flag-off
tables below, which are every table except (f): the closed bit knows when the
graph has closed and stops there, and section (f) reports what that is worth.

## Families

| family | instances | shape | median exact ms | median `sum A(v)` |
| --- | --- | --- | --- | --- |
| `dec` | 258 | the deceptive gadget alone | 0.13 | 32 |
| `wide` | 40 | a deceptive gadget under a width spine | 27.63 | 98348 |
| `mixed` | 180 | gadgets planted in a random cyclic backbone | 0.20 | 210310 |
| `rand` | 120 | the same backbone without gadgets | 0.07 | 1327426 |
| `xover` | 45 | the crossover family | 0.05 | 36754 |
| `width` | 15 | acyclic spine, `width` members per level | 6.84 | 32768 |
| `ac` | 15 | one MSet pair, `members` monomials per side | 64.58 | 4096 |

## Greedy is wrong on 71% of the corpus

MCGS at one playout is the initial rollout, the greedy descent that ranks
actions by the lazy-completion estimate. It returns a suboptimal term on 478
of 673 instances, and the split is by construction:

| family | n | greedy wrong | mean relative gap | max |
| --- | --- | --- | --- | --- |
| `dec` | 258 | 1.000 | 0.195 | 0.722 |
| `wide` | 40 | 1.000 | 0.105 | 0.233 |
| `mixed` | 180 | 1.000 | 0.150 | 0.483 |
| `rand` | 120 | 0.000 | 0 | 0 |
| `xover` | 45 | 0.000 | 0 | 0 |
| `width` | 15 | 0.000 | 0 | 0 |
| `ac` | 15 | 0.000 | 0 | 0 |
| all | 673 | 0.710 | 0.121 | 0.722 |

The three families that carry a deceptive gadget are wrong on every instance,
and the four that do not are optimal at one playout on every instance. The
pilot's finding that the symmetric families are decided by depth-1 information
holds at 673 instances: without a constructed misranking, the greedy descent
is already optimal, which is why B2 exists.

## (a) Simple regret against the playout budget

Relative size gap `(mcgs_size - exact_size) / exact_size`, over all 673
instances. The zero mass is reported separately from the mean among nonzero
gaps, because 29% to 80% of the mass is exactly zero and a mean over both
mixes two different quantities.

| playouts | zero fraction | mean | median | p90 | mean over nonzero | max |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 0.290 | 0.1213 | 0.0556 | 0.3737 | 0.1708 | 0.7222 |
| 2 | 0.312 | 0.1130 | 0.0455 | 0.3261 | 0.1642 | 0.7222 |
| 4 | 0.334 | 0.1046 | 0.0448 | 0.3095 | 0.1572 | 0.7222 |
| 8 | 0.377 | 0.0912 | 0.0409 | 0.2857 | 0.1464 | 0.7222 |
| 16 | 0.415 | 0.0822 | 0.0366 | 0.2633 | 0.1405 | 0.7222 |
| 32 | 0.450 | 0.0737 | 0.0294 | 0.2143 | 0.1340 | 0.5909 |
| 64 | 0.483 | 0.0683 | 0.0122 | 0.2059 | 0.1321 | 0.5909 |
| 128 | 0.532 | 0.0610 | 0 | 0.2059 | 0.1304 | 0.5909 |
| 256 | 0.599 | 0.0495 | 0 | 0.1667 | 0.1234 | 0.5909 |
| 512 | 0.637 | 0.0407 | 0 | 0.1554 | 0.1122 | 0.5909 |
| 1024 | 0.661 | 0.0360 | 0 | 0.1356 | 0.1062 | 0.4118 |
| 2048 | 0.712 | 0.0273 | 0 | 0.1000 | 0.0949 | 0.4118 |
| 4096 | 0.758 | 0.0227 | 0 | 0.0714 | 0.0939 | 0.4118 |
| 8192 | 0.782 | 0.0173 | 0 | 0.0455 | 0.0792 | 0.4118 |
| 16384 | 0.798 | 0.0155 | 0 | 0.0432 | 0.0768 | 0.4118 |

The curve is not flat: the mean gap falls 7.8x from one playout to 16384 and
the zero fraction rises from 0.290 to 0.798. Both movements come from the
deceptive families. The zero fraction by family at 1, 128, and 16384 playouts
is `dec` 0.000 to 0.450 to 0.771, `mixed` 0.000 to 0.261 to 0.761, `wide`
0.000 to 0.000 to 0.150, and 1.000 at every budget for `rand`, `xover`,
`width`, and `ac`.

The mean among nonzero gaps falls only 2.2x (0.171 to 0.077) while the zero
fraction rises 2.8x: most of the improvement is instances crossing to zero,
not instances improving gradually. That is what the gadget's structure
predicts. Its regret is a single wrong choice at the root, so an instance is
either still taking the decoy or has found the winner.

On the 45 instances with exact at or above 10 ms, the curve is flat at
mean 0.0516 and zero fraction 0.444 at every budget from 1 to 16384. Those 45
are 25 `wide`, 13 `ac`, and 7 `width`: the `ac` and `width` instances are
optimal at one playout and the `wide` instances do not close within 16384
playouts, because each spine level costs `width^2` actions before the buried
gadget is reachable. Hardness and improvability are not the same property, and
on this corpus they are anticorrelated.

## (b) Regret against wall clock, normalized by exact

On the same 45 instances, the entry cost dominates. The cheapest MCGS run of
an instance, the one playout that is the initial rollout, costs a median 0.545
of the exact solver's total time (p10 0.522, p90 2.398), because the initial
rollout is a full greedy descent that does per-node work comparable to exact
along one path.

| budget as a fraction of exact | instances with a run inside it | zero fraction | mean gap | p90 |
| --- | --- | --- | --- | --- |
| 0.1% | 0 | - | - | - |
| 1% | 0 | - | - | - |
| 5% | 0 | - | - | - |
| 10% | 0 | - | - | - |
| 25% | 0 | - | - | - |
| 50% | 0 | - | - | - |
| 100% | 32 of 45 | 0.219 | 0.0726 | 0.1667 |

The whole sub-50% region of the time axis is empty on this corpus: there is no
budget below half of exact's time at which MCGS returns anything at all. At
100% of exact's time, MCGS has an answer on 32 of 45 instances and that answer
is optimal on 21.9% of them. The statement "X% of optimal at N% of exact's
budget" has no data below N = 100 here, and the reason is measured, not
inferred: it is the initial rollout's cost, which A0's expansion work did not
touch.

## (c) Certification against the playout budget

| playouts | certified fraction |
| --- | --- |
| 1 to 8 | 0.000 |
| 16 | 0.016 |
| 64 | 0.052 |
| 256 | 0.080 |
| 1024 | 0.134 |
| 4096 | 0.162 |
| 16384 | 0.193 |

130 of 673 instances certify within 16384 playouts, against 0 of 263 in the
pilot. The pilot's filter selected instances whose `sum A(v)` was 1e4 to 1e6
against a 4096 ladder; this corpus reaches instances whose budget the ladder
can pay.

### The knee prediction

B1 predicts certification at about `sum A(v)` playouts. The census computes
`sum A(v)` per instance without running the search, so the prediction is
tested against an independent quantity. Buckets are decades of `sum A(v)`; 38
capped instances are excluded.

| `sum A(v)` decade | n | certified | median `sum A(v)` | median knee | knee / `sum A(v)` | ladder top below `sum A(v)` |
| --- | --- | --- | --- | --- | --- | --- |
| 1e0 | 22 | 1.000 | 8 | 40 | 4.89 | 0 |
| 1e1 | 264 | 0.284 | 36 | 512 | 20.48 | 0 |
| 1e2 | 33 | 0.364 | 121 | 768 | 3.20 | 0 |
| 1e3 | 25 | 0.640 | 3072 | 4096 | 1.56 | 0 |
| 1e4 | 80 | 0.062 | 26287 | 16384 | 1.00 | 54 |
| 1e5 | 101 | 0 | 210933 | - | - | 101 |
| 1e6 | 78 | 0 | 5335252 | - | - | 78 |
| 1e7 | 70 | 0 | 32963188 | - | - | 70 |

No instance certifies below its `sum A(v)`, so the bound direction holds
everywhere: `sum A(v)` is a lower bound on the certification budget, as the
exhaustiveness argument requires. Above 1e4 the ladder itself is the binding
constraint, and no instance whose `sum A(v)` exceeds 16384 certifies.

The prediction that the knee is *at* `sum A(v)` splits by search-graph shape,
which the decade buckets mix and the family breakdown separates:

| family | certified | median `sum A(v)` | median knee | knee / `sum A(v)` |
| --- | --- | --- | --- | --- |
| `width` | 7 | 4096 | 4096 | 1.00 |
| `ac` | 15 | 4096 | 4096 | 1.78 |
| `wide` | 2 | 3080 | 6144 | 1.99 |
| `xover` | 12 | 160 | 512 | 4.33 |
| `dec` | 83 | 15 | 256 | 17.07 |
| `mixed` | 11 | 25 | 512 | 19.69 |

On wide, shallow search graphs the prediction holds: `width`, `ac`, and `wide`
certify within a factor of 2 of `sum A(v)`, which is inside the ladder's own
factor-2 granularity. On deep, narrow graphs it fails by an order of
magnitude, and the miss grows with depth rather than with the action count:

| burial depth | n | certified | median `sum A(v)` | median knee | knee / `sum A(v)` |
| --- | --- | --- | --- | --- | --- |
| 3 | 33 | 1.000 | 9 | 64 | 7.11 |
| 5 | 39 | 0.897 | 15 | 512 | 34.13 |
| 8 | 45 | 0.333 | 24 | 2048 | 128.00 |
| 12 | 45 | 0 | 36 | - | - |
| 16 | 48 | 0 | 48 | - | - |
| 20 | 48 | 0 | 60 | - | - |

`sum A(v)` grows linearly with the burial depth, from 9 to 60, while the knee
grows from 64 to beyond 16384, and the deep-ladder run shows the ladder was
not what stopped it: at 2^18 playouts, 7281 times the predicted 36, no
instance at burial depth 12 certifies.

Verdict: the prediction is refuted as stated and holds in one direction.
`sum A(v)` counts the edges a certificate must realize and one playout
realizes at most one edge, so it is a lower bound. What it omits is which
edges a playout can reach. Selection descends by UCB1, which gives an arm that
looks worse by a margin only logarithmically many visits in the total budget,
so the actions buried behind a misranked action are realized after a budget
exponential in the burial depth, not linear in the action count. The deceptive
family isolates exactly that: it is the family whose whole construction is a
misranked action, and it is the family where the prediction misses by two
orders of magnitude and more.

The concrete consequence for the solver is a selection rule, not a bigger
budget: MCGS keeps descending into subtrees that are already closed, so a
playout spent there realizes nothing. Excluding closed children from selection
(the MCTS-solver rule) is what would make the certification budget track
`sum A(v)` on deep graphs, and it is testable against this corpus, since the
knee column is what it has to move. Section (f) is that test, run on the same
instances: the knee moves to 1.3x `sum A(v)`.

## Playouts to gap zero

The budget at which MCGS first returns an optimal term, on the main run's
ladder:

| family | n | reaches gap 0 | p50 | p90 | max |
| --- | --- | --- | --- | --- | --- |
| `dec` | 258 | 0.771 | 64 | 4096 | 16384 |
| `wide` | 40 | 0.150 | 6144 | 8192 | 8192 |
| `mixed` | 180 | 0.761 | 512 | 4096 | 16384 |
| `rand` | 120 | 1.000 | 1 | 1 | 1 |
| `xover` | 45 | 1.000 | 1 | 1 | 1 |
| `width` | 15 | 1.000 | 1 | 1 | 1 |
| `ac` | 15 | 1.000 | 1 | 1 | 1 |

On the deceptive family the budget is geometric in both knobs, which is the
mechanism behind the certification result above: each additional decoy is one
more arm that outranks the winner on the estimate, and each additional level
is one more such choice to make in sequence.

| burial depth | 1 decoy | 2 decoys | 4 decoys |
| --- | --- | --- | --- |
| 3 | 2 | 4 | 8 |
| 5 | 8 | 16 | 32 |
| 8 | 16 | 64 | 256 |
| 12 | 128 | 1024 | 4608 |
| 16 | 512 | 2048 | 8192 |
| 20 | 4096 | 8192 | - |

Median playouts to gap 0 over the instances that reach it; at burial depth 20
that is 75%, 19%, and 6% of the instances respectively, and the last cell has
too few to report.

## (e) The deep ladder: quality converges, certification does not

Repeating the `dec` and `mixed` families to 2^18 separates two questions the
main run's ladder conflates.

| playouts | zero fraction | mean gap | certified fraction |
| --- | --- | --- | --- |
| 1 | 0.000 | 0.1768 | 0.000 |
| 256 | 0.475 | 0.0664 | 0.117 |
| 4096 | 0.712 | 0.0266 | 0.194 |
| 16384 | 0.767 | 0.0165 | 0.215 |
| 65536 | 0.829 | 0.0122 | 0.231 |
| 262144 | 0.886 | 0.0076 | 0.242 |

Quality keeps converging: the zero fraction rises from 0.767 to 0.886 and the
mean gap halves between 2^14 and 2^18. Certification moves 0.215 to 0.242 over
the same 16x budget. On the deceptive family at burial depth 12, MCGS returns
the optimum at a median 128 playouts and has not proved it at 262144, a factor
of 2000 between finding and proving on instances whose entire search graph is
36 actions wide. Finding the optimum and certifying it are different problems
here, and only the first one is what the budget buys.

## (d) Time to optimum against exact's completion

| family | n | reaches gap 0 within 16384 playouts | reaches it before exact finishes | median time ratio at gap 0 |
| --- | --- | --- | --- | --- |
| `dec` | 258 | 0.771 | 0.360 | 1.03 |
| `wide` | 40 | 0.150 | 0 | 213.81 |
| `mixed` | 180 | 0.761 | 0.017 | 11.48 |
| `rand` | 120 | 1.000 | 0.625 | 0.93 |
| `xover` | 45 | 1.000 | 0.822 | 0.84 |
| `width` | 15 | 1.000 | 1.000 | 0.73 |
| `ac` | 15 | 1.000 | 0 | 2.41 |
| all | 673 | 0.798 | 0.331 | 1.08 |

MCGS reaches the optimum on 79.8% of the corpus within 16384 playouts and
reaches it faster than the exact solver finishes on 33.1%. The two rows that
matter are `width`, where MCGS is optimal at one playout costing 0.73 of
exact's time, and `wide`, where it needs 214x exact's time on the instances
where it gets there at all. The families where MCGS wins on time are the ones
where its first answer is already optimal; the families where it loses are the
ones where the first answer is wrong, which is the same split as table (a) and
the reason the anytime story on this corpus is about the initial rollout
rather than about the ladder.

## (f) The closed bit, 2026-08-17: the knee moves to 1.3x `sum A(v)`

Plan item A8 excludes fully resolved subgraphs from selection: an OR node
carries a bit set once every action below it is realized and every descendant
is closed, and neither `select_uct` nor the AND selectors descend into a closed
subtree. This run repeats the `dec` and `mixed` families of the main run, same
instances and same ladder, with `closed_bit` on: 438 instances, 6570 rows,
612 s wall, `corpus-closed.csv`. The comparison column is the main run's own
`dec` and `mixed` rows, which is why the ladder stops at 2^14 here; the
flag-off deep-family knee is past 2^18 by section (e).

| playouts | certified off | certified on | zero gap off | zero gap on | mean gap off | mean gap on |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 0.000 | 0.000 | 0.000 | 0.000 | 0.1768 | 0.1768 |
| 4 | 0.000 | 0.000 | 0.068 | 0.100 | 0.1512 | 0.1432 |
| 16 | 0.025 | 0.180 | 0.192 | 0.416 | 0.1167 | 0.0730 |
| 64 | 0.080 | 0.578 | 0.297 | 0.826 | 0.0953 | 0.0225 |
| 256 | 0.116 | 0.694 | 0.475 | 0.973 | 0.0664 | 0.0042 |
| 1024 | 0.176 | 0.694 | 0.571 | 1.000 | 0.0457 | 0 |
| 4096 | 0.194 | 0.694 | 0.712 | 1.000 | 0.0266 | 0 |
| 16384 | 0.215 | 0.715 | 0.767 | 1.000 | 0.0165 | 0 |

No rung regresses on either axis, and the two axes move for the same reason: a
playout that would have gone into a resolved subgraph goes into an unrealized
action instead. Certification at 2^14 on these families is 0.215 to 0.715; over
the whole 673-instance corpus the flag-off number is 0.193, and the families
this run repeats are the ones that carried the miss.

The knee against `sum A(v)`, the prediction B1 states and the census computes
without running either solver:

| family | certified off | certified on | median `sum A(v)` | median knee off | median knee on | knee / `sum A(v)` off | on |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `dec` | 83 of 258 | 258 of 258 | 32 | 256 | 32 | 17.07 | 1.33 |
| `mixed` | 11 of 180 | 55 of 180 | 65 | 512 | 128 | 19.69 | 1.28 |

Both families land inside the band the wide, shallow families already held
flag-off (`width` 1.00, `ac` 1.78, `wide` 1.99), and the bound direction is
unchanged: no instance certifies below its `sum A(v)`. The `mixed` instances
that still do not certify are the ones whose `sum A(v)` exceeds the ladder top
(1e5 and above); their knee is unmeasured, not missing.

The miss grew with burial depth flag-off, from 7.1 at depth 3 to past
measurement at depth 12. It no longer does:

| burial depth | n | certified | median `sum A(v)` | median knee | knee / `sum A(v)` |
| --- | --- | --- | --- | --- | --- |
| 3 | 33 | 1.000 | 9 | 16 | 1.33 |
| 5 | 39 | 1.000 | 15 | 16 | 1.28 |
| 8 | 45 | 1.000 | 24 | 32 | 1.33 |
| 12 | 45 | 1.000 | 36 | 64 | 1.33 |
| 16 | 48 | 1.000 | 48 | 64 | 1.33 |
| 20 | 48 | 1.000 | 60 | 64 | 1.28 |

Finding the optimum collapses with proving it. The budget at which the
deceptive family first returns an optimal term, median over instances, goes
from geometric in both knobs to within a factor of 2 of the certification knee:
depth 20 with 1 decoy 4096 to 32, with 2 decoys 8192 to 32, with 4 decoys
unmeasured (6% of instances reached it) to 64, and every deceptive and mixed
instance now reaches gap zero within the ladder against 0.771 and 0.761
flag-off. The factor of 2000 between finding and proving that section (e)
reports at depth 12 is a property of the flag-off selection rule, not of the
instances.

Wall clock splits by whether the instance closes. On the 313 instances that
close within the ladder, total MCGS time over all rungs falls 2.07x (6819 ms to
3292 ms), because the run stops when the root closes instead of spending the
rest of the budget: median time at 2^14 playouts is 7.840 ms flag-off against
0.552 ms flag-on. On the 125 that never close, the bookkeeping is pure
overhead and costs 14.3% (39893 ms to 45598 ms): one reverse-edge entry per
child position at expansion, and the closed-child scans in selection. That is
the trade the flag makes, and it is why the default stays off for runs whose
instances are known not to close.
