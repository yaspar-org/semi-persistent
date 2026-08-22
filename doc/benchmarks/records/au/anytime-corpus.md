# AU anytime and regret corpus

> **Historical predecessor record.** These campaigns predate
> `egraph/src/au/exact_fixed.rs`; their root baseline is the contextual Exact
> implementation and their timing, crossover, and delegation ratios are not
> current evidence for pair-mode fixed-point Exact. Retain the raw record for
> reproducibility, but rerun the current Criterion/corpus protocol before
> citing a solver comparison.

The data and harness state are pinned by source revision
`37044cba18f6fee072d449abdbf224a308cc7f59`. The commands below reproduce this
record only from that revision; at current HEAD they start a new campaign and
must write to a scratch or newly named output. Current solver behavior is
specified by `egraph/tests/au_differential.rs` and the rest of the AU suite.

The corpus answers how far MCGS is from the optimum as a function of its
budget, on both budget axes (playouts, and wall clock relative to the exact
solver), and how much budget a completion certificate costs against the
action-census prediction that certification needs about `sum A(v)` playouts.

Five runs, 2026-08-16 to 2026-08-18, release build on Apple Silicon. The main
run is 673 instances, 10095 rows, 1854 s wall; the deep-ladder run repeats the
`dec` and `mixed` families to 2^18 playouts (438 instances, 8322 rows, 1317 s)
to see whether the budget, rather than the algorithm, was what stopped
certification; the closed-bit run repeats the same two families on the main
run's ladder with the closed bit on (438 instances, 6570 rows, 612 s); the
hybrid run repeats them again with the closed bit and hybrid exact solving's
exact trigger on top (438 instances, 6570 rows, 568 s). Every spec of all four was
measured: no exact timeout, no MCGS timeout, no ladder cut on the per-instance
budget, no instance past the wall budget. Tables (a) to (d) are the main run,
whose ladder is 2^0 to 2^14; table (e) is the deep-ladder run; tables (f),
(g) and (h) are the closed-bit, hybrid and live-incumbent-pruning runs, the
only ones whose MCGS runs are not the default configuration. The exact solver runs with `exact_pruning` and
`context_subsumption` on in all four.

## Reproducing the Historical Campaign

```text
AU_BENCH_DIR=doc/benchmarks/records/au AU_CORPUS_SECS=5400 \
  cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  -- --ignored --nocapture
python3 doc/benchmarks/records/au/analyze.py doc/benchmarks/records/au/corpus.csv
```

The deep-ladder run is the same harness with three knobs:

```text
AU_BENCH_DIR=doc/benchmarks/records/au AU_CSV_NAME=corpus-deep.csv AU_FAMILIES=dec,mixed \
  AU_LADDER_TOP=262144 AU_CORPUS_SECS=7200 \
  cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  -- --ignored --nocapture
python3 doc/benchmarks/records/au/analyze.py doc/benchmarks/records/au/corpus-deep.csv
```

The closed-bit run of section (f) is the same harness with the flag on, in its
own CSV because it is a different solver configuration:

```text
AU_BENCH_DIR=doc/benchmarks/records/au AU_CSV_NAME=corpus-closed.csv AU_FAMILIES=dec,mixed \
  AU_CLOSED_BIT=1 AU_CORPUS_SECS=1800 \
  cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  -- --ignored --nocapture
python3 doc/benchmarks/records/au/analyze.py doc/benchmarks/records/au/corpus-closed.csv
```

The hybrid run of section (g) adds `AU_HYBRID`, the reachable-pair threshold
the exact trigger fires at, and reads its comparison off the closed-bit run:

```text
AU_BENCH_DIR=doc/benchmarks/records/au AU_CSV_NAME=corpus-hybrid.csv AU_FAMILIES=dec,mixed \
  AU_CLOSED_BIT=1 AU_HYBRID=4096 AU_CORPUS_SECS=1500 \
  cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  -- --ignored --nocapture
python3 doc/benchmarks/records/au/analyze.py doc/benchmarks/records/au/corpus-hybrid.csv \
  --against doc/benchmarks/records/au/corpus-closed.csv
```

`--against` prints the budget-by-budget comparison of two runs over the same
instances, and `hybrid_calls`/`hybrid_ms` are two extra CSV columns a hybrid
run fills and every earlier CSV leaves absent.

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

**The corpus is selected.** Ground truth is the exact solver under a 60 s
guard; an instance that does not finish is dropped, and none was. An initially
proposed 10 ms hardness floor was not used. The
calibration sweep (`calibrate_hardness` in the harness) shows why this run
does not apply one: with projection pruning and context subsumption on, the
cyclic families solve in microseconds, the crossover family at `cycles=20` in
0.3 ms and the mixed
family at `cycles=24` in 0.4 ms, so a 10 ms floor selects the `width` and `ac`
families and nothing else. The floor is reported rather than applied: every
instance carries its `exact_ms`, 45 of the 673 are at or above 10 ms, and the
wall-clock tables are computed on that subset.

**MCGS is deterministic**, so one run per (instance, budget) is the complete
picture, and no distribution over repetitions exists. All per-instance
variation comes from the generation seeds.

**Wall-clock numbers were measured on a shared machine**, concurrently with
unrelated builds on the same host. The wall-clock tables carry that
noise; the playout-axis tables do not, because the answer at a given budget is
a deterministic function of the instance.

**The ladder is coarse.** Budgets double, so a knee reported at budget b means
the certificate appeared in `(b/2, b]`, and every knee ratio carries that
factor-2 granularity.

**The census counts the unpruned budget.** `sum A(v)` is cycle-filtered but
not dominance-filtered, which is what the prediction is stated over and what
the measured runs do (`dominance_pruning` is off by default). The dominance
comparison records how much smaller the pruned budget is on cycle-heavy
shapes. 38 of 673 instances
hit the census cap (4e6 OR states or 20 s); their `sum A(v)` is a lower bound
and they are excluded from the knee tables.

**MCGS does not stop when the search graph closes.** On a `dec` instance with
`sum A(v) = 6`, the certificate is available at 16 playouts and the run at
16384 playouts still takes 10.8 ms against 0.03 ms at 16, growing linearly in
the budget. Wall-clock costs above the knee are therefore the cost of playouts
that realize nothing, not of the certificate. This holds for the flag-off
tables below, which are every table except (f) and (g): the closed bit knows
when the graph has closed and stops there, and sections (f) and (g) report what
that is worth.

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
is already optimal, which is why the deceptive family is included.

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
inferred: it is the initial rollout's cost, which descriptor-allocation changes
did not touch.

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

The action census predicts certification at about `sum A(v)` playouts. It computes
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

Closed-subgraph selection excludes fully resolved subgraphs from selection: an OR node
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

The knee against `sum A(v)`, the prediction the census computes
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

## (g) Hybrid exact subproblems, 2026-08-17: `mixed` certification 0.31 to 1.00

Hybrid exact solving hands a subproblem to the exact solver instead of enumerating it.
At OR-node creation MCGS measures the node with `estimates::reachable_pairs`,
the size of the class-pair rectangle its subgraph lives in
(`|{l} ∪ reach(l)| * |{r} ∪ reach(r)|`, two array reads off the snapshot's
per-SCC reachability popcounts); a node at or below `AuConfig::hybrid_threshold`
is solved by `exact::run_exact_at` on its own class pair and side contexts under the
run's cycle mode, and the result is marked exact. A marked node is terminal at
creation and a terminal node is closed at birth, so with the closed bit on the proof
propagates upward as a closure. This run repeats the `dec` and `mixed` families
of the closed-bit run, same instances and same ladder, with `closed_bit` and
`hybrid_exact` at threshold 4096: 438 instances, 6570 rows, 568 s,
`corpus-hybrid.csv`. The comparison column is the closed-bit run itself, so the
two differ in exactly one flag.

| playouts | certified closed | certified hybrid | zero gap closed | zero gap hybrid | mean gap closed | mean gap hybrid |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 0.000 | 0.142 | 0.000 | 0.144 | 0.1768 | 0.1519 |
| 4 | 0.000 | 0.189 | 0.100 | 0.224 | 0.1432 | 0.1288 |
| 16 | 0.180 | 0.301 | 0.416 | 0.523 | 0.0730 | 0.0643 |
| 64 | 0.578 | 0.836 | 0.826 | 0.966 | 0.0225 | 0.0033 |
| 256 | 0.694 | 1.000 | 0.973 | 1.000 | 0.0042 | 0.0000 |
| 1024 | 0.694 | 1.000 | 1.000 | 1.000 | 0.0000 | 0.0000 |
| 4096 | 0.694 | 1.000 | 1.000 | 1.000 | 0.0000 | 0.0000 |
| 16384 | 0.715 | 1.000 | 1.000 | 1.000 | 0.0000 | 0.0000 |

No rung regresses on either axis, and the certification column reaches 1.000 at
256 playouts against 0.715 at the top of the ladder. Total MCGS wall time over
the whole ladder falls 19.2x, 48890 ms to 2544 ms, because an instance that
certifies stops early: the 125 instances the closed bit never closed are the
ones that spent the full budget, and all of them now close.

The knee splits by family, and this is where the threshold shows:

| family | certified closed | certified hybrid | median `sum A(v)` | median knee closed | median knee hybrid |
| --- | --- | --- | --- | --- | --- |
| `dec` | 258 of 258 | 258 of 258 | 32 | 32 | 32 |
| `mixed` | 55 of 180 | 180 of 180 | 113019 | 128 | 64 |

`dec` does not move at this threshold: its root estimates run from 676 at burial
depth 5 with one decoy to 962361 at depth 20 with four, so a threshold of 4096
reaches only the last few levels of the chain, and the closed bit had already put the
`dec` knee at `sum A(v)`. `mixed` moves from 55 instances certified to all 180,
because its `sum A(v)` is 1e5 and above: those instances have more actions than
the ladder has playouts, and a proof that does not come from realizing actions
is the only proof available to them.

That is also the first result in this document that breaks the census lower bound.
`sum A(v)` bounds a certificate from below only while one playout realizes at
most one action and a certificate needs every action realized; one exact call
proves a whole subgraph without realizing any of it in MCGS. 221 of the 423
uncapped instances certify strictly below their own `sum A(v)`, which is sound
for the reason `au_differential.rs::hybrid_exact_mcgs_is_sound` asserts and not
a defect in the census.

What the calls cost:

| playouts | median calls | p90 calls | max calls | median hybrid ms | hybrid share of run time |
| --- | --- | --- | --- | --- | --- |
| 1 | 0 | 1 | 13 | 0.000 | 0.189 |
| 16 | 1 | 3 | 15 | 0.004 | 0.088 |
| 64 | 1 | 4 | 15 | 0.008 | 0.039 |
| 256 | 1 | 5 | 15 | 0.007 | 0.032 |
| 16384 | 1 | 5 | 15 | 0.007 | 0.031 |

Five calls at the 90th percentile and 15 at the maximum, 109 ms of the run's
2544 ms in total. The share is highest at one playout because there is almost
no playout work to divide it into, and it falls as the ladder rises: the calls
are made once, at node creation, and a longer run does not repeat them.

### The threshold sweep

Two sweeps chose 4096, because the corpus and the cost push in opposite
directions. The corpus sweep repeats the run at four thresholds
(`AU_HYBRID` 256 and 65536 into `/tmp`, 0 being the closed-bit run itself):

| T | certified | median knee | p90 knee | median calls | max calls | total MCGS ms | hybrid time share |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 (closed alone) | 313/438 | 64 | 128 | 0 | 0 | 48890 | 0.000 |
| 256 | 380/438 | 64 | 128 | 0 | 13 | 24007 | 0.001 |
| 4096 | 438/438 | 64 | 128 | 1 | 15 | 2544 | 0.043 |
| 65536 | 438/438 | 16 | 128 | 1 | 12 | 1852 | 0.137 |

On these two families the sweep is monotone: a higher threshold certifies at
least as often, at least as early, and faster.
`au_hybrid_exact.rs::hybrid_threshold_sweep` shows the same shape per instance
at nine thresholds, including the point at which the root's own estimate falls
under the threshold and the trigger absorbs the whole instance in one call.
What stops the sweep is the second one,
`au_corpus_bench.rs::calibrate_hybrid_threshold`, which prints the
trigger's estimate against what exact actually costs at that root, per family:

| instance | root estimate | max A(v) at one node | `sum A(v)` | exact ms |
| --- | --- | --- | --- | --- |
| `dec d5k1` | 676 | 2 | 10 | 0.08 |
| `xover d4w4c8` | 625 | 17 | 181111 | 0.05 |
| `ac m24c4` | 841 | 576 | 576 | 3.19 |
| `xover d5w8c12` | 1521 | 65 | 39212053+ | 0.12 |
| `width d4w16` | 4761 | 256 | 1024 | 0.28 |
| `ac m64c8` | 5329 | 4096 | 4096 | 64.64 |
| `ac m128c12` | 19881 | 16384 | 16384 | 644.23 |
| `dec d12k2` | 42025 | 3 | 36 | 0.16 |
| `wide d4w32` | 56169 | 1024 | 4120 | 1.43 |
| `width d4w64` | 68121 | 4096 | 16384 | 3.70 |
| `mixed c10` | 135054 | 82 | 32963165 | 0.15 |
| `width d12w256` | 9517225 | 65536 | 786432 | 163.50 |

The estimate counts class pairs and is therefore blind to how many members a
class has, which is exactly what the `ac` and `width` families vary: `ac m24c4`
lives in a rectangle of 841 pairs and still costs 3.19 ms, because its single
class pair carries 576 representation pairs. So the estimate does not order
instances the way exact's cost does, and the threshold is calibrated on the
worst call it admits rather than on a correlation. At 4096 the worst probe
admitted is `ac m24c4` at 3.19 ms; at 8192 it is `ac m64c8` at 64.64 ms; at
65536 it is `ac m128c12` at 644.23 ms, which is more than the entire MCGS
ladder costs on that instance. 4096 is the last threshold in the sweep whose
admitted calls stay in single-digit milliseconds, and buying the `dec` and
`mixed` knee at 65536 would cost 200x on the worst `ac` call. That is the
trade, and it is why the flag ships off with 4096 as its default rather than
on.

The honest limit this leaves: the estimate is a poor predictor of exact's cost
whenever fan-out rather than class count is what drives the search, and a
threshold calibrated on the worst case is correspondingly conservative for
everything else. The node's own action count is available for free at the
trigger (`ensure_or_stats` has already computed it) and would separate the `ac`
and `width` cases from the deep narrow ones; whether a two-part estimate beats
a single conservative threshold is a measurement nobody has run.


## (h) Live-incumbent pruning, 2026-08-18: the `dec` knee lands at 1.07x and `mixed` breaks the realization floor

Live-incumbent pruning caches every arm's admissible size
lower bound at stats creation and excludes the arm the moment the bound
strictly exceeds the node's current incumbent, which tightens as
compositions arrive; an excluded arm counts as resolved toward the
certificate ("realized or proven non-optimal", dominance pruning applied to the live
incumbent). This run is the FULL corpus, all seven families, with
`closed_bit` and `live_incumbent_pruning` on and the hybrid trigger off:
547 instances kept of 673 specs (126 past the 1500 s wall budget, none
otherwise lost), 8204 rows, 1516 s, `corpus-s1.csv`. Per family, with the
knee as the certification budget over `sum A(v)`:

| family | instances | certified | knee median | knee p90 | knee max |
| --- | --- | --- | --- | --- | --- |
| dec | 156 | 1.00 | 1.07 | 1.33 | 1.60 |
| mixed | 156 | 1.00 | 0.00 | 0.98 | 1.31 |
| wide | 40 | 0.20 | 1.98 | 2.00 | 2.00 |
| rand | 120 | 1.00 | 0.00 | 0.00 | 0.00 |
| xover | 45 | 1.00 | 0.00 | 0.05 | 0.17 |
| width | 15 | 1.00 | 0.02 | 0.06 | 0.08 |
| ac | 15 | 1.00 | 0.02 | 0.06 | 0.06 |

Against the closed-bit run (f) on the shared families: the `dec` knee moves
from median 1.33x / max 1.78x to median 1.07x / max 1.60x, and `mixed` goes
from 125 of 180 instances uncertified to zero uncertified. The `mixed`
median of 0.00 is not a rounding artifact: instances whose `sum A(v)` is in
the tens of millions certify within the 2^14 ladder, a ratio near 3e-4,
because an excluded arm needs no realization: the certificate no longer
pays the `sum A(v)` floor wherever bounds can dismiss arms. That floor was
(f)'s headline limit. Dynamic interval labels provide the general form of this
effect; the static live-incumbent bound delivers it wherever that test alone
suffices. The find side moves the same way:
`au_deceptive.rs::live_incumbent_pruning_collapses_deceptive_budget` pins
burial depths 3 to 12 reaching the planted optimum within 16 playouts
where the flag-off table needed 4096 at depth 20 and did not certify depth
12 at 2^18. Zero regressions: `rand`, `xover`, `width` and `ac` stay
optimal at one playout (all 195 of 195), and the `wide` family's 0.20
certified fraction is not a comparison against (f), which did not cover
`wide`; its ladder simply exhausts before the spine resolves, the regime
the hybrid trigger exists for.


## (i) Hybrid-search configuration and controls, 2026-08-19

Three CSVs record the combined configuration and controls: `corpus-t2.csv` (the
scaled `wide`/`width`/`ac` grid, the cell where exact costs
tens-to-hundreds of ms), `corpus-t2-s5.csv` (the same grid with
static child seeding on, the only difference), and `corpus-t1.csv` (the
`sat-ite` funnel family). The configuration under test is
`closed_bit + live_incumbent_pruning + hybrid_exact(4096) +
rollout_hybrid + session_exact_memo`.

### T2: the entry cost, measured where exact is slow

34 instances kept of 37 (3 exact timeouts at the 60 s guard), 299 rows,
1666 s. At one playout the configuration costs a median **0.703x** of
exact's total time, and the answer is already optimal on every `width`
and `ac` instance and on 9 of 16 `wide` instances (the rest carry the
gadget gap, 0.028 to 0.140). Per family the entry ratio is 0.52 to 0.64
on `wide`, 0.70 to 0.76 on `width`, and **2.3 to 3.2 on `ac`**.

**RETRACTED 2026-08-19: the `ac` column is not a hybrid-admission defect.** This
paragraph first read the single `hybrid_calls = 1` at one playout as the
rectangle-only gate handing the whole instance to the exact solver. The
calibration run refutes it: sweeping `hybrid_action_threshold` over
{0, 64, unbounded} on the same instances leaves the entry ratio
unchanged to two digits (2.82x, 3.06x, 3.29x, ... identical at every
threshold), and `hybrid_ms` is **0.0 on every `ac` instance**, so that
one call is a trivial node and no exact work is inside the measurement
at all.

The real cost is MCGS's own per-node work at an `ac` root: `ac`'s
representation-pair enumeration runs a transport feasibility solve per
pair before any playout can start, and the rollout then solves a flow
per surviving descriptor. That is the cost the corpus's own `ac` notes
already described (an `m64c16` root carries 4096 transport edges of 289
cells), it is paid whether or not the hybrid trigger exists, and it is
what puts the entry ratio above 1 on this family. Reducing it is an
enumeration-cost item, not an admission-gate item; the action-count gate is
still the right guard for the case it was built for (a small rectangle
whose node carries hundreds of actions), but this family is not evidence
for it, and the sweep that would calibrate `T2` needs a family where
`hybrid_ms` is actually nonzero.

### Static child seeding: no win on this grid, and why

Same grid, `static_child_seed` added: median marginal cost per playout
**0.95x** of the baseline (n = 26 instances with a measurable slope) and
one-playout entry 0.703x to **0.653x**, with **zero instances worse at
matched wall clock** and every gap unchanged. Static child seeding neither
pays nor costs here, and the reason is structural rather than a tuning failure: the
`wide`, `width` and `ac` ANDs have low arity, so nearly every expanded
child is selected soon after, and there are no never-visited siblings
whose rollouts the deferral saves. The flag ships default off; the
regime it was designed for is high fan-out, which is what T1 builds.

### T1: the `sat-ite` funnel, built by saturation

12 specs over guard depth k in {6, 8, 10}, edit count in {1, 2} and
saturation cap in {6, 10}; 11 kept (`k=10, edits=2, cap=6` lost its
ground truth to the 60 s exact guard), 240 rows, 184 s. Realized width,
which the rules decide and the spec only requests: 1 898 nodes / 799
classes at k = 6, 21 317 / 6 825 at k = 8, and 195 567 / 68 357 at
k = 10, where the saturation is still running when the iteration cap
stops it. The planted optimum
(`2*(2^k - 1) + 2^k + edits`, the projection identity) is pinned against
the exact solver at k = 2 and k = 3 by
`sat_ite_planted_optimum_matches_exact`, which is what licenses using it
as ground truth at k = 10.

| instance | exact | one playout | optimal at p1 | certified at | knee vs `sum A(v)` |
| --- | --- | --- | --- | --- | --- |
| k6e1c6 | 0.5 ms | 0.2 ms | yes | 256 | 1.6e-3 |
| k8e1c6 | 2.2 ms | 0.8 ms | yes | 2048 | 1.2e-4 |
| k8e2c10 | 3.6 ms | 0.9 ms | yes | 2048 | 1.2e-4 |
| k10e1c10 | 17.8 ms | 2.3 ms | yes | 8192 | 2.6e-4 |
| k10e2c10 | 35.0 ms | 1.9 ms | yes | 8192 | 2.6e-4 |

Two results. The first answer is **optimal at one playout on every
instance**, at 2x to 18x less time than exact's completion, which is the
anytime claim the family was built to test. The second is the
certification knee: 2048 playouts against a `sum A(v)` of 17.7 million
is **four orders of magnitude below the realization floor**, the
strongest form of what run (h) first showed, because a wide graph gives
the admissible bounds many arms to dismiss per composition.

The honest caveat on the acceptance criterion: the design predicted a
`(v^2)^k` blowup making exact infeasible across the family, and that is
not what the measurement shows. Exact with projection pruning and context
subsumption finishes 11
of 12 cells in under 35 ms. Only `k=10, edits=2, cap=6` exceeds the 60 s
guard, and it does so because the cap leaves the two guard orders partly
unmerged, which is harder for the search than the fully saturated
`cap=10` instance exact finishes in 35 ms. That single cell is the
regime, and
`sat_ite_mcgs_reaches_planted_optimum_where_exact_times_out` pins it:
one playout returns the planted optimum there in single-digit
milliseconds. The claim the corpus supports is "MCGS reaches the
optimum sooner and certifies far below the realization floor", not
"exact is generally infeasible on this family".

### T3: the honesty control, and what survives it

The control asks whether the MCGS result is really MCGS's: exact
warm-started with the one-playout incumbent as its initial pruning bound
and the session exact memo pre-seeded (`SearchSession::run_exact_warm`), against
cold exact and against the probe itself, on the `cap=6` funnel cells.
Times in milliseconds, and a checkmark is `Completion::Exact`:

| instance | cold exact | one playout | warm exact | cold | mcgs | warm |
| --- | --- | --- | --- | --- | --- | --- |
| k8e1c6 | 2.8 | 0.6 | 2.6 | yes | no | yes |
| k8e2c6 | 2.6 | 0.2 | 2.2 | yes | no | yes |
| k10e1c6 | 4.5 | 0.6 | 3.3 | yes | no | yes |
| k10e2c6 | **63 254** | **11.7** | **68 067** | no | no | no |
| k10e1c10 | 38.5 | 1.4 | 19.7 | yes | no | yes |
| k10e2c10 | 28.0 | 1.7 | 27.2 | yes | no | yes |

Warm starting is a real but modest speedup where exact already
finishes: 1.1x to 2.0x, best on `k10e1c10` (38.5 ms to 19.7 ms), which
is what a tighter initial bound buys a branch-and-bound search. On the
one cell where exact is infeasible it buys nothing: warm exact spends
68 s and still does not certify, while the probe that seeded it returned
the planted optimum in 11.7 ms. So the alternative claim the control was
written to allow ("probes make exact feasible, and the probe is not the
point") is refuted on this family: the probe answers where exact, warm
or cold, does not. The claim that survives is the narrow one: on a wide
graph MCGS reaches the optimum orders of magnitude sooner, and where
`sum A(v)` is in the millions it also certifies far below the
realization floor, while exact remains the better tool wherever its
pruning closes the instance in tens of milliseconds.

One column deserves its own note: `mcgs` is `no` everywhere in the
table, because one playout returns the optimum without proving it. The
certificates in the T1 table above arrive at 256 to 8192 playouts. Anytime
quality and certification are separate axes, and this family separates
them cleanly.


## (j) Interval bounds and the `blind` family, 2026-08-19

Dynamic interval bounds replace the static per-arm bound with one that tightens
as the search learns its subtree is expensive:
`L(and) = 1 + Σ count · L(child)`
(over the selected flow for a transport arm), `L(or) = min over the
node's live arms`, both monotone and propagated along the playout path
like the Q values, so a stale bound is weaker and never wrong.

### Why no existing family shows a difference

The static bound is `1 + Σ lb_pair` with `lb_pair = max(bs_l, bs_r) + 1`. That
is nearly exact whenever a mismatched pair costs about as much as its
larger side, which is true of every family the corpus had: `dec` and
`mixed` separate their decoys by a size margin, `wide` and `width` by
spine depth, `ac` by monomial count. Running the whole `blind` grid at
both settings before the family was tuned produced identical certification
budgets to the playout, and that is the expected result, not a bug.

### The two shapes that did not work, recorded so they are not retried

**Ordered spine with same-shaped leaves.** An `align` family paired
same-sized predicate definitions down an ordered spine. It measures
nothing: an ordered operator forces the positional pairing, so there is
no alignment choice, and chains of the same shape anti-unify to about
their own size whether or not the atoms agree, so a mismatch is not
expensive. Certification budgets matched to the playout at every point of
a 9-instance grid.

**A decoy that is only a leaf.** Rebuilding the decoy as a terminal pair
of unrelated chains made the family genuinely deceptive (the first answer
was wrong on every instance) and still moved nothing, for a reason worth
keeping: refuting that decoy saves a single expansion. An exclusion pays
only when the excluded arm guards a REGION.

### The family that works

`blind` gives each level two arms under the same operator, and the decoy
carries both an unrelated pair and its own spine:

```
 win  (l) = w( f^m(a), previous_win_left )      matched chains: cheap
 decoy(l) = w( f^S(a), junk_left )              unrelated pair + own region
 win  (r) = w( f^m(b), previous_win_right )
 decoy(r) = w( g^S(b), junk_right )             note g, not f
```

with `m/2 < S < m`. The three conditions the window enforces:

| condition | why it must hold | arithmetic |
| --- | --- | --- |
| the decoy attracts | else greedy never takes it | estimate `2(S+1)` < `2(m+1)` |
| the decoy is wrong | else it is not a decoy | true `2S+2` > `m+3` |
| the static bound is blind to it | else the static bound suffices | bound `S+2` < `m+2` |

The third line is the point: the decoy's static bound is *below the
winner's own*, so no incumbent the winner can produce will ever exceed
it, and static live-incumbent pruning cannot exclude the arm at any budget.
Intervals refute it after one expansion, because the unrelated pair is terminal at
`bs_l + bs_r` and lifts the arm's floor above the incumbent immediately.

### Result

Exact playout counts to a certificate (stepping by one below 64, then by
eighths; the doubling ladder is too coarse to see this), both
configurations asserted to certify the same optimum:

| instance | `sum A(v)` | static bound | dynamic intervals | speedup |
| --- | --- | --- | --- | --- |
| d2 m12 | 66 | 20 | 18 | 1.11x |
| d4 m12 | 84 | 81 | 44 | 1.84x |
| d6 m12 | 102 | 102 | 72 | 1.42x |
| d8 m12 | 120 | 128 | 91 | 1.41x |
| d10 m12 | 138 | 144 | 102 | 1.41x |
| d12 m12 | 156 | 162 | 114 | 1.42x |
| d16 m12 | 192 | 204 | 144 | 1.42x |
| d6 m20 | 136 | 144 | 91 | 1.58x |
| d10 m20 | 172 | 182 | 128 | 1.42x |

The ratio is stable as the graph grows, which is what a region-skipping
argument predicts: the decoy region is a constant fraction of the graph,
so the saving is a constant factor rather than a widening one.

### The limit, stated plainly

Intervals speed certification and never discovery. A bound excludes an
arm only once an incumbent beats it, and the incumbent comes from the
winner's own composition, so nothing here helps the search FIND the
winner. Instrumenting one `blind` run counted 916 interval-only
exclusions, every one of them after the winning composition had already
arrived. Anyone reading the 1.4x should read it as "the proof costs
less", not "the answer comes sooner".

## (k) `sat-ite` at k = 12, 2026-08-19: the first cell where the configurations separate, and why it still does not carry the hybrid claim

Every earlier `sat-ite` cell was a step function: the bare greedy rollout
returned the planted optimum on its first playout, so the ablation in section
(j) could not distinguish the three configurations. k = 12 on the 63-bit
binding (`Config64`, since the 31-bit AU arenas trap above k = 10) is the first
size at which no configuration reaches the target immediately, so the
comparison has something to measure.

### Ground truth first: cap 6 is invalid at k = 12

The cap that suffices at k <= 10 does not scale with k. At k = 12 cap 6 the
instance is 1076346 nodes and 453530 classes and saturation does not complete,
so the guard orders stay unmerged and the planted value is not achievable.
`sat_ite_planted_vs_exact_64` records it:

| cell | planted | exact | exact complete | MCGS-feasible | verdict |
| --- | --- | --- | --- | --- | --- |
| k12 e1 c6 | 12287 | 24572 | no | 14599 | **unverified** |
| k12 e1 c10 | 12287 | 12287 | yes | 12287 | **verified** |
| k12 e2 c10 | 12288 | 12288 | yes | 12288 | **verified** |

A feasible term of size 14599 exists, so 12287 is not established as the
minimum and exact's 24572 is not the minimum either. This is the same defect
that invalidated caps 2 and 4 at k = 8 and k = 10, appearing again one cap
higher because the instance grew. `crossover_study` now skips k >= 12 below
cap 10, and any percentage printed at k12 c6 is a distance to a construction
target, not to the optimum.

### The ablation, at equal playouts and at equal wall clock

`deep_ablation` runs the three configurations on the same k12 c6 e-graph, which
makes comparing them to each other sound even though the target is not the
optimum. Sizes, with wall clock:

| playouts | greedy | ms | + delegation | ms | full | ms |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 18436 | 30.9 | 17924 | 71.6 | 17924 | 57.3 |
| 4 | 18436 | 41.7 | 17924 | 193.3 | 17924 | 193.2 |
| 16 | 18436 | 139.9 | 17924 | 675.7 | 17924 | 591.2 |
| 64 | 18436 | 553.5 | 16900 | 2941.7 | 16900 | 2511.0 |
| 256 | 14599 | 1329.3 | 14598 | 7586.0 | 14598 | 6135.4 |

**At equal playouts, delegation wins.** It is 2.8% better at 1 through 16
playouts and 8.3% better at 64. This is the first measurement on any family
where delegation changes the answer, and it is the result section (j) predicted
would be needed.

**At equal wall clock, it loses.** The greedy rollout at 256 playouts returns
14599 in 1.33 s; the full configuration at 64 playouts returns 16900 in 2.51 s,
which is 15.8% worse for 1.9x the time. At 256 playouts the two converge to
within one node (14599 against 14598) and greedy gets there 4.6x faster.
Delegation costs roughly 5x per playout on this family and buys about 3%, which
the bare rollout recovers by spending the same seconds on more rollouts.

So the honest statement remains the narrow one. The claim "MCGS with sound
delegation beats exact where exact does not scale" needs a per-second win, and
`sat-ite` does not provide one at any size measured, including the size where
the configurations finally separate.

### What is claimed without reference to ground truth

At k12 c6, MCGS returns 14599 in 1.33 s while exact returns 24572 after 71 s
without finishing. Because 14599 is a term MCGS actually constructed, it is
feasible by exhibition, so exact's answer is at least 68% above a known-feasible
value after 53x the wall clock. That comparison needs no planted value and is
the strongest `sat-ite` result to date. It is a statement about exact's
scaling, not about the hybrid.

## (l) `sat-decoy`, 2026-08-19: the intersection family exists, and it credits the search rather than the delegation

Section (k) left one requirement: a family where the greedy rollout is wrong AND
exact does not scale. `blind` gave the first, `sat-ite` the second, neither gave
both. `sat-decoy` gives both, by keeping `sat-ite`'s two guard orders untouched
and unioning one `blind`-style decoy arm into the root class after saturation.
`build_sat_decoy` constructs it and `sat_decoy_probe` calibrates it.

### The arm

A decoy arm is a pair of chains over different unary operators, `P^S(X)` on the
left and `Q^S(Y)` on the right, unioned into the two root classes after
`(run cap)` so no rule ever sees it. Chains over different operators share no
structure, so anti-unifying them pays both sides: `2S + 2`. The winner's true
cost is the planted optimum `W`, and the rollout estimates the winner at about
`2W` because it has not yet discovered the sharing. The arm is therefore a decoy
when `W < 2S + 2 < 2W`.

Measured at k = 6 and k = 8, sweeping `S` as a fraction of `W`:

| S / W | exact | greedy at 1 playout | reading |
| --- | --- | --- | --- |
| 1/3 | 128, 512 | 128, 512 | arm is cheaper than the winner: it becomes the optimum |
| 1/2 | 191, 767 | 192, 768 | optimum preserved, rollout misled by one node |
| **2/3** | **191, 767** | **230, 904** | **optimum preserved, rollout misled by 20% and 18%** |
| 5/6 | 191, 767 | 191, 767 | arm too expensive; the rollout ignores it |
| 1/1 | 191, 767 | 191, 767 | ignored |
| 3/2 | 191, 767 | 191, 767 | ignored |

The band is `1/2 < S/W < 5/6` and the family ships at 2/3. The `levels = 0`
control reproduces plain `sat-ite` exactly, which is what attributes the error
to the arm and not to the instance.

### Two placements that do not work, and why

**A shared base atom.** Chain lengths halve as the levels descend, so with one
base atom per side every level's spine hash-conses to a prefix of level 0's.
The arms then share structure with each other and stop being structure-free
relative to the winner: `levels = 2` and `levels = 4` both returned the optimum
at one playout while `levels = 1` was wrong by 18 to 20%. Fixed by giving each
level its own base atoms.

**Arms on the THEN child instead of the spine.** The intent was
multiplicativity: THEN children at successive spine levels are disjoint
subtrees, the winner must solve all of them, so their decoys should compose.
They do not compose, because at that position no chain length is a decoy at all.
Sweeping 2/3 to 5x the subtree optimum, the arm either became the optimum (exact
fell from 191 to 160, 145, 135 as levels were added) or was ignored (greedy
returned 191 at one playout). There is no band in between. Only spine placement
has one, and at `levels = 1` that puts the single arm at the root.

So `sat-decoy` ships with one decoy, not a nest of them. Making the rollout's
error multiplicative in the depth is still open.

### The measurement, at k = 10 cap 6 where exact does not finish

`sat_decoy_ladder`, 60 s exact guard, planted optimum verified by the
`levels = 0` control:

| cell | exact after 62 s | greedy at 1 playout | greedy at 16 | greedy at 64 |
| --- | --- | --- | --- | --- |
| e2, no decoy | 3072, uncertified | 3072 | 3072 | 3072 |
| e2, decoy | 3072, uncertified | 3620 (+18%) | 3600 (+17%) | **3072 in 113 ms** |
| e4, no decoy | 6140 (+100%), uncertified | 3074 | 3074 | 3074 |
| e4, decoy | 4094 (+33%), uncertified | 3625 (+18%) | 3604 (+17%) | **3074 in 109 ms** |

The e4 decoy cell is the one to cite. Exact spends 61.9 s and returns a term 33%
above the optimum without certifying. MCGS returns the optimum in 109 ms: 568x
less time for a 33% better answer. The rollout alone does not get there, which
is what the e4 decoy cell establishes and what every earlier family failed to
show: at 1 and 16 playouts it sits 18% and 17% off, and only the search closes
the gap.

### What this does and does not credit

**It credits the search.** Going from 1 playout to 64 is what fixes the decoy,
on a family where the one-playout answer is measurably wrong. Section (j)'s
ablation could not show this because the rollout was already optimal everywhere
it ran.

**It does not credit the delegation.** The full configuration (closed bit, live
incumbent pruning, intervals, hybrid exact, session memo) tracks bare UCT's
answer at every budget and costs 3x to 8x more wall clock: 861.6 ms against
109.0 ms at 64 playouts on the e4 decoy cell. Delegation changes the answer by
at most 6 nodes out of 3600 anywhere in the table.

The reason is structural, and it predicts where delegation could help. The
rollout's error here is an OVERestimate of the winner, not an underestimate of
the decoy: the arm's cost `2S + 2` is estimated exactly, since chains over
different operators have no sharing to discover. Correcting the error means
tightening the winner's bound, and the winner is the whole ITE tree, which is
the subproblem exact cannot finish. Delegation only pays when the misestimated
subproblem is small enough to hand to exact, which is why intervals worked on
`blind` in section (j), where one expansion tightened the winner's bound, and
why nothing has made the hybrid pay on a `sat-ite`-sized instance.

**The next construction, stated so it is testable:** a family whose winner arm
becomes tightly bounded after a shallow amount of work while the instance stays
globally hard. Then the decoy is refutable by delegation rather than by
exhausting the search.

## (m) `sat-gadget`, 2026-08-20: delegation pays, in the region section (l) predicted

Section (l) reported delegation as a measured negative and gave the reason as a
specification: it pays only when the subproblem the rollout misjudges is small
enough to hand to the exact solver, inside an instance the exact solver cannot
finish whole. `au_delegation.rs` builds to that specification, and the negative
does not hold there.

### The gadget

The action estimate prices an action at `1 + Σ (bs(left) + bs(right))` over its
child pairs, which is exact for a pair sharing no operator and pessimistic for
one that factors through shared structure. A pair of that second kind, placed
beside a pair of the first, is misranked:

| arm | estimate | true cost |
| --- | --- | --- |
| `Wn(g(a), g(a))` against `Wn(g(b), g(b))` | 1 + 2(2+2) = 9 | 1 + 2(3) = 7 |
| `P(P(P(a)))` against `Q(Q(Q(b)))` | 8 | 8 |

The rollout compares 9 against 8 and takes the second; the truth is 7 against 8.
The winner's two children are the same pair, solved once and charged twice,
which is exactly the sharing the estimate cannot see. The gadget is three nodes
deep, so the exact solver settles it in microseconds. That last property is what
`sat-decoy`'s root arm lacked: correcting a misjudgement at the root means
bounding the whole instance.

### The host

`n` gadgets hang on a spine above a `sat-ite` core, so the search meets `n`
independent shallow misjudgements and then one subproblem the exact solver
cannot finish. The gadgets use per-gadget atoms, so no two share structure and
each is its own decision.

### The measurement

k = 8, two edits, cap 6, size against playouts:

| gadgets | 1 playout | 4 | 16 | 64 |
| --- | --- | --- | --- | --- |
| 0, bare | 768 | 768 | 768 | 768 |
| 0, delegated | 768 | 768 | 768 | 768 |
| 8, bare | 840 | 839 | 835 | 832 |
| 8, delegated | **832** | **832** | 832 | 832 |

At k = 10 with eight gadgets the wall clock is the point:

| | value | time |
| --- | --- | --- |
| delegated, 1 playout | 3136 | 1.0 ms |
| bare, 1 playout | 3144 | 1.0 ms |
| bare, 64 playouts | 3136 | 17.1 ms |

Delegation returns the best-known value at its first playout, in the same
millisecond bare search spends returning a worse one. Bare search needs
sixty-four playouts and about seventeen milliseconds to catch up: **17x on time
to equal quality**, and a strictly better answer at identical wall clock in the
low-budget region.

`delegation_reaches_the_same_value_sooner` asserts the time comparison rather
than quality at equal playouts, because quality at equal playouts is the
comparison that flattered delegation on every earlier family while it lost on
time.

### The control, and what this does not overturn

With zero gadgets the two configurations return the same answer and delegation
is slower, which `without_gadgets_delegation_only_costs` asserts. So the win is
the gadgets, not the machinery.

Sections (k) and (l) stand. On `sat-ite` and `sat-decoy` delegation still costs
3x to 8x wall clock for the same answer, and those families are not defective:
they are the case where the misjudgement is not locally correctable. What
changes is the scope of the claim. Delegation is not useless and it is not
generally profitable; it pays exactly when the rollout's error is concentrated in
subproblems the exact solver can absorb, and the two families now bracket that
condition from both sides.
