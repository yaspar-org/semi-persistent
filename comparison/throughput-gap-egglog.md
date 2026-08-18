# egglog's execution path on `math-microbenchmark`

This is the egglog half of a closed diagnosis; see the note at the head of
`throughput-gap-ours.md`.

This file records what egglog does when it runs
`comparison/math-microbenchmark.egglog.egg`, in enough detail to sit beside the
same account for our engine. It is a measurement record and a source reading of
one engine: it does not compare the two, and it does not say what our engine
should do.

All numbers come from egglog at commit `7b1adf2`, release build, `-j 1`
throughout, on the pilot machine. Source citations are `path:line` into that
commit. Regenerate with:

```
egglog -j 1 --report-level stage-info --save-report report.json \
    comparison/math-microbenchmark.egglog.egg
```

The pilot median for this benchmark is 508.3ms (`pilot-results.csv`); the runs
below land at 520-530ms wall, of which 518.7ms is saturation work that the
report attributes.

## Where the time goes

Eleven iterations, 22 rules, final e-graph of 1,047,896 rows.

| phase | time | share |
|---|---|---|
| search and apply | 224.3ms | 43.2% |
| merge | 76.3ms | 14.7% |
| rebuild | 218.1ms | 42.0% |
| total | 518.7ms | |

Total matches applied: 943,092. That is 4.21M matches/second against
search-and-apply time and 1.82M matches/second against the whole saturation.
Rebuild costs almost as much as matching, and egglog implements rebuild as
rules of its own (`egglog-bridge/src/lib.rs:950` builds an `incremental
rebuild` rule per table and column, itself run under seminaive).

## Per-rule search and apply

Summed over all eleven iterations and all seminaive variants. `var` is the
number of delta variants the rule expands into, which equals its number of
body atoms.

| time | share | matches | share | var | rule |
|---|---|---|---|---|---|
| 73.7ms | 33.1% | 309,520 | 32.8% | 2 | `(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))` |
| 54.3ms | 24.4% | 317,828 | 33.7% | 2 | `(rewrite (Add a (Add b c)) (Add (Add a b) c))` |
| 50.0ms | 22.4% | 44,219 | 4.7% | 3 | `(rewrite (Add (Mul a b) (Mul a c)) (Mul a (Add b c)))` |
| 14.7ms | 6.6% | 81,892 | 8.7% | 2 | `(rewrite (Mul a (Mul b c)) (Mul (Mul a b) c))` |
| 8.3ms | 3.7% | 12,825 | 1.4% | 2 | `(rewrite (Integral (Mul a b) x) ...)` |
| 6.2ms | 2.8% | 24,058 | 2.6% | 2 | `(rewrite (Integral (Add f g) x) (Add (Integral f x) (Integral g x)))` |
| 4.3ms | 1.9% | 72,847 | 7.7% | 1 | `(rewrite (Add a b) (Add b a))` |
| 4.0ms | 1.8% | 15,190 | 1.6% | 2 | `(rewrite (Diff x (Add a b)) (Add (Diff x a) (Diff x b)))` |
| 2.9ms | 1.3% | 53,415 | 5.7% | 1 | `(rewrite (Mul a b) (Mul b a))` |
| 2.1ms | 1.0% | 4,467 | 0.5% | 2 | `(rewrite (Diff x (Mul a b)) ...)` |
| 1.1ms | 0.5% | 2,654 | 0.3% | 2 | `(rewrite (Integral (Sub f g) x) ...)` |
| 0.7ms | 0.3% | 4,170 | 0.4% | 1 | `(rewrite (Sub a b) (Add a (Mul (Const -1) b)))` |
| <0.2ms | | <5 each | | | the remaining 10 rules |
| 222.7ms | | 943,092 | | | total |

The top three are distributivity forward, `Add` associativity, and
distributivity backward: 80% of matching time between them. Commutativity is
cheap in time (7.2ms combined) and expensive in matches (126,262): a
single-atom query with no join.

The backward distributivity rule is the outlier in the other direction: 22.4%
of the time for 4.7% of the matches. It is the only three-atom rule in the
file, so it expands into three delta variants and its plan has six stages
rather than three.

## How the associativity rule compiles

`(rewrite (Add a (Add b c)) (Add (Add a b) c))` has two body atoms over the
`Add` table, whose columns are `(arg0, arg1, value, timestamp)`:

- atom 0: `Add(b, c, @Add9)`, the inner sum
- atom 1: `Add(a, @Add9, @Add8)`, the outer sum

egglog plans the query once, at rule-declaration time, on an empty database.
`RuleBuilder::build_with_description` calls `plan_query`
(`core-relations/src/query.rs:568`), and the result is frozen into a
`CachedPlan` (`core-relations/src/query.rs:66`). `plan_query`
(`core-relations/src/free_join/plan.rs:1183`) hands off to
`tree_decompose_and_plan`, which returns a single bag without decomposition
whenever the query has two atoms or fewer, or `--no-decomp` is set
(`core-relations/src/free_join/plan.rs:1124`). Every rule in this benchmark
produces a `SinglePlan`: `Plan::to_report` is `todo!()` for a decomposed plan
(`core-relations/src/free_join/plan.rs:235`) and the `stage-info` run
completes, so no rule here reached the decomposed path. `--no-decomp` is
therefore a no-op on this file, and the measurement below confirms it.

The compiled plan, dumped from the trace log
(`core-relations/src/free_join/execute.rs:1221`, reachable with
`RUST_LOG=trace`):

```
stage 0  FusedIntersect  cover = atom0[Col(0), Col(1)]        binds b, c
stage 1  Intersect       var = @Add9
                         scans = atom0.Col(2), atom1.Col(1)
stage 2  FusedIntersect  cover = atom1[Col(0), Col(2)]        binds a, @Add8
```

Stage 0 scans the inner atom's key columns. Stage 1 is a generic-join
intersection on the shared e-class variable: the inner atom's value column
against the outer atom's second argument column. Stage 2 reads the outer
atom's remaining columns. `Add` is a function table, so `(b, c)` determines
`@Add9` and stage 1's first scan has cardinality one per binding.

**The static plan is not the execution order.** Before running, and again
every third stage, egglog re-sorts the remaining stages by the current subset
sizes: `run_join_stages` sorts once at
`core-relations/src/free_join/execute.rs:1230`, and `run_plan` re-sorts inside
the loop at `core-relations/src/free_join/execute.rs:1280` when the current
stage has more than 32 tuples. The sort key is
`(-times_refined, estimate_size, -num_intersected_rels)`
(`core-relations/src/free_join/execute.rs:2724` onward), and `estimate_size`
reads the live subset size of the atom
(`core-relations/src/free_join/execute.rs:2591`). A second dynamic choice sits
inside the two-way `Intersect`: it builds a column index over each side and
iterates whichever prober is smaller, probing the larger by key
(`core-relations/src/free_join/execute.rs:1461-1470`).

Together these two mechanisms mean the delta variant does not need its own
plan. Whichever atom the timestamp constraint has shrunk becomes the driving
scan by size, at runtime.

### How the delta restriction enters

`Query::add_rules_from_cached` (`egglog-bridge/src/rule.rs:779`) instantiates
the cached plan once per body atom, N variants for N atoms, in the standard
triangular form recorded in its own comment at
`egglog-bridge/src/rule.rs:808`:

```
A_new x B     x C
A_old x B_new x C
A_old x B_old x C_new
```

Each variant adds one `GeConst` on the focus atom's timestamp column and
`LtConst` on the timestamp column of every earlier atom
(`egglog-bridge/src/rule.rs:815-844`). The join stages themselves are cloned
verbatim: `get_rule_with_extra_constraints`
(`core-relations/src/query.rs:190-243`) copies `cached_plan.stages.instrs` and
rebuilds only the `JoinHeader` subsets.

The timestamp constraint is not a filter. Tables are `SortedWritesTable` sorted
by their timestamp column, so `fast_subset` turns `GeConst` into a dense
offset range by binary search (`core-relations/src/table/mod.rs:445`, `GeConst`
at `core-relations/src/table/mod.rs:497`). The delta is a contiguous suffix of
row ids, computed in O(log n) and carried as `Subset::Dense`. When that suffix
covers more than half the table, `get_index` reuses the table-level cached
column index rather than building one over the subset
(`core-relations/src/free_join/execute.rs:1156`), and those cached indexes are
refreshed incrementally from `updates_since`
(`core-relations/src/hash_index/mod.rs:74-107`), never rebuilt per iteration.

A variant whose focus atom has an empty delta is dropped before it runs:
`add_rule_from_cached_plan` returns `None` when a constrained subset is empty
(`core-relations/src/query.rs:257`, `core-relations/src/query.rs:146`). In
steady state this benchmark instantiates 30 plans per iteration under
seminaive against 22 under `--naive`, 322 against 238 over the whole run. Two
of the file's 24 rewrites never instantiate at all, under either mode:
`(rewrite (Add a (Const 0)) a)` and `(rewrite (Mul a (Const 0)) (Const 0))`
each constrain an atom to `Const(0)`, which no term in this benchmark creates,
so the same emptiness check drops them before they run and they are absent from
the report.

Per-variant totals for the top three rules, summed over eleven iterations:

| rule | variant | matches | time |
|---|---|---|---|
| `Mul a (Add b c)` | 0 (`Add` new) | 252,690 | 61.2ms |
| | 1 (`Add` old, `Mul` new) | 56,830 | 12.5ms |
| `Add a (Add b c)` | 0 (inner new) | 277,075 | 46.1ms |
| | 1 (inner old, outer new) | 40,753 | 8.2ms |
| `Add (Mul a b) (Mul a c)` | 0 | 31,086 | 31.4ms |
| | 1 | 6,607 | 9.4ms |
| | 2 | 6,526 | 9.1ms |

## Delta effectiveness, and the naive comparison

The single most informative number: on this benchmark egglog's seminaive
evaluation is worth nothing in wall time.

| | matches | search+apply | merge | rebuild | wall (5 runs) |
|---|---|---|---|---|---|
| seminaive (default) | 943,092 | 217.4ms | 70.7ms | 196.0ms | 0.53 0.52 0.52 0.53 0.52 |
| `--naive` | 1,070,188 | 213.5ms | 74.6ms | 193.4ms | 0.51 0.50 0.52 0.54 0.53 |
| `--no-decomp` | 943,092 | 217.3ms | 70.6ms | 197.0ms | 0.53 |

Seminaive removes 11.9% of the matches and costs 0.4% more search time to do
it. The two configurations are indistinguishable at 0.52s. `--naive` is wired
through `src/cli.rs:110` to `EGraph::seminaive` and reaches the backend at
`src/lib.rs:1163-1175`, so the flag is doing what it says: the match counts
differ.

The reason is the growth curve. The delta is only useful while it is small
relative to the table, and here it is not:

| iteration | `Add` rows | seminaive matches | naive matches | ratio | search | merge | rebuild |
|---|---|---|---|---|---|---|---|
| 0 | 20 | 20 | 20 | 1.00 | 0.07ms | 0.00ms | 0.00ms |
| 1 | 36 | 44 | 64 | 0.69 | 0.11ms | 0.01ms | 0.01ms |
| 2 | 69 | 65 | 129 | 0.50 | 0.11ms | 0.01ms | 0.00ms |
| 3 | 150 | 139 | 268 | 0.52 | 0.15ms | 0.01ms | 0.02ms |
| 4 | 317 | 368 | 627 | 0.59 | 0.23ms | 0.02ms | 0.02ms |
| 5 | 646 | 895 | 1,495 | 0.60 | 0.42ms | 0.05ms | 0.08ms |
| 6 | 1,165 | 2,195 | 3,453 | 0.64 | 0.85ms | 0.12ms | 0.15ms |
| 7 | 2,977 | 4,818 | 7,797 | 0.62 | 1.79ms | 0.29ms | 0.31ms |
| 8 | 12,067 | 16,665 | 23,804 | 0.70 | 5.43ms | 1.02ms | 2.72ms |
| 9 | 70,487 | 95,893 | 117,203 | 0.82 | 25.18ms | 6.51ms | 15.77ms |
| 10 | 641,743 | 821,990 | 915,328 | 0.90 | 189.93ms | 68.30ms | 198.99ms |

The `Add` table grows 9.1x in the last iteration, so 89% of its rows are new
when the last iteration runs, and the delta suffix covers 89% of the table.
Iteration 10 accounts for 84.7% of all search time and 91.2% of all rebuild
time. Seminaive's saving is bounded by what it can exclude from that one
iteration, which is 10% of the matches, and it pays for that with 322 plan
instantiations against naive's 238.

This is a property of the benchmark, not of either engine's seminaive
implementation. On a workload whose e-graph converges instead of growing 9x in
its final iteration, the delta ratio would stay near its iteration-2 value of
0.50 and the picture would be different. That is a measurement to make on a
different benchmark, not an inference to draw from this one.

## What the report does not contain

`--report-level stage-info` is documented as adding per-stage statistics on top
of the query plan, but the statistics are never populated: `SinglePlan::to_report`
writes `None` into every stage's `StageStats` slot
(`core-relations/src/free_join/plan.rs:384`), and the execution path carries a
`// TODO: add stats` where it would fill them
(`core-relations/src/free_join/execute.rs:481`). On this commit `stage-info`
and `with-plan` produce identical output. Per-stage candidate and success
counts, which would give the selectivity of each join stage, are not available
without patching the engine.

The report also names every atom by its table, so a plan over two `Add` atoms
prints both as `Add`. Atom identity has to be recovered from the variable names
in the scan specification, or from the trace-level dump, which prints `AtomId`.
