# Index Selectivity And Adaptive Matching

This chapter describes how the matcher estimates index selectivity, when it can
adapt atom order to a concrete binding, and how those choices compose with the
semi-naive full/delta index modes. It records current behavior and correctness
boundaries; historical performance investigations are not part of this design
contract.

Companion chapters: [indexes](06-index.md),
[leapfrog join](07-leapfrog.md),
[query compilation](08-query-compilation.md),
[pattern matching](09-pattern-matching.md), and
[semi-naive evaluation](18-semi-naive-evaluation.md).

## Selectivity Inputs

The scheduler chooses the next atom from a base relation cardinality and the
access paths available for already-bound keys. `IndexStore::measure_fanouts`
records three kinds of expected probe size for each round:

- `by_repr`: expected size of the class bucket reached by a class probe.
- `by_child_pos[(op, position)]`: expected number of `op` nodes in the parent
  bucket reached by a bound child at that position.
- `by_contains[op]`: expected number of variadic `op` nodes containing a bound
  element class.

Child-position and containment measurements are operator-restricted because a
join intersects those buckets with `by_op[op]`. A global bucket average would
mix unrelated operators and price a path the executor never opens.

For bucket sizes `b_i`, the estimator uses the size-biased mean

```text
sum(b_i^2) / sum(b_i)
```

rather than `sum(b_i) / bucket_count`. A key encountered while scanning index
entries lands in a bucket with probability proportional to that bucket's size.
The same pass records skew as

```text
(sum(b_i^2) * bucket_count) / sum(b_i)^2
```

which is `1` for a flat distribution and grows when a few hub buckets dominate.

These values are expectations, not per-binding facts. The runtime and sampled
modes below address that limitation at different points.

## Semi-Naive Cardinalities

A semi-naive variant assigns each join atom one of three modes:

| Atom position relative to the variant's delta atom | Mode | Base cardinality |
|---|---|---:|
| lower | `FullMinusDelta` | `|full.by_op| - |delta.by_op|` |
| equal | `Delta` | `|delta.by_op|` |
| higher | `Full` | `|full.by_op|` |

`variant_stats` stores this cardinality per atom, not per operator, because two
atoms with the same operator can have different modes in one variant.
`VariantIndex` applies the corresponding mode to every lookup emitted for that
atom. `FullMinusDelta` is a cursor difference over the full and delta buckets;
it is not materialized as a third index.

## Operator Restriction

A join with both `ByOp(op)` and a narrower bound-key lookup can enforce the
operator condition in either of two equivalent ways:

1. Keep `ByOp(op)` as a leapfrog intersection cursor.
2. Iterate candidates from the other lookup and test `op[candidate] == op`.

Both return the same set because all index families are built from the same
node stream. Their costs differ with the live bucket lengths, so the default
`OpFilterPolicy::Adaptive` decides per binding. Let `m` be the smallest other
bucket and `n = |by_op[op]|`; the implementation uses the candidate test when

```text
n >= min(512 * m, 131072) && m <= 2 * n
```

`AlwaysFilter` and `AlwaysLeapfrog` exist for conformance testing. The policy is
read once per query, and release execution carries no decision log.

## Atom Scheduling Modes

`SchedulingMode` has three values:

- `Static` is the default. The scheduler produces one step array from the
  round's cardinalities and fan-out estimates.
- `Runtime` re-runs the eager/choice loop at each binding and selects the unused
  atom whose first join opens the shortest live bucket. For
  `FullMinusDelta`, it reads the full-side bucket length as an upper bound; it
  does not traverse the difference merely to price it.
- `Auto` selects runtime ordering per rule per round when the rule's worst
  child-position or containment skew exceeds `8`; otherwise it uses the static
  plan.

Runtime scheduling represents bound variables and used atoms as `u64` masks.
Queries wider than 64 atoms or variables fall back to the static plan. Lowered
segments are memoized by atom and the two masks, so repeated binding states do
not recompile the same block.

The runtime choice is a performance choice only. It lowers the same resolved
atoms against the same `VariantIndex`; ties use the lowest atom index for
determinism.

CLI controls:

- `--runtime-scheduling`
- `--auto-scheduling`

The two modes are mutually exclusive.

## Sampled Cross-Index Selectivity

The size-biased mean assumes that keys produced by one atom follow the marginal
distribution of the index probed by the next atom. That need not hold. Optional
plan-time sampling estimates the joint distribution directly:

1. Draw up to `k` evenly spaced nodes from the emitter atom's driver relation.
   `Delta` samples delta; `Full` samples full; `FullMinusDelta` deliberately
   samples full as an upper-bound proxy rather than paying to materialize or
   count the difference.
2. Extract the classes exposed at the relevant node, child, or variadic-element
   site.
3. Read the operator-restricted target bucket lengths for those classes.
4. Replace the mean fan-out with the mean of those sampled lengths.

The draw is deterministic. Long target buckets are inspected through an
even-stride sample capped at 256 entries, then scaled to the bucket length.
Estimates and emitter draws are memoized for one scheduling call.

`SamplerConfig` defaults to `k = 32`, no bootstrap, and a coefficient-of-
variation threshold of `1.0`. When bootstrap resampling is enabled, an unstable
estimate is discarded and the scheduler falls back to the size-biased mean.
The fixed-seed resampler keeps plan selection reproducible.

Sampling is off by default. CLI controls are:

- `--sampled-selectivity`
- `--sampler-k`
- `--sampler-bootstrap`
- `--sampler-cv`

Sampling affects construction of the static plan. Runtime scheduling records
which atoms have already run and which node variables are already bound in two
`u64` bit sets. When a query has at most 64 atoms and at most 64 node
variables, per-binding `Runtime` scheduling does not consult the static plan or
the sampler. If either count exceeds 64, the matcher uses the static plan
instead. Under `Auto`, sampled estimates affect rules that stay on the static
path and this width fallback for rules otherwise selected for runtime
scheduling.

## Correctness Boundary

The planner and runtime scheduler may reorder conjunction atoms, but they do not
change the atom set, index snapshot, or per-atom semi-naive mode. The relevant
invariants are:

- all index families in a `VariantIndex` describe one snapshot;
- operator filtering and `ByOp` intersection denote the same candidate set;
- every semi-naive variant preserves its `Delta`/`FullMinusDelta`/`Full` mode by
  atom id, independent of execution order;
- static, runtime, and sampled plans evaluate the same conjunction.

The implementation validates these with deterministic tests:

- `ematch::tests::op_restriction_*` checks the policy and set equivalence;
- `tests/ematch_op_filter.rs` compares all restriction policies on hub-shaped
  inputs;
- `tests/ematch_runtime_schedule.rs` compares match sets and candidate-step
  counts for static and runtime ordering;
- `tests/ematch_sampled_selectivity.rs` checks sampled plans, fallback, and
  match-set equality;
- `saturate::variants_disjoint_and_complete` checks semi-naive decomposition
  under both scheduling modes;
- the `.egg` corpus runs with both static and runtime ordering.

Candidate-step assertions are deterministic correctness/performance-structure
checks. Wall-clock claims belong in Criterion benchmarks such as
`saturate_bench`, `leapfrog_bench`, and `index_bench`; tests do not fail on
host-sensitive timing ratios.

## Deferred Alternatives

**Watermark delta suffixes are not implemented.** Dense allocation-ordered node
ids could let a sorted bucket represent `delta` as the suffix at a round
watermark. The current engine instead builds separate full and delta indexes and
derives `FullMinusDelta` with a difference cursor. A suffix design would need to
preserve bucket id order and prove that the watermark exactly characterizes all
new-or-changed tuples, including class-growth events.

**Whole-stage re-sorting is not implemented.** Runtime mode chooses which atom
to lower next but preserves each atom's compiled variable order. A free-join
executor that reorders stages inside an atom would require a different execution
model and a separate correctness argument.

**Cross-round learned profiles are not implemented.** All estimates come from
the current immutable index snapshot. No execution history is fed into later
rounds.
