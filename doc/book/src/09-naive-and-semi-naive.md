# Naive and semi-naive evaluation

Chapter 8 defines the saturation round. This chapter compares only how the
naive and semi-naive strategies schedule matches within that round: full
recomputation, delta variants, and the cases that retain a full-index fallback.

## Naive evaluation

Given the post-rebuild snapshot defined in Chapter 8, naive evaluation matches
every selected rule against all indexed nodes. A match found in iteration 3
can be found and acted on again in iterations 4 and 5. There is no
cross-iteration set of previously applied matches.

This strategy repeats matching work as the graph grows. Its advantage is a
simple execution path with no delta bookkeeping, so it serves as the reference
strategy in differential tests.

## Semi-naive evaluation

Semi-naive evaluation uses a full match in its first iteration because the
entire initial graph is new. In later iterations it builds both the full index
and a delta index. The delta contains nodes touched since the previous full
index was built:

- nodes created by rule actions;
- nodes recanonicalized during rebuild;
- members recorded when one e-class is absorbed into another.

The delta is not merely a suffix of newly allocated node IDs. A merge can change
a stored node's canonical children or enlarge a class without allocating a
node, and either event can enable a match.

For an eligible rule with `k` relation-scanning atoms, Semper evaluates `k`
variants. Variant `i` restricts atoms before `i` to `full` minus `delta`,
restricts atom `i` to `delta`, and leaves later atoms on `full`. Every selected
match belongs to the variant containing its first delta atom, so the variants
do not duplicate one another.

Equality constraints, primitive predicates, and global comparisons are filters,
not relation-scanning atoms. Some equality and global-reference shapes can
become enabled by a merge that no scanning atom represents. Semper evaluates
those rules against the full index in every iteration rather than applying an
unsafe delta restriction.

## Delta boundaries

Rule actions performed during an iteration are outside its delta and become
visible in the next iteration. The four indexed relations, by operator, class
representative, child position, and variadic containment, all obey each atom's
`full`, `delta`, or `full` minus `delta` mode.

Variadic matching requires all four relations to share that boundary. An
associative, AC, or ACI parent can acquire a new canonical representation after
a child merge, and a class merge can expose new membership without changing the
surviving representative. Recanonicalized parents and absorbed class members
are therefore recorded in the touched log. Restricting only the operator scan
would miss or duplicate matches reached through child and containment indexes.

These rules implement the delta decomposition described in
[design chapter 18](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/18-semi-naive-evaluation.md).
The index relations are specified in
[design chapter 6](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/06-index.md).

## Equivalent outcomes

The user-facing contract is equivalent derivable equalities and check outcomes,
not identical execution traces. Naive evaluation emits old matches again.
Semi-naive evaluation emits delta-involving matches and uses full matching for
the exceptional rule shapes above. The strategies can consequently report
different emitted matches, node counts, iteration counts, and match-step counts.

The Chapter 9 fixture changes only the harness mode applied to the `dbl`
program introduced in Chapter 8:

```text
;; EVAL: both
```

The harness executes the multi-round program once with each strategy. Its
equality and disequality checks must pass in both executions.

The repository also differentially compares the resulting equality partition
over shared input nodes and exercises fresh nodes, recanonicalization, class
growth, variadic atoms, subsumption, globals, and equality constraints.
These executable tests support the implementation contract; they are not a
machine-checked proof of semi-naive completeness.

## Selecting a strategy

Naive evaluation is the default. `--use-naive` selects it explicitly, and
`--use-semi-naive` selects semi-naive evaluation. The flags are mutually
exclusive.

`EVAL` is a directive understood by the `.egg` test harness, not a Semper
language command. `;; EVAL: naive` and `;; EVAL: semi` select one strategy.
`;; EVAL: both` runs the fixture separately under both strategies and checks
the expected program outcome in each run.
