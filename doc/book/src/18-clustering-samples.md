# Clustering samples by equality saturation

Clustering composes the declarations, saturation, and equality checks from
Parts I and II. This chapter builds a partition of four samples, shows how one
domain fact changes it, and gives checks for diagnosing an unexpected
partition.

## The procedure

For one set of samples:

1. Declare the shared signature and only the algebraic properties valid in the
   domain.
2. Insert every sample with a distinct `let` name.
3. Assert the domain equalities that the comparison may use.
4. Run the selected rules to saturation.
5. Check every pair of sample names for equality or non-equality.

The fixture performs the checks both before and after its domain rule:

```lisp
{{#include ../examples/18-clusters.egg:clustering-program}}
```

All samples enter one e-graph. `s1` and `s2` canonize to the same node, so no
later proof is needed to join them. A rewrite can merge other sample classes
without discarding either representation.

## Reading the partition

Semper has no surface command that prints a partition. For four samples, the
six pairwise checks record it directly. Before the rewrite, the checks assert

```text
{s1, s2}  {s3}  {s4}
```

`s1` and `s2` differ only by conjunct order and a duplicate `core`. The ACI
declaration for `And` absorbs both. `s3` expands `approvedRegion` into two
specific regions, and `s4` names a different second region.

The four initial extractions print:

```text
(And (core) (approvedRegion (destination)))
(And (core) (approvedRegion (destination)))
(And (core) (Or (usEast (destination)) (euWest (destination))))
(And (core) (Or (usEast (destination)) (apSouth (destination))))
```

The rule states that this deployment's approved regions are `usEast` and
`euWest`. After three rounds, the partition is

```text
{s1, s2, s3}  {s4}
```

Extraction now prints the `approvedRegion` representative for the first three
samples. It still prints the `apSouth` disjunction for `s4`.

The check grid uses `n(n - 1) / 2` checks for `n` samples. For a larger
corpus, host code can group the class identifiers returned through the Rust
API. There is no separate clustering API.

## What the partition depends on

A cluster means that Semper proved its members equal under this program. It
does not assert semantic equivalence independently of the program.

| input to the comparison | effect |
| --- | --- |
| declaration attributes | decide which terms canonize during construction |
| rewrite and union commands | supply the domain equalities available to saturation |
| selected ruleset and round limit | decide which installed rules run and whether they reach a fixpoint |
| completion mode | decides whether additional AC or ACI consequences enter the retained graph |

The first and second partitions differ only because the rewrite was installed
and run. The samples themselves did not change.

## When a cluster is too fine

First inspect the unresolved syntax. If it is order or repetition, check the
Chapter 4 declaration. If it is a domain equation, check that Chapter 8 ran
the relevant ruleset to saturation. If it is an equality hidden by flattened
AC structure, Chapter 11 explains when `--derive-ac-eqs` is required.

## When a cluster is too coarse

A rule or union may have asserted more than the domain permits. With
`--proofs --dump-proofs FILE`, the proof dump records one path from each node
to its representative, including rewrite identifiers along that path. It can
identify which merge joined a class, but it does not directly produce a
named sample-to-sample explanation or enumerate alternative proofs. The
[proof-logging design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/15-proof-logging.md)
defines that output and its verification boundary.
