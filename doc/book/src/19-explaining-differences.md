# Explaining the differences between clusters

After clustering, one anti-unification query per cluster pair locates the
remaining differences. This chapter reads one such result and tests a proposed
domain resolution inside a temporary scope.

## One query per pair of clusters

For `k` clusters, choose one representative from each and run
`k(k - 1) / 2` queries. After Chapter 18's rewrite there are two clusters, so
its fixture needs one query:

```lisp
{{#include ../examples/18-clusters.egg:cluster-explanation}}
```

It prints:

```text
(anti-unify :size 9 :cr 0.7143 :completion exact
  (And
    (Or
      (usEast destination)
      (Variants (euWest destination) (apSouth destination)))
    core))
```

Any of `s1`, `s2`, or `s3` can represent the first cluster. An `antiunify`
operand resolves to its e-class, so all three names present the same search
state to the solver.

## Reading the explanation

The skeleton says that both clusters require `core`, use a disjunction of
regions, and include `usEast`. The marked position carries the remaining
alternatives:

```text
(Variants (euWest destination) (apSouth destination))
```

A reviewer must determine which region belongs in the deployment policy. A
configuration source, deployment test, or domain owner can settle that
question. Semper reports the alternatives but does not choose one.

A `Variants` node is a syntactic marker in the selected anti-unifier, not
necessarily one independent semantic decision. Chapter 22 shows one connective
change represented by two markers through identity elements.

## Ordering several differences

Semper reports `:cr` for each pair and the terms under each `Variants` node.
It does not rank review questions or aggregate them across queries. A review
can use three observable quantities as a convention:

1. inspect pairs with lower `:cr` first because their disagreement is more
   localized relative to their operands;
2. inspect smaller alternative subterms before alternatives that replace a
   complete formula;
3. group the same field and alternatives when they recur across cluster pairs.

Chapter 21 applies the third convention. These steps organize review; they are
not part of the AU objective from Chapter 12.

## Testing a resolution

A suspected domain equality can be tested without retaining it:

```lisp
{{#include ../examples/18-clusters.egg:speculative-resolution}}
```

Inside the scope, equating the two region predicates merges `s4` with all three
members of the other cluster. `pop` restores the two-cluster partition. The
scope behavior is the mechanism from Chapter 7; the union is only a hypothesis
being tested.

Even a one-cluster result establishes agreement only under the asserted facts.
Chapter 17's correlated-error warning still applies.
