# General policy conditions

> Chapter contents: the method on a policy whose conditions are not a single flat
> conjunction, four samples, the partition, the two seeded errors, the unexpected form
> the connective error is reported in, and a cross-check of the answer under graph
> search.
>
> Carry over: `v1-draft/06-worked-example.md` is the spine of this chapter and every
> number in it is measured against
> `egraph/examples/au_policy_divergence.egg`. Keep the sentence, the signature, the two
> encodings, the four-line account of which declarations do work, the size-42 and
> size-35 outputs, the substitution walk-through of the two-identity-element form, and
> the `uct` cross-check.
>
> Two changes are required. First, the v1 draft compares two candidates and this part's
> method takes three to five, so add two more samples and run the clustering step from
> chapter 18 before the pairwise queries. Second, it referred to a corpus chapter that no
> longer exists for the readability crossover; either state the crossover as an
> observation on this example or drop the claim.
>
> Example: write `examples/22-policy-conditions.egg`, self-contained. It may take the
> two existing encodings from `egraph/examples/au_policy_divergence.egg`, and its
> assertions must be re-measured after the two new samples are added, since size and
> `:cr` will change.

## The sentence

> Keep the v1 cross-region replication sentence. It is long enough to have a nested
> conditional, a numeric threshold and an implication, which is what makes it the right
> final example.

## The signature

> Keep the v1 declarations and the account of which four do work: `And` and `Or` ACI
> with their Boolean units, `Eq` commutative, `Lit` embedding the concrete `bool` sort
> so the units are real terms. Keep the statement that nothing else about Boolean
> algebra is implied, and the note that the nullary domain operators make this a ground
> instance for one request rather than a quantified policy.

## Four samples

> The two v1 encodings plus two more. Design the new ones so the partition is
> informative: one that agrees with an existing sample modulo the declared algebra, and
> one that introduces a third reading of one of the two seeded errors. State the seeded
> errors plainly, since this example is constructed and pretending otherwise would be
> dishonest: `Or` where the sentence says *and*, and a strict comparison where the
> sentence says *up to*.

## The partition

> The grid, the cluster count, and which noise the declarations absorbed with nothing
> asked of the search: conjunct order and the argument order of `Eq`.

## The disagreements

> The pairwise queries and their outputs. Keep the v1 accounting of the three groups in
> the size-42 result and which of them are the seeded errors.

## The connective error is reported through two units

> Keep this section nearly whole: it is the most instructive output in the book. The
> `And`/`Or` error appears as two groups expressed through the two identity elements
> rather than as one group holding `And` against `Or`. Keep the substitution walk-through
> of both sides. Keep the honest assessment that the smaller result is not the more
> readable one, and tie it to chapter 16's third qualifier: the objective is a definition
> of best, and this is the case where a reader can see that definition choosing.

## The domain fact

> Keep the v1 section: the `approvedRegion` expansion is a claim about the deployment
> rather than an operator law, so it is a rewrite rule and a run. Keep both output blocks
> and the drop from 42 to 35 and from 0.59 to 0.40, re-measured for four samples. Keep
> the observation that this is the step a syntactic diff cannot take at any level of
> effort.

## Cross-checking under graph search

> Keep the v1 section: the same query under `:algorithm uct` with a stated budget returns
> the same term. State what the cross-check is worth, which is a check on the exact
> solver's answer on a new problem shape, and repeat chapter 15's advice that `exact` is
> both certified and faster at this size.
