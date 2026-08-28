# A larger Dogwood policy

> Chapter contents: a rule with several conditions, five sampled encodings, a partition
> with more than two clusters, the pairwise queries that explain it, one difference that
> a domain rewrite dissolves and one that it cannot, and the decision a reviewer is left
> with.
>
> Example: write `examples/21-dogwood-larger.egg`. Five samples. The partition must move
> when the domain rewrite is asserted, so the file runs the grid twice, and it must
> retain at least one real disagreement afterwards. Keep it under a screen and a half.
>
> Sources: same as chapter 20, and the same scope discipline. Reuse chapter 20's
> signature where it fits and say that you are reusing it, so the reader is reading new
> material only.
>
> This is the chapter that shows the method at the size where a diff stops being usable,
> so the counts are the argument: how many textual differences, how many clusters, how
> many decisions.

## The rule

> Quote the English. Several conditions, at least one nested implication or conditional,
> and at least one numeric comparison, since those are where the two most common
> formalization errors live.

## Five samples

> The five encodings. Do not narrate all their differences: state the count and let the
> clustering find them, since the point of the chapter is that reading them is what the
> method replaces.

## The partition before the domain facts

> The check grid, quoted, with the cluster count. Then one sentence per cluster naming
> what distinguishes it, derived from the queries in the next section rather than
> asserted here.

## Explaining each pair

> One `checkau` per cluster pair, quoted. For each, the group or groups it reports and
> what each group means. Group the discussion by disagreement rather than by pair, since
> the same position will show up in several pairs, and say that it does.

## A domain fact merges two clusters

> The rewrite rule that expresses the deployment fact, the run, the new grid, and the
> new query output. Quote the sizes and the `:cr` values before and after. State the
> general point once, in the words chapter 18 already established: the partition is
> relative to what you declared and asserted, and this is how a reviewer discharges a
> difference they know is not a difference.

## What is left

> The disagreements that survive, each stated as a decision with both readings, and for
> each one what would settle it: a schema, a test, or a person who knows what the
> sentence meant. If one of them is settleable mechanically, settle it and show that.
> If none is, say so plainly rather than manufacturing a resolution.
