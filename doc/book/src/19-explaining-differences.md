# Explaining the differences between clusters

> Chapter contents: how to turn a set of clusters into a set of anti-unification
> queries, how to read each returned `Variants` group as a decision a reviewer has to
> make, how to order the decisions, and how to test a candidate resolution without
> disturbing the graph.
>
> Example: write `examples/19-explain-clusters.egg`, continuing the program of chapter
> 18 so the reader carries one signature through both chapters. It ends with one
> `checkau` per cluster pair, and with a `push`, a candidate resolution asserted, a
> check, and a `pop`.
>
> Sources: chapters 12 to 16 for the query, chapter 7 for the scopes. No new
> mechanism.

## One query per pair of clusters

> Pick one representative per cluster, then anti-unify each pair. With k clusters that
> is k(k-1)/2 queries, and for three clusters it is three lines. Show them and quote
> the output.
>
> State why representatives are safe to pick arbitrarily: the operands of `antiunify`
> are e-classes, so any member of the cluster names the same class and the answer does
> not depend on which sample you named. This is worth stating explicitly because it is
> the property that makes the whole procedure well defined.

## Reading a group as a decision

> Each `Variants` group is one position where the samples disagree, carrying both
> readings. Walk one from the example: what the skeleton around it establishes, what
> each side says, and what a reviewer would have to know to choose. State that the
> engine has ranked nothing and that choosing needs a schema, a test or a person, which
> chapter 12 already said and this chapter has to show.

## Ordering the decisions

> What the reader has to work with when there are several groups, stated without
> inventing a metric the engine does not compute: `:cr` per pair, which says how much
> of the two operands is shared and therefore how localized the disagreement is; the
> size of each group's two sides; and how many cluster pairs a given position appears
> in, since a position that differs across every pair is a position every sample
> disagreed about.
>
> Give the practical order the examples in chapters 20 to 22 follow, and say it is a
> convention, not a result.

## Testing a resolution

> The use of scopes from chapter 7, shown on the running example: `push`, assert the
> reading you believe is right as a union or a rule, re-run the cluster grid to see
> which clusters merge, `pop`, then try the other reading. Show both and quote both
> grids. State what this gives a reviewer that reading the formula does not: the
> consequence of a choice, measured against every other sample.

## When the samples agree and are all wrong

> The limit of the method, stated here because this is the chapter where a reader
> starts trusting it. One cluster means no disagreement was found, which is not
> evidence of correctness: it is evidence that the samples did not disagree, and
> correlated errors are the common reason. One paragraph, then chapter 23.
