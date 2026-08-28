# A simple Dogwood policy

> Chapter contents: one English rule from an agent runtime policy, a signature that
> models the fragment of the policy language it needs, three sampled encodings, the
> cluster partition, and the single disagreement the anti-unifier reports.
>
> Example: write `examples/20-dogwood-simple.egg`. Small enough to read in one screen:
> one sentence, three samples, two clusters, one `Variants` group. This is the first
> chapter of the part that shows the method end to end, so nothing in it should need a
> second pass to understand.
>
> Sources: Dogwood is an open source runtime verification policy language for agents.
> Take the operator set from the public guide at
> `https://dogwood-policy.github.io/dogwood/` and the repository at
> `https://github.com/dogwood-policy/dogwood`. A local clone may exist under the
> untracked `autoformalization/` scratch folder; you may read it, and neither the
> chapter nor the example file may reference that path or depend on anything in it.
>
> Scope discipline for both Dogwood chapters. The book is not a Dogwood tutorial and
> must not read as one. Model the fragment the example needs, say in one paragraph that
> it is a modeling choice rather than Dogwood's own semantics, and spend the chapter on
> the method.

## The rule

> Quote the English. One sentence, one condition with two conjuncts and one comparison,
> which is enough to seed a real disagreement and small enough that the reader can hold
> the intended reading in their head.

## Modelling the condition language

> The signature: a sort for conditions, a sort for each attribute domain the rule
> touches, the connectives declared with their algebraic attributes, and the comparison
> operators. State which declarations do work in this example and which are there only
> so the terms sort-check, so a reader can tell the difference.
>
> One paragraph on the modeling choice: what fragment is represented, what is left out,
> and that the encoding is chosen to make the engine's behaviour visible rather than to
> be a faithful compiler for the language.

## Three samples

> The three encodings as three `let`s. State the differences textually before running
> anything, and count them, the way a diff would. This is the baseline the chapter
> improves on.

## The clusters

> Run the procedure from chapter 18 and quote the check grid. Two of the three samples
> are one cluster. Account for why in terms of the declarations: name the attribute that
> absorbed the difference.

## The disagreement

> One `antiunify` between the two cluster representatives, its output, and the reading:
> one group, both sides quoted, and what a reviewer would check to resolve it. Then
> state what the chapter demonstrated in one sentence, comparing the number of
> differences a diff reported against the number of decisions the anti-unifier reported.
