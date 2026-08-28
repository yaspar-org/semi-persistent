# Three congruence closures

> Chapter contents: what plain congruence closure derives over AC operators, what
> eager AC completion adds and what it costs, what lazy AC completion does instead
> and what its answer means, one program run under all three with its measured
> output, and how to choose.
>
> Examples: `examples/11-cc-plain.egg`, `11-cc-eager.egg`, `11-cc-lazy.egg` exist:
> one program body, three directive lines. Their header comments already contain
> usable explanatory prose written against the implementation. Read all three first.
>
> Sources: `ac-congruence-completeness.md` is the primary source and states the
> completeness boundary. `ac-completion-spec.md` for the procedure.
> `ac-algebraic-properties.md` for the representation.
>
> This chapter has to keep two things apart that are easy to conflate, and the
> conflation is the reason it exists: AC **matching** is complete in every mode
> because leapfrog matching enumerates sub-multisets, and what the modes differ in is
> the **completion** procedure that runs in rebuild. State this early, state it once,
> and do not let any later sentence blur it.

## Plain congruence closure

> The default. Canonization normalizes each node's children and congruence closes
> under equal arguments. State exactly what this gives over an AC operator and show
> the case it misses: `examples/11-cc-plain.egg` ends in a `(check (!= ...))` that
> passes, and the reader should see that the two terms are AC-equal in the theory and
> not equal in the graph. Explain why in terms of chapter 10: no single node's
> children changed, so nothing recanonized.

## Eager AC completion

> `--derive-ac-eqs`. What completion does, at the level the file's header comment
> already puts it: treat each asserted AC equation as a rewrite rule on multisets and
> close that rule set under substitution of a known sub-sum and under superposition of
> two overlapping sums. Show the same program deriving the equality.
>
> State the two costs, both of which are observable: the closure runs on every
> rebuild whether or not anything needed it, and it mints nodes that stay in the
> graph. Give the node counts from the two files.
>
> State what the completion needs to converge, since the project learned this the
> hard way: naive superposition that merges both reducts without orienting the
> equation, normalizing before comparing, and inter-reducing the basis diverges.
> Name orientation, normalization and inter-reduction as the parts that make it
> terminate, cite `ac-completion-spec.md`, and keep it to a paragraph.

## Lazy AC completion

> `--lazy-ac-eqs`. Completion runs only when an equality check needs it, inside a
> transaction that is rolled back afterwards, so the graph does not grow. State the
> two consequences precisely: a `check` gets the completed answer, and anything that
> reads the graph rather than asking a question does not. The second consequence is
> what chapter 16 is about, so forward reference it here and do not develop it.
>
> State what `(check (!= ...))` means in this mode: a goal-directed completion search
> reached its fixpoint without deriving the equality.

## The three modes side by side

> One table: mode, flag, what it derives, when the work happens, whether the graph
> grows, and what a negative check means. Then the measured numbers from the three
> example files.

## Choosing

> Plain unless an AC equation has been asserted and you need its consequences. Lazy
> when you only ask equality questions. Eager when something other than a check reads
> the graph, which includes extraction and anti-unification. Say it in a short
> paragraph and point at chapter 16 for the anti-unification case, which is the one
> the rest of the book depends on.

## What is not implemented

> The honest boundary, in a few sentences: completion is ground AC completion over
> the asserted equations, `:cancellative` participates, and full group reasoning is
> not there. Cite `ac-congruence-completeness.md` for what is claimed and what is
> argued rather than proved, and cross-reference chapter 23.
