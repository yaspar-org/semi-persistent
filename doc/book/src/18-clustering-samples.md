# Clustering samples by equality saturation

> Chapter contents: the procedure for putting several samples of one sentence into
> one e-graph and reading off which of them are the same formula, what the partition
> depends on, how to write it down as a test, and what to do when the partition is
> not the one you expected.
>
> Example: write `examples/18-clusters.egg`. Four samples of one small sentence over a
> Boolean signature with `And` and `Or` declared ACI with units. Two samples differ
> only in conjunct order, a third differs by an expanded predicate, a fourth has a
> real difference. Before the domain rewrite there are three clusters, after it two.
> The file writes the full partition down as checks in both states, so it fails if
> either partition changes.
>
> Sources: no new engine mechanism. This chapter composes chapter 8 (saturation),
> chapter 10 (canonization), chapter 4 (declarations) and chapter 6 (what an equality
> check asks). Say so in the opening: the procedure is a use of the engine, not a
> feature of it.

## The procedure

> Numbered, five steps, each one command form the reader has already met: declare the
> signature with the algebraic attributes the domain has; insert every sample with
> `let`, one name per sample; assert the domain facts as rewrite rules; `run` to
> saturation; then read the partition. Show the whole program.
>
> State the property that makes this work at all, since it is the reason the e-graph
> is the right structure here: every sample is inserted into the same graph, so two
> samples that canonize to the same node were never two things, and two that saturation
> proves equal become one class without anything being rewritten away.

## Reading the partition

> There is no command that prints the partition, so say what a reader actually does.
> Two ways, both of which run as written:
>
> - `(check (= si sj))` and `(check (!= si sj))` over all pairs. For four samples that
>   is six lines, and the file then records the partition and fails if it moves. This
>   is the form every example in this part uses.
> - `(extract si)` for each sample. Samples in one class extract to the same term,
>   which gives a readable cluster representative for free.
>
> Show both on the example. State the cost honestly: the check grid is quadratic in
> the number of samples, which is why this part stays at three to five samples, and a
> larger corpus needs the Rust API.

## What the partition depends on

> Three things, all already explained, and the section is a table pointing at them:
> the declared attributes, the rewrite rules asserted, and the number of rounds run.
> State the consequence: a cluster is not "these samples mean the same thing", it is
> "these samples are equal under the algebra you declared and the facts you asserted".
>
> Then show it moving. Assert the domain rewrite in the example file and re-run the
> grid: two clusters where there were three. This is the demonstration the whole part
> is built on, so give it the room it needs and quote both grids.

## When a cluster is too coarse

> The failure the reader will hit second: two samples that should be distinguished are
> in one class because a rule was too strong. State how to find out which rule did it,
> namely `--proofs` and `--dump-proofs` from Annex C, and say what question that
> answers. Keep it to a paragraph.

## When a cluster is too fine

> The failure the reader will hit first: two samples that are the same formula are in
> different classes. State the checklist, in the order that finds the cause fastest:
> is the law a declared attribute or an unwritten rule, did the run reach saturation,
> is the difference an AC consequence that needs `--derive-ac-eqs` (chapter 11). Each
> item is one sentence and a chapter reference.

## What comes next

> One paragraph. Clustering says which samples are the same. It does not say what the
> difference between two clusters is, and with three clusters there are three
> differences to explain. Chapter 19 explains them.
