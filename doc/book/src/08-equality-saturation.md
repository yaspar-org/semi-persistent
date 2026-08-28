# Equality saturation

> Chapter contents: what a saturation round does, what saturation is a fixpoint of,
> the four forms of `run`, what `extract` returns and how cost is assigned, and the
> two ways a run ends other than saturation.
>
> Example: `examples/08-saturation.egg` exists and is already tied to a round count.
> Read it first.
>
> Sources: design `12-rule-application.md`, `16-extraction.md`, `17-interpreter.md`.
>
> Carry over: `v1-draft/02-first-program.md` sections "Saturation", "Checking" and
> "What 14 nodes counts" are accurate and measured. The last of these accounts for
> every node in a small graph and is worth keeping: it is the only place in the book
> that reconciles a printed count against a term by hand.

## A round

> The three phases in order: match every rule against the graph, apply the actions,
> rebuild. State that all matching happens against the graph as it stood at the start
> of the round, so a rule cannot see another rule's output within a round, and that
> this is what makes a round independent of rule order.

## Saturation

> The fixpoint condition: a round that adds no node and merges no class. State what
> it is a fixpoint of, in the words a reader must not misread: the declared rules,
> not the theory. A law nobody wrote does not hold, and `(check (!= ...))` passing
> means only that nothing derived the equality.
>
> Show a program that saturates in fewer rounds than requested and quote the output
> that says so.

## The four forms of run

> `(run n)`, `(run ruleset n)`, `(run n :until (= t1 t2))`, `(run n :until (!= t1
> t2))`. One line each. State what happens when the bound is reached without
> saturation, which is the case a reader will hit on a real problem: the graph is a
> sound under-approximation and the checks below it are about what was derived so
> far.

## Non-termination

> Which rule shapes do not saturate, with the smallest example that does not. State
> the practical rule the rest of the book follows: bound the run, then assert what
> you need with `check`, and treat an unbounded rule set as a bug in the rule set
> rather than something the engine will resolve.

## Extraction

> `(extract t)` returns a lowest-cost term from a class. State the cost model
> including how `:cost` and `:unextractable` enter it, and what happens when a class
> contains a cycle. Show one extraction on a class holding several terms.
>
> State the relation to the rest of the book in one sentence: extraction picks one
> term out of one class, anti-unification compares two classes, and Part III is
> about the second.

## Statistics

> `(print-stats)` and `(print-stats :file "p.json")`: what fields they report and
> which of them a reader would use to decide a rule set is too slow. Quote real
> output. Keep it short.
