# Naive and semi-naive evaluation

> Chapter contents: what the naive strategy recomputes each round, what the
> semi-naive strategy does instead, the invariant that ties the two together, the
> extra work semi-naive needs on variadic atoms, and how to select each.
>
> Sources: design `18-semi-naive-evaluation.md` is the specification.
> `06-index.md`, `07-leapfrog.md` and `20-index-selectivity-and-delta-suffixes.md`
> for the index and delta machinery this rests on.
>
> Example: write `examples/09-eval-strategies.egg` carrying `;; EVAL: both`, whose
> checks pass identically under either strategy. The value of the file is that the
> harness runs it twice.
>
> Audience note: a user does not need this chapter to use the engine, and the
> chapter should say so in its opening. It is here because the flag exists, because
> the two strategies are the clearest instance of the engine's differential testing
> discipline, and because a reader benchmarking the engine will otherwise measure the
> wrong thing.

## What naive evaluation does

> Full re-match every round: every rule is evaluated against the whole graph, so a
> match found in round 3 is found again in rounds 4 and 5. State the cost in terms
> of what it repeats, and state its one advantage, which is that it has no delta
> bookkeeping to get wrong and is therefore the reference.

## What semi-naive evaluation does

> A round only needs matches that use something new, so each rule is evaluated once
> per atom with that atom restricted to the previous round's delta and the others
> reading the full relation. State the standard result this rests on and the
> condition it needs: every match of the new round contains at least one new node.

## Where the delta argument needs care

> The case the implementation had to fix, stated as a property of variadic operators
> rather than as a bug report: for an AC operator, a parent atom driven from a child
> that did not change can still have a new match, because the parent's multiset
> changed. The engine re-joins such atoms against the intersection of the operator
> index and the representation index to keep the round delta-driven. Verify the
> current mechanism in `egraph/src/leapfrog/` and design chapter 18 before writing
> this, and name the indexes it actually intersects.
>
> State what the reader should take from it: a delta argument over a canonized
> representation is not the textbook one, which is why the two strategies are
> differentially tested on every example file rather than argued about.

## Selecting a strategy

> `--use-naive` and `--use-semi-naive` on the command line, `;; EVAL:` in a file.
> State the default. State the invariant that makes the choice safe: the two must
> produce the same match set, so they differ in work and never in result, and the
> test suite asserts this on every example in this book.
