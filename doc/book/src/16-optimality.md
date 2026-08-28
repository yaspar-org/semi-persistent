# What the result is optimal with respect to

> Chapter contents: the three qualifiers on an `exact` result, the measured
> consequence of each, and the one that changes how a reader should configure the
> engine before asking an anti-unification question.
>
> Examples: `examples/16-au-plain.egg`, `16-au-eager.egg`, `16-au-lazy.egg` exist:
> one program, three congruence modes, three measured results. They are the chapter.
>
> Carry over: `v1-draft/14-au-and-ac.md` is this chapter. One repair is required
> before reuse. Its "Measured" section opens with a sentence whose successor depends
> on it ("The case is wrapped in one common operator ..."), so rewrite that opening
> into a single self-contained sentence introducing the program.
>
> Sources: design `19-anti-unification.md` section 2.8 (optimality is relative to the
> e-graph, not to the AC theory), 2.7 (what correctness means here), 9.6 (the current
> proof boundary), and `ac-congruence-completeness.md`.
>
> This is the chapter that keeps the book honest, and it is short. Do not hedge it
> into vagueness and do not overstate the negative: the result is optimal, and the
> chapter says what over.

## Optimal over the e-graph, not over the theory

> The search enumerates alignments of the e-nodes that are in the graph. Two
> subterms that are equal in the AC theory but not merged in the graph are two
> different things to the search, so it reports a disagreement between them. State
> this as the general principle and then measure it: `16-au-plain.egg` against
> `16-au-eager.egg`, one number each.

## Lazy completion does not help the anti-unifier

> The result the project measured and the reason it is not obvious. Lazy completion
> runs inside a transaction that is rolled back, and it runs when an equality check
> asks. Anti-unification does not ask an equality check: it snapshots the graph and
> searches the snapshot, and the snapshot is taken outside the lazy transaction. So
> the solver is handed the same incomplete relation plain mode would have given it,
> and the measured result is the same as plain rather than the same as eager. Give
> both sizes.
>
> The practical instruction that follows, stated once and plainly: if the operands
> involve AC equations whose consequences you need the anti-unifier to see, run with
> `--derive-ac-eqs`. Chapter 11's advice to prefer lazy when you only ask equality
> questions does not extend to this query.

## Optimal within the cycle policy

> The second qualifier. A side policy certifies the optimum of its filtered graph and
> can exclude a valid finite generalizer; pair mode admits every finite derivation of
> the snapshot's grammar. A quoted result should name its policy. Keep this to a
> paragraph and point at chapter 14 and design 2.3.

## Optimal under this objective

> The third qualifier, and the shortest. `(size, variant_mass)` lexicographic is a
> definition of best, not a fact about it, and a different definition would return a
> different term. Name the case where it shows, which is chapter 22's connective bug:
> the smallest anti-unifier reports the bug through two identity elements rather than
> as one `Variants` holding `And` against `Or`, and the smaller result is not the more
> readable one.

## What is argued rather than proved

> One short section. Name what has a machine-checked proof, what has finite
> differential evidence, and what is a prose argument with regressions, and give the
> design section for each. Include the pair-cycle-erasure argument and the round bound
> from design 2.2 and 9.6, and the hybrid soundness argument from 9.4. A reader
> quoting the engine's optimality in a paper needs this section to know what they are
> quoting.
