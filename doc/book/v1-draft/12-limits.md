# Limits

This chapter states each result of the earlier chapters as what it does not give
you, in eleven sections: three on what the method does not do (uncorrelated
errors only, localizing without adjudicating, optimal without readable), two on
what a declaration does not check (an attribute is an assertion, declared
properties are not a theory), four on how to read one specific output (`!=`,
`checkau`'s bound, `:cr`, and the cost of `exact`), and two on what this book
does not measure or ship (the noise rates, the playground).

## The method finds uncorrelated errors only

This section states what a small `Variants` count is evidence of, and what it is
not.

Two candidates that make the *same* mistake agree at that position, and
agreement is exactly what the anti-unifier reports as shared skeleton. The
method is silent on it. Since two runs of the same model on the same sentence
share a prior, the errors are not independent, and a systematic misreading of an
ambiguous phrase is the case most likely to be shared.

So a small `Variants` count is not evidence of correctness. It is evidence of
agreement, and agreement between correlated sources is weak evidence.
Anti-unification is a way to spend a reviewer's attention well, not a soundness
argument.

## It localizes, it does not adjudicate

This section separates reporting a disagreement from settling it, and names the
kind of decision no tool settles.

A `Variants` node says the two candidates differ here and displays both
answers. Which one is right is a separate question, and
[chapter 7](07-repair-by-disagreement.md) has both outcomes: of two decisions,
one fell to a schema check and the other fell to nothing, because it was a fact
about the English sentence. There is no version of this tool that recovers the
second kind.

## Optimal is not the same as readable

This section states what the solvers' objective rewards, and what it leaves out.

The solvers minimize `(size, variant_mass)`. That objective rewards structure
sharing, which is why an `And` to `Or` difference is reported through two
identity elements rather than one connective-shaped node
([chapter 6](06-worked-example.md)), and why the corpus lands on that side of a
cost crossover ([chapter 9](09-corpus.md)). The result is correct and sometimes
the worse explanation, because nothing in the engine optimizes for explanation.

## Declaring an attribute is an assertion, and it is yours

This section states which side conditions a declaration leaves unchecked, and
that a domain rewrite carries the same exposure.

`:comm` on an operator makes the engine treat argument order as meaningless.
Whether that is true of the thing you are modelling is not checked. The concrete
instance in chapter 8: Cedar's `&&` short-circuits, so `a && b` and `b && a`
differ when an operand errors. The Cedar validator discharges that side
condition; the e-graph does not.

The same applies to a domain `(rewrite ...)`. `approvedRegion` expanding to two
named regions is a claim about a deployment. Asserting it collapses a reported
difference, and if the claim is wrong the collapse hid a real one.

## Declared properties are not a theory

This section lists what an ACI declaration with a unit gives you and what it
does not.

`:assoc-comm-idem` on `And` and `Or` gives you associativity, commutativity,
idempotence and, with `:identity`, the units. It does not give you
distributivity, De Morgan, absorption, or anything else about Boolean algebra.
Those are rewrite rules you write, and writing them changes what the engine
proves equal and therefore what it reports as agreed.

## `(check (!= ...))` is weaker than it looks

This section states what a passing disequality check means under each completion
setting.

It passes when the engine did not derive equality. With AC completion off, that
is a statement about congruence closure plus your rules. With `--lazy-ac-eqs` it
additionally means a goal-directed completion search reached its operational
fixpoint. Neither is a theorem of semantic disequality.

## `checkau` bounds from above only

This section states which direction of a size contrast `checkau` can assert, and
how the examples record the other direction.

It asserts `size <= :max_size`. So it can pin the good direction of a
contrast, and it cannot assert that some other configuration produces a
*different* size. `doc/book/examples/au-identity-arity.egg` says so in a comment
for exactly this reason: the size-10 bound carries the claim, and the size-13
line records a measurement rather than asserting a gap.

## `:cr` is not clamped over e-classes

This section gives the range of `:cr` over e-classes and what a reading of it
supports.

For a fixed pair of ground terms it runs from 0 to 1. Over e-classes the
denominator uses independently smallest representatives while the search may use
larger ones, so it can exceed 1. Read it as a comparison between runs on the
same pair, not as a percentage.

## `exact` is exponential in the worst case

This section gives the cost of the exact solver, the sizes it is fine on, and
what to use when it does not finish.

It is dynamic programming over the class-pair graph, and that graph is quadratic
in the class count before the AC structure multiplies it. On the problems in
this book it finishes in milliseconds and is faster than `uct`. On a large
saturated e-graph it will not finish, which is what `uct` and the hybrid mode
are for, and neither of those returns a certified optimum unless it says
`:completion exact`.

## The noise rates here are chosen, not measured

This section separates the part of the examples that is drawn from real model
output from the part that is picked by hand.

The kinds of difference in the examples are ones language models really emit.
Their frequencies in these files are picked by hand. [Chapter 9](09-corpus.md)
is the closest thing to a rate measurement in this repository and it is a
generated corpus, not a sample of real model output. No claim in this book is a
claim about how often anything happens in practice.

## There is no live playground yet

This section names the two things that block a `wasm32` build.

The engine does not currently build for `wasm32`, so there is no in-browser
version of these examples. Two things block it: the `containers-verus`
dependency has 64-bit-only paths, and the anti-unification solvers call
`Instant::now()` for their budget accounting. Both are fixable and neither is
done.
