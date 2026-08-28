# Limits

This chapter collects the boundaries established by the preceding chapters.
Each result is relative to declared laws, asserted equations, implemented
search procedures, and the evidence named below.

## Saturation is a fixpoint of the selected rules

Chapter 8's fixpoint contains what the declarations and selected rules derive.
An omitted domain law remains unavailable. A passing disequality check says
that the selected procedure did not derive equality; it is not a theorem of
semantic inequality.

## An algebraic declaration is an assertion

Chapter 4's tags cause Semper to enforce the listed laws, but Semper does not
prove that the modeled operator satisfies them. Structural declaration
invariants, including equal argument and result sorts for associative
operators, are checked separately.

## Inverse and cancellative reasoning are narrow

Chapter 4 defines the current behavior. `:inverse` cancels represented inverse
pairs and `:cancellative` contributes inference during AC completion. Pairs
exposed only after later merges can require completion, and the tags do not
derive double inverse, inverse distribution, or normalized signed
coefficients.

## Completion is opt-in and operational

Chapter 11's eager and lazy completion can stop at a growth or alternation
budget. An unchanged implemented round is an operational fixpoint, not an
unconditional completeness theorem. Lazy completion serves equality checks
and restores its transaction before anti-unification; Chapter 16 measures the
resulting difference.

## AC matching is maximum-partition matching

Chapter 5's scalar variables bind complete stored children and their
multiplicities. They do not range over implicit sub-sums or split one stored
multiplicity among several scalar variables. The implemented relation is a
specialization of classical AC matching, not a complete implementation of it.

## AU optimality has three qualifications

As Chapters 14 and 16 show, `:completion exact` certifies the minimum under the
`(size, variant_mass)` objective, over the equalities in the current e-graph
snapshot, and within the derivations admitted by the selected cycle policy.
Changing any of those three inputs can change the result.

## The production solver is not machine-verified

The `au-verus` crate proves objective and recurrence lemmas, not end-to-end
refinement of the Rust solver. Pair-cycle erasure, AC and ACI transport, and
global optimality retain prose arguments plus finite oracle and regression
evidence. Chapter 16 and the
[AU correctness plan](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/future/au-correctness-and-validation.md)
state the boundary.

## `checkau` and `:cr` are measurements

Chapter 12 defines both fields. `checkau` asserts only that the result is no
larger than `:max_size`; it does not assert an exact size. For e-classes,
`:cr` compares against independently smallest representatives while search may
select larger terms, so it can exceed one.

## Agreement is not evidence of correctness

Chapter 17 explains the correlated-error case. Samples can share the same
mistake, especially when one model and prompt produced all of them. Clustering
then reports agreement at that position because there is no disagreement to
localize.

## The smallest result need not be the clearest explanation

Chapter 16 demonstrates the objective's preference for a smaller common
representation, and Chapter 22 shows one connective change through two identity
elements. A presentation layer may need to regroup markers into domain-facing
decisions.

## Surface clustering is quadratic

Chapter 18 uses `n(n - 1) / 2` equality checks because Semper has no
clustering command. That grid is practical for the three-to-five-sample
workflow in this book. Larger collections require host code to group e-class
identifiers.

## The application evidence is limited

The examples in Part IV are constructed cases. The repository's formalizer
pilot uses one system to produce both readings and explicitly reports an
optimistic bound. It does not measure independent formalizers or population
error rates.

## Anti-unification does not adjudicate

Chapter 12 defines an anti-unifier as a shared skeleton with alternatives.
Schema validation, tests, domain facts, or a person must decide which
alternative should be enforced.
