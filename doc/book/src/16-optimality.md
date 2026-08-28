# What the result is optimal with respect to

An exact result minimizes the Chapter 12 objective over the derivations admitted
by its cycle policy and the equalities present in its e-graph snapshot. Each
qualification can change the returned term.

## Optimal over the e-graph, not over the theory

Chapter 11's containment example asserts
`add(a,b) = c` and `add(a,b,d) = n`. The AC theory entails
`add(c,d) = n`, but plain congruence does not derive it. Chapter 16 adds only
this query to that example:

```lisp
{{#include ../examples/16-au-plain.egg:ac-completion-query}}
```

The same program is executed in three completion modes:

| mode | result |
| --- | --- |
| plain | `:size 5 :cr 0.7500` -- `(g (Variants n (add c d)))` |
| eager | `:size 2 :cr 0.0000` -- `(g n)` |
| lazy | `:size 5 :cr 0.7500` -- identical to plain |

The size-two `checkau` bound deliberately fails in the plain and lazy fixtures
and succeeds in the eager fixture.

Plain mode reports an exact optimum over its snapshot. The snapshot lacks one
AC consequence, so it contains a disagreement where the theory does not. Eager
completion adds that equality before the snapshot is taken, and the
disagreement disappears.

## Lazy completion does not help the anti-unifier

The lazy result has size 5, the same as plain, rather than the eager result's
size 2. As Chapter 11 explains, lazy completion is scoped to equality and
disequality checks. Anti-unification reads the restored graph.

When an AU query must observe consequences of asserted AC equations, run Semper
with `--derive-ac-eqs`. Lazy completion is suitable for isolated equality
questions, not for preparing an anti-unification snapshot.

## Optimal within the cycle policy

Chapter 14's cyclic fixture measures size 9 under the default `sides` policy and
size 8 under `pair`. Both outputs say `:completion exact`; they optimize
different admitted derivations. A quoted cyclic result must therefore name its
cycle policy. Chapter 14 defines those policies and gives the measured terms.

## Optimal under this objective

The objective is a definition of which valid anti-unifier is best. It does not
encode domain terminology or a reader's preferred presentation.

In the next fixture, the two initial classes contain only domain-facing
`Approved` and `Rejected` terms. Each class is then merged with an equivalent
`Wire` representation:

```lisp
{{#include ../examples/16-objective-readability.egg:objective-readability}}
```

Before the unions, the only result is the explicit domain distinction:

```text
(anti-unify :size 6 :cr 1.0000 :completion exact
  (Variants (Approved common false) (Rejected common true)))
```

After the unions, the solver finds a smaller common representation:

```text
(anti-unify :size 4 :cr 0.3333 :completion exact
  (Wire common (Variants false true)))
```

The size-four result is optimal under `(size, variant_mass)`, but the size-six
result preserves the labels `Approved` and `Rejected`. Applications that
prefer those labels need a different output objective or a presentation layer;
the exact certificate does not claim readability.

## What is argued rather than proved

The `au-verus` crate proves properties of the lexicographic objective and a
recurrence lower bound. It does not verify the production Rust solver end to
end. A small exhaustive oracle supplies finite evidence for pair-mode Exact on
enumerable fixtures.

Pair-cycle erasure and global optimality remain prose arguments supported by
regressions. Hybrid calls have finite differential evidence. Chapters 14 and 15
state the operational claims, and
[`19-anti-unification.md`, section 9.6](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md)
states the current proof boundary.
