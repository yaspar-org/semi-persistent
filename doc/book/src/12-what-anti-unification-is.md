# What anti-unification is

## The definition

Unification finds a most general substitution that makes two terms identical.
Anti-unification is the dual: it finds a most specific term of which both
operands are instances. The common operators form a **skeleton**, and the
positions where the operands differ are generalized.

## How a disagreement is reported

For `f(a,a)` and `f(a,b)`, the first child belongs to the skeleton and the
second child differs:

```lisp
{{#include ../examples/12-first-au.egg:first-au}}
```

The `antiunify` command prints:

```text
(anti-unify :size 4 :cr 0.3333 :completion exact
  (f a (Variants a b)))
```

Textbook anti-unification would usually put a fresh variable in that position.
Semper instead writes `(Variants a b)`. Selecting the first child of each
`Variants` node reconstructs the left operand; selecting the second reconstructs
the right operand. The output therefore carries the two readings that produced
each disagreement.

## The commands

`antiunify` computes and prints an anti-unifier. `checkau` computes the same
result and fails when its size exceeds `:max_size`; it prints no anti-unifier on
success. Its bound is an upper bound, so `:max_size 4` accepts any result of size
four or less.

Both commands accept inline terms or names introduced by `let`. Book examples
use `checkau` to make the measured size an executable regression. The
[`antiunify` and `checkau` command signatures](B-command-reference.md) are
collected in Annex B, and [Annex A](A-full-grammar.md) gives their complete
grammar. Chapters 14 and 15 define the algorithm and cycle options.

## Reading the output

| field | meaning |
| --- | --- |
| `:size` | Concrete-node count of the result. A `Variants` marker costs zero, but both of its complete children count, so placing structure inside it does not hide that structure from the objective. |
| `:cr` | Linear compression ratio against the smallest representatives of the two operand classes. Lower is better. |
| `:completion` | `exact` when the selected search space was exhausted, and `budget` when search stopped at its budget. |

If `a` and `b` are the smaller and larger operand sizes, respectively, the
reported ratio is

```text
(result_size - a) / b
```

For a fixed pair of ground terms, zero denotes full agreement and one is the
no-sharing result that holds both terms in one `Variants` node. The example's
result has size four over two size-three operands, hence
`(4 - 3) / 3 = 0.3333`.

For e-classes, `a` and `b` are the independently smallest representatives.
Search may choose larger represented terms to obtain a common skeleton, so
`:cr` is not clamped and can exceed one.

## The objective

Both solvers minimize `(size, variant_mass)` lexicographically. Size is compared
first. If two results have the same size, the solver chooses the one with fewer
concrete nodes below `Variants` nodes, leaving more of the result in the common
skeleton. `variant_mass` is not printed by the surface command.

The exact definitions and the separate floating-point reward used only for UCT
selection are in
[`19-anti-unification.md`, section 2.5](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).

## What it does not do

Anti-unification localizes a disagreement; it does not decide which side is
correct. That decision requires a type checker, a schema, a test, or a person.
Part IV uses the shared skeleton and its `Variants` nodes to direct that review.
