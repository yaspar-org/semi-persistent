# Anti-unification

This chapter defines anti-unification, states the two ways this engine's version
differs from the textbook one, gives the two commands and their options, reads
each field of the printed output, compares the two solvers, and states what
anti-unification does not do.

Unification takes two terms and finds the most general term that both can be
specialized to. Anti-unification is the dual: it takes two terms and finds the
**most specific** term that both are specializations of. The shared part is the
**skeleton** and the placeholders are the disagreements.

For `f(a, b)` and `f(a, c)` the anti-unifier is `f(a, X)`.

This engine reports the placeholder as a `Variants` node carrying both sides,
because the two candidate answers are the useful part:

```lisp
(sort E)
(function a () E)
(function b () E)
(function f (E E) E)
(antiunify (f (a) (a)) (f (a) (b)) :algorithm exact)
```

```text
(anti-unify :size 4 :cr 0.3333 :completion exact
  (f a (Variants a b)))
```

## What makes this version different

**It runs over the e-graph, not over syntax.** The operands are e-classes, not
terms. So the search sees everything saturation has proved equal, and two
candidates that were written differently but proved equal have no disagreement
to report. A domain rewrite fired before the query changes the answer:
[chapter 6](06-worked-example.md) shows one doing exactly that, collapsing a
reported difference once the engine knows that the approved regions are exactly
two named ones.

**It works modulo the declared theory.** An AC operator's children are a sorted
multiset, so conjunct order is not a difference. An ACI operator's children are
a set, so repetition is not either. An operator with a unit can align a 3-child
node against a 2-child node. None of this is search: it is the representation,
so it costs nothing at query time.

## The commands

```text
(antiunify t1 t2 au_option*)
(checkau   t1 t2 (au_option | :max_size int)*)

au_option = :algorithm (exact | uct)
          | :cycles (sides | sides-current | pair)
          | :playouts int
```

`antiunify` prints the result. `checkau` prints it and additionally asserts
`size <= :max_size`, failing the program if not. Use `checkau` in any file you
intend to keep: it turns the example into a regression test, and every example
in this book uses it.

Both accept terms inline or as `let`-bound names.

## Reading the output

```text
(anti-unify :size 61 :cr 0.1864 :completion exact
  ...)
```

| field | meaning |
| --- | --- |
| `:size` | node count of the returned term. A `Variants` node is priced at the full size of both its sides, not as a single placeholder, so hiding structure inside a variant does not make a result look smaller |
| `:cr` | compression ratio, `(size(t) - a) / b` where `a` and `b` are the smaller and larger of the two operands' minimal representative sizes |
| `:completion` | `exact` if the result is certified optimal, otherwise the search stopped at its budget |

`:cr` runs from 0 to 1 for a fixed pair of ground terms, and **lower is
better**: 0 means the result is no larger than the smaller operand, so the two
agree completely, and 1 is the no-sharing endpoint where the result is a single
`Variants` node holding both operands whole. Over e-classes it is not clamped
and can exceed 1, because the denominator uses independently smallest
representatives while the search may use larger ones.

The solvers minimize `(size, variant_mass)` lexicographically, lower being
better on both. `variant_mass` is not printed. It breaks ties between two
results of equal size in favour of the one holding less of that size inside its
variant nodes, which is the one with more shared skeleton.

## Which solver

| `:algorithm` | what it is | when |
| --- | --- | --- |
| `exact` | dynamic programming over the class-pair graph, returns a certified optimum | the default choice for anything you will publish or assert |
| `uct` | Monte-Carlo graph search with a playout budget | large inputs where exact does not finish |

`exact` is what every example in this book uses, and on problems the size of a
policy it is also the faster of the two. `uct` exists for inputs where the pair
graph is too large; it is an anytime algorithm, so it returns its best result at
whatever budget `:playouts` allows and reports `:completion` accordingly.

There is also a hybrid mode that runs graph search and hands sufficiently small
subproblems to the exact solver. It is not reachable from `:algorithm`, only
from the Rust API, which is why the corpus in
[chapter 9](09-corpus.md) ships its own runner.

The `:cycles` option selects how the search handles cycles in the e-graph, which
changes what derivations are admissible and therefore can change the answer.
`sides` is the default. The three policies are specified in
[design chapter 19](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).

## What it does not do

Anti-unification localizes disagreement. It does not adjudicate it. A
`Variants` node says "your two candidates say different things here, and here is
what each of them says". Deciding which side is correct requires something else:
a type checker, a schema, a test, or a person. Chapter 7 works through an
example where one decision is settled mechanically and the other is not
settleable by any tool, because it depends on what the original sentence meant.
