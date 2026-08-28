# Your first program

This chapter walks one complete program command by command: the sort and operator
declarations, the two rewrite rules, the term insertion, the bounded saturation
run, the check, and what the closing node count counts.

Here is the program. It is
[`egraph/examples/basic.egg`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/examples/basic.egg),
and the test suite runs it.

```lisp
{{#include ../../../egraph/examples/basic.egg}}
```

```bash
target/release/semi-persistent egraph/examples/basic.egg
```

```text
ok — 14 nodes
```

## Sorts and operators

Every term has a sort. `(datatype Math ...)` declares the sort `Math` and one
operator per variant, so it is shorthand for:

```lisp
(sort Math)
(constructor Num (IBig) Math)
(constructor Add (Math Math) Math)
(constructor Mul (Math Math) Math)
```

`IBig` is the arbitrary-precision integer sort. It is one of the concrete sorts
the literal model registers automatically (`IBig`, `RBig`, `bool`, `String`,
and the machine integer types under `--types machine`), so you never declare
it. Everything else you declare.

`(function ...)` and `(constructor ...)` declare the same thing as far as
matching and congruence are concerned. `constructor` additionally marks the
operator a term former, which affects extraction only: see
[chapter 10](10-commands.md).

## Rewrite rules

```lisp
(rewrite (Add a b) (Add b a))
(rewrite (Add (Num x) (Num y)) (Num (IBig::+ x y)))
```

Lowercase identifiers in a pattern that are not declared operators are pattern
variables. The first rule says addition commutes. The second folds two integer
literals, calling the builtin `IBig::+` on the bound literal values.

A `rewrite` is one-directional: it adds the right side to the left side's
e-class. `(birewrite l r)` adds rules in both directions.

Note what the first rule is doing, and what chapter 3 replaces it with.
Declaring commutativity as a rewrite means the engine represents both
orderings as separate e-nodes and proves them equal. Declaring the operator
`:comm` instead means there is only one e-node, and the question never arises.

## Inserting a term

```lisp
(let expr (Mul (Num 2) (Add (Num 1) (Num 3))))
```

`let` builds the term, inserts it into the e-graph, and binds the name to its
e-class. The name is then usable in later commands, which is how queries refer
to terms. Commands that take terms also accept them inline, so
`(antiunify (f (a) (a)) (f (a) (b)))` is legal; naming the two candidates is a
readability choice, and the one place it becomes a requirement is the corpus
runner of [chapter 9](09-corpus.md).

## Saturation

```lisp
(run 10)
```

Run up to ten rounds of rule application, stopping early if a round adds
nothing new. `(run 10 :until (= a b))` stops as soon as the two terms are
proved equal.

## Checking

```lisp
(check (= expr (Num 8)))
```

Assert that the two terms are in the same e-class. If they are not, the program
fails with `error: check failed: terms are not equal` and a nonzero exit
status. `(check (!= a b))` asserts the opposite, and is weaker than it looks:
it passes when the engine's search did not derive equality, which is not the
same as a proof that the two terms are unequal. Chapter 12 says more about
that.

## What "14 nodes" counts

The e-graph ended with 14 e-nodes: the three input literals, the folded results,
the `Add` and `Mul` applications, and the commuted variants the first two rules
produced. The count is a progress signal, and nothing in the engine depends on
it.
