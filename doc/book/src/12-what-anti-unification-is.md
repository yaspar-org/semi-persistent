# What anti-unification is

> Chapter contents: the definition and its dual, how this engine reports a
> disagreement, the two commands and their options, every field of the printed
> output, and the objective the solvers minimize.
>
> Carry over: `v1-draft/05-anti-unification.md` is this chapter, minus its "What
> makes this version different" section, whose two halves now belong in chapter 13
> (modulo the algebra) and chapter 16 (over e-classes, not syntax). Its output-field
> table and its `:cr` explanation are accurate and measured: keep them.
>
> Example: the four-node `(f a (Variants a b))` program from the v1 draft, as
> `examples/12-first-au.egg`.
>
> Sources: design `19-anti-unification.md` sections 1 and 2.5.

## The definition

> Unification finds the most general term both operands specialize to.
> Anti-unification finds the most specific term both operands are specializations of.
> Name the shared part the skeleton and the placeholders the disagreements. Give
> `f(a,b)` against `f(a,c)` and its anti-unifier.

## How a disagreement is reported

> A `Variants` node carrying both sides, rather than a bare placeholder, because the
> two candidate answers are what a reader of the output needs. Show the smallest
> program and its real output.

## The commands

> `antiunify` prints, `checkau` prints and asserts a size bound. The option grammar
> as a `text` block. State that every example in the book uses `checkau`, since that
> is what makes an example a regression test, and that both accept inline terms or
> `let`-bound names.

## Reading the output

> Keep the v1 table: `:size`, `:cr`, `:completion`. Keep the two points that a reader
> gets wrong otherwise: a `Variants` node is priced at the full size of both its
> sides, so hiding structure in a variant does not make a result look smaller, and
> `:cr` runs low-is-better with 0 meaning full agreement and 1 the no-sharing
> endpoint. Keep the note that over e-classes `:cr` is not clamped and can exceed 1,
> with the reason.

## The objective

> `(size, variant_mass)` lexicographic, lower better on both, `variant_mass` not
> printed. State what the tie-break buys: between two results of equal size it prefers
> the one holding less of that size inside variant nodes, which is the one with more
> shared skeleton. Cite design 2.5 and its normalization requirements rather than
> restating them.

## What it does not do

> Keep the v1 section. Anti-unification localizes disagreement and does not
> adjudicate it. Deciding which side is right needs a type checker, a schema, a test
> or a person. Forward reference Part IV, which is entirely about what to do with a
> located disagreement.
