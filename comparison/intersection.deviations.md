# intersection: deviation ledger

Source: `egglog/tests/intersection.egg` at 7b1adf2. E-graph intersection as a
product construction: `(intersect x1 x2)` classes represent pairs, and one
rule with three root bindings closes the product under the unary constructor.
Its value in this set is the three-way root join and the negative check (an
equality present in only one factor must not survive the intersection).

Files: `intersection.egglog.egg` (theirs, verbatim), `intersection.rules.egg`
(ours), this ledger. No native column: no operator is associative or
commutative.

## Deviations

1. **Identifier renaming.** `$a1`..`$b3`, `$t1`..`$t3`, `$fb1` lose the
   sigil. Pure renaming.
2. **`(extract $t3 5)` becomes `(extract t3)`.** Their two-argument extract
   prints five variants; ours prints the best term. The extraction is
   illustrative; the two checks carry the validation.
3. `(print-size)` appended for the harness.

## Validation

Both checks pass on both engines, under both of our strategies: the
preserved equality `f(f(a3)) = f(f(b3))` and the non-equality
`f(a3) != f(b3)`. Node count ours at `(run 100)`: 28 under both strategies.
