# combinators: deviation ledger

Source: `egglog/tests/web-demo/combinators.egg` at 7b1adf2. Lambda-calculus
substitution through S/K/I combinators over a dual representation (Expr and
CExpr) linked by conversion rules. The benchmark's value in this set is
extraction under extreme cost asymmetry: `:cost 100` on `Var`, `10000` on the
uneliminated combinator forms, `1000000` on the `Comb` conversion wrapper.

Files: `combinators.egglog.egg` (theirs, verbatim), `combinators.rules.egg`
(ours), this ledger. No native column: no operator in the program is
associative or commutative, so there is nothing for native canonization to
canonize and the two encodings would be the same program.

## Deviations

1. **Identifier renaming.** `$T`/`$F`/`$CT`/`$CF`/`$CIf`/`$CAdd`/`$S`/`$K`/
   `$I`/`$test` become `tt`/`ff`/`ctt`/`cff`/`cif`/`cadd`/`scomb`/`kcomb`/
   `icomb`/`test`. Pure renaming.
2. **Literal-op qualification.** `(+ n m)` becomes `(i64::+ n m)`; the
   `(!= v1 v2)` guard becomes `(String::!= v1 v2)`. Pure renaming.
3. **Global-only root bindings bound through their constructors.** The source
   writes four rules of the shape `(rule ((= x $T)) ...)`, whose only
   left-hand-side atom equates a variable with a global. Our compiler emits a
   plan with no binding step for that shape and the matcher panics (engine
   defect, reported; four-line reproduction in the report). The translation
   binds through the nullary constructor instead: `(rule ((= x (TConst))) ...)`.
   The class scanned is the global's class, because the global is `(let tt
   (TConst))` and every `TConst` node is in it, so the match set is the same.
4. `(print-size)` appended for the harness; the source prints nothing.

## Validation

The check `(= test (N 3))` passes on both engines, under both of our
strategies. Both engines extract the identical term for `(Comb test)`:
`(CApp (CApp (CAddConst) (CN 1)) (CN 2))`, which is the substantive
cross-check for the cost model (the extractor must route around the
`:cost 1000000` wrapper and the `:cost 10000` unconverted forms). Node count
ours: 635 at `(run 11)`.

Both programs end with `(print-stats :file "...")` so the harness can read node, class, and iteration counts; egglog's `no-messages` timing runs suppress the terminal output either way.
