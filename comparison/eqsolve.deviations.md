# eqsolve: dropped, with reason

Source: `egglog/tests/web-demo/eqsolve.egg` at 7b1adf2. Benchmark 10 of the
intersection set, selected for extraction-path coverage: it solves two small
linear systems and the result is read out with `(extract …)` rather than
asserted by a check alone.

**Not translated.** No `.egg` files are shipped for it.

## Why

Most of the program translates. Three of its four `(rule …)` forms bind a
variable to a pattern's root e-class and then use it only in the action, so
substituting the pattern for the variable is exact:

| theirs | ours |
|---|---|
| `(rule ((= (Add x y) z)) ((union (Add z (Neg y)) x)))` | `(rule ((Add x y)) ((union (Add (Add x y) (Neg y)) x)))` |
| `(rule ((= x (Var v))) ((union (Mul (Num 1) x) x)))` | `(rule ((Var v)) ((union (Mul (Num 1) (Var v)) (Var v))))` |
| `(rule ((= x (Add x1 x2))) ((union (Mul (Num 1) x) x)))` | `(rule ((Add x1 x2)) ((union (Mul (Num 1) (Add x1 x2)) (Add x1 x2))))` |

The fourth does not:

```
(rule ((= (Mul (Num x) y) (Num z))
       (= (% z x) 0))
      ((union y (Num (/ z x)))))
```

It needs two things we do not have, either of which alone is fatal:

1. Two patterns sharing a root e-class — `(Mul (Num x) y)` and `(Num z)` must be
   the *same* class. Our patterns cannot name a root, so a multi-pattern rule
   listing both is a cross product, not a join on the root. Same gap as `matrix`;
   the probe is in `matrix.deviations.md`.
2. A primitive divisibility guard, `(% z x) = 0`. Primitive operators are
   rejected in left-hand sides outright. Same gap as `bdd`; the probe is in
   `bdd.deviations.md`.

This is the rule that turns `3y = 12` into `y = 4`, so it is the one that
produces the benchmark's output. Measured, on egglog, at the original `(run 5)`:

| | extract `(Var "x")` | `(Var "y")` | `(Var "z")` | checks |
|---|---|---|---|---|
| as written | `(Num 5)` | `(Num 4)` | `(Num 2)` | 7 of 7 pass |
| rule removed | — | — | — | fails at check 3 |

Removing the rule fails `(check (= (Var "y") (Add (Add (Num 12) (Neg (Var "y"))) (Neg (Var "y")))))`
at the original budget, and raising the budget to `(run 9)` to try to recover it
does not terminate within 120 s — the rule is also what keeps the search finite,
by collapsing classes onto numerals instead of letting the `Add`/`Neg`
rearrangements expand. So there is no scoped version of this benchmark that both
terminates and asserts what it was chosen to assert, and none at all that
exercises the extraction path on the intended answers.

Dropped under the drop-don't-fudge rule (`methodology.md` section 5).

## Consequence for coverage

The intersection set loses its only extraction-path benchmark. Extraction is
still exercised by our own corpus but not head to head against egglog. Recovering
it needs the root-binding pattern form and primitive guards together; a
replacement exhibit built from our own extraction tests would not be a
comparison.
