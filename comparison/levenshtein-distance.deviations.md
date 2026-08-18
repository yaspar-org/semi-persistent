# levenshtein-distance: deviation ledger

Source: `egglog/tests/web-demo/levenshtein-distance.egg` at 7b1adf2.
Demand-driven edit distance: strings are `Cons` chains of one-character
`String` literals, and `EditDist` demand splits on head equality with a
string-disequality guard and folds through `Min`/`Add` constant rules over
9-character inputs.

Files: `levenshtein-distance.egglog.egg` (theirs, verbatim),
`levenshtein-distance.rules.egg` (ours), this ledger. No native column: no
operator is associative or commutative.

## Deviations

1. **Identifier renaming and literal-op qualification.** Sigils and hyphens
   dropped; `+`/`min` become `i64::` forms; the `(!= head1 head2)` guard
   becomes `(String::!= head1 head2)`.
2. **The three-way min folds in two steps.** A primitive application takes
   plain variables, so the source's nested `(min (min a b) c)` stages through
   a helper constructor: `(Min (Num a) (Num b) c)` folds to
   `(Min2 (Num (i64::min a b)) c)` and `Min2` folds to the result. Same
   value, one extra materialized node per fold.
3. **The `Unwrap` table dropped and its extracts redirected.** The source's
   `:no-merge` function mirrors `(Num n)` classes into an i64 table only so
   `extract` prints a bare integer; we extract the `expr` class directly and
   the checks are unchanged.
4. **Global-only base cases bound through the constructor.**
   `(Length $Empty)` and the two `(EditDist $Empty s)` orientations scan
   `(EmptyConst)`.
5. `(print-size)` appended for the harness.

## Validation

All three checks pass on both engines, under both of our strategies
(distances 3, 5, 5). Node count ours at `(run 100)`: 511 under both
strategies.
