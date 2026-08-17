# herbie: deviation ledger

Source: `egglog/tests/web-demo/herbie.egg` at 7b1adf2. Benchmark 3 of the
intersection set: part of Herbie's simplification layer, 180 rewrites over
`BigRat` with an interval analysis, run in fourteen `push`/`run`/`check`/`pop`
blocks.

Files: `herbie.egglog.egg`, `herbie.rules.egg`, `herbie-dropped.txt`, this ledger.
`gen-herbie.py` regenerates the two programs and the dropped-form listing from
their original; it is the reproducible record of the strip.

**No native-AC dual.** Deferred, with reason, at the end of this file.

**Read the scoping section before the numbers.** This is a scoped column: the same
reduced program runs in both configurations.

## Correction to the plan's figures

`doc/egglog-comparison-plan.md` says 183 rewrites and fifteen push/run/check/pop
blocks. Counted at 7b1adf2 the file has **180** `(rewrite …)`, 16 `(rule …)` and
**14** blocks. The plan's earlier statement that herbie is out of the intersection
set entirely (its closing section, and `methodology.md` section 4's calc row)
turns out to be too strong: with the analysis stripped, 163 of the 180 rewrites
and 12 of the 14 blocks survive and both engines agree on all twelve checks.

## Scoping, applied to both configurations

`gen-herbie.py` removes 37 top-level forms and two test blocks. The listing with
every removed form verbatim is `herbie-dropped.txt`.

### 1. The interval lattice and the non-zero analysis (32 forms)

```
(function hi (Math) BigRat :merge (min old new))
(function lo (Math) BigRat :merge (max old new))
(relation non-zero (Math))
```

Three declarations, 15 rules that propagate the interval through the operators,
and 14 forms that mention `non-zero` (2 rules deriving it from the interval, 12
rewrites guarded by it). None of it is in the intersection set: we have no lattice
functions with `:merge`, no `set` action, no datalog relations, and our `:when`
takes patterns only, so a relation guard has nothing to compile to. The multi-fact
rules would also need the root-binding form `(= la (lo a))` that we lack
(see `matrix.deviations.md`).

This is the strip `methodology.md` section 4 anticipated. It is applied to the
egglog program as well, so neither side gets the analysis.

### 2. Five constant folds over unavailable primitives

`(Pow (Num a) (Num b))`, `(Log (Num a))`, `(Ceil (Num a))`, `(Floor (Num a))`,
`(Round (Num a))`. Our `RBig` primitive set is `+ - * / neg abs min max` and the
comparisons; `pow`, `log`, `ceil`, `floor` and `round` are not in it. Two of the
five are additionally guarded by primitive definedness —
`:when ((= res (pow a b)))`, which succeeds only when the rational power exists —
and that partiality test is not expressible on our side either.

### 3. Two test blocks

- **`$e10`**, `(Div (Mul x 3) x) = 3`. Provable only through the non-zero-gated
  `Div` rules. Measured: with the analysis stripped and this block kept, it is the
  single failing check out of fourteen.
- **`$e14`**, the golden-ratio identity. Needs the `pow` constant fold. Measured:
  with `$e10` also removed, it is the single remaining failing check.

Both were found by running the stripped program on egglog and reading which checks
failed, not by inspection.

### Counted consequence

| | original | scoped |
|---|---|---|
| `(rewrite …)` | 180 | 163 (90.6%) |
| `(rule …)` | 16 | 0 |
| push/run/check/pop blocks | 14 | 12 |
| checks | 14 | 12 |

## Deviations in the rules translation

Mechanical, all applied by `gen-herbie.py`:

1. **`BigRat` becomes `RBig`.**
2. **Rational literals.** `(bigrat (bigint N) (bigint D))` becomes `N/D`, which is
   our surface syntax for an `RBig` literal.
3. **Literal-op qualification.** `(+ a b)`, `(- a b)`, `(* a b)`, `(neg a)`,
   `(abs a)` become `RBig::`-qualified. `/` does not appear after the strip — the
   only rational division was in the non-zero-gated `Div` fold.
4. **Identifier renaming.** `$x` → `x`, with hyphens removed: `$r-zero` → `rzero`,
   `$neg-one` → `negone`. Pure renaming.
5. **Type groups.** Runs under `--types machine,bignum`, not `machine` alone: the
   datatype needs `RBig` from `bignum` and `String` from `machine`. This is the
   first benchmark in the set to need two groups, and it answers the note in
   `README.md`'s protocol section that the `bignum` group has no `String` sort —
   the groups compose on the command line.

Nothing else changes: all 163 rewrites, all 12 blocks, all 12 checks, same budgets.

## Cross-check

All twelve checks pass on both engines. That is the substantive cross-check for
this benchmark: the same twelve equalities are derived from the same 163 rewrites
by both systems.

Smoke pass (1 run, 0 warmups — not a timing result):

| config | nodes | classes | iterations |
|---|---|---|---|
| egglog | 6 | — | 24 |
| ours, rules, naive | 11 | 11 | 1 |
| ours, rules, semi-naive | 11 | 11 | 1 |

Neither the node column nor the iteration column means anything here. Every block
is inside `push`/`pop`, so the node counts are the base state after the last
`(pop)`; and egglog's stats file accumulates one entry per iteration over all
twelve `(run …)` commands while ours reports the last one only. Wall time is the
metric for this benchmark. Same caveat as `calc` and `until`.

## Native-AC dual: deferred

`Add` and `Mul` are AC in this file (lines 188-201 give both commutativity and
both directions of associativity), so a native dual is meaningful and would be the
most valuable column in the set — 163 rewrites is by far the largest AC workload
we have.

It is not written, because a rule-for-rule native translation would be wrong
rather than merely weaker, and the correct one needs per-rule analysis at a scale
this pass could not validate. Two distinct transformations are involved:

1. Rules whose left-hand side has `Add` or `Mul` at the root need a rest variable
   added, the ordinary n-ary lifting used in `math-microbenchmark.native.egg`.
2. Rules with *nested* same-operator patterns need reshaping, not lifting, because
   the nesting does not survive flattening. `(rewrite (Mul (Mul a b) (Mul a b)) (Mul (Mul a a) (Mul b b)))`
   is the clear case: under AC both sides are the multiset `{a,a,b,b}`, so the
   rule and its converse are tautologies and must be deleted, not restated. A
   mechanical lift would leave a pattern that matches nothing.

Getting this wrong is silent — the rules simply stop firing — so the dual needs a
rule-by-rule pass with the twelve checks as the oracle. Recorded as the next piece
of work on this benchmark. `repro-herbie-vanilla.egg` (471 rewrites, same
signature and same analysis) is deferred behind it for the same reason: its strip
would be the same mechanical one, but its native dual is the same unfinished
analysis at 2.9x the size.
