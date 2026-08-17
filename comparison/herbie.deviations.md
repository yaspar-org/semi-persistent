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

## Native-AC dual: delivered (2026-08-17)

`herbie.native.egg` is the hand-derived dual: `Add` and `Mul` are declared
variadic `:assoc-comm` and every rule that matched either operator is restated
against flattened multisets, per-rule, with the twelve checks as the oracle.
The file is not generated; the record of each decision is this section plus
the file's comments. The accounting closes exactly against the 163 rewrites of
the rules configuration:

| bucket | count |
|---|---|
| A/C rules deleted (2 commutativity, 4 associativity) | 6 |
| deleted as multiset tautologies | 2 |
| C-redundant pairs collapsed to one native rule | 12 pairs |
| restated verbatim (no AC position) | 84 |
| lifted n-ary or reshaped to multiset form (`:2`/`:3` elements) | 59 |
| coincidence twins added | 9 |
| native rewrites total | 152 |

The two tautologies are the nested difference-of-squares pair
`(Mul (Mul a b) (Mul a b)) <-> (Mul (Mul a a) (Mul b b))`: both sides flatten
to `{a:2, b:2}`, so the rules are contentless under native canonization and a
mechanical lift would have left patterns that match nothing (the failure mode
the deferral predicted). The two cube-root chains
`(Mul (Mul c c) c)` / `(Mul c (Mul c c))` flatten to one multiset
`{Cbrt x : 3}` and are one `:3` rule, counted among the 12 collapses.

Squared and cubed factors are multiset elements with multiplicity, so every
`(Mul t t)` subpattern is restated as `t:2` (`sin`/`cos`/`cosh`/`sinh`
identities, square roots, `Fabs`, difference of squares) and `x*x*x` as `x:3`.
The nine twins cover repeated children where the source's binary patterns
match by positional coincidence: the two `Num` folds at `:2`, the counting
rule at `:3` (`three` is a global), the `Neg`-pair and `exp`-pair rules at
`:2`, `zero`/`one`/`negone` identity elements at `:k>=2`, and the `Mul`
annihilator at `:k>=2`. Residuals, verified latent by the oracle: a `Num`
fold at multiplicity k >= 3 (the multiplicity is an i64 and RBig arithmetic
cannot consume it), counting at k >= 4, and any rule that must keep k-1
copies of its matched child on the right-hand side (the language carries no
multiplicity arithmetic; see the language guide's caveat section).

**Validation: naive passes 12/12; semi-naive passes 11/12 and is blocked by an
engine defect, not by the translation.** Block 9 (`e9 = (Sub (Add x one) one)`
at `(run 4)`) needs 8 semi-naive rounds where naive needs 3, and the minimal
repro is independent of this file:

```
(rewrite (Sub x x) zero)
(rewrite (Add zero ..rest) (Add ..rest))
(let t (Add x (Sub one one)))
(run 2)
(check (= t x))        ; naive ok, semi-naive fails
```

Replace the rule-derived merge by a literal `(union (Sub one one) zero)` and
semi-naive passes: when a merge produced by a rule recanonizes a parent AC
node (the child class collapses into `zero`'s class, so the parent's multiset
gains `zero` as an element), the recanonized parent is not visible to the next
round's delta for the rule that binds that element. Same family as the
root-binding gap fixed in 4258fa4. The budget is not raised to hide the lag:
the file keeps the source's `(run 4)` and the semi-naive column is blocked
until the engine fix lands, at which point the twelve checks re-validate it.

Smoke pass (1 run, 0 warmups; same base-state and last-block caveats as the
rules table above; wall time is the benchmark's metric and every block is
sub-millisecond on both configurations):

| config | nodes | classes | iterations |
|---|---|---|---|
| ours, native, naive | 11 | 11 | 1 |
| ours, native, semi-naive | blocked (engine defect above) | | |

`repro-herbie-vanilla.egg` is not behind this file after all: surveyed at
7b1adf2 it is not herbie's simplify layer at 2.9x but a typed-lowering
unsoundness repro with no checks; `repro-herbie-vanilla.deviations.md` has
the corrected characterization and the drop.
