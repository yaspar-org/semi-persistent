# herbie: deviation ledger

Source: `egglog/tests/web-demo/herbie.egg` at 7b1adf2. Benchmark 3 of the
intersection set: part of Herbie's simplification layer, 180 rewrites over
`BigRat` with an interval analysis, run in fourteen `push`/`run`/`check`/`pop`
blocks.

Files: `herbie.egglog.egg`, `herbie.rules.egg`, `herbie.native.egg`,
`herbie-dropped.txt`, this ledger. `gen-herbie.py` regenerates the egglog and
rules programs and the dropped-form listing from the original;
`herbie.native.egg` is hand-derived and this ledger records its accounting.

**This is a scoped column**: the same reduced program runs in every
configuration, and its timings are not comparable to anything upstream calls
herbie.

## Scoping, applied to every configuration

`gen-herbie.py` removes 37 top-level forms and two test blocks. The listing
with every removed form verbatim is `herbie-dropped.txt`.

### 1. The interval lattice and the non-zero analysis (32 forms)

```
(function hi (Math) BigRat :merge (min old new))
(function lo (Math) BigRat :merge (max old new))
(relation non-zero (Math))
```

Three declarations, 15 rules that propagate the interval through the
operators, and 14 forms that mention `non-zero` (2 rules deriving it from the
interval, 12 rewrites guarded by it). None of it is in the intersection set:
we have no lattice functions with `:merge`, no `set` action, and no datalog
relations, so a relation guard has nothing to compile to. The strip is
applied to the egglog program as well, so neither side gets the analysis.

### 2. Five constant folds over unavailable primitives

`(Pow (Num a) (Num b))`, `(Log (Num a))`, `(Ceil (Num a))`, `(Floor (Num a))`,
`(Round (Num a))`. Our `RBig` primitives are `+ - * / neg abs min max`, the
comparisons, `from_int`, `scale`, and integer-exponent `pow`; rational-exponent
`pow`, `log`, `ceil`, `floor` and `round` are not among them. Two of the five
folds are additionally guarded by primitive definedness,
`:when ((= res (pow a b)))`, which succeeds only when the rational power
exists, and that partiality test is not expressible on our side.

### 3. Two test blocks

- **`$e10`**, `(Div (Mul x 3) x) = 3`. Provable only through the
  non-zero-gated `Div` rules. Measured: with the analysis stripped and this
  block kept, it is the single failing check out of fourteen.
- **`$e14`**, the golden-ratio identity. Needs the rational-exponent `pow`
  constant fold. Measured: with `$e10` also removed, it is the single
  remaining failing check.

Both were found by running the stripped program on egglog and reading which
checks failed, not by inspection.

### Counted consequence

| | original | scoped |
|---|---|---|
| `(rewrite ...)` | 180 | 163 (90.6%) |
| `(rule ...)` | 16 | 0 |
| push/run/check/pop blocks | 14 | 12 |
| checks | 14 | 12 |

## Deviations in the rules translation

Mechanical, all applied by `gen-herbie.py`:

1. **`BigRat` becomes `RBig`.**
2. **Rational literals.** `(bigrat (bigint N) (bigint D))` becomes `N/D`,
   our surface syntax for an `RBig` literal.
3. **Literal-op qualification.** `(+ a b)`, `(- a b)`, `(* a b)`, `(neg a)`,
   `(abs a)` become `RBig::`-qualified. `/` does not appear after the strip:
   the only rational division was in the non-zero-gated `Div` fold.
4. **Identifier renaming.** `$x` becomes `x`, with hyphens removed:
   `$r-zero` becomes `rzero`, `$neg-one` becomes `negone`. Pure renaming.
5. **Type groups.** Runs under `--types machine,bignum`: the datatype needs
   `RBig` from `bignum` and `String` from `machine`; the groups compose on
   the command line.

Nothing else changes: all 163 rewrites, all 12 blocks, all 12 checks, same
budgets.

## The native encoding

`herbie.native.egg` declares `Add` and `Mul` variadic `:assoc-comm` and
restates every rule that matched either operator against flattened multisets,
rule by rule, with the twelve checks as the oracle. Counts, each verifiable
by grep against the two files:

| | count |
|---|---|
| source rewrites (`herbie.rules.egg`) | 163 |
| native rewrites (`herbie.native.egg`) | 151 |
| A/C rules carried by the declarations | 6 |
| deleted as multiset tautologies | 2 |
| C-redundant pairs collapsed to one rule each | 12 pairs |
| multiplicity variants (`:k>=2` rules) | 10 |

The two tautologies are the nested difference-of-squares pair
`(Mul (Mul a b) (Mul a b)) <-> (Mul (Mul a a) (Mul b b))`: both sides flatten
to `{a:2, b:2}`, so the rules are contentless under native canonization, and
a mechanical lift would leave patterns that match nothing. The two cube-root
chains `(Mul (Mul c c) c)` / `(Mul c (Mul c c))` flatten to one multiset
`{Cbrt x : 3}` and are one `:3` rule, counted among the collapses. Squared
and cubed factors are multiset elements with multiplicity, so every
`(Mul t t)` subpattern is restated as `t:2` and `x*x*x` as `x:3`.

The multiplicity variants exist because pattern elements bind distinct
children: an n-ary lift of a binary rule cannot match a repeated child, so
each affected rule carries the variant that covers multiplicity 2 or more.
They are k-generic where the count enters arithmetic, through the
integer-to-rational lift: the `Num` folds as `k*a` (`RBig::scale`) and `a^k`
(`RBig::pow`), counting as `(Num (RBig::from_int k))` times the child (this
one rule also carries the source's `x + x` counting rule), and the `Neg`,
`Pow` and `exp` pairs through `RBig::from_int`. The remaining uncovered
multiplicities are parity-shaped, not count-shaped: `negone`, `Sqrt`, `Fabs`,
`Neg` and `Cbrt` beyond their written `:2`/`:3` forms need an even/odd split
the rule language does not carry. Every parity-shaped case is verified
latent: the twelve checks pass without them.

## Validation and measurement

All twelve checks pass on both engines, in every configuration, under both
of our saturation strategies. Campaign medians (`final/final-r3-tables.md`):
egglog 120.2 ms; ours rules 28.9 ms naive, 37.1 ms semi-naive; ours native
14.1 ms naive, 20.6 ms semi-naive.

Base-state counts after the last `(pop)` (not a work measurement; every
block's work is popped):

| config | nodes | classes | iterations |
|---|---|---|---|
| egglog | 6 | | 24 |
| ours, rules, either strategy | 11 | 11 | 1 |
| ours, native, either strategy | 11 | 11 | 1 |

Neither the node column nor the iteration column measures the blocks' work:
every block is inside `push`/`pop`, so the counts are the base state, and
egglog's stats file accumulates one entry per iteration across every
`(run ...)` while ours reports the last one only (24 against 1). Wall time
is the metric for this benchmark, as for `calc` and `until`.
