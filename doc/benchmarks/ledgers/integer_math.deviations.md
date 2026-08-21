# integer_math: deviation ledger

Source: `egglog/tests/integer_math.egg` at 7b1adf2. Benchmark 5 of the
intersection set, selected by the plan for i64 shifts and division and for the
thirteen universe-relation rules that were expected to be the only thing stripped.

Files: `integer_math.egglog.egg`, `integer_math.rules.egg`,
`integer_math.native.egg`, this ledger.

**Read the scoping section before the numbers.** This benchmark is shipped as a
scoped column: the same reduced program runs in all three configurations, and it
is 19% of the original's size. Do not compare its timings to anything upstream
calls integer_math.

## Scoping, applied to all three configurations

Four groups of declarations and rules are removed. Each is removed from the
egglog program too, so the three configurations are the same problem.

### 1. The `MathU` universe relation and its 13 grounding rules

The plan's expected strip, and the largest one by consequence. `MathU` is
egglog's groundedness workaround, not part of the problem: but two rules use it
for more than grounding:

```
(rule ((MathU a) (!= a (Const 0))) ((union a (Add a (Const 0)))))
(rule ((MathU a) (!= a (Const 1))) ((union a (Mul a (Const 1)))))
```

These introduce an `Add`-with-zero and a `Mul`-with-one for every node in the
e-graph and are what makes the benchmark grow. They cannot survive the strip: they
need a "for every node" trigger, which is what the universe relation is.

**Measured consequence, on egglog, at the original `(run 4)`:** term nodes go from
537 to 100, an 81% reduction. (Original, excluding the relation tables:
Add 331, Mul 190, Const 6, LShift 2, Not 2, Div 1, Pow 1, Sub 1, Var 3. Scoped:
Add 43, Mul 42, Const 6, Var 3, Not 2, Div 1, LShift 1, Pow 1, Sub 1.) This is
the number that makes the column scoped rather than merely adjusted.

### 2. The `evals-to` relation and its two rules

```
(relation evals-to (Math i64))
(rule ((evals-to x vx)) ((union x (Const vx))))
(rule ((= e (Const c))) ((evals-to e c)))
```

Removed with no consequence, and the argument is short enough to check: the only
producer of an `evals-to` fact is the second rule, which fires on a node `e` that
*is* `(Const c)`; the only consumer is the first, which then unions `e` with
`(Const c)`. Every union it can perform is a node with itself. The pair is a
no-op.

### 3. The `is-not-zero` relation and the five rules guarded by it or by a
primitive disequality

Removed: `(rewrite (Div (Const a) (Const b)) (Const (/ a b)) :when ((!= 0 b)))`,
`(rewrite (Div a a) (Const 1) :when ((is-not-zero a)))`,
`(rewrite (Mul (Pow a b) (Pow a c)) (Pow a (Add b c)) :when (…))`,
`(rewrite (Pow x (Const 0)) (Const 1) :when (…))`,
`(rewrite (Pow x (Const -1)) (Div (Const 1) x) :when (…))`.

Two independent reasons. `is-not-zero` is a relation, and it is derived from
`MathU`, so it goes with it. And our `:when` takes patterns only: no
disequality, no primitive predicate: so neither `(is-not-zero a)` nor
`(!= 0 b)` has anything to compile to. Keeping these rules unguarded is not an
option: each is unsound at zero (`(Div a a) = 1`, `(Pow x 0) = 1`,
`(Pow x -1) = (Div 1 x)`), which is exactly what the guard is for.

The goal does not need them; see the cross-check.

### 4. The three bitwise constant folds

Removed: the `RShift`, `LShift` and `Not` folds, because our i64 primitive set has
`+ - * / %`, the wrapping and saturating variants, and the comparisons, but no
bitwise operators.

**Measured consequence: none.** At `(run 4)` all three rules have zero matches on
this program and the node count is identical with and without them (100 either
way, verified on egglog). The two shift-*introduction* rewrites
`(Mul x (Pow (Const 2) y)) → (LShift x y)` and
`(Div x (Pow (Const 2) y)) → (RShift x y)` are kept, so the shift structure the
plan selected this benchmark for is still exercised; what is not exercised is
folding a shift to a literal, which the original never does either.

## Deviations in the rules translation

1. **Literal-op qualification.** `(+ a b)` becomes `(i64::+ a b)`, and likewise
   `-` and `*`. Pure renaming.
2. **Goal names.** `$start-expr` → `startexpr`, `$equiv-expr` → `equivexpr`;
   `$` and `-` are outside our identifier class. Pure renaming.

Nothing else changes: the 22 remaining rewrites, both goal terms, `(run 4)` and
the check are copied as written.

## Deviations in the native translation

`Add` and `Mul` are AC: the source has commutativity and associativity rules for
both: so both are declared variadic `:assoc-comm` and the four A/C rules are
deleted. AC flattening and singleton collapse are both correct in our engine
(unlike `:assoc`; see `calc.deviations.md`), so no workaround is needed.

Seven rules are restated n-ary, because a binary pattern is exact against a flat
node and would stop firing at arity 3 or more:

| theirs | ours, native |
|---|---|
| `(rewrite (Add (Const a) (Const b)) (Const (+ a b)))` | `(rewrite (Add (Const a) (Const b) ..rest) (Add (Const (i64::+ a b)) ..rest))` |
| `(rewrite (Mul (Const a) (Const b)) (Const (* a b)))` | `(rewrite (Mul (Const a) (Const b) ..rest) (Mul (Const (i64::* a b)) ..rest))` |
| `(rewrite (Add a (Const 0)) a)` | `(rewrite (Add (Const 0) ..rest) (Add ..rest))` |
| `(rewrite (Mul a (Const 0)) (Const 0))` | `(rewrite (Mul (Const 0) ..rest) (Const 0))` |
| `(rewrite (Mul a (Const 1)) a)` | `(rewrite (Mul (Const 1) ..rest) (Mul ..rest))` |
| `(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))` | `(rewrite (Mul (Add b ..s) ..rest) (Add (Mul b ..rest) (Mul (Add ..s) ..rest)))` |
| `(rewrite (Add (Mul a b) (Mul a c)) (Mul a (Add b c)))` | `(rewrite (Add (Mul a ..p) (Mul a ..q) ..rest) (Add (Mul a (Add (Mul ..p) (Mul ..q))) ..rest))` |

The distribution and factoring forms are the ones already used and justified in
`math-microbenchmark.native.egg`. One more is n-ary here and is not in that file:

| `(rewrite (Mul x (Pow (Const 2) y)) (LShift x y))` | `(rewrite (Mul (Pow (Const 2) y) ..rest) (LShift (Mul ..rest) y))` |

The power-of-two factor may sit anywhere in a flattened product, and the rest of
the product is the shifted operand. `(Div x (Pow (Const 2) y)) → (RShift x y)`
needs no restatement: `Div` is an ordinary binary constructor.

## Cross-check

`(check (= startexpr equivexpr))` passes in all three configurations, unchanged
from the original. Its derivation uses only unguarded rules , 
`(Mul x (Pow (Const 2) y)) → (LShift x y)`, `(Sub a a) → (Const 0)`,
`(Add a (Const 0)) → a`, `(Not (Not x)) → x`, `(Mul a (Const 1)) → a`: which is
why the scoping does not touch it.

Smoke pass (1 run, 0 warmups: not a timing result):

| config | nodes | classes | iterations |
|---|---|---|---|
| egglog | 100 |: | 4 |
| ours, rules, naive | 116 | 49 | 4 |
| ours, rules, semi-naive | 117 | 50 | 4 |
| ours, native, naive | 34 | 24 | 4 |
| ours, native, semi-naive | 34 | 24 | 4 |

Native AC holds the same check at 29% of the rules encoding's nodes. Ours-vs-theirs
node counts are not comparable (`methodology.md` section 3); the 116 includes 9
interned literals that egglog never counts.

## Multiplicity variants

Pattern elements bind distinct children and take each child's whole
multiplicity, so the n-ary lift of a binary rule cannot match a repeated
child (`Add{Const4 : 2}`, `Add{(Mul a p) : 2}`). Each affected rule in
`integer_math.native.egg` carries its multiplicity variant, k-generic where
the count enters arithmetic: both constant folds (`k*a` via `i64::*`, `a^k`
via `i64::pow`), the factoring rule (`k` reinserted as a `Const` factor),
the distributivity rule (one copy distributed, `k-1` kept through an RHS
multiplicity expression), and the LShift rule (`(2^y)^k = 2^(y*k)`). The
identity and annihilator rules need no variants here: the fold variants
normalize a repeated `Const` to a single one, and the identities then fire.

Every count is identical to the campaign tables under both strategies
(34 nodes / 24 classes / 4 iterations): the variants fire zero times on
this workload. Fixtures: `egraph/tests/egg/ac_multiplicity_variant_gap.egg`
(the base-rule gap), `ac_multiplicity_variant.egg` (the variants),
`rhs_mult_expr.egg` (the keep-k-1 shape).
