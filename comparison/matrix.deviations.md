# matrix: deviation ledger

Source: `egglog/tests/web-demo/matrix.egg` at 7b1adf2. Benchmark 7 of the intersection
set, selected for one property: mixed AC and A-only operators in one signature. `Times`
over `Dim` has both an associativity pair and a commutativity rule (AC); `MMul` and `Kron`
over `MExpr` have associativity in both directions and no commutativity (A-only).

Files: `matrix.egglog.egg` (theirs), `matrix.rules.egg` (ours, A and C as explicit rewrite
rules), `matrix.native.egg` (ours, native AC on `Times` only), this ledger.

**Dropped 2026-08-16, translated 2026-08-17.** The drop was on a missing pattern-language
feature, a root-binding pattern form; that feature landed in commit 93d698d and the
benchmark translates with its conditional rewrite intact. The previous version of this
file, which argued the drop, is in the history of commit c2558c7; do not cite it as
current.

## What the guard is and how it is written

The benchmark's subject is one conditional rewrite whose guard is an equality between two
*derived* terms: the e-class of `(ncols A)` must be the e-class of `(nrows C)`.

```
(rewrite (MMul (Kron A B) (Kron C D))
    (Kron (MMul A C) (MMul B D))
    :when
        ((= (ncols A) (nrows C))
        (= (ncols B) (nrows D))))
```

Ours names the shared root explicitly. Each conjunct binds one pattern's root e-class, and
the repeated variable is what requires the two to be one class rather than two:

```
(rewrite (MMul (Kron a b) (Kron c d))
    (Kron (MMul a c) (MMul b d))
    :when
        ((= p (ncols a)) (= p (nrows c))
         (= q (ncols b)) (= q (nrows d))))
```

Both of the benchmark's assertions turn on this rule: `(check (= $ex1 $simple_ex1))`
derives through it and through nothing else, and the `fail` check exists to show that the
guard blocks the analogous term whose dimensions do not line up. Dropping the rule would
leave fifteen unconditional rules and no assertions.

## Adjustments on our side only

**`$`-prefixed names are renamed**, and renamed away from the rule variables. `$A` becomes
`matA` and `$n` becomes `dimN`, because `A` and `n` are pattern variables in the rules
above and our globals share one namespace with them. Mechanical.

**`(fail (check (= a b)))` becomes `(check (!= a b))`.** We have no `fail` wrapper; the
`!=` form asserts what the wrapped check was there to deny, that the two classes are
distinct. Both forms build their terms before comparing.

**Namespaced primitive.** `(* i j)` becomes `(i64::* i j)`.

**The two demand rules drop the root they never read.** Theirs writes
`(rule ((= e (MMul A B))) …)` and never mentions `e`; ours writes
`(rule ((MMul a b)) …)`.
Exact, and it keeps those two rules delta-restricted: a rule carrying a constraint
between two atoms' node variables is matched against the whole graph every round
(chapter 18), so
binding a root nothing reads would have cost the native column six semi-naive iterations,
measured at 10 against 4.

## The native configuration, and what it does not cover

`Times` is declared `(Times Dim :assoc-comm)`, its two associativity rewrites and its
commutativity rewrite are deleted, and its constant fold is restated n-ary:
`(rewrite (Times (Lit i) (Lit j) ..rest) (Times (Lit (i64::* i j)) ..rest))`.

**`MMul` and `Kron` keep their four associativity rewrites.** They are the A-only half
of the signature, which is the property this benchmark was selected for, so this is the
column's limitation and not a convenience.

The n-ary restatement is writable as of commit e998295, which gave `:assoc` operators the
flattened-sequence normal form: `(MMul a ..rest)`, `(MMul ..pre (Id n) ..suf)` and the
rest all rely on a one-element application denoting its argument, and it now does. What
blocks the column is a matcher defect the restatement reaches. With `MMul` and `Kron`
declared `:assoc` and all eight rules that mention them restated, the guarded Kron/MMul
rewrite panics:

```
thread 'main' panicked at egraph/src/ematch.rs:229:29:
called `Option::unwrap()` on a `None` value
```

`Match::get` through `bucket_in`'s `IndexLookup::ByRepr` arm: the scheduler emitted a
re-join keyed on a variable that is not bound when the join runs. It needs the guard
(deleting the `:when` clause, and nothing else, makes the same program run) and it needs
eight of the twelve rules at once; each rule alone is clean, each pair is clean, and no
smaller synthetic reproduces it. Reported rather than chased, because it is a matcher
defect and this pass owns `comparison/`.

Revisit when that is fixed: the AC half of this column needs no change and the eight
n-ary restatements are mechanical.

## Validated

Both checks and the negative check pass in every configuration, on both engines, at the
source's `(run 20)` and `(run 10)`. Both engines exit non-zero on a failed check.

| configuration | nodes | classes | iterations |
|---|---|---|---|
| egglog | 53 | | 13 |
| ours, rules, naive | 92 | 25 | 10 |
| ours, rules, semi-naive | 91 | 25 | 4 |
| ours, native, naive | 91 | 25 | 10 |
| ours, native, semi-naive | 90 | 25 | 4 |

The guarded rule is the reason commit 4258fa4 exists: under semi-naive delta restriction
it never fired, at the source's budget of 20 and at 60, because the merge that makes its
two roots equal changes no node's tuple and so appears in no variant's delta. A rule
carrying such a constraint is now matched against the whole graph every round. Without
that, both of this benchmark's assertions failed under `--use-semi-naive` and passed
under naive matching, which is how the defect was found.
