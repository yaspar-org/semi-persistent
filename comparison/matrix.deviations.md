# matrix: deviation ledger

Source: `egglog/tests/web-demo/matrix.egg` at 7b1adf2. Benchmark 7 of the intersection
set, selected for one property: mixed AC and A-only operators in one signature. `Times`
over `Dim` has both an associativity pair and a commutativity rule (AC); `MMul` and `Kron`
over `MExpr` have associativity in both directions and no commutativity (A-only).

Files: `matrix.egglog.egg` (theirs), `matrix.rules.egg` (ours, A and C as explicit rewrite
rules), `matrix.native.egg` (ours, native AC on `Times` only), `matrix.native-A.egg`
(ours, native AC on `Times` and native A on `MMul` and `Kron`), this ledger.

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

## The two native configurations

`matrix.native.egg` is the AC-only column: `Times` is declared
`(Times Dim :assoc-comm)`, its two associativity rewrites and its commutativity rewrite
are deleted, and its constant fold is restated n-ary:
`(rewrite (Times (Lit i) (Lit j) ..rest) (Times (Lit (i64::* i j)) ..rest))`. `MMul` and
`Kron` keep their four associativity rewrites there.

`matrix.native-A.egg` is the column this benchmark was selected for: `MMul` and `Kron`
are declared `:assoc` as well, their four associativity rewrites are deleted, and the
eight rules that mention either are restated n-ary with rest variables, the guarded
Kron/MMul rewrite included. Both columns ship, because the pair isolates what A-only
declarations buy on a signature that also carries AC.

The n-ary restatement is writable as of commit e998295, which gave `:assoc` operators the
flattened-sequence normal form: `(MMul a ..rest)`, `(MMul ..pre (Id n) ..suf)` and the
rest all rely on a one-element application denoting its argument, and it now does.

**Blocked 2026-08-17, unblocked the same day.** The A-only restatement reached a matcher
defect: with all eight rules restated the guarded Kron/MMul rewrite panicked in
`Match::get`, and the previous version of this section reported it as a defect for
someone else to chase and kept the program as `matrix.native-A-draft.egg.txt`. The
diagnosis found the panic to be the milder of two symptoms. A variadic expansion checks a
fixed child whose variable an earlier atom bound, but its cleanup cleared every local
child, so the next window rebound the variable from its own children rather than checking
it: the guard's constraint was erased and the rule fused Kronecker products of mismatched
dimensions, with no crash. Fixed in the matcher, fenced by
`egraph/tests/egg/a_matrix_kron_fusion.egg` (this program) and by the minimal
`a_prebound_fixed_child.egg`; the registry entry is section 6 of `methodology.md`. The
draft file is gone, the column is validated below, and this program's negative check
`(check (!= ex2 (Kron matA matC)))` is what asserts the guard is enforced.

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
| ours, native-A, naive | 62 | 23 | 10 |
| ours, native-A, semi-naive | 62 | 23 | 3 |

The native-A column's counts are smaller because the declaration is doing the work the
deleted rules used to: one flat `MMul` or `Kron` node stands for every association of its
factors, where the rules encoding materializes each. Its node and class counts are equal
under the two strategies, and the four rows above it are unchanged by the matcher fix
that unblocked it, to the digit. The counts are not comparable to egglog's 53 term-wise:
that column has no `@String` nodes (ours interns six) and binary `MMul` and `Kron` nodes
against ours n-ary. What is comparable is the three assertions, which hold on both
engines. Measured after the fix, so the section 9 campaign, which predates it, carries no
timing for this column.

The guarded rule is the reason commit 4258fa4 exists: under semi-naive delta restriction
it never fired, at the source's budget of 20 and at 60, because the merge that makes its
two roots equal changes no node's tuple and so appears in no variant's delta. A rule
carrying such a constraint is now matched against the whole graph every round. Without
that, both of this benchmark's assertions failed under `--use-semi-naive` and passed
under naive matching, which is how the defect was found.
