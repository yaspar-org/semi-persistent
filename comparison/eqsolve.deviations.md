# eqsolve: deviation ledger

Source: `egglog/tests/web-demo/eqsolve.egg` at 7b1adf2. Benchmark 10 of the intersection
set, selected for extraction-path coverage: it solves two small linear systems and the
result is read out with `(extract …)` rather than asserted by a check alone.

Files: `eqsolve.egglog.egg` (theirs), `eqsolve.rules.egg` (ours, A and C as explicit
rewrite rules), this ledger. No native-AC dual ships; the reason is below.

**Dropped 2026-08-16, translated 2026-08-17.** The drop was on two missing
pattern-language features at once, a root-binding form and primitive predicates in
`:when`; both landed (commits 93d698d and 99c690f) and the benchmark translates with its
division rule intact. The previous version of this file, which argued the drop, is in the
history of commit c2558c7; do not cite it as current.

## The rule that produces the benchmark's output

```
(rule ((= (Mul (Num x) y) (Num z))
       (= (% z x) 0))
      ((union y (Num (/ z x)))))
```

It turns `3y = 12` into `y = 4`, and it is also what keeps the search finite, by
collapsing classes onto numerals instead of letting the `Add`/`Neg` rearrangements expand.
It needs two things at once: two patterns constrained to one root e-class, and a
divisibility test over the two bound literals. Ours:

```
(rule ((= (Mul (Num x) y) (Num z))
       (i64::!= x 0)
       (i64::== (i64::% z x) 0))
      ((union y (Num (i64::/ z x)))))
```

The three other `(rule …)` forms of the source bind a pattern's root and use it only in
the action; they now translate verbatim rather than by substituting the pattern for the
variable, which is what the drop-era ledger proposed.

## Adjustments applied to both configurations

**The run budget is 6, not 5.** Measured: at `(run 5)` our engine has not yet joined
`(Var "x")` to `(Num 5)`, so the three answers are not available, while all seven of the
benchmark's own checks already pass. At `(run 6)` all three answers hold. egglog's output
is identical at 5 and at 6, so raising it changes nothing on their side and both engines
run one program.

**The three answers are asserted, not only printed.** `(check (= (Var "x") (Num 5)))` and
its two siblings are added to both files. The source only extracts them, and an extraction
is not a check; asserting them is what makes the two engines' agreement on the answers
part of the validation rather than something a reader has to eyeball.

## Adjustments on our side only

**A `x /= 0` guard with no counterpart in theirs.** Their `%` is partial and yields no
value at zero, so their rule silently does not fire when `x` is `0`; ours is total and
traps, and `(Num 0)` does reach a `Mul` position in this program. `(i64::!= x 0)` written
before the divisibility guard restores their behaviour. It is checked first for a reason
that does not depend on source order: a guard is lowered as soon as the atoms binding its
values have run, the zero test reads `x` alone and the divisibility test reads `x` and
`z`, so the first is never checked after the second (chapter 08, Phase A). The rule fires
on exactly the same matches either way.

**`(- 0 n)` becomes `(i64::neg n)`.** A primitive's arguments on a right-hand side must be
bound literal-value variables, so a literal `0` cannot appear there. `0 - n` and `-n` agree
on every i64 except `i64::MIN`, which this program does not reach.

**Our extractor prints `(Var "x")` where theirs prints `(Num 5)`.** The classes agree,
which the three added checks assert. `(Var "x")` and `(Num 5)` are both a constructor over
one leaf, so they tie on cost and the tie breaks the other way. Not a deviation in what is
derived, only in which of two equally cheap representatives is printed.

## No native-AC dual, and why

`Add` is AC and `Mul` is commutative-only, so the dual is written the same way as
`integer_math`'s: declare `(Add Expr :assoc-comm)` and `(Mul Expr Expr :comm)`, delete the
three A/C rules, and restate the rules that matched an `Add` in n-ary form. Two things
came out of writing it, and only the first is fixable inside this directory.

**An AC pattern's elements match distinct children, so every n-ary lift of a binary rule
needs a multiplicity-2 twin.** `(Add (Mul y x) (Mul z x) ..rest)` does not match the node
`{(Mul 1 y) : 2}`, because the two pattern elements have to bind distinct children;
`(Add (Mul y x):2 ..rest)` is the case it misses, and it is the one that turns `y + y`
into `2y`. Reproduction:

```
(datatype E (N i64) (plus E :assoc-comm) (Mark E))
(let t (plus (N 1) (N 1)))
(rule ((= s (plus a b ..rest))) ((union (Mark s) s)))
(run 3)
(check (= (Mark t) t))
```

```
error: check failed: terms are not equal
```

`integer_math.native.egg` has the same shape in its constant folds and its factoring rule,
and its checks pass, so the gap is latent there rather than load-bearing. Worth a pass over
that file.

**The dual still fails, on AC congruence completeness.** With the twins added, checks 3
through 7 fail at 6, 8, 10 and 12. The reason is the problem
`egraph/doc/design/ac-congruence-completeness.md` opens with: `a+b = p` entails
`a+b+c = p+c`, and deriving that class of consequence is completion's job, not
canonicalization's. This program needs exactly it, because `z = 6 + (-y)` has to entail
`z + z = 6 + (-y) + 6 + (-y)`. Measured in the saturated graph:

```
(let f1 (Add (Add (Num 6) (Neg (Var "y"))) (Add (Num 6) (Neg (Var "y")))))
(let f2 (Add (Num 6) (Num 6) (Neg (Var "y")) (Neg (Var "y"))))
(check (= f1 f2))
```

```
error: check failed: terms are not equal
```

`--derive-ac-eqs`, which exists to close exactly this, does not terminate within 120 s on
this program. So the dual is **postponed, not dropped**: it becomes writable when AC
completion is fast enough to run on a program of this size, and the test of that is this
file. The rules configuration ships and is validated, which is the same position `herbie`
is in for a different reason.

## Validated

All seven of the source's checks plus the three added answer checks pass in both shipped
configurations, on both engines, at `(run 6)`.

| configuration | nodes | classes | iterations |
|---|---|---|---|
| egglog | 2110 | | 6 |
| ours, rules, naive | 9583 | 1567 | 6 |
| ours, rules, semi-naive | 9085 | 1534 | 6 |

Node counts are not comparable across engines (methodology section 3). The set keeps its
extraction-path column: both engines reach the same three answers, and the two agree on
every class the benchmark asserts.

**Update 2026-08-17.** The "worth a pass over that file" above is done: the
partition-semantics reading was confirmed as intended (an element takes its
child's whole multiplicity, exactly 1 unless annotated), `:k>=2` twins with
RHS-readable `k` were added by hand to `integer_math.native`,
`math-microbenchmark.native` and both `matrix` native files, and all
re-validated counts are identical to the campaign (the twins fire zero times
on the shipped workloads). Methodology section 6, same date, has the summary;
`egraph/tests/egg/ac_coincidence_twin*.egg` pin both directions. The
reproduction above still fails by design: its two-element rule needs the twin,
which is the documented migration rule, not an engine defect.

## The three completion modes, measured (2026-08-17)

The engine now has three ways to run an AC workload — plain (canonization and
congruence only), eager completion (`--derive-ac-eqs`) and lazy completion
(`--lazy-ac-eqs`, the completion pass inside a mark/complete/restore
transaction at failing checks, with goal-directed rule/completion alternation;
design doc section 13). Measured on the experimental native dual with its
twins (checks numbered 1-10 as in this file):

- **plain**: 69 nodes at `(run 6)`; checks 1, 2 and 8 pass (system 1 solves
  without completion), the rest fail on congruence completeness.
- **eager**: every round budget up to 5 terminates (37 / 146 / 608 / 30 978 /
  203 908 nodes at 0 / 0 / 0 / 15 / 33 s), and checks 1-8 hold at budget 5.
  Budget 6, which the answer checks 9-10 need, exceeds 600 s: not a loop —
  the reduced basis converges each round — but compounding growth from the
  completion-with-rules interaction (lcm superposition widens sums, rules
  multiply them, folding mints new atoms that refeed the next round).
- **lazy**: decides check 3 instantly (eager spends 15 s+ before reaching it)
  and check 7 in 124 s; checks 9-10 sit past the same interaction blowup, and
  today each check re-derives from scratch (the shared-transaction refinement
  is recorded in the design doc).

The rules encoding remains the shipped configuration and the right one for
this benchmark: 129 ms, all ten checks, because binary nodes keep the
intermediate sums whose plain congruence decides these entailments for free.
The native column stays postponed; what would unblock it is completion cost,
not translation.

## The native dual ships, validated under lazy completion (2026-08-17, later)

The three lazy refinements (design doc section 13: one transaction shared
across consecutive checks, goal polling inside the completion loop, in-round
budget check) bring the remaining checks into reach: `eqsolve.native.egg`
passes **all ten checks** under `--lazy-ac-eqs` in one 484 s run, ending at
the restored 73-node graph. The file carries a `REQUIRES` header and is
excluded from the timed tables and default-flag sweeps: 484 s against the
rules encoding's 123 ms is a validation result, not a competitive column
(matrix.native-A precedent: validated, no timing row). The rules encoding
remains the shipped configuration for this benchmark.
