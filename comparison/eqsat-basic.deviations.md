# eqsat-basic: deviation ledger

Source: `egglog/tests/web-demo/eqsat-basic.egg` at 7b1adf2. Benchmark 8 of the
intersection set, the calibration smoke test: four rewrite rules, one goal check.

Files: `eqsat-basic.egglog.egg` (theirs), `eqsat-basic.rules.egg` (ours, commutativity
as a rewrite rule), `eqsat-basic.native.egg` (ours, commutativity native).

## Adjustments to the egglog original

1. Appended `(print-size)`, `(print-stats)`, and
   `(print-stats :file "eqsat-basic.egglog.stats.json")`. The original reports nothing;
   the harness needs node counts and an iteration count. The three commands run after
   the `(check …)`, so they cannot affect the saturation being timed.

No other change. The program is otherwise byte-identical to theirs.

## Deviations in the translation

1. **Global names.** `$expr1`/`$expr2` become `expr1`/`expr2`. Our identifier grammar
   has no `$`; egglog warns when a global lacks one. Naming only.
2. **Primitive namespace.** Bare `(+ a b)` and `(* a b)` become `(i64::+ a b)` and
   `(i64::* a b)`, run under `--types machine` so `i64` and `String` are in scope. Same
   two's-complement `i64` semantics on both sides; this benchmark never overflows.
3. **Statistics.** `(print-stats)` becomes `(print-stats :file "…")` so the harness
   reads JSON. `(print-size)` is kept on both sides.

Nothing else differs: same datatype, same four rules, same two terms, same `(run 10)`,
same `(check (= expr1 expr2))`.

## Deviation specific to the native configuration

**The native dual of this program is C, not AC.** The original has a commutativity rule
for `Add` and no associativity rule, so `.native.egg` declares `(Add Math Math :comm)`,
binary and commutative, and deletes `(rewrite (Add a b) (Add b a))`. Declaring `Add`
`:assoc-comm` would have added associativity the original never had, making the native
configuration strictly stronger than the two it is compared against. The three remaining
rules are unchanged and still match up to the commutative swap.

`Mul` stays plain: the original gives it neither property.

## Semantic cross-check

`(check (= expr1 expr2))` passes in all three configurations, at the same 3 iterations.

Node counts differ by construction, and the differences are explained:

| | egglog | ours, rules | ours, native |
|---|---|---|---|
| Add | 4 | 6 | 3 |
| Mul | 3 | 3 | 3 |
| Num | 3 | 3 | 3 |
| Var | 1 | 1 | 1 |
| literal nodes | not counted | 4 | 4 |
| total | 11 | 17 | 14 |

Two accounting differences and one real one.

*Accounting, literals.* Our totals include one node per distinct interned literal
(`@i64: 3`, `@String: 1`); egglog's `(print-size)` sums table cardinalities and never counts a
primitive as a node. Subtracting those four leaves 13 and 10 against their 11.

*Accounting, canonical tuples vs. stored nodes.* egglog's `print-size` reports table
cardinality after rebuild, so two nodes that congruence merged collapse to one tuple; ours reports
stored nodes, and a node that became a duplicate under canonicalization is still stored.
The two-node gap in the `Add` count is exactly this: distribution builds
`Add(Mul(2,x), Mul(2,3))`, constant folding then puts `Mul(2,3)` in `Num 6`'s class, and
the node becomes a duplicate of the `Add(Mul(2,x), Num 6)` that commutativity had already
built. Confirmed on a two-line probe: after `(union (a) (b))` merges `f(a)` with `f(b)`,
egglog prints `f: 1` and we print `f: 2`. Every node-count comparison in this pilot
inherits this bias, and it runs in egglog's favour.

*Real.* The native configuration stores `Add(u,v)` and `Add(v,u)` as one commutative
node, which is the point of the configuration: 3 `Add` nodes against the rules
encoding's 6.

No rules dropped, no checks weakened, no schedule change.
