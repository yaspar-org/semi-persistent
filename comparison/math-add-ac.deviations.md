# math-add-ac: deviation ledger

Source: the `add-ac` ruleset block of `egglog/tests/web-demo/math.egg` at 7b1adf2,
lines 138-160 (`; math_associate_adds`). Benchmark 2 of the intersection set: egglog's
one scoped AC experiment, a seven-term sum re-associated and re-ordered end to end.

Files: `math-add-ac.egglog.egg` (theirs, extracted), `math-add-ac.rules.egg` (ours, A/C
as rewrite rules), `math-add-ac.native.egg` (ours, native AC).

## Adjustments turning the block into a standalone egglog program

1. **Declarations reduced to what the block needs.** The extraction keeps
   `(datatype Math (Add Math Math) (Const f64))` and drops the other eleven variants,
   the `MathU` relation and its thirteen groundedness rules, the constant-folding
   rules, the `prune` ruleset, and every default-ruleset rewrite. This is sound because
   the block runs `(run add-ac 7)`, the `add-ac` ruleset only, which contains exactly
   the two rules declared inside the block, and because nothing before line 138 in
   `math.egg` inserts a term or runs a schedule, so the e-graph at the `(push)` is empty.
   The dropped declarations are unreachable from this block, not simplified away.
2. **`(push)`/`(pop)` dropped.** Nothing follows the block in the standalone file, so the
   scope has no effect. Saturation is timed identically with or without it.
3. **Appended `(print-size)`, `(print-stats)`, `(print-stats :file "…")`,** after the
   `(check …)`, for the harness. Cannot affect the saturation being timed.

No rule, term, budget, or check was altered.

## Deviations in the translation

1. **Ruleset name.** `add-ac` becomes `add_ac`. Our identifier grammar is
   `letter , { letter | digit }` with `letter` including `_` but not `-`, so a hyphen in
   a ruleset name is a parse error. Naming only.
2. **Global name.** `$res` becomes `res` (no `$` in our identifier grammar).
3. **Statistics.** `(print-stats)` becomes `(print-stats :file "…")`.
4. **Type group.** Run under `--types machine` so the `f64` sort is in scope. The
   program does no `f64` arithmetic, because `Const` applied to seven literals is the only
   use, so float semantics never enter.

Same datatype, same ruleset, same two rules, same seven-term input, same `(run add_ac 7)`,
same check.

## Deviations specific to the native configuration

1. **Both rewrite rules deleted**, `Add` declared `(Add Math :assoc-comm)`: variadic, one
   element sort, multiset semantics. This is the intended dual and needs no restatement of
   any other rule, because the block has no other rules.
2. **The empty ruleset is kept declared and still run.** `(ruleset add_ac)` and
   `(run add_ac 7)` remain so the command sequence matches `.rules.egg` exactly; the run
   has nothing to fire and stops after one iteration. Dropping the run instead would have
   removed a command the other configuration pays for.

## Semantic cross-check

The check passes in all three configurations.

| | egglog | ours, rules | ours, native |
|---|---|---|---|
| Add | 1932 | 3242 | 11 |
| Const | 7 | 7 | 7 |
| literal nodes | not counted | 7 | 7 |
| total (naive) | 1939 | 3256 | 25 |
| total (semi-naive) | not run | 3304 | 25 |
| iterations | 7 | 7 | 1 |

The `Add` gap between egglog and our rules encoding (1932 vs. 3242) is the canonical-tuples
vs. stored-nodes accounting difference described in `eqsat-basic.deviations.md`,
amplified here by the 14 446 rule firings the two A/C rules produce.

Our two saturation strategies disagree slightly in the rules encoding (3256 nodes / 148
classes naive, 3304 / 134 semi-naive) because they reach the 7-iteration budget having
applied the two A/C rules in different orders; neither has saturated.

**Superseded 2026-08-17: our four counts above are pre-fix and must not be cited.** They
were measured on 2026-08-15, and the pinned final campaign measures 3317 nodes / 159
classes naive and 3359 / 136 semi-naive; the current figures are in
`final/final-tables.md`, which is the citable table. The cause is the one this section
already names: neither strategy saturates at the 7-iteration budget, and roughly twenty
ematch and scheduling commits landed between 2026-08-15 and the pin that change which
matches are found in which round, so the count at the budget moves with them. The check
passes in every configuration before and after, and the egglog column is unchanged at
1939 nodes / 7 iterations, so what moved is how much work the budget buys and not what
the run concludes. The `Add`, `Const` and literal counts in the table above are left as
measured on 2026-08-15 for the same reason.

The native column is the honest headline of this benchmark: **11 `Add` nodes instead of
1932-3242, and one iteration** (the run fires nothing and reports saturation
immediately). Both the seven-term input and the seven-term reversed
check term flatten at construction into multisets over `{Const 1.0 … Const 7.0}`; the two
outermost multisets are equal, so the check holds before any rule runs. The 11 nodes are
the intermediate prefixes the two nested constructions build on the way in (`{6,7}`,
`{5,6,7}`, … and `{2,1}`, `{3,2,1}`, …), which are genuinely different multisets. The
rules encoding has to enumerate the re-associations that construction gives the native
encoding for free: that is the property under test, not a weakened problem.

No rules dropped, no checks weakened, no schedule change.
