# until: deviation ledger

Source: `egglog/tests/until.egg` at 7b1adf2. Benchmark 6 of the intersection set,
paired with `calc`. Same group signature; the point of this one is a deliberately
non-terminating rule that `:until` has to cut short. Their own comment: "if you
remove `:until`, this will take a very long time".

Files: `until.egglog.egg`, `until.rules.egg`, `until.native.egg`, this ledger.

## Adjustment applied to all three configurations

**The `allgs` relation becomes a constructor into an empty sort.** The original
writes the generator as datalog:

```
(relation allgs (G))
(rule ((allgs x)) ((allgs (g* $B x))))
(allgs $A)
```

We have no relations. The generator is not incidental: it is the benchmark, since
`:until` exists here to stop it: so it is re-encoded rather than dropped, and the
same re-encoding is applied to the egglog program so that all three configurations
run one problem:

```
(datatype U)                 ;; (sort U) on our side
(constructor allgs (G) U)
(rule ((= u (allgs x))) ((allgs (g* $B x))))   ;; (rule ((allgs x)) …) on our side
(allgs $A)
```

The rewritten rule generates the same unbounded chain, one new group element per
iteration. What changes is bookkeeping: a relation row becomes a node, so `allgs`
now contributes to both engines' node counts. Verified on egglog: the generator
fires three times before the `:until` goal is reached, and all three checks pass.

The egglog side additionally needs `(= u (allgs x))` rather than a bare
`(allgs x)` fact, because `allgs` is now a function. `u` is unused. Our side has
no root-binding pattern form and does not need one here, since `u` is unused.

## Deviations in the rules translation

1. `(datatype G)` with no variants becomes `(sort G)`; `(datatype U)` likewise.
2. Identifiers renamed into our lexical class: `g*` → `gmul`, `$X` → `gX`.

Nothing else changes: same rules, same `:until` budget of 10000, same three
checks, all passing.

## Deviations in the native translation

`gmul` is `:assoc`, not `:assoc-comm`: the source has an assoc birewrite and no
commutativity rule.

The identity and cyclic rules are restated n-ary with prefix and suffix rest
variables, same table as `calc`: a binary pattern is an exact pattern against a
flat sequence node and would stop firing at length 3 or more.

**Withdrawn 2026-08-15.** This file carried the `:assoc` flattening workaround
described in `calc.deviations.md` item 1: the `gmul` terms written flat and the
singleton law `(rewrite (gmul x) x)` stated explicitly. The engine defect is fixed,
both are gone, and the terms are back to the source's nested form
(`(let gA4 (gmul gA2 gA2))` and so on). Kept here because the pilot's first
published numbers for this benchmark were measured under it.

The generator's right-hand side `(gmul gB x)` now flattens when `x` is itself a
`gmul`, so the native column's `gmul` count is over the flattened chain rather than
over sequences of length 2. The generator's behaviour is unchanged either way: one
node per iteration: but the node totals below moved: naive 25 → 22, semi-naive
19 → 17, with the class count and iteration count unchanged at 9 and 2.

## Cross-check

All three checks pass in all three configurations. Smoke pass (1 run, 0 warmups , 
not a timing result):

| config | nodes | classes | iterations |
|---|---|---|---|
| egglog | 7 |: | 3 |
| ours, rules, naive | 52 | 15 | 3 |
| ours, rules, semi-naive | 75 | 22 | 4 |
| ours, native, naive | 22 | 9 | 2 |
| ours, native, semi-naive | 17 | 9 | 2 |

**These node counts are not a result, and the spread between them is expected.**
The program does not saturate: it runs a generator that never stops and halts on a
goal. How many nodes exist when the goal is noticed therefore depends on how many
generator steps happened to run in the round that proved it, which differs by
engine, by encoding and by saturation strategy. The naive/semi-naive split within
one encoding (52 vs 75 nodes, 3 vs 4 iterations) is the clearest case: both are
correct, they stopped at different points. Report wall time for this benchmark and
do not read its node column as an e-graph size comparison. This is the same class
of caveat as `methodology.md` section 4's note on class counts at truncated
budgets, and stronger, because here the budget is a goal rather than a count.
