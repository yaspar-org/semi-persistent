# eqsolve: deviation ledger

Source: `egglog/tests/web-demo/eqsolve.egg` at 7b1adf2. Benchmark 10 of the
intersection set, selected for extraction-path coverage: it solves two small
linear systems and the result is read out with `(extract ...)`.

Files: `eqsolve.egglog.egg`, `eqsolve.rules.egg`, `eqsolve.native.egg`, this
ledger. The rules encoding is the timed configuration; the native encoding is
validated and excluded from timed tables, for the measured reason below.

## The rule that produces the benchmark's output

```
(rule ((= (Mul (Num x) y) (Num z))
       (i64::!= x 0)
       (i64::== (i64::% z x) 0))
      ((union y (Num (i64::/ z x)))))
```

It turns `3y = 12` into `y = 4`, and it is what keeps the search finite, by
collapsing classes onto numerals instead of letting the `Add`/`Neg`
rearrangements expand. It uses the root-binding pattern form (two patterns
constrained to one root e-class) and primitive predicates in `:when`.

## Adjustments applied to every configuration

**The run budget is 6, not 5.** Measured: at `(run 5)` our engine has not
joined `(Var "x")` to `(Num 5)` while all seven of the source's checks
already pass; at `(run 6)` all three answers hold. egglog's output is
identical at 5 and at 6, so both engines run one program.

**The three answers are asserted, not only printed.** `(check (= (Var "x")
(Num 5)))` and its two siblings are added to every configuration. The source
only extracts them, and an extraction is not a check; asserting them makes
the engines' agreement on the answers part of the validation.

## Adjustments on our side only

**A `x /= 0` guard with no counterpart in theirs.** Their `%` is partial and
yields no value at zero, so their rule silently does not fire when `x` is
`0`; ours is total and traps, and `(Num 0)` does reach a `Mul` position in
this program. `(i64::!= x 0)` written before the divisibility guard restores
their behaviour. A guard is lowered as soon as the atoms binding its values
have run; the zero test reads `x` alone and the divisibility test reads `x`
and `z`, so the first is never checked after the second. The rule fires on
exactly the same matches either way.

**`(- 0 n)` becomes `(i64::neg n)`.** A primitive's arguments on a
right-hand side must be bound literal-value variables, so a literal `0`
cannot appear there. `0 - n` and `-n` agree on every i64 except `i64::MIN`,
which this program does not reach.

**Our extractor prints `(Var "x")` where theirs prints `(Num 5)`.** The
classes agree, which the three added checks assert. `(Var "x")` and
`(Num 5)` are both a constructor over one leaf, so they tie on cost and the
tie breaks the other way. Not a deviation in what is derived, only in which
of two equally cheap representatives is printed.

## The native encoding: validated, not timed

`eqsolve.native.egg` declares `Add` variadic `:assoc-comm` and `Mul` binary
`:comm`, deletes the three A/C rules, and restates the `Add` rules n-ary
with their multiplicity variants. It carries a `REQUIRES` header: it needs
`--lazy-ac-eqs` and a budget of about 600 s.

The reason is AC congruence completeness. Flattening erases intermediate
sums, so `z = 6 + (-y)` does not entail `z + z = 6 + (-y) + 6 + (-y)` by
canonization and congruence alone; deciding this program's checks needs the
completion pass. Measured, all three completion modes on this program:

- **plain** (no completion): 69 nodes at `(run 6)`; checks 1, 2 and 8 pass
  (the first system solves without completion), the rest fail on congruence
  completeness.
- **eager** (`--derive-ac-eqs`): every round budget up to 5 terminates
  (37 / 146 / 608 / 30 978 / 203 908 nodes at 0 / 0 / 0 / 15 / 33 s) and
  checks 1-8 hold at budget 5; budget 6, which the answer checks need,
  exceeds 600 s. The growth is compounding, not a cycle: the reduced basis
  converges each round, and the completion-with-rules interaction widens
  sums while folding mints new atoms that feed the next round.
- **lazy** (`--lazy-ac-eqs`): **all ten checks pass in one 484 s run**,
  ending at the restored 69-node graph. The lazy transaction is shared
  across consecutive checks and every completion pass is goal-directed
  (`ac-congruence-completeness.md` section 13).

484 s against the rules encoding's 118-128 ms is a validation result, not a
competitive configuration, so the native encoding appears in no campaign
table. What would change this is completion cost, not translation.

## The rules encoding's gap to egglog is match volume

Campaign medians (`final/final-r3-tables.md`): egglog 24.9 ms; ours rules
127.7 ms naive, 118.0 ms semi-naive. Measured attribution: deleting the
program's three `(extract ...)` commands moves wall time by nothing (157 ms
with, 155 ms without, 3 runs each), and the run performs 2 741 637
e-matching steps on a 9 583-node graph, 286 steps per node, the same
signature as bdd's rules configuration. The gap is e-matching volume from
the A/C rules encoding, dominated by the isolation rule matching every
`Add` decomposition each round. Extraction's future is the Max-SAT design
in `A3-future-work.md`.

## Validated

All seven of the source's checks plus the three added answer checks pass in
both timed configurations, on both engines, at `(run 6)`; the native
encoding passes all ten under `--lazy-ac-eqs`.

| configuration | nodes | classes | iterations |
|---|---|---|---|
| egglog | 2110 | | 6 |
| ours, rules, naive | 9583 | 1567 | 6 |
| ours, rules, semi-naive | 9398 | 1563 | 6 |

Node counts are not comparable across engines (methodology section 3).
