# knapsack: deviation ledger

Source: `egglog/tests/web-demo/knapsack.egg` at 7b1adf2. Demand-driven 0/1
knapsack: the `Knap` constructor is demand, split by arithmetic guards on the
capacity, folded through `Max`/`Add` constant rules.

Files: `knapsack.egglog.egg` (theirs, verbatim), `knapsack.rules.egg` (ours),
this ledger. No native column: no operator is associative or commutative
(`Add` and `Max` here are applied to two known operands and folded, never
rearranged).

## Deviations

1. **Identifier renaming and literal-op qualification.** `$Nil`/`$test*`
   lose the sigil; `+`/`-`/`max`/`<=`/`>` become their `i64::` forms. The
   guards `(i64::<= weight capacity)` and `(i64::> weight capacity)` are
   primitive predicate atoms in the rule bodies, as in the source.
2. **The `Unwrap` table dropped.** The source ends with a `:no-merge`
   function and a `set` rule that mirror `(Num n)` classes into an i64 table;
   nothing reads it and the check does not depend on it. We have no
   primitive-valued function tables; the drop costs the benchmark nothing
   (the check is on `test1`'s class).
3. **A global-only base-case rule bound through its constructor.**
   `(rule ((= f (Knap capacity $Nil))) ...)` scans
   `(Knap capacity (NilConst))`.
4. `(print-size)` appended for the harness.

## Validation

The check `(= test1 (Num 13))` passes on both engines, under both of our
strategies. Node count ours at `(run 100)`: 276 under both strategies.

Both programs end with `(print-stats :file "...")` so the harness can read node, class, and iteration counts; egglog's `no-messages` timing runs suppress the terminal output either way.
