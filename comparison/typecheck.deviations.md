# typecheck: deviation ledger

Source: `egglog/tests/web-demo/typecheck.egg` at 7b1adf2. Demand-driven
typechecking of the simply typed lambda calculus: `typeof` nodes are demand,
inserted by an application rule and discharged by unification through the
arrow constructor, weakening with a string-disequality guard, and the
abstraction rule whose right-hand side creates further demand.

Files: `typecheck.egglog.egg` (theirs, verbatim), `typecheck.rules.egg`
(ours), this ledger. No native column: no operator is associative or
commutative.

## Deviations

1. **Identifier renaming.** `$TUnit`/`$MyUnit`/`$Nil`/`$e`/`$id`/`$t-id`/
   `$t-app`/`$free`/`$t-free-*` lose the sigil and hyphens. Pure renaming.
2. **Guard qualification.** `(!= x y)` over strings becomes
   `(String::!= x y)`. Pure renaming.
3. **A global-only unit rule bound through its constructor.**
   `(rewrite (typeof ctx $MyUnit) $TUnit)` matches through the pattern
   `(typeof ctx (MyUnitConst))`; the scanned class is the global's.
4. The demand rule's bare-term actions translate verbatim: a bare term in a
   rule action is an insert on both engines.
5. `(print-size)` appended for the harness.

## Validation

All four checks pass on both engines, under both of our strategies. Node
counts ours at `(run 15)`: 73 naive, 62 semi-naive; the strategies
materialize different demand scaffolding on the way to the same checked
classes, the path dependence methodology section 3 records for
demand-driven programs.

Both programs end with `(print-stats :file "...")` so the harness can read node, class, and iteration counts; egglog's `no-messages` timing runs suppress the terminal output either way.
