# resolution: deviation ledger

Source: `egglog/tests/web-demo/resolution.egg` at 7b1adf2. Ground resolution
over CNF clauses: a clause is a right-nested `myor` chain terminated by
`false`, saturated by resolution, unit propagation, absorption and
simplification. The source's own comments state that encoding the set nature
of clauses through AC rules is inefficient, which is what the native column
measures.

Files: `resolution.egglog.egg` (theirs, verbatim), `resolution.rules.egg`
(ours, A/C/absorption as explicit rules), `resolution.native.egg` (ours,
`myor` declared variadic `:assoc-comm-idem`), this ledger.

## Deviations in the rules translation

1. **Identifier renaming.** `$True`/`$False`/`$p0`/`$p1`/`$p2` become
   `tt`/`ff`/`p0`/`p1`/`p2`. Pure renaming.
2. **Pattern-equals-global rules bound explicitly.** The source's
   `(rule ((= (negate p) $True)) ...)` shape becomes
   `(rule ((= x (negate p)) (= x tt)) ...)`: the root is bound by the scan
   and constrained to the global's class. Same match set.
3. **The bare-variable rewrite dropped as a duplicate.** The source contains
   both `(rewrite p $True :when ((= $True (myor p $False))))` and the rule
   form of the same inference one line below; the two derive the same
   equality. The translation keeps the rule form only.

## The native column's reshaping

`myor` is `:assoc-comm-idem`: a clause is a set of literals, so the two A/C
rules and the idempotent absorption `(myor a (myor a b)) -> (myor a b)` are
canonization and are deleted. The complementary-pair absorption and the
true-absorption restate n-ary with a rest variable. Two decisions carry the
translation:

1. **The false terminator stays in every clause as its sentinel.** Dropping
   it (the source's `(myor $False a) -> a`) would collapse a unit clause to a
   bare literal by singleton collapse and take it out of `myor` form, where
   the unit-propagation and resolution patterns live. With the sentinel kept,
   the unit clause is exactly the two-element set `{p, false}` and the
   pattern `(myor p (FalseConst))` matches it. The two false-drop and two
   true-drop orientation duplicates of the source collapse to one rule each.
2. **Resolution unions the two rests through a double splice**,
   `(myor ..as ..bs)`: set union deduplicates shared literals and the
   sentinel, and the result is never empty because both rests carry `false`.

No multiplicity variants are needed anywhere: an idempotent set holds every
element at multiplicity 1.

## Validation

All three checks (`tt != ff`, `p0 = ff`, `p2 = ff`) pass on both engines,
under both of our strategies, in both encodings. Node counts ours at
`(run 10)`: rules 72, native 19; the set canonization removes the
rearrangement chains the rules encoding materializes.
