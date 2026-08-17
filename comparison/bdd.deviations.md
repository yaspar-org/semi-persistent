# bdd: deviation ledger

Source: `egglog/tests/web-demo/bdd.egg` at 7b1adf2. Benchmark 9 of the intersection set,
selected as the commutative-without-associative case: `bddand`, `bddor` and `bddxor` each
have a commutativity rewrite and no associativity rewrite, so their native dual is
`:comm`.

Files: `bdd.egglog.egg` (theirs), `bdd.rules.egg` (ours, commutativity as explicit rewrite
rules), `bdd.native.egg` (ours, native C), this ledger.

**Dropped 2026-08-16, translated 2026-08-17.** The drop was on a missing pattern-language
feature, primitive predicates in `:when`; that feature landed in commit 99c690f and the
benchmark translates with the guard intact. The previous version of this file, which
argued the drop, is in the history of commit c2558c7; do not cite it as current.

## What the guard is and why nothing else would do

Six of the benchmark's rules are the variable-ordering rules that make it a BDD rather
than an arbitrary if-then-else soup, and each is guarded by a comparison on the two i64
variable labels:

```
(rewrite (bddand (ITE n a1 a2) (ITE m b1 b2))
    (ITE n (bddand a1 (ITE m b1 b2)) (bddand a2 (ITE m b1 b2)))
    :when ((< n m)))
```

The guard is the rules' correctness condition, not a restriction on an otherwise sound
rule: unguarded, `(< n m)` and `(< m n)` both fire on every pair of distinct labels, the
two orderings expand each other, and the ITE tree grows without bound. The twelve checks
assert BDD canonicity, which is exactly what the ordering discipline buys.

Ours writes the same guard with the operator's namespaced name:

```
(rewrite (bddand (ITE n a1 a2) (ITE m b1 b2))
    (ITE n (bddand a1 (ITE m b1 b2)) (bddand a2 (ITE m b1 b2)))
    :when ((i64::< n m)))
```

`n` and `m` are bound to i64 payloads by the two `ITE` patterns, and the guard is
evaluated over those two values once both are bound. Nothing has to exist in the e-graph
for it to hold. See `egraph/doc/design/A1-language-guide.md`, "Predicate Guards".

## Adjustments applied to all three configurations

**Harness lines sit before the final `(pop)`.** The benchmark wraps its tests in one
`push`/`pop` pair, so `(print-size)` and `(print-stats)` after the `(pop)` would describe
an empty graph. Both engines print before the pop instead, so the counts describe the
saturated graph the run built. `calc` reports post-pop counts because its blocks are
interleaved; the two benchmarks' node columns are therefore not comparable with each
other, which they were not anyway (methodology section 3).

## Adjustments on our side only

**`$`-prefixed names are renamed.** `$True` becomes `bTrue`, `$v0` becomes `bv0`, and so
on: our identifiers are letters, digits and underscore. Mechanical, no semantic content.
The same renaming is applied in `until` and `calc`.

**Namespaced primitive.** `(< n m)` becomes `(i64::< n m)`. We resolve primitives by
qualified name because more than one numeric type can be in scope.

## The native configuration

`bddand`, `bddor` and `bddxor` are declared `:comm` and their three commutativity rewrites
are deleted. Nothing else changes: the operators are binary in both encodings, because
commutative-without-associative is a binary operator kind on our side and not a variadic
one. No rule needed restating.

Declaring them AC would compare against a strictly stronger system, the same reasoning as
`eqsat-basic`'s `:comm`-only dual.

## Validated

All twelve checks pass in every configuration, on both engines, at the source's
`(run 30)`. Both engines exit non-zero on a failed check, so a clean sweep is the
validation.

| configuration | nodes | classes | iterations |
|---|---|---|---|
| egglog | 99 | | 9 |
| ours, rules, naive | 337 | 16 | 9 |
| ours, rules, semi-naive | 241 | 16 | 7 |
| ours, native, naive | 206 | 16 | 10 |
| ours, native, semi-naive | 136 | 16 | 8 |

Node counts are not comparable across engines (methodology section 3) and differ between
our two evaluation strategies for the reason `math-add-ac` records: a fixed budget is
reached along different paths. The native column materializes fewer nodes because the
commutative dual of each `bddand`/`bddor`/`bddxor` node is not a node.
