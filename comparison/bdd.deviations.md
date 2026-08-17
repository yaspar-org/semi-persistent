# bdd: dropped, with reason

Source: `egglog/tests/web-demo/bdd.egg` at 7b1adf2. Benchmark 9 of the
intersection set, selected as the commutative-without-associative case:
`bddand`, `bddor` and `bddxor` each have a commutativity rewrite and no
associativity rewrite, so their native dual is `:comm`, which we support.

**Not translated.** No `.egg` files are shipped for it.

## Why

Six of the benchmark's rules — the variable-ordering rules that make it a BDD
rather than an arbitrary if-then-else soup — are guarded by a primitive
comparison on the two `i64` variable labels:

```
(rewrite (bddand (ITE n a1 a2) (ITE m b1 b2))
    (ITE n (bddand a1 (ITE m b1 b2)) (bddand a2 (ITE m b1 b2)))
    :when ((< n m)))
```

Our `:when` takes patterns, and a primitive operator may not appear in a
left-hand side at all. Probed directly:

```
(rewrite (ITE n a b) (Mark a) :when ((i64::< n 5)))
```

```
sort error: sort error: primitive operator 'name' cannot appear in LHS pattern
(only in RHS or ground terms)
```

Dropping the guard is not an option: it is not a restriction on an otherwise
sound rule, it is the rule's correctness condition. Unguarded, `(< n m)` and
`(< m n)` both fire on every pair of distinct labels, so the two orderings
expand each other and the ITE tree grows without bound. The benchmark's twelve
checks assert BDD canonicity, which is precisely what the ordering discipline
buys; without it there is nothing left to check.

Dropping the six rules instead leaves the compression rule, the constant folds
and the commutativity rules. Of the twelve checks, the ones that survive are the
ones that never needed a variable ordering (`$t0`, `$t3`, `$t4`), and the
benchmark stops being a BDD benchmark. That is a drop under the
drop-don't-fudge rule (`methodology.md` section 5), not a scoping.

## What would unblock it

Primitive predicates in `:when` — a guard form that evaluates a builtin
comparison over already-bound pattern variables and fails the match when it is
false. This is a narrower feature than the root-binding form `matrix` needs, and
it would also cover `integer_math`'s `:when ((!= 0 b))` (already handled there by
dropping a rule with zero matches) and part of what `eqsolve` needs.
