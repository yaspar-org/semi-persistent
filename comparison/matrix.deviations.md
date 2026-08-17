# matrix: dropped, with reason

Source: `egglog/tests/web-demo/matrix.egg` at 7b1adf2. Benchmark 7 of the
intersection set, selected for one property: mixed AC and A-only operators in one
signature. `Times` over `Dim` has both an associativity pair and a commutativity
rule (AC); `MMul` and `Kron` over `MExpr` have associativity in both directions and
no commutativity (A-only).

**Not translated.** No `.egg` files are shipped for it.

## Why

The benchmark's subject is one conditional rewrite:

```
(rewrite (MMul (Kron A B) (Kron C D))
    (Kron (MMul A C) (MMul B D))
    :when
        ((= (ncols A) (nrows C))
        (= (ncols B) (nrows D))))
```

The guard is an equality between two *derived* terms: the e-class of `(ncols A)`
must be the e-class of `(nrows C)`. Expressing it needs a pattern form that binds
the root e-class of a sub-pattern, which egglog writes `(= v (f x))` and our
pattern language does not have. Our patterns are `(Op children…)` only; there is no
way to name a pattern's root, so there is no way to state that two patterns share
one. Probed directly:

```
(datatype E (F i64) (G E) (H E E))
(rule ((= e (F x))) ((union e (G (F x)))))
```

```
sort error: sort error: unknown operator '='
```

The same error comes from `:when ((= x zero))`, which
`egraph/doc/design/A1-language-guide.md` line 149 documents as supported. The
guide is wrong on that point: `parse_rule_tags` reads `:when` as a list of
`SurfacePattern`, and sortcheck rejects `=` as an operator. Reported separately;
it is not a `comparison/` fix.

Dropping the rule is sound but not honest here, because both of the benchmark's
substantive assertions turn on it:

- `(check (= $ex1 $simple_ex1))` — the derivation of
  `(MMul (Kron (Id n) B) (Kron A (Id m))) = (Kron A B)` goes through exactly this
  rewrite and through no other.
- `(fail (check (= $ex2 (Kron $A $C))))` — the negative test, whose whole content
  is that the guard *blocks* the rewrite when the dimensions disagree.

Removing the rule makes the first check fail and the second pass vacuously. What
would be left is fifteen unconditional A and AC rules with no assertions: a node
generator, not the benchmark. Under the drop-don't-fudge rule
(`methodology.md` section 5) that is a drop, not a scoping.

A second, independent blocker would have applied even with the guard: `MMul` and
`Kron` are A-only, and our `:assoc` does not flatten nested applications (see
`calc.deviations.md`). The native column would have needed the same pre-flattening
workaround, on operators whose whole role here is re-association.

## What would unblock it

A root-binding pattern form — `(= v pat)` in rule left-hand sides and in `:when`,
binding `v` to the matched node's e-class. That single feature makes the guard
expressible and is what the language guide already claims. `bdd` and `eqsolve` are
blocked on primitive guards instead, which is a different gap; see their ledgers.
