# Anti-unification modulo the declared algebra

Chapter 4 defines the algebraic declarations, and Chapter 10 shows their child
representations. This chapter measures their effect on anti-unification. Order
and repetition can disappear during term canonization. A declared identity also
lets the anti-unifier align collection nodes with different cardinalities.

## Order, absorbed by commutativity

The two pairs below differ only in whether their operator is declared
commutative:

```lisp
{{#include ../examples/13-order.egg:order-comparison}}
```

The order-sensitive pair reports both positional disagreements. The
commutative pair was already one canonical e-node before the query:

```text
(anti-unify :size 5 :cr 0.6667 :completion exact
  (Pair (Variants a b) (Variants b a)))
(anti-unify :size 3 :cr 0.0000 :completion exact
  (PairC a b))
```

Declaring commutativity changes the measured result from size 5 and ratio
0.6667 to size 3 and ratio 0.

## Repetition, absorbed by idempotence

The next comparison gives the left operand two copies of `a` and the right
operand two copies of `b`. `Bag` preserves those multiplicities, while `SetI`
is idempotent:

```lisp
{{#include ../examples/13-repetition.egg:repetition-comparison}}
```

The multiset result shares one `a` and one `b`, then reports the unmatched
copies. Canonization removes the duplicate members from both `SetI` terms:

```text
(anti-unify :size 5 :cr 0.2500 :completion exact
  (Bag a b (Variants a b)))
(anti-unify :size 3 :cr 0.0000 :completion exact
  (SetI a b))
```

Idempotence changes the measured result from size 5 and ratio 0.25 to size 3
and ratio 0.

## Arity, aligned by an identity element

Order and duplicate removal happen while Semper constructs the operands.
Different cardinalities require an additional AU operation: when an AC or ACI
operator has an identity, the solver can pad the shorter collection with that
identity before aligning children.

The next fixture compares a three-condition conjunction with the same
conjunction missing one condition. `AndU` declares `(Lit true)` as its identity;
`AndN` has the same ACI properties but no identity:

```lisp
{{#include ../examples/13-identity-arity.egg:identity-comparison}}
```

The two measured results are:

```text
(anti-unify :size 10 :cr 0.6250 :completion exact
  (AndU
    (versioningOn src)
    (encrypted src)
    (Variants (approvedRegion (regionOf dst)) (Lit true))))
(anti-unify :size 13 :cr 1.0000 :completion exact
  (Variants
    (AndN (versioningOn src) (encrypted src) (approvedRegion (regionOf dst)))
    (AndN (versioningOn src) (encrypted src))))
```

With the identity, the absent condition is paired with `true`, while the two
shared conditions remain in the skeleton. Without it, the unequal-cardinality
nodes have no structural alignment and both conjunctions are generalized
whole. Identity padding changes the measured result from size 13 and ratio 1
to size 10 and ratio 0.625.

## Where absorption stops

The final query in the repetition fixture compares `(SetI a b)` with
`(SetI a c)`. ACI canonization absorbs order and repetition, but it does not
equate `b` with `c`:

```text
(anti-unify :size 4 :cr 0.3333 :completion exact
  (SetI a (Variants b c)))
```

This is a genuine replacement under the declared algebra: `a` remains shared
and the replacement remains visible. A domain equality can still be established
by a Chapter 5 rule before the query. Part IV covers cases that require a
reviewer rather than another equality.
