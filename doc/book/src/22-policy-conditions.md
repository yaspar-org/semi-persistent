# General policy conditions

The final example contains nested conditions, two Boolean connectives, and a
numeric boundary. It shows one connective error represented through two
identity elements, removes a domain-specific difference, and cross-checks the
result under UCT.

## The sentence

> A cross-region replication request is permitted only if the source bucket
> has versioning enabled and the destination bucket lies in an approved region.
> If the object is tagged confidential, the destination and source accounts
> must be the same and server-side encryption with a customer-managed key must
> be in effect. Objects up to the multipart threshold are copied directly;
> larger objects require a multipart copy.

The self-contained fixture models one ground request. `And` and `Or` are ACI
with their Boolean identities, and `Eq` is commutative. No other Boolean law is
implicit.

## The selected disagreement

`formulaA` follows the sentence. `formulaB` seeds two policy errors: it uses
`Or` instead of `And` for the confidential-object requirements, and `Lt`
instead of `Lte` at the multipart threshold. It also reorders conjuncts,
reverses the account equality, and expands `approvedRegion`.

The first selected query is:

```lisp
{{#include ../examples/22-policy-conditions.egg:policy-first-query}}
```

It prints:

```text
(anti-unify :size 42 :cr 0.5862 :completion exact
  (Implies
    permit
    (And
      (Implies
        (taggedConfidential obj)
        (And
          (Or (Eq (accountOf dst) (accountOf src)) (Variants (Lit false) sseCmk))
          (Variants sseCmk (Lit true))))
      (Ite
        (Variants
          (Lte (sizeOf obj) multipartThreshold)
          (Lt (sizeOf obj) multipartThreshold))
        directCopy
        multipartCopy)
      (versioningOn src)
      (Variants
        (approvedRegion (regionOf dst))
        (Or (usEast1 (regionOf dst)) (euWest1 (regionOf dst)))))))
```

Conjunct order and equality-operand order have disappeared. Four `Variants`
nodes describe three semantic disagreements: the connective change, the
threshold comparison, and the named region predicate.

## One connective error through two units

The confidential-object difference appears as

```lisp
(And
  (Or (Eq (accountOf dst) (accountOf src))
      (Variants (Lit false) sseCmk))
  (Variants sseCmk (Lit true)))
```

Selecting both left alternatives gives
`(And (Or eq false) sseCmk)`. The `Or` identity reduces this to
`(And eq sseCmk)`, which is `formulaA`'s condition. Selecting both right
alternatives gives `(And (Or eq sseCmk) true)`. The `And` identity reduces
that to `(Or eq sseCmk)`, which is `formulaB`'s condition.

One semantic connective change therefore uses two syntactic markers. The term
is optimal under Chapter 12's objective, but "and versus or" is the clearer
human description. Chapter 16 separates objective optimality from readable
presentation.

## Adding the domain fact

The approved-region expansion is a fact about this deployment, not an
algebraic property of `Or`. The fixture asserts it as a rewrite and saturates:

```lisp
{{#include ../examples/22-policy-conditions.egg:policy-domain-fact}}
```

The new result is:

```text
(anti-unify :size 35 :cr 0.4000 :completion exact
  (Implies
    permit
    (And
      (Implies
        (taggedConfidential obj)
        (And
          (Or (Eq (accountOf dst) (accountOf src)) (Variants (Lit false) sseCmk))
          (Variants sseCmk (Lit true))))
      (Ite
        (Variants
          (Lte (sizeOf obj) multipartThreshold)
          (Lt (sizeOf obj) multipartThreshold))
        directCopy
        multipartCopy)
      (versioningOn src)
      (approvedRegion (regionOf dst)))))
```

The domain marker is gone. Size falls from 42 to 35 and `:cr` from 0.5862 to
0.4000. The two samples still contain different syntax at that position, but
saturation proved the terms equal. The connective and boundary questions
remain.

## Cross-checking under graph search

The same query under UCT uses a fixed 3,000-playout budget:

```lisp
{{#include ../examples/22-policy-conditions.egg:policy-uct-cross-check}}
```

UCT returns the identical size-35 term with `:cr 0.4000` and
`:completion exact`. Agreement between the two implementations is differential
evidence on this problem shape. It is not an independent proof because Exact
and UCT share the action semantics defined in Chapter 14.
