# A worked example

This chapter runs the whole method on one policy: the sentence, the signature, the
two candidate encodings, the first anti-unifier, the unexpected shape the
connective bug is reported in, the same query after one domain fact is asserted,
and the same query under graph search.

The earlier chapters used terms of two or three nodes. The file is
[`egraph/examples/au_policy_divergence.egg`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/examples/au_policy_divergence.egg)
and the test suite executes it, including the size bounds quoted below.

## The sentence

> A cross-region replication request is permitted only if the source bucket has
> versioning enabled and the destination bucket lies in an approved region. If
> the object is tagged confidential, the destination and source accounts must be
> the same and server-side encryption with a customer-managed key must be in
> effect. Objects up to the multipart threshold are copied directly; larger
> objects require a multipart copy.

## The signature

```lisp
(sort Formula)
(sort Int)
(sort Bucket)
(sort Object)
(sort Region)
(sort Account)

(function Lit (bool) Formula)
(function And (Formula) Formula :assoc-comm-idem :identity (Lit true))
(function Or (Formula) Formula :assoc-comm-idem :identity (Lit false))
(function Implies (Formula Formula) Formula)
(function Ite (Formula Formula Formula) Formula)
(function Eq (Account Account) Formula :comm)
(function Lt (Int Int) Formula)
(function Lte (Int Int) Formula)
```

Four declarations do work here. `And` and `Or` are ACI with their Boolean units,
`Eq` is commutative, and `Lit` embeds the engine's concrete `bool` sort so the
units are real terms. Nothing else about Boolean algebra is implied: no
distributivity, no De Morgan, no absorption. Adding those would mean adding
rewrite rules and would change what the engine proves equal.

The domain vocabulary is ordinary declarations, plus one detail worth noticing:
`src`, `dst` and `obj` are nullary, so this is a ground instance for one request
rather than a universally quantified policy.

## The two candidates

Encoding A:

```lisp
(let formulaA
  (Implies (permit)
    (And
      (versioningOn (src))
      (approvedRegion (regionOf (dst)))
      (Implies
        (taggedConfidential (obj))
        (And
          (Eq (accountOf (dst)) (accountOf (src)))
          (sseCmk)))
      (Ite
        (Lte (sizeOf (obj)) (multipartThreshold))
        (directCopy)
        (multipartCopy)))))
```

Encoding B:

```lisp
(let formulaB
  (Implies (permit)
    (And
      (Ite
        (Lt (sizeOf (obj)) (multipartThreshold))
        (directCopy)
        (multipartCopy))
      (Implies
        (taggedConfidential (obj))
        (Or
          (Eq (accountOf (src)) (accountOf (dst)))
          (sseCmk)))
      (Or
        (usEast1 (regionOf (dst)))
        (euWest1 (regionOf (dst))))
      (versioningOn (src)))))
```

There are five textual differences. Three of them mean nothing:

- the four conjuncts are in a different order;
- `Eq`'s two arguments are swapped;
- B expanded `approvedRegion` into the disjunction of two concrete regions.

Two of them are bugs:

- B wrote `Or` where the sentence says *and*, so it permits confidential
  cross-account replication as long as encryption is in effect;
- B wrote `Lt` where the sentence says *up to*, so an object exactly at the
  threshold takes the multipart path.

A textual diff reports five differences and ranks none of them.

## First query

```lisp
(antiunify formulaA formulaB :algorithm exact)
(checkau formulaA formulaB :max_size 42 :algorithm exact)
```

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

Two of the three noise differences are gone. Conjunct order never appears
because `And` is ACI, and `Eq`'s argument order never appears because `Eq` is
commutative. Neither cost any search: the two candidates are the same e-nodes at
those positions.

Three `Variants` groups remain. The `Ite` condition is one of the real bugs,
stated exactly: `Lte` on one side, `Lt` on the other. The last one is the
`approvedRegion` expansion, which is noise the signature alone cannot absorb,
because whether the two are equal is a fact about the domain and not about the
operators.

## The connective bug is reported in an unexpected shape

The `And`/`Or` bug is the first group, and it is not one `Variants` holding
`(And ...)` against `(Or ...)`. It is two, expressed through the two identity
elements:

```lisp
(And
  (Or (Eq (accountOf dst) (accountOf src)) (Variants (Lit false) sseCmk))
  (Variants sseCmk (Lit true)))
```

Substitute the left side of both variants and you get
`(And (Or eq false) sseCmk)`, which reduces by `Or`'s unit to
`(And eq sseCmk)`: candidate A. Substitute the right side of both and you get
`(And (Or eq sseCmk) true)`, which reduces by `And`'s unit to
`(Or eq sseCmk)`: candidate B.

The result is correct, and it is smaller than the single-node form, which is why
the solver chose it. Whether it is the *readable* form is a separate question:
"the encryption conjunct moved and two units appeared" is a worse explanation
for a human than "the connective changed from and to or". This is a cost
crossover rather than a rule, and chapter 9 gives the crossover point and the
reason the corpus lands on this side of it.

## Adding the domain fact

The `approvedRegion` difference is not a signature property, it is a claim about
this deployment: the approved regions are exactly these two. Say so as a rewrite
and saturate.

```lisp
(rewrite
  (approvedRegion r)
  (Or (usEast1 r) (euWest1 r)))
(run 3)

(antiunify formulaA formulaB :algorithm exact)
(checkau formulaA formulaB :max_size 35 :algorithm exact)
```

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

The third group is gone and `approvedRegion (regionOf dst)` is now reported as
agreed. Size dropped from 42 to 35 and `:cr` from 0.59 to 0.40.

This is the part that a syntactic diff cannot do at any level of effort. The two
candidates still *say* different things at that position; the engine proved them
equal, so there is no longer a decision there.

Two decisions remain: `Or` where the sentence says *and*, and `Lt` where it says
*up to*.

## The same query with graph search

```lisp
(antiunify formulaA formulaB :algorithm uct :playouts 3000)
(checkau formulaA formulaB :max_size 35 :algorithm uct :playouts 3000)
```

It returns the same size-35 term. Running `uct` once on a new problem class is a
useful cross-check, and on problems this size `exact` is both certified and
faster.
