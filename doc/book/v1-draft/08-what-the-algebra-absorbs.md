# What the algebra absorbs

Chapter 7 claimed that six algebraic declarations absorb six meaningless
differences, leaving exactly two decisions to review. This chapter tests that
claim by withholding one declaration at a time and measuring what the reviewer
gets instead.

The harness is
[`autoformalization/dogwood/ablate.py`](https://github.com/yaspar-org/semi-persistent/blob/main/autoformalization/dogwood/ablate.py).
It edits one line of `repair.egg`, reruns the query, and records three numbers.
Withholding is always a **weakening of the signature**, never a rewrite of the
candidates: the two policies are byte-identical in every row.

## The identity element absorbs a difference of arity

Commutativity and idempotence absorb differences of order and repetition. The
identity element absorbs a difference of **arity**, and nothing else does.

Consider a conjunction of three conditions and a conjunction of the same three
minus one. No reordering makes those the same shape. But if the operator has a
unit, the two terms can be matched with the missing conjunct paired against the
unit.

Here are the same two terms twice, under signatures that differ in exactly one
attribute. `AndU` carries `:identity (Lit true)`; `AndN` does not. Both are
`:assoc-comm-idem`.

```lisp
{{#include ../examples/au-identity-arity.egg}}
```

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

The first result says: both candidates require versioning and encryption; one
additionally requires an approved region and the other requires nothing there.
That is the report a reviewer needs for a dropped requirement.

The second says nothing at all. Two of the three conjuncts are identical and none
of that is reported, because with no unit there is no way to line up a 3-child
node against a 2-child node, so the anti-unifier returns both conjunctions whole.
`:cr 1.0000` is the no-sharing endpoint of the compression ratio exactly.

The `checkau` bounds make the contrast an assertion the test suite enforces. The
same construction with `Or` and `(Lit false)` handles a dropped disjunct, and is
in
[`egraph/examples/au_policy_divergence.egg`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/examples/au_policy_divergence.egg).

## What is measured

| column | meaning |
| --- | --- |
| `size` | skeleton size of the returned term |
| `shown` | how many `Variants` nodes the reviewer is asked to look at |
| `kind` | is decision 1 still isolated? |
| `guard` | is decision 2 still isolated? |

"Isolated" means some single `Variants` node offers exactly that decision's two
answers and nothing else. A decision that is still visible but bundled with
other structure is not isolated, because the reviewer no longer has a binary
question in front of them.

## One engine constraint

`:identity` requires an AC operator ([chapter 3](03-algebra.md)), so weakening
`eAnd` from `:assoc-comm-idem :identity (eTrue)` down to `:assoc` drops the unit
at the same time. The two effects cannot be separated in one row. The unit
therefore gets its own row, where `:comm` is kept and only `:identity` is
withheld.

## The measurement

| withheld | absorbs | size | shown | kind | guard |
| --- | --- | --- | --- | --- | --- |
| nothing | the whole declared theory | 61 | 2 | yes | yes |
| `eAnd :comm` (and the unit with it) | Cedar conjunct order | 102 | 1 | no | no |
| `eAnd :identity` | a dropped Cedar conjunct | 102 | 1 | no | no |
| `tAnd :comm` | temporal conjunct order | 80 | 3 | no | yes |
| `args :comm` | predicate field order | 70 | 8 | yes | yes |
| `eEq :comm` | which side of `==` the literal is on | 69 | 4 | yes | no |
| the `birewrite` | a mirrored comparison | 92 | 2 | no | yes |
| window normalization | the window's surface unit | 62 | 3 | yes | yes |
| all of the above | nothing | 102 | 1 | no | no |

## Reading it

**Four of the rows destroy a decision.** Withhold `eAnd`'s unit and the output
is a single `Variants` node holding both policies whole: skeleton 102, nothing
reported as agreed, neither decision isolated. That is the strongest row in the
table and also the one to take most seriously, for the reason in the next
section. Withholding `tAnd :comm` or the `birewrite` costs the kind decision:
the kind bug sits underneath the temporal conjunction and inside the comparison,
so a difference at either of those positions swallows it. Withholding
`eEq :comm` costs the guard decision, because the dropped guard's sibling in the
`eAnd` is the `eEq`.

The pattern is not that every declaration matters. It is that **a property
matters exactly when a real mistake sits underneath the operator it was
withheld from.**

**Two of the rows only add clutter.** `args :comm` keeps both decisions isolated
and raises the count from 2 to 8: the reviewer still has the two real questions,
now with six spurious ones alongside. Window normalization behaves the same way
at 3, and it is not even a declaration, it is an encoding choice made when the
surface syntax is translated to seconds.

Clutter is a real cost, since the point of the exercise is to be worth reading.
But it is a different and smaller cost than losing the decision.

**Note what a falling `shown` count means.** In four rows the count goes *down*,
to 1. That is not an improvement. It means the variants fused into a single node
containing whole subterms, which is the degenerate output, and it is why the
table reports `kind` and `guard` separately rather than ranking on the count.

## The honest objection

For five of the six differences, a canonicalizing pretty-printer plus `diff`
would absorb them at far lower cost than an e-graph. Sort the conjuncts,
normalize equality orientation, normalize the comparison direction, normalize
the window unit, print, diff. That is a weekend of work and no dependency.

What a normalizer cannot do is align a 2-conjunct condition against a 3-conjunct
one. There is no normal form that makes those the same shape. Matching modulo
the identity element is what pairs the absent conjunct with `eTrue`, and it is
the row where withholding one keyword takes the output from "two binary
questions" to "here are both policies, good luck".

So the defensible claim is narrower than "the algebra absorbs the noise". It is:
ACI and commutativity are a convenient way to get normalization you could have
got otherwise, and the identity element does something a normalizer cannot do at
all.

## Two costs to state

**A soundness side condition.** Declaring Cedar's `&&` commutative is sound only
for subexpressions that do not error. Cedar's `&&` short-circuits, so
`a && b` and `b && a` differ when one operand raises. The Cedar validator
discharges that condition; the e-graph does not check it. Declaring the
attribute is an assertion about the terms being compared, and it is the user's
assertion.

**The noise in the example is chosen.** The kinds of difference in the two
candidates are ones that language models really emit. Their rates in this one
example are not measured, they are picked. So the table measures how much of a
given difference the algebra absorbs, not how often such differences occur.
[Chapter 9](09-corpus.md) is the closest thing here to a rate measurement, and
it is a generated corpus rather than a sample of real model output.
