# Three congruence closures

Chapters 6 and 10 define generic congruence and local canonization. This
chapter compares the additional equalities obtained in plain mode, eager
completion, and lazy completion.

The selected mode does not change the maximum-partition matching relation
defined in Chapter 5. Completion derives equalities between stored terms; it
does not broaden rule matching into classical AC matching.

## A consequence plain mode misses

Consider the asserted equations `add(a,b) = c` and `add(a,b,d) = n`. The
declared AC theory entails `add(c,d) = n`, but flattening means that the larger
stored sum has direct children `a`, `b`, and `d`. The class for `add(a,b)` is
not one of those direct children.

```lisp
{{#include ../examples/11-cc-plain.egg:completion-example}}
```

The first check demonstrates ordinary congruence through a direct child-class
reference. The final check fails because plain mode performs no sub-sum
substitution. Its preceding `print-size` reports 8 e-nodes.

## The modes side by side

For multiset and set operators, eager completion treats asserted ground
equations as an oriented basis and closes implemented inter-reduction,
superposition, and cancellative consequences during rebuild. It also performs
a narrower inter-reduction pass over associative sequences, closing some
equalities hidden when construction flattened an intermediate sequence. Lazy
completion runs the same work only to answer equality and disequality checks,
inside a transaction that is later restored.

| mode | flag | additional work | retained graph | meaning of a passing `!=` |
| --- | --- | --- | --- | --- |
| plain | none | no completion | local canonization and generic congruence | the retained classes are distinct |
| eager | `--derive-ac-eqs` | completion during every rebuild | generated nodes remain | the latest eager rebuild left the classes distinct |
| lazy | `--lazy-ac-eqs` | goal-directed completion for checks | generated nodes are restored away | the operational search reached a fixpoint without joining them |

The eager and lazy fixtures use the same declarations, equations, and decisive
check as the displayed program. Immediately before that check, the measured
node counts are 8 in plain mode, 9 in eager mode, and 8 in lazy mode. Plain
fails the equality check. Eager and lazy pass it, but only eager retains the
additional node.

Eager work runs on every rebuild and is visible to rules, extraction, and
anti-unification. Lazy work is visible to consecutive equality or disequality
checks in the shared transaction. The first other command closes that
transaction, so other graph readers see the restored plain graph.

## Choosing a mode

Use plain mode when the program needs no consequences of asserted equations
over associative, AC, or ACI nodes. Use lazy mode for a limited sequence of
equality questions. Use eager mode when rules, extraction, anti-unification,
or another graph reader must observe completion-derived classes.

One practical point when choosing plain mode: because plain mode derives no
AC consequences, its answer to an equality query over AC or ACI nodes can
depend on the **order the statements appear in**. Flattening a nested
same-operator argument is declined once that argument's class is referenced
as a child anywhere else, and that condition never becomes false again, so
building an unrelated term earlier can change how a later term is spelled:

```lisp
(let t0 (Add (Mul D D) A))    ; delete this line, or move it below, and
(let t1 (Mul D D A D))        ; the following check passes instead of failing
(let t2 (Mul A D (Mul D D)))
(check (= t1 t2))
```

Both readings are sound — a reordering never makes a *false* equality
provable, only a true one unprovable — and within a single term the order is
fixed, so the effect appears only across statements. If a program depends on
equalities like this one, that is the signal to enable `--derive-ac-eqs` or
`--lazy-ac-eqs`, which prove it in either order. Operators declared
associative-only (`:assoc`) are not affected: their flattening is decided
from the written form of the application, so it does not depend on what else
the program has built.

Chapter 23 collects the limits and qualifications of these modes. The
procedures are specified in
[`ac-completion-spec.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/ac-completion-spec.md),
with the scope of the completeness argument in
[`ac-congruence-completeness.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/ac-congruence-completeness.md).
