# Three congruence closures

This chapter covers the two halves of AC reasoning and a gap between them, in five
sections: what plain congruence closure derives and where it is complete, where it
breaks for AC, eager completion under `--derive-ac-eqs`, lazy completion under
`--lazy-ac-eqs`, and a table for choosing among the three. The gap bears on any `!=`
over an AC operator.

[Chapter 3](03-algebra.md)'s declarations are about **canonization**: what a single
node absorbs the moment it is built, which is argument order, nesting, multiplicity,
the count clamp, and the unit. Those are free, they need no rule, and they are what
the node kinds are for. This chapter is about the other half, congruence closure.

## What plain congruence closure gives you

This section states what congruence closure derives and where it is complete.

Congruence closure derives one thing: equal arguments make equal applications. If
`x` and `y` are in the same class then `f(x)` and `f(y)` are too, at every depth,
for every operator above them.

Canonization plus congruence closure is **complete** for free operators. Two ground
terms over uninterpreted function symbols are equal in the theory of the asserted
equations exactly when the e-graph puts them in one class.

## Where it breaks for AC

This section gives the smallest case where canonization erases a class reference that
congruence would have followed, and the check that fails because of it.

Congruence follows class references. Canonization of an AC node **erases** some of
them: flattening splices a nested same-operator child into its parent, so the child
class stops being a child at all.

The smallest case. Assert that `{a, b}` is `c`, and that `{a, b, d}` is `n`. AC
entails `n = c + d`, by grouping the known sub-sum out of `n`:

```text
add(a, b, d)  =  add( add(a, b), d )  =  add(c, d)
```

Plain recanonicalization cannot take that step. It walks `n`'s children `{a, b, d}`
and calls `find` on each. All three are unchanged, so nothing happens. The
sub-multiset `{a, b}` is not a child of `n`; flattening erased it, and with it the
reference congruence would have followed to `c`.

This program therefore **fails** its last check, and the test suite asserts that it
keeps failing:

```lisp
{{#include ../examples/13-cc-plain.egg}}
```

```text
error: check failed: terms are not equal
```

Note the check just above the failing one. Congruence itself is present and firing;
`f(add(a,b))` and `f(c)` are equal because there the class reference survived. The
gap is specific to a sub-multiset that flattening consumed.

## Eager completion

This section covers `--derive-ac-eqs`: the two operations its closure performs, the
same program under the flag, and what running it on every rebuild costs.

`--derive-ac-eqs` makes every rebuild attempt **AC completion**. It treats each
asserted AC equation as a rewrite rule on multisets and closes that rule set under
the two operations ground AC completion needs: substituting a known sub-sum into a
node that contains it, which handles the case above, and building the superposition
of two overlapping sums, which handles the harder case where the term that exposes
the equality is in no node at all.

Same program, one flag:

```lisp
{{#include ../examples/13-cc-eager.egg}}
```

```text
ok — 9 nodes
```

The price is that the closure runs on every rebuild whether or not anything needed
it, and that it mints nodes: the substituted forms are real nodes that stay.

## Lazy completion

This section covers `--lazy-ac-eqs`: the transaction the search decides inside, and
the two properties that bound what the mode can serve.

`--lazy-ac-eqs` runs saturation plain and pays for completion only when an equality
check asks something plain congruence cannot answer. The search runs inside a
**semi-persistent transaction**: mark the graph, turn completion on, decide, restore.
Every node the decision minted is discarded, so the graph you keep is the plain one.

```lisp
{{#include ../examples/13-cc-lazy.egg}}
```

```text
ok — 9 nodes
```

Two properties bound what lazy mode can serve: the trigger is an equality check,
and consecutive checks share one transaction.

**The trigger is an equality check.** `(check (= a b))` and `(check (!= a b))` are
the only two commands that open the transaction. The first command that is not one
of them closes it and restores. So lazy mode answers questions asked in that form,
and does nothing for a computation that consults equality some other way.
[Chapter 14](14-au-and-ac.md) covers one such computation, anti-unification.

**Consecutive checks share one transaction.** The mark is taken at the first failing
check and released at the first non-check command, so a run of checks accumulates
completion state instead of each rederiving from nothing.

## Choosing

This section tabulates what the three modes compute and when each applies, then
enters one caution about `!=` under the default.

| | what it computes | when to use it |
| --- | --- | --- |
| plain (default) | canonization and plain congruence | no AC operators, or AC operators with no asserted equations between AC nodes |
| eager (`--derive-ac-eqs`) | completion on every rebuild | you need the full relation available to something other than an equality check |
| lazy (`--lazy-ac-eqs`) | completion per equality check, then rolled back | a few `=`/`!=` questions over a large graph you do not want to grow |

One caution about the default. A `(check (!= a b))` that passes in plain mode means
"plain congruence did not derive this", which is weaker than "the theory does not
entail it". If a `!=` over AC operators is carrying a claim, run it under eager
completion, where a passing `!=` means the closure the engine implements found no
derivation.

Neither mode makes the closure a decision procedure for every AC-entailed equality
in the presence of user rules. The completeness argument, its open obligations, and
the growth budgets that can report a result as inconclusive are in the design
chapter
[`ac-congruence-completeness.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/ac-congruence-completeness.md).
