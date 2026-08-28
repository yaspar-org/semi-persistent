# What anti-unification is optimal with respect to

This chapter states what the solver's notion of minimum is measured against, in five
sections: which questions the solver asks of the graph, which direction its error
goes, the three congruence modes measured on one program, why lazy completion does not
help, and the rule that follows. The solver is given two e-classes and returns a
minimum anti-unifier; what "minimum" is measured against changes what a reported
difference means.

## The solver reads the graph, not the theory

This section states which questions the solver asks of the graph, and how much of AC
plain mode settles before the search starts.

Every question the solver asks is a question about the graph as it stands. It reads
members and child classes from a snapshot, and it compares two child positions by
asking whether they are the same class. It never asks whether two terms are equal in
the AC theory.

So a reported optimum is optimal **for the equality relation the graph holds**. From
chapter 13 you know that relation is sound but not complete for AC.

Plain mode already settles most of AC. Every AC fact that is a property of a single
node holds at build time: argument order, flattening, multiplicity, the clamp, the
dropped unit. The solver's AC action generation is AC-aware on top of that, choosing
which child of one multiset pairs with which child of the other by minimum-cost
transport. The gap is the erased class reference of chapter 13: an equality between
two AC nodes that follows from grouping a known sub-sum out of one of them.

## The failure is one-sided, and it is the expensive direction

This section states which way a missing AC consequence moves the reported size, and
why that is the costly direction for a reader.

A missing AC consequence puts two AC-equal subterms in different classes. The solver
then finds no common operator at that position and emits a `Variants` node, priced at
the full hidden mass of both sides. The reported anti-unifier is therefore **larger**
than the AC optimum.

It is never smaller, and it never reports two things equal that are not, because
canonization and congruence only ever assert real AC consequences. So the error has a
direction: the solver over-reports disagreement.

For the diagnosis use that the anti-unification part of this book is about, that is
the expensive direction. A reported difference the theory does not have points a
reader at a part of a formalization that is in fact stable, and tells them to go
look at it.

## Measured

This section runs chapter 13's containment case under all three modes. The case is
wrapped in one common operator so the anti-unifier has a skeleton and the only
candidate disagreement is the AC-equal pair. Under plain congruence:

```lisp
{{#include ../examples/14-au-plain.egg}}
```

```text
(anti-unify :size 5 :cr 0.7500 :completion exact
  (g (Variants n (add c d))))
error: check failed: anti-unifier size 5 exceeds max_size 2
```

The same program with `--derive-ac-eqs`. The rebuild before the snapshot now runs
completion, so `n` and `add(c, d)` are one class by the time the search starts, there
is no position at which the two sides disagree, and the anti-unifier is the shared
term:

```lisp
{{#include ../examples/14-au-eager.egg}}
```

```text
(anti-unify :size 2 :cr 0.0000 :completion exact
  (g n))
ok — 9 nodes
```

Size 5 became size 2 and the `Variants` node is gone. The solver is the same in
both runs, and the only difference is the equality relation it read.

## Lazy completion does not help

This section runs the same program under `--lazy-ac-eqs`, gives the reason the result
matches plain mode, and states what routing lazy completion to the solver would take.

The same program a third time, with `--lazy-ac-eqs`:

```lisp
{{#include ../examples/14-au-lazy.egg}}
```

```text
(anti-unify :size 5 :cr 0.7500 :completion exact
  (g (Variants n (add c d))))
error: check failed: anti-unifier size 5 exceeds max_size 2
```

The result is identical to plain mode, including the compression ratio.

The reason is the trigger from chapter 13. Lazy completion opens its transaction only
for `(check (= a b))` and `(check (!= a b))`. `antiunify` and `checkau` are not
equality checks, so they close any open transaction, which restores the graph and
discards whatever completion derived, and only then does the solver take its
snapshot. The snapshot it searches is the plain graph.

Routing lazy completion to the solver is not a local change. Lazy mode is
goal-directed: it installs one pair as the completion goal and stops the closure the
moment that pair joins, which is what makes it cheap. The solver has one search node
per reachable ordered class pair and no single pair to install, because determining
which pairs matter is what the search does. A lazy variant would be one goal-directed
completion search per visited pair, each inside its own mark and restore, discarding
between pairs exactly the accumulated state that makes consecutive equality checks
cheap.
Eager completion pays the closure once for the whole graph and hands the solver a
snapshot it can read directly.

## The rule

This section states the rule the three measurements give, then two limits on it.

The three modes are not three points on one speed axis. **Plain and lazy hand the
solver the same relation. Only eager changes what the answer means.**

So: if you are anti-unifying over AC operators and you care whether a reported
difference is real, run with `--derive-ac-eqs`. Otherwise the solver's optimality
claim is about a weaker equality than the one you have in mind, and it will
over-report.

Two limits on that, one on eager and one on plain. Eager completion does not make the
solver complete for AC in
general; it makes it complete relative to the closure the engine implements, whose
open obligations are in the design chapter. And plain mode is not useless for AC: a
workload with no asserted equations between AC nodes has no gap to close, and
canonization was doing the AC work all along.

The three sizes above are pinned exactly as a regression test in
[`egraph/tests/au_ac_completion_modes.rs`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/tests/au_ac_completion_modes.rs),
and the argument in full, including why the search shape rules out the lazy variant,
is
[`19-anti-unification.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md)
§2.8.
