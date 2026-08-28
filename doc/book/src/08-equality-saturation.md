# Equality saturation

Equality saturation repeatedly matches and applies rules, rebuilds the e-graph,
and stops at an operational fixpoint, a goal, or an iteration bound. This chapter
defines that round order, the forms of `run`, extraction, and run statistics.

## A round

Before a run with an `:until` goal starts, Semper builds the two ground goal
terms. Each iteration then performs these operations in order:

1. Rebuild the e-graph, then test the goal against the current union-find.
2. Build an immutable full index and its scheduling statistics.
3. Process the selected rules in declaration order. For each rule, schedule and
   collect its matches against the index, then apply its actions.
4. Recycle the index and test whether the action counter is zero.

The index represents the graph immediately after step 1. Nodes and canonical
forms produced by rule actions are therefore available to matching in the next
iteration, after another rebuild and index construction. A rule's matches are
collected before any of that rule's actions run.

The first example needs several rounds because each recursive rewrite creates the
next `dbl` application that can match.

{{#include ../examples/08-saturation.egg:saturation}}

The first one-round run cannot finish `d2`. Two more rounds derive `d2 = four`.
The final run requests ten iterations but reaches its operational fixpoint after
three.

The complete rule-application procedure is specified in
[design chapter 12](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/12-rule-application.md).

## Saturation

A run reports saturation when an iteration's action counter is zero. A union
counts only when it merges two previously distinct classes. An insert counts
whenever its action is applied, even when hash-consing finds an existing node,
and a subsume action also counts whenever it is applied. A repeatedly matching
insert or subsume rule can therefore keep `saturated` false without increasing
the graph.

This is an operational fixpoint of the selected declared rules and the current
driver. It is not a completeness result for an unstated theory. A law that was
neither declared as an algebraic property nor encoded by a rule is absent.
Likewise, a successful `(check (!= a b))` says only that `a` and `b` currently
belong to different classes.

If the iteration bound is reached first, the run stops with `saturated: false`.
The e-graph retains everything derived so far, and subsequent checks inspect that
partial result.

## The forms of `run`

The four common forms select a budget, an optional ruleset, and an optional
goal:

| Form | Effect |
| --- | --- |
| `(run n)` | Run the untagged default ruleset for at most `n` iterations. |
| `(run ruleset n)` | Run only rules tagged with that declared ruleset. |
| `(run n :until (= a b))` | Stop when the two ground terms join. |
| `(run n :until (!= a b))` | Stop when the two ground terms are in different classes. |

A named run may also carry either `:until` goal. Each run selects exactly one
ruleset. It does not combine the named ruleset with untagged rules.

{{#include ../examples/08-run-forms.egg:run-forms}}

The goal is tested after rebuild and before matching in the first and every
later iteration. It is rebuilt and tested once more after the final permitted
round. A goal that already holds still costs zero iterations. An equality goal
can become true as classes merge. An inequality goal either succeeds initially
or cannot become true during that run: saturation merges classes and never
splits them. `:until (!= ...)` records no permanent disequality constraint.

## Runs that do not saturate

Some rules generate a fresh term at every iteration. The `up` rewrite below can
keep extending its argument, so increasing the iteration bound keeps exposing
more work. An equality goal stops this run as soon as the requested depth has
joined the starting term.

{{#include ../examples/08-saturation.egg:until-goal}}

The practical control is always a finite iteration bound, optionally combined
with an equality goal, followed by checks for the facts the program requires.
A run that repeatedly reaches its budget should be treated as a property of the
rule set, not as evidence that Semper will eventually choose to stop.

## Extraction

`(extract t)` rebuilds the graph and prints a lowest-cost ground term from
`t`'s e-class. It uses the per-operator costs and exclusions introduced in
Chapter 3. Costs are additive over the root and children, including each
occurrence represented by a multiplicity.

{{#include ../examples/08-extraction.egg:extraction}}

The class in this example contains `(expensive)`, `(hidden)`, and
`(wrap (unit))`. Extraction prints `(wrap (unit))`: its cost is 2,
`(expensive)` costs 5, and `(hidden)` is not a candidate.

A cycle is not itself an error when its class also has an extractable grounded
member. Extraction fails when no candidate has a fully extractable child set.
It reports a more specific error when every node in the requested class is
marked `:unextractable`.

{{#include ../examples/08-extraction-failure.egg:extraction-failure}}

Extraction chooses one representative of one e-class. Anti-unification compares
two e-classes and is introduced in Part III. The extraction algorithm and its
failure cases are specified in
[design chapter 16](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/16-extraction.md).

## Statistics

`(print-stats)` prints the current node and class counts followed by the most
recent run's iteration count, match-step count, wall time, saturation flag, and
goal flag. `(print-stats :file "path.json")` writes the same fields as JSON.
The match-step count includes executed lowered matching steps and emitted
matches. It is an implementation work measure, not a semantic match count.

`print-stats` does not rebuild the e-graph. Its node and class fields describe
the graph when the command executes, while the remaining fields still describe
the last run. The presence of a `print-stats` command enables match-step
counting for that program.

Under the naive strategy selected by the saturation fixture, the first printed
reading is 23 nodes, 9 classes, 3 iterations, and 111 match steps, with
saturation true. The goal-directed run then reports 30 nodes, 10 classes,
3 iterations, and 144 match steps, with `goal-met` true and saturation false.
Wall time depends on the machine and run.

The interpreter's command behavior and statistics fields are specified in
[design chapter 17](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/17-interpreter.md).
