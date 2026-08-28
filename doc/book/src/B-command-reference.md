# Annex B. Command reference

This annex is a compact index of Semper's commands. Follow the chapter links
for semantics and [Annex A](A-full-grammar.md) for the complete grammar.

## Symbol declarations and algebraic properties

| Command | Effect |
| --- | --- |
| `(sort S)` | Declare an uninterpreted sort `S`. |
| `(function f (S1 ... Sn) S :tag*)` | Declare an operator with result sort `S`. |
| `(constructor f (S1 ... Sn) S :tag*)` | Declare the operator as a constructor. |
| `(datatype T (C S ... :tag*) ...)` | Declare `T` and one constructor per variant. |
| `(ruleset r)` | Declare a ruleset name for `:ruleset r` and `(run r n)`. |

Algebraic properties are attached to operator declarations and individual
datatype variants as tags. They determine an operator's representation and
required arity. [Chapter 4](04-declaring-algebra.md) gives their laws, legal
combinations, and exact arity rules. [Chapter 3](03-sorts-and-terms.md)
defines the extraction tags. Annex A contains the complete declaration grammar.

## Building terms

| Command | Effect |
| --- | --- |
| `(let name term)` | Insert `term` and bind `name` to its e-class. |
| `(union left right)` | Insert both terms and merge their e-classes. |
| `(f a b)` | Insert a ground application without naming it. |

A bare operator application at top level is an insertion command. A name
introduced by `let` denotes the resulting e-class and may be used wherever a
ground term is accepted. [Chapter 3](03-sorts-and-terms.md#building-a-term)
explains term construction in detail.

## Rules

| Command | Effect |
| --- | --- |
| `(rewrite lhs rhs tags...)` | Match `lhs`, build `rhs`, and merge it with the matched root class. |
| `(birewrite lhs rhs tags...)` | Install one rewrite in each direction. Both sides use pattern syntax. |
| `(rule (pattern...) (action...) tags...)` | Run a conjunctive query and execute its actions for every match. |

| Modifier | Accepted by | Effect |
| --- | --- | --- |
| `:when (pattern...)` | `rewrite`, `birewrite` | Add conjuncts to the query. A primitive predicate here computes over bound literal values. |
| `:subsume` | `rewrite` | After applying the rewrite, hide the matched e-node from future pattern indexes. |
| `:ruleset r` | all three forms | Put the installed rule in declared ruleset `r` instead of the default ruleset. |

Modifiers may appear in any order. `birewrite` rejects `:subsume`; a general
`rule` puts guards in its query list and accepts only `:ruleset` as a trailing
modifier.

### General-rule actions

| Action | Effect |
| --- | --- |
| `(union lhs rhs)` | Build both RHS terms and merge their classes. |
| `(f rhs...)` | Build and insert an application. RHS splices and comprehensions are accepted in its variadic children. |
| `(set (f rhs...) value)` | Reserved syntax. It parses, but execution is not implemented. |

[Chapter 5](05-rules-and-patterns.md) defines pattern matching, multiplicities,
rest variables, comprehensions, modifiers, and action ordering.

## Running rules and scopes

| Command | Effect |
| --- | --- |
| `(run n)` | Run the untagged default ruleset for at most `n` iterations. |
| `(run r n)` | Run only declared ruleset `r` for at most `n` iterations. |
| `(run n :until (= a b))` | Stop early when `a` and `b` join. A named run may use the same goal. |
| `(run n :until (!= a b))` | Stop early when the two terms are in different classes. This does not assert a persistent disequality. |
| `(push)` | Record a semi-persistent scope. |
| `(push :shrink)` | Reclaim sufficiently overallocated storage, then record a scope. |
| `(pop)` | Restore the most recent scope, including e-graph, installed-rule, and runtime-name state. |

A run selects exactly one ruleset. [Chapter 8](08-equality-saturation.md)
defines round ordering, stopping, and statistics. [Chapter 7](07-semi-persistence.md)
defines scope lifetime and `:shrink`.

## Checks, extraction, and statistics

| Command | Effect |
| --- | --- |
| `(check term)` | Build `term`. This form has no additional truth or equality test. |
| `(check (= a b))` | Rebuild and require `a` and `b` to belong to the same e-class. |
| `(check (!= a b))` | Rebuild and require the terms to belong to different e-classes under the selected completion mode. |
| `(extract term)` | Rebuild and print a lowest-cost extractable representative. |
| `(print-size)` | Print nonzero per-operator e-node counts and the total. |
| `(print-size f)` | Print the e-node count for operator `f`. |
| `(print-stats)` | Print current graph counts and the most recent run's counters. |
| `(print-stats :file "path.json")` | Write the same statistics as JSON. |

[Chapter 8](08-equality-saturation.md) defines extraction and statistics.
[Chapter 11](11-three-congruence-closures.md) explains how the completion mode
affects equality and disequality checks.

## Anti-unification

| Command | Effect |
| --- | --- |
| `(antiunify left right options...)` | Compute and print an anti-unifier. |
| `(checkau left right options...)` | Compute the same result and fail if its size exceeds `:max_size`; print nothing on success. |

| Option | Values | Default | Effect |
| --- | --- | --- | --- |
| `:algorithm` | `uct`, `exact` | `uct` | Select budgeted graph search or exhaustive exact search. |
| `:playouts` | unsigned integer | `1000` | Set the UCT playout budget. Exact search does not use it. |
| `:cycles` | `sides`, `sides-current`, `pair` | `sides` | Select the cycle-context policy defined in Chapter 14. |
| `:max_size` | unsigned 32-bit integer | `u32::MAX` (`4294967295`) | Set the inclusive upper bound checked by `checkau`; unavailable on `antiunify`. |

[Chapter 12](12-what-anti-unification-is.md) defines the result and size bound.
[Chapters 14](14-exact-algorithm.md) and [15](15-graph-search.md) define the
algorithms, cycle modes, and playout budget.
