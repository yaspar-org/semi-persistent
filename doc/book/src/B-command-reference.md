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
| `(rewrite (op ... (..g P) ..rest) rhs tags...)` | A sequence rewrite: filters `(..g P)` and bare sequences `..name` over the children of an `:assoc`, `:assoc-comm`, or `:assoc-comm-idem` root ([Chapter 5](05-rules-and-patterns.md#sequence-patterns)). It accepts `:let`, `:when`, `:flatten`, and `:ruleset`. |

| Modifier | Accepted by | Effect |
| --- | --- | --- |
| `:when (pattern...)` | `rewrite`, `birewrite` | Add conjuncts to the query. A primitive predicate here computes over bound literal values. |
| `:when (expr...)` | sequence `rewrite` | Require each right-hand-side expression, computed over the matched sequences, to be `true`. |
| `:subsume` | ordinary `rewrite` | After applying the rewrite, hide the matched e-node from future pattern indexes and from extraction under a cost model. |
| `:let ((x e)...)` | sequence `rewrite` | Name values computed from the matched sequences, for the right-hand side and `:when`. |
| `:flatten` | all four forms | Match every associative, AC, or ACI operator of the pattern on the flattened form of a node, where a child class holding a node of the same operator contributes that node's children. Nothing stored changes. At most once per rule. On a rule without such an operator it has no effect and raises a warning; a `:comm` operator does not count. |
| `:ruleset r` | all four forms | Put the installed rule in declared ruleset `r` instead of the default ruleset. |

Modifiers may appear in any order. `birewrite` rejects `:subsume`, and so does a
sequence rewrite. A general `rule` puts guards in its query list and accepts
only `:flatten` and `:ruleset` as trailing modifiers.

### General-rule actions

| Action | Effect |
| --- | --- |
| `(union lhs rhs)` | Build both RHS terms and merge their classes. |
| `(f rhs...)` | Build and insert an application. RHS splices and comprehensions are accepted in its variadic children. |
| `(set (f rhs...) value)` | Reserved syntax. It parses, and the sort checker rejects it as not implemented. |

[Chapter 5](05-rules-and-patterns.md) defines pattern matching, multiplicities,
rest variables, comprehensions, modifiers, and action ordering.

## Running rules and scopes

| Command | Effect |
| --- | --- |
| `(run n)` | Run the untagged default ruleset for at most `n` iterations. |
| `(run r n)` | Run only declared ruleset `r` for at most `n` iterations. |
| `(run n :until fact ...)` | Stop early, before a round, once the facts have a match, as `check` would find one. In lazy AC mode the goal is evaluated without completion, so completion can only delay the stop. |
| `(run n :goal (= a b))` | Build `a` and `b` once, then stop early when they join. A named run may use the same goal. |
| `(run n :goal (!= a b))` | Stop early when the two terms are in different classes. This does not assert a persistent disequality. |
| `(push)` | Record a semi-persistent scope. |
| `(push :shrink)` | Reclaim sufficiently overallocated storage, then record a scope. |
| `(pop)` | Restore the most recent scope, including e-graph, installed-rule, and runtime-name state. |

A run selects exactly one ruleset. [Chapter 8](08-equality-saturation.md)
defines round ordering, stopping, and statistics. [Chapter 7](07-semi-persistence.md)
defines scope lifetime and `:shrink`.

## Checks, extraction, and statistics

| Command | Effect |
| --- | --- |
| `(check fact ...)` | Rebuild and require the conjunctive query to have a match. The facts are those of a rule body: a pattern, `(= p q)`, `(!= p q)` (the classes differ), or a guard. Literal values are compared by the typed guard, such as `(IBig::!= n m)`, where egglog writes `(!= n m)`. The check builds nothing: a term that was never built has no match. A name that is a global refers to it; any other name is a variable of this one check. |
| `(check fact ... :count k)`, `:min k`, `:none` | Require exactly `k` matches, at least `k`, or none. Matches are counted as distinct assignments of the check's named variables. In lazy AC mode, `:count` and `:none` are decided at the completion fixpoint. |
| `(query fact ... [:limit n])` | Print the matches of the facts, up to `n` (default 10): each named variable as a term extracted from its class. Matches are ordered by content colour, so the output does not depend on class ids. Nothing is built or required. |
| `(set-option :completion off\|eager)` | From this command on, rebuild does (`eager`) or does not run AC completion; turning it on rebuilds at once. Overrides `--derive-ac-eqs` ([Chapter 11](11-three-congruence-closures.md)). |
| `(set-option :check-completion on\|off)` | From this command on, checks complete temporarily to answer while `:completion` is `off` (lazy mode). Overrides `--lazy-ac-eqs`. |
| `... :complete`, `... :no-complete` | After the arguments of `check`, `query`, `check-eq` or `check-neq`: turn check completion on or off for that one command. |
| `(check-eq a b ...)` | Build every term, rebuild, and require them all to belong to one e-class. |
| `(check-neq a b)` | Build both terms, rebuild, and require them to belong to different e-classes under the selected completion mode. |
| `(extract term)` | Rebuild and print a lowest-cost extractable representative. |
| `(cost-model name :script "file.roto")` | Compile a cost script when the program is checked ([Part V](24-extraction-under-cost-models.md)). |
| `(cost-model name :rust "id")` | Name a cost registered in Rust ([Part V](24-extraction-under-cost-models.md)). |
| `(cost-model name :asp "file.lp")` | Name a cost written as answer-set rules over the e-graph's facts, solved by clingo ([Part V](24-extraction-under-cost-models.md)). |
| `(cost-model name :minizinc "file.mzn")` | Name a cost written in MiniZinc, solved through `minizinc` ([Part V](24-extraction-under-cost-models.md)). |
| `(extract term :cost name [:rung r] [:solver s] [:budget n] [:file "f"] [:proof "d"])` | Extract under a cost model, print the cost, its status, and the term ([Part V](24-extraction-under-cost-models.md)). `r` is `selection` (the default), `levels`, `splits`, `binary`, or `orders`. `s` is `internal` (the default), `dpw`, `roundingsat`, `greedy`, `(opb "prog" ...)`, `(asp "clingo" ...)`, or `(minizinc "solver" ...)`. `:proof` needs `roundingsat` or an `opb` solver. |
| `(extract term :cost name :band lo hi [:count n] ...)` | List up to `n` (default 10) terms whose cost lies in `[lo, hi]`, on the internal solver ([Part V](24-extraction-under-cost-models.md)). |
| `(dump-egraph term :file "f")` | Write the whole e-graph as JSON in egglog's format, `term`'s class as the root. Classes and nodes are named and ordered by content colour, so equal e-graphs write equal bytes ([Part V](24-extraction-under-cost-models.md)). |
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
