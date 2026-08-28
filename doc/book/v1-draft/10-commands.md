# Commands

This chapter is the command reference, in seven groups: declaring sorts and
operators, building terms, writing rules, running saturation, asserting, querying,
and scoping with `push` and `pop`.

A program is a sequence of commands, executed in order. Declarations must
precede the terms that use them; there is no forward reference and no separate
declaration pass.

Comments run from `;` to end of line.

## Declaring

This section lists the declaration commands and the tags they accept.

| command | effect |
| --- | --- |
| `(sort S)` | declare an uninterpreted sort `S` |
| `(function f (S1 ... Sn) S :tag*)` | declare an operator, arguments then result |
| `(constructor f (S1 ... Sn) S :tag*)` | same, marked as a constructor |
| `(datatype T (C1 S ...) ...)` | declare a sort and its variants in one command |
| `(ruleset r)` | declare a rule set name for `:ruleset r` |

An operator declared with an algebraic attribute is **variadic** or **binary**
according to that attribute, and its declared argument list must have the
matching length. [Chapter 3](03-algebra.md) has the legality table.

Declaration tags:

```text
:assoc-comm-idem | :assoc-comm | :assoc | :assoc-left | :assoc-right | :comm
:idempotent | :nilpotent int? | :identity term | :cancellative | :inverse ident
:cost int | :unextractable
```

`:cost` and `:unextractable` affect `extract`, not equality.

## Building terms

This section lists the three ways to put a term into the e-graph.

| command | effect |
| --- | --- |
| `(let x t)` | insert `t`, bind `x` to its e-class |
| `(union t1 t2)` | assert that the two terms are equal |
| `(f a b)` | insert a ground term without naming it |

A bare term at top level is sugar for insertion. It is how you populate the
e-graph with the terms a rule should fire on when you do not need a name.

## Rules

This section gives the three rule forms, the action grammar, the two modifiers,
and the variadic pattern surface.

```text
(rewrite  lhs rhs :when (pattern*)? :subsume? :ruleset r?)
(birewrite lhs rhs :when (pattern*)? :ruleset r?)
(rule (pattern*) (action*) :ruleset r?)
```

`rewrite` is one direction, `birewrite` both. `rule` is the general form: a
conjunctive query over the e-graph, then actions.

```text
action = (union rhs rhs) | (set (f rhs*) rhs) | (f rhs*)
```

`:when` adds guard patterns that must also match. `:subsume` marks the matched
term unusable by later rules, and is not accepted on `birewrite`.

Patterns support variadic matching against AC operators: `..rest` binds the
remaining children, `x:2` requires multiplicity exactly 2, `x:k` binds the
multiplicity, `x:k>=2` constrains it. The right-hand side can splice with
`..rest` and with set, multiset and sequence comprehensions. `A1-language-guide`
section "Variadic Pattern Matching" is the reference for that surface.

## Running

This section gives the four forms of `run` and states what saturation is a
fixpoint of.

```text
(run n)
(run ruleset n)
(run n :until (= t1 t2))
(run n :until (!= t1 t2))
```

Applies rules for at most `n` rounds, stopping early on saturation or when the
`:until` condition holds. Saturation is a fixpoint of the declared rules, not of
the theory: a rule you did not write does not fire.

## Asserting

This section lists the four assertion forms and enters one caution about `!=`.

| command | passes when |
| --- | --- |
| `(check (= t1 t2))` | the two terms are in the same e-class |
| `(check (!= t1 t2))` | they are not |
| `(check t)` | `t` is present in the e-graph |
| `(checkau t1 t2 ... :max_size n)` | the anti-unifier's size is at most `n` |

A failed check aborts the program with exit status 1. This is what makes an
example file a test: every example in this book ends in checks, and the test
suite runs them.

`(check (!= t1 t2))` deserves a caution. It passes when the engine has not
derived equality, which is a statement about what the declared rules proved, not
about semantic disequality. Under `--lazy-ac-eqs` it additionally means a
goal-directed completion search reached its fixpoint without deriving equality.

## Querying

This section lists the commands that print, and the options the two
anti-unification commands share.

| command | prints |
| --- | --- |
| `(extract t)` | a lowest-cost term from `t`'s e-class |
| `(antiunify t1 t2 au_option*)` | the anti-unifier |
| `(checkau t1 t2 ...)` | the anti-unifier, and asserts its size |
| `(print-size)` / `(print-size f)` | e-node count, total or for one operator |
| `(print-stats)` / `(print-stats :file "p.json")` | saturation statistics |

```text
au_option = :algorithm (exact | uct) | :cycles (sides | sides-current | pair)
          | :playouts int
```

[Chapter 5](05-anti-unification.md) covers the options and the output fields.

## Scoping

This section gives the scoping commands, states what a scope costs, and names the
use this book makes of them.

```text
(push)
(push :shrink)
(pop)
```

`push` opens a scope and `pop` discards everything asserted since. This is the
semi-persistent mechanism the project is named for: `pop` replays an undo log
rather than restoring a copy, so a scope costs what was done inside it rather
than the size of the e-graph. `:shrink` additionally releases the memory the
scope grew into, which trades the cost of shrinking for a lower footprint after
the pop.

The relevant use for this book is speculative work: push, assert a candidate
completion, check what it implies, pop, and try the next one, on the same
e-graph.
