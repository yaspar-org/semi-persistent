# Rules and patterns

> Chapter contents: the grammar of the three rule forms, what a pattern matches
> against, how variables bind, what actions may do, the two modifiers, and rule
> sets. Variadic patterns over AC operators are chapter 13, not here: this chapter
> covers ordinary fixed-arity operators only, and should say so once.
>
> Example: `examples/04-rewrite-rules.egg`.
>
> Sources: design `09-pattern-matching.md`, `12-rule-application.md`,
> `A1-language-guide.md`.
>
> Carry over: `v1-draft/02-first-program.md` section "Rewrite rules" and
> `v1-draft/10-commands.md` section "Rules".

## The grammar

Semper has three surface forms for defining rules. This chapter uses only
fixed-arity patterns over ordinary operators; chapter 13 introduces variadic
patterns over operators with algebraic properties.

```text
(rewrite lhs rhs [:when (pattern ...)] [:subsume] [:ruleset name])
(birewrite lhs rhs [:when (pattern ...)] [:ruleset name])
(rule (pattern ...) (action ...) [:ruleset name])

action = (union rhs rhs)
       | (set (operator rhs ...) rhs)
       | (operator rhs ...)
```

Square brackets mark optional syntax. The trailing modifiers on `rewrite` and
`birewrite` may appear in any order. `:subsume` is accepted only by `rewrite`.
A `rule` puts all its query patterns directly in the first parenthesized list,
followed by its actions in the second; its only trailing modifier is
`:ruleset`.

The `set` action is part of the surface grammar, but rule application does not
implement it yet, so it cannot currently be used in an executing program.
[Annex A](A-full-grammar.md) gives the complete grammar, including the
variadic pattern and right-hand-side forms omitted here.

## What a pattern matches

A Semper pattern matches the e-graph, not a single syntax tree. Each operator
must be witnessed by an e-node, but its children are e-classes. A nested
pattern may therefore continue through any e-node in a child class, even when
the resulting composite term was never inserted.

```lisp
{{#include ../examples/04-rewrite-rules.egg:pattern-matching}}
```

The program never inserts `(f (g b))`. It inserts `(f a)` and `(g b)`, then
places `a` and `(g b)` in the same e-class. The pattern `(f (g x))` can
therefore match `outer`, binding `x` to `b`'s e-class.

Pattern variables also bind e-classes rather than particular syntax. In
`(pair x x)`, one occurrence binds `x` and the other requires the same
e-class. Although `a` and `inner` are written differently, their union allows
`pair_term` to match.

## rewrite and birewrite

A `rewrite` is directional in what triggers it, not in the equality it
establishes. When its left-hand side matches, Semper builds the right-hand side
and merges it with the matched e-class. After that merge the equality is
symmetric, but an existing right-hand-side shape does not cause the
left-hand side to be built.

```lisp
{{#include ../examples/04-rewrite-directions.egg:rewrite-directions}}
```

The first rule uses `(f a)` to build `(g a)`. It does not use `(g b)` to build
`(f b)`. A `birewrite` is parser shorthand for two rewrites, one in each
direction. Consequently, `(f a)` builds `(h a)`, while `(h c)` builds `(f c)`.

Neither form replaces or deletes its input. Ordinary rewrites leave the
matched left-hand-side node available to later rules, while adding nodes and
equalities monotonically.

Adding `:subsume` performs the same build and merge, then marks the matched
left-hand-side e-node so future pattern indexes skip it. The node and its
equality remain in the e-graph, and subsumption does not prevent extraction
or hide other nodes in its e-class. Matches already collected for the current
rule application still run. `birewrite` rejects `:subsume`, since each side
must remain available to trigger the opposite direction.

## rule and actions

> The general form: a conjunctive query over the e-graph, then actions. Show a rule
> with two patterns whose shared variable is the join. Give each action form once:
> `union`, `set`, and a bare term as an insertion.

## Guards

> `:when` adds patterns that must also match. Show a rule that fires only in the
> presence of an unrelated fact, since that is the shape a domain assumption takes
> in Part IV.

## Subsumption and rule sets

> `:subsume` marks the matched term unusable by later rules and is not accepted on
> `birewrite`. `(ruleset r)` plus `:ruleset r` names a group so that `(run r n)` can
> run it alone. Show one use of each. State what `:subsume` is for in one sentence
> and do not develop it: nothing else in the book uses it.
