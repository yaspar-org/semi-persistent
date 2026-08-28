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

> The point a reader coming from term rewriting needs: a pattern is matched against
> the e-graph, so it matches an e-class whenever any e-node in that class matches,
> and one rule can therefore fire on a term nobody wrote. Show it: insert two terms,
> union them, and have a rule fire through the union.
>
> State that a variable binds to an e-class, and that repeating a variable in a
> pattern requires the same class in both positions rather than the same syntax.

## rewrite and birewrite

> `rewrite` adds the right side to the matched class in one direction, `birewrite`
> in both. Show each. State that neither deletes anything: the left side stays in
> the graph, which is what makes saturation monotone and is why `(check (!= ...))`
> means what chapter 5 says it means.

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
