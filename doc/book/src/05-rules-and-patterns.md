# Rules and patterns

> Chapter contents: the three rule forms, matching and binding over every operator
> representation, rule actions and modifiers, variadic remainders and
> multiplicities, and sequence, multiset, and set comprehensions.
>
> Examples: `examples/05-rewrite-rules.egg`, the other `05-*.egg` rule fixtures,
> and one variadic fixture per representation: `05-rules-over-seq.egg`,
> `05-rules-over-mset.egg`, and `05-rules-over-set.egg`.
>
> Sources: design `09-pattern-matching.md`, `12-rule-application.md`,
> `07-leapfrog.md`, and the "Variadic Pattern Matching" section of
> `A1-language-guide.md`.
>
> Carry over: `v1-draft/02-first-program.md` section "Rewrite rules" and
> `v1-draft/10-commands.md` section "Rules".

## The grammar

Semper has three surface forms for defining rules. The first sections use
fixed-arity patterns over ordinary operators. The final section applies the
same forms to sequence, multiset, and set operators and introduces the
additional variadic pattern and right-hand-side syntax.

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
{{#include ../examples/05-rewrite-rules.egg:pattern-matching}}
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
{{#include ../examples/05-rewrite-directions.egg:rewrite-directions}}
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

A `rule` separates a conjunctive query from the actions performed for each
match. Every pattern in the first list must match under one shared binding
environment. A variable appearing in several patterns is a join key. Unlike
`rewrite`, a `rule` has no distinguished root and performs no implicit merge.

```lisp
{{#include ../examples/05-rule-actions.egg:rule-actions}}
```

The shared `y` requires the destination of the first edge and the source of
the second to belong to the same e-class. For that match, the bare
`(path x z)` action inserts a term. The following rewrite can fire only
because that term was inserted. The `union` action builds its two arguments
and merges their e-classes.

Actions execute in source order:

| Action | Effect |
| --- | --- |
| `(union lhs rhs)` | Build both right-hand-side terms and merge their e-classes. |
| `(operator rhs ...)` | Build and insert a term without merging it. |
| `(set (operator rhs ...) value)` | Reserved for a lattice-valued update. |

`set` is parsed, sortchecked, and compiled, but its runtime implementation is
currently a `todo!`. A rule that reaches it stops with an unimplemented-action
panic, so it is not yet usable in executing programs.

## Guards

A `:when` clause adds conjuncts to a rewrite's query. Every guard pattern must
match under the same binding environment as the left-hand side. On a
`birewrite`, the same guards apply in both directions.

A guard with no shared variables is an independent conjunct. Operationally,
its matches form a Cartesian product with the left-hand-side matches. The
existence of one such match therefore enables the rewrite, while several
matches may cause the actions to be applied more than once. This is useful for
representing an ambient domain assumption.

The following example uses `--types machine`:

```lisp
{{#include ../examples/05-guards.egg:guards}}
```

Before `(assumption)` is inserted, the first rewrite cannot fire. Once that
unrelated fact exists, it enables the rewrite for `waiting`. A fact inserted
between runs is visible when the next run builds its matching index; a fact
produced during a round becomes visible in a later round.

The second guard is a primitive predicate. It is evaluated over literal values
rather than matched against an e-node. Here `(num n)` binds `n` to an `i64`
value, and `i64::<` keeps only the match for `3`.

A primitive predicate must be a top-level guard, may read only literal values
bound by earlier patterns, and must return `bool`. Its result is tested and
discarded without inserting a node. A general `rule` places the same pattern
and predicate guards directly in its first list rather than using `:when`.

## Subsumption and rule sets

Subsumption is useful when a rule represents a one-way transition: the old
e-node remains in the e-graph, but no longer triggers rules in later matching
indexes.

Rulesets partition rules into explicitly selected groups. A named ruleset must
be declared before it is used, and `:ruleset name` assigns a `rewrite`,
`birewrite`, or general `rule` to it. `(run name n)` runs only rules assigned
to that named set for at most `n` iterations. A bare `(run n)` runs only
untagged rules, which form the default ruleset.

```lisp
{{#include ../examples/05-subsumption-rulesets.egg:subsumption-rulesets}}
```

The first run selects `simplify`, so only the tagged rewrite fires. It merges
`value` with `(reduced item)` and subsumes the matched `(old item)` node. The
untagged rewrite to `final` does not participate in that run.

The bare second run selects the default ruleset. It can rewrite
`(reduced item)` to `(final item)`, but it cannot use the subsumed
`(old item)` node to produce `(stale item)`. Named rulesets are not implicitly
included in a default run; each run selects exactly one ruleset.

## Rules over variadic operators

> This section is the complete user-facing reference for rules over associative
> sequence, associative-commutative multiset, and
> associative-commutative-idempotent set operators. The three example files named
> in the chapter metadata are its spine.

### Why a variadic pattern is different

> A fixed-arity pattern binds argument positions. A flattened sequence, multiset,
> or set has a variable number of children, so a pattern selects part of that
> collection and must account for the remainder. Explain that one pattern can
> consequently produce several matches against one node, and show the count.

### Binding the remainder

> `..rest` binds every child the pattern did not name and can be spliced back into
> the right-hand side. Show a rule that names part of a node and reconstructs it
> with the remainder intact.

### Patterns over a sequence

> Build on `examples/05-rules-over-seq.egg`. Order is represented, so verify and
> explain that the fixed children match a contiguous window. Show what prefix and
> suffix rest variables mean at the front, back, and middle of a sequence.

### Patterns over a multiset

> Build on `examples/05-rules-over-mset.egg`. The full multiplicity surface applies:
> `x:2` requires exactly two copies, `x:k` binds the count, and `x:k>=2` constrains
> it. Include a rule that finds a given sub-sum regardless of the other summands,
> and state that a binding consumes the child's whole multiplicity.

### Patterns over a set

> Build on `examples/05-rules-over-set.egg`. Every multiplicity is one, so explain
> which qualifiers are meaningless and how two named variables bind distinct
> children.

### Right-hand-side splicing and comprehensions

A rest binding can be copied unchanged with `..rest`. Under the same operator,
this reconstructs the unmatched sequence, multiset, or set without naming its
elements individually.

Comprehensions transform those elements while splicing their results into the
surrounding application:

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-forms}}
```

A sequence comprehension uses `..[...]` and visits its source in order. A set
comprehension uses `..{...}` and visits each distinct member once. A multiset
comprehension also uses braces, but requires both multiplicity annotations:
`body:output-count` and `element:source-count`. It visits each distinct child
once while exposing that child's complete multiplicity. Using `count` as the
output count in the example preserves every source multiplicity.

An optional `if` evaluates an RHS term for each source element. The body is
emitted only when that evaluation returns a literal value which the active
literal model considers truthy.

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-filter}}
```

The filter above calls the Rust primitive `i64::<` with `threshold`, a literal
value bound on the LHS, and `count`, the current source multiplicity. It keeps
the children whose count is greater than one.

A comprehension filter is not an e-graph query. Semper rejects an ordinary
application such as `(Keep element)` because it constructs an e-node rather
than computing a literal:

```lisp
{{#include ../examples/05-illegal-comprehension-filter.egg:illegal-comprehension-filter}}
```

To require a graph fact, bind the element on the LHS and add `(Keep element)`
as a rewrite guard or as a conjunct of a general `rule`.

Comprehension binders are lexical. The source is resolved in the enclosing
environment. The element and source-count names then shadow outer names inside
the body, output count, and filter. They disappear afterward, leaving the outer
bindings unchanged.

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-scope}}
```

Sibling and nested comprehensions may reuse binder names. Within one multiset
comprehension, the element and count must have different names: `for k:k` is
rejected.

Output counts are literals, bound multiplicities, or checked expressions using
`u64::+`, `u64::-`, `u64::*`, `u64::/`, `u64::%`, `u64::min`, and
`u64::max`. A local source count lies in `[1, u64::MAX]`, so subtracting one is
valid:

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-count}}
```

An output count of zero omits the element without evaluating its body.
Subtraction that might underflow and division or remainder by a possibly zero
value are rejected when the rule is installed. LHS constraints such as
`x:k>=2` narrow query multiplicity intervals and can make otherwise unsafe
expressions valid. Addition and multiplication remain checked at runtime.

A bound multiplicity can also appear wherever an `i64` term or primitive
argument is expected. For example, `(Count count)` converts the count to an
`i64` term, while `(Count (i64::+ count offset))` uses it in a primitive
calculation.

### What a variadic rule cannot say

Semper's AC matcher uses maximum-partition matching, not unrestricted classical
AC matching. Each scalar pattern element binds one distinct stored child and
consumes that child's entire multiplicity. The rest variable receives every
unbound child, also with its complete multiplicity.

```lisp
{{#include ../examples/05-variadic-limits.egg:variadic-limits}}
```

The exact pattern `(Add x:1 y:1)` does not match `Add{a:2}`. The subject has
one distinct child with multiplicity two, not two children that `x` and `y`
can bind separately. The multiplicity variant `(Add x:k>=2 ..rest)` handles
that case.

A pattern also cannot split `a:5`, consuming two copies while leaving three in
`..rest`. It must bind the complete count and reconstruct the required number
of copies on the RHS with an expression such as `(u64::- k 2)`.

Scalar variables range over existing e-classes. They do not range over
implicit sub-sums or arbitrary subsets of a flattened node. Matching
`(Add x:1 y:1)` against a node containing only `Add(a,b,c)` cannot bind `x`
to an unmaterialized `Add(a,b)`. Such a subterm must already have an e-class,
be constructed by another rule, or be expressed by naming individual children
and a rest variable.

Sequence patterns may have one prefix and one suffix rest variable because
their fixed children describe a contiguous window. AC and ACI patterns are
unordered and permit only one remainder. Comprehensions likewise iterate an
LHS rest binding of the required collection kind; they cannot iterate an
arbitrary RHS term.
