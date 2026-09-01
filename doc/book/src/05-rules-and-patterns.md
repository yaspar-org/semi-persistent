# Rules and patterns

This chapter defines all three rule forms, fixed and variadic patterns, rule
actions and modifiers, multiplicity constraints, remainder bindings, and
right-hand-side comprehensions.

## The grammar

Semper has three surface forms for defining rules:

```text
(rewrite lhs rhs [:when (pattern ...)] [:subsume] [:ruleset name])
(birewrite lhs rhs [:when (pattern ...)] [:ruleset name])
(rule (pattern ...) (action ...) [:ruleset name])

action = (union rhs rhs)
       | (set (operator rhs ...) rhs)
       | (operator rhs ...)
```

Square brackets mark optional syntax. The trailing modifiers on `rewrite` and
`birewrite` may appear in any order. Only `rewrite` accepts `:subsume`. A
general `rule` puts its query patterns in the first parenthesized list and its
actions in the second. Its only trailing modifier is `:ruleset`.

The `set` action is part of the surface grammar, but rule application does not
implement it yet. A rule that reaches this action stops with an unimplemented
action panic. [Annex A](A-full-grammar.md) gives the complete grammar.

## Fixed-arity patterns

A pattern matches the e-graph rather than one syntax tree. Each application
must be witnessed by an e-node, but the children of that node are e-classes. A
nested pattern may therefore continue through any suitable node in a child
class, even when the complete nested term was never inserted.

```lisp
{{#include ../examples/05-rewrite-rules.egg:pattern-matching}}
```

The program never inserts `(f (g b))`. It inserts `(f a)` and `(g b)`, then
places `a` and `(g b)` in the same e-class. The pattern `(f (g x))` can match
`outer`, binding `x` to `b`'s e-class.

Variables bind e-classes, not one spelling of a term. The repeated variable in
`(pair x x)` is non-linear: its first occurrence binds `x`, and its second
requires the same e-class. The union of `a` and `inner` therefore lets
`pair_term` match.

For an ordinary fixed-arity operator, each pattern child corresponds to one
declared argument position. A literal or nested application constrains that
position. A fresh variable binds it, and a variable already bound elsewhere in
the query checks equality with it.

## `rewrite`, `birewrite`, and `:subsume`

A `rewrite` is directional in what triggers it, not in the equality it
establishes. When the left-hand side matches, Semper builds the right-hand side
and merges it with the matched root class. The equality is then symmetric, but
an existing right-hand-side shape does not cause the left-hand side to be
built.

```lisp
{{#include ../examples/05-rewrite-directions.egg:rewrite-directions}}
```

The first rule uses `(f a)` to build `(g a)`. It does not use `(g b)` to build
`(f b)`. A `birewrite` installs two rewrites, one in each direction. Thus
`(f a)` builds `(h a)`, and `(h c)` builds `(f c)`.

Neither form replaces or deletes its input. An ordinary rewrite leaves the
matched left-hand-side node available to later rules. A rewrite with
`:subsume` performs the same build and merge, then marks that matched e-node so
future pattern indexes skip it. The node remains in its e-class and remains
available to extraction. Matches already collected for the current
application still execute.

`birewrite` rejects `:subsume` because subsuming either trigger would disable
one direction of the installed pair.

## General rules and actions

A general `rule` separates a conjunctive query from the actions performed for
each match. Every pattern in the first list must match under one shared binding
environment. A variable used by several patterns is a join key. Unlike
`rewrite`, a general rule has no distinguished root and performs no implicit
merge.

```lisp
{{#include ../examples/05-rule-actions.egg:rule-actions}}
```

The shared `y` requires the destination of the first edge and the source of the
second to be in the same e-class. The bare `(path x z)` action inserts a term.
The following rewrite can fire only because that term was inserted. The
`union` action builds both arguments and merges their e-classes.

Actions execute in source order:

| action | effect |
| --- | --- |
| `(union lhs rhs)` | Build both right-hand-side terms and merge their e-classes. |
| `(operator rhs ...)` | Build and insert a term without merging it. |
| `(set (operator rhs ...) value)` | Reserved for a lattice-valued update and not implemented. |

## Guards

A `:when` clause adds conjuncts to a rewrite query. Every guard pattern must
match under the same binding environment as the left-hand side. The same
guards are attached to both directions of a `birewrite`. A general `rule`
places equivalent conjuncts directly in its query list.

A guard with no shared variables is independent of the left-hand side. One
matching fact enables the rewrite. Several matching facts may produce several
query rows and apply the same actions more than once.

```lisp
{{#include ../examples/05-guards.egg:guards}}
```

Before `(assumption)` is inserted, the first rewrite cannot fire. Once that
unrelated fact exists, it enables the rewrite for `waiting`. A fact inserted
between runs is visible to the next run. A fact produced during a matching
round becomes visible after the next index build.

The second guard is a primitive predicate rather than an e-node pattern.
`(num n)` binds an `i64` literal value, and `i64::<` keeps only the match for
`3`. A primitive predicate must be a top-level query conjunct, may use literal
values bound by other query patterns, and must return `bool`. Matching
computes and discards its result without inserting a literal node.

## Rulesets

Rulesets partition installed rules into explicitly selected groups. A named
ruleset must be declared before a command refers to it. Adding
`:ruleset name` assigns a `rewrite`, `birewrite`, or general `rule` to it.
Untagged rules belong to the default ruleset.

```lisp
{{#include ../examples/05-subsumption-rulesets.egg:subsumption-rulesets}}
```

The first run selects `simplify`, so only the tagged rewrite fires. It merges
`value` with `(reduced item)` and subsumes the matched `(old item)` node. The
untagged rewrite to `final` does not participate.

The bare second run selects the default ruleset. It can rewrite
`(reduced item)` to `(final item)`, but the subsumed `(old item)` node cannot
produce `(stale item)`. A run selects exactly one ruleset. It does not include
named rulesets implicitly.

## Variadic patterns and remainders

Associative, AC, and ACI declarations produce variadic nodes. Their patterns
do not bind a fixed list of declared positions. They select children from an
ordered sequence, multiset, or set. A rest variable such as `..rest` binds the
children not selected by the fixed pattern elements.

The absence of a rest variable makes the pattern exact. Every stored child
must then be consumed. With a rest variable, one node may produce several
matches as different children satisfy the fixed elements. Splicing `..rest`
on the right-hand side copies the unmatched collection into the new
application.

Chapter 4's singleton collapse also applies to matching. A one-child pattern
such as `(Set x)` has no one-child `Set` node to match. `(Set x ..rest)` binds
one member while allowing the stored node to contain additional members.

### Sequence patterns

An associative-only operator stores an ordered, flattened sequence. Fixed
pattern elements match a contiguous window. A rest variable after them binds
the suffix, one before them binds the prefix, and rests on both sides bind the
prefix and suffix around a sliding window.

```lisp
{{#include ../examples/05-rules-over-seq.egg:sequence-ends}}
```

The front rule binds the first child, while the back rule binds the last.
Changing source order changes both matches.

```lisp
{{#include ../examples/05-rules-over-seq.egg:sequence-window}}
```

The two fixed variables slide across three adjacent pairs in a four-child
sequence. They never match the nonadjacent pair `a,c`. Without either rest
variable, the same two-child pattern would match only a sequence with exactly
two children.

A repeated variable in a sequence pattern constrains positions. For example,
`(Seq ..pre x x ..suffix)` matches two adjacent children in the same e-class.
It does not match equal children separated by another element.

### Multiset patterns

An AC operator stores each distinct child with its multiplicity. Every scalar
pattern element binds one distinct stored child and consumes that child's
whole multiplicity. A bare element has an implicit exact multiplicity of one.
The rest receives all unbound children with their complete multiplicities.

```lisp
{{#include ../examples/05-rules-over-mset.egg:multiset-remainder}}
```

The one node has two matches. Binding `x` to `a` also binds `k` to `3` and
gives `b:2` to `rest`. Binding `x` to `b` binds `k` to `2` and gives `a:3` to
`rest`. The matcher does not leave two copies of the selected child in the
remainder.

Multiplicity annotations have these forms:

| pattern element | accepted multiplicity |
| --- | --- |
| `x` or `x:1` | exactly 1 |
| `x:3` | exactly 3 |
| `x:k` | any positive count, also bind it to `k` |
| `x:k>=2` | bind `k` and require the stated relation |

The relational form accepts `>=`, `>`, `<=`, `<`, `==`, and `!=`. Semper
collects the constraints on each multiplicity variable and reduces them to a
closed interval used during rule installation:

| constraint | interval contribution |
| --- | --- |
| no relation | `[1, u64::MAX]` |
| `k>=n` or `k>n` | `[n, u64::MAX]` or `[n+1, u64::MAX]` |
| `k<=n` or `k<n` | `[1, n]` or `[1, n-1]` |
| `k==n` | `[n, n]` |
| `k!=n` | exclusion checked while matching; interval remains conservative |

Constraints from repeated uses are intersected. An empty intersection rejects
the rule as unsatisfiable. Reusing the same multiplicity variable also makes
it non-linear: all occurrences must bind the same count.

```lisp
{{#include ../examples/05-rules-over-mset.egg:multiplicity-patterns}}
```

The exact rule accepts `a:2` but not `b:1`. The non-linear rule accepts the
node where two distinct children both have count two and rejects the node
whose counts are three and two.

### Set patterns

An ACI operator stores a set, so every represented child has multiplicity one.
A scalar element binds one distinct member. The remainder receives every
unbound member.

```lisp
{{#include ../examples/05-rules-over-set.egg:set-patterns}}
```

The first rule finds `a` and `b` in either source order and reconstructs the
remainder with `d`. The second rule's two variables bind distinct set members.
The repeated-variable rule cannot match because one set member cannot satisfy
two scalar elements.

Multiplicity annotations on set elements are errors, including `x:1`.

```lisp
{{#include ../examples/05-illegal-set-multiplicity.egg:illegal-set-multiplicity}}
```

Use an AC operator when a rule needs to observe or constrain counts.

## Multiplicities on the right-hand side

A multiplicity bound on the left-hand side can be used as an `i64` term or as
an argument to an `i64` primitive. This conversion constructs an ordinary
literal term on the right-hand side:

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:multiplicity-as-term}}
```

The query binds `count` to three. `(Count count)` constructs the literal term
`Count(3)`, while the primitive expression constructs `Count(13)`.
Multiplicity variables are accepted only where an `i64` value is expected.

A child of a variadic right-hand side may also carry an output multiplicity:
`term:count`, `term:2`, or `term:(u64::- count 1)`. Multiplicity expressions
use `u64::+`, `u64::-`, `u64::*`, `u64::/`, `u64::%`, `u64::min`, and
`u64::max`.

Subtraction is accepted only when the collected left-hand-side interval proves
that it cannot underflow. Division and remainder require a divisor whose
interval excludes zero. Addition and multiplication use checked arithmetic at
runtime: an overflow, or a computed count too wide for the configured
multiplicity type, stops the run with an error naming the rule and the operands
rather than wrapping or aborting the process. An output multiplicity of zero
omits the child without evaluating its term.

## Splicing and comprehensions

A plain `..rest` splice copies a rest binding unchanged. A comprehension maps
its elements while splicing the results into the surrounding application:

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-forms}}
```

A sequence comprehension uses `..[...]` and visits its source in order. A set
comprehension uses `..{...}` and visits each member once. A multiset
comprehension also uses braces, but requires both multiplicity annotations:
`body:output-count` and `element:source-count`. It visits each distinct child
once and exposes the child's complete source count.

The source after `in` must be an LHS rest binding of the required collection
kind. A comprehension cannot iterate an arbitrary right-hand-side term.
Its element binder has the source collection's element sort, and its body must
produce the destination operator's element sort. A comprehension can therefore
map between sorts through a declared function. A direct `..rest` splice performs
no mapping, so its source and destination element sorts must be equal. Splices
and comprehensions are rejected under fixed-arity destination operators.

### Filters

An optional `if` computes one concrete literal value per source element. The
body is emitted only when the active literal model considers that value
truthy.

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-filter}}
```

The filter combines the LHS-bound `threshold` with the current source
`count`. It keeps children whose multiplicity is greater than one.

A filter is not an e-graph query. An ordinary application such as
`(Keep element)` would construct an e-node rather than compute a literal, so
Semper rejects it:

```lisp
{{#include ../examples/05-illegal-comprehension-filter.egg:illegal-comprehension-filter}}
```

To require a graph fact, bind the element on the LHS and add `(Keep element)`
as a rewrite guard or a conjunct of a general rule.

### Lexical scope

The source rest variable is resolved in the enclosing environment. The
element and optional source-count binders then introduce fresh local names for
the body, output multiplicity, and filter. These locals shadow outer names and
disappear after the comprehension. Outer query bindings remain unchanged.

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-scope}}
```

The local `element` maps `c` and `marker`. After the comprehension, the final
`(Keep element)` refers to the unchanged outer binding `a`. Sibling and nested
comprehensions may reuse binder names because each introduces a new scope.

The element and count names of one multiset comprehension must differ.
`for k:k` is rejected as a duplicate declaration in one scope.

```lisp
{{#include ../examples/05-illegal-comp-binders.egg:illegal-comp-binders}}
```

### Computed output counts

A multiset comprehension can transform each source count:

```lisp
{{#include ../examples/05-rhs-comprehensions.egg:comprehension-count}}
```

Each local source count is at least one, so subtracting one is statically safe.
The count-one child maps to zero and is omitted without constructing `(F a)`.
The count-three child produces two copies of `(F b)`.

## Limits of variadic matching

Semper's AC matcher implements maximum-partition matching, not unrestricted
classical AC matching. Scalar elements bind distinct stored children and take
their complete multiplicities. The rest variable takes all remaining stored
children.

```lisp
{{#include ../examples/05-variadic-limits.egg:variadic-limits}}
```

The exact pattern `(Add x:1 y:1)` does not match `Add{a:2}`. The subject has
one distinct child with multiplicity two, not two children for `x` and `y`.
The variant `(Add x:k>=2 ..rest)` handles that representation.

A pattern also cannot split `a:5`, consume two copies, and leave three in
`rest`. It must bind the complete count and reconstruct the desired number on
the right-hand side, for example with `(u64::- k 2)`.

Scalar variables range over existing e-classes. They do not range over
implicit sums or arbitrary subsets of one flattened node. A pattern cannot
bind `x` to an unmaterialized `Add(a,b)` inside `Add(a,b,c)`. Another command
must first construct that subterm, or the pattern must name its children
separately.

Sequence patterns permit one prefix and one suffix rest because their fixed
elements describe a contiguous window. AC and ACI patterns are unordered and
permit one remainder.

The
[pattern-matching design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/09-pattern-matching.md)
defines the matching relations and their limits. The
[rule-application design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/12-rule-application.md)
specifies right-hand-side evaluation and actions.
