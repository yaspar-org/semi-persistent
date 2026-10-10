# Rules and patterns

This chapter defines all three rule forms, fixed and variadic patterns, rule
actions and modifiers, multiplicity constraints, remainder bindings,
right-hand-side comprehensions, sequence patterns over n-ary operators, and what
makes matching complete over A, C, AC, and ACI operators.

## The grammar

Semper has three surface forms for defining rules:

```text
(rewrite lhs rhs [:when (pattern ...)] [:subsume] [:flatten] [:ruleset name])
(birewrite lhs rhs [:when (pattern ...)] [:flatten] [:ruleset name])
(rule (pattern ...) (action ...) [:flatten] [:ruleset name])
(rewrite seq-lhs rhs [:let ((name expr) ...)] [:when (expr ...)]
         [:flatten] [:ruleset name])

action = (union rhs rhs)
       | (set (operator rhs ...) rhs)
       | (operator rhs ...)
```

Square brackets mark optional syntax. The trailing modifiers may appear in any
order, and `:flatten` at most once. Only an ordinary `rewrite` accepts
`:subsume`. A general `rule` puts its query patterns in the first parenthesized
list and its actions in the second. Its trailing modifiers are `:flatten` and
`:ruleset`. The last form is a sequence rewrite, whose left-hand side holds a
sequence pattern ([Sequence patterns](#sequence-patterns)). Its `:when` holds
right-hand-side expressions rather than patterns, and only this form accepts
`:let`.

The `set` action is part of the surface grammar, but rule application does not
implement it. The sort checker rejects a rule that contains it, before any
command runs:

```text
sort error: the `set` action (on 'f') is not implemented; write the value as a term and use `union` instead
```

[Annex A](A-full-grammar.md) gives the complete grammar.

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
available to `(extract term)`. Extraction under a cost model
([Part V](24-extraction-under-cost-models.md)) excludes it. Matches already
collected for the current application still execute.

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
| `(set (operator rhs ...) value)` | Reserved for a lattice-valued update; the sort checker rejects it as not implemented. |

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
such as `(Set x)` normally has no one-child `Set` node to match
([Patterns that do not match](#patterns-that-do-not-match)). `(Set x ..rest)`
binds one member while allowing the stored node to contain additional members.

### Ordered patterns (`:assoc`)

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
`term:count`, `term:2`, or `term:(u64::- count 1)`. Under an AC operator it is
the child's count; under an associative operator the child is repeated. An ACI
operator stores a set, so a count on its child is rejected.
Multiplicity expressions use `u64::+`, `u64::-`, `u64::*`, `u64::/`, `u64::%`,
`u64::min`, and `u64::max`, each with two arguments. A sequence rewrite accepts `+`, `-`, `*`,
`min`, and `max`, with or without the `u64::` prefix, and no division or
remainder.

Subtraction is accepted only when the collected left-hand-side interval proves
that it cannot underflow. Division and remainder require a divisor whose
interval excludes zero. Addition and multiplication use checked arithmetic at
runtime: an overflow, or a computed count too wide for the configured
multiplicity type, stops the run with an error naming the rule and the operands
rather than wrapping or aborting the process. An output multiplicity of zero
omits the child without evaluating its term.

### Occurrences and empty applications

A count is a number of occurrences, so it is at least 1, and an omitted count
is 1. A count of 0 says that the element does not occur, so writing `x:0` says
nothing: it is rejected in a ground term, a pattern, and a right-hand side. A
count that a multiplicity expression computes to 0 is different: the child is
absent, and it is dropped.

An application of an A, AC, or ACI operator with no children denotes the
operator's identity. It therefore has a meaning only when the operator declares
`:identity`, and then it reduces to the identity element. Without one it means
nothing, and Semper never builds it:

- written in a ground term or a right-hand side, it is rejected when the program
  is checked ("operator 'Add' has no :identity, so an application of it with no
  children is meaningless");
- written as a pattern, it is rejected because no stored node is empty;
- left empty at run time, because every child's count was computed to 0 or a rest
  was empty, the action is not applied, and the run prints `warning: N rule
  action(s) not applied: the right-hand side was an application with no children
  of an operator without :identity, which has no meaning`.

A sequence rule treats a right-hand side with no value the same way: the match
does not fire, and the run reports the count.

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

In an ordinary rule, the source after `in` must be an LHS rest binding of the
required collection kind. A comprehension cannot iterate an arbitrary
right-hand-side term there. Tuple binders and expression sources belong to
sequence rewrites ([Comprehensions](#comprehensions)).
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

## Sequence patterns

A sequence pattern matches a run of children of an n-ary node in one match, and
the right-hand side computes over the whole run. It is written at the root of a
`rewrite` over an `:assoc`, `:assoc-comm`, or `:assoc-comm-idem` operator. Three
items make up the pattern:

| item | under A (`:assoc`) | under AC and ACI |
| --- | --- | --- |
| a pattern `P` | the next child | one child no other item takes |
| `..name` | a gap: zero or more consecutive children; any number per node | the children no other item takes; at most one per node |
| `(..name P)`, a filter | a run: zero or more consecutive children matching `P`, maximal toward adjacent gaps | every remaining child with a member matching `P`, possibly none |

Every variable of a filter's pattern binds a sequence with one entry per child the
filter took, in the same order. A node with no matching child still matches, with
the filter empty. The right-hand side, `:let`, and `:when` read those sequences.

### Merging and factoring under ACI

The example below is the pair of rules the book's MLTL examples use (MLTL, a temporal
logic with interval-bounded operators, is introduced in
[Chapter 24](24-extraction-under-cost-models.md#when-the-cost-depends-on-a-grouping-the-e-graph-does-not-store)). The first merges
the always-windows of one operand into maximal runs; the second gives all the
always-operators of a conjunction one outer window.

```lisp
{{#include ../examples/05-collection-rules.egg:collection-rules}}
```

The first rule merges `G[0,3] a` and `G[4,6] a` into `G[0,6] a`. The second gives
the two windows of `f` the common outer window `[2,5]` over one inner
conjunction. The inner window of `a` is `[0,0]`, which is `a` itself.

The expressions available on the right-hand side, in `:let`, and in `:when` are:

- reductions of a sequence: `min`, `max`, `sum`, `count`;
- the scalar primitives of [Chapter 3](03-sorts-and-terms.md), applied element
  by element inside a reduction or a comprehension, and `if`;
- splices `..name`, which put a matched sequence back as children;
- comprehensions `..{ body for binders in source }`, which build unordered
  children, and `..[ body for binders in source ]`, which build ordered ones;
- the sequence primitives `(zip s1 ... sn)` (positions paired, shortest input
  wins), `(concat s1 ... sn)`, `(union-by p l u)` (the windows `[l, u]`
  grouped by `p` and unioned into maximal runs), `(narrow ...)`, and
  `(narrowed ...)`.

A sequence used where a scalar is expected is rejected when the rule is checked.
A `min` or `max` of an empty sequence has no value, and the rule does not fire on
that node.

### Runs under an associative operator

Under `:assoc` the items cover the children in written order, so a pattern is a
regular expression over the child list: one child, a run, or a gap. Any number of
gaps is allowed. A run next to a gap is maximal toward it.

```lisp
{{#include ../examples/05-seq-assoc-runs.egg:seq-assoc-runs}}
```

### Multiplicities under AC

Under `:assoc-comm` each child carries a multiplicity. A filter takes the
annotation of an ordinary AC element after its name: `(..fs:k P)` takes any
multiplicity and binds it, `(..fs:k>=2 P)` takes only those at least 2, and `:3`
takes exactly 3. An unannotated filter takes only children of multiplicity 1, as
an unannotated AC element does. Outside the filter, `k` is a sequence parallel to
`fs`, so `(sum k)` counts copies and `(count fs)` counts distinct children.

```lisp
{{#include ../examples/05-seq-ac-multiplicity.egg:seq-ac-multiplicity}}
```

### Several filters, and `:except`

Filters are matched independently. A child that two filters match is given to
each in turn, and every assignment is a match. `:except other` removes from a
filter the children `other`'s pattern matches, for a rule that wants one
assignment. `:except` is accepted under AC and ACI only, since under `:assoc`
order already separates runs, and it must name a sibling filter.

```lisp
{{#include ../examples/05-seq-except.egg:seq-except}}
```

### Simple items beside filters

A plain pattern beside filters takes one child, and every choice of child is a
separate match. The filters then take from the remaining children. The same
holds for the member of a class: where several members of a child's class match,
each is a separate match.

```lisp
{{#include ../examples/05-seq-simple-items.egg:seq-simple-items}}
```

### Comprehensions

A comprehension's binders name the columns of its source. An element
comprehension `for f:k in fs` reads each child with its multiplicity, and the
body states the output multiplicity after a colon. A column of a multiset
sequence must be bound as `x:k`, or as `x:_` to drop the multiplicity; a bare `x`
there is rejected, since whether the count is dropped would be implicit.

```lisp
{{#include ../examples/05-seq-comprehensions.egg:seq-comprehensions}}
```

### Narrowing

`(narrow c d r a b q)` reads one eventually-window `[c, d]` over `r` per row of
its first three columns, and the always-windows `[a, b]` over `q` of the last
three. For each `r` it shrinks `[c, d]` past the windows whose `q` is `r`, and
gives one row `(r c2 d2)`. `(narrowed ...)` gives only the rows whose window
changed, so a guard on its count keeps the rule from rewriting a node to itself.

```lisp
{{#include ../examples/05-seq-narrow.egg:seq-narrow}}
```

### Splicing across operator kinds

A sequence matched under one kind can be spliced under another. From AC to ACI
the multiplicities are dropped. From an unordered match to an ordered operator,
the children come in the order the e-graph stores them, which is not a function
of the e-graph's contents, and the checker warns.

```lisp
{{#include ../examples/05-seq-splice.egg:seq-splice}}
```

### Rejected forms

The checker rejects the five shapes below, each with a reason. It also
rejects a root that is not A, AC, or ACI, a sequence pattern below the root, a
rest or a non-plain operator inside a filter's pattern, and a name bound twice,
by two filters or by a filter and a simple item.

A sequence pattern under a `:comm` operator. Such a node has exactly two
children, and two simple patterns already match it in both orders:

```lisp
{{#include ../examples/05-seq-illegal-comm.egg:seq-illegal-comm}}
```

A filter inside a filter:

```lisp
{{#include ../examples/05-seq-illegal-nested.egg:seq-illegal-nested}}
```

Two bare sequences under AC or ACI, which would divide the remaining children
with nothing to tell them apart:

```lisp
{{#include ../examples/05-seq-illegal-two-bare.egg:seq-illegal-two-bare}}
```

An `:except` cycle, where a child matching every filter of the cycle would go to
none:

```lisp
{{#include ../examples/05-seq-illegal-except-cycle.egg:seq-illegal-except-cycle}}
```

A sequence pattern anywhere but the left-hand side of a `rewrite`:

```lisp
{{#include ../examples/05-seq-illegal-outside-rewrite.egg:seq-illegal-outside-rewrite}}
```

### When sequence rules run

Sequence rules are matched in each round on the round's snapshot, together with
the ordinary rules, by one `Collect` step of the compiled query. Under
`--use-semi-naive` they are semi-naive with the ordinary rules: each rule
assembles only the nodes whose matches can have changed, when its estimate says
that pays, and otherwise matches naively. Without the flag they are naive.

### Alternatives considered

The design went through several forms, and four were rejected with a measured
reason.

- **`(each name pattern)` and a pass after each round.** The first form matched
  a separate pass after each round of the ordinary rules, over ACI roots only.
  It was replaced by the filter syntax and the in-round `Collect` step. The pass
  survives only as the reference the engine's differential tests compare
  against; on the 1,172 MLTL specifications Johannsen and Rozier publish with their FMCAD 2026 paper ([Chapter 24](24-extraction-under-cost-models.md#when-the-cost-depends-on-a-grouping-the-e-graph-does-not-store)) the two build the same e-graph.
- **The member of smallest node id.** Where a class had several matching
  members, the first implementation took the one of smallest id. That is sound,
  but the smallest id depends on insertion and merge order, so two runs building
  the same e-graph could rewrite differently.
- **All matching members in one match.** Sound for ACI, but it builds one term
  holding every window, and the cheaper single-choice terms never enter the
  e-graph.
- **Keeping the pairwise rules as a backstop.** Saturation with both would be
  complete by the ordinary semantics, and it grows the e-graph to 1,505,268 nodes
  at 4 rounds on one benchmark. The n-ary rules exist to avoid that.

One property is given up by design: a filter takes the maximal set of matching
children, never a subset. Enumerating subsets is 2^k firings on a k-ary node,
which is the growth sequence patterns exist to avoid.

## Matching completeness over A, C, AC, and ACI

An e-graph stores one node per n-ary application, with its children flattened
and normalized, and a pattern is matched against those stored children. Four
mechanisms decide which matches exist.

**Construction flattens.** Building `(Flat (Flat a b) (Flat c d))` stores one
node `Flat(a, b, c, d)`. Every path that builds or recanonizes an n-ary node,
and every flattened view below, goes through one normalization function. It
coalesces or deduplicates children, drops the identity, applies the nilpotent
clamp, and cancels inverse pairs, so all of them agree.

```lisp
{{#include ../examples/05-rules-over-seq.egg:construction-flattens}}
```

**Nesting can still appear.** A merge after construction can make a child class
hold a node of the same operator, and the parent is not rebuilt as flat: with AC
completion off, the nested and the flat spelling of one content can both exist.
Completion, when on, proves the two spellings equal; it does not build the flat
node, so a pattern still sees the stored children.

**`:flatten` matches through nesting.** A rule tagged `:flatten` matches each
n-ary node against every *view* of it. A view opens a child class that holds a
node of the same operator, and splices that node's children in its place. A
class is opened only when an item takes an element from inside it, so a view
never repeats a match the stored children already give. One node's enumeration
stops at 2^20 views, 2^24 steps, or 2^24 elements. A node over a bound, or one
whose view multiplicity exceeds the configured width, is skipped with a warning
naming the rule, and the run continues. Under `--use-semi-naive`, an ordinary
rule tagged `:flatten` is matched naively in every round; a sequence rule
tagged `:flatten` stays semi-naive. On a rule whose query has no A, AC, or ACI
operator, `:flatten` has no effect, and installing the rule prints the warning
`:flatten has no effect: the rule's pattern has no associative, AC, or ACI
operator`. A `:comm` operator does not count.

```lisp
{{#include ../examples/05-flatten.egg:flatten}}
```

Without the tag, the same rule reads the stored children `{g1, cc}`, which hold
one `Global`, and the factoring does not fire:

```lisp
{{#include ../examples/05-flatten-control.egg:flatten-control}}
```

**Commutative pairs match in both orders.** A `:comm` operator has exactly two
children; a pattern over it matches both argument orders, and `:flatten` leaves
it untouched. With neither child bound, `(c x y)` matches a stored `c(a, a)`
twice, once per order.

What is not complete, by design: scalar variables range over existing classes,
not over unmaterialized sub-sums such as `Add(a,b)` inside `Add(a,b,c)` (below);
a sequence filter takes the maximal set, never a subset; and an untagged rule
reads only the stored children.

### Patterns that do not match

Patterns are matched as written. No stage normalizes a pattern by the declared
laws, and none warns about one that construction would store in another form.
Each pattern below loses matches:

- **An identity child.** `(Plus x (Zero))` with `:identity (Zero)` matches no
  node, since construction, rebuild, and views drop the unit.
- **An element past a nilpotent order.** `x:2` under `:nilpotent 2` never binds,
  since counts are reduced modulo the order.
- **An inverse pair.** `(Plus x (Neg x))` with `:inverse Neg` never matches,
  since pairs cancel at build and rebuild.
- **A repeated element.** `(Or x x)` under ACI never matches, since a stored set
  holds distinct classes. `(Add x x)` under AC never matches either; `x:2` is
  the form that does.
- **A nested same-operator application.** `(Plus (Plus a b) x)` matches only
  where a child class holds a `Plus{a, b}` node. A flat stored `Plus{a, b, c}`
  gives no match, with or without `:flatten`, since views open classes, not
  sub-multisets.
- **A single element.** `(Plus x)` matches only a degenerate stored node, such as
  an `And{K}` that rebuild can leave in `K`'s class, and never under `:flatten`.

An application with no element, `(Plus)`, is rejected when the rule is checked.

Two cases lose matches under `:flatten` itself. If inverse cancellation or the
nilpotent clamp removes every element an opened class contributes, the view is
dropped. For example, `Add{a, d, e, f, K}` with `K` equal to
`Add{(Neg a), (Neg d)}` has the view `{e, f}`, which `(Add x y) :flatten` should
match and does not. A degenerate node such as `And{K}` has only a single-class
view, which is not matched, so a tagged rule misses the match an untagged one
finds there.

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

An ordinary pattern under `:assoc` permits one prefix and one suffix rest,
because its fixed elements describe a contiguous window; a sequence pattern
permits any number of gaps. AC and ACI patterns are unordered and permit one
remainder.

The
[pattern-matching design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/07-rules-and-pattern-matching.md#74-pattern-matching-execution)
defines the matching relations and their limits. The
[rule-application design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/07-rules-and-pattern-matching.md#77-rule-application-and-rhs-evaluation)
specifies right-hand-side evaluation and actions.
