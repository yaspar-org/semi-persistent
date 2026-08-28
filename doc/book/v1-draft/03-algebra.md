# Declaring operators with algebraic properties

This chapter pairs each attribute with the law it declares and the child
representation it selects, names the two attributes that are accepted but not
finished, says what an application of a variadic operator means at one child and
at none, gives the combinations the engine rejects with the error text for each,
and separates the laws canonization carries from the ones you write as rewrite
rules.

Chapter 2 wrote commutativity as a rewrite rule:

```lisp
(rewrite (Add a b) (Add b a))
```

That works, and it is what an engine without native theory support requires.
The cost is that `(Add x y)` and `(Add y x)` are two e-nodes, the rule has to
fire to relate them, and every operator above them sees two children instead of
one. For an n-ary conjunction the same encoding produces a permutation blowup.

The alternative is to declare the property on the operator:

```lisp
(function Add (Math) Math :assoc-comm)
```

Now there is one e-node. Its children are stored as a sorted multiset, so
argument order is not represented and cannot differ. No rule fires, because
there is nothing to prove.

Note the signature change. An associative operator is **variadic**: it takes one
argument sort, not two, and applications may have any number of children.

```lisp
(function And (Formula) Formula :assoc-comm-idem)   ; (And a b c d) is legal
```

## The attributes

| attribute | meaning | representation |
| --- | --- | --- |
| `:assoc` | associative | variadic sequence, order kept |
| `:comm` | commutative | binary, unordered pair |
| `:assoc-comm` | both (AC) | variadic sorted multiset |
| `:assoc-comm-idem` | AC and idempotent (ACI) | variadic sorted set |
| `:assoc-left`, `:assoc-right` | associative with an explicit nesting direction | variadic sequence |
| `:idempotent` | `f(x,x) = f(x)` | duplicate children collapse |
| `:nilpotent n` | `n` copies of a child cancel | child multiplicities taken mod `n` |
| `:identity t` | `t` is the neutral element | `t` children are dropped |

Everything in that table is what the rest of the book uses.

## Two more attributes, not finished

The declaration checker accepts two further attributes. Neither is complete, and
this book does not build on either.

| attribute | meaning | what it does today |
| --- | --- | --- |
| `:cancellative` | `f(a,c) = f(b,c)` implies `a = b` | generates cancellation critical pairs during AC completion, so it has no effect unless `--derive-ac-eqs` is on |
| `:inverse g` | `g` is the inverse operator | cancels inverse *pairs* at build time, so `x` and `g(x)` in one monomial drop out |

`:inverse` is pair cancellation and nothing more. There is no elimination over
sums of several summands, and a pair whose `g(x)` node was never built is not
seen, so it does not add up to group reasoning. Full group completion is
postponed, which [chapter 12](12-limits.md) restates among the limits.

## Arity: one child, and none

A variadic application is notation for folding the binary operator over the
children, so the two degenerate arities have forced readings. Folding a
one-element list gives that element, and folding an empty one gives the unit. The
engine resolves both at build time by returning an existing e-class rather than
storing a node:

| application | result |
| --- | --- |
| two or more children | an `And` node holding them, canonized |
| `(And x)` | `x`'s class, and no `And` node is built |
| `(And)` with `:identity t` declared | `t`'s class |
| `(And)` with no identity | `sort error: ... has no :identity — a zero-argument application (the empty monomial) is meaningless` |

So `(And x)` **is** `x`. It is not a node that later reduces to `x`, and
`(print-size And)` does not count it, because nothing was built. An `:assoc`-only
operator has the same one-child rule and cannot declare an identity, so its
zero-child application is rejected with `requires at least 1 argument`.

Two consequences for the way you declare and match.

**Declare a variadic operator over a single sort.** `f(f(a,b),c)` uses `f`'s
result as `f`'s argument, so an associative operator's argument sort has to be its
return sort, and the one-child collapse is well sorted only when it is. The
declaration checker does not currently reject a mismatch, so this one is on you,
like the other declaration assertions [chapter 12](12-limits.md) lists.

**A one-child pattern never matches.** `(rewrite (And a) (mark a))` is accepted
and fires zero times, because there is no one-child `And` node in the e-graph for
it to match. To bind one child and leave the rest alone, name the rest:

```lisp
(rewrite (And a ..rest) (mark a))
```

That fires once per child, binding `a` to it and `..rest` to the others.

## Which combinations are legal

The engine enforces these at declaration time, and they constrain what an
experiment can hold fixed.

| rule | error if violated |
| --- | --- |
| `:assoc` alone takes exactly 1 argument sort | `:assoc requires 1 argument sort` |
| `:comm` alone takes exactly 2 argument sorts | `:comm requires 2 argument sorts` |
| `:assoc :comm` together take exactly 1 argument sort | `:assoc :comm operator takes one argument sort` |
| `:idempotent` and `:nilpotent` need both `:assoc` and `:comm` | `:idempotent/:nilpotent require :assoc :comm` |
| `:identity`, `:inverse`, `:idempotent`, `:nilpotent` need `:comm` | `:idempotent/:nilpotent/:identity/:inverse require :comm (an AC operator)` |
| the same four need `:assoc` | `:idempotent/:nilpotent/:identity/:inverse require :assoc (an AC operator)` |
| `:nilpotent` needs `:identity` | `:nilpotent requires :identity (the emptied monomial must reduce to the unit)` |
| `:inverse` needs `:identity` | `:inverse requires :identity` |
| `:idempotent` excludes `:cancellative` | `:idempotent and :cancellative are mutually exclusive` |
| a property attribute needs a structural one | `algebra tags require :assoc and/or :comm` |

One consequence constrains what an experiment can vary: **an identity element
requires a full AC operator.** You cannot declare an
associative-but-not-commutative operator with
a unit, so weakening `:assoc-comm-idem :identity (Lit true)` down to `:assoc`
drops the unit at the same time. Chapter 8 runs into this and has to work
around it.

## Canonization carries the declared laws, rewrite rules carry the rest

Declaring `And` and `Or` associative, commutative and idempotent with units puts
those laws into canonization: every application is stored in the normal form they
define, and no rule has to fire to relate two spellings of the same term. Every
other law of Boolean algebra is a rewrite rule you write, including
distributivity, De Morgan, absorption and double negation. Writing one changes
what the e-graph proves equal, which changes what the anti-unifier reports as
shared, and [chapter 6](06-worked-example.md) shows one domain rewrite doing
exactly that.

The full attribute semantics, the canonization procedure and the AC completion
machinery are in the design chapters
[`ac-algebraic-properties.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/ac-algebraic-properties.md)
and
[`04-canonization.md`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/04-canonization.md).
