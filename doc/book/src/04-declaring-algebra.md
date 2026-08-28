# Declaring algebraic operators

Chapter 3 established which declarations Semper accepts. This chapter defines
the semantic contract those declarations create. Chapter 10 later explains how
the corresponding canonical representations are implemented.

Semper lets you tag operators with algebraic properties. Once declared, these
properties are enforced through automatic term canonization rather than rewrite
rules. The most familiar example is associativity and commutativity:

```lisp
(function Add (Math) Math :assoc-comm)
```

Applications of `Add` are flattened and stored as sorted multisets.
Reassociation and permutation therefore disappear from the representation: a
whole family of AC-equivalent terms is compressed into a single e-node rather
than stored as separate nodes connected by rewrite rules.

Operators declared with `:assoc`, `:assoc-left`, `:assoc-right`, or an AC
alias are variadic. Their declaration contains one argument sort, and an
application may contain one or more children. An application with no children
is also valid when the operator declares an identity.

## The attributes

Compatible attributes may be combined and written in any order.
`:assoc-comm` is an alias for `:assoc :comm`, while
`:assoc-comm-idem` expands to
`:assoc :comm :idempotent`.

| attribute | meaning | canonical representation or effect |
| --- | --- | --- |
| `:assoc` | `f(f(x,y),z) = f(x,f(y,z))` | flatten every nested same-operator child into an order-preserving sequence |
| `:assoc-left` | an application is a left fold | flatten the first-child spine into an order-preserving sequence |
| `:assoc-right` | an application is a right fold | flatten the last-child spine into an order-preserving sequence |
| `:comm` | `f(x,y) = f(y,x)` | binary sorted pair |
| `:assoc-comm` | associative and commutative (AC) | variadic sorted multiset |
| `:assoc-comm-idem` | AC and `f(x,x) = x` (ACI) | variadic sorted set |
| `:idempotent` | `f(x,x) = x` | duplicate children collapse |
| `:nilpotent n` | `n` copies of a child cancel to the identity | child multiplicities are reduced modulo `n`; the default is `2` |
| `:identity t` | `f(x,t) = x` | children equal to `t` are dropped |

`:nilpotent` must be accompanied by `:identity`. The identity is a ground term
of the result sort, built from declarations available at that point. Reducing
child multiplicities modulo the nilpotence order can empty the multiset. When
that happens, Semper canonizes the result directly to the identity's e-class.
The same rule applies to an explicitly empty application such as `(Xor)`;
there is no separate empty `Xor` node connected to the identity by a rewrite.

```lisp
{{#include ../examples/04-nilpotent-identity.egg:nilpotent-identity}}
```

Semper rejects both a `:nilpotent` declaration without an identity and an
empty variadic application whose operator has no identity. A nullary operator
declared with an empty argument list remains an ordinary constant; this
restriction applies only to empty applications of variadic operators.

`:assoc-left` and `:assoc-right` specify fold direction rather than full
associativity. For a left fold,

`f(f(a,b),c) = f(a,b,c)`

but `f(a,f(b,c))` retains its grouped right child. A right fold is the
mirror image. Bare `:assoc` flattens both nestings, so all three terms have
the same canonical representation.

The three sequence tags are mutually exclusive. A directional fold also
cannot be combined with `:comm`; an AC declaration uses `:assoc :comm`.

These effects are applied when ground terms are inserted and when rewrite
rules construct their right-hand sides. They require neither rewrite rules
nor AC completion. Not every other combination is legal; the legality
table later in this chapter lists the supported combinations.

## Inverse-pair cancellation and cancellativity

Semper supports two additional algebraic attributes with deliberately narrow
contracts. They provide inverse-pair cancellation and cancellative inference,
not general group reasoning.

| attribute | meaning | what it does today |
| --- | --- | --- |
| `:cancellative` | `f(a,c) = f(b,c)` implies `a = b` | cancels common summands in equations and generates cancellative critical pairs during AC completion |
| `:inverse g` | `f(x,g(x))` equals `f`'s identity | cancels represented `x` and `g(x)` pairs during canonization and makes `f` cancellative |

The inverse attribute names a previously declared unary operator:

```lisp
(sort E)
(function Zero () E)
(function Neg (E) E)
(function Add (E) E
  :assoc-comm
  :identity (Zero)
  :inverse Neg)
```

`Neg` must have signature `E -> E`, and `Add` must declare an identity. This
declaration asserts that `Add(x, Neg(x)) = Zero`. Semper cancels such explicit
pairs while constructing terms, even in plain mode. For example,
`Add(a, a, Neg(a))` canonizes to `a`.

In plain mode, `:cancellative` performs no inference because AC completion does
not run. It participates both in eager completion with `--derive-ac-eqs` and in
checks using `--lazy-ac-eqs`. Given an asserted equality
`Add(a,c) = Add(b,c)`, completion may therefore derive `a = b`.

These transformations are sound relative to the laws declared by the user:
each removed inverse pair equals the declared identity, and common summands are
removed only from equations for an operator declared cancellative. This
soundness argument is backed by focused tests but is not yet machine-checked
end to end.

The boundary is completeness. Semper recognizes an inverse pair only when the
corresponding `Neg(x)` node exists, and pairs exposed only by later merges may
require AC completion. The tags alone do not derive general Abelian-group laws
such as `Neg(Neg(x)) = x`, distribute `Neg` over `Add`, or normalize sums to
signed coefficients. In particular, `:inverse` means a group inverse, not a
Boolean complement: `Not(x)` is not an inverse for `And`, because
`And(x, Not(x))` is `False` while `And`'s identity is `True`.

## Arity: one child, and none

A variadic application denotes a fold of its binary operator. Folding one child
returns that child; folding no children returns the identity, when one has been
declared. Semper performs these reductions during term construction rather than
storing nodes that later need rewriting.

| application | result |
| --- | --- |
| two or more children | a canonized operator node |
| `(And x)` | `x`'s e-class; no `And` node is built |
| `(And)` with `:identity t` | `t`'s e-class |
| `(And)` without an identity | a sort error |

For an AC or ACI operator without an identity, the last case reports:

```text
operator 'And' has no :identity — a zero-argument application (the empty monomial) is meaningless; declare an identity or supply at least one argument
```

An associative-only operator cannot declare an identity, so its empty
application instead reports:

```text
operator 'And' requires at least 1 argument
```

Associative operators must therefore be closed over one sort. Their argument
and result sorts must coincide, both because nested applications feed results
back as arguments and because singleton collapse returns the child's e-class
directly. Semper enforces this invariant. For example,

```lisp
(sort A)
(sort B)
(function Bad (A) B :assoc-comm)
```

is rejected with:

```text
associative operator 'Bad' must use the same argument and return sort (argument 'A', return 'B')
```

Singleton collapse also affects matching. A one-child pattern such as
`(And a)` never matches because no one-child `And` node exists. To bind one
child while preserving the others, use a rest variable:

```lisp
(rewrite (And a ..rest) (mark a))
```

## Which combinations are legal

Semper validates algebraic attributes when an operator is declared.

| invariant | error if violated |
| --- | --- |
| `:assoc`, `:assoc-left`, and `:assoc-right` are mutually exclusive | `:assoc, :assoc-left, and :assoc-right are mutually exclusive` |
| directional associativity cannot be commutative | `:assoc-left/:assoc-right cannot be combined with :comm; use :assoc :comm for AC` |
| associative-only operators take one argument sort | `:assoc requires 1 argument sort` |
| AC operators take one argument sort | `:assoc :comm operator takes one argument sort` |
| commutative-only operators take two argument sorts | `:comm requires 2 argument sorts` |
| associative argument and result sorts coincide | `associative operator 'Bad' must use the same argument and return sort (argument 'A', return 'B')` |
| commutative arguments have the same sort | `commutative operator 'Bad' must use the same sort for both arguments (got 'A' and 'B')` |
| `:idempotent` and `:nilpotent` are exclusive | `:idempotent and :nilpotent are mutually exclusive` |
| `:idempotent` and `:inverse` are exclusive | `:idempotent and :inverse are mutually exclusive (an idempotent op has no group inverse; logical negation is xor-with-true, not an and-inverse)` |
| `:idempotent` and `:cancellative` are exclusive | `:idempotent and :cancellative are mutually exclusive (a cancellative idempotent monoid collapses to the identity)` |
| `:idempotent` and `:nilpotent` require AC | `:idempotent/:nilpotent require :assoc :comm` |
| `:cancellative` requires AC | `:cancellative requires :assoc :comm (an AC operator)` |
| `:nilpotent` requires an identity | `:nilpotent requires :identity (the emptied monomial must reduce to the unit)` |
| `:inverse` requires an identity | `:inverse requires :identity` |
| property attributes require a structural attribute | `algebra tags require :assoc and/or :comm` |

A commutative-only operator's return sort may differ from its shared argument
sort. For example, `(function Same (E E) R :comm)` is legal.

One important implementation restriction follows from the table: an identity
requires a full AC operator. Semper cannot currently attach an identity to an
associative-but-noncommutative operator.

## Canonization carries the declared laws, rewrite rules carry the rest

> Keep this section. It is framed positively on the user's instruction: declaring the
> attributes puts those laws into canonization, and every other law of the domain is a
> rewrite rule you write. Name the Boolean laws that are rules rather than
> declarations: distributivity, De Morgan, absorption, double negation. Keep the
> forward reference to the domain rewrite in Part IV that changes a reported
> difference.
