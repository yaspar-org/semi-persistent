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

Associative operators are variadic. Their declaration contains one argument
sort, and applications may contain any number of children:

```lisp
(function And (Formula) Formula :assoc-comm-idem)
```

## The attributes

Attributes may be combined and written in any order. `:assoc-comm` is an alias
for `:assoc :comm`, while `:assoc-comm-idem` expands to
`:assoc :comm :idempotent`.

| attribute | declared law | canonical representation or effect |
| --- | --- | --- |
| `:assoc` | `f(f(x,y),z) = f(x,f(y,z))` | variadic flat sequence; order is preserved |
| `:comm` | `f(x,y) = f(y,x)` | binary sorted pair |
| `:assoc-comm` | associative and commutative (AC) | variadic sorted multiset |
| `:assoc-comm-idem` | AC and `f(x,x) = x` (ACI) | variadic sorted set |
| `:assoc-left`, `:assoc-right` | associative | variadic flat sequence; the direction is retained as declaration metadata but currently does not change behavior |
| `:idempotent` | `f(x,x) = x` | duplicate children collapse |
| `:nilpotent n` | `n` copies of a child cancel to the identity | child multiplicities are reduced modulo `n`; the default is `2` |
| `:identity t` | `f(x,t) = x` | children equal to `t` are dropped |

These effects are part of canonization and hold without running rewrite rules
or AC completion. Not every combination is legal; the legality table later in
this chapter gives the supported combinations.

## Two more attributes, not finished

> Keep this section as written. `:cancellative` generates cancellation critical pairs
> during AC completion and therefore has no effect unless `--derive-ac-eqs` is on.
> `:inverse g` cancels inverse pairs at build time and is not group reasoning: no
> elimination over sums of several summands, and a pair whose `g(x)` node was never
> built is not seen. Both are stated as what they do today under a heading that marks
> them as unfinished, which is the accurate framing and the one the user asked for.

## Arity: one child, and none

> Keep this section as written. Every claim in it was verified by running the engine:
> a variadic application is a fold, so one child resolves to that child's class with
> no node built, zero children resolve to the unit's class when `:identity` is
> declared, and are rejected otherwise with the quoted error. `(And x)` is `x`.
>
> Keep the two consequences: declare a variadic operator over a single sort, and a
> one-child pattern never matches.
>
> Add the note that came out of writing it, if the engine still behaves this way:
> the declaration checker does not verify that a variadic operator's argument sort
> equals its result sort, so `(function Bad (A) B :assoc-comm)` is accepted and
> `(Bad (x))` yields an `A`-sorted class where the term was typed `B`. State it as a
> declaration assertion the user is responsible for and cross-reference chapter 23.
> Check first whether `src/sortcheck.rs` has since been fixed; if it has, delete the
> caveat and keep the requirement.

## Which combinations are legal

> Keep the legality table and the error text for each row. Keep the consequence the
> v1 draft drew out, that an identity element requires a full AC operator, because
> chapter 13 runs into it.

## Canonization carries the declared laws, rewrite rules carry the rest

> Keep this section. It is framed positively on the user's instruction: declaring the
> attributes puts those laws into canonization, and every other law of the domain is a
> rewrite rule you write. Name the Boolean laws that are rules rather than
> declarations: distributivity, De Morgan, absorption, double negation. Keep the
> forward reference to the domain rewrite in Part IV that changes a reported
> difference.
