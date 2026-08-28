# Declaring algebraic operators

> Chapter contents: each attribute paired with the law it declares and the
> representation it selects, the two attributes that are accepted but not finished,
> what an application of a variadic operator means at one child and at none, the
> combinations the engine rejects with the error text for each, and the division
> between the laws canonization carries and the laws a rewrite rule carries.
>
> Carry over: `v1-draft/03-algebra.md` is this chapter. It was written against the
> engine, every claim in its arity section was verified by running programs, and the
> user reviewed and approved its structure. Keep it whole. Required changes:
>
> - enter from chapter 3's brief introduction: this chapter defines the user-facing
>   semantic contract, while chapter 10 later explains its representation;
> - renumber cross-references (limits is now chapter 23, the worked example is now
>   chapter 22);
> - its "one-child pattern never matches" material overlaps chapter 5. Keep the
>   statement here, keep the `..rest` remedy here since it is two lines, and let
>   chapter 5 develop the pattern surface.
>
> Example: `examples/04-illegal-clamp.egg` and
> `examples/04-illegal-seq-identity.egg` exist for the legality table. Add
> `examples/04-arity.egg` for the one-child and
> zero-child cases, with the error-expecting cases in their own files since a sort
> error aborts the program.

## The attributes

> The table from the v1 draft: attribute, meaning, representation. Ends at
> `:identity`. Do not put `:cancellative` or `:inverse` in this table.

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
