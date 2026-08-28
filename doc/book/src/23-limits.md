# Limits

> Chapter contents: each result of the earlier chapters restated as what it does not
> give you, with the chapter it came from and, where one exists, what to do instead.
>
> Carry over: `v1-draft/12-limits.md` has eleven sections and most of them survive.
> Its chapter opening enumerated all eleven, which duplicated eleven headings that are
> each already a sentence: open with one sentence instead.
>
> Every entry here is stated somewhere else in the book too, at the point where the
> reader meets it. That repetition is intended: this chapter is what a reader is
> pointed at when they ask what the engine does not do, and it should be readable on
> its own.
>
> Keep every entry to a short paragraph. If an entry needs more, it belongs in its own
> chapter and this one links to it.
>
> Do not add a closing section that summarizes the limits or reassures the reader. The
> last entry is the end of the chapter.

## Saturation is a fixpoint of the rules, not of the theory

> From chapter 8. A law nobody wrote does not hold, so `(check (!= ...))` reports what
> was not derived.

## A declared attribute is an assertion, not a check

> From chapter 4. The engine takes `:assoc-comm` as given and does not verify that any
> intended interpretation satisfies it. Include the specific unchecked case if it is
> still unchecked: a variadic operator's argument sort is not required to equal its
> result sort, so a mismatched declaration is accepted and its one-child collapse
> produces a class of the wrong sort. Verify against `src/sortcheck.rs` first and delete
> this if it has been fixed.

## Two attributes are accepted and not finished

> From chapter 4. `:cancellative` acts only during AC completion, `:inverse` cancels
> pairs at build time, and full group reasoning is not implemented.

## AC completion is off by default, and what that costs the anti-unifier

> From chapters 11 and 16. Plain mode leaves AC consequences underived, lazy mode
> derives them for equality checks and not for the anti-unifier, and the fix is
> `--derive-ac-eqs`.

## Optimality is relative to the e-graph, the cycle policy, and the objective

> From chapters 14 and 16. Three qualifiers on a certified result, one sentence each.

## Some of the argument is prose, not proof

> From chapter 16. Name what is machine-checked, what has differential evidence, and
> what is argued, with the design sections. Keep it factual and do not apologize for it.

## Agreement is not evidence of correctness

> From chapters 17 and 19. Correlated errors, and the consequence that the method finds
> uncorrelated errors only.

## The smallest anti-unifier is not always the most readable one

> From chapters 16 and 22. The two-identity-element form is the instance.

## Clustering is quadratic in the samples, and there is no command for it

> From chapter 18. The check grid is what the book uses, it is fine at five samples, and
> a larger corpus needs the Rust API.

## Anti-unification does not adjudicate

> From chapter 12. It reports where a decision exists. Something else has to make it.

> Add or drop entries as the writing of the earlier chapters demands. Every entry must
> name the chapter it comes from and must correspond to something the book actually
> showed. Do not add a limit the book never demonstrated.
