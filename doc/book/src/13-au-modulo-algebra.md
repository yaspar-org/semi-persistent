# Anti-unification modulo the declared algebra

> Chapter contents: what each declared attribute absorbs before the search starts,
> one measured pair per attribute, what an AC node's children being a multiset does
> to the search itself, and where the absorption stops.
>
> Examples: `examples/13-identity-arity.egg` exists and is measured (a `:size 10 :cr
> 0.6250` result against a `:size 13 :cr 1.0000` result once the identity is
> removed). Add `examples/13-order.egg` and `examples/13-repetition.egg` on the same
> pattern: same two terms, one file with the attribute declared and one without, so
> every claim in the chapter is a pair of measured numbers rather than an assertion.
>
> Carry over: `v1-draft/05-anti-unification.md`, the paragraph beginning "It works
> modulo the declared theory". `v1-draft/08-what-the-algebra-absorbs.md` section "The
> identity element absorbs a difference of arity" is written and measured: keep it.
>
> The chapter's claim is that this costs nothing at query time because it is the
> representation and not search. Each section should end in the number that shows it.

## Order, absorbed by commutativity

> An AC operator's children are a sorted multiset, so two candidates that differ only
> in argument order are the same e-node and there is nothing for the search to report.
> Measured pair, with and without the attribute.

## Repetition, absorbed by idempotence

> An ACI operator's children are a set, so a repeated conjunct is not a difference.
> Measured pair.

## Arity, absorbed by an identity element

> Keep the written section. A unit lets a three-child node align against a two-child
> node, which is the one case where the anti-unifier can relate operands of different
> arity. Keep both measured outputs and the account of the aligned result.
>
> Keep the constraint from chapter 4 that this section runs into: an identity
> requires a full AC operator, so an experiment cannot weaken `:assoc-comm-idem
> :identity` to `:assoc` without dropping the unit at the same time. Say what was done
> instead.

## What the multiset representation does to the search

> The part that is not free. When both operands are AC nodes, aligning their children
> is a matching problem over multisets rather than a positional walk, and the solver
> solves it as a transport problem. State this at the level of what it means for the
> reader: the number of ways to align two AC nodes grows with their arity, this is
> where the search cost of an AC-heavy problem comes from, and it is the reason the
> two algorithms of chapters 14 and 15 exist at all. Cite design 19 section 3.4 for
> action generation per node kind and its worked AC example in appendix B.

## Where absorption stops

> Positively framed, per the same instruction that governs chapter 4. The
> declarations absorb order, repetition and arity. A difference that is a domain fact
> rather than an operator law is absorbed by a rewrite rule you write and a run of
> saturation, and chapter 22 shows one doing it. A difference that is neither is a real
> disagreement and is what the output is for.
