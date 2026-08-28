# What autoformalization is

> Chapter contents: what an autoformalization pipeline produces, why its output
> cannot be checked against a reference, what validating and testing and reading each
> leave undetected, the alternative of comparing several samples against each other,
> and the two ways that alternative fails.
>
> Carry over: `v1-draft/04-no-ground-truth.md` is most of this chapter and its
> argument is sound. Two changes. First, it was written as the book's opening and can
> now assume everything in Parts I to III, so it should name the tool it is going to
> reach for rather than motivating from zero. Second, it promises a two-candidate
> comparison, and the method this part actually uses takes three to five samples and
> clusters them, so its "Run it twice instead" section becomes "Sample it several
> times" and hands off to chapter 18.
>
> Do not put any engine mechanism in this chapter. It states a problem. Chapters 18
> and 19 give the procedure, and 20 to 22 run it.

## The problem

> A pipeline takes a sentence and produces a formal artifact: a policy, a
> specification, a formula. The sentence is what somebody wanted, the artifact is what
> will be enforced. Keep the v1 draft's example sentence and its observation that the
> person who wrote the sentence and the person who can read the artifact are usually
> not the same person.

## Why the obvious checks do not settle it

> Keep the v1 draft's four, each with the specific thing it leaves undetected:
> comparing against a reference (there is none, and every technique that assumes a
> gold answer goes with it), validating (accepts every well-formed artifact that says
> the wrong thing), testing (finds the bug once you have a trace that exposes it,
> which means you already suspected it), and reading (a 60-node formula presents 60
> places where a mistake could be and no ranking over them).
>
> Keep the instruction to do the second and third anyway. The claim is not that they
> are useless.

## Sample it several times

> Sample the same sentence three to five times, or use several formalizers, and
> compare the samples against each other. Keep the v1 draft's account of what the
> comparison is for: not deciding which sample is right, but finding the positions
> where a decision exists at all. Where the samples agree there is nothing to review.
>
> State the output that would serve this, which chapters 18 and 19 produce: a
> partition of the samples into groups that are provably the same, and
> for each pair of groups, the shared structure with every difference marked in place
> and both readings attached to the mark.

## Presentational noise

> Keep the v1 list of differences that carry no meaning: conjunct order, which side
> of an equality a literal sits on, `>= 1` against `1 <=`, `15m` against `900s`, one
> sample expanding a predicate another left folded. Keep the consequence: a textual
> diff reports all of them alongside the real disagreements and ranks none, and
> unsuppressed noise trains the reviewer to skim.
>
> Now that Part II exists, name where each kind of noise is suppressed: order and
> repetition by the declaration (chapter 4), a folded predicate by a rewrite rule and
> a run of saturation (chapter 8), and a unit-arity difference by an identity element
> (chapter 13).

## Correlated errors

> Keep the v1 section. Two samples from one model on one prompt make the same mistake
> more often than two independent authors would, so agreement is weaker evidence than
> it looks and the method finds uncorrelated errors only. State it as a bound on what
> the method claims: it is a way to direct a reviewer's attention, not a soundness
> argument. Cross-reference chapter 23.
