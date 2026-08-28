# Two candidates, no ground truth

This chapter states why comparing against a reference, validating, testing, and
reading each fail on this problem, then gives the alternative of comparing two
candidates against each other, then names the two ways that alternative fails.

A formalization pipeline takes a sentence and produces a formal artifact. The
sentence is what somebody wanted. The artifact is what will actually be
enforced, checked, or proved.

> The agent may POST to `/deploy`, but only if a health check has already come
> back 200 in the last 15 minutes.

A language model can turn that into a policy with a temporal condition in a few
seconds. Reviewing the result is the hard part, and the difficulty is not that
the formalism is long. It is that the person who wrote the sentence is usually
not the person who can read a metric first-order temporal logic formula, and the
one who can read it does not know what the sentence was supposed to mean.

## Why the obvious approaches do not apply

**Compare against a reference.** There is no reference. If a correct
formalization were available, the pipeline would not be needed. It rules out
every technique that assumes a gold answer: no accuracy metric, no regression
baseline, no diff against expected output.

**Validate the artifact.** Do this, always, and it is not enough. A type
checker or schema validator rejects artifacts that are malformed. It accepts
every well-formed artifact that says the wrong thing. In
[chapter 7](07-repair-by-disagreement.md) one of two candidate policies is
rejected by the real validator, and the other candidate validates cleanly while
permitting an action the sentence forbids.

**Test the artifact.** Also do this. Replaying traces against a policy finds
the bug once you have a trace that exposes it, which means you already
suspected the bug. The failure mode being hunted here is a condition that is
missing, and the trace that exposes a missing condition is the one nobody
thought to write.

**Read the artifact.** This is what actually happens, and it is what the rest of
this book is trying to make cheaper. The reviewer's problem is not
comprehension in principle, it is that a 60-node formula presents 60 places
where a mistake could be and no ranking over them.

## Run it twice instead

Sample the formalizer twice, or use two different formalizers, and compare the
two candidates against **each other**.

Neither candidate is authoritative. That is fine, because the comparison is not
being used to decide which is right. It is being used to find the positions
where a decision exists at all. Where two independently produced formalizations
of the same sentence agree, there is nothing to review. Where they disagree, one
of them is wrong, or the sentence is ambiguous, and either way a human has to
look.

So the output that would be useful is: the structure both candidates share, with
the disagreements marked in place, and both candidate answers attached to each
mark. That output is the two candidates' anti-unifier, and
[chapter 5](05-anti-unification.md) is about computing it.

## Two failure modes: presentational noise and correlated errors

**Presentational noise.** Two candidates for the same sentence differ in ways
that carry no meaning: conjunct order, which side of an equality a literal sits
on, `>= 1` versus `1 <=`, `15m` versus `900s`, one candidate expanding a named
predicate that the other left folded. A textual diff reports all of these
alongside the real disagreements and ranks none of them. If the noise is not
suppressed the output trains the reviewer to skim.

Suppressing it is what the algebraic declarations of
[chapter 3](03-algebra.md) are for, and
[chapter 8](08-what-the-algebra-absorbs.md) measures how much they actually
suppress on a real example.

**Correlated errors.** Two samples from the same model, on the same prompt, make
the same mistake more often than two independent authors would. Agreement is
therefore weaker evidence of correctness than it looks, and this method finds
uncorrelated errors only. It is a way to spend a reviewer's attention well, not
a soundness argument. Chapter 12 restates this among the other limits.
