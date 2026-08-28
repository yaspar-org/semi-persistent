# Using e-graphs and anti-unification for semantic comparison in autoformalization

Autoformalization turns a natural-language requirement into a formal artifact.
This chapter defines the review problem, explains what ordinary checks leave
unsettled, and introduces comparison across several generated samples.

## From a sentence to an enforced artifact

A formalization pipeline may produce a policy, specification, formula, or
proof obligation. The sentence records what somebody requested. The generated
artifact is what another system will enforce, check, or prove.

Consider this requirement:

> The agent may POST to `/deploy`, but only if a health check has already come
> back 200 in the last 15 minutes.

Its policy must represent the request method, path, event kind, response
status, and time window. A reviewer who knows the formal language may not know
the intended policy, while the author of the sentence may not know the formal
language. Comparing syntax does not resolve that division.

## What the ordinary checks leave open

**Compare against a reference.** A correct reference would settle the question,
but many autoformalization tasks have no such artifact. Accuracy against a gold
answer and a diff against expected output are unavailable in that case.

**Validate the artifact.** Validation remains required. It rejects malformed
terms, unknown fields, and sort errors. It also accepts a well-formed artifact
that expresses the wrong condition.

**Test the artifact.** Tests remain required as well. A replay exposes a
missing condition only when its trace exercises the behavior that condition
would have excluded. The test author must first identify the behavior to test.

**Read the artifact.** Direct review can find every category of error, but a
large formula gives no ordering over its possible error locations. The
reviewer reads agreed structure and disputed structure with equal attention.

Validation and testing answer questions that comparison cannot. The method in
this part supplements them by identifying where samples disagree.

## Sample it several times

Generate three to five formalizations of the same sentence, or obtain them
from several formalizers. The comparison does not treat any sample as a
reference. It produces two intermediate results:

1. a partition whose members are equal under the declared algebra and asserted
   domain facts;
2. an anti-unifier for each pair of clusters, with both readings attached at
   every localized difference.

Agreement means that this comparison localized no disagreement at that
position. It does not establish that the agreed reading is correct. Chapters
18 and 19 construct the partition and the pairwise explanations.

## Presentational noise

Several syntactic differences may preserve the intended meaning: reordered or
repeated conjuncts, reversed equality operands, `>= 1` versus `1 <=`, 15
minutes versus 900 seconds, or a named predicate versus its expansion. A text
diff reports these beside changes to event kinds, connectives, and guards.

Different mechanisms remove or localize different kinds of noise:

| difference | treatment |
| --- | --- |
| order and repetition | algebraic declarations from Chapter 4 canonize the terms |
| a named predicate and its expansion | a Chapter 5 rule followed by Chapter 8 saturation can prove them equal |
| equivalent literal encodings | the encoder or an explicit rule must normalize them |
| a missing child of an operator with an identity | Chapter 13's AU alignment pairs it with the identity |

Identity alignment does not make the samples equal. It keeps their shared
children in the skeleton and localizes the missing child.

## Correlated errors

Samples from one model under one prompt can repeat the same interpretation.
Agreement among those samples is therefore weaker than agreement among
independent sources. The repository's
[formalizer pilot](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/tests/au_formalizer_pilot.rs)
uses one system and explicitly treats its result as an optimistic bound, not a
population study.

This method directs review toward uncorrelated differences. It is not a
soundness argument, and Chapter 23 retains that boundary among the engine's
other limits.
