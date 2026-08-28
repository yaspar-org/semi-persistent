# Introduction

Semper is an equality saturation engine. It reads a program of S-expression
commands, builds an e-graph, saturates it with rewrite rules, and answers
queries about the result. It also computes, for two terms, their **most specific
anti-unifier**: the largest structure they share, with the places they disagree
marked.

[Chapters 1 to 3](01-install.md) build the engine, run a program, and declare an
operator with algebraic properties. [Chapters 4 to 9](04-no-ground-truth.md) are
the subject: what anti-unification computes, three worked examples of increasing
size, and a corpus of 100 executable problems. [Chapters 13 and
14](13-congruence-modes.md) state what the equality relation behind an
anti-unifier is relative to, and which congruence mode changes it. [Chapters 10
to 12](10-commands.md) are reference material, including an explicit statement of
what the engine does not claim.

## The use

A formalization pipeline turns a sentence into a formal artifact: a policy, a
specification, a contract, a set of constraints. A language model can produce
that artifact. Nobody can easily check it, because checking it means reading the
formalism, and the person who wrote the sentence usually cannot.

There is no reference to compare against. If a correct formalization were
available, the pipeline would be unnecessary.

So compare two candidates against each other. Run the formalizer twice, or run
two different formalizers, and anti-unify the results. What comes back is the
part both candidates agree on, with one marked position per disagreement. A
reviewer reads the marked positions rather than the whole artifact, and each
one arrives with both candidate answers side by side.

The engine's algebraic declarations decide how much of that output is worth
reading. Two candidates for the same sentence differ in ways that do not
matter: conjunct order, which side of an equality a literal sits on, whether a
window is written in minutes or seconds. Declare the relevant operator
associative, commutative, or idempotent and those differences never appear in
the output, because the two candidates are the same term. What remains is where
the candidates say different things.

[Chapter 8](08-what-the-algebra-absorbs.md) measures this rather than asserting
it, one declaration at a time, and reports which declarations earn their place
and which only reduce clutter.

## The examples

Every program shown in this book is a file in the repository that the test suite
executes. None of them are written out in prose only.

## What this book is not

It is not the design documentation. The engine's internals, the storage layout,
the join algorithm, the proof format, the soundness argument and the
anti-unification search itself are covered by
[the design chapters](13-design-documents.md), which are written for people
changing the engine rather than using it.

It is also not a survey of equality saturation. It assumes you either know what
an e-graph is or are willing to treat it as an opaque structure that holds many
terms and knows which of them are equal.
