# Annex C. Flag reference

> Annex contents: every command-line flag in five groups (representation,
> saturation, AC completion, scheduling and selectivity, proofs), plus the
> per-file directives that select the same settings from inside an `.egg` file.
>
> Carry over: `v1-draft/11-cli.md` almost verbatim, dropping its five "This section
> ..." openers and renumbering its cross-references. Add the directives section,
> which the v1 draft did not have.
>
> Verify before writing: `semi-persistent --help` and the flag definitions in
> `egraph/src/config.rs`, so that no flag is missing and every default is right.
>
> Keep the framing the v1 draft had: none of these flags is needed for the use the
> book makes of the engine, the defaults are what every example runs under, and
> several flags exist so that two implementations of one semantics can be compared
> against each other.

## Representation

> `--id-bits`, `--push-pop`, `--types`. Table of flag, default, meaning.

## Saturation

> `--use-naive`, `--use-semi-naive`, `--union-by`. State that the two evaluation
> strategies must produce the same match set and that the test suite runs example
> files under both, with the link to chapter 9.

## AC completion

> `--derive-ac-eqs`, `--lazy-ac-eqs`, `--check-ac-basis`. Keep the distinction the
> v1 draft drew: AC matching is always complete because leapfrog matching
> enumerates sub-multisets, and what these flags turn on is the completion procedure
> in rebuild. Link chapter 11, which is where the three modes are explained and
> measured.

## Scheduling and selectivity

> `--runtime-scheduling`, `--auto-scheduling`, `--sampled-selectivity`,
> `--sampler-k`, `--sampler-bootstrap`, `--sampler-cv`, `--count-match-steps`.
> State the invariant that covers the whole group: they change the query plan and
> never the match set.

## Proofs

> `--proofs`, `--dump-proofs`. State which question proofs answer, and contrast it
> with the question anti-unification answers, since a reader who wants to know why
> two terms became equal is in the wrong part of the book and should be sent here.

## Selecting a mode from inside a file

> The first-six-lines directives, as a `text` block: `EXPECT`, `TYPES`, `EVAL`,
> `DERIVE_AC_EQS`, `LAZY_AC_EQS`, `UNION_BY`, `CHECK_AC_BASIS`, with defaults. State
> that they are read by the test harness rather than by the engine binary, that they
> must appear in the first six lines, and that every example in this book uses them
> so a file is self-contained. Point at `egraph/tests/egg_tests.rs` for the reader
> who wants to see the list in code.
