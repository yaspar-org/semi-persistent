# Command-line flags

This chapter is the flag reference, in five groups: representation, saturation
strategy, AC completion, scheduling and selectivity, and proofs.

```bash
semi-persistent <FILE> [OPTIONS]
```

One positional argument, the path to an `.egg` program. Query output goes to
stdout; the closing `ok — N nodes` line goes to stderr, so redirecting stdout
gives you just the answers.

Nothing below is needed for the use in this book. The defaults are the
configuration every example runs under. The flags exist because the engine is
also a research artifact, and several of them exist specifically to compare two
implementations of the same semantics against each other.

## Representation

This section covers the flags that change how the e-graph is stored.

| flag | default | meaning |
| --- | --- | --- |
| `--id-bits <31\|63>` | `31` | e-class identifier width |
| `--push-pop <diff\|clone>` | `diff` | `diff` is the semi-persistent undo log; `clone` deep-copies |
| `--types <groups>` | `bignum` | comma-separated literal type groups: `machine`, `bignum` |

`--id-bits 31` packs an e-class key into a single ring cell. `--push-pop clone`
is the reference implementation `diff` is differentially tested against, and it
is not currently wired up for every path.

## Saturation

This section covers the flags that change how rounds are evaluated and which
representative survives a merge.

| flag | default | meaning |
| --- | --- | --- |
| `--use-naive` | on | full re-match each round |
| `--use-semi-naive` | off | delta-driven rounds; mutually exclusive with the above |
| `--union-by <rank\|size\|uses\|sum>` | `rank` | merge survivor policy |

The two evaluation strategies must produce the same match sets, and the two
scheduling modes likewise; the test suite runs example files under both and
compares. `--union-by` changes which representative survives a merge, and so
changes work and printed representatives, not which equalities hold.

## AC completion

This section covers the three completion flags and separates AC matching, which is
always complete, from the completion procedure in rebuild, which is off by
default.

| flag | default | meaning |
| --- | --- | --- |
| `--derive-ac-eqs` | off | run completion rounds (superposition and inter-reduction) during rebuild |
| `--lazy-ac-eqs` | off | run goal-directed completion only when an equality check needs it, inside a transaction that is then rolled back |
| `--check-ac-basis` | off | check reduced-basis invariants each completion round and report; diagnostic, needs `--derive-ac-eqs` |

With completion off, leapfrog matching still enumerates sub-multisets of AC
nodes, so AC **matching** is complete; what is off is the completion procedure
in rebuild. This distinction is the subject of
`ac-congruence-completeness.md`, and it is the reason `(check (!= ...))` is a
statement about the implemented search rather than a semantic theorem. The two
flags are mutually exclusive.

## Scheduling and selectivity

This section covers the flags that change the query plan, and states what holds
the match set fixed across all of them.

| flag | default | meaning |
| --- | --- | --- |
| `--runtime-scheduling` | off | order a rule's atoms per binding from live bucket lengths |
| `--auto-scheduling` | off | choose the mode per rule per round; skewed joins get per-binding ordering |
| `--sampled-selectivity` | off | price a bound key by sampling the emitter's relation |
| `--sampler-k <n>` | `32` | emitter nodes drawn per sampled estimate |
| `--sampler-bootstrap <n>` | `0` | bootstrap resamples guarding an estimate; 0 disables |
| `--sampler-cv <f>` | `1.0` | coefficient of variation above which an estimate is discarded |
| `--count-match-steps` | off | count total e-matching steps |

`--runtime-scheduling` and `--auto-scheduling` are mutually exclusive. All of
these change the query plan, never the match set, and the finite differential
tests of design chapter 20 check that.

## Proofs

This section covers the two proof flags and states which question proofs answer,
as against the one anti-unification answers.

| flag | default | meaning |
| --- | --- | --- |
| `--proofs` | off | record a justification for every merge |
| `--dump-proofs <FILE>` | | write one proof-path record per e-node after the program finishes; requires `--proofs` |

Proof recording answers "why are these two terms equal", which is the
complementary question to the one this book asks. Anti-unification reports where
two terms are *not* equal; a proof explains a specific equality the engine
derived, which is what you want when saturation collapsed something you did not
expect it to.
