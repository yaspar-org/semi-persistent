# Annex C. Flag reference

The command-line form is:

```text
semi-persistent [OPTIONS] <FILE>
```

`FILE` is the required path to one Semper program.

## Representation and literal model

| Flag | Values | Default | Effect |
| --- | --- | --- | --- |
| `--bits` | `32`, `64` | `32` | Width preset, by storage word: 31-bit ids with 32-bit multiplicities, or 63-bit ids with 64-bit multiplicities. Operator and sort ids are 31-bit in both. Every operation on a count is checked: a count past the width is reported as `multiplicity overflow: …` with the width and its maximum. `--id-bits` is an alias, and either spelling accepts `31` for `32` and `63` for `64`. |
| `--cost-bits` | `32`, `64`, `big` | `big` | An optional signed cap on a cost model's values and on the cost `(extract … :cost m)` reports; `big` sets none. Arithmetic is exact either way, and a value outside the cap is a reported error naming the operation. Each solver's own range is checked separately, before it runs ([Part V](24-extraction-under-cost-models.md)). |
| `--push-pop` | `diff` | `diff` | Select scope storage. `diff` uses semi-persistent logs. `clone` is a reserved value: the argument parser rejects it, since no deep-copy backend exists, and the program exits with status 2. |
| `--types` | `machine`, `bignum` | `bignum` | Select comma-separated literal groups. `machine,bignum` enables both groups. An unknown group exits with status 1. |
| `--proofs` | flag | off | Record merge justifications for proof extraction. |
| `--dump-proofs FILE` | path | none | Write one proof-path record per e-node after execution, and report the record count on standard error. Requires `--proofs`. |

The machine group provides `i64`, `u64`, `f64`, `usize`, `String`, and `bool`;
the bignum group provides `IBig`, `UBig`, `RBig`, and `bool`.

## Saturation and completion

| Flag | Default | Effect |
| --- | --- | --- |
| `--use-naive` | selected | Explicitly select full re-matching each round. Conflicts with `--use-semi-naive`. |
| `--use-semi-naive` | off | Select delta-driven saturation. Conflicts with `--use-naive`. |
| `--derive-ac-eqs` | off | Run eager AC completion during rebuild. Conflicts with `--lazy-ac-eqs`. |
| `--lazy-ac-eqs` | off | Run goal-directed AC completion for equality and disequality checks. Conflicts with `--derive-ac-eqs`. |
| `--check-ac-basis` | off | Print expensive reduced-basis invariant checks during eager completion. It has no effect without `--derive-ac-eqs`. |
| `--count-match-steps` | off | Count matching work and report `match steps: N` on standard error after the closing status. |
| `--flatten-rhs` | off | Give an AC node a rewrite builds a flat alternative for each same-operator child kept nested because its class is used elsewhere; not for operators with `:inverse`. |

[Chapters 9](09-naive-and-semi-naive.md) and
[11](11-three-congruence-closures.md) define the evaluation and completion
modes.

## Matching and union policies

| Flag | Value | Default | Effect |
| --- | --- | --- | --- |
| `--runtime-scheduling` | flag | off | Choose atom order per binding from live bucket lengths. Conflicts with `--auto-scheduling`. |
| `--auto-scheduling` | flag | off | Select static or per-binding atom ordering for each rule and round. Conflicts with `--runtime-scheduling`. |
| `--sampled-selectivity` | flag | off | Estimate bound-key fan-out by sampling the emitter relation. |
| `--sampler-k` | nonnegative integer | `32` | Set emitter nodes drawn per sampled estimate. Relevant with `--sampled-selectivity`. |
| `--sampler-bootstrap` | nonnegative integer | `0` | Set bootstrap resamples per estimate; zero disables the guard. Relevant with `--sampled-selectivity`. |
| `--sampler-cv` | floating-point number | `1.0` | Reject a bootstrapped estimate when its coefficient of variation exceeds this threshold. Relevant with a nonzero `--sampler-bootstrap`. |

The parser does not enforce the three "relevant with" conditions: the value is
accepted and has no effect.
| `--union-by` | `rank`, `size`, `uses`, `sum` | `rank` | Choose the surviving representative by union-find rank, class size, use-list length, or size plus uses. |

These policies change operational work and representative choice, not the
equalities asserted by the input program.

## Help

| Flag | Effect |
| --- | --- |
| `-h`, `--help` | Print the generated command-line help. |

An unknown flag or an invalid value exits with status 2 and a usage line.

## Test directives

The test harness in `egraph/tests/egg_tests.rs` reads directives from the first
eight lines of a program. Each directive mirrors a flag; pass the flag when
running the file by hand.

| Directive | Values | Default | Flag |
| --- | --- | --- | --- |
| `;; EXPECT:` | `ok`, `check-failed`, `parse-error`, `sort-error`, `error` | `ok` | none; the expected outcome |
| `;; MESSAGE:` | text | none | none; the outcome's message must contain the text |
| `;; WARNING:` | text, or `none` | none | none; some warning must contain the text, one directive per warning, or no warning may be raised |
| `;; TYPES:` | as `--types` | `bignum` | `--types` |
| `;; EVAL:` | `naive`, `semi`, `both` | `both` | `--use-naive` or `--use-semi-naive` |
| `;; DERIVE_AC_EQS:` | `on` | off | `--derive-ac-eqs` |
| `;; LAZY_AC_EQS:` | `on` | off | `--lazy-ac-eqs` |
| `;; CHECK_AC_BASIS:` | `on` | off | `--check-ac-basis`; the harness also asserts the invariants after a successful run |
| `;; UNION_BY:` | `rank`, `size`, `uses`, `sum` | `rank` | `--union-by` |

The harness runs every file under both the static and the runtime
atom-scheduling modes, with the 32-bit preset and without proof recording.

## Feature-gated diagnostics

Two environment variables affect binaries built with optional instrumentation
features; they are not command-line flags:

| Build feature and environment | Effect |
| --- | --- |
| `phase-timing`, `EGRAPH_PHASE=1` | Print aggregate rebuild, indexing, matching, and application timings at exit. |
| `phase-timing`, `EGRAPH_PHASE=rounds` | Also print one timing line per saturation round. |
| `seek-stats`, `EGRAPH_SEEK=1` | Print leapfrog seek-distance histograms at exit. |

Without the corresponding Cargo feature, setting the environment variable has
no effect.
