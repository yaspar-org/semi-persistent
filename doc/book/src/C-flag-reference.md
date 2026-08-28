# Annex C. Flag reference

The command-line form is:

```text
semi-persistent [OPTIONS] <FILE>
```

`FILE` is the required path to one Semper program.

## Representation and literal model

| Flag | Values | Default | Effect |
| --- | --- | --- | --- |
| `--id-bits` | `31`, `63` | `31` | Select 31-bit or 63-bit e-class identifiers. |
| `--push-pop` | `diff`, `clone` | `diff` | Select scope storage. `diff` uses semi-persistent logs; `clone` is accepted as a value but currently exits with “not yet implemented.” |
| `--types` | `machine`, `bignum` | `bignum` | Select comma-separated literal groups. `machine,bignum` enables both groups. |
| `--proofs` | flag | off | Record merge justifications for proof extraction. |
| `--dump-proofs FILE` | path | none | Write one proof-path record per e-node after execution. Requires `--proofs`. |

The machine group provides `i64`, `u64`, `f64`, `usize`, `String`, and `bool`;
the bignum group provides `IBig`, `UBig`, `RBig`, `String`, and `bool`.

## Saturation and completion

| Flag | Default | Effect |
| --- | --- | --- |
| `--use-naive` | selected | Explicitly select full re-matching each round. Conflicts with `--use-semi-naive`. |
| `--use-semi-naive` | off | Select delta-driven saturation. |
| `--derive-ac-eqs` | off | Run eager AC completion during rebuild. Conflicts with `--lazy-ac-eqs`. |
| `--lazy-ac-eqs` | off | Run goal-directed AC completion for equality and disequality checks. |
| `--check-ac-basis` | off | Print expensive reduced-basis invariant checks during eager completion. It has no effect without `--derive-ac-eqs`. |
| `--count-match-steps` | off | Count and report matching work. |

[Chapters 9](09-naive-and-semi-naive.md) and
[11](11-three-congruence-closures.md) define the evaluation and completion
modes.

## Matching and union policies

| Flag | Value | Default | Effect |
| --- | --- | --- | --- |
| `--runtime-scheduling` | flag | off | Choose atom order per binding from live bucket lengths. Conflicts with `--auto-scheduling`. |
| `--auto-scheduling` | flag | off | Select static or per-binding atom ordering for each rule and round. |
| `--sampled-selectivity` | flag | off | Estimate bound-key fan-out by sampling the emitter relation. |
| `--sampler-k` | nonnegative integer | `32` | Set emitter nodes drawn per sampled estimate. Relevant with `--sampled-selectivity`. |
| `--sampler-bootstrap` | nonnegative integer | `0` | Set bootstrap resamples per estimate; zero disables the guard. |
| `--sampler-cv` | floating-point number | `1.0` | Reject a bootstrapped estimate when its coefficient of variation exceeds this threshold. |
| `--union-by` | `rank`, `size`, `uses`, `sum` | `rank` | Choose the surviving representative by union-find rank, class size, use-list length, or size plus uses. |

These policies change operational work and representative choice, not the
equalities asserted by the input program.

## Help

| Flag | Effect |
| --- | --- |
| `-h`, `--help` | Print the generated command-line help. |

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
