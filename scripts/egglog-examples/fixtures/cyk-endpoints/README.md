# Finite CYK endpoint example

The authoritative inventory is `../../manifests/cyk-endpoints.json`: one
upstream example, three cases, and nine engine/arm entries. Every case
provides original egglog, encoded egglog, and encoded ours programs.

| Case | Observation |
| --- | --- |
| `source-801` | Original 801 mixed/nested JSON tokens; root presence, root definedness, and absence of conflicting trees |
| `validation-4` | Nine tokens; all 28 saved positive chart facts and 40 sampled negative facts |
| `ambiguous-three` | Three tokens and an added ambiguous production; native merge rejection and encoded conflict-check rejection |

`cykjson/upstream.egg` is the byte-exact upstream source. Its three active
CSV inputs are preserved at `cykjson/tests/cykjson_Prod.csv`,
`cykjson/tests/cykjson_End.csv`, and
`cykjson/tests/cykjson_small_token.csv`. The upstream program can resolve its
original relative input paths when run from `cykjson`. The commented-out
medium input is outside this selected source case.

All manifest programs are self-contained: their grammar and token facts
are inlined from the CSV inputs. They retain all three parsing rules. Encoded terminals
use `[pos,pos+1)`; both composition rules join `[start,mid)` with `[mid,end)`.
The coordinate map is `(span,start) -> (start,start+span)`. All existing
presence guards and free-tree conflict validation remain unchanged.
Original arms retain span/start coordinates, native no-merge tables, and
`run 10000`. Encoded arms retain `compute 10000`, then `validate 10000`, and
the two ours-only statistics commands.

The source root lookup's returned tree is otherwise unused. `HasB 1 802
"VAL"` preserves that lookup's definedness, and `P 1 802 "VAL"` preserves
root membership. There is no independent full-chart oracle or tree-output
comparison for source-801. It represents 801 tokens, not a 400-element flat
array and not an additional independent CYK family.

`cykjson/observations.json` associates each case with its archived input
JSON, source-data hashes, root mapping, schedule, and oracle scope.
`cykjson/validation-4/oracle.json` contains only the selected original
span/start oracle and its existing endpoint mapping, with provenance for the
full audit oracle. Its positive facts and sampled negatives are executable
assertions in the validation programs. It does not exhaust negative facts or
compare all engine states or parse-tree outputs.

The audit labeled every ambiguity arm `runtime_failure`. The manifest
refines the two encoded arms to `check_failure`, matching their actual
explicit `Conflict` checks, and retains native `runtime_failure` for
`Illegal merge attempted for function B`. Literal diagnostic oracles prevent
unrelated failures from satisfying the control. The program bodies remain
unchanged; only a provenance/license comment was prepended.
Encoded rejection occurs after conflict validation, so rejection timing
differs from native no-merge behavior.

The scope requires finite immutable positive positions/spans without i64
overflow and free immutable `T`/`NT` trees. Arbitrary tree unions, evolving
keys, runtime CSV APIs, general no-merge tables, arbitrary-input equivalence,
and performance improvements are not claimed.

The source and runnable-program hashes are recorded in the
[manifest](../../manifests/cyk-endpoints.json). The
[corpus validation record](../../validation.json) includes 18 executions
for this group on the fresh release build, in both modes and all listed
arms. Every execution matched its expected outcome. These are correctness
checks, not performance measurements.
