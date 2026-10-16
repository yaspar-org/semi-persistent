# Finite collection examples

The authoritative inventory is `../../manifests/collections.json`: four
upstream examples, 12 cases, and 36 engine/arm entries. Every case provides
original egglog, encoded egglog, and encoded ours programs. Each example
retains the exact upstream source as `upstream.egg`.

| Example | Validation | Negative control |
| --- | --- | --- |
| `map` | `update-3` | `negative-wrong-value` |
| `set` | `input-3` | `negative-multiplicity` |
| `unstable-fn` | `input-3` | `negative-wrong-result` |
| `eqsat-basic-multiset` | `input-3` | `negative-not-constant` |

The programs retain their audited observation checks. Manifest
`stdout_contains` oracles also retain the complete extraction expressions for
successful map and function-value cases. Native `map-of` contents correspond
to encoded `MCons` association lists; ours prints these simple string values
without quotes. `(SquareFn)` decodes to `(unstable-fn "square")`. These
representation changes do not preserve extraction spelling or cost.
All negative controls require an explicit check-failure diagnostic.

The encodings use runtime ordered lists for sets and maps, specialized
closure constructors for the source callbacks, and explicit bag operations
for the arithmetic multiset example. The set helper schedule and closure
dispatch schedule are bounded. The manifests document each adaptation,
retained observation, and limitation. These finite examples establish neither
the full native collection/callback APIs nor arbitrary-input equivalence.

The source and runnable-program hashes are recorded in the
[manifest](../../manifests/collections.json). The
[corpus validation record](../../validation.json) includes 72 executions
for this group on the fresh release build, in both modes and all listed
arms. Every execution matched its expected outcome. These are correctness
checks, not performance measurements.
