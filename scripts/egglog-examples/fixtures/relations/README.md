# Finite relation examples

The authoritative inventory is `../../manifests/relations.json`: six upstream
examples, 16 cases, and 46 engine/arm entries. Each example retains the exact
upstream bytes in `upstream.egg` and provides original egglog, encoded egglog,
and encoded ours programs for its source case.

| Example | Additional cases |
| --- | --- |
| `points-to` | `updates-scopes`, `ignore-load-field` |
| `schedule-demo` | `steps-2`, `steps-5` |
| `relation-query-allowed` | `third-row`, `identity-counterexample` |
| `test-combined` | `late-edge` |
| `test-combined-steps` | `steps-3`, `snapshot-counterexample` |
| `stratified` | `phase-boundaries` |

Accepted encodings keep each relation's row identity separate from its
presence witness: `AuditHolds_<relation>(Row) = AuditPresent`. Constructing a
row does not establish membership, and distinct rows are never unioned.
The shared-marker identity counterexample deliberately violates this
invariant and must fail. The snapshot counterexample deliberately executes
combined children sequentially and must fail. These two counterexamples have
only encoded arms because the audit supplied no native counterpart.
`ignore-load-field` deliberately removes a field-identity guard and fails in
all three arms.

All source and validation assertions remain executable in the copied files.
Negative controls also require the specific literal diagnostic in the
manifest. Bounded saturation expansion relies on the named schedule's
one-step frontier invariant. The manifests document the other adaptations
and limits per example. These are finite examples, without a claim of full
native relation APIs or arbitrary-input equivalence.

The source and runnable-program hashes are recorded in the
[manifest](../../manifests/relations.json). The
[corpus validation record](../../validation.json) includes 92 executions
for this group on the fresh release build, in both modes and all listed
arms. Every execution matched its expected outcome. These are correctness
checks, not performance measurements.
