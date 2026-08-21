# Conformance and Release Work

The e-graph executes on `semi-persistent-containers-verus`. The legacy
`semi-persistent-containers` crate remains an independent reference used by
`containers-conformance`; it is not a second production implementation.

This document records compatibility and validation work that remains after the
production cutover. Correctness claims continue to come from Verus contracts and
the trust-boundary inventory. The differential and performance suites provide
finite evidence for the executable boundary.

## 1. Consumer `Tagged` Law Tests

### Current state

The canary exports `tagged_fuzzer_template::check_tagged_laws` and applies it to
a consumer-shaped fixture. The e-graph defines the actual `Tagged`
implementations for `Justification`, `PoolDirector`, `FixedArityNode`,
`VariableArityNode`, and `LitNode`, as well as macro-generated id families.
Those implementations are outside the crate Verus verifies.

### Gap

No property test applies the law checker to each production implementation. A
bad representation round trip or tag operation could corrupt capture state
without violating the verified container core's assumptions.

### Task

Add property generators for every production `Tagged` family and run the common
law checker on representative values, including boundary ids, every enum
variant, and tag-set/tag-clear sequences. Macro-generated ids need at least one
representative at each supported width.

### Acceptance criteria

- Every e-graph `Tagged` implementation is named by a property test.
- Round trip, value preservation under tag changes, and idempotent set/clear
  laws are checked.
- Tests include maximum in-range payloads and explicit filler/default values.
- The trust-boundary table links to the per-type tests rather than only to the
  shaped canary.

## 2. B+ Header History

### Current state

`BPlusTreeSet::header_archive` is a plain stack of
`(root, key_count, last_leaf)` tuples maintained in parallel with the node
arena's snapshot history. A verified agreement invariant keeps the two stacks
in lockstep.

### Gap

Branch history is encoded twice. The implementation is sound under its current
proof, but a new header field or restore path must manually preserve the
parallel-stack agreement.

### Task

Represent the mutable header through the standard snapshot/fork-history
machinery, or introduce an equivalent verified header journal shared with the
arena token. Remove the independent archive only after nested restore and
branch-cut behavior are expressed by the common token model.

### Acceptance criteria

- One mechanism determines header and arena snapshot ancestry.
- Reused, foreign, and abandoned-future tokens are rejected before mutation.
- Nested mark/restore property tests cover `root`, `last_leaf`, and key count.
- The replacement verifies without adding a trusted contract.

## 3. Package and Reference Cutover

### Current state

The e-graph aliases package `semi-persistent-containers-verus` as
`semi-persistent-containers`. The legacy package remains in the workspace only
as the independent differential and performance reference.

### Gap

Package identity still exposes the migration-era name, while removing the
legacy crate now would also remove an independent executable oracle.

### Task

Define an explicit cutover:

1. publish and consume the verified package under the production package name;
2. preserve a version-pinned reference implementation while differential
   evidence remains useful; and
3. retire the reference only after its maintained oracles have replacements.

### Acceptance criteria

- `cargo publish --dry-run` succeeds for the renamed package and its dependants.
- License and dependency-policy checks accept the packaged Verus runtime.
- No production dependency aliases one package under another package's public
  name.
- Removing the reference crate does not remove the only oracle for any claimed
  shared behavior or layout.

## 4. Reduced Miri Contract Fuzzing

### Current state

The property suites exercise total APIs, misuse traps, and trusted executable
contracts under ordinary Rust execution. Historical one-off Miri runs found no
issue.

### Gap

There is no maintained Miri workflow. Large property counts and some
dependencies make the default suites unsuitable for direct Miri execution.

### Task

Add an environment-controlled reduced case count and run the trusted-contract,
token-misuse, vector, sparse-set, list, and B+ property slices under Miri on a
scheduled or explicitly triggered workflow.

### Acceptance criteria

- The reduced mode changes only case counts and sizes, not asserted
  properties.
- The workflow covers mark/restore, branch cuts, boundary ids, and packed
  representation operations.
- Miri failures retain the seed and operation trace.
- Ordinary CI remains bounded; the Miri job is scheduled or manually
  triggerable.

## 5. Criterion Coverage

### Current state

`containers-conformance` uses Criterion confidence intervals rather than fixed
wall-time or ratio gates. It covers vector batch insertion and rollback,
untracked list operations, map/intern workloads, sparse-set churn, B+ insertion
and seeking, nested marks, and aggregate `EClasses` workloads. Isolated restore
and class-ring splice/walk/restore rows preserve the useful phase measurements
from the retired custom gate.

### Gap

No paired Criterion row currently covers:

- B+ `TRACK=true` mark/restore;
- clustered B+ insertion traces with real e-graph round and restore boundaries;
- miss-heavy `SpMap` lookup;
- tracked `ListArena`;
- standalone reference-versus-verified `SortedVecCursor`;
- use-list-heavy paired `EClasses`;
- reference-versus-verified `Vec` iteration;
- allocation counts across corresponding implementations; or
- phase-separated B+, map, and sparse-set operations where a complete cycle can
  hide a local regression.

### Task

Add paired rows as a consumer workload needs them. Use `iter_batched_ref` or
`iter_batched` with `BatchSize::LargeInput` to keep fixture construction out of
the measured phase. Run registration orders separately when allocator history
can affect one arm. Record Criterion estimates, bootstrap confidence intervals,
host, revision, and configuration; do not convert them into a fixed-ratio CI
gate.

For B+, retain anonymized key-arrival traces from representative e-graph index
updates, including clustered inserts, round boundaries, marks, restores, and
query bursts. Compare those traces with random and ascending controls under
`TRACK=true`. The historical untracked synthetic sweep favored 256-byte nodes,
while the maintained default remains `Layout64U32`; change that default only
after the tracked trace reports time, split count, touched-node bytes, retained
memory, and restore cost across layouts.

Count slow-insert right-spine recomputations of `last_leaf`, nodes touched per
split, and bulk-load/cursor boundary checks. If a representative trace
attributes material cost to them, evaluate threading a rightmost-leaf result
through recursive insertion and crate-private proved-bound helpers for verified
bulk-load/cursor call sites. Public misuse checks stay intact; no historical
microbenchmark ratio alone justifies weakening that boundary.

### Acceptance criteria

- Every claimed performance-sensitive compatibility surface has a
  mechanism-specific Criterion row.
- Restore, mutation, and traversal phases remain separable.
- B+ layout selection includes tracked clustered traces and reports memory as
  well as time; a default change names the target architecture and workload
  envelope it is based on.
- A retained B+ optimization moves its named recomputation, touched-node, or
  boundary-check counter on the same trace that improves in Criterion.
- Allocation-parity claims use a counting allocator in addition to elapsed
  time.
- Reports identify source revision and host state.

## 6. API and Derive Compatibility

### Current state

The verified implementation intentionally differs from the reference in total
error-returning APIs, token validation, deterministic hashing, visibility, and
some trait implementations. The e-graph uses the verified surface directly.

### Gap

There is no promised compatibility matrix for external consumers. Restoring
missing aliases or `Default`/`Clone`/`Debug`/`Hash` derives mechanically could
reopen invalid states or imply compatibility the crate does not support.

### Task

Publish a supported compatibility matrix before expanding the facade. Classify
each item as source compatibility, behavioral compatibility, intentional
divergence, or unsupported legacy surface. Add aliases and derives only when
their invariants and executable behavior are specified.

### Acceptance criteria

- The supported matrix is narrower than, or equal to, the tested surface.
- Intentional panic/error and token-semantic differences remain explicit.
- Each restored trait or alias has a compile fixture and, where behavioral, a
  differential test.
- Compatibility work is not described as a correctness proof.

## 7. Proof-Forest Verification

### Current state

Proof-parent and justification columns participate in the verified storage and
mark/restore invariants. Path reversal in `reroot_proof` and proof-tree walking
for explanation are trusted executable glue over those columns.

### Gap

There is no ghost acyclicity/forest invariant or proof that rerooting preserves
it. The explanation algorithm therefore must not be described as verified even
though its storage is verified and runtime tests exercise it.

### Task

Add a ghost forest model relating every proof-parent edge to the executable
columns. Prove that edge insertion and path reversal preserve acyclicity,
connectivity, and justification alignment. Then verify that explanation reaches
a common ancestor and emits a valid adjacent path.

### Acceptance criteria

- `reroot_proof` no longer relies on an unverified path-reversal body.
- Every parent walk has a decreasing argument derived from the forest model.
- Mark/restore preserves the modeled proof forest at every archived frame.
- Differential tests compare verified explanations with an independent graph
  walk, including reroot-heavy and restored traces.

## 8. Const-Generic Tracking Refinement

### Current state

The vector primitive and composites verify for both values of `TRACK`.
Code inspection and generated-code measurements show that const-gated capture,
diff, and restore work is absent when `TRACK=false`. The structs still contain
empty diff, frame, and fork-history fields, and callers still execute general
runtime checks not guarded solely by the const generic.

### Gap

There is no relational theorem comparing tracked and untracked executions.
Current evidence supports execution elision with retained empty-state fields,
not observational equivalence between instantiations, zero layout overhead, or
a minimum-layout result.

### Task

Define a projection that erases tracking metadata and prove that equal initial
source data remains equal after the same sequence of operations available in
both modes. Start at the vector primitive, then lift the relation through maps,
sets, lists, union-find, and `EClasses`. Keep snapshot operations outside the
untracked API relation: `mark` and restore must continue to refuse when
tracking is disabled.

Pair the theorem with compiler-version-scoped code-generation checks for the
tracking-only write and restore paths. Treat those checks as erasure evidence,
not as a semantic proof.

### Acceptance criteria

- The exported theorem relates return values and source-of-truth data for every
  shared public operation.
- The composite proof is derived from the primitive relation rather than from
  duplicated per-container assumptions.
- Untracked snapshot refusal is tested and is not weakened to make the
  relation easier to state.
- Layout documentation continues to count the retained empty fields and does
  not claim zero memory overhead.
- Code-generation evidence names the compiler and target and fails if a
  tracking-only write or restore call reappears in the untracked hot path.
