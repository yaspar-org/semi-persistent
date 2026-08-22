# Runtime Performance Validation

Performance work must use maintained workloads and statistically robust
estimates. Machine-sensitive fixed wall-time or ratio gates are not evidence:
Criterion's warm-up, adaptive sampling, outlier analysis, and bootstrap
confidence intervals are the default for local microbenchmarks. Cross-process
campaigns must retain every sample, binary hashes, source state, and host
metadata.

## 1. Semi-Naive Rules Regression

### Current state

The retained `final-r6` campaign reports
`math-microbenchmark.rules` at 396.3 ms under naive evaluation and 1165.3 ms
under semi-naive evaluation. Native encoding is approximately equal between the
two strategies. The campaign measured a predecessor source snapshot on a loaded
host using process medians without bootstrap confidence intervals. These values
identify a historical candidate, not a demonstrated current regression or a
machine-independent ratio.

Semi-naive evaluation explores fewer partial-match extensions in general, but
its k-variant scheduling, full-minus-delta cursors, and rule-level overhead can
still cost more on a particular rule shape.

### Gap

No current Criterion result establishes that the roughly threefold historical
rules-only difference persists, and no phase attribution explains it if it
does.

### Task

Add a Criterion workload for the translated rules program, preserving the same
source, run budget, scheduler, and union policy. Measure:

- index full and delta builds;
- variant planning and cursor construction;
- matching by rule and variant;
- rule application and rebuild; and
- total rounds, matches, and match steps.

Compare naive and semi-naive with identical fixture construction outside the
timed body. Test whether the existing delta-size fallback and trigger-prefilter
proposals predict the measured expensive rounds before implementing either.

### Acceptance criteria

- The regression appears in Criterion with non-overlapping or otherwise
  statistically interpreted confidence intervals.
- Node/class outcomes and normalized equality partitions agree.
- At least one measured phase accounts for the majority of the delta.
- A fix is retained only when its mechanism-specific counter moves with wall
  time on this workload and does not regress the broader saturation suite.

## 2. Proof-Forest Re-root Allocation

### Current state

With `PROOFS=true`, `UnionFind::reroot_proof` allocates `vec![x]` for every
justified merge and grows it along the proof-parent path. Existing runtime
performance suites mostly instantiate `PROOFS=false`.

### Gap

The allocation mechanism is visible in code but its contribution to
proof-enabled saturation and bulk proof export is unmeasured.

### Task

Add proof-enabled Criterion rows and allocation counters for merge-heavy,
rewrite-heavy, and batch-export workloads. If the allocation is material,
replace it with a reusable scratch path owned by the proof columns or a borrowed
`ProofBuf`.

### Acceptance criteria

- Measurements separate merge logging from explanation/export.
- The optimized path performs no per-merge allocation after warm-up.
- Proof paths and all-term dumps are byte-equivalent modulo explicitly
  nondeterministic metadata.
- `TRACK=true` mark/restore truncates reusable scratch and proof state
  correctly.

## 3. AC Completion Attribution and Driver

### Current state

AC completion allocates while generating critical pairs, owned reducts,
normalization scratch, and materialized nodes. The node-growth budget does not
bound pair-generation work or queued memory. Dense canonical bases can require
genuine `O(critical pairs x rules)` subset tests.

### Gap

Allocation and phase attribution are not retained in a Criterion workload.
Without that attribution, a local buffer change cannot be distinguished from
an algorithmic pair-count problem.

### Task

Instrument and benchmark:

- candidate-pair scans;
- generated and retained pairs;
- owned reduct entries;
- normalization calls;
- materialization and merge counts; and
- peak queued bytes.

First implement the deterministic completion-work budget specified in
`ac-completion-limitations.md`. Evaluate streaming pair closure or a per-round
worklist only if the counters show avoidable retained or repeated work. Preserve
the full confirmation round required for a convergence report.

### Acceptance criteria

- Criterion rows cover a small convergent case and a budget-stopped dense case.
- Every proposed allocation change moves allocation or peak-byte counters.
- A truncated round cannot report convergence.
- A worklist or streaming driver produces the same normalized partition and
  replayable justifications when both runs converge.

## 4. Directed-Merge Root Walks

### Current state

The use-count survivor policy finds both roots to compare their use lists, then
the merge core resolves its arguments again. Fully compressed trees usually
make those walks short.

### Gap

There is no measurement showing that an already-canonical-root entry point
would move end-to-end time, and forcing survivor policies can create deeper
union-find trees.

### Task

Count root-walk hops by policy in the `EClasses` Criterion workload and a
representative saturation workload. Add an internal merge-from-roots API only
if duplicated walks are material. Its precondition must establish that both
arguments are current roots; the public total API remains unchanged.

### Acceptance criteria

- Hop counts and elapsed time are reported together.
- A new root entry point is verified against the ordinary merge model.
- Stale or non-root inputs cannot reach the unchecked internal path.
- The broader saturation suite shows a confidence-interval-supported benefit.

## 5. AU Solver Allocation and Transport Attribution

### Current state

Pair-mode root Exact and the side- or pair-context MCGS/delegation paths retain
several allocation and recomputation costs that are visible in code but not
isolated by a maintained Criterion benchmark:

- pair-mode root Exact materializes the complete reachable pair graph and clones each
  generated structural action into that graph;
- every relaxation round clones the full quality and witness vectors;
- AC/ACI root actions rebuild lower-bound and achieved-cost matrices and may
  run two transport solves per action per round when pruning is enabled;
- contextual MCGS transport recomputation rebuilds matrices for value and term
  composition;
- `TermPool::intern` and `ContextStore::intern` allocate owned vector keys
  before determining whether the key is already interned;
- contextual child derivation allocates and sorts temporary vectors; and
- snapshot best-term discovery scans every e-node until a full pass makes no
  change.

The ignored AU timing harnesses and retained corpus records measure solver
outcomes at selected inputs. Records captured before `exact_fixed.rs` are
historical evidence for the predecessor contextual root solver and cannot be
used as current pair-mode root-Exact comparisons. None provide Criterion confidence
intervals or attribute time and allocation to these mechanisms.

### Gap

There is no stable evidence showing which path dominates pair-graph discovery,
relaxation, AC transport, MCGS, context-heavy delegation, or large-snapshot
workloads. The AU quality-at-time and delegation numbers also have not been
refreshed across one common implementation with cycle policy recorded.
Consequently, caching,
dirty-bit, scratch-buffer, interner, or worklist changes cannot be accepted on
mechanism alone, and one optimization may merely move cost between phases.

### Task

Add an AU Criterion suite with at least five fixture families:

- a non-AC root pair with many reachable pairs and structural actions;
- a long cyclic chain that requires many root-Exact relaxation rounds;
- an AC/ACI root pair with large transport matrices;
- a cyclic, context-heavy UCT/delegation pair with high context-interner reuse;
  and
- a large e-graph whose best-term fixpoint needs multiple passes.

Record counters for pair states/actions discovered, relaxation rounds, quality
and witness-vector bytes copied, context and term interner hits/misses and key
bytes, child-context temporary bytes, transport solve calls and matrix cells,
composition offers, best-term passes, and e-node visits. Keep snapshot and
fixture construction outside a solver-only timed row, and retain an end-to-end
row that includes snapshot cost.

Use the attribution before selecting an implementation:

- compact or lazily discover pair actions only if graph materialization
  dominates and the change preserves complete deterministic enumeration;
- use in-place double buffers or dirty worklists only if full-round copying or
  unchanged-state scans dominate, preserving synchronous-round semantics or
  proving an equivalent schedule;
- use borrowed-key lookup or reusable owned scratch only if interner key
  allocation is material;
- version transport children, skip unchanged value/composition solves, and
  reuse session-owned matrices or network storage if repeated solves dominate;
  and
- replace the best-term full scan with parent-driven propagation only if node
  visits, rather than unrelated snapshot work, dominate.

### Acceptance criteria

- Criterion reports estimates and confidence intervals for solver-only and
  end-to-end rows, with allocation counters reported alongside time.
- One campaign reruns root Exact, UCT, and delegation from the same source and
  binaries, recording `CycleMode` for every row and comparing like policies,
  before any AU timing or crossover number is promoted to
  `doc/claims.md` or the future paper.
- Every retained optimization moves its mechanism-specific counter and the
  corresponding workload estimate.
- Exact result quality, projection validity, deterministic tie behavior,
  timeout accounting, and proof-certificate data are unchanged.
- Transport reuse preserves the exact integer solver for lexicographic
  composition and the documented quantization boundary for MCGS values.
- A best-term worklist agrees with the full-scan oracle on generated cyclic and
  acyclic e-graphs, including unreachable classes and saturated-size cases.

## 6. Evidence-Triggered Work

The following changes were previously measured as neutral or negative. They
remain valid designs only under the listed revival condition:

| Change | Revival condition |
| --- | --- |
| Extraction worklist | A maintained workload needs more than two fixpoint passes. |
| Shared-subterm extraction | The API returns a shared DAG; memoizing an owned `Term` still deep-copies hits. See `max-sat-extraction.md`. |
| Stride-hinted galloping | Advance distance is predominantly unimodal in `d = 4..64`, or a substantial measured share is `d >= 1024`. |
| Incremental B+ index maintenance | A workload is restore-heavy or interleaves queries and updates enough to beat bulk rebuild under Criterion. |
| RHS comprehension borrow split | A maintained comprehension workload attributes material allocation or time to copying match slices. |
| Pre-mark union-find compression | Directed merges produce materially deep trees in a hop histogram. |
| Branchless multiset duplicate merge | Recanonization is frequent on wide multisets and the duplicate branch is near unpredictable, rather than rare. |
| AC RHS-shift delta enrichment | A round census shows noninitial, nonfinal full rounds recovering work missed after rule RHS classes shift. |
| Indexed completion candidates | The union of per-child candidate lists is measured to be substantially smaller than the active rule set. |
| Compact class-ring cells | A production consumer performs dense ring walks or a memory profile attributes material footprint to ring cells. |
| Sorted or sparse span metadata | Index construction dominates probing on a maintained workload; the prior sorted prototype saved build time but lost overall because each probe became `O(log occupied keys)`. |
| Operator-qualified `by_child_pos` keys | Mixed-operator child-position buckets are both common and long enough that splitting them saves more probe work than the larger key space costs in memory and build time. |
| Per-binding leapfrog driver selection | Live bucket asymmetry leaves material time in seek after adaptive operator filtering; measure candidate steps and seek time separately from runtime atom ordering. |
| Per-binding bucket-resolution cache | Runtime ordering or adaptive operator filtering spends material time resolving the same immutable-snapshot lookup more than once at one binding; count resolutions and scope any cache to one plan step and index mode. |
| Residual AC/ACI matcher allocation | A maintained decomposition workload still allocates materially more per emitted match than plain matching after pool recycling; attribute allocation sites before changing match storage again. |
| Online join feedback | One rule dominates a round and its surviving intersections are much smaller than either input bucket, so plan-time marginal and sampled estimates remain predictably wrong. |
| Persistent per-rule profiles | The same ruleset runs repeatedly over sufficiently similar e-graphs for prior-round observations to predict later plans without destabilizing first-run behavior. |
| MCGS transport quantization | An exact-rational decision oracle finds selection distortion, values exceed the fixed-grid precision envelope, or transport still dominates after buffer reuse. Any replacement needs a termination argument and an explicit exact-versus-approximate contract. |

These are not active performance claims. A revival requires a current workload,
mechanism-specific counters, Criterion estimates, and unchanged correctness
oracles.

## 7. Reporting Contract

- Report point estimates with confidence intervals, sample count, outliers,
  host, toolchain, and source revision.
- Keep fixture construction out of the timed phase with `iter_batched` or
  `iter_batched_ref`.
- Separate phases when a complete cycle can hide a regression.
- Confirm time attribution with an allocation, instruction, hop, pair, or match
  counter appropriate to the proposed mechanism.
- Treat loaded-host campaign observations as qualified evidence and rerun under
  controlled conditions before publishing absolute timing.
- Never turn a machine-sensitive ratio into an uncalibrated CI pass/fail gate.

For cross-engine release claims, add a Criterion harness that invokes both
pinned release binaries on the same translated corpus and treats process setup
consistently. Keep `compare.py` for semantic validation, structural statistics,
and provenance until that harness exists; its process medians alone are not a
release-performance result.
