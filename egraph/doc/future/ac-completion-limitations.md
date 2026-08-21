# AC Completion: Limits and Validation Work

AC completion is opt-in. The default rebuild establishes ordinary congruence
closure. Two completion modes are available:

- **eager** (`--derive-ac-eqs`, `AcMode::Eager`, or `EGraph::set_cc(true)`):
  every rebuild runs completion;
- **lazy** (`--lazy-ac-eqs`, `AcMode::Lazy`): a failed equality check runs a
  semi-persistent mark/complete/restore transaction and stops early if its goal
  classes join.

Lazy mode is real on-demand completion. It is not incremental completion
performed silently during ordinary insertion.

The implemented correspondence is summarized in
[the completion specification](../design/ac-completion-spec.md). This file
records permanent scope limits and concrete work that is not yet discharged.
Each open item states the current implementation, the remaining gap, the task,
and acceptance criteria.

## 1. Resource Bound During Pair Generation

### Current state

`completion_node_budget` limits nodes added during one completion-enabled
rebuild. `cc_should_stop` is polled in the associative-only apply loop, the AC
inter-reduction apply loop, and the critical-pair close loop. The rebuild also
checks growth between rounds. Exceeding the limit is reported as
`CompletionOutcome::AbortedGrowthLimit`; it is not reported as convergence.
Pending ordinary congruence work is drained before returning.

The zero-budget regression in `tests/ac_matrix.rs` exercises that outcome and a
later recovery with a larger budget.

### Gap

The node budget does not bound critical-pair generation. `cc_round` constructs
the complete `crit` vector before either AC apply loop polls
`cc_should_stop`. Axiom pairs, overlapping-rule pairs, cancel-close pairs, and
cancelative disjoint superpositions can therefore consume substantial CPU and
memory while the node count remains unchanged. The cancelative pair scan is
quadratic in the number of active rules, and each queued pair owns both
reducts.

The present guarantee is consequently a materialized-node growth limit, not a
completion work or wall-time limit. A lazy goal that becomes true during this
phase is also not observed until generation finishes.

### Task

Add a deterministic completion-work budget separate from the node budget.
Count work before allocation, across every pair-generation path. The accounting
unit must include at least examined rule pairs, generated critical pairs, and
owned reduct entries; a chunked or streaming close loop may be used instead of
retaining the full vector.

Stopping for this budget must:

- return a distinct reported non-convergence outcome;
- preserve every equality already derived;
- drain pending ordinary congruence work;
- never let a truncated round report `Converged`; and
- remain configurable independently of the node budget.

Poll the lazy goal during long generation scans as well as during application.

### Acceptance criteria

- A fixture with many candidate pairs and no required node growth stops under a
  tiny work budget before the queued-pair storage exceeds that budget.
- Axiom, overlap, cancel-close, cancelative-disjoint, and associative-only work
  paths are each covered by a budget test.
- The result distinguishes work exhaustion, node-growth exhaustion,
  goal-directed success, and convergence.
- Raising the work budget and rebuilding the same graph can complete normally.
- Every equality returned before either abort is independently replayable from
  its justification.

## 2. Randomized ACI and Nilpotent Differential Oracles

### Current state

`tests/ac_vs_rules.rs` generates only plain binary `add` instances. It compares
native AC completion with an enumerative associativity-and-commutativity rules
encoding. Idempotent and finite-order nilpotent semantics are covered by
handwritten fixtures, including their semantic-axiom critical pairs.

### Gap

No randomized differential test exercises the clamp domains or the
per-rule axiom critical-pair generation. A future omission of an idempotent or
nilpotent axiom-pair arm could therefore pass the current randomized oracle.

### Task

Parameterize the generated instance by algebra:

- plain AC;
- ACI, with an idempotence rule in the bounded rules oracle; and
- nilpotent AC, with the selected finite-order law and identity handling in the
  bounded rules oracle.

Render the same generated declarations, terms, and asserted equalities into the
native and rules encodings. Compare the full partition over named terms.
Because enumerative saturation may hit its bound, classify oracle
non-convergence as inconclusive and retain the input for investigation; do not
classify it automatically as a native failure.

### Acceptance criteria

- A committed deterministic seed corpus covers all three algebras.
- Every oracle run records whether the rules side saturated before comparing
  partitions.
- A mutation that omits the idempotent axiom-pair arm is detected by at least
  one committed seed.
- A mutation that omits the nilpotent axiom-pair arm is detected by at least
  one committed seed.
- The larger randomized campaign remains an explicit ignored or Criterion-style
  test so the ordinary unit-test gate stays bounded.

## 3. Basis Determinism and Input-Order Invariance

### Current state

For a fixed admissible constant order, Kapur's reduced basis is unique. The
engine's constant order is derived from dense class ids, so declaration and
insertion order can change ids and can change the concrete basis
representation. This does not by itself imply a semantic difference.

The basis checker now reads both MSet and Set completion partitions and
normalizes in the operator's count domain. That representation bug is closed.

### Gap

No AC-completion test currently pins either:

- reproducibility of the basis for an identical program and id order; or
- semantic invariance of derived equalities when declarations are permuted.

Tests for determinism in the anti-unification subsystem do not cover this
completion property.

### Task

Add two independent checks:

1. Run a rule-heavy completion input repeatedly and compare a stable serialized
   basis projection, including runs in separate processes so randomized hash
   state cannot be hidden.
2. Run declaration-order permutations of one semantic input. Permit ids and
   concrete basis rows to differ, but compare the normalized equality partition
   and every corresponding check result.

Document next to the uniqueness claim that it is relative to a fixed constant
order.

### Acceptance criteria

- Identical inputs produce byte-identical stable basis projections.
- Declaration permutations produce equivalent equality partitions.
- The test contains an input whose concrete ids actually differ, so it cannot
  pass vacuously.
- The design documentation never states basis uniqueness without the
  fixed-order qualification.

## 4. Completion Proof Certificates

### Current state

`tests/ac_matrix.rs` exercises class-level `explain` reconstruction under all
four `(TRACK, PROOFS)` configurations. It asserts exact completion labels for
axiom critical pairs, inverse cancellation, cancellative closure,
superposition, and inter-reduction. The late-unit case asserts reconstruction
only; it does not assert a faithful unit-drop label. Generic deep
reconstruction tests cover MSet and Set congruence.

### Gap

The following are not yet established:

- completion-specific `explain_deep` paths that descend through the MSet or Set
  premises of each completion inference;
- an independent checker for exported completion steps;
- sufficient premises in every completion justification for such a checker to
  replay the inference; and
- faithful labels for all algebraic recanonization merges.

In particular, the Set singleton-collapse regression in
`tests/au_proof_certificates.rs` demonstrates that a merge between an ACI node
and a leaf is currently labeled `Congruence`, even though the nodes have
different operators. Deep expansion cannot recover the missing algebraic
premise from that label.

### Task

Define explicit justifications for unit drop, nilpotent empty collapse, and
singleton collapse. Extend completion justifications with the premise node ids
or compact witnesses needed to reconstruct overlap, clamp, cancellation, and
inter-reduction steps. Then add completion-specific deep tests and an
independent replay checker.

A shared certificate/checker specification must cover both AU projections and
AC completion. The AC tests here must establish that every completion label
accepted by that future checker has enough data.

### Acceptance criteria

- No algebraic merge between unlike operators is labeled ordinary congruence.
- Deep reconstruction traverses a nontrivial MSet premise and a nontrivial Set
  premise for every applicable completion label.
- A checker with no access to union-find internals accepts each valid exported
  fixture and rejects a fixture with a corrupted premise, multiplicity, or
  label.
- The tests run with `PROOFS=true` both with and without tracking, including a
  mark/restore/rederive sequence.

## 5. Late Inverse Pairs With Completion Disabled

### Current state

For an operator with `:inverse`, pair cancellation runs when a term is built
and during AC completion normalization. Ordinary congruence rebuild
recanonicalizes merged children, identity elements, and clamp counts, but it
does not re-run inverse-pair cancellation.

Consequently, `add(a, x)` built before `x = neg(a)` collapses to the unit when
completion runs, but not in the default completion-disabled mode.

### Gap

The same declared algebraic law has different late-merge behavior depending on
whether completion is enabled. This is not merely missing completion: build-time
canonization already treats inverse-pair cancellation as a definitional law.

### Task

Add a post-recanonization inverse-degeneracy path to ordinary congruence rebuild.
After child representatives settle, cancel inverse pairs, materialize or find
the residual canonical term, and merge it with the original node using an
explicit inverse-cancellation justification. The path must not start general AC
completion.

### Acceptance criteria

- A completion-off fixture derives `add(a, x) = e` after `x = neg(a)`.
- Residual cases such as `add(a, x, b) = b` are covered, including
  multiplicities and self-inverse classes.
- Eager, lazy, and completion-off modes agree on the equality.
- Proof-enabled configurations expose an `InverseCancel` step, not
  `Congruence`.
- Mark/restore removes and then permits re-derivation of the late equality.

## 6. Per-Constant Cancelative Closure After Late Introduction

### Current state

For cancelative operators without an identity, section 5.2(iii)(b) closure is
generated over the operator's current summand pool. A later full completion
round is intended to cover constants that enter that pool after an earlier
round. The static SC2 fixture exercises per-constant closure for constants
already present.

### Gap

The full-round argument for a constant introduced after earlier completion is
encoded in comments but has no focused regression or machine-checked invariant.
The static SC2 fixture does not test this incremental boundary.

### Task

Add a fixture that:

1. reaches a completion fixpoint;
2. introduces a new constant into an active monomial of the same operator;
3. rebuilds; and
4. checks the newly required per-constant consequence.

State and prove, or encode as an executable invariant, that a reported full
fixpoint has generated section 5.2(iii)(b) closure for every constant in the
then-current summand pool.

### Acceptance criteria

- The interleaved fixture passes in eager mode.
- The corresponding failed check triggers and passes in lazy mode.
- A negative control proves the consequence was not already present before the
  new constant entered the pool.
- A mutation that omits the full confirmation round or late-pool generation
  fails the fixture.

## 7. `CcSnapshot` Ownership Decision

### Current state

`CcSnapshot` represents both MSet and Set nodes. Its focused partner-selection
test compares the MSet path with brute-force candidate selection after
representative changes; the Set gate currently checks only that Set completion
nodes enter the snapshot. Production `cc_round` does not use `CcSnapshot`;
production finds candidates through class use-lists. The snapshot is currently
used only by tests and diagnostics.

### Gap

Two implementations encode the active completion-node and partner-selection
semantics. Representation coverage is tested, but a future change can still
make the unused snapshot drift from the production use-list path.

### Task

Choose one ownership model:

- make `CcSnapshot` the production round index and differential-test it against
  the use-list reference; or
- remove `CcSnapshot` and test the production candidate iterator directly
  against a brute-force oracle.

Keeping a production-dead duplicate is not a stable endpoint.

### Acceptance criteria

- There is one authoritative implementation of active-node filtering and
  partner selection.
- Both MSet and Set partner selection, user-subsumed nodes, and AC-collapsed nodes are
  covered.
- A brute-force property test compares candidate sets after representative
  changes.
- Module and method documentation names the implementation actually used by
  production.

## 8. Associative-Only Scope

### Current state

Associative-only operators flatten nested applications to an ordered sequence.
This is the canonical representation for equality generated solely by
associativity. When asserted ground sequence equations create the
erased-reference problem, the opt-in `a_round` performs shortlex-decreasing
inter-reduction. Its soundness has a transition-level paper argument and focused
tests, not an end-to-end machine-checked theorem.

The implementation deliberately does not chase critical pairs for arbitrary
ground sequence equations. That would be completion of a finite semi-Thue
system; the general finitely presented monoid word problem is undecidable.

### Gap

The narrow flattening theorem is not machine checked. It must also remain
clearly separated from the impossible broad claim that the current
inter-reduction pass completely decides arbitrary asserted associative
equations.

### Task

Formalize the structural result only:

```text
flatten(s) = flatten(t)
    iff s and t are equal in the free semigroup modulo associativity
```

Prove soundness and strict shortlex descent for each `a_round` rewrite. Keep
arbitrary ground-equation completeness explicitly out of scope; bounded
critical-pair exploration, if added, must report a bounded or incomplete
outcome rather than reuse an unqualified completeness claim.

### Acceptance criteria

- A proof or precise theorem citation establishes the flattening normal form.
- Property tests generate parenthesizations of the same word and distinct-word
  negative controls.
- Every `a_round` step has a replayable justification and decreases shortlex.
- `CompletionOutcome::Converged` and public documentation are explicitly
  scoped so they do not claim a decision procedure for arbitrary A-only ground
  equations.

## 9. Maximum-Partition Matcher Verification

### Current state

Chapter 9 defines the implemented matching relation independently of the
algorithm. For an existing AC or ACI node, scalar pattern variables consume
whole distinct child entries, multiplicity constraints apply to those complete
entries, and a rest variable receives the complete residual multiset or set.
`DecomposeAC` and `DecomposeACI` are exercised by focused fixtures and
plan-equivalence regressions.

This is finite evidence for the implementation's soundness. There is no theorem
that every emitted binding satisfies the relation or that every binding in the
relation is emitted.

### Gap

Matcher completeness is open even within the stated maximum-partition
semantics. The proof must cover pre-bound and nonlinear variables, intersected
multiplicity intervals, exact and rest patterns, cleanup during backtracking,
and canonical class ids. It must not silently broaden the relation to
term-valued classical AC matching: scalar variables range over existing
e-classes, not implicit sub-sums that have never been materialized. General AC
unification is broader still.

### Task

Define a small executable reference relation over canonical child
sets/multisets and prove:

1. every `DecomposeAC` and `DecomposeACI` result satisfies that relation;
2. every relation solution is reached by the continuation-driven decomposition;
3. backtracking preserves bindings made by earlier query steps and removes
   exactly the local bindings; and
4. composing decomposition with the surrounding query plan preserves the same
   match set.

Use Verus for the executable decomposition/refinement proof. If the
decomposition search is first modeled in a proof assistant, retain a refinement theorem
from the Rust state machine to that model. Before the universal proof lands,
add an independent exhaustive-small oracle and property generators for AC and
ACI nodes.

### Acceptance criteria

- Exhaustive enumeration agrees with production on all generated small
  patterns and subjects, including repeated multiplicities, nonlinear
  variables, pre-bound variables, empty residuals, and unsatisfiable
  intervals.
- Mutations that skip a candidate child, clear an earlier binding, or admit two
  scalar variables on one child are detected.
- An exported theorem states soundness and completeness for the precise
  maximum-partition relation.
- The theorem and public documentation explicitly exclude implicit sub-sum
  bindings, broader classical AC matching, and general AC unification.

## 10. Combined Saturation and Completion Termination

### Current state

The completion argument applies to one fixed finite pool of ground AC nodes.
The surrounding equality-saturation driver may run user rewrites that create
new terms between completion calls. Expanding rules can make that outer loop
diverge by design. Runtime iteration, node-growth, and alternation limits bound
selected executions, but they are operational limits rather than a general
termination theorem.

### Gap

There is no theorem for the combined rules-plus-completion loop. An
unconditional theorem is impossible for arbitrary productive rewrite systems,
and the current documentation does not define a useful restricted class under
which the two terminating components compose. Until the pair-generation work
budget in section 1 is implemented, a nominally bounded completion call also
has an unbounded amount of work before its next budget poll.

### Task

Specify both of the guarantees that are actually attainable:

1. a conditional termination theorem for rule systems with an explicit finite
   term universe or a well-founded rule-generation measure, composed with
   termination of completion over each resulting finite pool; and
2. a fuel-based operational theorem for the unrestricted driver, after every
   completion phase consumes the deterministic work budget from section 1.

The outcome model must distinguish a joint fixpoint from rule-iteration,
completion-work, completion-growth, and goal-directed stops. A joint fixpoint
requires one full rules round and one full completion confirmation round with
no change.

### Acceptance criteria

- The restricted theorem states checkable hypotheses on rule application and
  proves that completion cannot invalidate their decreasing measure.
- A committed expanding-rule counterexample prevents any unconditional
  saturation-termination claim.
- Every unrestricted loop has a decreasing fuel or work counter at each
  potentially unbounded phase.
- Exhaustion cannot be reported as `CompletionOutcome::Converged` or as a
  definitive failed equality check.
- A generated bounded-state oracle compares the joint driver with exhaustive
  closure on small systems.

## 11. Unsupported Full Abelian-Group Completion

The shipped group facet is pair-level inverse cancellation plus cancelative
closure. Full Abelian-group completion is not implemented: there is no signed
exponent representation, standardized rule basis, gcd or triangular
inter-reduction, or Gaussian-elimination equivalent. For example, deriving the
general linear consequence of `2a = b` and `3a = c` is outside the shipped
guarantee.

This is a permanent scope statement, not an active release task. If resumed,
the work requires a separate signed-monomial representation and correctness
argument; extending pair cancellation incrementally is not sufficient.

## 12. Release Claims

Documentation may claim:

- ordinary congruence closure by default;
- opt-in eager and lazy AC completion;
- a reported node-growth abort that preserves the same local soundness argument,
  drains plain congruence, and does not claim completion;
- class-level proof reconstruction for the tested completion merge kinds; and
- the explicitly listed implemented algebraic facets.

Documentation must not claim:

- that the node budget bounds critical-pair generation, memory, or wall time;
- basis invariance across different constant orders;
- independently checked completion certificates;
- full Abelian-group reasoning;
- complete arbitrary associative-only ground-equation reasoning; or
- complete maximum-partition matching;
- general termination of rules interleaved with completion; or
- end-to-end formally verified completion soundness or completeness.
