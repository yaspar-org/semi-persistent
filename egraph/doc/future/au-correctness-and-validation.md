# Anti-Unification Correctness and Validation

[Anti-Unification design](../design/19-anti-unification.md)

The production exact solver has extensive finite differential and property
evidence. The current Verus model proves objective-order, representation, and
positional lower-bound lemmas. It does not prove the target theorem
`D(A, B) = OPT(A, B)`, and it does not model the production AC/ACI and search
machinery.

This document separates the theorem work from validation and calibration of the
shipping implementation.

## 1. Positional `D = OPT`

### Current state

The Verus recurrence predicate requires its value to be no greater than each
available action. The lower-bound induction proves that such a value is below
every represented positional term pair. It does not require equality with the
least action, and the constant-zero function satisfies the current predicate.

Representation lemmas establish that structurally assembled terms exist, but
their postconditions do not yet connect an assembled witness's quality to the
chosen recursive action.

### Gap

No exported theorem states that the recurrence value is attained or equals the
minimum represented anti-unifier quality.

### Task

1. Define the recurrence by equality with the minimum action value, or construct
   its least solution explicitly.
2. Prove every state has a nonempty finite action set and that its minimum can
   be selected.
3. Strengthen the structural witness lemma with recursive witness-quality
   premises and an assembled-quality postcondition.
4. Prove the selected value is attained by represented terms, including the
   treatment of cyclic e-classes.
5. Combine attainability with the existing lower-bound induction in one
   exported equality theorem.

### Acceptance criteria

- The final theorem's postcondition states equality with `OPT`, not only a
  lower-bound inequality.
- A zero recurrence cannot satisfy the strengthened recurrence except when zero
  is the actual optimum.
- The proof constructs or identifies an attaining represented witness.
- Verification passes without `admit`, `assume`, or a new trusted axiom.

## 2. Refinement to the Production Solver

### Current state

The formal model is positional Plotkin anti-unification. Production additionally
uses:

- AC/ACI transportation with multiplicities;
- identity padding and canonical representatives;
- cycle contexts and context subsumption;
- projection bounds and incumbent pruning;
- Monte-Carlo graph search; and
- exact/MCGS delegation with a shared semi-persistent session.

These mechanisms have named finite oracles and regression suites, but they are
not refinements of the Verus recurrence yet.

### Gap

Even a completed positional `D = OPT` theorem would not by itself establish
optimality or correctness of the shipping AC/ACI solver and search
optimizations.

### Task

Define one refinement boundary per mechanism. Each theorem must relate a
production action or pruning decision to the abstract action graph:

- transport actions denote exactly their multiplicity-preserving projections;
- identity padding and canonicalization preserve both source classes;
- cycle filters remove only invalid cyclic derivations;
- every lower bound is admissible;
- pruning removes no action below the live incumbent;
- context subsumption preserves the feasible result set; and
- delegated exact results compose with MCGS bounds and certificates.

Porting the full solver to Verus is an alternative, larger implementation
strategy. Until a refinement is proved, keep its claim finite and test-scoped.

### Acceptance criteria

- Every production-only mechanism is either covered by a refinement theorem or
  explicitly listed as tested-only.
- Refinement tests include a mutation that violates the corresponding theorem's
  premise or conclusion.
- The exact and MCGS implementations consume one specified action semantics.
- Public optimality claims name the exact theorem boundary they rely on.

## 3. Universal Optimization Lemmas

### Current state

The following properties have exhaustive-small-instance or property-test
evidence:

- `lb_pair` never exceeds the enumerated optimum;
- edge-count multiplication accounts for sharing in the tested unfolded
  graphs;
- AC transport agrees with exhaustive member matching on bounded cases; and
- optimum quality is independent of member enumeration and representation
  order on the tested cases.

### Gap

Finite enumeration does not establish these properties for arbitrary e-graphs,
multiplicities, or cycles. Each property is used to justify a production
optimization or representation choice.

### Task

Prove four independent lemmas:

1. **Bound admissibility:** every valid projected witness has quality at least
   `lb_pair`.
2. **Edge-count sharing:** the recurrence's edge multiplicities equal the
   objective's unfolded occurrence count while state memoization remains
   representation sharing only.
3. **AC transport:** every feasible integral flow corresponds to valid left and
   right projections, and the minimum flow cost equals the least action cost for
   fixed child qualities.
4. **Representation independence:** changing member order or choosing another
   representation of the same e-class pair does not change `OPT`.

### Acceptance criteria

- The universal statements quantify over supported multiplicity widths and
  include identity-padded cells.
- Cycle-context premises are explicit rather than hidden in an acyclic model.
- Existing finite oracles remain as executable correspondence tests.
- A proof failure cannot be masked by increasing property-test bounds.

## 4. Independent Formalizer Validation

### Current state

`tests/au_formalizer_pilot.rs` scores two policy-controlled renderings produced
by one formalizer against a constructed oracle. It establishes that the
pipeline and metrics run on the tested corpus; it is not evidence about
independent formalizers.

### Gap

Outputs from one system can share conventions and correlated mistakes. The
pilot does not measure inter-system variation or population validity.

### Task

Collect formalizations produced independently, without access to each other's
outputs. Preserve the current constructed-oracle scoring: report backbone
precision/recall, variation-point placement, canonization-only agreement, and
invalid projection rates separately.

### Acceptance criteria

- At least two independent formalizers contribute held-out outputs.
- Inputs, prompts or policies, raw formalizations, and scoring configuration
  are retained.
- Invalid formalizations are reported rather than silently excluded.
- Claims remain scoped to the sampled signatures, systems, and corpus.

## 5. AC Action-Enumeration Startup Cost

### Current state

Before a playout, an AC root enumerates representation pairs and runs transport
feasibility for each pair. Scaling fixtures show startup cost can exceed exact
solve time even when `hybrid_ms` is zero, so the cost is not delegated work.

### Gap

The engine has no cheap prefilter or lazy representation-pair iterator with a
stated completeness condition.

### Task

Attribute startup work by pair count, transport cells, feasibility failures,
and retained actions. Evaluate sound prefilters and lazy enumeration under
Criterion or a statistically equivalent harness. Any lazy order must retain
fairness or provide a certificate that all potentially better pairs were
considered.

### Acceptance criteria

- Measurements separate graph construction, pair enumeration, feasibility, and
  playout time.
- A proposed filter has an independent oracle proving it removes only
  infeasible or dominated pairs on bounded instances.
- Exact results and deterministic action order remain unchanged unless a new
  order is part of the specification.
- Improvements reproduce with confidence intervals on a scaling family.

## 6. Hybrid and Delegation Decision Rule

### Current state

A constructed family in `tests/au_delegation.rs` demonstrates that exact
delegation can reach the same value sooner when the rollout error lies in
shallow subproblems exact search can absorb. Control families show that
delegation otherwise adds cost. Existing tests therefore establish a profitable
region, not a generally profitable policy.

### Gap

Admission uses local thresholds rather than a calibrated instance-level rule.
Several historical families record `hybrid_ms = 0`, so they cannot calibrate
delegation cost or benefit.

No retained family makes rollout regret compound with depth. Nested-decoy
placements tried so far do not compose: increasing depth adds search work but
does not multiply the quality error. The current evidence therefore cannot
support a claim that delegation prevents compounding rollout error.

### Task

Build a calibration corpus spanning:

- shallow-correctable and globally hard instances;
- a depth-indexed family whose independently checked optimum shows compounding
  rollout regret, plus controls demonstrating that the effect is not merely a
  larger action count;
- globally exact-solvable instances;
- AC roots dominated by representation-pair startup; and
- controls where delegation performs work but cannot improve the incumbent.

Fit or derive a decision rule from observable pre-search features. Validate it
on held-out families and compare at equal wall time, not only equal playout
count.

### Acceptance criteria

- Calibration rows include nonzero delegated calls and `hybrid_ms`.
- Bare MCGS, delegated MCGS, and exact search use identical objective and
  timeout accounting.
- The selected rule improves a preregistered quality-at-time metric on held-out
  instances without regressing the control envelope beyond its stated bound.
- For the depth-indexed family, greedy and delegated quality are reported
  against an exact or constructed optimum at every depth; any claimed
  compounding law is fitted on held-out depths and includes uncertainty.
- The fallback remains deterministic and sound when the rule declines
  delegation.

## 7. Exact-Solved Subgraph Publication

### Current state

Session-level exact memoization preserves context-clean bare-pair terms and
support sets across hybrid calls. A completed hybrid call offers its root term
to the requested MCGS OR state and marks that state exact. The exact solver's
other completed frames stay in its private search space or bare-pair memo; they
are not published as exact-marked MCGS states.

### Gap

When a later playout reaches a subframe that exact already solved internally,
MCGS may reconstruct and expand the corresponding overlay state before the
root-only bridge can benefit it. Publishing every safe completed frame could
turn those states into terminal nodes immediately, but the state keys include
cycle contexts and mode while the reusable session memo intentionally erases
contexts only under a support-disjointness condition.

### Task

Define a publication record that maps a completed exact frame to the identical
MCGS `(left, right, left-context, right-context, cycle-mode)` state. Publish a
term and exact marker only when completion is proved for that state. A
context-clean bare-pair entry may serve another context only after the existing
support-disjointness check; budget-exhausted, cycle-tainted, or merely
incumbent frames must never be marked exact.

Make publication transactional with the shared session. Mark/restore must
rewind terms, results, exact markers, and any created overlay nodes together.
Track published nodes and bytes so a configurable budget can prevent exact
delegation from growing the shared overlay without bound.

### Acceptance criteria

- Every published state agrees in term quality and completion status with an
  independent exact solve started at the same full state key.
- With publication enabled or disabled, root terms, certificates, deterministic
  ties, and timeout accounting are identical.
- A funnel workload shows completed exact subframes becoming terminal without a
  second exact call or MCGS expansion.
- Mark/restore removes all publication effects and permits deterministic
  re-publication.
- Criterion reports hybrid time, MCGS expansions, exact calls, published-state
  count, and peak shared bytes; the feature is retained only with a measured
  quality-at-time or work reduction inside its memory budget.
