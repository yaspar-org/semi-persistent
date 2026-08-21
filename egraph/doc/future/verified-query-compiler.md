# Verified Query Compiler

## Current state

Resolved patterns are compiled into scheduled matcher steps and executed by the
optimized matcher. Differential, metamorphic, and fixture tests cover many plan
shapes, but the compiler and executor do not have a machine-checked refinement
theorem.

Historical defects show two distinct risks:

- backtracking cleanup can clear variables a step did not bind; and
- a literal atom can be emitted without its required lookup, making the rule
  unreachable.

Tests for the optimized matcher alone cannot exclude a shared compiler/executor
mistake.

## Gap

There is no verified invariant checker for executable plans and no independent
pattern-level matcher that can serve as a semantic oracle.

## 1. Verified Plan Validator

Define a reified plan model and validate it when a rule is installed. At
minimum, require:

- every variable is bound before it is read;
- every cleanup action clears exactly the bindings introduced by its step;
- every source atom contributes a reachable check or lookup;
- literal atoms carry a literal lookup;
- guards execute only after all of their inputs are bound;
- node and e-class variables are not interchanged; and
- AC/ACI decomposition steps carry the multiplicity and rest-variable metadata
  required by their source pattern.

Validation failure must reject the rule rather than fall back to unchecked
execution.

## 2. Independent Reference Matcher

Specify match sets directly over the e-graph model and resolved pattern:

- plain and commutative fixed-arity matching;
- ordered subsequence semantics for associative operators;
- maximum-partition AC/ACI semantics;
- literal and equality atoms;
- global bindings; and
- guards.

Implement the specification as a deliberately simple executable matcher and
prove its emitted bindings sound. Use it as a differential oracle for the
scheduled matcher. It must not call the production scheduler or reuse its plan
steps.

## 3. Compiler Refinement

The final theorem relates plan execution to the reference semantics:

```text
validate(plan, pattern)
  && execute(plan, graph) = matches
  ==> matches == reference_matches(pattern, graph)
```

If completeness is staged separately, first prove subset soundness and keep the
missing direction explicit.

## Acceptance criteria

- The validator verifies without `admit`, `assume`, or a new trusted axiom.
- Seeded plans reproducing every known cleanup, missing-lookup, read-before-bind,
  and guard-order defect are rejected.
- The independent matcher reproduces the committed pattern corpus at the
  specified snapshot boundary.
- Generated small e-graphs compare complete normalized binding sets, not only
  match counts.
- AC/ACI tests include multiplicity, rest-only, bound-element, identity, and
  negative-control cases.
- The refinement theorem, when delivered, names whether it proves soundness,
  completeness, or equality.
