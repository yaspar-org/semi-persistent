# Proofs

Lean 4 formalizations of the correctness arguments of the egraph crate, and
the programs that reproduce the incompleteness findings they led to.

## lean/

A Lake project pinned to Mathlib v4.35.0 (`lean-toolchain`,
`lakefile.toml`). Build and gate:

    cd proofs/lean
    lake exe cache get          # the prebuilt Mathlib oleans, about 7 GB on disk
    bash scripts/check-proofs.sh   # lake build, then the two gates

The gates: no declaration uses `sorry`, and every `#print axioms` in the
`*Check.lean` files reports only `propext`, `Classical.choice` and
`Quot.sound`. CI runs the same script (`.github/workflows/lean.yml`) on
every change under `proofs/lean`. Cost with the Mathlib cache present: a
clean build of the project's own modules takes 82 s wall on 14 cores (Apple
M4 Pro, 2026-11-04), and the gates about 70 s more; expect several times
that on a 4-core runner, plus the cache download.

- `SemperProofs/CC/`: AC congruence completion. `completion_sound`,
  `completion_complete_at_convergence`, the min-monomial slot invariant I5
  and its preservation by the fixed engine (`reachable_I5`,
  `fix_sufficient`, `shrinkNoRefresh_breaks_I5`), termination
  (`kapur_termination`), confluence modulo the laws. `Laws/`: the concrete
  identity, nilpotent, idempotent and inverse clamps of `nary_canon`, the
  completeness theorem instantiated for each, and `InvRules*.lean`: the
  five inverse rules the engine applies at rebuild and in completion, proved
  sound and sufficient (`completion_complete_inverse_engine`,
  `completion_complete_combined_engine`).
- `SemperProofs/EMatch/`: e-matching under maximum-partition semantics.
  The reference plan (`ematch_sound`, `ematch_complete`); `Engine/`, every
  plan the scheduler can produce, runtime scheduling, the ByOp demotion,
  semi-naive variants; `Flatten/`, views, the demand rule, its corrected
  form and the per-kind rule (`demand_fix_complete_ac`,
  `demand_kind_complete_*`), and the rule under laws
  (`demand_laws_complete_*`); `Steps/`, globals, literals, predicates and
  the sequence-pattern engine; `Env/`, the mutable match environment with
  undo refines the reference interpreter (`env_refine`, `env_restore`).
- `STATUS.md`: the theorems in words with their hypotheses, the stub
  statements that were false and how they were corrected, and what is not
  modelled.

The implementation invariants these proofs and the conformance generators
found, each with the engine section that explains it, are listed in
`egraph/doc/design/13-soundness.md`, §5.

## repro/

Each program fails `check-eq` on the engine before the named commit and
passes after; the `*control*` programs pass before and after.

- `min-slot-gap.egg` (commit bb961302): the min-monomial slot not refreshed
  on an in-place shrink.
- `demand-gap.egg` (commit d95883f5): the `:flatten` demand rule rejects a
  match whose untaken leaf opened a taken class.
- `inv-into-unit.egg`, `unit-inverse.egg`, `non-matching.egg`,
  `rule-inverse-cp.egg`, `z3-inverse.egg` (commit e1e6aec8): the five
  consequences of the inverse law across nodes, rules R1 to R5.
- `aci-overaccept.egg`, `aci-overaccept-ac.egg`: probes, not failures: a
  redundant set match the demand rule admits, and its multiset analogue
  which it rejects.
- `assoc-incomplete.egg`, `assoc-incomplete-witness.egg`: a consequence of
  two associative-only equations that completion does not derive, because
  `a_round` reduces and never superposes; the header explains why no
  terminating completion can be complete for associativity alone (the word
  problem for finitely presented semigroups is undecidable).
