# Proofs

Lean 4 formalizations of the two correctness arguments of the egraph crate,
and the programs that reproduce the two incompleteness findings.

## lean/

A Lake project pinned to Mathlib v4.35.0 (`lean-toolchain`,
`lakefile.toml`). Build:

    cd proofs/lean
    lake exe cache get   # fetches the prebuilt Mathlib oleans, about 7 GB on disk
    lake build

Every theorem is sorry-free and depends only on `propext`,
`Classical.choice` and `Quot.sound`; `SemperProofs/CC/Check.lean` and
`SemperProofs/EMatch/Check.lean` print the axiom audit.

- `SemperProofs/CC/`: AC congruence completion. `completion_sound` (no
  merge leaves the equational theory), `completion_complete_at_convergence`
  (two active nodes equal in the theory share a class, at a fixed round,
  under the engine- and law-level hypotheses listed in its docstring),
  `SlotState.fix_sufficient` and `reachable_I5` (the min-monomial slot
  refresh keeps the slot the degree-lex-least active monomial of its class
  through every operation), `shrinkNoRefresh_breaks_I5` (the state of
  `proofs/repro/min-slot-gap.egg` as a counter-model without the refresh).
- `SemperProofs/EMatch/`: leapfrog e-matching under maximum-partition
  semantics. `ematch_sound` and `ematch_complete` for the reference plan
  compiler and the list-based reference interpreter.
- `STATUS.md`: statements in words, hypotheses in engine terms, the stub
  statements that were false and how they were corrected, and what is not
  modelled.

## repro/

- `min-slot-gap.egg`: fails `check-eq` before commit 231ac1b, passes after.
  `min-slot-gap-control.egg`: the same facts asserted in another order,
  passes before and after.
- `assoc-incomplete.egg`, `assoc-incomplete-witness.egg`: a consequence of
  two associative-only equations that completion does not derive, because
  `a_round` reduces and never superposes; the header explains why no
  terminating completion can be complete for associativity alone (the word
  problem for finitely presented semigroups is undecidable).
