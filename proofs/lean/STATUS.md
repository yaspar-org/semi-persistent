# Status of the Lean development

Lean 4 with Mathlib v4.35.0. `lake build` of the whole project passes;
`grep -rn sorry SemperProofs/` is empty; every `#print axioms` in the
`Check.lean` files prints only `propext`, `Classical.choice`, `Quot.sound`.
Written 2026-11-04 after the second extension.

## CC: AC-congruence closure (`SemperProofs/CC/`)

- `completion_sound`: invariant I2 (nodes of one class are `=_E`-equal) is
  preserved by every inference step.
- `completion_complete_at_convergence`: at a fixed round, `=_E`-equal active
  nodes are in one class. Hypotheses: slot maintenance with the refresh
  (`SlotState.OpsStar`, `I5` initially, `Agrees`), `I0Active`, `hcanon`,
  `RoundFixed`, law facts `hlaw`/`hnf_ax`/`hcp`, `hcc`, `hS`, `hcancel`.
- `reachable_I5`, `fix_sufficient`, `shrinkNoRefresh_breaks_I5`: the
  min-monomial refresh keeps I5; the unrefreshed shrink is the repro state.
- `kapur_termination`, `run_stabilizes`, `confluent_modulo`, `newman`.
- `Laws/`: concrete instances `identity`, `nilpotent`, `idempotent`,
  `inverse` (the engine's one-directional walk `invWalk`, proved normalizing
  by `invNormal_invWalk`), `combined`; `hlaw` and `hnf_ax` discharged;
  `completion_complete_{identity,nilpotent,idempotent,inverse,combined}` with
  `hcp` reduced to rule-side conditions: `RuleRuleCP`, and for `:inverse`
  `InvMatching`, `InvUnitFree`, `InverseAxiomCP`, `NilpotentInverseCP`,
  which the engine did not establish (four confirmed gaps, `proofs/repro`).
- `Laws/InvRules*.lean`: the five rules R1-R5 the engine now applies
  (injectivity and involution of the inverse, inverse against the unit,
  rule-inverse critical pairs, the nilpotent-inverse pairs) as inference
  steps; `inv_rules_sound` extends soundness; `RoundFixedInv`,
  `RoundFixedInvUnit`, `RoundFixedInvNil` discharge the four hypotheses
  (`invMatching_of_fixed`, `invUnitFree_of_fixed`,
  `inverseAxiomCP_of_fixed`, `nilpotentInverseCP_of_fixed`), giving
  `completion_complete_inverse_engine` and
  `completion_complete_combined_engine` with engine-level hypotheses only,
  plus the retirement-order invariant I3.

## EMatch: e-matching (`SemperProofs/EMatch/`)

- Base (`Defs`, `Ref`, `Main`): `MatchN`/`MatchC` (maximum partition),
  reference compiler and interpreter, `ematch_sound`, `ematch_complete`,
  per-step decomposition lemmas. `join` binds node and class (`joinBind`).
- `Engine/`: atoms (`atoms_iff_match`), lowering under any bound set
  (`lower_sound_complete`), scheduler plan grammar (`Sched`, `PlanOK`,
  `plan_matches`, `engine_plan_sound/complete`), runtime scheduling
  (`runND_matches`, `runND_indep`), `byOp_demotion`, semi-naive
  `variant_partition`/`variants_disjoint`/`variants_cover_new`.
- `Engine/Rounds/`: the cross-round half of semi-naive matching. A
  `Round` is the transition between two frozen snapshots with the deferred
  unions, the added nodes, subsumption, the touched log and the
  merge-membership delta; `Round.WF` is what rebuild guarantees.
  `delta_complete`: for tracked matching, a binding that satisfies a rule's
  atoms after the round and not before binds some join atom to a new node;
  `semi_naive_round_complete` and `semi_naive_complete` over a chain of
  rounds compose it with the within-round partition. Counter-models
  `delta_incomplete_global` (an equality with a global, the sixth engine
  gap, fixed by routing such rules to naive matching) and
  `delta_incomplete_untracked` (why the merge-membership delta exists).
  Not modelled: `:flatten` and sequence rules across rounds, action
  application, the transport of bindings through later merges.
- `Flatten/`: opening trees, views, normalization, demand; `views_sound`,
  `views_complete`, `flatten_match_{sound,complete}_{ac,aci,assoc}`;
  `Fix.lean`/`FixMain.lean`/`FixKind.lean`: the corrected demand rule
  (`acceptsFix`: a leaf is satisfied when it holds a taken class or its
  opened class is taken), `demand_fix_complete_{ac,aci,assoc}`,
  `demand_fix_no_redundancy_*`, `accepts_imp_acceptsFix`; the original rule
  is complete for sequences (`demand_orig_complete_assoc`) and for sets under
  `TwoClasses` (`demand_orig_complete_aci`), which rebuild guarantees by
  merging a one-child member into its child's class; `acceptsKind` is the
  engine's per-kind rule (`merge_on_close` for multisets only).
  `Laws.lean`/`LawsMain.lean`: the rule under laws for any `Laws` (identity,
  nilpotent, inverse, composed): a leaf is also satisfied when closing it is
  not inert (`nonInertB`: its class is the unit, its refolded count clamps
  to zero, or a cancellation pair touches it); `refold_normalize_inert`,
  `demand_laws_complete_{ac,aci,assoc}` (the sequence case no longer needs
  `NoNullary`), `demand_laws_no_redundancy_*`, `acceptsFix_imp_acceptsLaws`;
  five executed counterexamples against the kept-count rule in
  `LawsCheck.lean`.
- `Steps/`: globals, literals, `CheckNeq`, `CheckPred` with faults,
  `CopyBinding`/`BindGlobal`, `Collect` (sequence patterns: A and AC/ACI
  relations, filters, `:except`, dedup, the bound as a hypothesis);
  `step_sound`/`step_complete`, `collect_sound`/`collect_complete`,
  `xplan_wf_sound`, `core_lifts`.
- `Env/`: the engine's mutable `Match` with undo; `env_restore`,
  `env_refine` (set equality with the reference interpreter under `WF`),
  `comm_pair_duplicate`, `ac_nodup`, `RoundSnapshot`.

## Not modelled

View bounds `MAX_VIEWS`/`MAX_WORK`/`MAX_ELEMS` and multiplicity widths
(hypotheses only); the index skip predicates; cross-round delta
completeness; the galloping cursor (Verus, containers-verus); faults inside
sequence sub-queries; `Nodup` of emitted lists (membership only).
