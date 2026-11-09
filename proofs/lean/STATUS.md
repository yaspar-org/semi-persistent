# Status of the Lean development

Lean 4 with Mathlib v4.35.0. `lake build` of the whole project passes;
`grep -rn sorry SemperProofs/` is empty; every `#print axioms` in the
`Check.lean` files prints only `propext`, `Classical.choice`, `Quot.sound`;
`scripts/check-proofs.sh` checks both. This file is the per-file index of the
development: which theorems each directory holds and what each states in one
clause. [`GUIDE.md`](GUIDE.md) states the main theorems in full with their
hypotheses classified, the conformance tests (its Section 8), the remaining
gaps (Section 9) and the constraints on the engine (Section 10); section
numbers below refer to it. [`HISTORY.md`](HISTORY.md) records the dates, the
commits and the withdrawn claims.

## Final theorem (`SemperProofs/Final/Store.lean`, `Final/Main.lean`)

- `Final/Store.lean`: `saturation_modulo_complete_store_atoms`, the final theorem
  in its strongest form (store rounds `SActRoundN`, matches on the index,
  consequences as normal forms `FiredN`, `:subsume` allowed, the completion
  state with leaf constants `CompleteAtoms` entering through `SubRep` on the
  index); `saturation_modulo_complete_store` (with `CompleteHyps`),
  `_store_engine` (the engine's stop test), `_store_cover` (with `FCover`),
  `_store_atomic` (with `CompleteAtomic`), and
  `saturation_modulo_complete_store_retired` and `_retired_atoms` (with
  `SubRepR` over active and retired nodes, `FCover` over both, `I2`, `I3`:
  every match of the index, a match rooted at a retired node included). The
  statement, its reading and its hypotheses: GUIDE Section 7.7.
- `Final/Witness.lean`: `witness_saturation_modulo_complete`,
  `witness_fires_modulo`, `witness_saturation_modulo_complete_retired`,
  `witness_fires_retired`, `witness_saturation_modulo_complete_atomic`,
  `not_cover`, `retired_class`: every hypothesis of the store theorems proved
  on two rounds of `(rewrite (+ x y) (g x y))` and `(rewrite (+ x y z) k)`
  over the state of `AtomsWitness`, by hand and `decide` (GUIDE Section 7.7).
- `Final/Closed.lean`: `theoryClosed_of_complete`, the store's closure under the
  theory (`TheoryClosed`) derived from the completion state through the
  correspondence: `readClass`, `readMset` read a store class and a child
  multiset in the state, `ACStep.readE` and `EqAC.readE` read a normalization
  chain as an `=_E`-equality (the inverse of `ACStep.mapE`), `ACStep.count_mod`
  and `eq_of_chain_not_noded` keep a class holding no node out of every chain
  but the trivial one, `closedAC_of_complete` closes the AC operator of the
  state; `LawsRead` (the laws read alike), `SummandsAtomic` (the summands'
  classes hold their atoms), `TheoryClosedRest` the remainder (the other
  operators, the ACI and A theories). `saturation_complete_closed_of_complete`
  and `_atoms`: `saturation_complete_closed` with the completion hypotheses in
  place of `TheoryClosed` (GUIDE Section 6.5).
- `Final/Main.lean`: the literal forms `saturation_modulo_complete`,
  `saturation_modulo_complete_atoms` (`A.R.after = represents st f act`,
  literal `Den`; vacuous for a rule set with a match whose right-hand side
  builds a node other than an active `f`-multiset node, as their docstrings
  state, limit 3), `saturation_modulo_complete_sub` and
  `saturation_modulo_complete_within` (with `SubRep`), `matches_at_active`,
  `matches_at_sub`, and `saturation_modulo_sound`, the soundness of one
  matching run on the represented graph (not a converse of completeness).
  GUIDE Sections 7.2 to 7.6.
- Hypotheses no theorem discharges (`SubRep`, `CompleteAtoms` with `hlat`,
  the per-law conditions `LawSpec.Conds`, the minimal-monomial
  hypotheses, the round facts, `TheoryClosedRest`): GUIDE Section 9.

## CC: AC-congruence closure (`SemperProofs/CC/`)

- `completion_sound`: invariant I2 (nodes of one class are `=_E`-equal) is
  preserved by every inference step.
- `completion_complete_at_convergence`: at a fixed round, `=_E`-equal active
  nodes are in one class. Hypotheses: minimal-monomial maintenance with the
  refresh (`SlotState.OpsStar`, `I5` initially, `Agrees`), `I0Active`,
  `hcanon`, `RoundFixed`, law facts `hlaw`/`hnf_ax`/`hcp`, `hcc`, `hS`,
  `hcancel`. The bundles `CompleteHyps` and `CompleteAtoms` take
  `hlat : L.cancellative → LatticeClosed` in its place, so the final theorems
  rest on what `lattice_round` establishes. `RoundFixed` states the engine's
  three checks (`nf_present`, `lhs_reduced`: no rule's left-hand side
  reducible by another rule, `cp_joinable` over non-containing pairs),
  `hcp_of_fixed` derives the rule-rule critical pairs from it
  (`ruleRuleCP_of_fixed`), and the bundles take `hcp_ax : AxiomCP`, the
  pairs involving a law instance, in place of `hcp`; `CompleteHyps.ofLaws`
  and `CompleteAtoms.ofLaws` take the per-law conditions `LawSpec.Conds`
  instead, from which `axiomCP_of_laws` derives it for every law set
  `LawSpec` names. The atoms witness
  retires `{a, b, d}` as the engine does (`witness_I3`). `I0Active`
  constrains only the classes that hold an active node and `hcc` only the
  active nodes; the statement over every class of `Fin n` (`I0ActiveAll`,
  which no state with a leaf constant meets) is the corollary
  `completion_complete_at_convergence_of_all`. GUIDE Section 5.3.
- `Atoms.lean`, `AtomsEngine.lean`, `AtomsWitness.lean` (leaf constants): the engine identifies the one-element monomial `{x}` with the
  class `x` (`Normal::Single`, `degeneracy_pair`, the right-hand side
  `{find c}` of an atomic class) and the empty monomial with the unit's
  class. `State.withAtoms A u` is the completion view with these implicit
  nodes: `({x}, x)` for each atomic class `x ∈ A`, `(∅, u)` for the unit.
  `RoundFixedA` is a fixed round of the view plus the one-element collapse
  `AtomCollapse` (a node whose normal form is an implicit node's monomial
  is in that node's class; `roundFixedA_iff`). From it and `hcc` on the
  stored active nodes, `RoundFixedA.materialized` proves that a stored node
  with an implicit node's monomial (a one-element node the engine keeps
  until the degeneracy merge) is in that node's class, and
  `RoundFixedA.congr` gives congruence on the view.
  `completion_complete_atoms` (packaged as `CompleteAtoms`, with
  `atom_class`: a node `=_E` a constant `{x}` is in `x`'s class, `atoms`,
  `unit_class`, `materialized`) and
  `completion_complete_{cancellative,inverse,combined,identityInverse}_engine_atoms`
  are the completeness theorems for graphs with leaf constants;
  `invNodes_withAtoms` derives the one-element nodes the inverse rules R1-R5
  are stated on from atomic `g`-node classes; `CompleteAtoms.ofLaws` builds
  the bundle from the per-law conditions `LawSpec.Conds` on the view's rules
  in place of `hcp_ax`. `AtomsWitness.witness_complete`
  proves every hypothesis of `CompleteAtoms` (through `CompleteAtoms.ofLaws`
  at `LawSpec.plain`) for the converged state of
  `(union (+ a b) c)`, `t = a+b+d`, `u = c+d` (four leaf constants, a
  normal form `{c}` collapsed into `c`'s class), by hand and `decide`;
  `witness_not_all` shows `I0ActiveAll` fails on it. `A` is a parameter and
  the theorems hold for every `A` that meets their hypotheses.
- `AtomicOf.lean`: `atomicOf st` is the set the engine's
  `atomic` bit defines on the store of one operator, a child of a stored
  node (`add_use`) or a class with no `f`-node (`register_if_fresh`, a node
  of another operator); a class holding an `f`-node and another operator's
  node, never a child, is atomic in the engine and outside the model's
  store. `addNF` models `add` on a degenerate normal form (`{x}` to `x`'s
  class, `∅` to the unit's), `AddStep` the normalize step with it, and
  `atomCollapse_of_addFixed` derives `AtomCollapse` at a fixpoint of
  `AddStep`; `roundFixedA_of_addFixed` gives `RoundFixedA` from `RoundFixed`
  of the view and the fixpoint. `CompleteAtomic` is `CompleteAtoms` at
  `atomicOf st`; `saturation_modulo_complete_store_atomic` is the final
  theorem with it; `witness_atomicOf : atomicOf wst = wA` lets the witnesses
  discharge both. The fixtures `egraph/tests/egg/atomic_bit_*.egg` probe
  the bit's five transitions against the bounded oracle.
- `reachable_I5`, `fix_sufficient`, `shrinkNoRefresh_breaks_I5`: the
  min-monomial refresh keeps I5; the unrefreshed shrink is the repro state.
  `Infer.unretire` (a retired node no current rule reduces is active again)
  with `State.refreshRhs`: `unretire_I0`, `refreshRhs_I0`,
  `unretire_refresh_I5`, `unretire_refresh_reachable`; in `Slot.lean`
  `SlotState.unretire` is an `Op`, `unretire_I5`, and
  `unretireNoRefresh_breaks_I5` is the repro `ac_reactivate_min_monomial.egg`.
- `MinMonoKey.lean`: completion orders monomials by per-class order
  keys (`keyDegLex`; a merged class takes the lesser key, `key_merge`), not by
  representative id. `rename_key_le`, `survivor_key_le`: at a merge every
  node's keyed monomial stays or shrinks, so each recanonization is a no-op or
  an `Op.shrink` (`merge_recanon_op`) and `reachable_I5` covers the engine
  (`keyed_reachable_I5`). `keyDegLex_wf`, `keyDegLex_add_right`,
  `keyDegLex_total` (keys distinct, `key_merge_injOn`).
  `idOrder_grow_breaks_I5`: under the id order a node grows and I5 fails
  (`ac_minmono_grow_wa.egg`).
- `kapur_termination`, `run_stabilizes`, `confluent_modulo`, `newman`.
- `Lattice.lean`: `hcancel` (joinability cancels a common summand) is not an
  engine fact (`hcancel_not_derivable`); the engine closes a cancellative
  operator with `lattice_round`. `E_mem_lattice`, `E_of_mem_lattice`,
  `E_iff_mem_lattice` (under `CancelClosed`, from `cancelClosed_of_cancellative`
  or `cancelClosed_of_nil`), `combined_E_iff`, `stateLattice_eq_closure`
  (`nodeEqs`, `classEqs`), `engine_merge_E`, `lattice_merge_sound` (under
  `FlatSound`, a hypothesis), `latticeClosed_of_engineFixed`,
  `completion_complete_cancellative_engine`. Coset representatives are
  modelled as lattice membership only. Fixtures: `cancel_lattice.egg`,
  `cancel_crit_pair.egg`, `nilpotent_group_lattice.egg`,
  `cancel_lattice_lazy.egg`. GUIDE Section 5.7.
- `ARound.lean`: the A-only inter-reduction `a_round`. `rewrite_left_sound`,
  `rewrite_right_sound` (offset 0 of a left fold, the last offset of a right
  fold, every magma), `rewrite_both_sound` (any offset, every semigroup),
  `left_off_spine_unsound`, `right_off_spine_unsound` (a counter-model in ℤ
  with subtraction for every other offset), and `aRound_sound` (a spine-restricted merge
  preserves I2). `ARound/Choice.lean`: the least spelling is unique
  (`isLeastSpelling_unique`), every other spelling is oriented towards it
  (`rule_of_ne_least`), an oriented rewrite decreases in shortlex
  (`rewriteAt_shortlex`, `orientedRewrite_wf`), and the engine's
  first-occurrence choice is an allowed step that exists whenever an
  occurrence does (`firstRule_theq`, `firstRule_complete`). `ARound/Store.lean`:
  hash-consing, a rewrite to an existing node merges its class, preserves I2
  (`aRoundH_sound`), and merges from a finite node set terminate
  (`aRoundH_wf`, `aRoundH_chain_bound`). `ARound/Nested.lean`: spine
  splicing preserves the denotation (`splice_den_left/right/both`), off-spine
  splicing has counter-models. Not modelled: recanonicalization by rebuild
  (termination rests on a fixed alphabet), termination of `a_round`
  interleaved with AC rounds and congruence, the one-element collapse in
  `add`.
- `Countermodel.lean`: `not_E_of_separates`, `E_sound`. A valuation into a
  commutative monoid that satisfies the asserted pairs and the law
  instances, and is cancellative when the operator is, separates only pairs
  that are not `=_E`-equal. `semper-conform-cc-cert` (`Conform/CC/Cert.lean`)
  emits `check-neq` only on pairs such a model separates, so a failing
  `check-neq` there is an engine unsoundness.
- `Laws/`: concrete instances `identity`, `nilpotent`, `idempotent`,
  `inverse` (the engine's one-directional walk `invWalk`, proved normalizing
  by `invNormal_invWalk`), `combined`, `identityInverse` (identity, inverse)
  and `idempotentIdentity` (identity, idempotent), one for every tag set the
  engine accepts; `hlaw` and `hnf_ax` discharged;
  `completion_complete_{identity,nilpotent,idempotent,inverse,combined,identityInverse,idempotentIdentity}`
  with `hcp` reduced to rule-side conditions: `RuleRuleCP` (derived from the
  fixed round), and for `:inverse` `InvMatching`, `InvUnitFree`,
  `InverseAxiomCP`, `NilpotentInverseCP`, which the inverse rules R1 to R5
  establish (below; reproducers in `proofs/repro`).
- `Laws/InvRules*.lean`: the five rules R1-R5 the engine applies
  (injectivity and involution of the inverse, inverse against the unit,
  rule-inverse critical pairs, the nilpotent-inverse pairs) as inference
  steps; `inv_rules_sound` extends soundness; `RoundFixedInv`,
  `RoundFixedInvUnit`, `RoundFixedInvNil` discharge the four hypotheses
  (`invMatching_of_fixed`, `invUnitFree_of_fixed`,
  `inverseAxiomCP_of_fixed`, `nilpotentInverseCP_of_fixed`), giving
  `completion_complete_inverse_engine`, `completion_complete_combined_engine`
  and `completion_complete_identityInverse_engine`, which take `hcancel`, `hcc`, `hS`,
  the minimal-monomial hypotheses, I3 and conditions on left-hand sides
  (GUIDE Section 5.6).
- `Laws/AxiomCP.lean`: `LawSpec`, the law sets the model names (`plain`,
  `identity`, `nilpotent`, `idempotent`, `inverse`, `combined`,
  `identityInverse`, `idempotentIdentity`; `identityNilpotent` is
  `combined` with the empty inverse), one case for every tag set the engine
  accepts, with `LawSpec.laws` and the per-law conditions `LawSpec.Conds`
  (`IdentityConds`, `NilpotentConds`, `IdempotentConds`, `InverseConds`,
  `CombinedConds`, `IdentityInverseConds`, `IdempotentIdentityConds`);
  `LawSpec.hlaw`, `LawSpec.hnf_ax`, `LawSpec.hcp` and
  `axiomCP_of_laws` (a `RoundFixed` state whose rules meet the conditions
  satisfies `AxiomCP`, by case analysis on the law set);
  `LawSpec.conds_inverse_of_fixed`, `conds_identityInverse_of_fixed` and
  `conds_combined_of_fixed` (the inverse conditions from the fixpoints of
  R1 to R5). GUIDE Sections 5.6, 9.

- `Bridge/`: `represents st f A`, the matching graph of one AC operator read
  from a completion state; `ac_equal_same_class_graph` (at a converged
  state, theory-equal nodes share a class), `matches_closed_under_theory`
  and `classMatches_congr` (the match set of a class is determined by the
  class's theory-equivalence class), `engine_match_modulo_complete`/`_sound`
  (every match at a theory-equal present node is emitted with the root in
  the class), and `per_node_form_fails`, the formal counterexample to the
  per-node statement; `CompleteHyps.ofLaws`, the bundle from the per-law
  conditions for a law set `LawSpec` names.

## EMatch: e-matching (`SemperProofs/EMatch/`)

- Base (`Defs`, `Ref`, `Main`): `MatchN`/`MatchC` (maximum partition),
  reference compiler and interpreter, `ematch_sound`, `ematch_complete`,
  per-step decomposition lemmas. `join` binds node and class (`joinBind`).
- `Engine/`: atoms (`atoms_iff_match`), lowering under any bound set
  (`lower_sound_complete`), scheduler plan grammar (`Sched`, `PlanOK`,
  `plan_matches`, `engine_plan_sound/complete`), runtime scheduling
  (`runND_matches`, `runND_indep`; under the semi-naive index settings
  `runNDA_matches`; with the engine's choice function `chooseEngine`, the
  transcription of `choose_atom`, `runEngine_matches`, checked against the
  engine on the `conform-rounds` corpus by
  `atom_choice_agrees_with_the_model_on_the_rounds_corpus`), the static
  scheduler `scheduleEngine` (`Engine/Schedule.lean`, the transcription of
  `schedule_inner`; `scheduleEngine_schedA`: its plan is in the grammar
  whatever the prices, checked against the engine on the same corpus by
  `static_plan_agrees_with_the_model_on_the_rounds_corpus`), the rule's
  `Matcher` with `matcherOK_static`/`matcherOK_engine`/
  `matcherOK_static_engine` and `matchersOK_compiled`, `byOp_demotion`,
  semi-naive `variant_partition`/`variants_disjoint`/`variants_cover_new`,
  and the cursor matcher's decomposition frames (`Engine/Cursor.lean`:
  `findLoop_terminates`, `advance_terminates`, `preFix_diverges`,
  `drive_eq_enum`, `acFrame_eq_decomposeAC`, `aciFrame_eq_decomposeACI`,
  `decomposeAC_nodup`, `decomposeACI_nodup`; checked against the engine by
  `cursor_agrees_with_the_recursive_executor_on_the_rounds_corpus` and
  `cursor_frames_agree_with_the_lean_model_on_random_residuals`).
- `Engine/Rounds/`: the cross-round half of semi-naive matching. A
  `Round` is the transition between two frozen snapshots with the deferred
  unions, the added nodes, subsumption, the touched log and the
  merge-membership delta; `Round.WF` is what rebuild guarantees.
  `delta_complete`: for tracked matching, a binding that satisfies a rule's
  atoms after the round and not before binds some join atom to a new node;
  `semi_naive_round_complete` and `semi_naive_complete` over a chain of
  rounds compose it with the within-round partition. Counter-models
  `delta_incomplete_global` (an equality with a global; such rules are
  routed to naive matching) and
  `delta_incomplete_untracked` (why the merge-membership delta exists).
  Not modelled: `:flatten` and sequence rules across rounds, action
  application, the transport of bindings through later merges.
- `Engine/Rounds/SeqSplice.lean`: the key `add` stores for a sequence
  node whose same-operator child is spliced (`flatten_seq_children`; the AC
  and ACI twins splice the same way). `normalizeSeq` (spliced elements
  `find`'d) is canonical, so `add` and recanonicalization agree
  (`recanon_normalizeSeq`); `addSeq_preserves` keeps canonical keys and one
  id per key, and `dedup_of_inv` derives `Round.WF.dedup` from them.
  Counter-model `raw_breaks_dedup`: a build that keeps the
  stored (stale) children of the spliced node, leaves two nodes of equal
  content in two classes (`seq_hashcons_miss_min.egg`, `r1_0581`).
- `Engine/Saturate/`: the saturation loop. Actions (`insert`, `union`,
  `subsume` as apply.rs runs them), `Den` (a right-hand-side term built in
  the graph), `Fired`, the transport of a binding through a round's merges
  (`fired_transport`; `matches_transport` needs `NoCollapse`, the
  maximum-partition fact that a two-item AC pattern stops matching when its
  two children classes merge, realized by the probe `ac_collapse.egg`),
  rounds with actions (`ActRound`, `fired_after_actions`), the invariant
  with one round of latency (`InvLag`, `inv_step`, `invLag_chain`) and the
  fixpoint theorem `saturation_complete`: at a state where a round changed
  nothing, every match of every rule is fired, for tracked semi-naive and
  naive routing. Not modelled: `:subsume` runs, literals, globals,
  primitives, comprehensions, `--flatten-rhs`, sequence rules; n-ary
  right-hand sides are stored literally, their normal forms are the
  bridge's side.
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
  `EngineRule.lean`/`EngineComplete.lean`: the engine's one
  `Demand::accepts` (`acceptsE`: the opened-class clause for multisets
  only) is `acceptsLaws` on multisets (`acceptsE_ac_iff`) and implies it on
  every kind; the engine's flag computed as the code does
  (`nonInertEng`, residue loop and the three inverse loops) equals
  `nonInertB` on every leaf block (`nonInertEng_eq`); the walk's pruning
  with `may_be_non_inert` is match-preserving (`prune_engine`);
  completeness of the engine's rule under any laws,
  `demand_engine_complete_{ac,aci,assoc}` (sets under the collapse
  invariant `MembersTwoClassesL` and `NodeTwoClassesL`, from which
  `twoClassesL_of_members` derives `TwoClassesL`; `aci1.egg` records the
  engine merging a set node reduced to one class into that class).
  `PlanDefs.lean`/`Plan.lean`: the flattened plan with one view register
  per n-ary atom (`planF`, `runE`, any atom order, joins without
  `by_contains`, pruned enumeration), `lowerF_sound`/`lowerF_complete`,
  `flatten_plan_sound`/`flatten_plan_complete` for `AtomSatF` (each n-ary
  atom on a view of its own node accepted by its own demand).
  `Fold.lean`/`FoldPlan.lean`: folds open only their spine
  (`fold_open_off_spine_unsound`, the counter-model to opening off the
  spine; `otLeft_sound`/`otRight_sound`); `runED` with the
  spine-restricted enumerator, equal to `runE` without folds (`runED_both`).
  The plan theorems hold for any enumeration meeting `Enumerator.Spec`
  (every view a normalization result, pruning keeping the accepted matches):
  `flatten_plan_sound_of_spec`/`flatten_plan_complete_of_spec`, with
  `Enumerator.base_spec` for the walk alone.
  `RegroupDefs.lean`/`Regroup*.lean`: regrouped views as
  `flatten.rs` builds them. `fitsR` is `fits` (sub-multiset, subset, run,
  prefix of a left fold, suffix of a right fold; at least two entries, not
  the whole view, not a node over its own class), `regroupRec` adds the
  group's class `g` to a leaf holding a class of the group and records `g`
  as needed, at most one needed class per item, `regroupLevels` iterates it,
  `takeableR` is the takeable closure through `f`-members, and
  `Enumerator.regroup` / `runER` is `Step::Flatten` with regrouping. A needed
  class is the leaf `needLeaf g`, so `DemandL` and the demand rules are
  unchanged (`needLeaf_okE`, `needLeaf_okL`). `prune_regroup` (from
  `takeableR_down`, `keepRec_of_accept`), `regroup_spec`,
  `regroup_plan_sound`/`regroup_plan_complete` (any fold direction, any
  laws). Soundness: `regroup_step_sound_{ac,aci,assoc}` and
  `regroup_views_sound_{ac,aci,assoc}` (laws-free operators, a consistent
  denotation into a commutative monoid, a join semilattice, a monoid),
  `regroup_step_sound_left/right`, `regroup_off_spine_unsound`.
  Completeness, laws-free, every kind and fold direction
  (`RegroupChain.lean`): `RegroupsTo` states one regrouping of a view
  declaratively (a sub-multiset for AC, a subset for ACI, a run on the
  spine for `:assoc`, a prefix of a left fold, a suffix of a right fold:
  `regroupsTo_left_iff`, `regroupsTo_right_iff`; at least two entries, not
  the whole view), `RegroupStep` one regrouping of a record by an
  `f`-member (leaves through `addG`, needed classes through `needsAfter`),
  `RegroupChain` any finite chain of steps, with no bound on the needed
  classes along it, so nested groups (`G2 ∋ f{G1, c}`, `G1` itself a
  regrouping) and groups covering the view together are chains. The
  enumeration keeps the records needing at most one class per item
  (`withinLimit`, `mem_withinLimit`) after regrouping, as the engine does.
  `regroupStep_mem`, `regroupChain_mem_levels` (a step is a regrouping of
  the model and shrinks the view, so a chain lies within the levels the
  model runs) and the converse `regroupStep_of_mem`,
  `regroupChain_of_mem_levels`; `regroup_view_complete` and
  `regroup_views_iff` (a view of `enumerateR` accepts `taken` iff a chain
  from a walk record reaches it, its last record needing at most `limit`
  classes, with its leaves and needed classes satisfied);
  `regroup_match_complete` and `regroup_match_iff` (an n-ary atom holds
  under `AtomSatG (Enumerator.regroup dir)` iff a chain reaches a view its
  shallow pattern matches, its last record needing at most as many classes
  as the atom has items). The limit bounds only the classes the last record
  needs: `regroup_nested_matches` (`RegroupNested.lean`) is a chain to
  `{h, k, G3}`, `G3 ∋ F{G1, G2}`, that needs `G1` and `G2` midway and `G3`
  alone at the end, and with a limit of one the view `{h, k, G3}` is
  enumerated and accepts `x = G3`; the engine finds the same match
  (`flatten_regroup_nested_needs.egg`). `regroup_fold_nested`: the nested
  prefixes of a left fold (`(a - b) - c` in `((a - b) - c) - d`) are
  reached, needing one class at each step. The disjoint-group AC form
  (`regroup_chain_ac`, `regroup_view_complete_ac`,
  `regroup_match_complete_ac`) admits groups that cover the view together
  (their sum within the view, none the whole view); `regroup_chain_ac`
  bounds the needed classes by one per group instead of assuming a limit.
  One group fits, per step (`RegroupFits.lean`):
  `fitsR_ac_complete`, `fitsR_aci_complete`, `fitsR_assoc_complete`,
  `fitsR_left_complete`, `fitsR_right_complete`. Operators with laws are
  covered by `RegroupLaws.lean` (below), except a normal form reached only by
  insertion and an ACI group kept beside its class. The generators use `regroupLevelsCapped` (`regroupLevelsCapped_eq`)
  with a budget of 45,000 records per node; one committed `conform` sample
  (`c1_0052.egg`) is past it, and the engine stops regrouping a node of it at
  its own bounds too.
  The engine's skips (`RegroupSkipDefs.lean`, `RegroupSkip.lean`):
  `regroupAllSkip` is `FlattenScratch::regroup` step for step (views by entry,
  largest first and the latest entry among equal sizes, candidates by node
  id; a target with an unconditional record, the source's other records when
  it has one, and a derived record whose signature the target has, all
  skipped). `regroupRec_shrink`: regrouping shrinks a view under any laws, so
  `mem_regroupLevels_iff_reach` (the full levels are the reachable records)
  and a target is never a view already regrouped (`addTarget_spec`; the
  engine asserts it). `Cov` (same view, an equal leaf for each leaf, a
  subset of the needed classes) with `Cov.accepts`, `Cov.acceptsL`,
  `Cov.length`, `Cov.derive`, `cov_uncond`, `cov_of_same`; the loop
  invariant (`addTarget_spec`, `regroupView_spec`, `step_spec`,
  `run_finished`, `init_inv`) and `regroupSkipG_spec`: every record kept is
  reachable, every reachable record is covered by one kept. Hence
  `regroupSkipG_iff` / `regroupSkipG_iffL` (same accepted matches per view
  after the item limit, any laws, kind, direction, candidate order; the
  candidate list need only hold the members with a fit, `CandSup`, and
  `regroupAllSkipAt_eq` equates the loop with the engine's per-view
  candidates from the use lists, `groupsOfEngineAt`, to the loop over every
  filed `f`-member, since a member holding no class of the view has no fit,
  `fitsR_nil_of_not_cand`),
  `enumerateRSkip_iff`, `enumerateRDSkip_iff`, `regroupSkip_spec`,
  `atomSat_regroupSkip_iff`, and the final theorems for
  `Enumerator.regroupSkip`: `regroupSkip_plan_sound`,
  `regroupSkip_plan_complete`, `regroupSkip_plan_complete_full`,
  `regroupSkip_views_iff`, `regroupSkip_match_iff`,
  `regroupSkip_match_complete`. The generators stay on `regroupLevels`: on the
  engine's loop they emit the same `check-eq` sets in another order, which
  changes the sampled `check-neq` candidates.
  The engine's bounds (`RegroupBoundsDefs.lean`,
  `RegroupBounds.lean`): `BSt.run` is the loop with the engine's counters,
  incremented and checked where `flatten.rs` does: `views` (records added
  after the skips, checked against `MAX_REGROUP_VIEWS`, 2^14, before the
  record is stored), `work` (the use-list lengths of the popped view's
  distinct classes, then each candidate's children, checked against
  `MAX_REGROUP_WORK`, 2^20, so a view no record reaches still costs), the
  stored elements against `MAX_ELEMS` (`OVER_BOUND`: the node is skipped),
  and the fits whose normalization overflows the width or leaves a count
  past `u64::MAX`, which the engine counts in `flatten_overflowed`
  (`Ix.wide`). A run
  stops at once and keeps its records. `regroupBounded_halt_iff`: the run
  stops iff the run without bounds ends past a bound, wherever the bound is
  crossed (`regroupBounded_halt_ok`, `regroupBounded_truncated_iff` for
  which bound); `regroupBounded_exact`: a run that does not stop, without
  overflow, ends with `regroupSkipG`'s records; `regroupBounded_sub`,
  `regroupBounded_sub_skip`, `regroupBounded_reach`: a truncated run's
  records are records of the run without bounds, and reachable.
  `takeableRCap` is the takeable set with the engine's cap of 4,096 classes
  on the closure (`regroupSkipCap_spec`). `runB` runs a flattened plan with
  the bounded enumeration (`enumerateRDBounded`, which regroups when the
  decomposition has items or the laws can drop a class, `canDrop`) and sums
  `flatten_regroup_truncated`, `flatten_skipped` and `flatten_overflowed`
  over its `Flatten` evaluations: `regroupBounded_plan_sound` for any
  counters, and with the three zero `regroupBounded_query_exact` /
  `regroupBounded_match_exact`: exactly the bindings of
  `Enumerator.regroupSkip`, which `regroupSkip_match_iff` characterizes.
  With no item, a regrouped record within the limit needs no class, which
  only laws that drop a class allow (`mem_base_of_reach`); the engine
  regroups exactly then (`laws_drop` in `flatten.rs`), so `(f ..r)` finds
  such a view (`flatten_regroup_laws_no_item.egg`, `exNoItem`). Every regrouping the engine runs on
  the `conform` and `conform-flatten` samples has the counters of the
  model's run on a node of the case (an instrumented engine against an
  executable mirror of `BSt.run`, not committed); on `c1_0052.egg` both stop
  at `MAX_REGROUP_VIEWS` (16,385 records). The generators keep
  `regroupCap`: `BSt.run` reads its state through function updates and is too
  slow for them. Not modelled: the walk's own bounds and overflows, which
  skip or count the node before regrouping; a view size saturated past 2^64
  under a 128-bit width.
  Regrouped views under laws (`RegroupLaws.lean`). Soundness in models of the laws (`LawsModelAC`, `LawsModelACI`,
  `LawsModelA`: the unit denotes the identity, `k • x = 0` under `:nilpotent k`, a
  class and its inverse class sum to zero): `denAC_normalizeList`,
  `denACI_normalizeList`, `denA_normalizeList`,
  `regroup_step_sound_{ac,aci,assoc}_laws`, `regroup_views_sound_{ac,aci,assoc}_laws`,
  `regroupSkip_views_sound_{ac,aci,assoc}_laws`. The exact characterization for any
  laws: `RegroupsToL` (the laws-free `RegroupsTo` to a canonical view, then the normal
  form under the laws is a node), `RegroupStepL`, `RegroupChainL`;
  `fit_of_regroupsTo`, `regroupStepL_iff` (a step is exactly a regrouping of the
  model), `regroupStepL_free_iff`, `regroupChainL_iff`, `regroup_views_iff_laws`,
  `regroup_match_iff_laws`, `regroupSkip_views_iff_laws`,
  `regroupSkip_match_iff_laws`, `regroupSkip_match_complete_laws`,
  `regroupSkip_plan_complete_laws`. Classes the normalization drops (the unit, a clamp
  to zero, a cancelled inverse):
  `needsAfter` keeps only the needed classes the normalized view holds and `addG`
  flags a leaf that gains a dropped class, so `reach_needs_held` (every needed class
  of a reachable record is in its view) and `needs_taken_of_all`; `mayNonInert` keeps
  every leaf under an identity, `canDrop_of_gone`, `mayNonInert_of_canDrop` and the
  relaxed `LeafRel` keep `prune_regroup`;
  `regroup_drop_need_{unit,nilpotent,inverse,leaf}` are the four matches of
  `flatten_regroup_laws_drop_need.egg`. Beyond chains, a normal form reached only by
  inserting the unit stays lost (`regroup_insert_unit_lost`,
  `flatten_regroup_laws_insert.egg`); a set group kept beside its class, which the loop
  alone never forms (`regroup_idem_overlap_loop_lost`, sound by
  `regroup_idem_overlap_sound`, the two conjuncts of the former
  `regroup_idem_overlap_lost`), is formed by the overlap stage below.
  Overlap views under idempotence (`RegroupOverlapDefs.lean`,
  `RegroupOverlap.lean`, `RegroupOverlapBounds.lean`): after the regrouping loop, for an
  `:assoc-comm-idem` operator, the engine adds the views with the class of a group and as
  many of its members dropped as the pattern's item count fixes (`overlapDrops`,
  `overlapFits`, `dropSets`), in the three forms of the regrouping model (`overlapStage`,
  `regroupAllO`, `enumerateRO`, `Enumerator.regroupO`; `SkipSt.overlapAll`,
  `regroupSkipO`, `enumerateRSkipO`, `Enumerator.regroupSkipO`; `BSt.overlapAll`,
  `regroupBoundedO`, `enumerateRDBoundedO`, `runBO`). Soundness in join semilattices:
  `overlap_step_sound_aci`, `overlap_step_sound_aci_laws`, `regroupO_views_sound_aci_laws`,
  `regroupSkipO_views_sound_aci_laws`; without idempotence the stage is empty
  (`enumerateRO_eq_of_not_aci`, `enumerateRSkipO_eq_of_not_aci`). The engine's stage
  step for step: `overlapAll_spec`, `regroupSkipO_spec`, `regroupSkipO_iff`,
  `enumerateRSkipO_iff`, `regroupAllSkipOAt_eq`, `prune_regroupO` (through
  `recRel_overlap`), `regroupSkipO_specE`, `atomSat_regroupSkipO_iff`,
  `regroupSkipO_plan_sound/complete`. The characterization: `OverlapStepL`,
  `RegroupChainO` (a chain then at most one overlap step), `regroupO_views_iff_laws`,
  `regroupO_match_iff_laws`, `regroupSkipO_views_iff_laws`, `regroupSkipO_match_iff_laws`,
  `regroupSkipO_plan_complete_laws`, `regroupChainO_iff_of_not_aci`; the statements
  without the stage are unchanged. The counter-model turned witness:
  `regroup_idem_overlap_found` (`flatten_regroup_laws_idem.egg`, its last check now
  `check-eq`). The bounds: `regroupBoundedO_cases`, `regroupBoundedO_halt_iff`,
  `regroupBoundedO_exact`, `regroupBoundedO_sub`, `regroupBoundedO_reach`,
  `enumerateRDBoundedO_le/ge`, `runBO_fst`, `runBO_ge`, `regroupBoundedO_plan_sound`,
  `regroupBoundedO_plan_complete`, `regroupBoundedO_query_exact`,
  `regroupBoundedO_match_exact`; the stage counts each raw fit against the work bound
  (no fixture hits a bound inside the stage, GUIDE Section 9). Both
  generators run the stage (`runERO`, `overlapStage` in `Conform.regroupedRecs`); eight
  of the 400 committed samples carry overlap matches and are regenerated, and the engine agrees with
  all 400. Not formed: a view with two overlap groups, and a kept member in a rest
  variable.
  Folds (`FoldEnum.lean`, `FoldRegroup.lean`): the executable spine
  enumerator is the spine trees, `rawNodeD_left_iff`/`rawNodeD_right_iff`
  (`rawOptD` with a direction produces exactly the views of `OTLeft`/`OTRight`,
  under `SeqShaped`: every `f`-member a sequence node), `enumerateLD_left/right_iff`,
  `enumerateLD_left/right_sound` (`otLeft_sound`/`otRight_sound` on the executable
  mirror), `rawNodeD_sub_both`. Regrouped views of a laws-free fold denote the
  node's fold in the free magma: `reach_lfold_left`/`reach_rfold_right`,
  `regroup_views_sound_left/right`, `regroupSkip_views_sound_left/right`, and for
  the declarative chains `regroupsTo_left/right_sound`,
  `regroupStep_left/right_sound`, `regroupChain_left/right_sound`,
  `regroup_chain_left/right_sound`; the monoid soundness under an identity for
  every direction, `reach_den_assoc_dir`, `regroup_views_sound_assoc_laws_dir`,
  `regroupSkip_views_sound_assoc_laws_dir`; `baseRecsR_left/right_views_iff` read
  the walk records the chains of `regroup_match_iff_laws` start from, for a fold,
  as the normal forms of the spine views. The fold mirror (the oracle's `runER`
  with the case's directions against the engine, bindings compared as the distinct
  `Tag` nodes) agrees on the 400 committed samples and 400 more of seed 3, 230 of
  them with a fold; the comparison test is not committed (GUIDE Section 8).
- `Steps/`: globals, literals, `CheckNeq`, `CheckPred` with faults,
  `CopyBinding`/`BindGlobal`, `Collect` (sequence patterns: A and AC/ACI
  relations, filters, `:except`, dedup, the bound as a hypothesis);
  `step_sound`/`step_complete`, `collect_sound`/`collect_complete`,
  `xplan_wf_sound`, `core_lifts`.
- `Env/`: the engine's mutable `Match` with undo; `env_restore`,
  `env_refine` (set equality with the reference interpreter under `WF`),
  `comm_pair_duplicate`, `ac_nodup`, `RoundSnapshot`. `WF` tracks per-step
  binding kinds (a join makes its target a node variable, `joinKinds`;
  `KindOk`: node variables are bound), so a nested child variable may be
  bound as a class and refined by the nested atom's join, or bound as a node
  and read as a class. `planOK_envWF`: every `PlanOK` plan is `WF` from
  `Match::new` under the resolver's variable discipline (`EnvAtomsWF`);
  `exec_matches`: the executor emits exactly the matches;
  `nested_plans_wf`, `nested_exec_matches`: the plans of `(f (g x) y)` both
  ways round.

## Fidelity (`SemperProofs/Fidelity/`)

- `Index.lean`: the index is a filter on the store by the skip predicates
  of `index.rs:521-537` (subsumed, shielded, unmatchable class);
  `matches_index_iff`, `mem_runNaive_index_iff`.
- `Subsume.lean`: saturation with `:subsume` runs, consequences read on the
  store: `saturation_complete_store` (no `subsumed = ∅`).
- `ByOpPolicy.lean`: `OpFilterPolicy`/`demote_by_op` as a parameter;
  `policy_candidates_eq` (same candidates for every policy).
- `Normalize.lean`, `NormalizeSat.lean`: right-hand sides present as the
  normal forms `add` builds (`DenN`: splice, unit drop, nilpotent clamp,
  inverse cancellation, degenerate arity); `DenN.persist` (under literal
  persistence), `fired_after_actions_N`, `saturation_complete_N` (store,
  `:subsume`, normal forms); `den_misses_single`, the literal `Den` has no
  value for a one-element AC right-hand side.
- `Recanon.lean`: recanonicalization as the laws apply it.
  `StorePersistN`: the fixed-arity nodes persist literally (`LiteralFixed`:
  tuple and pair; the sequence nodes are not covered, `RecanonComplete.lean`
  adds them as `LiteralSeq`), an AC or ACI node persists as the normal form of its mapped children under
  the recanonicalization steps (`RStep`, `RSetStep`) or collapses to a leaf.
  `DenN.persist_fixed` carries right-hand sides without n-ary application;
  `denN_persist_fails` shows `DenN.persist` does not extend to n-ary ones,
  so the round chains (`AChain`, `SChain`, `SChainN`) route the rules that
  build them naive after a round whose rebuild is not literal (`route`), as
  the engine's `respelled` re-match does when it counts a law applied at
  recanonicalization in `spelling_epoch`. The invariants are guarded
  accordingly (`InvLagL`, `InvLagS`, `InvLagN`); the fixpoint theorems keep
  their statements.
- `RecanonComplete.lean`: the completion-on case, where the
  engine does not re-match. `EqAC`, `EqACI`, `EqA`: the theory of an n-ary
  operator modulo the store, the equivalence the normalization steps
  generate. `DenE`: a right-hand side present modulo the theory;
  `DenE.persist` carries it across any rebuild meeting `StorePersistE`
  (`StorePersistN` with the sequence nodes literal) with no routing
  (`ACStep.mapE`: a splice through a recanonicalized node is a splice
  through its normal form). `SChainE`, `saturation_complete_E`: the chain
  with any routing per round and its fixpoint theorem (`InvE`).
  `TheoryClosed`: the store is closed under the theory, the store reading of
  `ac_equal_same_class`; `denE_denN_eq`, `saturation_complete_closed`: under
  it every value `add` builds for a right-hand side is in the match root's
  class, so a re-match would merge nothing. `PersistFails.sa_not_closed`:
  the counter-model's after-store is not closed; `PersistFails.completed`:
  its completion is, meets `StorePersistE`, and reaches the instance.
  Fixture `egraph/tests/egg/semi_recanon_completion_on.egg`. `ClosedAC`,
  `ClosedACI`, `ClosedA`, `PairsSorted`, `TheoryClosedRest`,
  `TheoryClosed.ofParts`: the split of `TheoryClosed` into the closure under
  one AC operator and its remainder, which `Final/Closed.lean` derives from
  the completion state; `closedAC_of_absent`, `closedACI_of_absent`,
  `closedA_of_absent` for an operator with no stored node of the kind and no
  law.
- `Sound.lean`: `denN_sound`, `firedN_sound`, `union_recorded_sound`: what
  the actions build denotes the right-hand side in every model of the graph
  and the operator laws. The round-level converse of `Saturate.Inv` (with
  the rebuild's merges) is open.
- `StopTest.lean`: the action phase as mints, merges,
  subsumes and hits with the node and class counts (`Phase.nodeCount`,
  `Phase.classCount`); the engine's stop test (no reported change, the size
  stamp `(node count, class count)` unmoved) implies `Unchanged`:
  `engine_stop_unchanged` (and `_N`, `_round`); the converse
  `Phase.stamp_ne`; `saturation_complete_engine`,
  `saturation_complete_store_engine`, `saturation_complete_N_engine` take the
  engine's stop condition. A stop test of `changes == 0` alone (a union that
  minted nodes counting 0) is not `Unchanged`: `Phase.stamp_ne`; the engine's
  test adds `EGraph::size_stamp`. The rebuild is modelled (`CompletionRun` over a step function of the store,
  `CompletionOutcome` as the engine reports it) and `rebuild_idle` is a
  theorem: a round matches on a completion fixpoint (`before_fixed`, from a
  converged previous rebuild), so a rebuild after an idle action phase goes
  nowhere. A rebuild after an aborted one is not idle in general.
- The completion settings, which do not re-match after a spelling change,
  join the instances the routing re-fires with completion off:
  `saturation_complete_closed` (`RecanonComplete.lean`), under the store's
  closure under the theory (`TheoryClosed`), derived from the completion
  state in `Final/Closed.lean` up to the remainder `TheoryClosedRest`
  (`saturation_complete_closed_of_complete`); GUIDE Section 6.5.

## Not modelled

View bounds `MAX_VIEWS`/`MAX_WORK`/`MAX_ELEMS` and multiplicity widths
(hypotheses only); the galloping cursor (Verus, containers-verus); faults inside
sequence sub-queries; `Nodup` of emitted lists (membership only); the
build-time spelling of a right-hand side's AC term (`flatten_mset_children`
reads each argument class's `atomic` bit and minimal monomial):
`saturation_complete` is about matches, not about the nodes a right-hand
side builds. Without completion a change to either input changes no node, so no
delta records it; the engine counts such changes (`spelling_epoch`) and the
next semi-naive round matches the rules that build an AC term in full, as
naive does (`semi_naive_atomic_semi.egg`, `semi_naive_minmono.egg`). The full
list of what is outside the model is GUIDE Section 9.
