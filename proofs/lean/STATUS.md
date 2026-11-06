# Status of the Lean development

Lean 4 with Mathlib v4.35.0. `lake build` of the whole project passes;
`grep -rn sorry SemperProofs/` is empty; every `#print axioms` in the
`Check.lean` files prints only `propext`, `Classical.choice`, `Quot.sound`.
Written 2026-11-04 after the second extension; regrouped views added 2026-11-05.

## Final theorem (`SemperProofs/Final/Main.lean`)

`saturation_modulo_complete`: for a chain of saturation rounds (rebuild's
round facts, merge tracking on, no `:subsume`, well-formed rules and plans,
every variant or naive match emitted per round) whose last state is the
represented graph of a completion state satisfying the convergence
hypotheses, at a round that changed nothing, for every rule with head `f`
and every pair of theory-equal active nodes, every match at one node is
fired and its root binds the class of the other. `saturation_modulo_sound`
is the matching-side converse. The two known limits are in the docstring:
a theory-equal term that is absent is matched through its class only
(`per_node_form_fails`), and maximum partition drops a two-item match when
its two children classes merge (`NoCollapse`).

## CC: AC-congruence closure (`SemperProofs/CC/`)

- `completion_sound`: invariant I2 (nodes of one class are `=_E`-equal) is
  preserved by every inference step.
- `completion_complete_at_convergence`: at a fixed round, `=_E`-equal active
  nodes are in one class. Hypotheses: slot maintenance with the refresh
  (`SlotState.OpsStar`, `I5` initially, `Agrees`), `I0Active`, `hcanon`,
  `RoundFixed`, law facts `hlaw`/`hnf_ax`/`hcp`, `hcc`, `hS`, `hcancel`.
- `reachable_I5`, `fix_sufficient`, `shrinkNoRefresh_breaks_I5`: the
  min-monomial refresh keeps I5; the unrefreshed shrink is the repro state.
- `MinMonoKey.lean` (row EG1): completion orders monomials by per-class order
  keys (`keyDegLex`; a merged class takes the lesser key, `key_merge`), not by
  representative id. `rename_key_le`, `survivor_key_le`: at a merge every
  node's keyed monomial stays or shrinks, so each recanonization is a no-op or
  an `Op.shrink` (`merge_recanon_op`) and `reachable_I5` covers the engine
  (`keyed_reachable_I5`). `keyDegLex_wf`, `keyDegLex_add_right`,
  `keyDegLex_total` (keys distinct, `key_merge_injOn`).
  `idOrder_grow_breaks_I5`: under the id order a node grows and I5 fails
  (`grow_wa.egg`).
- `kapur_termination`, `run_stabilizes`, `confluent_modulo`, `newman`.
- `hcancel` (joinability cancels a common summand) is a hypothesis, and the
  engine's Kapur §5 inferences (cancel-close each rule, superpose disjoint
  pairs) do not establish it: `cancel_lattice.egg` converged without
  `C5 = c1c3²`, which needs `c1c4² = c0²` plus two copies of `c4 = c0c3`.
  The engine now runs `lattice_round` at the completion fixpoint: classes
  whose vectors differ by a member of the lattice the equations span are
  merged. `Lattice.lean` formalizes the argument: `E_mem_lattice` (theory
  equality implies lattice membership, every law set), `E_of_mem_lattice`
  (the converse when `CancelClosed`, from `cancelClosed_of_cancellative` or
  `cancelClosed_of_nil`), `combined_E_iff` (identity, nilpotent and inverse
  laws: exactly the rows `lattice_round` builds), `latticeClosed_of_engineFixed`
  (the step's fixpoint gives `LatticeClosed`), `lattice_merge_sound` (a lattice
  merge preserves I2), and `completion_complete_cancellative_engine`
  (`completion_complete_at_convergence` with `hcancel` replaced by
  `LatticeClosed`). `hcancel` itself does not follow from lattice closure:
  `hcancel_not_derivable` is a converged, lattice-closed state where two
  joinable sums cancel to distinct normal forms, because `hcancel`
  quantifies over every monomial and lattice closure over the nodes present.
  The merges the engine performs are covered: `stateLattice_eq_closure`
  shows the model lattice is the span of the engine rows (`nodeEqs`, the
  class equals its node's monomial, and `classEqs`, classmates), and
  `engine_merge_E` / `lattice_merge_sound` show each merge is a theory
  consequence and preserves I2 under `FlatSound` (every node and classmate
  equation holds in `E L S`; a hypothesis, not derived from the engine
  steps). Coset representatives are modelled as lattice membership only.
  Fixtures:
  `cancel_lattice.egg`, `cancel_crit_pair.egg`, `nilpotent_group_lattice.egg`,
  `cancel_lattice_lazy.egg`.
- `ARound.lean`: the A-only inter-reduction `a_round`. `rewrite_left_sound`,
  `rewrite_right_sound` (offset 0 of a left fold, the last offset of a right
  fold, every magma), `rewrite_both_sound` (any offset, every semigroup),
  `left_off_spine_unsound`, `right_off_spine_unsound` (a counter-model in ℤ
  with subtraction for every other offset, so the step before commit
  `7beed39f` is unsound), and `aRound_sound` (a spine-restricted merge
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

- `Bridge/`: `represents st f A`, the matching graph of one AC operator read
  from a completion state; `ac_equal_same_class_graph` (at a converged
  state, theory-equal nodes share a class), `matches_closed_under_theory`
  and `classMatches_congr` (the match set of a class is determined by the
  class's theory-equivalence class), `engine_match_modulo_complete`/`_sound`
  (every match at a theory-equal present node is emitted with the root in
  the class), and `per_node_form_fails`, the formal counterexample to the
  per-node statement.

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
- `Engine/Rounds/SeqSplice.lean`: the key `add` stores for a sequence
  node whose same-operator child is spliced (`flatten_seq_children`; the AC
  and ACI twins splice the same way). `normalizeSeq` (spliced elements
  `find`'d) is canonical, so `add` and recanonicalization agree
  (`recanon_normalizeSeq`); `addSeq_preserves` keeps canonical keys and one
  id per key, and `dedup_of_inv` derives `Round.WF.dedup` from them.
  Counter-model `raw_breaks_dedup`: the unfixed build, which kept the
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
  `demand_engine_complete_{ac,aci,assoc}` (sets under `TwoClassesL`).
  `PlanDefs.lean`/`Plan.lean`: the flattened plan with one view register
  per n-ary atom (`planF`, `runE`, any atom order, joins without
  `by_contains`, pruned enumeration), `lowerF_sound`/`lowerF_complete`,
  `flatten_plan_sound`/`flatten_plan_complete` for `AtomSatF` (each n-ary
  atom on a view of its own node accepted by its own demand).
  `Fold.lean`/`FoldPlan.lean`: folds open only their spine
  (`fold_open_off_spine_unsound`, the counter-model of the engine bug
  fixed in `flatten.rs`; `otLeft_sound`/`otRight_sound`); `runED` with the
  spine-restricted enumerator, equal to `runE` without folds (`runED_both`).
  The plan theorems hold for any enumeration meeting `Enumerator.Spec`
  (every view a normalization result, pruning keeping the accepted matches):
  `flatten_plan_sound_of_spec`/`flatten_plan_complete_of_spec`, with
  `Enumerator.base_spec` for the walk alone.
  `RegroupDefs.lean`/`Regroup*.lean` (2026-11-05): regrouped views as
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
  `f`-member (leaves through `addG`, needed classes through `needsAfter`,
  at most `limit` of them), `RegroupChain` any finite chain of steps, so
  nested groups (`G2 ∋ f{G1, c}`, `G1` itself a regrouping) and groups
  covering the view together are chains. `regroupStep_mem`,
  `regroupChain_mem_levels` (a step is a regrouping of the model and
  shrinks the view, so a chain lies within the levels the model runs) and
  the converse `regroupStep_of_mem`, `regroupChain_of_mem_levels`;
  `regroup_view_complete` and `regroup_views_iff` (a view of `enumerateR`
  accepts `taken` iff a chain from a walk record reaches it with its leaves
  and needed classes satisfied); `regroup_match_complete` and
  `regroup_match_iff` (an n-ary atom holds under
  `AtomSatG (Enumerator.regroup dir)` iff a chain within the atom's
  per-item limit reaches a view its shallow pattern matches). The limit
  bounds the needed classes at every step of the chain, as the engine
  checks it: `regroup_nested_limit_counter` (`RegroupNested.lean`) is a
  chain to `{h, k, G3}`, `G3 ∋ F{G1, G2}`, that ends needing `G3` alone but
  needs `G1` and `G2` midway, and no view with a limit of one holds `G3`;
  the engine misses the same match (`flatten_regroup_nested_limit.egg`,
  expected `check-failed`). `regroup_fold_nested`: the nested prefixes of a
  left fold (`(a - b) - c` in `((a - b) - c) - d`) are reached within one
  needed class per step. The disjoint-group AC form (`regroup_chain_ac`,
  `regroup_view_complete_ac`, `regroup_match_complete_ac`) now admits
  groups that cover the view together (their sum within the view, none the
  whole view). One group fits, per step (`RegroupFits.lean`):
  `fitsR_ac_complete`, `fitsR_aci_complete`, `fitsR_assoc_complete`,
  `fitsR_left_complete`, `fitsR_right_complete`. Not covered: operators
  with laws (identity, nilpotence, inverses) in the completeness theorems;
  the engine's regrouping
  bounds (`MAX_REGROUP_VIEWS`, 2^14 regrouped records added after the skips,
  and `MAX_REGROUP_WORK`, 2^20 use-list entries and member children
  examined, which also counts views no record reaches) and its skipping of
  records (a target view with an unconditional record, a source view with
  one, the per-target signature deduplication; acceptance-preserving,
  argued, not proved); soundness under laws. The generators use `regroupLevelsCapped` (`regroupLevelsCapped_eq`)
  with a budget of 45,000 records per node.
- `Steps/`: globals, literals, `CheckNeq`, `CheckPred` with faults,
  `CopyBinding`/`BindGlobal`, `Collect` (sequence patterns: A and AC/ACI
  relations, filters, `:except`, dedup, the bound as a hypothesis);
  `step_sound`/`step_complete`, `collect_sound`/`collect_complete`,
  `xplan_wf_sound`, `core_lifts`.
- `Env/`: the engine's mutable `Match` with undo; `env_restore`,
  `env_refine` (set equality with the reference interpreter under `WF`),
  `comm_pair_duplicate`, `ac_nodup`, `RoundSnapshot`.

## Fidelity: rows closed against the engine (`SemperProofs/Fidelity/`)

- `Index.lean`: the index is a filter on the store by the skip predicates
  of `index.rs:521-537` (subsumed, shielded, unmatchable class);
  `matches_index_iff`, `mem_runNaive_index_iff`.
- `Subsume.lean`: saturation with `:subsume` runs, consequences read on the
  store: `saturation_complete_store` (no `subsumed = ∅`).
- `ByOpPolicy.lean`: `OpFilterPolicy`/`demote_by_op` as a parameter;
  `policy_candidates_eq` (same candidates for every policy).
- `Normalize.lean`, `NormalizeSat.lean`: right-hand sides present as the
  normal forms `add` builds (`DenN`: splice, unit drop, nilpotent clamp,
  inverse cancellation, degenerate arity); `DenN.persist`,
  `fired_after_actions_N`, `saturation_complete_N` (store, `:subsume`, normal
  forms); `den_misses_single`, the literal `Den` has no value for a
  one-element AC right-hand side.
- `Sound.lean`: `denN_sound`, `firedN_sound`, `union_recorded_sound`: what
  the actions build denotes the right-hand side in every model of the graph
  and the operator laws. The round-level converse of `Saturate.Inv` (with
  the rebuild's merges) is open.
- `StopTest.lean` (rows SA11, SA30): the action phase as mints, merges,
  subsumes and hits with the node and class counts (`Phase.nodeCount`,
  `Phase.classCount`); the engine's stop test (no reported change, the size
  stamp `(node count, class count)` unmoved) implies `Unchanged`:
  `engine_stop_unchanged` (and `_N`, `_round`); the converse
  `Phase.stamp_ne`; `saturation_complete_engine`,
  `saturation_complete_store_engine`, `saturation_complete_N_engine` take the
  engine's stop condition. The engine stop test before the fix
  (`changes == 0` alone, a union that minted nodes counting 0) is not
  covered: fixed in the engine by `EGraph::size_stamp`.
- Known divergences, not modelled: none of the stop test (closed by
  `StopTest.lean` and the engine's size stamp) or of the minimal monomial
  under node growth (closed by `CC/MinMonoKey.lean` and the engine's order
  keys). `Round.Persist`/`StorePersist` assume recanonicalization
  is a literal map, which a unit drop or degenerate collapse on rebuild
  breaks.

## Not modelled

View bounds `MAX_VIEWS`/`MAX_WORK`/`MAX_ELEMS` and multiplicity widths
(hypotheses only); the galloping cursor (Verus, containers-verus); faults inside
sequence sub-queries; `Nodup` of emitted lists (membership only); the
build-time spelling of a right-hand side's AC term (`flatten_mset_children`
reads each argument class's `atomic` bit and minimal monomial):
`saturation_complete` is about matches, not about the nodes a right-hand
side builds. In plain mode a change to either input changes no node, so no
delta records it; the engine counts such changes (`spelling_epoch`) and the
next semi-naive round matches the rules that build an AC term in full, as
naive does (`semi_naive_atomic_semi.egg`, `semi_naive_minmono.egg`).
