# Status of the Lean development

Lean 4 with Mathlib v4.35.0. `lake build` of the whole project passes;
`grep -rn sorry SemperProofs/` is empty; every `#print axioms` in the
`Check.lean` files prints only `propext`, `Classical.choice`, `Quot.sound`.
Written 2026-11-04 after the second extension; regrouped views added 2026-11-05;
the engine's regrouping skips and leaf constants 2026-11-06; the final theorem
over the store with its non-vacuity witness, and the executor's binding kinds
for nested patterns, 2026-11-06 (branch `feat/real-rules`).

## Final theorem (`SemperProofs/Final/Store.lean`, `Final/Main.lean`)

`saturation_modulo_complete_store_atoms` (`Final/Store.lean`): for a chain of
store rounds with normalized right-hand sides (`SActRoundN`: round 0 naive,
then semi-naive rounds; rebuild's round facts, merge tracking on,
`StorePersist`, `:subsume` allowed, well-formed rules and plans, every
variant or naive match emitted per round), at a round that changed nothing,
and for a completion state with leaf constants satisfying `CompleteAtoms`
whose active `f`-nodes are stored in the index after the round under ids
`ι` (`SubRep A.Sa.index st f act ι`, `CC/Bridge/Sub.lean`; the index may hold
any other node: leaf constants, other operators, the nodes right-hand sides
build): for every rule whose query is one pattern with head `f`, every pair
of theory-equal active nodes `p`, `p'` and every match rooted at the node
of `p'`, the instance is fired in the store as normal forms (`FiredN`), its
root binds the class of `p`, it matches the pattern at that class, and it
matches at the represented node of `p'`. `saturation_modulo_complete_store`
is the form with `CompleteHyps`, `_store_engine` takes the engine's stop
test, `_store_cover` (with `FCover`) concludes for every match.

Non-vacuity: `Final/Witness.lean` proves every hypothesis of
`saturation_modulo_complete_store_atoms` for two concrete rounds of
`(rewrite (+ x y) (g x y))` (`g` a plain binary operator) over the
leaf-constant state of `AtomsWitness` (`(union (+ a b) c)`, `t = a+b+d`,
`u = c+d`), by hand and `decide`: `witness_saturation_modulo_complete` is
the theorem applied to that run, and `witness_fires_modulo` reads it at the
match rooted at `{c, d}` for the theory-equal node `{a, b, d}`. Both rounds
route the rule naive.

The former statements remain: `saturation_modulo_complete` and
`saturation_modulo_complete_atoms` (`Final/Main.lean`) take
`A.R.after = represents st f act` and literal right-hand sides (`Den`), so
they hold vacuously for any rule set with a match whose right-hand side
builds a node other than an active `f`-multiset node (another operator, a
leaf constant, a one-element `(f x)`): `saturation_complete` derives `Fired`
for it and the represented graph has no such node. Their docstrings state
this (limit 3). `saturation_modulo_complete_sub` restates the literal form
with `SubRep`, and `saturation_modulo_complete_within` is its corollary.
`saturation_modulo_sound` is the soundness of one matching run on the
represented graph, not a converse of completeness. The two other known
limits are in the docstrings: a theory-equal term that is absent is matched
through its class only (`per_node_form_fails`), and maximum partition drops
a two-item match when its two children classes merge (`NoCollapse`).

Still assumed: `SubRep`, `CompleteAtoms` (with `hcancel`, `hcp` and the
minimal-monomial hypotheses) and the round facts; no theorem relates the
completion state to the rounds or to the engine's rebuild.

## CC: AC-congruence closure (`SemperProofs/CC/`)

- `completion_sound`: invariant I2 (nodes of one class are `=_E`-equal) is
  preserved by every inference step.
- `completion_complete_at_convergence`: at a fixed round, `=_E`-equal active
  nodes are in one class. Hypotheses: minimal-monomial maintenance with the
  refresh (`SlotState.OpsStar`, `I5` initially, `Agrees`), `I0Active`,
  `hcanon`, `RoundFixed`, law facts `hlaw`/`hnf_ax`/`hcp`, `hcc`, `hS`,
  `hcancel`. Since 2026-11-06 `I0Active` constrains only the classes that
  hold an active node and `hcc` only the active nodes; the former statement
  (`I0ActiveAll`, every class of `Fin n`, which no state with a leaf constant
  meets) is the corollary `completion_complete_at_convergence_of_all`.
- `Atoms.lean`, `AtomsEngine.lean`, `AtomsWitness.lean` (leaf constants,
  2026-11-06): the engine identifies the one-element monomial `{x}` with the
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
  `completion_complete_{cancellative,inverse,combined}_engine_atoms` are the
  completeness theorems for graphs with leaf constants;
  `invNodes_withAtoms` derives the one-element nodes the inverse rules R1-R5
  are stated on from atomic `g`-node classes. `AtomsWitness.witness_complete`
  proves every hypothesis of `CompleteAtoms` for the converged state of
  `(union (+ a b) c)`, `t = a+b+d`, `u = c+d` (four leaf constants, a
  normal form `{c}` collapsed into `c`'s class), by hand and `decide`;
  `witness_not_all` shows `I0ActiveAll` fails on it. Not modelled: which
  classes are atomic (`A` is a parameter; the engine's `atomic` bit, set on
  use as a child and on holding a non-AC node, is not derived; the
  theorems hold for every `A` that meets their hypotheses).
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
  The engine's skips (2026-11-06, `RegroupSkipDefs.lean`, `RegroupSkip.lean`):
  `regroupAllSkip` is `FlattenScratch::regroup` step for step (views by entry,
  largest first and the latest entry among equal sizes, candidates by node
  id; a target already regrouped, a target with an unconditional record, the
  source's other records when it has one, and a derived record whose
  signature the target has, all skipped). `regroupRec_shrink`: regrouping
  shrinks a view under any laws, so `mem_regroupLevels_iff_reach` (the full
  levels are the reachable records) and the skip of a target already
  regrouped never fires. `Cov` (same view, an equal leaf for each leaf, a
  subset of the needed classes) with `Cov.accepts`, `Cov.acceptsL`,
  `Cov.length`, `Cov.derive`, `cov_uncond`, `cov_of_same`; the loop
  invariant (`addTarget_spec`, `regroupView_spec`, `step_spec`,
  `run_finished`, `init_inv`) and `regroupSkipG_spec`: every record kept is
  reachable, every reachable record is covered by one kept. Hence
  `regroupSkipG_iff` / `regroupSkipG_iffL` (same accepted matches per view
  after the item limit, any laws, kind, direction, candidate order),
  `enumerateRSkip_iff`, `enumerateRDSkip_iff`, `regroupSkip_spec`,
  `atomSat_regroupSkip_iff`, and the final theorems for
  `Enumerator.regroupSkip`: `regroupSkip_plan_sound`,
  `regroupSkip_plan_complete`, `regroupSkip_plan_complete_full`,
  `regroupSkip_views_iff`, `regroupSkip_match_iff`,
  `regroupSkip_match_complete`. The generators stay on `regroupLevels`: on the
  engine's loop they emit the same `check-eq` sets in another order, which
  changes the sampled `check-neq` candidates.
  The engine's bounds (2026-11-06, `RegroupBoundsDefs.lean`,
  `RegroupBounds.lean`): `BSt.run` is the loop with the engine's counters,
  incremented and checked where `flatten.rs` does: `views` (records added
  after the skips, checked against `MAX_REGROUP_VIEWS`, 2^14, before the
  record is stored), `work` (the use-list lengths of the popped view's
  distinct classes, then each candidate's children, checked against
  `MAX_REGROUP_WORK`, 2^20, so a view no record reaches still costs), the
  stored elements against `MAX_ELEMS` (`OVER_BOUND`: the node is skipped),
  and the fits whose normalization overflows the width (`Ix.wide`). A run
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
  Regrouped views under laws (2026-11-06, `RegroupLaws.lean`), which settles
  "operators with laws ... in the completeness theorems" and "soundness under laws" in
  the list above. Soundness in models of the laws (`LawsModelAC`, `LawsModelACI`,
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
  to zero, a cancelled inverse; fixed in the engine and the model the same day):
  `needsAfter` keeps only the needed classes the normalized view holds and `addG`
  flags a leaf that gains a dropped class, so `reach_needs_held` (every needed class
  of a reachable record is in its view) and `needs_taken_of_all`; `mayNonInert` keeps
  every leaf under an identity, `canDrop_of_gone`, `mayNonInert_of_canDrop` and the
  relaxed `LeafRel` keep `prune_regroup`;
  `regroup_drop_need_{unit,nilpotent,inverse,leaf}` are the four matches of
  `flatten_regroup_laws_drop_need.egg`. Beyond chains, two kinds of match stay lost: a
  normal form reached only by inserting the unit (`regroup_insert_unit_lost`,
  `flatten_regroup_laws_insert.egg`) and a set group kept beside its class
  (`regroup_idem_overlap_lost`, `flatten_regroup_laws_idem.egg`).
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
