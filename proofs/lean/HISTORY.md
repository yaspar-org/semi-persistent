# History of the Lean development

This file records how the Lean development in `proofs/lean` reached the state
[`GUIDE.md`](GUIDE.md) describes: the engine defects the proofs located, the findings of the
earlier editions of the guide with the commits that resolve them, and the claims the
development has withdrawn. Nothing here is current state; a reader who wants the current
theorems, their hypotheses and the remaining gaps reads the guide. Commit hashes are those of
the `yaspar-org/semi-persistent` repository. Conventions are the guide's: file paths are
relative to `proofs/lean/SemperProofs/` unless they start with `egraph/` or `proofs/`, and a
fixture without a path is in `egraph/tests/egg/`.

Section 1 is the timeline of the commits the findings cite. Section 2 is the list of findings
of the guide's second edition, numbered as that edition numbered them, each with its
resolution. Section 3 is the status of the first edition's findings against the sources of
the branch. Section 4 is the table of counterexample theorems and the engine defects they
record. Section 5 lists the claims that have been retracted; each is marked so that it is not
cited as current. Section 6 records the editions of the guide.

## 1. Timeline

Every commit the findings cite, by date. "Engine" marks a change to `egraph/`, "proofs" a
change to `proofs/lean/`.

| Date | Commit | Side | Change |
|---|---|---|---|
| 2026-11-03 | `bb961302` | engine | refresh the minimal monomial when recanonicalization shrinks a node |
| 2026-11-04 | `844bcba`, `d95883f5` | engine | keep a `:flatten` match whose untaken leaf opened a taken class |
| 2026-11-04 | `10c9065`, `96279a6f` | engine | keep a `:flatten` match whose untaken leaf is not inert under the laws |
| 2026-11-04 | `7beed39f` | engine | rewrite a fold's spelling in completion only where it is a subterm |
| 2026-11-04 | `f995e5d6` | engine | open a fold's nested child only on its spine |
| 2026-11-04 | `ab214e9c` | engine | order completion by per-class keys instead of representative ids |
| 2026-11-04 | `c98d7fc` | engine | assert the inverse-law consequences R1 to R5 at rebuild and generate rule-inverse critical pairs |
| 2026-11-04 | `e937653` | proofs | the saturation fixpoint theorem modulo the AC theory; the sixth engine gap (equality to a global) routed naive |
| 2026-11-05 | `00f9d46f` | engine | PR #153: the unsound and incomplete cases the Lean model located, with the proofs and the conformance tests |
| 2026-11-05 | `6c37120b` | engine | PR #155: the regrouping item limit on the final records, regrouped matching complete for chains of every kind |
| 2026-11-05 | `cdcb2186` | engine | close cancellative completion with the lattice step; log AC spelling changes for semi-naive |
| 2026-11-05 | `e06360e5` | engine | reactivate a collapsed node that a materialized normal form or a recanonicalization makes irreducible |
| 2026-11-05 | `e97b80e0` | engine | skip a completion partner whose left-hand side is disjoint instead of asserting it cannot be |
| 2026-11-05 | `4ee0cf45` | engine | one cumulative node budget per lazy decision and a work budget per completion round |
| 2026-11-06 | `a5cfa2d7` | proofs | the first edition of the guide, written against `6c37120b` |
| 2026-11-06 | `15b5fa2e` | proofs | the engine, bridge and saturation completeness theorems with leaf constants |
| 2026-11-06 | `7838c767` | proofs | `I0Active` weakened to the classes that hold an active node, congruence to active nodes |
| 2026-11-06 | `29666b9a`, `992d9205` | proofs | the engine's regrouping skips preserve the match set; the loop with an explicit fuel |
| 2026-11-06 | `212d3bc6` | engine | the regrouping skips' comment points at their proof |
| 2026-11-06 | `ed7d52ea` | proofs | regrouped views characterized under the operator's laws |
| 2026-11-06 | `f1e8be1a` | proofs | per-step binding kinds in the executor; every scheduled plan well formed |
| 2026-11-06 | `8932dc12` | proofs | the final theorem over the store with the represented graph as the `f`-part of the index; a run meeting every hypothesis |
| 2026-11-08 | `19452248` | proofs | the executable fold enumerator linked to the spine trees |
| 2026-11-08 | `0d0f051d` | proofs | soundness of regrouped views for fold chains |
| 2026-11-08 | `1be51963` | proofs | `hcancel` replaced by lattice closure in `CompleteHyps` and `CompleteAtoms` |
| 2026-11-08 | `2e40098d` | proofs | the rule-rule critical pairs derived from the fixed round |
| 2026-11-08 | `26ee4f9e` | proofs | the engine's choice function, the adaptive scheduler under the index settings, rule matchers |
| 2026-11-08 | `e48db120` | engine | `choose_atom` checked against `chooseEngine` on the rounds corpus |
| 2026-11-08 | `2da55f68` | engine | refresh the minimal monomial of a collapsed node that is active again |
| 2026-11-08 | `329b25bc` | proofs | persistence as the laws recanonicalize; n-ary builders routed naive after a non-literal rebuild |
| 2026-11-08 | `8a84644b` | engine | a law applied at recanonicalization counts as a spelling change |
| 2026-11-08 | `5d4fc78a` | proofs | `CompletionOutcome` modelled; `rebuild_idle` a theorem |
| 2026-11-08 | `54bea39b` | engine | a regrouping view size past `u64::MAX` counted in `flatten_overflowed` |
| 2026-11-08 | `636ea372` | proofs | the engine's per-view regrouping candidates give the model's records |
| 2026-11-08 | `798af6c9` | proofs | `TwoClassesL` derived from the collapse invariant, with `aci1.egg` |
| 2026-11-08 | `c4530325` | proofs | the atomic set derived from the atomic bit, the collapse from `add` |
| 2026-11-08 | `68814795` | engine | five fixtures probing the atomic bit transitions |
| 2026-11-08 | `e5ed0211`, `7e579f4f` | proofs | the final theorem at a retired root; its witness |
| 2026-11-08 | `fa6be660` | proofs | merge of `wip/sched-fidelity`: the engine's choice function in the scheduler model, matchers in place of plans |
| 2026-11-09 | `893fc3ac` | proofs | overlap views under idempotence: sound, characterized and bounded |
| 2026-11-09 | `b932241b` | engine | overlap views of a set view under idempotence |
| 2026-11-09 | `989409fc` | proofs | completion-on saturation: right-hand sides present modulo the theory |
| 2026-11-09 | `f9eae3b5` | engine | `semi_recanon_completion_on.egg` |
| 2026-11-09 | `4e267030` | engine | the cursor's AC and ACI search resumes from the advanced entry after a backtrack (Section 5) |
| 2026-11-09 | `70b0d77c` | engine | the cursor's `ac_advance` and `aci_advance` resume through `find_first` (item 22) |
| 2026-11-09 | `bf025ce8`, `4abacd2d`, `1eea5659` | proofs | the cursor's AC and ACI decomposition frames: termination by the index measure, the yields are `decomposeAC` and `decomposeACI` |
| 2026-11-09 | `b08afa5b` | engine | the cursor's single-shot sequence steps hold a frame, AC nodes read through `ac_children`, a bound element takes the first matching entry of its class (item 22) |
| 2026-11-09 | `85077252` | engine | `MatchIterator` mirrored against `run_query` on the rounds corpus and against the Lean frame on random residuals |
| 2026-11-09 | `e49dc09e` | proofs | `AxiomCP` derived from the fixed round and the per-law conditions for every law set `LawSpec` names (`axiomCP_of_laws`); `CompleteHyps.ofLaws` and `CompleteAtoms.ofLaws` take the conditions in place of `hcp_ax` (gap 3 of the guide reduced to the count-threshold conditions and the two tag sets without a model) |
| 2026-11-09 | `e2a6b9ce` | proofs | `Laws.identityInverse` and `Laws.idempotentIdentity`, the two accepted tag sets without an instance, with `hcp_identityInverse`, `hcp_idempotentIdentity`, their completeness theorems and `LawSpec` cases; `axiomCP_of_laws` covers every tag set the engine accepts (gap 3 reduced to the count-threshold conditions) |

## 2. The findings of the second edition and their resolutions

The second edition of the guide listed these findings, most serious first, each with a
proposed fix; the numbering is that edition's, and the guide's Section 9 refers to no item
number. Each item carries its resolution after the original text. Items 6 (the
minimal-monomial hypotheses), 15 (stale docstrings) and 21 (the overlap-truncation fixture)
have no resolving commit and appear in the guide's Section 9 as gaps; item 16 is resolved by
the rewrite of `STATUS.md` that accompanies the present-state guide.

1. Literal `Den` with `hG` makes both final theorems vacuous for any rule with a match whose
   right-hand side builds a node other than a stored active `f`-multiset node. Fix: state the
   final theorem over `DenN` and the store (`saturation_complete_N` with the bridge), and
   prove a witness with rounds, a state and one rewrite rule meeting every hypothesis.
   **Resolved** by commit `8932dc12`: `saturation_modulo_complete_store`,
   `saturation_modulo_complete_store_atoms` (and `_store_engine`, `_store_cover`) over
   `SActRoundN`, `DenN` and the index, with `witness_saturation_modulo_complete` and
   `witness_fires_modulo` (guide, Section 7.7). The old theorems are kept, with the restriction in
   their docstrings.
2. `hG` restricts the final theorems to a graph of active `f`-multiset nodes, with no leaf,
   retired or other-operator nodes. Fix: read the graph as the index filtered by
   `Fidelity/Index.lean`, with `represents` a subgraph of it, and prove the bridge for the
   subgraph. **Resolved** by commit `8932dc12`: `SubRep` and `FCover` (`CC/Bridge/Sub.lean`),
   `ac_equal_same_class_sub`, `matches_closed_under_theory_sub`; the store theorems take
   `SubRep A.Sa.index st f act ι`, and `saturation_modulo_complete_sub` restates the literal
   form with it.
3. *Resolved, commit `1be51963`.* `hcancel` stayed in `CompleteHyps` and `CompleteAtoms`, and
   the engine does not establish it. Fix applied: the bundles take `LatticeClosed` in place of
   `hcancel`.
4. `Env.WF` excludes every nested pattern, so `env_refine` does not cover the plans the
   scheduler emits. Fix: replace the `κ` partition by per-variable binding kinds that allow a
   variable to be both a child class and a joined node, and prove `PlanOK → Env.WF`.
   **Resolved** by commit `f1e8be1a`: `Env.WF κ B plan` with per-step kinds (`joinKinds`,
   `KindOk`), `env_refine` re-proved, `planOK_envWF` under `EnvAtomsWF`, `exec_matches`, and
   the worked plans of `(f (g x) y)` (`nested_plans_wf`, `nested_exec_matches`; Section 3.7).
5. *Resolved, commit `2e40098d`.* `hcp` was not derived from `RoundFixed`, and the engine
   skips containment pairs. Fix applied: `RoundFixed` states the engine's three checks
   (`nf_present`, `lhs_reduced`, `cp_joinable` over non-containing pairs);
   `RoundFixed.cp_joinable_all`, `ruleRuleCP_of_fixed` and `hcp_of_fixed` derive the rule-rule
   part of `hcp`; the bundles take `AxiomCP` (the pairs involving a law instance) in its
   place, and the law theorems drop `hRR`. Remainder: `AxiomCP` for an abstract law set, which
   `CC/Laws/` reduces per law to conditions on the stored left-hand sides.
6. The minimal-monomial hypotheses amount to assuming I5. Fix: replace `h5₀`, `hrun`, `ha`
   by `I5 st` in the statements, or link `OpsStar` to the inference run.
7. `AtomCollapse` and the atomic set `A` are assumed. Fix: derive `AtomCollapse` from a model
   of `add` returning `x`'s class, and `A` from a model of the `atomic` bit.
   **Resolved** by commit `c4530325`: `atomicOf st` (`CC/AtomicOf.lean`; a child of a stored
   node, or a class with no `f`-node) and `addNF`, `AddStep`, `AddFixed`,
   `atomCollapse_of_addFixed`, `roundFixedA_of_addFixed`; `CompleteAtomic`,
   `completion_complete_atomic`, `saturation_modulo_complete_store_atomic`; the witnesses
   `witness_atomicOf`, `witness_complete_atomic`, `witness_saturation_modulo_complete_atomic`.
   The five fixtures `egraph/tests/egg/atomic_bit_*.egg` (commit `68814795`) probe the bit's
   transitions against the bounded oracle; the engine passes them. What remains: `AddFixed`
   is a hypothesis on the normalize pass, and a class that holds an `f`-node and another
   operator's node without being a child is atomic in the engine and not in `atomicOf st`,
   because the model's store holds `f`-nodes only.
8. *Resolved, commit `798af6c9`.* `TwoClassesL` was assumed, and the cited `aci1.egg` was
   missing. Fix applied: `twoClassesL_of_members` derives it from the collapse invariant
   (`MembersTwoClassesL`, `NodeTwoClassesL`), which `demand_engine_complete_aci` takes in its
   place; `egraph/tests/egg/aci1.egg` is committed and cited from the docstring.
9. **Resolved** by `329b25bc` (persistence) and `5d4fc78a` (`CompletionOutcome`), with the
   engine change `8a84644b`. Remainder: `DenN.persist` under normal-form recanonicalization
   is false (`denN_persist_fails`), so the theorems rely on the routing hypothesis of the
   chains instead; the engine meets it with completion off (`respelled`), and with completion
   on, where it does not re-match, the instances are expected to be joined by completion,
   which is not proved. **Resolved** (completion on) by commit `989409fc`
   (`Fidelity/RecanonComplete.lean`) and the fixture `semi_recanon_completion_on.egg`
   (commit `f9eae3b5`): a right-hand side is read modulo the theory of its operator (`DenE`),
   which persists across any rebuild (`DenE.persist`, through `ACStep.mapE`: a splice through
   a recanonicalized node is a splice through its normal form); `saturation_complete_E`
   drops the routing, and `saturation_complete_closed` concludes, at a store closed under the
   theory (`TheoryClosed`, the store reading of `ac_equal_same_class`), that every value
   `add` builds for a right-hand side is in the match root's class (`denE_denN_eq`): a
   re-match would merge nothing. The counter-model's after-store is not closed
   (`PersistFails.sa_not_closed`); its completion is and reaches the instance
   (`PersistFails.completed`). The engine passes the fixture under both strategies; the
   `respelled` re-match stays off with completion on. Remainder: `TheoryClosed` is a
   hypothesis on the store, not derived from `CompleteHyps` through `SubRep`; the conclusion
   is `FiredE`, not `FiredN`, since the new spelling need not be stored as a node.
10. *Resolved, commit `2da55f68`.* The re-activation of collapsed nodes may break I5. Fix: add
    an un-retire step to `Infer` and prove I5 is preserved, or change the engine to refresh
    after clearing the flag. Both applied. A debug check of I5 after every congruence
    rebuild of the completion loop (`check_min_monomial_invariant`, recomputing the least
    active monomial of every class and operator) found one case in the 400 committed
    conformance files, `conform-cc-cert/cs1_0129.egg`, reduced to
    `ac_reactivate_min_monomial.egg` (guide, Section 5.5). The engine now refreshes the class's
    minimal monomial when the flag is cleared, in `materialize` and in the recanonization
    path (where the refresh ran before the flag was cleared). Lean: `Infer.unretire` with the
    side condition that no current rule reduces the node, `State.refreshRhs`, `unretire_I0`,
    `refreshRhs_I0`, `unretire_refresh_I5`, `unretire_refresh_reachable` (`CC/Lemmas.lean`);
    `SlotState.unretire` as an `Op`, `unretire_I5`, and the repro
    `unretireNoRefresh_breaks_I5` (`CC/Slot.lean`).
11. *Resolved, commit `54bea39b`.* The engine's regrouping loop saturated view sizes at
    `u64::MAX` without counting it, where the skip of a regrouped target could fire. Fix
    applied: a count past `u64::MAX` is counted in `flatten_overflowed` (`saturated_size`,
    `flatten.rs`, with a unit test on the conversion), and a fit whose normalized view holds
    one is skipped as `Ix.wide` models; `regroupBounded_query_exact` covers the case with no
    new proof.
12. *Resolved, commit `636ea372`.* The engine's regrouping candidates were a subset of the
    model's. Fix applied: `fitsR_nil_of_not_cand` (a member with no class in the view has no
    fit, every kind), `hgs'` restated as `CandSup` (members with a fit), and
    `regroupAllSkipAt_eq` (the loop with the engine's per-view candidates `groupsOfEngineAt`
    ends with the model's records).
13. *Resolved, commits `ed7d52ea` (laws) and `0d0f051d` (folds).* Soundness of regrouping
    under laws and for fold chains, and completeness under laws, were unproved. Fix applied:
    `regroup_views_sound_{ac,aci,assoc}_laws` and `regroup_match_iff_laws`
    (`RegroupLaws.lean`), `regroup_views_sound_left/right`,
    `regroupSkip_views_sound_left/right`, `regroup_chain_left/right_sound` and
    `regroup_views_sound_assoc_laws_dir` (`FoldRegroup.lean`); `regroup_match_iff_laws`
    covers the fold kinds as stated, with `baseRecsR_left/right_views_iff` for its base.
    Remainder: the fold soundness is laws-free, as the engine's folds are (guide, Section 4.5).
14. *Resolved, commit `19452248`.* The executable fold enumerator was not linked to
    `OTLeft` and `OTRight`. Fix applied: `rawNodeD_left_iff`, `rawNodeD_right_iff`,
    `enumerateLD_left/right_iff`, `enumerateLD_left/right_sound` (`FoldEnum.lean`), under
    `SeqShaped`; the fold mirror agrees with the engine on 230 fold samples (guide, Section 4.5).
15. Stale docstrings: tracking in `Rounds/Round.lean:65-67` and `Rounds/Counter.lean:21-22`;
    `egraph.rs:3068` in `CC/Laws/CriticalPairs.lean:146-149` and `CC/Laws/Main.lean:96-101`;
    `changes == 0` in `Final/Main.lean:131-132`; AC only in `Flatten/RegroupFits.lean:17-19`;
    `completion_complete_atom_class` in `CC/Atoms.lean:53`; `regroupSkip_iff` in
    `Flatten/RegroupSkip.lean:10`; `grow_wa.egg` in `CC/MinMonoKey.lean` and `STATUS.md`;
    drifted Rust line numbers and the renamed or missing files of Section 3 below. Fix: one pass
    over the docstrings replacing line numbers by function names.
16. `STATUS.md` calls the `_engine` theorems engine-level and `saturation_modulo_sound` the
    converse of completeness, and does not state the vacuity of item 1. Fix: state the
    remaining hypotheses and the restriction to right-hand sides the graph holds.
17. *Resolved, with item 5.* The runtime design note claimed the skips have no check and
    the confirmation round checks `hcp`. Fix applied: the note states that the skips need no
    check (`regroupSkipG_iff`), that the confirmation round checks the rule-rule part through
    `lhs_reduced` and `cp_joinable`, and that `AxiomCP` is the part left to the per-law
    conditions.
18. *Resolved by commits `e5ed0211` and `7e579f4f`.* `FCover` requires every `f`-node of
    the index to be an active node of the completion state, and the engine keeps a
    collapsed node (`FLAG_AC_COLLAPSED`) in the index and matchable. So
    `saturation_modulo_complete_store_cover` applies to no run in which completion
    collapsed a node (`Final/Witness.lean`, `not_cover`, kept as the record of the limit).
    Fix applied: `SubRepR` (`CC/Bridge/Sub.lean`) extends `SubRep` to the retired nodes, and
    `saturation_modulo_complete_store_retired` (`Final/Store.lean`) concludes, for a match
    rooted at a retired node, at the class of an active node it rewrites to
    (`node_reduces_active`: I3 and well-founded induction on `→_R`; `I2` makes the rewrite
    an `=_E`-equality). `witness_fires_retired` reads it at the match rooted at `{a, b, d}`
    on the witness run (guide, Section 7.7).
19. *Resolved, commit `4e267030`.* The cursor matcher (`MatchIterator`, `run_query_iter`,
    reached by no production path; `run_query` executes the plans) did not terminate on an
    exact AC pattern with more elements than the node has entries: after a backtrack,
    `ac_find_first` and `aci_find_first` scanned every element but the first from entry 0,
    re-took the entry just undone and looped (`cursor_shapes.rs`,
    `exact_decompositions_backtrack_without_a_rest`). Fix applied: the search resumes from
    the advanced entry. `EMatch/Engine/Cursor.lean` (commits `bf025ce8`, `4abacd2d`) now
    models the decomposition frames: `findLoop_terminates` by the measure `pos` on the entry
    indices, and `preFix_diverges` for the search before the fix, which returns for no fuel
    on three elements over two entries.
20. *Resolved, commits `893fc3ac` (model) and `b932241b` (engine).* Regrouped
    matching under idempotence never kept a member of a set group beside its class, so with
    `sab = S{A, B}` and `s = S{A, B, C}` the pattern `(S x y z)` never bound
    `x = sab, y = A, z = C`, although `S{sab, A, C} = s` in every ACI model
    (`regroup_idem_overlap_lost`, `flatten_regroup_laws_idem.egg`). Fix applied: an overlap
    stage after the regrouping loop, for `:assoc-comm-idem` operators only, forms the views
    that add the class of a group and drop as many of its members as the pattern's item count
    fixes, counted against the regrouping budgets (`FlattenScratch::regroup`, `flatten.rs`);
    the model has it in all three forms (`RegroupOverlapDefs.lean`), with soundness
    (`overlap_step_sound_aci_laws`, `regroupSkipO_views_sound_aci_laws`), the
    characterization (`regroupSkipO_match_iff_laws`, `RegroupChainO`), the step-for-step
    theorems (`regroupSkipO_iff`, `regroupAllSkipOAt_eq`) and the bounds
    (`regroupBoundedO_query_exact`); `regroup_idem_overlap_lost` became
    `regroup_idem_overlap_sound`, `regroup_idem_overlap_loop_lost` and
    `regroup_idem_overlap_found` (guide, Section 4.6). Eight of the 400 conformance samples changed
    (`conform/c1_0081.egg`, `c1_0101.egg`, `c1_0152.egg`, `c1_0181.egg`,
    `conform-flatten/f2_0026.egg`, `f2_0112.egg`, `f2_0118.egg`, `f2_0135.egg`) and were
    regenerated; the engine agrees with all 400. Remainder: a view with two overlap groups,
    and a kept member in a rest variable, are not formed (guide, Section 10).
21. **New.** Truncation of overlap views is not exercised by a fixture. The bounds are
    constants (`MAX_REGROUP_VIEWS` 2^14, `MAX_REGROUP_WORK` 2^20), and a family of overlap
    views past them needs a set of about fifty children, on which the set decomposition of
    the pattern enumerates `48 · 47 · 46 · 45 · 44` partial assignments per node before the
    stage is reached (hours in a debug build; the fixture drafted for this round ran for
    seven hours in the matcher's `decompose_aci_elem` and was dropped). The bounds are now settable from a test
    (`FlattenBounds`, `MatchPool::set_flatten_bounds`, `flatten_bounds.rs`), which is the
    lever; the Lean bounds model takes them as values (`Bounds` in `RegroupBoundsDefs.lean`).
    Fix: a small test lowering them over a set node with overlap views, and assert the truncation counter and that only overlap views
    are reported, as `regroupBoundedO_plan_sound` states.

22. *Resolved, commits `70b0d77c` and `b08afa5b`.* Four more defects of the cursor matcher,
    found by the model of its decomposition frames and by the mirror of `run_query_iter`
    against `run_query` on the rounds corpus (`85077252`): `ac_advance` and `aci_advance`
    completed the elements after the moved one greedily, so an assignment with a bound later
    element was missed, and their retry path undid the moved element a second time at an
    index it never took, which read past the residual (`(F x y (c))` over `F{a, b, c}`); a
    sequence pattern with at most one rest bound its children with no frame, so the join
    below moved to its next node with the previous node's children still bound; an AC
    decomposition read its node through `mset_children`, which panics on a commutative pair;
    and a bound element took any entry of its class, so a commutative pair with equal children
    gave an assignment twice where `decompose_ac_elem` gives it once. Fixes applied: the
    advance resumes through `find_first` from the last element; a `Once` frame holds the
    single-shot bindings; `ac_children`; the first matching entry of the class. After them the
    corpus mirror agrees on every plan (1427 plans, 770 with a match) and
    `cursor_shapes.rs` holds the failing shapes.
## 3. The first edition's findings and their status

The first edition of the guide (commit `a5cfa2d7`, written against `6c37120b`) collected the
gaps between the model and the engine from its adequacy notes, in the order a reader trying
to strengthen the final theorem would meet them. The second edition (commit `fa6be660`)
rechecked each item against the sources of the branch; its statuses follow, one of three:
**still true**; **resolved**, with the commit
and the theorem that resolve it; or **changed**, with what changed. Items marked **new**
were located by the second edition.

**Hypotheses the engine does not discharge.**

1. **Still true.** `hG`: the final theorem is about an index that contains only active
   `f`-multiset nodes (guide, Section 7.5). `saturation_modulo_complete_atoms` keeps the same `hG`;
   its graph has no node for a leaf constant. *Resolved since, by commit `8932dc12`:*
   `saturation_modulo_complete_store_atoms` takes `SubRep` on the index (guide, Section 7.7).
2. **Still true, and it extends to the leaf-constant form.** Literal `Den` with `hG` makes
   `saturation_modulo_complete` hold vacuously for any rule with a match whose right-hand side
   builds a node other than an active `f`-multiset node, and
   `saturation_modulo_complete_atoms`, with the same `hG` and `Fired` (Final/Main.lean:183-200),
   adds the case of a right-hand side naming a leaf constant or a one-element `f`-term
   (guide, Section 7.5). Neither docstring nor `STATUS.md` states the restriction, and no theorem
   exhibits rounds, a state and rules satisfying all the hypotheses together. This is the
   most serious finding of the guide: the hypotheses are joint, so one such rule with a match
   makes the theorem vacuous for every rule of the set, and a rule set whose right-hand sides
   use a second operator or a constant is the common case. *Resolved since, by commit `8932dc12`:*
   `saturation_modulo_complete_store_atoms` reads right-hand sides as normal forms on the
   store, and `witness_saturation_modulo_complete` proves all its hypotheses on a run of
   `(rewrite (+ x y) (g x y))` (guide, Section 7.7).
3. **Resolved, by commit `1be51963`.** `CompleteHyps` and `CompleteAtoms` take
   `hlat : L.cancellative → LatticeClosed` in place of `hcancel`; `CompleteAtoms.same_class`
   and `ac_equal_same_class` go through `complete_of_latticeClosed` for a cancellative
   operator and through the rewriting argument, where `hcancel` is vacuous, otherwise. The
   final theorems are unchanged in statement. `hcancel` remains only in
   `completion_complete_at_convergence`, `completion_complete_atoms` and the inverse and
   combined `_engine` theorems, which the bundles no longer use for a cancellative operator.
4. **Resolved** by `2e40098d` (`RoundFixed` with `lhs_reduced`, `hcp_of_fixed`,
   `CC/Assemble.lean`). The first edition recorded that `hcp` was not derived from
   `RoundFixed`, and that the engine skips disjoint and containment pairs (`cc_round`) and
   states that the normalize pass handles containment. `RoundFixed` now states the
   reducibility pass as `lhs_reduced`, `hcp_of_fixed` derives the rule-rule part of `hcp`
   from it, and the bundles take `AxiomCP` for the pairs involving a law instance (guide, Section
   5.3). Remainder: `AxiomCP` for an abstract law set, reduced per law in `CC/Laws/`; in the
   leaf-constant form it ranges over the view's rules `M → {x}`.
5. **Still true.** The minimal-monomial hypotheses amount to assuming I5:
   `witness_complete` discharges them with `ss₀ = ss` and the reflexive run.
6. **Resolved** by `798af6c9` (`twoClassesL_of_members`, `EMatch/Flatten/EngineComplete.lean`).
   `TwoClassesL` is derived from the collapse invariant `MembersTwoClassesL` and
   `NodeTwoClassesL`, which `demand_engine_complete_aci` takes (guide, Section 4.3), and the
   fixture `egraph/tests/egg/aci1.egg` is committed.
7. **Resolved** by `329b25bc`. `Round.Persist` and `StorePersist` are no longer per-round
   hypotheses: `Round.PersistFixed`, `LiteralFixed` and `StorePersistN`
   (`Fidelity/Recanon.lean`) state what `recanonize_node` does, including the unit drop,
   the nilpotent clamp and the degenerate arity; inverse-pair cancellation
   (`canon_repair_round`) is a merge the round records. `denN_persist_fails` shows the
   weakened hypothesis does not transport n-ary right-hand sides, so the chains route the
   rules that build them naive after a non-literal rebuild, as the engine does since
   `8a84644b`.
8. **Resolved** by `5d4fc78a`. `EnginePhase.rebuild_idle` is a theorem of a model of the
   rebuild with `CompletionOutcome`; the round matches on a completion fixpoint
   (`before_fixed`), which a converged previous rebuild gives and an aborted one does not.
9. **Resolved** by `7838c767` (`I0Active`, `CC/Assemble.lean:94`;
   `completion_complete_at_convergence_of_all`, `CC/Main.lean:125`). The first edition
   recorded that `I0Active` quantified over every class id of `Fin n`. It now constrains only
   the classes that hold an active node, and `hcc` only the active nodes;
   `witness_not_all` shows the former hypothesis failed on a state with leaf constants.
10. **Resolved** by `c4530325` (`CC/AtomicOf.lean`, Section 5.9). `atomicOf st` is the set the
    `atomic` bit defines on the store of one operator, and `atomCollapse_of_addFixed`
    derives the collapse from a fixpoint of the normalize step with `add` modelled by
    `addNF`. The first edition recorded both as assumed.

**Model components not connected to each other.**

1. **Still true, and stronger than recorded.** The mutable executor (`Env/`) is not
   connected to the scheduler theorems. The first edition located the conflict in the re-join
   `byRepr a.node`; `Env.WF`'s partition of variables into node and class variables excludes
   every plan of a nested pattern, in either lowering order (guide, Section 3.7). *Resolved since,
   by commit `f1e8be1a`:* per-step binding kinds, `planOK_envWF` and `exec_matches`
   (guide, Section 3.7).
2. **Still true for `exec`.** `runND` models the adaptive scheduler, and `exec` models static
   plans only. *Since commit `26ee4f9e`:* the adaptive scheduler reaches the saturation
   theorems through `runNDA`, `chooseEngine` (`runEngine_matches`) and `Matcher`; the former
   `hplan : PlansOK rules` is `hmatch : MatchersOK rules`, a theorem for the adaptive
   scheduler (`matcherOK_engine`) and `SchedA` of the compiled plan for the static one
   (`matcherOK_static`), which no theorem proved `schedule_with_stats` emits. The choice
   function is checked against `choose_atom` by a conformance test (guide, Section 3.4). *Since
   `scheduleEngine_schedA` (`EMatch/Engine/Schedule.lean`):* the static scheduler is
   transcribed and its plan proved in the grammar, so `MatchersOK` is a theorem for the
   static path too (`matcherOK_static_engine`, `matchersOK_compiled`); the transcription is
   checked against `schedule_with_stats` by `static_plan_agrees_with_the_model_on_the_rounds_corpus`
   (guide, Section 3.4). What remains outside is the price, a parameter of the model, and the atoms
   the grammar does not have (item 3).
3. **Still true.** Guards, literals and globals have per-step theorems only (guide, Section 3.8).
4. **Resolved** by `19452248` (`rawNodeD_left_iff`, `rawNodeD_right_iff`,
   `EMatch/Flatten/FoldEnum.lean`). The executable fold enumerator is linked to `OTLeft` and
   `OTRight` under `SeqShaped` (guide, Section 4.5).
5. **Still true.** `Flatten/` feeds nothing above it: no module of `Saturate/`, `Bridge/`,
   `Final/` or `Fidelity/` imports it; `:flatten` and sequence rules across rounds are not
   modelled.
6. **Resolved for the store form** by `8932dc12` (`saturation_modulo_complete_store_atoms`,
   `Final/Store.lean`, Section 7.7), which composes `saturation_complete_N` with the bridge on
   a part of the index (`SubRep`), and `_store_engine`, which takes the stop test. The
   literal forms `saturation_modulo_complete` and `saturation_modulo_complete_atoms` still
   use `saturation_complete` and `represents`, as recorded.
7. **Still true.** `ARound/` uses its own state, not `State`; joint termination with AC rounds
   is not proved.
8. **Resolved** by `29666b9a` and `992d9205` (`regroupSkipG_iff`,
   `EMatch/Flatten/RegroupSkip.lean:1222`; `regroupSkip_match_iff`, `:1410`). The first
   edition recorded that the engine's regrouping skips were not modelled and were argued
   acceptance-preserving in comments only. `RegroupSkipDefs.lean` models the loop with its
   skips, and the match set equals that of the full enumeration for any laws (guide, Section 4.7).
   `212d3bc6` points the engine's comment at the proof.

**Engine behaviour not modelled.**

1. **Resolved** (Section 2, item 10). The engine re-activates collapsed nodes after a
   recanonicalization and when completion materializes their monomial again. `Infer.unretire`
   models the step, `refresh_min_monomial` runs after the flag is cleared in both places,
   and `unretire_refresh_I5` and `SlotState.unretire_I5` show the refresh keeps I5. The
   unrefreshed re-activation did break I5 (`ac_reactivate_min_monomial.egg`,
   `unretireNoRefresh_breaks_I5`).
2. **Still true.** The engine's `Comm` atom joins through `by_contains`, as AC does
   (`egraph/src/schedule.rs:749`). The model's `byContains` ignores pairs and adds a
   `decomposeComm` step with no Rust counterpart.
3. **Changed.** The walk's bounds `MAX_VIEWS`, `MAX_WORK` and `MAX_ELEMS` and the
   multiplicity widths appear as hypotheses or not at all. The regrouping bounds
   `MAX_REGROUP_VIEWS` and `MAX_REGROUP_WORK` are modelled (`RegroupBounds.lean`, Section
   4.7), and the regrouping skips are modelled (item 8 above). The saturated view size of the
   engine's loop is counted in `flatten_overflowed` since `54bea39b`, so
   `regroupBounded_query_exact` covers it.
4. **Still true.** Emitted lists are compared as sets; `Nodup` is not modelled beyond single
   steps.
5. **Still true.** The build-time spelling of an AC right-hand side (`flatten_mset_children`,
   which reads each argument class's `atomic` bit and minimal monomial) is outside
   `saturation_complete`. The engine covers it with `spelling_epoch`.
6. **Resolved** by `636ea372` (`regroupAllSkipAt_eq`, `groupsOfEngineAt_candSupAt`,
   `EMatch/Flatten/RegroupBounds.lean`; `CandSup`, `RegroupSkipDefs.lean`). The engine's
   regrouping candidates come from the use lists of the view's classes; the model's loop over
   every filed `f`-member ends with the same records, and `hgs'` asks only for the members
   with a fit (guide, Section 4.7).

**Stale statements in the sources.** These do not affect the proofs, but they mislead a
reader who checks the Rust.

1. **Changed.** `Rounds/Round.lean:65-67` and `Rounds/Counter.lean:21-22` still say tracking
   is off in `saturate_semi`; `saturate_rules_semi` turns it on for every entry point
   (`egraph/src/saturate.rs:946-950`). The first edition also listed
   `Saturate/Invariant.lean:27-28`; that docstring says tracking is required, which is
   accurate, and the citation was an error of the first edition.
2. **Still true.** `InverseAxiomCP` (`CC/Laws/CriticalPairs.lean:146-149`) and
   `completion_complete_inverse` (`CC/Laws/Main.lean:96-101`) say the engine generates no
   rule-inverse pairs, citing `egraph.rs:3068`, which is now inside `a_round`. The engine
   generates them (`egraph/src/egraph.rs:3799-3829`).
3. **Still true.** The final theorem's docstring (`Final/Main.lean:131-132`) equates
   `Unchanged` with the loop's `changes == 0`. `Fidelity/StopTest.lean` shows that test was
   insufficient before the size-stamp fix.
4. **Still true.** `Flatten/RegroupFits.lean:17-19` says the chain theorems are proved for AC
   only; `Flatten/RegroupChain.lean` proves them for every kind.
5. **Still true.** Most line numbers cited in docstrings for `egraph.rs`, `saturate.rs`,
   `ematch.rs` and `flatten.rs` have drifted; the functions exist under the same names. The
   citations `egraph.rs:4291-4305` (`EMatch/Env/Exec.lean:39`) and `apply.rs:1401-1411`
   (`EMatch/Env/Snapshot.lean:46`) point at unrelated code. `Fidelity/StopTest.lean:14`
   cites `s11_self_union.egg` and `s11_assoc.egg`, which appear to have been renamed to
   `stop_self_union_mints.egg` and `stop_assoc_flatten_mints.egg`. `ac_collapse.egg` is in
   `proofs/repro/`. `spec-flatten.md`, cited by `EMatch/Flatten/Views.lean:6`, `Laws.lean:12`
   and `Main.lean:10`, is not in the repository; neither is
   `doc/goal-canonical-flatten-views.md`, which the Rust sources cite
   (`egraph/src/nary_canon.rs:4`, `seq_collect.rs:252`).
6. **New.** `CC/Atoms.lean:53` names `completion_complete_atom_class`, which does not exist
   (the theorem is `CompleteAtoms.atom_class`). `EMatch/Flatten/RegroupSkip.lean:10` names
   `regroupSkip_iff`, which does not exist (the theorem is `regroupSkipG_iff`).
7. **New.** `CC/MinMonoKey.lean:11`, `:215` and `STATUS.md` cite `grow_wa.egg`; the fixture
   is `egraph/tests/egg/ac_minmono_grow_wa.egg`.
8. **Resolved.** The first edition recorded that the runtime design note
   ([`runtime-completeness-checks.md`](../../egraph/doc/future/runtime-completeness-checks.md))
   said in Section 6 that the regrouping skips are not modelled and have no check, and in
   Section 4 that the confirmation round checks `hcp`. The note now says that the skips need
   no check (`regroupSkipG_iff`) and that the confirmation round checks the rule-rule part
   through `lhs_reduced` and `cp_joinable`, with `AxiomCP` left to the per-law conditions.

**Errors of the first edition, corrected here.** It cited `QAtom` and `Sched` one line early
(they are at `EMatch/Engine/Sched.lean:32` and `:74`), and `Round.Persist` at a line inside a
later proof (it is at `Saturate/Transport.lean:45`). It named the fixture of
`idOrder_grow_breaks_I5` `grow_wa.egg`; the fixture is `ac_minmono_grow_wa.egg`. It gave the
A-only round's file without its `CC/` prefix (`CC/ARound/Basic.lean`). It cited the chain
lemmas `regroupStep_mem`, `regroupChain_mem_levels` and `regroupChain_of_mem_levels` by bare
line numbers after a citation of `Flatten/RegroupNested.lean`, which its own convention read
as that file; they are in `Flatten/RegroupChain.lean`. The citation of
`Saturate/Invariant.lean` among the stale tracking statements was wrong (item 1 above).

## 4. The counterexample theorems and the engine defects they record

Several theorems of the development are refutations. Each records an engine defect, with the
commit or engine function that fixed it, or a hypothesis that cannot be dropped; the guide's
Section 10 states the constraint each one evidences. Those marked "eval" are `#eval` scripts whose expected
outputs appear only in comments; nothing asserts them.

| Lean | File | What it shows | Fixture |
|---|---|---|---|
| `shrinkNoRefresh_breaks_I5` | `CC/Slot.lean:290` | a shrink without refreshing the minimal monomial breaks I5 and drops a rule; fixed by `refresh_min_monomial` | |
| `idOrder_grow_breaks_I5` | `CC/MinMonoKey.lean:250` | under the id order a renamed node grows past its classmate; fixed by per-class order keys | `ac_minmono_grow_wa.egg` |
| `witness_not_all` | `CC/AtomsWitness.lean:297` | the former `I0Active` (now `I0ActiveAll`) fails on a state with a leaf constant, and on every state with a class that holds no active node; fixed by weakening `I0Active` in `7838c767` | |
| `hcancel_not_derivable` | `CC/Lattice.lean:725` | lattice closure does not give `hcancel` | `cancel_lattice.egg` |
| `left_off_spine_unsound`, `right_off_spine_unsound` | `CC/ARound/Basic.lean:390`, `:420` | `a_round` before commit `7beed39f` rewrote off the spine and was unsound | `ac_fold_completion_spine.egg` |
| `stub_counterexample` | `CC/Proofs/CriticalPairModulo.lean:202` | the earlier local-confluence lemma is false; motivates rules plus law instances in `hcp` | |
| `invGen_cp_not_joinable` | `CC/Laws/Inverse.lean:512` | without `InvMatching` a generator critical pair is not joinable | |
| `combined_counterexample` | `CC/Laws/Combined.lean:160` | without `InvUnitFree` the composite clamp has two normal forms | |
| `delta_incomplete_untracked` | `Rounds/Counter.lean:184` | without the merge delta a new match has no new node | `semi_merge_membership_delta.egg` |
| `delta_incomplete_global` | `Rounds/Counter.lean:98` | a rule with a global misses a match under tracking; fixed by naive routing | `semi_eq_global_local.egg` |
| `raw_breaks_dedup` | `Rounds/SeqSplice.lean:292` | `add` spliced a same-operator child with stale children: two equal nodes in two classes | `seq_hashcons_miss_min.egg`, `rounds_r1_0581.egg` |
| `den_misses_single` | `Fidelity/NormalizeSat.lean:210` | literal `Den` has no value for a one-element AC right-hand side | |
| `denN_persist_fails` | `Fidelity/Recanon.lean` | a fired instance of a rule that builds an n-ary term need not survive a rebuild that applied a law to a node its right-hand side was built through; the engine counts such a rebuild in `spelling_epoch` since `8a84644b` | `semi_recanon_unit_drop.egg`, `semi_recanon_idem_collapse.egg`, `semi_recanon_inverse_cancel.egg`, `semi_recanon_pending_collapse.egg` |
| `per_node_form_fails` | `CC/Bridge/Modulo.lean:251` | matching modulo the theory holds at the class level only | |
| `fold_open_off_spine_unsound` | `Flatten/Fold.lean:138` | the flatten walk opened every position of a fold; fixed by `flatten::spine` | `flatten_fold_spine.egg` |
| `regroup_off_spine_unsound` | `Flatten/RegroupSound.lean:525` | regrouping off a fold's spine is unsound | |
| `preFix_cycles`, `preFix_diverges` | `Engine/Cursor.lean` | the cursor's search before commit `4e267030` cycles on three elements over two entries and returns for no fuel | `cursor_shapes.rs` |
| original demand rule on AC (eval) | `Flatten/FixCheck.lean:39-64` | the rule rejected a match that lives on no other view; fixed in commit `d95883f5` | `proofs/repro/demand-gap.egg` |
| kept-count rule under laws (eval) | `Flatten/LawsCheck.lean` | five cases where the corrected rule loses a match under inverse, identity, nilpotent and unit laws | |

## 5. Retracted claims

Each claim below appeared in an edition of the guide, in `STATUS.md` or in a Lean docstring,
and is withdrawn. None is to be cited as current.

- **Retracted: eager completion does not terminate on a four-equation `:identity :inverse`
  program.** A soundness wave reported that eager completion ran past 180 s in every matching
  option on a ground program with negation applied to monomials. The timing compared a debug
  binary at the PR head with a release binary at the main baseline; in one profile both
  heads converge in 43 rounds with 215 rules and 5,752 nodes (11 s release, 112 s debug),
  with byte-identical round traces. The run is a large but finite Gröbner basis of the
  lattice ideal (coefficients 10 and 2, where a ℤ-echelon basis has 3 rows), not a defect.
  Withdrawn as a nontermination report; what stands is the design observation that the
  lattice pass runs only at the fixpoint, so eager completion on `:inverse` instances with
  coefficients pays for the binomial basis first.
  The cursor matcher finding (item 19 of Section 2) is not retracted: `MatchIterator` did
  loop, and commit `4e267030` fixes the resume point of `ac_find_first` and `aci_find_first`.

- **Retracted: `hcancel` is a hypothesis the engine establishes.** `completion_complete_at_convergence`
  takes `hcancel` (joinability cancels a common summand), and the first edition and
  `STATUS.md` described the inverse and combined `_engine` theorems as having engine-level
  hypotheses only. `hcancel_not_derivable` (`CC/Lattice.lean:725`) is a converged,
  lattice-closed cancellative state in which `hcancel` fails, because it quantifies over every
  monomial and lattice closure over the nodes present. Commit `1be51963` replaces it in
  `CompleteHyps` and `CompleteAtoms` by `hlat : L.cancellative → LatticeClosed`, which
  `latticeClosed_of_engineFixed` derives from the fixpoint of `lattice_round`; `hcancel`
  remains only in the unbundled theorems, where the guide marks it as a limit.
- **Retracted: `DenN.persist` holds under normal-form recanonicalization.** `DenN.persist`
  (`Fidelity/Normalize.lean`) carries a right-hand side present as the normal forms `add`
  builds across a rebuild under literal persistence. The claim that it extends to the
  recanonicalization the laws perform is false: `denN_persist_fails` (`Fidelity/Recanon.lean`)
  is a store, a round meeting `StorePersistN`, and a right-hand side with an n-ary application
  that has a value before the round and only another value after it. The development keeps
  `DenN.persist_fixed` for right-hand sides without n-ary application, routes the rules that
  build one naive after a non-literal rebuild (`AChain`, `SChainN`; the engine's `respelled`
  re-match, commit `8a84644b`), and with completion on reads right-hand sides modulo the
  theory (`DenE.persist`, commit `989409fc`).
- **Retracted: `I0Active` over every class.** Until commit `7838c767`, `I0Active` quantified
  over every class of `Fin n`, so `completion_complete_at_convergence` applied to no state
  with a leaf constant (`witness_not_all`). That statement is now `I0ActiveAll` and the
  corollary `completion_complete_at_convergence_of_all`; the theorem constrains only the
  classes that hold an active node.
- **Retracted: `hcp` includes the containing pairs.** Until commit `2e40098d`, `RoundFixed`
  had an unrestricted `cp_joinable` and no `lhs_reduced`, so it asserted joinability of
  critical pairs the engine never superposes, and the law theorems took a separate hypothesis
  `hRR` (`RuleRuleCP`). `RoundFixed` now states the reducibility pass as `lhs_reduced`,
  `ruleRuleCP_of_fixed` and `hcp_of_fixed` derive the rule-rule part from it, and `hRR` is
  gone from the law theorems.
- **Retracted: `Env.WF` with a node/class partition of the variables.** Until commit
  `f1e8be1a`, `Env.WF` (`EMatch/Env/Model.lean:612`) partitioned the variables by `κ` into
  node and class variables; its `join` clause required the target to be a node variable
  (`κ t = true`) and every variable a lookup reads a class variable (`κ x = false`), and its
  `extractChild` clause required the extracted child to be a class variable. `atoms` gives a
  nested child one variable that is both the parent's child class and the nested atom's node
  variable, so with the parent lowered first `extractChild` then `join` gave it both kinds,
  and with the nested atom first `join` then the parent's `byChildPos` lookup did; the re-join
  `join a.node [byRepr a.node, byOp a.op]` violated `Env.WF` a second time by reading its own
  target. No theorem derived `Env.WF` from `PlanOK`, so the executor refinement was not
  connected to `plan_matches` for any nested pattern. The per-step binding kinds (`joinKinds`,
  `KindOk`) replace the partition, and `planOK_envWF` derives well-formedness from `PlanOK`.
- **Retracted: `regroup_idem_overlap_lost` as a limit of regrouped matching.** The theorem
  stated that `S{A, B, C}` equals `S{A, C, sab}` in every join semilattice and that no view
  of the regrouping enumeration is that view. Its two conjuncts are now
  `regroup_idem_overlap_sound` and `regroup_idem_overlap_loop_lost`, and the overlap stage
  (commits `893fc3ac`, `b932241b`) forms the view: `regroup_idem_overlap_found` is the
  counter-model turned witness.
- **Retracted: the stale citations of the first edition.** The first edition cited `QAtom`
  and `Sched` one line early (they are at `EMatch/Engine/Sched.lean:32` and `:74`), `Round.Persist`
  at a line inside a later proof (it is at `Saturate/Transport.lean:45`), the fixture of
  `idOrder_grow_breaks_I5` as `grow_wa.egg` (it is `ac_minmono_grow_wa.egg`), the A-only
  round's file without its `CC/` prefix (`CC/ARound/Basic.lean`), the chain lemmas
  `regroupStep_mem`, `regroupChain_mem_levels` and `regroupChain_of_mem_levels` by bare line
  numbers after a citation of `Flatten/RegroupNested.lean` (they are in
  `Flatten/RegroupChain.lean`), and `Saturate/Invariant.lean:27-28` among the stale tracking
  statements (that docstring says tracking is required, which is accurate).

## 6. Editions of the guide

- **First edition** (commit `a5cfa2d7`, 2026-11-06), written against upstream `main` at
  `6c37120b`: the vocabulary, the theorems of each layer with adequacy notes, and the list of
  hypotheses no theorem discharges (Section 3 above).
- **Second edition** (branch `wip/guide-rewrite`, commit `fa6be660`, 2026-11-08), written
  against `feat/completeness-proofs` as of 2026-11-06 (upstream `main` at `6c37120b` plus the
  regrouping-skip proof and the completeness theorems with leaf constants): a **Reading**
  paragraph under each main theorem, the pseudo-code of every algorithm the model states, the
  learnings, and the list of open and resolved findings (Section 2 above). Branch
  `feat/real-rules` resolved its items 1, 2 and 4: commit `f1e8be1a` replaced the executor's
  partition of variables by per-step binding kinds, and commit `8932dc12` stated the final
  theorem over the store with the represented graph as a part of the index and proved a run
  that meets all its hypotheses. The build and the axiom audit were not re-run for that
  edition; `STATUS.md` reported that `lake build` passes, that no declaration uses `sorry`,
  and that every `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.
  The runtime design note had no check implemented at the time of that edition.
- **Present-state edition** (branch `wip/guide-present`): the guide restructured as current
  state (what the development proves, the conformance and mirror tests, the remaining gaps,
  the constraints on the engine), with the findings, the defect narratives and the retracted
  claims moved to this file.
