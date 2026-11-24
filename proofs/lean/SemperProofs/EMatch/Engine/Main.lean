import SemperProofs.EMatch.Engine.Atoms
import SemperProofs.EMatch.Engine.AtomsMatch
import SemperProofs.EMatch.Engine.Lower
import SemperProofs.EMatch.Engine.Sched
import SemperProofs.EMatch.Engine.SchedRun
import SemperProofs.EMatch.Engine.Plan
import SemperProofs.EMatch.Engine.WF
import SemperProofs.EMatch.Engine.Runtime
import SemperProofs.EMatch.Engine.SemiNaive
import SemperProofs.EMatch.Engine.ByOp
import SemperProofs.EMatch.Engine.Pattern
import SemperProofs.EMatch.Engine.AtomsWF

/-!
# Engine plans: final theorems (spec-scheduler §1.3, §2.3, §3, §4, §5, §6)

Re-exports, under the names of the spec, of the theorems proved in the
`Engine/` files. The development covers every plan the engine's static or
runtime scheduler can produce for the scanning atoms `Plain`, `Comm`, A,
AC, ACI and the eager `Eq` atoms, under any selectivity estimate.

* `atoms_iff_match` (§1.3): a pattern matches at a class iff some extension
  of the binding satisfies every atom of its post-order flattening.
* `lower_sound_complete` (§3.2): one atom under any bound set.
* `plan_matches` (§3.2): every `PlanOK` plan emits exactly the bindings
  satisfying every atom with the right domains; `planOK_wf` (§3.1);
  `planOKFrom_matches` (§3.3).
* `engine_plan_sound` / `engine_plan_complete`: for a pattern, every
  `PlanOK` plan of `atoms P r` emits exactly the `MatchN` bindings.
* `runND_indep`, `runND_matches`, `runND_eq_plan` (§4).
* `byOp_demotion`, `byOp_demotion_op` (§5).
* `variant_partition`, `variants_disjoint`, `variants_cover_new` (§6).
-/

namespace Semper.EMatch

/-- §1.3. -/
theorem engine_atoms_iff_match (G : Graph) (P : Pat) (r : Var) (c : C) (σ : Binding)
    (hP : P.head.isSome = true) (hr : r ∉ P.vars) :
    MatchC G P c σ ↔
      ∃ σ', AgreeOn P.vars σ σ' ∧ σ'.cls r = some c ∧ ∀ a ∈ atoms P r, AtomSat G σ' a :=
  atoms_iff_match G P r c σ hP hr

/-- §3.2, one atom. -/
theorem engine_lower_sound_complete {G : Graph} {sig : Sym → Kind} (a : RAtom) (B : Finset Var)
    (σ : Binding) (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : a.WK sig)
    (hdom : ClsDom σ B) (hn : σ.node a.node = none) (hrf : a.RestFresh σ) :
    ∀ σ', σ' ∈ run G (lower a B) σ ↔ LowerSpec G a B σ σ' :=
  lower_sound_complete a B σ hk hconf hwk hdom hn hrf

/-- §3.2, whole plan. -/
theorem engine_plan_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (hwf : AtomsWF G sig atoms) (h : PlanOK atoms plan) :
    ∀ σ', σ' ∈ run G plan Binding.empty ↔ Matches G atoms σ' :=
  plan_matches hwf h

/-- §3.1, `PlanOK → PlanWF`. -/
theorem engine_planOK_wf {atoms : List QAtom} {plan : Plan} (h : PlanOK atoms plan) :
    PlanWF [] plan :=
  planOK_wf h

/-- Corollary for a pattern: soundness. Hypotheses: distinct node ids,
nodes conform to the kind signature and the pattern is well-kinded,
distinct rest variables, the root node variable is not a pattern variable,
the pattern is an application. -/
theorem engine_plan_sound {G : Graph} {sig : Sym → Kind} {P : Pat} {r : Var} {plan : Plan}
    {σ : Binding} (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : PatWK sig P)
    (hnd : P.restVars.Nodup) (hr : r ∉ P.vars) (hP : P.head.isSome = true)
    (h : PlanOK ((atoms P r).map QAtom.scan) plan) (hσ : σ ∈ run G plan Binding.empty) :
    ∃ id n, σ.node r = some id ∧ (id, n) ∈ G.nodes ∧ σ.cls r = some (G.find id) ∧ MatchN G P n σ :=
  engine_plan_sound' (atoms_atomsWF G sig P r hk hconf hwk hnd hr hP) hP h hσ

/-- Corollary for a pattern: completeness. -/
theorem engine_plan_complete {G : Graph} {sig : Sym → Kind} {P : Pat} {r : Var} {plan : Plan}
    {σ : Binding} {id : NodeId} {n : Node} (hk : G.KeysNodup) (hconf : G.Conforms sig)
    (hwk : PatWK sig P) (hnd : P.restVars.Nodup) (hr : r ∉ P.vars) (hP : P.head.isSome = true)
    (h : PlanOK ((atoms P r).map QAtom.scan) plan) (hmem : (id, n) ∈ G.nodes) (hm : MatchN G P n σ) :
    ∃ σ' ∈ run G plan Binding.empty, σ'.node r = some id ∧ BelowOn P.vars σ' σ :=
  engine_plan_complete' (atoms_atomsWF G sig P r hk hconf hwk hnd hr hP) hP hr h hmem hm

/-- §4. -/
theorem engine_runND_indep {G : Graph} {sig : Sym → Kind} {atoms : List QAtom}
    (choose₁ choose₂ : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runND G atoms choose₁ atoms.length ∅ ∅ Binding.empty ↔
      σ' ∈ runND G atoms choose₂ atoms.length ∅ ∅ Binding.empty :=
  runND_indep choose₁ choose₂ hwf

theorem engine_runND_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom}
    (choose : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runND G atoms choose atoms.length ∅ ∅ Binding.empty ↔ Matches G atoms σ' :=
  runND_matches choose hwf

/-- §5. -/
theorem engine_byOp_demotion (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym)
    (hop : Lookup.byOp f ∈ ls) :
    candidates G σ ls = (candidates G σ (ls.erase (.byOp f))).filter (fun id => decide (id ∈ G.byOp f)) :=
  byOp_demotion G σ ls f hop

/-- §6. -/
theorem engine_variant_partition {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {atoms : List QAtom} {ap : APlan} (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap)
    {k : Nat} {ak : RAtom} (hk : atoms[k]? = some (.scan ak)) :
    ∀ σ', σ' ∈ runVariant G isNew k ap ↔
      σ' ∈ runNaive G ap ∧ (∃ id, σ'.node ak.node = some id ∧ isNew id = true) ∧
        ∀ (j : Nat) (a : RAtom), j < k → atoms[j]? = some (.scan a) →
          ∃ id, σ'.node a.node = some id ∧ isNew id = false :=
  variant_partition hwf h hk

end Semper.EMatch
