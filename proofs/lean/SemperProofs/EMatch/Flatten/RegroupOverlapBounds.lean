import SemperProofs.EMatch.Flatten.RegroupOverlap

/-!
# `:flatten`: the overlap stage with the engine's bounds

`RegroupBounds.lean` proves that the regrouping loop with the engine's
counters (`BSt.run`) is the loop without them when no bound is hit, and
only keeps records of it otherwise. This file does the same for the overlap
stage of `RegroupOverlapDefs.lean` (`BSt.overlapAll`), with the same
simulation relations: each step of the stage with bounds against the step
without them (`StepR`, `RunR`), and the step without bounds against the
loop state (`ProjR`).

* `regroupBoundedO_cases`, `regroupBoundedO_halt_iff`,
  `regroupBoundedO_exact`, `regroupBoundedO_sub`: the bounded loop with the
  stage against the run without bounds, as `regroupBounded_cases` and its
  corollaries; a truncated run keeps records of the run without bounds.
* `regroupBoundedO_reach`: every record of any bounded run with the stage
  is reachable or one overlap step from a reachable record (`ReachO`).
* `enumerateRDBoundedO_le`, `enumerateRDBoundedO_ge`: one `Flatten`
  evaluation with the bounds and the stage against the engine's enumeration
  with the stage; `runBO_fst`, `runBO_ge` lift them to a query.
* `regroupBoundedO_plan_sound`, `regroupBoundedO_plan_complete`,
  `regroupBoundedO_query_exact`, `regroupBoundedO_match_exact`: the final
  theorems of `RegroupBounds.lean` with the stage. When a query ends with
  `flatten_regroup_truncated`, `flatten_skipped` and `flatten_overflowed`
  all zero, the bindings emitted are exactly those of the engine's
  enumeration with the stage, which `regroupSkipO_match_iff_laws`
  characterizes; with a counter nonzero, every binding emitted is still a
  match. The overlap stage counts its raw fits one by one against
  `MAX_REGROUP_WORK` and its records against `MAX_REGROUP_VIEWS`, so a run
  past a bound stops inside the stage as it does inside the loop.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch
open Binding (Extends)

/-! ## The steps against the steps without bounds -/

/-- `RunR.checkWork` for an inner step known on running states only. -/
theorem RunR.checkWorkR {B : Bounds} {n : Nat} {FB FN : BSt → BSt} (hF : RunR B FB FN) :
    RunR B
      (fun b => if pastB B.work (b.work + n) then { b with work := b.work + n, halt := some .truncated }
        else FB { b with work := b.work + n })
      (fun b => if pastB Bounds.none.work (b.work + n) then
          { b with work := b.work + n, halt := some .truncated }
        else FN { b with work := b.work + n }) := by
  simp only [Bounds.none, pastB_none, Bool.false_eq_true, ↓reduceIte]
  have hu : ∀ b : BSt, b.halt = Option.none → Grow b { b with work := b.work + n } :=
    fun b hb => ⟨rfl, le_refl _, Nat.le_add_right _ _, le_refl _, le_refl _, Mono.refl _⟩
  refine ⟨fun b hb => (hu b hb).trans (hF.grow _ hb), fun b hb he => ?_⟩
  have G := hF.grow { b with work := b.work + n } hb
  split
  · rename_i hp
    right
    exact ⟨Or.inr (pastB_mono G.work hp), G.mono⟩
  · rename_i hp
    refine hF.sim _ hb ?_
    simp only [BSt.exc, not_or, Bool.not_eq_true] at he ⊢
    exact ⟨he.1, Bool.of_not_eq_true hp, he.2.2⟩

theorem addTargetO_stepR (B : Bounds) (t : View) (ds : List RecR) :
    StepR B (fun b => b.addTargetO B t ds) (fun b => b.addTargetO Bounds.none t ds) := by
  have hrest := (RunR.ite (p := fun b => (b.st.recs t).any RecR.uncond = true) (RunR.id B)
    (StepR.foldl ds (fun d _ => addRec_stepR B t d)).run).guard
  exact ((enterTarget_stepR B t).run.comp hrest).guard

theorem overlapFitStep_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (srcs : List RecR)
    (gg : C × List (C × Nat)) (raw : List (C × Nat)) :
    StepR B (fun b => BSt.overlapFitStep B ix ctx laws srcs gg b raw)
      (fun b => BSt.overlapFitStep Bounds.none ix ctx laws srcs gg b raw) := by
  have hw : RunR B (fun b => { b with ovf := b.ovf + 1 }) (fun b => { b with ovf := b.ovf + 1 }) :=
    ⟨fun b hb => ⟨rfl, le_refl _, le_refl _, le_refl _, Nat.le_add_right _ _, Mono.refl _⟩,
      fun b _ he => Or.inl ⟨rfl, by simpa [BSt.exc] using he⟩⟩
  have hm : StepR B (fun b => match normalize ctx.κ laws raw with
      | .node t => b.addTargetO B t ((srcRecs srcs).map (deriveRec t gg.1 (gg.2.map Prod.fst)))
      | _ => b)
      (fun b => match normalize ctx.κ laws raw with
      | .node t => b.addTargetO Bounds.none t ((srcRecs srcs).map (deriveRec t gg.1 (gg.2.map Prod.fst)))
      | _ => b) := by
    generalize normalize ctx.κ laws raw = nr
    cases nr with
    | node t => exact addTargetO_stepR B t _
    | _ => exact StepR.id B
  exact (RunR.checkWorkR (n := 1) (RunR.ite (p := fun _ => ix.wide laws raw = true) hw hm.run)).guard

theorem overlapGroupStep_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (w : View) (srcs : List RecR) (gg : C × List (C × Nat)) :
    StepR B (fun b => BSt.overlapGroupStep B ix ctx laws limit w srcs b gg)
      (fun b => BSt.overlapGroupStep Bounds.none ix ctx laws limit w srcs b gg) :=
  (RunR.ite (p := fun _ => (!isCand w gg) = true) (RunR.id B)
    (RunR.checkWork (StepR.foldl _
      (fun raw _ => overlapFitStep_stepR B ix ctx laws srcs gg raw)))).guard

theorem overlapView_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (w : View) (srcs : List RecR) :
    StepR B (BSt.overlapView B ix ctx laws limit gs w srcs)
      (BSt.overlapView Bounds.none ix ctx laws limit gs w srcs) :=
  (RunR.checkWork (StepR.foldl gs
    (fun gg _ => overlapGroupStep_stepR B ix ctx laws limit w srcs gg))).guard

theorem overlapAll_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) :
    StepR B (BSt.overlapAll B ix ctx laws limit gs) (BSt.overlapAll Bounds.none ix ctx laws limit gs) := by
  unfold BSt.overlapAll
  by_cases hg : (ctx.κ != .aci || limit == 0) = true
  · simp only [hg, ↓reduceIte]
    exact StepR.id B
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    exact (RunR.diag
      (F := fun b₀ b => b₀.st.order.foldl
        (fun b w => BSt.overlapView B ix ctx laws limit gs w (b₀.st.recs w) b) b)
      (G := fun b₀ b => b₀.st.order.foldl
        (fun b w => BSt.overlapView Bounds.none ix ctx laws limit gs w (b₀.st.recs w) b) b)
      (fun b₀ => (StepR.foldl b₀.st.order
        (fun w _ => overlapView_stepR B ix ctx laws limit gs w (b₀.st.recs w))).run)).guard

/-! ## The run without bounds is the stage -/

theorem addTargetO_projR (t : View) (ds : List RecR) :
    ProjR (fun b => b.addTargetO Bounds.none t ds) (fun s => s.addTargetO t ds) := by
  intro b hb ho
  beta_reduce at ho ⊢
  have hfold := ProjR.foldl (fN := BSt.addRec Bounds.none t) (f := SkipSt.addRec t) ds
    (fun d _ => (addRec_stepR Bounds.none t d).grow) (fun d _ => addRec_projR t d)
  have hgE := (enterTarget_stepR Bounds.none t).grow b hb
  set b₁ := b.enterTarget Bounds.none t with hb₁
  have hh1 : b₁.halt = Option.none := hgE.halt.trans hb
  have hst1 : b₁.st = if t ∈ b.st.order then b.st else { b.st with order := b.st.order ++ [t] } := by
    rw [hb₁]
    simp only [BSt.enterTarget, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      Bounds.none, pastB_none]
    split <;> rfl
  have hgF := (StepR.foldl ds (fun d _ => addRec_stepR Bounds.none t d)).grow b₁ hh1
  have e : b.addTargetO Bounds.none t ds =
      if (b₁.st.recs t).any RecR.uncond then b₁ else ds.foldl (BSt.addRec Bounds.none t) b₁ := by
    rw [hb₁] at hh1
    simp only [BSt.addTargetO, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hh1, hb₁]
  rw [e] at ho ⊢
  unfold SkipSt.addTargetO
  dsimp only
  rw [← hst1]
  by_cases hu : (b₁.st.recs t).any RecR.uncond = true
  · simp [hu]
  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    have ho1 : b₁.ovf = b.ovf := le_antisymm (ho ▸ hgF.ovf) hgE.ovf
    exact hfold b₁ hh1 (ho.trans ho1.symm)

theorem overlapFitStep_projR (ix : Ix) (ctx : Ctx) (laws : Laws) (srcs : List RecR)
    (gg : C × List (C × Nat)) (raw : List (C × Nat)) :
    ProjR (fun b => BSt.overlapFitStep Bounds.none ix ctx laws srcs gg b raw)
      (fun s => SkipSt.overlapFitStep ctx laws srcs gg s raw) := by
  intro b hb ho
  beta_reduce at ho ⊢
  unfold BSt.overlapFitStep at ho ⊢
  unfold SkipSt.overlapFitStep
  simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none_work, pastB_none]
    at ho ⊢
  by_cases hw : ix.wide laws raw = true
  · simp [hw] at ho
  · simp only [hw, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    revert ho
    cases normalize ctx.κ laws raw with
    | node t =>
        exact fun ho => addTargetO_projR t _
          ⟨b.st, b.views, b.work + 1, b.elems, b.gelems, b.peak, b.ovf, Option.none⟩ rfl ho
    | _ => exact fun _ => rfl

theorem overlapGroupStep_projR (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat) (w : View)
    (srcs : List RecR) (gg : C × List (C × Nat)) :
    ProjR (fun b => BSt.overlapGroupStep Bounds.none ix ctx laws limit w srcs b gg)
      (fun s => SkipSt.overlapGroupStep ctx laws limit w srcs s gg) := by
  intro b hb ho
  beta_reduce at ho ⊢
  unfold BSt.overlapGroupStep at ho ⊢
  unfold SkipSt.overlapGroupStep
  simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none_work, pastB_none]
    at ho ⊢
  by_cases hc : isCand w gg = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    exact ProjR.foldl (fN := BSt.overlapFitStep Bounds.none ix ctx laws srcs gg)
      (f := SkipSt.overlapFitStep ctx laws srcs gg) _
      (fun raw _ => (overlapFitStep_stepR Bounds.none ix ctx laws srcs gg raw).grow)
      (fun raw _ => overlapFitStep_projR ix ctx laws srcs gg raw)
      ⟨b.st, b.views, b.work + gg.2.length, b.elems, b.gelems, b.peak, b.ovf, Option.none⟩ rfl ho
  · rw [overlapFits_nil_of_not_cand (Bool.of_not_eq_true hc)]
    simp [Bool.of_not_eq_true hc]

theorem overlapView_projR (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (w : View) (srcs : List RecR) :
    ProjR (BSt.overlapView Bounds.none ix ctx laws limit gs w srcs)
      (SkipSt.overlapView ctx laws limit gs w srcs) := by
  intro b hb ho
  unfold BSt.overlapView at ho ⊢
  unfold SkipSt.overlapView
  simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none_work, pastB_none]
    at ho ⊢
  exact ProjR.foldl (fN := BSt.overlapGroupStep Bounds.none ix ctx laws limit w srcs)
    (f := SkipSt.overlapGroupStep ctx laws limit w srcs) gs
    (fun gg _ => (overlapGroupStep_stepR Bounds.none ix ctx laws limit w srcs gg).grow)
    (fun gg _ => overlapGroupStep_projR ix ctx laws limit w srcs gg)
    ⟨b.st, b.views, b.work + useWork ix w, b.elems, b.gelems, b.peak, b.ovf, Option.none⟩ rfl ho

theorem overlapAll_projR (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) :
    ProjR (BSt.overlapAll Bounds.none ix ctx laws limit gs) (SkipSt.overlapAll ctx laws limit gs) := by
  intro b hb ho
  unfold BSt.overlapAll at ho ⊢
  unfold SkipSt.overlapAll
  by_cases hg : (ctx.κ != .aci || limit == 0) = true
  · simp [hg]
  · simp only [hg, Bool.false_eq_true, ↓reduceIte, hb, Option.isSome_none] at ho ⊢
    exact ProjR.foldl
      (fN := fun b' w => BSt.overlapView Bounds.none ix ctx laws limit gs w (b.st.recs w) b')
      (f := fun s w => SkipSt.overlapView ctx laws limit gs w (b.st.recs w) s) b.st.order
      (fun w _ => (overlapView_stepR Bounds.none ix ctx laws limit gs w (b.st.recs w)).grow)
      (fun w _ => overlapView_projR ix ctx laws limit gs w (b.st.recs w)) b hb ho

/-! ## The bounded run with the stage -/

section Run

variable (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
  (gs : List (C × List (C × Nat))) (base : List RecR)

/-- **The bounded run with the stage against the run without bounds**: the
latter never stops; the former is the latter, within the bounds, or stopped
with the latter past the bound it stopped at, its records among the
latter's. -/
theorem regroupBoundedO_cases :
    (regroupBoundedO Bounds.none ix ctx dir laws limit gs base).halt = Option.none ∧
      ((regroupBoundedO B ix ctx dir laws limit gs base =
            regroupBoundedO Bounds.none ix ctx dir laws limit gs base ∧
          ¬(regroupBoundedO Bounds.none ix ctx dir laws limit gs base).exc B) ∨
        (HaltOK B (regroupBoundedO B ix ctx dir laws limit gs base).halt
            (regroupBoundedO Bounds.none ix ctx dir laws limit gs base) ∧
          Mono (regroupBoundedO B ix ctx dir laws limit gs base).st
            (regroupBoundedO Bounds.none ix ctx dir laws limit gs base).st)) :=
  let h := (run_stepR B ix ctx dir laws gs (skipFuel ctx dir laws base)).comp
    (overlapAll_stepR B ix ctx laws limit gs)
  ⟨(h.grow _ rfl).halt, h.sim _ rfl (init_not_exc B base)⟩

/-- The run without bounds, when no fit overflows the width, ends with the
records of the loop and the stage. -/
theorem regroupBoundedO_none_records
    (ho : (regroupBoundedO Bounds.none ix ctx dir laws limit gs base).ovf = 0) :
    (regroupBoundedO Bounds.none ix ctx dir laws limit gs base).st.records =
      regroupSkipO ctx dir laws limit gs base := by
  unfold regroupBoundedO regroupBoundedG at ho ⊢
  have h := ProjR.comp (g₁ := BSt.run Bounds.none ix ctx dir laws gs (skipFuel ctx dir laws base))
    (g₂ := BSt.overlapAll Bounds.none ix ctx laws limit gs)
    (f₁ := SkipSt.run ctx dir laws gs (skipFuel ctx dir laws base))
    (f₂ := SkipSt.overlapAll ctx laws limit gs)
    (run_stepR Bounds.none ix ctx dir laws gs _).grow (overlapAll_stepR Bounds.none ix ctx laws limit gs).grow
    (run_projR ix ctx dir laws gs _) (overlapAll_projR ix ctx laws limit gs)
  rw [h (BSt.init base) rfl ho]
  rfl

/-- **The run stops iff the run without bounds ends past a bound.** -/
theorem regroupBoundedO_halt_iff :
    (regroupBoundedO B ix ctx dir laws limit gs base).halt.isSome = true ↔
      (regroupBoundedO Bounds.none ix ctx dir laws limit gs base).exc B := by
  obtain ⟨hu, h | ⟨hh, -⟩⟩ := regroupBoundedO_cases B ix ctx dir laws limit gs base
  · rw [h.1, hu]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact h.2
  · exact ⟨fun _ => hh.exc, fun _ => hh.isSome⟩

/-- **Exactness**: a run that does not stop, with no fit past the width,
ends with the records of the loop and the stage. -/
theorem regroupBoundedO_exact
    (hh : (regroupBoundedO B ix ctx dir laws limit gs base).halt = Option.none)
    (ho : (regroupBoundedO B ix ctx dir laws limit gs base).ovf = 0) :
    (regroupBoundedO B ix ctx dir laws limit gs base).st.records =
      regroupSkipO ctx dir laws limit gs base := by
  obtain ⟨-, he | ⟨hk, -⟩⟩ := regroupBoundedO_cases B ix ctx dir laws limit gs base
  · rw [he.1] at ho ⊢
    exact regroupBoundedO_none_records ix ctx dir laws limit gs base ho
  · rw [hh] at hk; exact hk.elim

/-- **Soundness under truncation**: every record of the bounded run with the
stage is a record of the run without bounds. -/
theorem regroupBoundedO_sub {r : RecR}
    (h : r ∈ (regroupBoundedO B ix ctx dir laws limit gs base).st.records) :
    r ∈ (regroupBoundedO Bounds.none ix ctx dir laws limit gs base).st.records := by
  obtain ⟨-, he | ⟨-, hm⟩⟩ := regroupBoundedO_cases B ix ctx dir laws limit gs base
  · rwa [he.1] at h
  · exact mem_records_of_mono hm h

end Run

/-! ## Every record of any run is a record of the stage -/

section Reach

variable {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {base : List RecR}

/-- Every record is filed under its view and reachable or one overlap step
from a reachable record. -/
def RInvO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (base : List RecR) (b : BSt) :
    Prop :=
  ∀ w, ∀ r ∈ b.st.recs w, r.1 = w ∧ ReachO ctx dir laws limit base r

theorem RInvO.of_rinv {b : BSt} (h : RInv ctx dir laws base b) : RInvO ctx dir laws limit base b :=
  fun w r hr => ⟨(h w r hr).1, Or.inl (h w r hr).2⟩

theorem addRec_rinvO {B : Bounds} {t : View} {b : BSt} {d : RecR}
    (h : RInvO ctx dir laws limit base b) (hd : d.1 = t ∧ ReachO ctx dir laws limit base d) :
    RInvO ctx dir laws limit base (b.addRec B t d) := by
  intro w r hr
  unfold BSt.addRec at hr
  split at hr; · exact h w r hr
  split at hr; · exact h w r hr
  split at hr; · exact h w r hr
  split at hr; · exact h w r hr
  simp only at hr
  unfold SkipSt.addRec at hr
  split at hr
  · exact h w r hr
  · by_cases hw : w = t
    · subst hw
      simp only [Function.update_self, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h _ r hr
      · exact hd
    · simp only [Function.update_of_ne hw] at hr
      exact h w r hr

theorem addTargetO_rinvO {B : Bounds} {t : View} {ds : List RecR} {b : BSt}
    (h : RInvO ctx dir laws limit base b) (hds : ∀ d ∈ ds, d.1 = t ∧ ReachO ctx dir laws limit base d) :
    RInvO ctx dir laws limit base (b.addTargetO B t ds) := by
  have he : RInvO ctx dir laws limit base (b.enterTarget B t) := by
    intro w r hr; rw [enterTarget_recs] at hr; exact h w r hr
  unfold BSt.addTargetO
  split; · exact h
  dsimp only
  split; · exact he
  split; · exact he
  exact foldl_induct (BSt.addRec B t) (RInvO ctx dir laws limit base) ds _ he
    (fun b d hd hb => addRec_rinvO hb (hds d hd))

theorem overlapFitStep_rinvO {B : Bounds} {ix : Ix} {w : View} {srcs : List RecR}
    (hsrc : SrcOK ctx dir laws base w srcs) {gg : C × List (C × Nat)} (hgg : gg ∈ groupsOf ctx)
    {raw : List (C × Nat)} (hraw : raw ∈ overlapFits ctx.κ limit w gg.1 gg.2) {b : BSt}
    (h : RInvO ctx dir laws limit base b) :
    RInvO ctx dir laws limit base (BSt.overlapFitStep B ix ctx laws srcs gg b raw) := by
  unfold BSt.overlapFitStep
  split; · exact h
  split; · exact h
  dsimp only
  split; · exact h
  split
  · rename_i t hn
    refine addTargetO_rinvO h (fun d hd => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
    have hr' : r ∈ srcs := (srcRecs_spec (fun r hr => (hsrc r hr).1)).1 r hr
    obtain ⟨hrw, hreach⟩ := hsrc r hr'
    refine ⟨rfl, Or.inr ⟨r, hreach, ?_⟩⟩
    exact overlapRec_of (g := gg.1) (grp := gg.2) hgg (by rw [hrw]; exact hraw) hn
  · exact h

theorem overlapGroupStep_rinvO {B : Bounds} {ix : Ix} {w : View} {srcs : List RecR}
    (hsrc : SrcOK ctx dir laws base w srcs) {gg : C × List (C × Nat)} (hgg : gg ∈ groupsOf ctx)
    {b : BSt} (h : RInvO ctx dir laws limit base b) :
    RInvO ctx dir laws limit base (BSt.overlapGroupStep B ix ctx laws limit w srcs b gg) := by
  unfold BSt.overlapGroupStep
  split; · exact h
  split; · exact h
  split; · exact h
  exact foldl_induct (BSt.overlapFitStep B ix ctx laws srcs gg) (RInvO ctx dir laws limit base) _ _ h
    (fun b raw hraw hb => overlapFitStep_rinvO hsrc hgg hraw hb)

theorem overlapView_rinvO {B : Bounds} {ix : Ix} {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) {w : View} {srcs : List RecR}
    (hsrc : SrcOK ctx dir laws base w srcs) {b : BSt} (h : RInvO ctx dir laws limit base b) :
    RInvO ctx dir laws limit base (BSt.overlapView B ix ctx laws limit gs w srcs b) := by
  unfold BSt.overlapView
  split; · exact h
  split; · exact h
  exact foldl_induct (BSt.overlapGroupStep B ix ctx laws limit w srcs) (RInvO ctx dir laws limit base)
    gs _ h (fun b gg hgg hb => overlapGroupStep_rinvO hsrc (hgs gg hgg) hb)

theorem overlapAll_rinvO {B : Bounds} {ix : Ix} {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) {b₀ : BSt} (h : RInv ctx dir laws base b₀) :
    RInvO ctx dir laws limit base (BSt.overlapAll B ix ctx laws limit gs b₀) := by
  unfold BSt.overlapAll
  split; · exact RInvO.of_rinv h
  split; · exact RInvO.of_rinv h
  have hsrc : ∀ w, SrcOK ctx dir laws base w (b₀.st.recs w) := fun w r hr => h w r hr
  exact foldl_induct _ (RInvO ctx dir laws limit base) b₀.st.order b₀ (RInvO.of_rinv h)
    (fun b w _ hb => overlapView_rinvO hgs (hsrc w) hb)

/-- **Every record of a bounded run with the stage is reachable or one
overlap step from a reachable record**, whatever the bounds and overflows. -/
theorem regroupBoundedO_reach (B : Bounds) (ix : Ix) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) {r : RecR}
    (h : r ∈ (regroupBoundedO B ix ctx dir laws limit gs base).st.records) :
    ReachO ctx dir laws limit base r := by
  simp only [SkipSt.records, List.mem_flatMap] at h
  obtain ⟨v, -, hr⟩ := h
  exact (overlapAll_rinvO hgs (run_rinv hgs _ _ (init_rinv base)) v r hr).2

end Reach

/-! ## One `Flatten` evaluation -/

/-- The records of the stage within any limit are covered by the engine's
regrouping with the stage within the limit. -/
theorem cov_skipO {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {limit : Nat} {r : RecR} (hr : ReachO ctx dir laws limit base r)
    (hl : r.2.2.length ≤ limit) :
    ∃ c ∈ withinLimit limit (regroupSkipO ctx dir laws limit (groupsOfEngine ctx) base), Cov c r := by
  obtain ⟨hs, hc⟩ := regroupSkipO_spec (dir := dir) (laws := laws) hb (groupsOfEngine_sub ctx)
    (candSup_of_sup dir (groupsOfEngine_sup ctx)) (candSupO_of_sup (groupsOfEngine_sup ctx))
  obtain ⟨c, hc', hcov⟩ := hc r hr
  exact ⟨c, mem_withinLimit.2 ⟨hc', le_trans (hcov.length (reachO_good hb (hs c hc')).2) hl⟩, hcov⟩

section Eval

variable (B : Bounds) (ix : Ix) (T : C → Bool) (ctx : Ctx) (dir : Dir) (laws : Laws)
  (limit : Nat) (n : Node)

/-- **Soundness of one evaluation with the stage**: every view of the bounded
enumeration is a view of the engine's enumeration with the stage, whose
demand accepts at least as much, whatever stopped it. -/
theorem enumerateRDBoundedO_le :
    ∀ w d, (w, d) ∈ (enumerateRDBoundedO B ix T ctx dir laws limit n).views →
      ∃ d', (w, d') ∈ enumerateRDSkipO T ctx dir laws limit n ∧
        ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true := by
  have hb := baseGood_filter (baseGood_baseRecsR ctx dir laws n) (keepRec ctx.κ T laws)
  unfold enumerateRDBoundedO enumerateRDSkipO regroupAllSkipO
  dsimp only
  split
  · refine viewLe_of_cov (fun r hr => cov_skipO hb (Or.inl ⟨r, hr, Relation.ReflTransGen.refl⟩) ?_)
    obtain ⟨-, -, -, -, hn⟩ := mem_baseRecsR (List.mem_filter.1 hr).1
    rw [hn]; exact Nat.zero_le _
  · split
    · exact viewLe_nil _
    · refine viewLe_of_cov (fun r hr => ?_)
      obtain ⟨hr, hl⟩ := mem_withinLimit.1 hr
      exact cov_skipO hb (regroupBoundedO_reach B ix (groupsOfEngine_sub ctx) hr) hl

/-- **Exactness of one evaluation with the stage**: with no truncation, no
skip and no overflow, the engine's enumeration with the stage has no view
the bounded one lacks, nor a demand accepting more. -/
theorem enumerateRDBoundedO_ge
    (h : (enumerateRDBoundedO B ix T ctx dir laws limit n).counts = 0) :
    ∀ w d, (w, d) ∈ enumerateRDSkipO T ctx dir laws limit n →
      ∃ d', (w, d') ∈ (enumerateRDBoundedO B ix T ctx dir laws limit n).views ∧
        ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true := by
  have hb := baseGood_filter (baseGood_baseRecsR ctx dir laws n) (keepRec ctx.κ T laws)
  revert h
  unfold enumerateRDBoundedO enumerateRDSkipO regroupAllSkipO
  dsimp only
  split
  · rename_i hl
    obtain ⟨hl, hd⟩ := hl
    intro _
    subst hl
    refine viewLe_of_cov (fun r hr => ?_)
    obtain ⟨hr, hl⟩ := mem_withinLimit.1 hr
    have hreach := (regroupSkipO_spec (dir := dir) (laws := laws) hb (groupsOfEngine_sub ctx)
      (candSup_of_sup dir (groupsOfEngine_sup ctx)) (candSupO_of_sup (groupsOfEngine_sup ctx))).1 r hr
    exact ⟨r, mem_base_of_reach hd (reach_of_reachO_zero hreach)
      (List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)), Cov.refl r⟩
  · split
    · intro h; simp [BOut.counts] at h; cases h
    · rename_i hov
      intro h
      simp only [BOut.counts] at h
      have hc : ∀ {a b c d e f : Nat}, (⟨a, b, c⟩ : Counts) = ⟨d, e, f⟩ → a = d ∧ c = f :=
        fun h => by cases h; exact ⟨rfl, rfl⟩
      obtain ⟨htr, ho⟩ := hc h
      have hnone : (regroupBoundedO B ix ctx dir laws limit (groupsOfEngine ctx)
          ((baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws))).halt = Option.none := by
        cases hH : (regroupBoundedO B ix ctx dir laws limit (groupsOfEngine ctx)
          ((baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws))).halt with
        | none => rfl
        | some x =>
            cases x
            · rw [hH] at htr; simp at htr
            · exact absurd hH hov
      rw [regroupBoundedO_exact B ix ctx dir laws limit _ _ hnone ho]
      exact viewLe_refl _

end Eval

/-! ## The capped takeable set -/

/-- **The engine's enumeration with the stage and the capped takeable set
meets the plan specification.** -/
theorem regroupSkipOCap_spec (dir : Sym → Dir) : (Enumerator.regroupSkipOCap dir).Spec where
  normal h := normal_enumerateRSkipO h
  normalP h := normal_enumerateRDSkipO h
  to_full {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRDSkipO (takeableRCap ctx σ items) ctx (dir ctx.f) laws
        items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRDSkipO_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroupO (takeableRCap_down _ _ _) (takenOf_takeableRCap hext hb)).1 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRSkipO ctx (dir ctx.f) laws items.length n ∧ _
    exact enumerateRSkipO_iff.2 ⟨d₂, hd₂, hacc₂⟩
  to_pruned {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRSkipO ctx (dir ctx.f) laws items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRSkipO_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroupO (takeableRCap_down _ _ _) (takenOf_takeableRCap hext hb)).2 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRDSkipO (takeableRCap ctx σ items) ctx (dir ctx.f) laws
      items.length n ∧ _
    exact enumerateRDSkipO_iff.2 ⟨d₂, hd₂, hacc₂⟩

theorem atomSat_regroupSkipOCap_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom} :
    AtomSatG (Enumerator.regroupSkipOCap dir) c σ a ↔
      AtomSatG (Enumerator.regroupSkipO dir) c σ a := by
  unfold AtomSatG Enumerator.regroupSkipOCap Enumerator.regroupSkipO
  exact Iff.rfl

/-! ## A query -/

theorem runStepBO_fst (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) (s : EStep)
    (env : EEnv) :
    (runStepBO B ix dir c s env).1 = runEStepG (Enumerator.regroupBoundedO B ix dir) c s env := by
  cases s with
  | flatten v f κ out items =>
      simp only [runStepBO, runEStepG]
      cases env.σ.nodeOf c.G v <;> rfl
  | _ => rfl

/-- The environments of `runBO` are those of the plan run with the bounded
enumeration with the stage. -/
theorem runBO_fst (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    ∀ (ss : List EStep) (env : EEnv),
      (runBO B ix dir c ss env).1 = runEG (Enumerator.regroupBoundedO B ix dir) c ss env
  | [], _ => rfl
  | s :: ss, env => by
      simp only [runBO, runEG, List.flatMap_map, runStepBO_fst]
      congr 1
      funext y
      exact runBO_fst B ix dir c ss y

/-- With the counters zero, the plan run with the unbounded enumeration with
the stage emits nothing the bounded one does not. -/
theorem runBO_ge (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    ∀ (ss : List EStep) (env env' : EEnv), (runBO B ix dir c ss env).2 = 0 → EnvLe env' env →
      ∀ x' ∈ runEG (Enumerator.regroupSkipOCap dir) c ss env',
        ∃ x ∈ (runBO B ix dir c ss env).1, EnvLe x' x
  | [], env, env', _, h, x', hx' => by
      simp only [runEG, List.mem_singleton] at hx'
      subst hx'
      exact ⟨env, List.mem_singleton_self _, h⟩
  | s :: ss, env, env', hz, h, x', hx' => by
      simp only [runBO] at hz ⊢
      obtain ⟨hz₁, hz₂⟩ := Counts.add_eq_zero.1 hz
      rw [Counts.sum_eq_zero] at hz₂
      simp only [runEG, List.mem_flatMap] at hx'
      obtain ⟨y', hy', hx'⟩ := hx'
      have hf : ∀ v f κ out items n, s = .flatten v f κ out items → env'.σ.nodeOf c.G v = some n →
          CallLe (Enumerator.regroupSkipOCap dir) (Enumerator.regroupBoundedO B ix dir)
            (c.ctx f κ) (c.laws f) env'.σ items n := by
        rintro v f κ out items n rfl hn
        rw [h.1] at hn ⊢
        have hz₁' := hz₁
        simp only [runStepBO, hn] at hz₁'
        exact enumerateRDBoundedO_ge B ix _ (c.ctx f κ) (dir f) (c.laws f) items.length n hz₁'
      obtain ⟨y, hy, hyy⟩ := runEStepG_le h hf hy'
      rw [← runStepBO_fst] at hy
      have hzy : (runBO B ix dir c ss y).2 = 0 :=
        hz₂ _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨y, hy, rfl⟩, rfl⟩)
      obtain ⟨x, hx, hxx⟩ := runBO_ge B ix dir c ss y y' hzy hyy x' hx'
      exact ⟨x, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨y, hy, rfl⟩, hx⟩, hxx⟩

/-! ## The final theorems -/

/-- **Soundness of the bounded plan with the stage**: every binding the plan
emits with the engine's bounds, whatever was truncated, skipped or
overflowed, satisfies every atom under the engine's enumeration with the
stage and without bounds. -/
theorem regroupBoundedO_plan_sound {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix) {env : EEnv}
    (h : env ∈ (runBO B ix dir c (planF as ∅ r) EEnv.empty).1) :
    (∀ a ∈ as, AtomSatG (Enumerator.regroupSkipO dir) c env.σ a) ∧
      ClsDom env.σ (planBound as ∅) := by
  rw [runBO_fst] at h
  obtain ⟨env', h', hle⟩ := runEG_le (E₁ := Enumerator.regroupBoundedO B ix dir)
    (E₂ := Enumerator.regroupSkipOCap dir)
    (fun ctx laws σ items n => by
      unfold CallLe Enumerator.regroupBoundedO Enumerator.regroupSkipOCap
      exact enumerateRDBoundedO_le B ix (takeableRCap ctx σ items) ctx (dir ctx.f) laws
        items.length n)
    _ _ _ (EnvLe.refl _) env h
  obtain ⟨hsat, hdom⟩ := flatten_plan_sound_of_spec (regroupSkipOCap_spec dir) r hw h'
  rw [hle.1]
  exact ⟨fun a ha => atomSat_regroupSkipOCap_iff.1 (hsat a ha), hdom⟩

/-- **Completeness of the bounded plan with the stage when the counters are
zero.** -/
theorem regroupBoundedO_plan_complete {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix)
    (hz : (runBO B ix dir c (planF as ∅ r) EEnv.empty).2 = 0) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG (Enumerator.regroupSkipO dir) c σ' a) :
    ∃ env ∈ (runBO B ix dir c (planF as ∅ r) EEnv.empty).1, Extends env.σ σ' := by
  obtain ⟨env', h', hext⟩ := flatten_plan_complete_of_spec (regroupSkipOCap_spec dir) r hw
    (fun a ha => atomSat_regroupSkipOCap_iff.2 (hsat a ha))
  obtain ⟨env, h, hle⟩ := runBO_ge B ix dir c _ _ _ hz (EnvLe.refl _) env' h'
  exact ⟨env, h, hle.1 ▸ hext⟩

/-- **The runtime check, with the stage**: when a query ends with the three
counters of its `Flatten` steps zero, the bindings the bounded plan emits are
exactly those satisfying every atom under the engine's enumeration with the
stage, which `regroupSkipO_match_iff_laws` characterizes. -/
theorem regroupBoundedO_query_exact {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix)
    (hz : (runBO B ix dir c (planF as ∅ r) EEnv.empty).2 = 0) :
    (∀ env ∈ (runBO B ix dir c (planF as ∅ r) EEnv.empty).1,
        ∀ a ∈ as, AtomSatG (Enumerator.regroupSkipO dir) c env.σ a) ∧
      ∀ σ', (∀ a ∈ as, AtomSatG (Enumerator.regroupSkipO dir) c σ' a) →
        ∃ env ∈ (runBO B ix dir c (planF as ∅ r) EEnv.empty).1, Extends env.σ σ' :=
  ⟨fun _ h => (regroupBoundedO_plan_sound r hw B ix h).1,
    fun _ hsat => regroupBoundedO_plan_complete r hw B ix hz hsat⟩

/-- **The runtime check, per atom, with the stage**: with the counters zero,
an emitted binding satisfies each n-ary atom through a chain of regroupings
under the operator's laws followed by at most one overlap step. -/
theorem regroupBoundedO_match_exact {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix)
    (hz : (runBO B ix dir c (planF as ∅ r) EEnv.empty).2 = 0) {σ : Binding} {a : RAtom}
    (ha : a ∈ as) {κ : FlatKind} (hκ : a.shape.flatKind = some κ) {env : EEnv}
    (henv : env ∈ (runBO B ix dir c (planF as ∅ r) EEnv.empty).1) (hσ : env.σ = σ) :
    ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
      σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
      ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
        RegroupChainO (c.ctx a.op κ) (dir a.op) (c.laws a.op) a.elems.length r₀ r ∧
        r.2.2.length ≤ a.elems.length ∧
        MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
        ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) := by
  subst hσ
  exact (regroupSkipO_match_iff_laws hκ).1
    ((regroupBoundedO_query_exact r hw B ix hz).1 env henv a ha)

end Semper.EMatch.Flatten
