import SemperProofs.EMatch.Flatten.RegroupBoundsDefs
import SemperProofs.EMatch.Flatten.RegroupSkip
import SemperProofs.EMatch.Flatten.RegroupNested

/-!
# `:flatten`: the engine's regrouping bounds, proved

The bounded loop (`RegroupBoundsDefs.lean`) against the loop without bounds
(`RegroupSkipDefs.lean`):

* the run without bounds (`Bounds.none`) never stops, and its loop state is
  `SkipSt.run`'s when no fit overflows the width (`regroupBounded_none_st`);
* **the stop is the bounds' crossing**: the run with bounds `B` stops iff the
  run without bounds ends with a counter past `B` (`regroupBounded_halt_iff`).
  Every counter only grows and the bounded run is the unbounded one until it
  stops, so where the crossing happens does not matter;
* **exactness**: a run that does not stop, with no overflow, ends with
  `regroupSkipG`'s records (`regroupBounded_exact`);
* **soundness under truncation**: every record of a run that stopped is a
  record of the run without bounds (`regroupBounded_sub`), and with no
  overflow of `regroupSkipG` (`regroupBounded_sub_skip`); every record of
  any run, overflow included, is reachable (`regroupBounded_reach`);
* at the level of a query (`runB`): every binding the bounded plan emits
  satisfies every atom (`regroupBounded_plan_sound`), and when the query's
  three counters are zero the plan emits exactly the bindings of
  `Enumerator.regroupSkipCap` (`runB_ge`, `regroupBounded_query_exact`), so
  the matches are those of `regroupSkip_match_iff`
  (`regroupBounded_match_exact`). An atom with no item regroups when the
  laws can drop a class (`canDrop`): only then may a regrouped record need
  no class (`mem_base_of_reach`).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch
open Binding (Extends)

/-! ## Counters -/

theorem pastB_mono {b : Option Nat} {x y : Nat} (h : x ≤ y) (hx : pastB b x = true) :
    pastB b y = true := by
  cases b with
  | none => simp [pastB] at hx
  | some b => simp only [pastB, decide_eq_true_eq] at hx ⊢; omega

theorem pastB_max {b : Option Nat} {x y : Nat} :
    pastB b (max x y) = (pastB b x || pastB b y) := by
  cases b with
  | none => rfl
  | some b => simp [pastB, lt_max_iff]

@[simp] theorem pastB_none (x : Nat) : pastB Option.none x = false := rfl

@[simp] theorem Bounds.none_views : Bounds.none.views = Option.none := rfl
@[simp] theorem Bounds.none_work : Bounds.none.work = Option.none := rfl
@[simp] theorem Bounds.none_elems : Bounds.none.elems = Option.none := rfl

theorem pastB_zero (b : Option Nat) : pastB b 0 = false := by
  cases b <;> simp [pastB]

/-- Some counter is past a bound. -/
def BSt.exc (B : Bounds) (b : BSt) : Prop :=
  pastB B.views b.views = true ∨ pastB B.work b.work = true ∨ pastB B.elems b.peak = true

/-- What a step of the run without bounds does: it does not stop, its
counters and records only grow. -/
structure Grow (b b' : BSt) : Prop where
  halt : b'.halt = b.halt
  views : b.views ≤ b'.views
  work : b.work ≤ b'.work
  peak : b.peak ≤ b'.peak
  ovf : b.ovf ≤ b'.ovf
  mono : Mono b.st b'.st

theorem Grow.refl (b : BSt) : Grow b b :=
  ⟨rfl, le_refl _, le_refl _, le_refl _, le_refl _, Mono.refl _⟩

theorem Grow.trans {a b c : BSt} (h₁ : Grow a b) (h₂ : Grow b c) : Grow a c :=
  ⟨h₂.halt.trans h₁.halt, le_trans h₁.views h₂.views, le_trans h₁.work h₂.work,
    le_trans h₁.peak h₂.peak, le_trans h₁.ovf h₂.ovf, h₁.mono.trans h₂.mono⟩

theorem Grow.exc {B : Bounds} {b b' : BSt} (h : Grow b b') (he : b.exc B) : b'.exc B := by
  rcases he with h1 | h1 | h1
  · exact Or.inl (pastB_mono h.views h1)
  · exact Or.inr (Or.inl (pastB_mono h.work h1))
  · exact Or.inr (Or.inr (pastB_mono h.peak h1))

/-- Why a run stopped, read on the run without bounds: a truncation has a
regrouping counter past its bound, `OVER_BOUND` the element count. -/
def HaltOK (B : Bounds) : Option Halt → BSt → Prop
  | some .truncated, u => pastB B.views u.views = true ∨ pastB B.work u.work = true
  | some .overBound, u => pastB B.elems u.peak = true
  | Option.none, _ => False

theorem HaltOK.isSome {B : Bounds} {h : Option Halt} {u : BSt} (hh : HaltOK B h u) :
    h.isSome = true := by
  cases h with
  | none => exact hh.elim
  | some _ => rfl

theorem HaltOK.exc {B : Bounds} {h : Option Halt} {u : BSt} (hh : HaltOK B h u) : u.exc B := by
  match h, hh with
  | some .truncated, Or.inl hv => exact Or.inl hv
  | some .truncated, Or.inr hw => exact Or.inr (Or.inl hw)
  | some .overBound, hp => exact Or.inr (Or.inr hp)

theorem HaltOK.grow {B : Bounds} {h : Option Halt} {u u' : BSt} (hh : HaltOK B h u)
    (g : Grow u u') : HaltOK B h u' := by
  match h, hh with
  | some .truncated, Or.inl hv => exact Or.inl (pastB_mono g.views hv)
  | some .truncated, Or.inr hw => exact Or.inr (pastB_mono g.work hw)
  | some .overBound, hp => exact pastB_mono g.peak hp

/-- A step with bounds `B` (`fB`) against the same step without bounds
(`fN`): on a stopped state the bounded step does nothing; the unbounded one
grows; from a running state within the bounds, either both give the same
state, within the bounds, or the bounded one stops, the unbounded one ends
past a bound, and the bounded records are among the unbounded ones. -/
structure StepR (B : Bounds) (fB fN : BSt → BSt) : Prop where
  stop : ∀ b, b.halt.isSome = true → fB b = b
  grow : ∀ b, b.halt = Option.none → Grow b (fN b)
  sim : ∀ b, b.halt = Option.none → ¬b.exc B →
    (fB b = fN b ∧ ¬(fN b).exc B) ∨
      (HaltOK B (fB b).halt (fN b) ∧ Mono (fB b).st (fN b).st)

theorem StepR.id (B : Bounds) : StepR B (fun b => b) (fun b => b) :=
  ⟨fun _ _ => rfl, fun b _ => Grow.refl b, fun _ _ he => Or.inl ⟨rfl, he⟩⟩

theorem StepR.comp {B : Bounds} {f₁ g₁ f₂ g₂ : BSt → BSt} (h₁ : StepR B f₁ g₁)
    (h₂ : StepR B f₂ g₂) : StepR B (fun b => f₂ (f₁ b)) (fun b => g₂ (g₁ b)) := by
  refine ⟨fun b hb => by rw [h₁.stop b hb, h₂.stop b hb], fun b hb => ?_, fun b hb he => ?_⟩
  · have g1 := h₁.grow b hb
    exact g1.trans (h₂.grow _ (g1.halt.trans hb))
  · have g1 := h₁.grow b hb
    have hb1 : (g₁ b).halt = Option.none := g1.halt.trans hb
    rcases h₁.sim b hb he with ⟨he1, hx1⟩ | ⟨hs1, hm1⟩
    · rw [he1]
      exact h₂.sim _ hb1 hx1
    · right
      have g2 := h₂.grow _ hb1
      rw [h₂.stop _ hs1.isSome]
      exact ⟨hs1.grow g2, hm1.trans g2.mono⟩

theorem StepR.foldl {α : Type} {B : Bounds} {fB fN : BSt → α → BSt} :
    ∀ (xs : List α), (∀ x ∈ xs, StepR B (fun b => fB b x) (fun b => fN b x)) →
      StepR B (fun b => xs.foldl fB b) (fun b => xs.foldl fN b)
  | [], _ => StepR.id B
  | x :: xs, h => by
      simp only [List.foldl_cons]
      exact (h x (List.mem_cons_self ..)).comp
        (StepR.foldl xs (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem StepR.ite {B : Bounds} {p : BSt → Prop} [DecidablePred p] {f g f' g' : BSt → BSt}
    (h : StepR B f g) (h' : StepR B f' g') :
    StepR B (fun b => if p b then f b else f' b) (fun b => if p b then g b else g' b) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb he => ?_⟩
  · by_cases hp : p b
    · simp only [hp, ↓reduceIte]; exact h.stop b hb
    · simp only [hp, ↓reduceIte]; exact h'.stop b hb
  · by_cases hp : p b
    · simp only [hp, ↓reduceIte]; exact h.grow b hb
    · simp only [hp, ↓reduceIte]; exact h'.grow b hb
  · by_cases hp : p b
    · simp only [hp, ↓reduceIte]; exact h.sim b hb he
    · simp only [hp, ↓reduceIte]; exact h'.sim b hb he

/-- The run without bounds against the loop without counters: a step keeps
the loop state of `f` when no fit overflows in it. -/
def ProjR (fN : BSt → BSt) (f : SkipSt → SkipSt) : Prop :=
  ∀ b, b.halt = Option.none → (fN b).ovf = b.ovf → (fN b).st = f b.st

theorem ProjR.comp {g₁ g₂ : BSt → BSt} {f₁ f₂ : SkipSt → SkipSt}
    (hg₁ : ∀ b, b.halt = Option.none → Grow b (g₁ b))
    (hg₂ : ∀ b, b.halt = Option.none → Grow b (g₂ b))
    (h₁ : ProjR g₁ f₁) (h₂ : ProjR g₂ f₂) :
    ProjR (fun b => g₂ (g₁ b)) (fun s => f₂ (f₁ s)) := by
  intro b hb ho
  have G1 := hg₁ b hb
  have hb1 : (g₁ b).halt = Option.none := G1.halt.trans hb
  have G2 := hg₂ _ hb1
  have ho1 : (g₁ b).ovf = b.ovf := le_antisymm (ho ▸ G2.ovf) G1.ovf
  have ho2 : (g₂ (g₁ b)).ovf = (g₁ b).ovf := ho1 ▸ ho
  show (g₂ (g₁ b)).st = f₂ (f₁ b.st)
  rw [h₂ _ hb1 ho2, h₁ b hb ho1]

theorem ProjR.foldl {α : Type} {fN : BSt → α → BSt} {f : SkipSt → α → SkipSt} :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ b, b.halt = Option.none → Grow b (fN b x)) →
      (∀ x ∈ xs, ProjR (fun b => fN b x) (fun s => f s x)) →
      ProjR (fun b => xs.foldl fN b) (fun s => xs.foldl f s)
  | [], _, _ => fun _ _ _ => rfl
  | x :: xs, hg, h => by
      simp only [List.foldl_cons]
      have hgx : ∀ b, b.halt = Option.none → Grow b (xs.foldl fN b) := by
        intro b hb
        exact foldl_grow xs (fun y hy => hg y (List.mem_cons_of_mem _ hy)) b hb
      exact ProjR.comp (g₁ := fun b => fN b x) (g₂ := fun b => xs.foldl fN b)
        (hg x (List.mem_cons_self ..)) hgx (h x (List.mem_cons_self ..))
        (ProjR.foldl xs (fun y hy => hg y (List.mem_cons_of_mem _ hy))
          (fun y hy => h y (List.mem_cons_of_mem _ hy)))
where
  foldl_grow : ∀ (xs : List α), (∀ x ∈ xs, ∀ b, b.halt = Option.none → Grow b (fN b x)) →
      ∀ b, b.halt = Option.none → Grow b (xs.foldl fN b)
    | [], _, b, _ => Grow.refl b
    | x :: xs, hg, b, hb => by
        simp only [List.foldl_cons]
        have G := hg x (List.mem_cons_self ..) b hb
        exact G.trans (foldl_grow xs (fun y hy => hg y (List.mem_cons_of_mem _ hy)) _
          (G.halt.trans hb))

/-- `StepR` on running states only: what a step does under its guard. -/
structure RunR (B : Bounds) (fB fN : BSt → BSt) : Prop where
  grow : ∀ b, b.halt = Option.none → Grow b (fN b)
  sim : ∀ b, b.halt = Option.none → ¬b.exc B →
    (fB b = fN b ∧ ¬(fN b).exc B) ∨
      (HaltOK B (fB b).halt (fN b) ∧ Mono (fB b).st (fN b).st)

theorem StepR.run {B : Bounds} {fB fN : BSt → BSt} (h : StepR B fB fN) : RunR B fB fN :=
  ⟨h.grow, h.sim⟩

/-- A step guarded by the stop flag. -/
theorem RunR.guard {B : Bounds} {fB fN : BSt → BSt} (h : RunR B fB fN) :
    StepR B (fun b => if b.halt.isSome then b else fB b)
      (fun b => if b.halt.isSome then b else fN b) := by
  refine ⟨fun b hb => by simp [hb], fun b hb => ?_, fun b hb he => ?_⟩
  · simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; exact h.grow b hb
  · simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; exact h.sim b hb he

theorem RunR.comp {B : Bounds} {f₁ g₁ f₂ g₂ : BSt → BSt} (h₁ : RunR B f₁ g₁)
    (h₂ : StepR B f₂ g₂) : RunR B (fun b => f₂ (f₁ b)) (fun b => g₂ (g₁ b)) := by
  refine ⟨fun b hb => ?_, fun b hb he => ?_⟩
  · have g1 := h₁.grow b hb
    exact g1.trans (h₂.grow _ (g1.halt.trans hb))
  · have g1 := h₁.grow b hb
    have hb1 : (g₁ b).halt = Option.none := g1.halt.trans hb
    rcases h₁.sim b hb he with ⟨he1, hx1⟩ | ⟨hs1, hm1⟩
    · rw [he1]
      exact h₂.sim _ hb1 hx1
    · right
      have g2 := h₂.grow _ hb1
      rw [h₂.stop _ hs1.isSome]
      exact ⟨hs1.grow g2, hm1.trans g2.mono⟩

theorem RunR.ite {B : Bounds} {p : BSt → Prop} [DecidablePred p] {f g f' g' : BSt → BSt}
    (h : RunR B f g) (h' : RunR B f' g') :
    RunR B (fun b => if p b then f b else f' b) (fun b => if p b then g b else g' b) := by
  refine ⟨fun b hb => ?_, fun b hb he => ?_⟩
  · by_cases hp : p b
    · simp only [hp, ↓reduceIte]; exact h.grow b hb
    · simp only [hp, ↓reduceIte]; exact h'.grow b hb
  · by_cases hp : p b
    · simp only [hp, ↓reduceIte]; exact h.sim b hb he
    · simp only [hp, ↓reduceIte]; exact h'.sim b hb he

/-- A step that reads the state it is applied to. -/
theorem RunR.diag {B : Bounds} {F G : BSt → BSt → BSt} (h : ∀ b₀, RunR B (F b₀) (G b₀)) :
    RunR B (fun b => F b b) (fun b => G b b) :=
  ⟨fun b hb => (h b).grow b hb, fun b hb he => (h b).sim b hb he⟩

theorem RunR.id (B : Bounds) : RunR B (fun b => b) (fun b => b) := (StepR.id B).run

/-- A counter increment and its check (`work`): past the bound the bounded
step stops, otherwise both continue with `F`. -/
theorem RunR.checkWork {B : Bounds} {n : Nat} {FB FN : BSt → BSt} (hF : StepR B FB FN) :
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

/-! ## The steps -/

theorem addRec_stepR (B : Bounds) (t : View) (d : RecR) :
    StepR B (fun b => b.addRec B t d) (fun b => b.addRec Bounds.none t d) := by
  refine ⟨fun b hb => by simp [BSt.addRec, hb], fun b hb => ?_, fun b hb he => ?_⟩
  · simp only [BSt.addRec, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none,
      pastB_none]
    split
    · exact Grow.refl b
    · exact ⟨hb.symm, by simp, le_refl _, le_max_left _ _, le_refl _, (addRec_frame t b.st d).2.2.2⟩
  · have hm := (addRec_frame t b.st d).2.2.2
    simp only [BSt.exc, not_or, Bool.not_eq_true] at he
    obtain ⟨hv, hw, hp⟩ := he
    simp only [BSt.addRec, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none,
      pastB_none]
    split
    · exact Or.inl ⟨rfl, by simp [BSt.exc, hv, hw, hp]⟩
    · split
      · rename_i h1 h2
        exact Or.inr ⟨Or.inl h2, hm⟩
      · split
        · rename_i h1 h2 h3
          exact Or.inr ⟨by simp [HaltOK, pastB_max, h3], hm⟩
        · rename_i h1 h2 h3
          refine Or.inl ⟨rfl, ?_⟩
          simp only [BSt.exc, pastB_max, not_or, Bool.not_eq_true, Bool.or_eq_false_iff]
          exact ⟨Bool.of_not_eq_true h2, hw, hp, Bool.of_not_eq_true h3⟩

theorem addRec_projR (t : View) (d : RecR) :
    ProjR (fun b => b.addRec Bounds.none t d) (fun s => s.addRec t d) := by
  intro b hb _
  simp only [BSt.addRec, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none,
    pastB_none]
  unfold SkipSt.addRec
  split <;> rfl

theorem enterTarget_stepR (B : Bounds) (t : View) :
    StepR B (fun b => b.enterTarget B t) (fun b => b.enterTarget Bounds.none t) := by
  have hm : ∀ st : SkipSt, Mono st { st with order := st.order ++ [t] } :=
    fun st => ⟨fun _ _ h => h, fun _ h => List.mem_append_left _ h⟩
  refine ⟨fun b hb => by simp [BSt.enterTarget, hb], fun b hb => ?_, fun b hb he => ?_⟩
  · simp only [BSt.enterTarget, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      Bounds.none, pastB_none]
    split
    · exact Grow.refl b
    · exact ⟨by simp [hb], le_refl _, le_refl _, le_max_left _ _, le_refl _, hm _⟩
  · simp only [BSt.exc, not_or, Bool.not_eq_true] at he
    obtain ⟨hv, hw, hp⟩ := he
    simp only [BSt.enterTarget, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      Bounds.none, pastB_none]
    split
    · exact Or.inl ⟨rfl, by simp [BSt.exc, hv, hw, hp]⟩
    · split
      · rename_i h1 h2
        exact Or.inr ⟨by simp [HaltOK, pastB_max, h2], hm _⟩
      · rename_i h1 h2
        refine Or.inl ⟨rfl, ?_⟩
        simp only [BSt.exc, pastB_max, not_or, Bool.not_eq_true, Bool.or_eq_false_iff]
        exact ⟨hv, hw, hp, Bool.of_not_eq_true h2⟩

theorem addTarget_stepR (B : Bounds) (t : View) (ds : List RecR) :
    StepR B (fun b => b.addTarget B t ds) (fun b => b.addTarget Bounds.none t ds) := by
  have hrest := (RunR.ite (p := fun b => (b.st.recs t).any RecR.uncond = true) (RunR.id B)
    (StepR.foldl ds (fun d _ => addRec_stepR B t d)).run).guard
  exact (RunR.ite (p := fun b => b.st.done t = true) (RunR.id B)
    ((enterTarget_stepR B t).run.comp hrest)).guard

theorem fitStep_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (w : View)
    (gg : C × List (C × Nat)) (raw : List (C × Nat)) :
    StepR B (fun b => BSt.fitStep B ix ctx laws w gg b raw)
      (fun b => BSt.fitStep Bounds.none ix ctx laws w gg b raw) := by
  have hw : RunR B (fun b => { b with ovf := b.ovf + 1 }) (fun b => { b with ovf := b.ovf + 1 }) :=
    ⟨fun b hb => ⟨rfl, le_refl _, le_refl _, le_refl _, Nat.le_add_right _ _, Mono.refl _⟩,
      fun b _ he => Or.inl ⟨rfl, by simpa [BSt.exc] using he⟩⟩
  have hm : RunR B (fun b => match normalize ctx.κ laws raw with
      | .node t => b.addTarget B t ((srcRecs (b.st.recs w)).map
          (deriveRec t gg.1 (gg.2.map Prod.fst)))
      | _ => b)
      (fun b => match normalize ctx.κ laws raw with
      | .node t => b.addTarget Bounds.none t ((srcRecs (b.st.recs w)).map
          (deriveRec t gg.1 (gg.2.map Prod.fst)))
      | _ => b) := by
    generalize normalize ctx.κ laws raw = nr
    cases nr with
    | node t =>
        exact RunR.diag (F := fun b₀ b => b.addTarget B t ((srcRecs (b₀.st.recs w)).map
          (deriveRec t gg.1 (gg.2.map Prod.fst))))
          (G := fun b₀ b => b.addTarget Bounds.none t ((srcRecs (b₀.st.recs w)).map
          (deriveRec t gg.1 (gg.2.map Prod.fst))))
          (fun b₀ => (addTarget_stepR B t _).run)
    | _ => exact RunR.id B
  exact (RunR.ite (p := fun _ => ix.wide laws raw = true) hw hm).guard

theorem groupStep_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws) (w : View)
    (gg : C × List (C × Nat)) :
    StepR B (fun b => BSt.groupStep B ix ctx dir laws w b gg)
      (fun b => BSt.groupStep Bounds.none ix ctx dir laws w b gg) :=
  (RunR.ite (p := fun _ => (!isCand w gg) = true) (RunR.id B)
    (RunR.checkWork (StepR.foldl _ (fun raw _ => fitStep_stepR B ix ctx laws w gg raw)))).guard

theorem regroupView_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) (w : View) :
    StepR B (BSt.regroupView B ix ctx dir laws gs w) (BSt.regroupView Bounds.none ix ctx dir laws gs w) :=
  (RunR.checkWork (StepR.foldl gs (fun gg _ => groupStep_stepR B ix ctx dir laws w gg))).guard

theorem mark_runR (B : Bounds) (w : View) : RunR B (fun b => b.mark w) (fun b => b.mark w) :=
  ⟨fun b _ => ⟨rfl, le_refl _, le_refl _, le_refl _, le_refl _, ⟨fun _ _ h => h, fun _ h => h⟩⟩,
    fun b _ he => Or.inl ⟨rfl, he⟩⟩

theorem run_stepR (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) :
    ∀ n, StepR B (BSt.run B ix ctx dir laws gs n) (BSt.run Bounds.none ix ctx dir laws gs n)
  | 0 => StepR.id B
  | n + 1 => by
      have h := (RunR.diag
        (F := fun b₀ b => match b₀.st.next with
          | Option.none => b
          | some w => BSt.run B ix ctx dir laws gs n (BSt.regroupView B ix ctx dir laws gs w (b.mark w)))
        (G := fun b₀ b => match b₀.st.next with
          | Option.none => b
          | some w => BSt.run Bounds.none ix ctx dir laws gs n
              (BSt.regroupView Bounds.none ix ctx dir laws gs w (b.mark w)))
        (fun b₀ => by
          cases b₀.st.next with
          | none => exact RunR.id B
          | some w =>
              exact (mark_runR B w).comp ((regroupView_stepR B ix ctx dir laws gs w).comp
                (run_stepR B ix ctx dir laws gs n)))).guard
      have e : ∀ B' : Bounds, BSt.run B' ix ctx dir laws gs (n + 1) = fun b =>
          if b.halt.isSome then b else match b.st.next with
          | Option.none => b
          | some w => BSt.run B' ix ctx dir laws gs n
              (BSt.regroupView B' ix ctx dir laws gs w (b.mark w)) := by
        intro B'; funext b; rfl
      rw [e B, e Bounds.none]
      exact h

/-! ## The run without bounds is the loop -/

theorem isCand_of_fitsR {κ : FlatKind} {dir : Dir} {w : View} {g : C} {grp : List (C × Nat)}
    {raw : List (C × Nat)} (h : raw ∈ fitsR κ dir w g grp) : isCand w (g, grp) = true := by
  have key : ∀ c, c ∈ grp.map Prod.fst → c ∈ w.map Prod.fst → isCand w (g, grp) = true := by
    intro c hc hw
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    exact List.any_eq_true.2 ⟨e, he, decide_eq_true hw⟩
  unfold fitsR at h
  split at h
  · simp at h
  · split at h
    · simp only at h
      split at h
      · simp at h
      · rename_i hk
        obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 h
        split at hp
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨e, he⟩ : ∃ e, e ∈ grp := List.exists_mem_of_ne_nil _
            (fun h0 => by simp [h0] at hk)
          have h1 : e.1 ∈ grp.map Prod.fst := List.mem_map_of_mem he
          refine key e.1 h1 ?_
          rw [← hc.2] at h1
          obtain ⟨x, hx, hxe⟩ := List.mem_map.1 h1
          exact hxe ▸ List.mem_map_of_mem (List.mem_of_mem_drop (List.mem_of_mem_take hx))
        · simp at hp
    all_goals
      simp only at h
      split at h
      · simp at h
      · rename_i htwo
        split at h
        · rename_i v hv
          generalize hn : groupNorm _ grp = norm at hv htwo
          cases norm with
          | nil => simp at htwo
          | cons e rest =>
              unfold subEntries at hv
              split at hv
              · rename_i x hf
                have hcw : e.1 ∈ w.map Prod.fst := by
                  have := List.mem_of_find?_eq_some hf
                  have he := List.find?_some hf
                  simp only [decide_eq_true_eq] at he
                  exact he ▸ List.mem_map_of_mem this
                refine key e.1 ?_ hcw
                have hmem : e ∈ groupNorm _ grp := hn ▸ List.mem_cons_self ..
                unfold groupNorm coalesce dedupAci at hmem
                split at hmem
                · have := mem_entries_fst.1 (List.mem_map_of_mem (f := Prod.fst) hmem)
                  obtain ⟨e', he', he'e, -⟩ := mem_ofEntries.1 this
                  exact he'e ▸ List.mem_map_of_mem he'
                · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hmem
                  simpa using hc
              · simp at hv
        · simp at h

theorem fitsR_nil_of_not_cand {κ : FlatKind} {dir : Dir} {w : View} {gg : C × List (C × Nat)}
    (h : isCand w gg = false) : fitsR κ dir w gg.1 gg.2 = [] := by
  cases hf : fitsR κ dir w gg.1 gg.2 with
  | nil => rfl
  | cons raw _ =>
      have := isCand_of_fitsR (hf ▸ List.mem_cons_self .. : raw ∈ fitsR κ dir w gg.1 gg.2)
      rw [h] at this; simp at this

theorem addTarget_projR (t : View) (ds : List RecR) :
    ProjR (fun b => b.addTarget Bounds.none t ds) (fun s => s.addTarget t ds) := by
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
  have e : b.addTarget Bounds.none t ds = if b.st.done t then b else
      if (b₁.st.recs t).any RecR.uncond then b₁ else ds.foldl (BSt.addRec Bounds.none t) b₁ := by
    rw [hb₁] at hh1
    simp only [BSt.addTarget, hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hh1, hb₁]
  rw [e] at ho ⊢
  unfold SkipSt.addTarget
  by_cases hd : b.st.done t = true
  · simp [hd]
  · simp only [hd, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    rw [← hst1]
    by_cases hu : (b₁.st.recs t).any RecR.uncond = true
    · simp [hu]
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at ho ⊢
      have ho1 : b₁.ovf = b.ovf := le_antisymm (ho ▸ hgF.ovf) hgE.ovf
      exact hfold b₁ hh1 (ho.trans ho1.symm)

theorem fitStep_projR (ix : Ix) (ctx : Ctx) (laws : Laws) (w : View)
    (gg : C × List (C × Nat)) (raw : List (C × Nat)) :
    ProjR (fun b => BSt.fitStep Bounds.none ix ctx laws w gg b raw)
      (fun s => SkipSt.fitStep ctx laws w gg s raw) := by
  intro b hb ho
  beta_reduce at ho ⊢
  unfold BSt.fitStep at ho ⊢
  unfold SkipSt.fitStep
  simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ho ⊢
  by_cases hw : ix.wide laws raw = true
  · simp [hw] at ho
  · simp only [hw, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    revert ho
    cases normalize ctx.κ laws raw with
    | node t => exact fun ho => addTarget_projR t _ b hb ho
    | _ => exact fun _ => rfl

theorem groupStep_projR (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws) (w : View)
    (gg : C × List (C × Nat)) :
    ProjR (fun b => BSt.groupStep Bounds.none ix ctx dir laws w b gg)
      (fun s => SkipSt.groupStep ctx dir laws w s gg) := by
  intro b hb ho
  beta_reduce at ho ⊢
  unfold BSt.groupStep at ho ⊢
  unfold SkipSt.groupStep
  simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none_work, pastB_none]
    at ho ⊢
  by_cases hc : isCand w gg = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    exact ProjR.foldl (fN := BSt.fitStep Bounds.none ix ctx laws w gg)
      (f := SkipSt.fitStep ctx laws w gg) _
      (fun raw _ => (fitStep_stepR Bounds.none ix ctx laws w gg raw).grow)
      (fun raw _ => fitStep_projR ix ctx laws w gg raw)
      ⟨b.st, b.views, b.work + gg.2.length, b.elems, b.gelems, b.peak, b.ovf, Option.none⟩ rfl ho
  · rw [fitsR_nil_of_not_cand (Bool.of_not_eq_true hc)]
    simp [Bool.of_not_eq_true hc]

theorem regroupView_projR (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) (w : View) :
    ProjR (BSt.regroupView Bounds.none ix ctx dir laws gs w)
      (SkipSt.regroupView ctx dir laws gs w) := by
  intro b hb ho
  unfold BSt.regroupView at ho ⊢
  unfold SkipSt.regroupView
  simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bounds.none_work, pastB_none]
    at ho ⊢
  exact ProjR.foldl (fN := BSt.groupStep Bounds.none ix ctx dir laws w)
    (f := SkipSt.groupStep ctx dir laws w) gs
    (fun gg _ => (groupStep_stepR Bounds.none ix ctx dir laws w gg).grow)
    (fun gg _ => groupStep_projR ix ctx dir laws w gg)
    ⟨b.st, b.views, b.work + useWork ix w, b.elems, b.gelems, b.peak, b.ovf, Option.none⟩ rfl ho

theorem run_projR (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) :
    ∀ n, ProjR (BSt.run Bounds.none ix ctx dir laws gs n) (SkipSt.run ctx dir laws gs n)
  | 0 => fun _ _ _ => rfl
  | n + 1 => by
      intro b hb ho
      unfold BSt.run at ho ⊢
      unfold SkipSt.run
      simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ho ⊢
      revert ho
      cases b.st.next with
      | none => exact fun _ => rfl
      | some w =>
          intro ho
          have hm : (b.mark w).halt = Option.none := hb
          have G1 := (regroupView_stepR Bounds.none ix ctx dir laws gs w).grow _ hm
          have h1 : (BSt.regroupView Bounds.none ix ctx dir laws gs w (b.mark w)).halt =
              Option.none := G1.halt.trans hm
          have G2 := (run_stepR Bounds.none ix ctx dir laws gs n).grow _ h1
          have ho1 : (BSt.regroupView Bounds.none ix ctx dir laws gs w (b.mark w)).ovf = b.ovf :=
            le_antisymm (ho ▸ G2.ovf) G1.ovf
          rw [run_projR ix ctx dir laws gs n _ h1 (ho.trans ho1.symm),
            regroupView_projR ix ctx dir laws gs w _ hm ho1]
          rfl

/-! ## The bounded run -/

section Run

variable (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
  (gs : List (C × List (C × Nat))) (base : List RecR)

theorem init_not_exc : ¬(BSt.init base).exc B := by
  simp [BSt.exc, BSt.init, pastB_zero]

/-- **The bounded run against the run without bounds**: the latter never
stops; the former is the latter, within the bounds, or stopped with the
latter past the bound it stopped at, its records among the latter's. -/
theorem regroupBounded_cases :
    (regroupBoundedG Bounds.none ix ctx dir laws gs base).halt = Option.none ∧
      ((regroupBoundedG B ix ctx dir laws gs base = regroupBoundedG Bounds.none ix ctx dir laws gs base ∧
          ¬(regroupBoundedG Bounds.none ix ctx dir laws gs base).exc B) ∨
        (HaltOK B (regroupBoundedG B ix ctx dir laws gs base).halt
            (regroupBoundedG Bounds.none ix ctx dir laws gs base) ∧
          Mono (regroupBoundedG B ix ctx dir laws gs base).st
            (regroupBoundedG Bounds.none ix ctx dir laws gs base).st)) :=
  let h := run_stepR B ix ctx dir laws gs (skipFuel ctx dir laws base)
  ⟨(h.grow _ rfl).halt, h.sim _ rfl (init_not_exc B base)⟩

/-- The run without bounds, when no fit overflows the width, ends with the
loop's records. -/
theorem regroupBounded_none_records
    (ho : (regroupBoundedG Bounds.none ix ctx dir laws gs base).ovf = 0) :
    (regroupBoundedG Bounds.none ix ctx dir laws gs base).st.records =
      regroupSkipG ctx dir laws gs base := by
  unfold regroupBoundedG at ho ⊢
  rw [run_projR ix ctx dir laws gs _ (BSt.init base) rfl ho]
  rfl

/-- **The run stops iff the run without bounds ends past a bound**: the
views counter past `B.views`, the work counter past `B.work`, or an element
count the `MAX_ELEMS` checks read past `B.elems`. The counters only grow, so
the point where the bound is crossed does not matter. -/
theorem regroupBounded_halt_iff :
    (regroupBoundedG B ix ctx dir laws gs base).halt.isSome = true ↔
      (regroupBoundedG Bounds.none ix ctx dir laws gs base).exc B := by
  obtain ⟨hu, h | ⟨hh, -⟩⟩ := regroupBounded_cases B ix ctx dir laws gs base
  · rw [h.1, hu]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact h.2
  · exact ⟨fun _ => hh.exc, fun _ => hh.isSome⟩

/-- **Which bound**: a truncation has a regrouping counter of the run
without bounds past its bound, `OVER_BOUND` its element count. -/
theorem regroupBounded_halt_ok {h : Halt}
    (hh : (regroupBoundedG B ix ctx dir laws gs base).halt = some h) :
    HaltOK B (some h) (regroupBoundedG Bounds.none ix ctx dir laws gs base) := by
  obtain ⟨hu, he | ⟨hk, -⟩⟩ := regroupBounded_cases B ix ctx dir laws gs base
  · rw [he.1, hu] at hh; cases hh
  · rw [hh] at hk; exact hk

/-- Within the element bound, the run is truncated iff the run without
bounds ends with its views or work counter past its bound. -/
theorem regroupBounded_truncated_iff
    (he : pastB B.elems (regroupBoundedG Bounds.none ix ctx dir laws gs base).peak = false) :
    (regroupBoundedG B ix ctx dir laws gs base).halt = some .truncated ↔
      pastB B.views (regroupBoundedG Bounds.none ix ctx dir laws gs base).views = true ∨
        pastB B.work (regroupBoundedG Bounds.none ix ctx dir laws gs base).work = true := by
  constructor
  · intro hh
    exact regroupBounded_halt_ok B ix ctx dir laws gs base hh
  · intro hp
    have hs := (regroupBounded_halt_iff B ix ctx dir laws gs base).2
      (by rcases hp with hp | hp
          · exact Or.inl hp
          · exact Or.inr (Or.inl hp))
    cases hb : (regroupBoundedG B ix ctx dir laws gs base).halt with
    | none => rw [hb] at hs; simp at hs
    | some h =>
        cases h with
        | truncated => rfl
        | overBound =>
            have := regroupBounded_halt_ok B ix ctx dir laws gs base hb
            simp only [HaltOK] at this
            rw [he] at this; cases this

/-- **Exactness**: a run that does not stop, with no fit past the width,
ends with `regroupSkipG`'s records. -/
theorem regroupBounded_exact
    (hh : (regroupBoundedG B ix ctx dir laws gs base).halt = Option.none)
    (ho : (regroupBoundedG B ix ctx dir laws gs base).ovf = 0) :
    (regroupBoundedG B ix ctx dir laws gs base).st.records = regroupSkipG ctx dir laws gs base := by
  obtain ⟨-, he | ⟨hk, -⟩⟩ := regroupBounded_cases B ix ctx dir laws gs base
  · rw [he.1] at ho ⊢
    exact regroupBounded_none_records ix ctx dir laws gs base ho
  · rw [hh] at hk; exact hk.elim

theorem mem_records_of_mono {st st' : SkipSt} (hm : Mono st st') {r : RecR}
    (h : r ∈ st.records) : r ∈ st'.records := by
  simp only [SkipSt.records, List.mem_flatMap] at h ⊢
  obtain ⟨v, hv, hr⟩ := h
  exact ⟨v, hm.2 v hv, hm.1 v r hr⟩

/-- **Soundness under truncation**: every record of the bounded run is a
record of the run without bounds. -/
theorem regroupBounded_sub {r : RecR}
    (h : r ∈ (regroupBoundedG B ix ctx dir laws gs base).st.records) :
    r ∈ (regroupBoundedG Bounds.none ix ctx dir laws gs base).st.records := by
  obtain ⟨-, he | ⟨-, hm⟩⟩ := regroupBounded_cases B ix ctx dir laws gs base
  · rwa [he.1] at h
  · exact mem_records_of_mono hm h

/-- The same against `regroupSkipG`, when no fit of the run without bounds
overflows the width. -/
theorem regroupBounded_sub_skip
    (ho : (regroupBoundedG Bounds.none ix ctx dir laws gs base).ovf = 0) {r : RecR}
    (h : r ∈ (regroupBoundedG B ix ctx dir laws gs base).st.records) :
    r ∈ regroupSkipG ctx dir laws gs base := by
  rw [← regroupBounded_none_records ix ctx dir laws gs base ho]
  exact regroupBounded_sub B ix ctx dir laws gs base h

end Run

/-! ## Every record of any run is reachable -/

section Reach

variable {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}

/-- Every record is filed under its view and reachable from the walk's. -/
def RInv (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) (b : BSt) : Prop :=
  ∀ w, ∀ r ∈ b.st.recs w, r.1 = w ∧ Reach ctx dir laws base r

theorem addRec_rinv {B : Bounds} {t : View} {b : BSt} {d : RecR}
    (h : RInv ctx dir laws base b) (hd : d.1 = t ∧ Reach ctx dir laws base d) :
    RInv ctx dir laws base (b.addRec B t d) := by
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

theorem enterTarget_recs {B : Bounds} {t : View} {b : BSt} :
    (b.enterTarget B t).st.recs = b.st.recs := by
  unfold BSt.enterTarget
  split; · rfl
  split; · rfl
  split <;> rfl

theorem addTarget_rinv {B : Bounds} {t : View} {ds : List RecR} {b : BSt}
    (h : RInv ctx dir laws base b) (hds : ∀ d ∈ ds, d.1 = t ∧ Reach ctx dir laws base d) :
    RInv ctx dir laws base (b.addTarget B t ds) := by
  have he : RInv ctx dir laws base (b.enterTarget B t) := by
    intro w r hr; rw [enterTarget_recs] at hr; exact h w r hr
  unfold BSt.addTarget
  split; · exact h
  split; · exact h
  dsimp only
  split; · exact he
  split; · exact he
  exact foldl_induct (BSt.addRec B t) (RInv ctx dir laws base) ds _ he
    (fun b d hd hb => addRec_rinv hb (hds d hd))

theorem fitStep_rinv {B : Bounds} {ix : Ix} {w : View} {gg : C × List (C × Nat)}
    (hgg : gg ∈ groupsOf ctx) {raw : List (C × Nat)} (hraw : raw ∈ fitsR ctx.κ dir w gg.1 gg.2)
    {b : BSt} (h : RInv ctx dir laws base b) :
    RInv ctx dir laws base (BSt.fitStep B ix ctx laws w gg b raw) := by
  unfold BSt.fitStep
  split; · exact h
  split; · exact h
  split
  · rename_i t hn
    refine addTarget_rinv h (fun d hd => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
    have hr' : r ∈ b.st.recs w := by
      unfold srcRecs at hr
      split at hr
      · rename_i u hu
        rw [List.mem_singleton] at hr; subst hr
        exact List.mem_of_find?_eq_some hu
      · exact hr
    obtain ⟨hrw, hreach⟩ := h w r hr'
    refine ⟨rfl, reach_step hreach ?_⟩
    exact deriveRec_mem (g := gg.1) (grp := gg.2) hgg (by rw [hrw]; exact hraw) hn
  · exact h

theorem groupStep_rinv {B : Bounds} {ix : Ix} {w : View} {gg : C × List (C × Nat)}
    (hgg : gg ∈ groupsOf ctx) {b : BSt} (h : RInv ctx dir laws base b) :
    RInv ctx dir laws base (BSt.groupStep B ix ctx dir laws w b gg) := by
  unfold BSt.groupStep
  split; · exact h
  split; · exact h
  split; · exact h
  exact foldl_induct (BSt.fitStep B ix ctx laws w gg) (RInv ctx dir laws base) _ _ h
    (fun b raw hraw hb => fitStep_rinv hgg hraw hb)

theorem regroupView_rinv {B : Bounds} {ix : Ix} {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) {w : View} {b : BSt} (h : RInv ctx dir laws base b) :
    RInv ctx dir laws base (BSt.regroupView B ix ctx dir laws gs w b) := by
  unfold BSt.regroupView
  split; · exact h
  split; · exact h
  exact foldl_induct (BSt.groupStep B ix ctx dir laws w) (RInv ctx dir laws base) gs _ h
    (fun b gg hgg hb => groupStep_rinv (hgs gg hgg) hb)

theorem run_rinv {B : Bounds} {ix : Ix} {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) :
    ∀ n (b : BSt), RInv ctx dir laws base b →
      RInv ctx dir laws base (BSt.run B ix ctx dir laws gs n b)
  | 0, _, h => h
  | n + 1, b, h => by
      unfold BSt.run
      split; · exact h
      split
      · exact h
      · exact run_rinv hgs n _ (regroupView_rinv hgs (b := b.mark _) h)

theorem init_rinv (base : List RecR) : RInv ctx dir laws base (BSt.init base) :=
  fun w r hr => ((init_inv (ctx := ctx) (dir := dir) (laws := laws) base).core.sound w r hr)

/-- **Every record of a bounded run is reachable** from the walk's, whatever
the bounds and the overflows: a record of the full enumeration
(`mem_regroupAll_iff_reach`). -/
theorem regroupBounded_reach (B : Bounds) (ix : Ix) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) {r : RecR}
    (h : r ∈ (regroupBoundedG B ix ctx dir laws gs base).st.records) :
    Reach ctx dir laws base r := by
  simp only [SkipSt.records, List.mem_flatMap] at h
  obtain ⟨v, -, hr⟩ := h
  exact (run_rinv hgs _ _ (init_rinv base) v r hr).2

end Reach

/-! ## The takeable set with the engine's cap -/

theorem takeableRCap_down (ctx : Ctx) (σ : Binding) (items : List Var) :
    DownClosed ctx (takeableRCap ctx σ items) := by
  intro a b hk ha
  cases h : items.mapM σ.cls with
  | none => simp [takeableRCap, h]
  | some bound =>
      simp only [takeableRCap, h] at ha ⊢
      split
      · rename_i hcl
        rw [if_pos hcl] at ha
        simp only [decide_eq_true_eq] at ha ⊢
        exact hcl.1 (kidOf_mem_belowStep ha hk)
      · rfl

theorem takenOf_takeableRCap {ctx : Ctx} {σ σ' : Binding} (hext : Extends σ σ')
    {items : List Var} (hb : ∀ x ∈ items, ∃ c, σ'.cls x = some c) :
    ∀ c ∈ takenOf σ' items, takeableRCap ctx σ items c = true := by
  intro c hc
  cases h : items.mapM σ.cls with
  | none => simp [takeableRCap, h]
  | some bound =>
    rw [← takenOf_extends hext items (bound_of_mapM h), takenOf_of_mapM h] at hc
    have hc' := subset_belowIter ctx ((classesOf ctx.G).card + 1) bound hc
    simp only [takeableRCap, h]
    split <;> simp [hc']

/-- **The engine's enumeration with the capped takeable set meets the plan
specification**: past the cap every class is takeable, which prunes less. -/
theorem regroupSkipCap_spec (dir : Sym → Dir) : (Enumerator.regroupSkipCap dir).Spec where
  normal {ctx laws items n w d} h := by
    unfold Enumerator.regroupSkipCap enumerateRSkip at h
    exact normal_enumerateFromRSkip (baseGood_baseRecsR ctx (dir ctx.f) laws n)
      normal_baseRecsR h
  normalP {ctx laws σ items n w d} h := by
    unfold Enumerator.regroupSkipCap enumerateRDSkip at h
    exact normal_enumerateFromRSkip (baseGood_filter (baseGood_baseRecsR ctx (dir ctx.f) laws n) _)
      (fun r hr => normal_baseRecsR r (List.mem_filter.1 hr).1) h
  to_full {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRDSkip (takeableRCap ctx σ items) ctx (dir ctx.f) laws
        items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRDSkip_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroup (takeableRCap_down _ _ _) (takenOf_takeableRCap hext hb)).1 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRSkip ctx (dir ctx.f) laws items.length n ∧ _
    exact enumerateRSkip_iff.2 ⟨d₂, hd₂, hacc₂⟩
  to_pruned {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRSkip ctx (dir ctx.f) laws items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRSkip_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroup (takeableRCap_down _ _ _) (takenOf_takeableRCap hext hb)).2 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRDSkip (takeableRCap ctx σ items) ctx (dir ctx.f) laws
      items.length n ∧ _
    exact enumerateRDSkip_iff.2 ⟨d₂, hd₂, hacc₂⟩

/-- The two enumerations share their full side: an atom holds under one iff
under the other. -/
theorem atomSat_regroupSkipCap_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom} :
    AtomSatG (Enumerator.regroupSkipCap dir) c σ a ↔ AtomSatG (Enumerator.regroupSkip dir) c σ a := by
  unfold AtomSatG Enumerator.regroupSkipCap Enumerator.regroupSkip
  exact Iff.rfl

/-! ## Views of record lists -/

/-- The views of `recs₁` are views of `recs₂`, each with a demand accepting
at least what the first accepts. -/
def ViewLe (recs₁ recs₂ : List RecR) : Prop :=
  ∀ w d, (w, d) ∈ enumerateFromR recs₁ → ∃ d', (w, d') ∈ enumerateFromR recs₂ ∧
    ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true

theorem enumerateFromR_unique {recs : List RecR} {w : List (C × Nat)} {d d' : DemandL}
    (h : (w, d) ∈ enumerateFromR recs) (h' : (w, d') ∈ enumerateFromR recs) : d = d' := by
  unfold enumerateFromR at h h'
  obtain ⟨w₁, -, he⟩ := List.mem_map.1 h
  obtain ⟨w₂, -, he'⟩ := List.mem_map.1 h'
  simp only [Prod.mk.injEq] at he he'
  rw [← he.2, ← he'.2, he.1, he'.1]

theorem enumerateFromR_of_mem {recs : List RecR} {r : RecR} (h : r ∈ recs) :
    ∃ d, (r.1, d) ∈ enumerateFromR recs := by
  unfold enumerateFromR
  exact ⟨_, List.mem_map.2 ⟨r.1, mem_dedupH.2 (List.mem_map_of_mem h), rfl⟩⟩

/-- Every record of `recs₁` covered by one of `recs₂`: the views compare. -/
theorem viewLe_of_cov {recs₁ recs₂ : List RecR} (h : ∀ r ∈ recs₁, ∃ c ∈ recs₂, Cov c r) :
    ViewLe recs₁ recs₂ := by
  intro w d hd
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR hd
  obtain ⟨c, hc, hcov⟩ := h r hr
  obtain ⟨d', hd'⟩ := enumerateFromR_of_mem hc
  rw [hcov.1] at hd'
  refine ⟨d', hd', fun κ taken hacc => ?_⟩
  rw [DemandL.acceptsEB_iff] at hacc ⊢
  obtain ⟨r₁, hr₁, hw₁, hok₁⟩ := acceptsE_enumerateFromR.1 ⟨d, hd, hacc⟩
  obtain ⟨c₁, hc₁, hcov₁⟩ := h r₁ hr₁
  obtain ⟨d'', hd'', hacc''⟩ :=
    (acceptsE_enumerateFromR (κ := κ)).2 ⟨c₁, hc₁, hcov₁.1.trans hw₁, hcov₁.accepts hok₁⟩
  rwa [enumerateFromR_unique hd'' hd'] at hacc''

theorem viewLe_refl (recs : List RecR) : ViewLe recs recs :=
  viewLe_of_cov (fun r hr => ⟨r, hr, Cov.refl r⟩)

theorem viewLe_nil (recs : List RecR) : ViewLe [] recs := by
  intro w d hd
  simp [enumerateFromR, dedupH] at hd

/-! ## One `Flatten` evaluation -/

/-- Under laws that drop no class, a reachable record needing no class is a
walk record: a regrouping needs its group's class, which its view keeps. -/
theorem mem_base_of_reach {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR} {r : RecR}
    (hd : canDrop ctx.κ laws = false) (h : Reach ctx dir laws base r) (hn : r.2.2 = []) :
    r ∈ base := by
  obtain ⟨r₀, h₀, hch⟩ := h
  cases hch with
  | refl => exact h₀
  | @tail a _ _ hs =>
      obtain ⟨g, grp, raw, -, hraw, hnorm, -, he⟩ := mem_regroupRec hs
      have hg : g ∈ r.1.map Prod.fst := by
        by_contra hg
        rw [canDrop_of_gone hraw hnorm hg] at hd
        cases hd
      rw [hn] at he
      have : g ∈ needsAfter g (grp.map Prod.fst) (r.1.map Prod.fst) a.2.2 := by
        unfold needsAfter
        refine List.mem_filter.2 ⟨?_, decide_eq_true hg⟩
        split
        · assumption
        · simp
      rw [← he] at this
      simp at this

/-- The walk's records within any limit are covered by the engine's
regrouping within the limit. -/
theorem cov_skip {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {limit : Nat} {r : RecR} (hr : Reach ctx dir laws base r)
    (hl : r.2.2.length ≤ limit) :
    ∃ c ∈ withinLimit limit (regroupSkipG ctx dir laws (groupsOfEngine ctx) base), Cov c r := by
  obtain ⟨hs, hc⟩ := regroupSkipG_spec (dir := dir) (laws := laws) hb (groupsOfEngine_sub ctx)
    (groupsOfEngine_sup ctx)
  obtain ⟨c, hc', hcov⟩ := hc r hr
  exact ⟨c, mem_withinLimit.2 ⟨hc', le_trans (hcov.length (reach_good hb (hs c hc')).2) hl⟩, hcov⟩

section Eval

variable (B : Bounds) (ix : Ix) (T : C → Bool) (ctx : Ctx) (dir : Dir) (laws : Laws)
  (limit : Nat) (n : Node)

/-- **Soundness of one evaluation**: every view of the bounded enumeration is
a view of the engine's enumeration without bounds, whose demand accepts at
least as much, whatever stopped it. -/
theorem enumerateRDBounded_le :
    ∀ w d, (w, d) ∈ (enumerateRDBounded B ix T ctx dir laws limit n).views →
      ∃ d', (w, d') ∈ enumerateRDSkip T ctx dir laws limit n ∧
        ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true := by
  have hb := baseGood_filter (baseGood_baseRecsR ctx dir laws n) (keepRec ctx.κ T laws)
  unfold enumerateRDBounded enumerateRDSkip regroupAllSkip
  dsimp only
  split
  · refine viewLe_of_cov (fun r hr => cov_skip hb ⟨r, hr, Relation.ReflTransGen.refl⟩ ?_)
    obtain ⟨-, -, -, -, hn⟩ := mem_baseRecsR (List.mem_filter.1 hr).1
    rw [hn]; exact Nat.zero_le _
  · split
    · exact viewLe_nil _
    · refine viewLe_of_cov (fun r hr => ?_)
      obtain ⟨hr, hl⟩ := mem_withinLimit.1 hr
      exact cov_skip hb (regroupBounded_reach B ix (groupsOfEngine_sub ctx) hr) hl

/-- **Exactness of one evaluation**: with no truncation, no skip and no
overflow, the engine's enumeration without bounds has no view the bounded
one lacks, nor a demand accepting more. Without items the engine regroups
only when the laws can drop a class; otherwise a regrouped record needs its
group's class, so no record it skips is within the limit. -/
theorem enumerateRDBounded_ge (h : (enumerateRDBounded B ix T ctx dir laws limit n).counts = 0) :
    ∀ w d, (w, d) ∈ enumerateRDSkip T ctx dir laws limit n →
      ∃ d', (w, d') ∈ (enumerateRDBounded B ix T ctx dir laws limit n).views ∧
        ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true := by
  have hb := baseGood_filter (baseGood_baseRecsR ctx dir laws n) (keepRec ctx.κ T laws)
  revert h
  unfold enumerateRDBounded enumerateRDSkip regroupAllSkip
  dsimp only
  split
  · rename_i hl
    obtain ⟨hl, hd⟩ := hl
    intro _
    subst hl
    refine viewLe_of_cov (fun r hr => ?_)
    obtain ⟨hr, hl⟩ := mem_withinLimit.1 hr
    have hreach := (regroupSkipG_spec (dir := dir) (laws := laws) hb (groupsOfEngine_sub ctx)
      (groupsOfEngine_sup ctx)).1 r hr
    exact ⟨r, mem_base_of_reach hd hreach (List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)),
      Cov.refl r⟩
  · split
    · intro h; simp [BOut.counts] at h; cases h
    · rename_i hov
      intro h
      simp only [BOut.counts] at h
      have hc : ∀ {a b c d e f : Nat}, (⟨a, b, c⟩ : Counts) = ⟨d, e, f⟩ → a = d ∧ c = f :=
        fun h => by cases h; exact ⟨rfl, rfl⟩
      obtain ⟨htr, ho⟩ := hc h
      have hnone : (regroupBoundedG B ix ctx dir laws (groupsOfEngine ctx)
          ((baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws))).halt = Option.none := by
        cases hH : (regroupBoundedG B ix ctx dir laws (groupsOfEngine ctx)
          ((baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws))).halt with
        | none => rfl
        | some x =>
            cases x
            · rw [hH] at htr; simp at htr
            · exact absurd hH hov
      rw [regroupBounded_exact B ix ctx dir laws _ _ hnone ho]
      exact viewLe_refl _

end Eval

/-! ## A query -/

/-- `env'` has the binding of `env` and, in each register `env` fills, the
same view with a demand accepting at least as much. -/
def EnvLe (env env' : EEnv) : Prop :=
  env.σ = env'.σ ∧ ∀ r w d, env.views r = some (w, d) →
    ∃ d', env'.views r = some (w, d') ∧
      ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true

theorem EnvLe.refl (env : EEnv) : EnvLe env env :=
  ⟨rfl, fun _ _ d h => ⟨d, h, fun _ _ h => h⟩⟩

theorem EnvLe.withBinding {env env' : EEnv} (h : EnvLe env env') (σ : Binding) :
    EnvLe (env.withBinding σ) (env'.withBinding σ) :=
  ⟨rfl, h.2⟩

theorem EnvLe.setView {env env' : EEnv} (h : EnvLe env env') (out : Nat) {w : List (C × Nat)}
    {d d' : DemandL} (hd : ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true) :
    EnvLe (env.setView out (w, d)) (env'.setView out (w, d')) := by
  refine ⟨h.1, fun r w₁ d₁ hr => ?_⟩
  by_cases hro : r = out
  · subst hro
    simp only [EEnv.setView, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr ⊢
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨d', ⟨rfl, rfl⟩, hd⟩
  · simp only [EEnv.setView, Function.update_of_ne hro] at hr ⊢
    exact h.2 r w₁ d₁ hr

/-- The views of one evaluation of `E₁` are views of the same evaluation of
`E₂`, with a demand accepting at least as much. -/
def CallLe (E₁ E₂ : Enumerator) (ctx : Ctx) (laws : Laws) (σ : Binding) (items : List Var)
    (n : Node) : Prop :=
  ∀ w d, (w, d) ∈ E₁.pruned ctx laws σ items n → ∃ d', (w, d') ∈ E₂.pruned ctx laws σ items n ∧
    ∀ κ taken, d.acceptsEB κ taken = true → d'.acceptsEB κ taken = true

/-- One step of the plan, with the flatten step's evaluations compared. -/
theorem runEStepG_le {E₁ E₂ : Enumerator} {c : FCtx} {s : EStep} {env env' : EEnv}
    (h : EnvLe env env')
    (hf : ∀ v f κ out items n, s = .flatten v f κ out items → env.σ.nodeOf c.G v = some n →
      CallLe E₁ E₂ (c.ctx f κ) (c.laws f) env.σ items n)
    {x : EEnv} (hx : x ∈ runEStepG E₁ c s env) : ∃ x' ∈ runEStepG E₂ c s env', EnvLe x x' := by
  obtain ⟨hσ, hv⟩ := h
  cases s with
  | base st =>
      simp only [runEStepG, List.mem_map] at hx ⊢
      obtain ⟨σ'', hσ'', rfl⟩ := hx
      exact ⟨_, ⟨σ'', hσ ▸ hσ'', rfl⟩, EnvLe.withBinding ⟨hσ, hv⟩ σ''⟩
  | flatten v f κ out items =>
      simp only [runEStepG] at hx ⊢
      rw [← hσ]
      revert hx
      cases hn : env.σ.nodeOf c.G v with
      | none => simp
      | some n =>
          intro hx
          obtain ⟨⟨w, d⟩, hwd, rfl⟩ := List.mem_map.1 hx
          obtain ⟨d', hd', hacc⟩ := hf v f κ out items n rfl hn w d hwd
          exact ⟨_, List.mem_map_of_mem hd', EnvLe.setView ⟨hσ, hv⟩ out hacc⟩
  | decomposeAC _ elems rest r =>
      simp only [runEStepG] at hx ⊢
      revert hx
      cases hr : env.views r with
      | none => simp
      | some wd =>
          obtain ⟨w, d⟩ := wd
          obtain ⟨d', hr', hacc⟩ := hv r w d hr
          rw [hr', ← hσ]
          intro hx
          obtain ⟨σ'', hσ'', rfl⟩ := List.mem_map.1 hx
          obtain ⟨hm, hk⟩ := List.mem_filter.1 hσ''
          exact ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨hm, hacc _ _ hk⟩),
            EnvLe.withBinding ⟨hσ, hv⟩ σ''⟩
  | decomposeACI _ elems rest r =>
      simp only [runEStepG] at hx ⊢
      revert hx
      cases hr : env.views r with
      | none => simp
      | some wd =>
          obtain ⟨w, d⟩ := wd
          obtain ⟨d', hr', hacc⟩ := hv r w d hr
          rw [hr', ← hσ]
          intro hx
          obtain ⟨σ'', hσ'', rfl⟩ := List.mem_map.1 hx
          obtain ⟨hm, hk⟩ := List.mem_filter.1 hσ''
          exact ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨hm, hacc _ _ hk⟩),
            EnvLe.withBinding ⟨hσ, hv⟩ σ''⟩
  | expandA _ pre elems suf r =>
      simp only [runEStepG] at hx ⊢
      revert hx
      cases hr : env.views r with
      | none => simp
      | some wd =>
          obtain ⟨w, d⟩ := wd
          obtain ⟨d', hr', hacc⟩ := hv r w d hr
          rw [hr', ← hσ]
          intro hx
          obtain ⟨σ'', hσ'', rfl⟩ := List.mem_map.1 hx
          obtain ⟨hm, hk⟩ := List.mem_filter.1 hσ''
          exact ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨hm, hacc _ _ hk⟩),
            EnvLe.withBinding ⟨hσ, hv⟩ σ''⟩

/-- A plan with every evaluation compared. -/
theorem runEG_le {E₁ E₂ : Enumerator} {c : FCtx}
    (hE : ∀ ctx laws σ items n, CallLe E₁ E₂ ctx laws σ items n) :
    ∀ (ss : List EStep) (env env' : EEnv), EnvLe env env' → ∀ x ∈ runEG E₁ c ss env,
      ∃ x' ∈ runEG E₂ c ss env', EnvLe x x'
  | [], env, env', h, x, hx => by
      simp only [runEG, List.mem_singleton] at hx ⊢
      subst hx
      exact ⟨env', rfl, h⟩
  | s :: ss, env, env', h, x, hx => by
      simp only [runEG, List.mem_flatMap] at hx ⊢
      obtain ⟨y, hy, hx⟩ := hx
      obtain ⟨y', hy', hyy⟩ := runEStepG_le h (fun _ _ _ _ _ _ _ _ => hE _ _ _ _ _) hy
      obtain ⟨x', hx', hxx⟩ := runEG_le hE ss y y' hyy x hx
      exact ⟨x', ⟨y', hy', hx'⟩, hxx⟩

/-! ### The counters of a query -/

theorem Counts.zero_def : (0 : Counts) = ⟨0, 0, 0⟩ := rfl

theorem Counts.add_eq_zero {a b : Counts} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  obtain ⟨b₁, b₂, b₃⟩ := b
  show Counts.add _ _ = _ ↔ _
  simp only [Counts.add, Counts.zero_def, Counts.mk.injEq]
  omega

theorem Counts.sum_eq_zero :
    ∀ (l : List Counts), l.foldr (· + ·) 0 = 0 ↔ ∀ x ∈ l, x = 0
  | [] => by simp
  | x :: l => by
      simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
      rw [Counts.add_eq_zero, Counts.sum_eq_zero l]

/-- The environments of `runB` are those of the plan run with the bounded
enumeration. -/
theorem runStepB_fst (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) (s : EStep)
    (env : EEnv) :
    (runStepB B ix dir c s env).1 = runEStepG (Enumerator.regroupBounded B ix dir) c s env := by
  cases s with
  | flatten v f κ out items =>
      simp only [runStepB, runEStepG]
      cases env.σ.nodeOf c.G v <;> rfl
  | _ => rfl

theorem runB_fst (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    ∀ (ss : List EStep) (env : EEnv),
      (runB B ix dir c ss env).1 = runEG (Enumerator.regroupBounded B ix dir) c ss env
  | [], _ => rfl
  | s :: ss, env => by
      simp only [runB, runEG, List.flatMap_map, runStepB_fst]
      congr 1
      funext y
      exact runB_fst B ix dir c ss y

/-- With the counters zero, the plan run with the unbounded enumeration
emits nothing the bounded one does not. -/
theorem runB_ge (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    ∀ (ss : List EStep) (env env' : EEnv), (runB B ix dir c ss env).2 = 0 → EnvLe env' env →
      ∀ x' ∈ runEG (Enumerator.regroupSkipCap dir) c ss env',
        ∃ x ∈ (runB B ix dir c ss env).1, EnvLe x' x
  | [], env, env', _, h, x', hx' => by
      simp only [runEG, List.mem_singleton] at hx'
      subst hx'
      exact ⟨env, List.mem_singleton_self _, h⟩
  | s :: ss, env, env', hz, h, x', hx' => by
      simp only [runB] at hz ⊢
      obtain ⟨hz₁, hz₂⟩ := Counts.add_eq_zero.1 hz
      rw [Counts.sum_eq_zero] at hz₂
      simp only [runEG, List.mem_flatMap] at hx'
      obtain ⟨y', hy', hx'⟩ := hx'
      have hf : ∀ v f κ out items n, s = .flatten v f κ out items → env'.σ.nodeOf c.G v = some n →
          CallLe (Enumerator.regroupSkipCap dir) (Enumerator.regroupBounded B ix dir)
            (c.ctx f κ) (c.laws f) env'.σ items n := by
        rintro v f κ out items n rfl hn
        rw [h.1] at hn ⊢
        have hz₁' := hz₁
        simp only [runStepB, hn] at hz₁'
        exact enumerateRDBounded_ge B ix _ (c.ctx f κ) (dir f) (c.laws f) items.length n hz₁'
      obtain ⟨y, hy, hyy⟩ := runEStepG_le h hf hy'
      rw [← runStepB_fst] at hy
      have hzy : (runB B ix dir c ss y).2 = 0 :=
        hz₂ _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨y, hy, rfl⟩, rfl⟩)
      obtain ⟨x, hx, hxx⟩ := runB_ge B ix dir c ss y y' hzy hyy x' hx'
      exact ⟨x, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨y, hy, rfl⟩, hx⟩, hxx⟩

/-! ### The final theorems -/

/-- **Soundness of the bounded plan**: every binding the plan emits with the
engine's bounds, whatever was truncated, skipped or overflowed, satisfies
every atom under the engine's enumeration without bounds. -/
theorem regroupBounded_plan_sound {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix) {env : EEnv}
    (h : env ∈ (runB B ix dir c (planF as ∅ r) EEnv.empty).1) :
    (∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c env.σ a) ∧
      ClsDom env.σ (planBound as ∅) := by
  rw [runB_fst] at h
  obtain ⟨env', h', hle⟩ := runEG_le (E₁ := Enumerator.regroupBounded B ix dir)
    (E₂ := Enumerator.regroupSkipCap dir)
    (fun ctx laws σ items n => by
      unfold CallLe Enumerator.regroupBounded Enumerator.regroupSkipCap
      exact enumerateRDBounded_le B ix (takeableRCap ctx σ items) ctx (dir ctx.f) laws
        items.length n)
    _ _ _ (EnvLe.refl _) env h
  obtain ⟨hsat, hdom⟩ := flatten_plan_sound_of_spec (regroupSkipCap_spec dir) r hw h'
  rw [hle.1]
  exact ⟨fun a ha => atomSat_regroupSkipCap_iff.1 (hsat a ha), hdom⟩

/-- **Completeness of the bounded plan when the counters are zero**: if the
query ends with `flatten_regroup_truncated`, `flatten_skipped` and
`flatten_overflowed` all zero, every binding satisfying every atom under the
engine's enumeration is extended by an emitted one. -/
theorem regroupBounded_plan_complete {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix)
    (hz : (runB B ix dir c (planF as ∅ r) EEnv.empty).2 = 0) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c σ' a) :
    ∃ env ∈ (runB B ix dir c (planF as ∅ r) EEnv.empty).1, Extends env.σ σ' := by
  obtain ⟨env', h', hext⟩ := flatten_plan_complete_of_spec (regroupSkipCap_spec dir) r hw
    (fun a ha => atomSat_regroupSkipCap_iff.2 (hsat a ha))
  obtain ⟨env, h, hle⟩ := runB_ge B ix dir c _ _ _ hz (EnvLe.refl _) env' h'
  exact ⟨env, h, hle.1 ▸ hext⟩

/-- **The runtime check**: when a query ends with the three counters of its
`Flatten` steps zero (`flatten_regroup_truncated`, `flatten_skipped`,
`flatten_overflowed`, `ematch.rs`), the bindings the bounded plan emits are
exactly those satisfying every atom under the engine's enumeration, which
`regroupSkip_match_iff` characterizes for laws-free operators. -/
theorem regroupBounded_query_exact {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix)
    (hz : (runB B ix dir c (planF as ∅ r) EEnv.empty).2 = 0) :
    (∀ env ∈ (runB B ix dir c (planF as ∅ r) EEnv.empty).1,
        ∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c env.σ a) ∧
      ∀ σ', (∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c σ' a) →
        ∃ env ∈ (runB B ix dir c (planF as ∅ r) EEnv.empty).1, Extends env.σ σ' :=
  ⟨fun _ h => (regroupBounded_plan_sound r hw B ix h).1,
    fun _ hsat => regroupBounded_plan_complete r hw B ix hz hsat⟩

/-- **The runtime check, per atom**: with the counters zero, a binding is
emitted (up to extension) iff every atom holds, an n-ary atom over a
laws-free operator exactly when `regroupSkip_match_iff`'s chain exists. -/
theorem regroupBounded_match_exact {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix)
    (hz : (runB B ix dir c (planF as ∅ r) EEnv.empty).2 = 0) {σ : Binding} {a : RAtom}
    (ha : a ∈ as) {κ : FlatKind} (hκ : a.shape.flatKind = some κ)
    (hlaws : c.laws a.op = Laws.free) {env : EEnv}
    (henv : env ∈ (runB B ix dir c (planF as ∅ r) EEnv.empty).1) (hσ : env.σ = σ) :
    ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
      σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
      ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) Laws.free n, ∃ r,
        RegroupChain (c.ctx a.op κ) (dir a.op) r₀ r ∧ r.2.2.length ≤ a.elems.length ∧
        MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
        ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) := by
  subst hσ
  exact (regroupSkip_match_iff hκ hlaws).1 ((regroupBounded_query_exact r hw B ix hz).1 env henv a ha)

end Semper.EMatch.Flatten
