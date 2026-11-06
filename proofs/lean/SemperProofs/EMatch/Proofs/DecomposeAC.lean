import SemperProofs.EMatch.Lemmas

/-!
# E-matching: AC and ACI decomposition (sketch lemmas 5, 6 and 7)

Proves `decompose_ac_sound'`, `decompose_ac_complete'`,
`decompose_aci_sound'` and `decompose_aci_complete'`.

The soundness statements of `Lemmas.lean` are false as written when the
rest variable is already bound in the input binding: `decomposeAC` and
`decomposeACI` overwrite the rest entry (`Binding.setRest`,
`Binding.setSetRest`), so `Extends σ σ'` fails. Counterexample for
`decompose_ac_sound`: `elems = []`, `rest = some 0`, `m = {1}`,
`σ = Binding.empty.setRest 0 ∅`; the result is `[σ.setRest 0 {1}]` and
`σ.rest 0 = some ∅ ≠ some {1}`. The primed versions add the hypothesis
that the rest variable is unbound in `σ`, which `PlanWF` guarantees for
the compiler's plans (each variable is bound once).

Method: the residual passed to the decomposition is generalized to
`resOf m Z` (the entries of `m` with the classes in `Z` zeroed) and
`resSet s Z` (the sorted elements of `s` without those in `Z`); the
recursion zeroes or erases the taken class, which is `Z ↦ c :: Z`.
-/

namespace Semper.EMatch

open Binding

/-! ## Binding helpers -/

theorem extends_setCls {σ : Binding} {x : Var} {c : C} (h : σ.cls x = none) :
    Extends σ (σ.setCls x c) := by
  refine ⟨?_, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h⟩
  intro x' c' hx'
  have hne : x' ≠ x := by
    rintro rfl
    rw [h] at hx'
    cases hx'
  simp [Binding.setCls, Function.update_of_ne hne, hx']

theorem extends_setRest {σ : Binding} {r : Var} {v : Multiset C}
    (h : σ.rest r = none) : Extends σ (σ.setRest r v) := by
  refine ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, ?_, fun _ _ h => h,
    fun _ _ h => h⟩
  intro r' v' hr'
  have hne : r' ≠ r := by
    rintro rfl
    rw [h] at hr'
    cases hr'
  simp [Binding.setRest, Function.update_of_ne hne, hr']

theorem extends_setSetRest {σ : Binding} {r : Var} {v : Finset C}
    (h : σ.finRest r = none) : Extends σ (σ.setSetRest r v) := by
  refine ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h, ?_⟩
  intro r' v' hr'
  have hne : r' ≠ r := by
    rintro rfl
    rw [h] at hr'
    cases hr'
  simp [Binding.setSetRest, Function.update_of_ne hne, hr']

/-- `multMatches` changes the multiplicity map only. -/
theorem multMatches_fields {σ σ₁ : Binding} {μ : Mult} {m : Nat}
    (h : multMatches σ μ m = some σ₁) :
    σ₁.cls = σ.cls ∧ σ₁.rest = σ.rest ∧ σ₁.finRest = σ.finRest := by
  cases μ with
  | exact k =>
      simp only [multMatches] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rfl, rfl, rfl⟩
      · cases h
  | var k lo hi =>
      simp only [multMatches] at h
      split at h
      · split at h
        · split at h
          · obtain rfl := Option.some.inj h
            exact ⟨rfl, rfl, rfl⟩
          · cases h
        · obtain rfl := Option.some.inj h
          exact ⟨rfl, rfl, rfl⟩
      · cases h

theorem MultOk.mono {σ σ' : Binding} {μ : Mult} {m : Nat} (h : MultOk σ μ m)
    (he : Extends σ σ') : MultOk σ' μ m := by
  cases μ with
  | exact k => exact h
  | var k lo hi => exact ⟨he.2.2.1 k m h.1, h.2.1, h.2.2⟩

/-! ## Residuals of a multiset -/

/-- The entries of `m` with the classes in `Z` zeroed. -/
def resOf (m : Multiset C) (Z : List C) : List (C × Nat) :=
  (m.toFinset.sort (· ≤ ·)).map (fun c => (c, if c ∈ Z then 0 else m.count c))

theorem entries_eq_resOf (m : Multiset C) : Multiset.entries m = resOf m [] := by
  simp [Multiset.entries, resOf]

theorem zeroEntry_resOf (m : Multiset C) (Z : List C) (c : C) :
    zeroEntry c (resOf m Z) = resOf m (c :: Z) := by
  unfold zeroEntry resOf
  rw [List.map_map]
  apply List.map_congr_left
  intro d _
  simp only [Function.comp_apply, List.mem_cons]
  by_cases hdc : d = c
  · subst hdc
    simp
  · simp [hdc]

theorem mem_resOf {m : Multiset C} {Z : List C} {c : C} {k : Nat} :
    (c, k) ∈ resOf m Z ↔ c ∈ m ∧ k = (if c ∈ Z then 0 else m.count c) := by
  simp only [resOf, List.mem_map, Finset.mem_sort, Multiset.mem_toFinset,
    Prod.mk.injEq]
  constructor
  · rintro ⟨d, hd, rfl, rfl⟩
    exact ⟨hd, rfl⟩
  · rintro ⟨hc, rfl⟩
    exact ⟨c, hc, rfl, rfl⟩

theorem find?_resOf {m : Multiset C} {Z : List C} {c : C} (hc : c ∈ m)
    (hZ : c ∉ Z) :
    (resOf m Z).find? (fun e => decide (e.1 = c ∧ e.2 ≠ 0)) =
      some (c, m.count c) := by
  have hcount : m.count c ≠ 0 := by
    rw [Ne, Multiset.count_eq_zero]
    exact fun h => h hc
  have hentry : (c, m.count c) ∈ resOf m Z := mem_resOf.2 ⟨hc, by rw [if_neg hZ]⟩
  obtain ⟨e, he⟩ : ∃ e, (resOf m Z).find? (fun e => decide (e.1 = c ∧ e.2 ≠ 0)) =
      some e := by
    have : ((resOf m Z).find? (fun e => decide (e.1 = c ∧ e.2 ≠ 0))).isSome :=
      List.find?_isSome.2 ⟨(c, m.count c), hentry,
        decide_eq_true (⟨rfl, hcount⟩ : c = c ∧ m.count c ≠ 0)⟩
    exact Option.isSome_iff_exists.1 this
  rw [he]
  have hep := List.find?_some he
  have hemem := List.mem_of_find?_eq_some he
  obtain ⟨c', k⟩ := e
  simp only [decide_eq_true_eq] at hep
  obtain ⟨rfl, _⟩ := hep
  obtain ⟨_, hkeq⟩ := mem_resOf.1 hemem
  rw [if_neg hZ] at hkeq
  subst hkeq
  rfl

theorem ofEntries_cons (e : C × Nat) (res : List (C × Nat)) :
    ofEntries (e :: res) = Multiset.replicate e.2 e.1 + ofEntries res := by
  simp [ofEntries]

theorem ofEntries_filter_nonzero (res : List (C × Nat)) :
    ofEntries (res.filter (fun e => e.2 ≠ 0)) = ofEntries res := by
  induction res with
  | nil => rfl
  | cons e res ih =>
      rw [List.filter_cons]
      split
      · rw [ofEntries_cons, ofEntries_cons, ih]
      · next hp =>
        have h0 : e.2 = 0 := by simpa using hp
        rw [ih, ofEntries_cons, h0, Multiset.replicate_zero, zero_add]

theorem count_ofEntries_map (l : List C) (g : C → Nat) (hl : l.Nodup) (d : C) :
    Multiset.count d (ofEntries (l.map (fun c => (c, g c)))) =
      if d ∈ l then g d else 0 := by
  induction l with
  | nil => simp [ofEntries]
  | cons c l ih =>
      rw [List.nodup_cons] at hl
      rw [List.map_cons, ofEntries_cons, Multiset.count_add, ih hl.2]
      by_cases hdc : d = c
      · subst hdc
        simp [hl.1]
      · simp [hdc, Multiset.mem_replicate]

theorem count_ofEntries_resOf (m : Multiset C) (Z : List C) (d : C) :
    Multiset.count d (ofEntries (resOf m Z)) =
      Multiset.count d (m.filter (fun c => c ∉ Z)) := by
  unfold resOf
  rw [count_ofEntries_map _ _ (Finset.sort_nodup _ _), Multiset.count_filter]
  simp only [Finset.mem_sort, Multiset.mem_toFinset]
  by_cases hZ : d ∈ Z
  · simp [hZ]
  · by_cases hm : d ∈ m
    · simp [hZ, hm]
    · simp [hZ, hm, Multiset.count_eq_zero.2 hm]

theorem ofEntries_resOf (m : Multiset C) (Z : List C) :
    ofEntries ((resOf m Z).filter (fun e => e.2 ≠ 0)) =
      m.filter (fun c => c ∉ Z) := by
  rw [ofEntries_filter_nonzero]
  ext d
  exact count_ofEntries_resOf m Z d

/-! ## The generalized rest condition -/

/-- `MsetRestOk` relative to the classes `Z` already zeroed. -/
def RestOkZ (σ' : Binding) (rest : Option Var) (m : Multiset C)
    (Z taken : List C) : Prop :=
  match rest with
  | none => ∀ c ∈ m, c ∈ Z ++ taken
  | some r => σ'.rest r = some (m.filter (fun c => c ∉ Z ++ taken))

theorem RestOkZ.shift {σ' : Binding} {rest : Option Var} {m : Multiset C}
    {Z taken : List C} {c : C} (h : RestOkZ σ' rest m (c :: Z) taken) :
    RestOkZ σ' rest m Z (c :: taken) := by
  cases rest with
  | none =>
      intro d hd
      have := h d hd
      simp only [List.mem_append, List.mem_cons] at this ⊢
      tauto
  | some r =>
      show σ'.rest r = some _
      rw [show σ'.rest r = _ from h]
      congr 1
      apply Multiset.filter_congr
      intro d _
      simp only [List.mem_append, List.mem_cons]
      tauto

theorem RestOkZ.unshift {σ' : Binding} {rest : Option Var} {m : Multiset C}
    {Z taken : List C} {c : C} (h : RestOkZ σ' rest m Z (c :: taken)) :
    RestOkZ σ' rest m (c :: Z) taken := by
  cases rest with
  | none =>
      intro d hd
      have := h d hd
      simp only [List.mem_append, List.mem_cons] at this ⊢
      tauto
  | some r =>
      show σ'.rest r = some _
      rw [show σ'.rest r = _ from h]
      congr 1
      apply Multiset.filter_congr
      intro d _
      simp only [List.mem_append, List.mem_cons]
      tauto

/-! ## AC: soundness -/

theorem decomposeAC_sound_gen (es : List (Var × Mult)) (rest : Option Var)
    (m : Multiset C) :
    ∀ (Z : List C) (σ σ' : Binding), (∀ r ∈ rest, σ.rest r = none) →
      σ' ∈ decomposeAC es rest (resOf m Z) σ →
      Extends σ σ' ∧ ∃ taken : List C, taken.Nodup ∧ es.length = taken.length ∧
        (∀ c ∈ taken, c ∈ m ∧ c ∉ Z) ∧
        (∀ et ∈ es.zip taken, σ'.cls et.1.1 = some et.2) ∧
        (∀ et ∈ es.zip taken, MultOk σ' et.1.2 (m.count et.2)) ∧
        RestOkZ σ' rest m Z taken := by
  induction es with
  | nil =>
      intro Z σ σ' hfresh h
      cases rest with
      | none =>
          simp only [decomposeAC] at h
          split at h
          · next hempty =>
            rw [List.mem_singleton] at h
            subst h
            refine ⟨Extends.refl _, [], List.nodup_nil, rfl, by simp, by simp,
              by simp, ?_⟩
            intro c hc
            simp only [List.append_nil]
            by_contra hZ
            have hmem : (c, m.count c) ∈ resOf m Z :=
              mem_resOf.2 ⟨hc, by rw [if_neg hZ]⟩
            have hne : m.count c ≠ 0 := by
              rw [Ne, Multiset.count_eq_zero]
              exact fun h' => h' hc
            have hin : (c, m.count c) ∈ (resOf m Z).filter (fun e => e.2 ≠ 0) :=
              List.mem_filter.2 ⟨hmem, by simpa using hne⟩
            rw [List.isEmpty_iff.1 hempty] at hin
            simp at hin
          · cases h
      | some r =>
          simp only [decomposeAC] at h
          rw [List.mem_singleton] at h
          subst h
          refine ⟨extends_setRest (hfresh r rfl), [], List.nodup_nil, rfl, by simp,
            by simp, by simp, ?_⟩
          show (σ.setRest r _).rest r = some _
          simp only [Binding.setRest, Function.update_self]
          rw [ofEntries_resOf]
          simp
  | cons e es ih =>
      intro Z σ σ' hfresh h
      obtain ⟨x, μ⟩ := e
      simp only [decomposeAC] at h
      split at h
      · next c hx =>
        split at h
        · next e' hfind =>
          split at h
          · next σ₁ hmm =>
            have he'mem := List.mem_of_find?_eq_some hfind
            have he'p := List.find?_some hfind
            obtain ⟨c', k⟩ := e'
            simp only [decide_eq_true_eq] at he'p
            obtain ⟨rfl, hk⟩ := he'p
            obtain ⟨hcm, hkeq⟩ := mem_resOf.1 he'mem
            have hcZ : c' ∉ Z := by
              intro hZ
              rw [if_pos hZ] at hkeq
              exact hk hkeq
            rw [if_neg hcZ] at hkeq
            subst hkeq
            obtain ⟨hok, hext₁⟩ := mult_matches_sound σ σ₁ μ _ hmm
            obtain ⟨_, hrest₁, _⟩ := multMatches_fields hmm
            rw [zeroEntry_resOf] at h
            obtain ⟨hext₂, taken, hnd, hlen, hmemZ, hclsT, hmultT, hrestT⟩ :=
              ih (c' :: Z) σ₁ σ' (by
                intro r hr
                rw [hrest₁]
                exact hfresh r hr) h
            refine ⟨hext₁.trans hext₂, c' :: taken, ?_, by simp [hlen], ?_, ?_, ?_,
              hrestT.shift⟩
            · rw [List.nodup_cons]
              exact ⟨fun hc => (hmemZ c' hc).2 (by simp), hnd⟩
            · intro d hd
              rw [List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact ⟨hcm, hcZ⟩
              · exact ⟨(hmemZ d hd).1, fun hZ => (hmemZ d hd).2 (by simp [hZ])⟩
            · intro et het
              rw [List.zip_cons_cons, List.mem_cons] at het
              rcases het with rfl | het
              · exact (hext₁.trans hext₂).1 x c' hx
              · exact hclsT et het
            · intro et het
              rw [List.zip_cons_cons, List.mem_cons] at het
              rcases het with rfl | het
              · exact hok.mono hext₂
              · exact hmultT et het
          · cases h
        · cases h
      · next hx =>
        rw [List.mem_flatMap] at h
        obtain ⟨⟨c, k⟩, hmem, h⟩ := h
        simp only at h
        split at h
        · cases h
        · next hk =>
          split at h
          · next σ₁ hmm =>
            obtain ⟨hcm, hkeq⟩ := mem_resOf.1 hmem
            have hcZ : c ∉ Z := by
              intro hZ
              rw [if_pos hZ] at hkeq
              exact hk hkeq
            rw [if_neg hcZ] at hkeq
            subst hkeq
            obtain ⟨hok, hext₁⟩ := mult_matches_sound σ σ₁ μ _ hmm
            obtain ⟨hcls₁, hrest₁, _⟩ := multMatches_fields hmm
            have hx₁ : σ₁.cls x = none := by
              rw [hcls₁]
              exact hx
            have hext₁' : Extends σ₁ (σ₁.setCls x c) := extends_setCls hx₁
            rw [zeroEntry_resOf] at h
            obtain ⟨hext₂, taken, hnd, hlen, hmemZ, hclsT, hmultT, hrestT⟩ :=
              ih (c :: Z) (σ₁.setCls x c) σ' (by
                intro r hr
                show σ₁.rest r = none
                rw [hrest₁]
                exact hfresh r hr) h
            have hext₃ : Extends σ₁ σ' := hext₁'.trans hext₂
            refine ⟨hext₁.trans hext₃, c :: taken, ?_, by simp [hlen], ?_, ?_, ?_,
              hrestT.shift⟩
            · rw [List.nodup_cons]
              exact ⟨fun hc => (hmemZ c hc).2 (by simp), hnd⟩
            · intro d hd
              rw [List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact ⟨hcm, hcZ⟩
              · exact ⟨(hmemZ d hd).1, fun hZ => (hmemZ d hd).2 (by simp [hZ])⟩
            · intro et het
              rw [List.zip_cons_cons, List.mem_cons] at het
              rcases het with rfl | het
              · exact hext₂.1 x c (by simp [Binding.setCls])
              · exact hclsT et het
            · intro et het
              rw [List.zip_cons_cons, List.mem_cons] at het
              rcases het with rfl | het
              · exact hok.mono hext₃
              · exact hmultT et het
          · cases h

/-- Lemma 5 (`decompose_ac_sound`), with the hypothesis that the rest
variable is unbound in the input binding. -/
theorem decompose_ac_sound' (elems : List (Var × Mult)) (rest : Option Var)
    (m : Multiset C) (σ σ' : Binding)
    (hfresh : ∀ r ∈ rest, σ.rest r = none)
    (h : σ' ∈ decomposeAC elems rest (Multiset.entries m) σ) :
    Binding.Extends σ σ' ∧
      ∃ taken : List C, taken.Nodup ∧ elems.length = taken.length ∧
        (∀ c ∈ taken, c ∈ m) ∧
        (∀ et ∈ elems.zip taken, σ'.cls et.1.1 = some et.2) ∧
        (∀ et ∈ elems.zip taken, MultOk σ' et.1.2 (m.count et.2)) ∧
        MsetRestOk σ' rest m taken := by
  rw [entries_eq_resOf] at h
  obtain ⟨hext, taken, hnd, hlen, hmem, hcls, hmult, hrest⟩ :=
    decomposeAC_sound_gen elems rest m [] σ σ' hfresh h
  refine ⟨hext, taken, hnd, hlen, fun c hc => (hmem c hc).1, hcls, hmult, ?_⟩
  cases rest with
  | none =>
      intro c hc
      simpa using hrest c hc
  | some r =>
      show σ'.rest r = _
      rw [show σ'.rest r = _ from hrest]
      simp

/-! ## AC: completeness -/

theorem decomposeAC_complete_gen (es : List (Var × Mult)) (rest : Option Var)
    (m : Multiset C) :
    ∀ (Z : List C) (σ σ' : Binding) (taken : List C),
      Extends σ σ' → taken.Nodup → es.length = taken.length →
      (∀ c ∈ taken, c ∈ m ∧ c ∉ Z) →
      (∀ et ∈ es.zip taken, σ'.cls et.1.1 = some et.2) →
      (∀ et ∈ es.zip taken, MultOk σ' et.1.2 (m.count et.2)) →
      RestOkZ σ' rest m Z taken →
      ∃ σ'' ∈ decomposeAC es rest (resOf m Z) σ, Extends σ'' σ' := by
  induction es with
  | nil =>
      intro Z σ σ' taken hext hnd hlen hmem hcls hmult hrest
      cases taken with
      | cons _ _ => cases hlen
      | nil =>
      cases rest with
      | none =>
          simp only [decomposeAC]
          have hleft : (resOf m Z).filter (fun e => e.2 ≠ 0) = [] := by
            rw [List.filter_eq_nil_iff]
            rintro ⟨c, k⟩ hmemck
            obtain ⟨hcm, rfl⟩ := mem_resOf.1 hmemck
            have := hrest c hcm
            simp only [List.append_nil] at this
            simp [this]
          rw [hleft]
          exact ⟨σ, by simp, hext⟩
      | some r =>
          simp only [decomposeAC]
          refine ⟨_, List.mem_singleton_self _, ?_⟩
          have hr : σ'.rest r = some (m.filter fun c => c ∉ Z) := by
            have := (show σ'.rest r = _ from hrest)
            rw [this]
            simp
          refine ⟨hext.1, hext.2.1, hext.2.2.1, ?_, hext.2.2.2.2.1, hext.2.2.2.2.2⟩
          intro r' v hr'
          by_cases hrr : r' = r
          · subst hrr
            simp only [Binding.setRest, Function.update_self] at hr'
            rw [hr, ← hr', ofEntries_resOf]
          · simp only [Binding.setRest, Function.update_of_ne hrr] at hr'
            exact hext.2.2.2.1 r' v hr'
  | cons e es ih =>
      intro Z σ σ' taken hext hnd hlen hmem hcls hmult hrest
      obtain ⟨x, μ⟩ := e
      cases taken with
      | nil => cases hlen
      | cons c taken =>
      rw [List.nodup_cons] at hnd
      have hxc : σ'.cls x = some c := hcls ((x, μ), c) (by simp)
      have hμc : MultOk σ' μ (m.count c) := hmult ((x, μ), c) (by simp)
      obtain ⟨hcm, hcZ⟩ := hmem c (by simp)
      have hmem' : ∀ d ∈ taken, d ∈ m ∧ d ∉ c :: Z := fun d hd =>
        ⟨(hmem d (by simp [hd])).1, by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => hnd.1 (h ▸ hd), (hmem d (by simp [hd])).2⟩⟩
      have hcls' : ∀ et ∈ es.zip taken, σ'.cls et.1.1 = some et.2 :=
        fun et het => hcls et (by simp [het])
      have hmult' : ∀ et ∈ es.zip taken, MultOk σ' et.1.2 (m.count et.2) :=
        fun et het => hmult et (by simp [het])
      have hrest' : RestOkZ σ' rest m (c :: Z) taken := hrest.unshift
      have hcount : m.count c ≠ 0 := by
        rw [Ne, Multiset.count_eq_zero]
        exact fun h => h hcm
      have hentry : (c, m.count c) ∈ resOf m Z :=
        mem_resOf.2 ⟨hcm, by rw [if_neg hcZ]⟩
      obtain ⟨σ₁, hmm, hext₁⟩ := mult_matches_complete σ σ' μ (m.count c) hμc hext
      obtain ⟨hcls₁, _, _⟩ := multMatches_fields hmm
      have hlen' : es.length = taken.length := by simpa using hlen
      simp only [decomposeAC]
      cases hx : σ.cls x with
      | some c₀ =>
          have hc₀ : c₀ = c := by
            have := hext.1 x c₀ hx
            rw [hxc] at this
            exact (Option.some.inj this).symm
          subst hc₀
          dsimp only
          rw [find?_resOf hcm hcZ]
          simp only [hmm, zeroEntry_resOf]
          exact ih (c₀ :: Z) σ₁ σ' taken hext₁ hnd.2 hlen' hmem' hcls' hmult' hrest'
      | none =>
          have hx₁ : σ₁.cls x = none := by
            rw [hcls₁]
            exact hx
          have hext₂ : Extends (σ₁.setCls x c) σ' := by
            refine ⟨?_, hext₁.2.1, hext₁.2.2.1, hext₁.2.2.2.1, hext₁.2.2.2.2.1,
              hext₁.2.2.2.2.2⟩
            intro x' c' hx'
            by_cases hxx : x' = x
            · subst hxx
              simp only [Binding.setCls, Function.update_self] at hx'
              rw [← hx']
              exact hxc
            · simp only [Binding.setCls, Function.update_of_ne hxx] at hx'
              exact hext₁.1 x' c' hx'
          obtain ⟨σ'', hσ'', hext''⟩ :=
            ih (c :: Z) (σ₁.setCls x c) σ' taken hext₂ hnd.2 hlen' hmem' hcls' hmult'
              hrest'
          refine ⟨σ'', ?_, hext''⟩
          dsimp only
          rw [List.mem_flatMap]
          refine ⟨(c, m.count c), hentry, ?_⟩
          simp only [hcount, if_false, hmm, zeroEntry_resOf]
          exact hσ''

/-- Lemma 6 (`decompose_ac_complete`), as stated in `Lemmas.lean`. -/
theorem decompose_ac_complete' (elems : List (Var × Mult)) (rest : Option Var)
    (m : Multiset C) (σ σ' : Binding) (taken : List C)
    (hext : Binding.Extends σ σ')
    (hnd : taken.Nodup) (hlen : elems.length = taken.length)
    (hmem : ∀ c ∈ taken, c ∈ m)
    (hcls : ∀ et ∈ elems.zip taken, σ'.cls et.1.1 = some et.2)
    (hmult : ∀ et ∈ elems.zip taken, MultOk σ' et.1.2 (m.count et.2))
    (hrest : MsetRestOk σ' rest m taken) :
    ∃ σ'' ∈ decomposeAC elems rest (Multiset.entries m) σ,
      Binding.Extends σ'' σ' := by
  rw [entries_eq_resOf]
  refine decomposeAC_complete_gen elems rest m [] σ σ' taken hext hnd hlen
    (fun c hc => ⟨hmem c hc, by simp⟩) hcls hmult ?_
  cases rest with
  | none =>
      intro c hc
      simpa using hrest c hc
  | some r =>
      show σ'.rest r = _
      rw [show σ'.rest r = _ from hrest]
      simp

/-! ## Residuals of a set -/

/-- The sorted elements of `s` without those in `Z`. -/
def resSet (s : Finset C) (Z : List C) : List C :=
  (s.sort (· ≤ ·)).filter (fun c => decide (c ∉ Z))

theorem sort_eq_resSet (s : Finset C) : s.sort (· ≤ ·) = resSet s [] := by
  simp [resSet]

theorem mem_resSet {s : Finset C} {Z : List C} {c : C} :
    c ∈ resSet s Z ↔ c ∈ s ∧ c ∉ Z := by
  simp [resSet, Finset.mem_sort]

theorem resSet_nodup (s : Finset C) (Z : List C) : (resSet s Z).Nodup :=
  (Finset.sort_nodup _ _).filter _

theorem resSet_erase (s : Finset C) (Z : List C) (c : C) :
    (resSet s Z).erase c = resSet s (c :: Z) := by
  rw [(resSet_nodup s Z).erase_eq_filter]
  unfold resSet
  rw [List.filter_filter]
  apply List.filter_congr
  intro d _
  by_cases h1 : d = c <;> by_cases h2 : d ∈ Z <;> simp [h1, h2]

theorem resSet_toFinset (s : Finset C) (Z : List C) :
    (resSet s Z).toFinset = s.filter (fun c => c ∉ Z) := by
  ext d
  simp [resSet, Finset.mem_sort]

/-- `SetRestOk` relative to the classes `Z` already erased. -/
def SetRestOkZ (σ' : Binding) (rest : Option Var) (s : Finset C)
    (Z taken : List C) : Prop :=
  match rest with
  | none => ∀ c ∈ s, c ∈ Z ++ taken
  | some r => σ'.finRest r = some (s.filter (fun c => c ∉ Z ++ taken))

theorem SetRestOkZ.shift {σ' : Binding} {rest : Option Var} {s : Finset C}
    {Z taken : List C} {c : C} (h : SetRestOkZ σ' rest s (c :: Z) taken) :
    SetRestOkZ σ' rest s Z (c :: taken) := by
  cases rest with
  | none =>
      intro d hd
      have := h d hd
      simp only [List.mem_append, List.mem_cons] at this ⊢
      tauto
  | some r =>
      show σ'.finRest r = some _
      rw [show σ'.finRest r = _ from h]
      congr 1
      apply Finset.filter_congr
      intro d _
      simp only [List.mem_append, List.mem_cons]
      tauto

theorem SetRestOkZ.unshift {σ' : Binding} {rest : Option Var} {s : Finset C}
    {Z taken : List C} {c : C} (h : SetRestOkZ σ' rest s Z (c :: taken)) :
    SetRestOkZ σ' rest s (c :: Z) taken := by
  cases rest with
  | none =>
      intro d hd
      have := h d hd
      simp only [List.mem_append, List.mem_cons] at this ⊢
      tauto
  | some r =>
      show σ'.finRest r = some _
      rw [show σ'.finRest r = _ from h]
      congr 1
      apply Finset.filter_congr
      intro d _
      simp only [List.mem_append, List.mem_cons]
      tauto

/-! ## ACI: soundness -/

theorem decomposeACI_sound_gen (es : List Var) (rest : Option Var) (s : Finset C) :
    ∀ (Z : List C) (σ σ' : Binding), (∀ r ∈ rest, σ.finRest r = none) →
      σ' ∈ decomposeACI es rest (resSet s Z) σ →
      Extends σ σ' ∧ ∃ taken : List C, taken.Nodup ∧ es.length = taken.length ∧
        (∀ c ∈ taken, c ∈ s ∧ c ∉ Z) ∧
        (∀ et ∈ es.zip taken, σ'.cls et.1 = some et.2) ∧
        SetRestOkZ σ' rest s Z taken := by
  induction es with
  | nil =>
      intro Z σ σ' hfresh h
      cases rest with
      | none =>
          simp only [decomposeACI] at h
          split at h
          · next hempty =>
            rw [List.mem_singleton] at h
            subst h
            refine ⟨Extends.refl _, [], List.nodup_nil, rfl, by simp, by simp, ?_⟩
            intro c hc
            simp only [List.append_nil]
            by_contra hZ
            have hin : c ∈ resSet s Z := mem_resSet.2 ⟨hc, hZ⟩
            rw [List.isEmpty_iff.1 hempty] at hin
            simp at hin
          · cases h
      | some r =>
          simp only [decomposeACI] at h
          rw [List.mem_singleton] at h
          subst h
          refine ⟨extends_setSetRest (hfresh r rfl), [], List.nodup_nil, rfl, by simp,
            by simp, ?_⟩
          show (σ.setSetRest r _).finRest r = some _
          simp only [Binding.setSetRest, Function.update_self]
          rw [resSet_toFinset]
          simp
  | cons x es ih =>
      intro Z σ σ' hfresh h
      simp only [decomposeACI] at h
      split at h
      · next c hx =>
        split at h
        · next hcin =>
          obtain ⟨hcs, hcZ⟩ := mem_resSet.1 hcin
          rw [resSet_erase] at h
          obtain ⟨hext, taken, hnd, hlen, hmemZ, hclsT, hrestT⟩ :=
            ih (c :: Z) σ σ' hfresh h
          refine ⟨hext, c :: taken, ?_, by simp [hlen], ?_, ?_, hrestT.shift⟩
          · rw [List.nodup_cons]
            exact ⟨fun hc => (hmemZ c hc).2 (by simp), hnd⟩
          · intro d hd
            rw [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact ⟨hcs, hcZ⟩
            · exact ⟨(hmemZ d hd).1, fun hZ => (hmemZ d hd).2 (by simp [hZ])⟩
          · intro et het
            rw [List.zip_cons_cons, List.mem_cons] at het
            rcases het with rfl | het
            · exact hext.1 x c hx
            · exact hclsT et het
        · cases h
      · next hx =>
        rw [List.mem_flatMap] at h
        obtain ⟨c, hcin, h⟩ := h
        obtain ⟨hcs, hcZ⟩ := mem_resSet.1 hcin
        rw [resSet_erase] at h
        have hext₁ : Extends σ (σ.setCls x c) := extends_setCls hx
        obtain ⟨hext₂, taken, hnd, hlen, hmemZ, hclsT, hrestT⟩ :=
          ih (c :: Z) (σ.setCls x c) σ' (by
            intro r hr
            show σ.finRest r = none
            exact hfresh r hr) h
        refine ⟨hext₁.trans hext₂, c :: taken, ?_, by simp [hlen], ?_, ?_, hrestT.shift⟩
        · rw [List.nodup_cons]
          exact ⟨fun hc => (hmemZ c hc).2 (by simp), hnd⟩
        · intro d hd
          rw [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact ⟨hcs, hcZ⟩
          · exact ⟨(hmemZ d hd).1, fun hZ => (hmemZ d hd).2 (by simp [hZ])⟩
        · intro et het
          rw [List.zip_cons_cons, List.mem_cons] at het
          rcases het with rfl | het
          · exact hext₂.1 x c (by simp [Binding.setCls])
          · exact hclsT et het

/-- Lemma 7 (`decompose_aci_sound`), with the hypothesis that the rest
variable is unbound in the input binding. -/
theorem decompose_aci_sound' (elems : List Var) (rest : Option Var)
    (s : Finset C) (σ σ' : Binding)
    (hfresh : ∀ r ∈ rest, σ.finRest r = none)
    (h : σ' ∈ decomposeACI elems rest (s.sort (· ≤ ·)) σ) :
    Binding.Extends σ σ' ∧
      ∃ taken : List C, taken.Nodup ∧ elems.length = taken.length ∧
        (∀ c ∈ taken, c ∈ s) ∧
        (∀ et ∈ elems.zip taken, σ'.cls et.1 = some et.2) ∧
        SetRestOk σ' rest s taken := by
  rw [sort_eq_resSet] at h
  obtain ⟨hext, taken, hnd, hlen, hmem, hcls, hrest⟩ :=
    decomposeACI_sound_gen elems rest s [] σ σ' hfresh h
  refine ⟨hext, taken, hnd, hlen, fun c hc => (hmem c hc).1, hcls, ?_⟩
  cases rest with
  | none =>
      intro c hc
      simpa using hrest c hc
  | some r =>
      show σ'.finRest r = _
      rw [show σ'.finRest r = _ from hrest]
      simp

/-! ## ACI: completeness -/

theorem decomposeACI_complete_gen (es : List Var) (rest : Option Var)
    (s : Finset C) :
    ∀ (Z : List C) (σ σ' : Binding) (taken : List C),
      Extends σ σ' → taken.Nodup → es.length = taken.length →
      (∀ c ∈ taken, c ∈ s ∧ c ∉ Z) →
      (∀ et ∈ es.zip taken, σ'.cls et.1 = some et.2) →
      SetRestOkZ σ' rest s Z taken →
      ∃ σ'' ∈ decomposeACI es rest (resSet s Z) σ, Extends σ'' σ' := by
  induction es with
  | nil =>
      intro Z σ σ' taken hext hnd hlen hmem hcls hrest
      cases taken with
      | cons _ _ => cases hlen
      | nil =>
      cases rest with
      | none =>
          simp only [decomposeACI]
          have hempty : resSet s Z = [] := by
            rw [List.eq_nil_iff_forall_not_mem]
            intro c hc
            obtain ⟨hcs, hcZ⟩ := mem_resSet.1 hc
            have := hrest c hcs
            simp only [List.append_nil] at this
            exact hcZ this
          rw [hempty]
          exact ⟨σ, by simp, hext⟩
      | some r =>
          simp only [decomposeACI]
          refine ⟨_, List.mem_singleton_self _, ?_⟩
          have hr : σ'.finRest r = some (s.filter fun c => c ∉ Z) := by
            have := (show σ'.finRest r = _ from hrest)
            rw [this]
            simp
          refine ⟨hext.1, hext.2.1, hext.2.2.1, hext.2.2.2.1, hext.2.2.2.2.1, ?_⟩
          intro r' v hr'
          by_cases hrr : r' = r
          · subst hrr
            simp only [Binding.setSetRest, Function.update_self] at hr'
            rw [hr, ← hr', resSet_toFinset]
          · simp only [Binding.setSetRest, Function.update_of_ne hrr] at hr'
            exact hext.2.2.2.2.2 r' v hr'
  | cons x es ih =>
      intro Z σ σ' taken hext hnd hlen hmem hcls hrest
      cases taken with
      | nil => cases hlen
      | cons c taken =>
      rw [List.nodup_cons] at hnd
      have hxc : σ'.cls x = some c := hcls (x, c) (by simp)
      obtain ⟨hcs, hcZ⟩ := hmem c (by simp)
      have hmem' : ∀ d ∈ taken, d ∈ s ∧ d ∉ c :: Z := fun d hd =>
        ⟨(hmem d (by simp [hd])).1, by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => hnd.1 (h ▸ hd), (hmem d (by simp [hd])).2⟩⟩
      have hcls' : ∀ et ∈ es.zip taken, σ'.cls et.1 = some et.2 :=
        fun et het => hcls et (by simp [het])
      have hrest' : SetRestOkZ σ' rest s (c :: Z) taken := hrest.unshift
      have hcin : c ∈ resSet s Z := mem_resSet.2 ⟨hcs, hcZ⟩
      have hlen' : es.length = taken.length := by simpa using hlen
      simp only [decomposeACI]
      cases hx : σ.cls x with
      | some c₀ =>
          have hc₀ : c₀ = c := by
            have := hext.1 x c₀ hx
            rw [hxc] at this
            exact (Option.some.inj this).symm
          subst hc₀
          dsimp only
          rw [if_pos hcin, resSet_erase]
          exact ih (c₀ :: Z) σ σ' taken hext hnd.2 hlen' hmem' hcls' hrest'
      | none =>
          have hext₂ : Extends (σ.setCls x c) σ' := by
            refine ⟨?_, hext.2.1, hext.2.2.1, hext.2.2.2.1, hext.2.2.2.2.1,
              hext.2.2.2.2.2⟩
            intro x' c' hx'
            by_cases hxx : x' = x
            · subst hxx
              simp only [Binding.setCls, Function.update_self] at hx'
              rw [← hx']
              exact hxc
            · simp only [Binding.setCls, Function.update_of_ne hxx] at hx'
              exact hext.1 x' c' hx'
          obtain ⟨σ'', hσ'', hext''⟩ :=
            ih (c :: Z) (σ.setCls x c) σ' taken hext₂ hnd.2 hlen' hmem' hcls' hrest'
          refine ⟨σ'', ?_, hext''⟩
          dsimp only
          rw [List.mem_flatMap]
          refine ⟨c, hcin, ?_⟩
          rw [resSet_erase]
          exact hσ''

/-- Lemma 7 (`decompose_aci_complete`), as stated in `Lemmas.lean`. -/
theorem decompose_aci_complete' (elems : List Var) (rest : Option Var)
    (s : Finset C) (σ σ' : Binding) (taken : List C)
    (hext : Binding.Extends σ σ')
    (hnd : taken.Nodup) (hlen : elems.length = taken.length)
    (hmem : ∀ c ∈ taken, c ∈ s)
    (hcls : ∀ et ∈ elems.zip taken, σ'.cls et.1 = some et.2)
    (hrest : SetRestOk σ' rest s taken) :
    ∃ σ'' ∈ decomposeACI elems rest (s.sort (· ≤ ·)) σ,
      Binding.Extends σ'' σ' := by
  rw [sort_eq_resSet]
  refine decomposeACI_complete_gen elems rest s [] σ σ' taken hext hnd hlen
    (fun c hc => ⟨hmem c hc, by simp⟩) hcls ?_
  cases rest with
  | none =>
      intro c hc
      simpa using hrest c hc
  | some r =>
      show σ'.finRest r = _
      rw [show σ'.finRest r = _ from hrest]
      simp

end Semper.EMatch
