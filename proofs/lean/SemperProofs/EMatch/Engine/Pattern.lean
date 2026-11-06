import SemperProofs.EMatch.Engine.Plan
import SemperProofs.EMatch.Engine.AtomsMatch

/-!
# Patterns through plans (spec-scheduler §3.2, corollary)

For an application pattern `P` flattened into `atoms P r`, every `PlanOK`
plan emits exactly the `MatchN` bindings at the stored node bound to the
root node variable `r`: `engine_plan_sound'` and `engine_plan_complete'`
(primed: with the atom-list hypotheses `AtomsWF` explicit; the unprimed
versions in `Main.lean` discharge them from the pattern).
-/

namespace Semper.EMatch

open Classical

/-- Restriction of a binding to the variables of an atom list. -/
noncomputable def restrict (atoms : List QAtom) (σ : Binding) : Binding where
  cls x := if ∃ q ∈ atoms, x ∈ q.binds then σ.cls x else none
  node v := if ∃ a, QAtom.scan a ∈ atoms ∧ a.node = v then σ.node v else none
  mult k := if ∃ a, QAtom.scan a ∈ atoms ∧ k ∈ a.multVars then σ.mult k else none
  rest r := if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.msetRestVars then σ.rest r else none
  seqRest r := if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.seqRestVars then σ.seqRest r else none
  finRest r := if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.setRestVars then σ.finRest r else none

theorem restrict_cls {atoms : List QAtom} {σ : Binding} {x : Var} (h : ∃ q ∈ atoms, x ∈ q.binds) :
    (restrict atoms σ).cls x = σ.cls x := by
  show (if ∃ q ∈ atoms, x ∈ q.binds then σ.cls x else none) = σ.cls x
  rw [if_pos h]
theorem restrict_cls_none {atoms : List QAtom} {σ : Binding} {x : Var}
    (h : ¬ ∃ q ∈ atoms, x ∈ q.binds) : (restrict atoms σ).cls x = none := by
  show (if ∃ q ∈ atoms, x ∈ q.binds then σ.cls x else none) = none
  rw [if_neg h]
theorem restrict_node {atoms : List QAtom} {σ : Binding} {v : Var}
    (h : ∃ a, QAtom.scan a ∈ atoms ∧ a.node = v) : (restrict atoms σ).node v = σ.node v := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ a.node = v then σ.node v else none) = σ.node v
  rw [if_pos h]
theorem restrict_node_none {atoms : List QAtom} {σ : Binding} {v : Var}
    (h : ¬ ∃ a, QAtom.scan a ∈ atoms ∧ a.node = v) : (restrict atoms σ).node v = none := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ a.node = v then σ.node v else none) = none
  rw [if_neg h]
theorem restrict_mult {atoms : List QAtom} {σ : Binding} {k : Var}
    (h : ∃ a, QAtom.scan a ∈ atoms ∧ k ∈ a.multVars) : (restrict atoms σ).mult k = σ.mult k := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ k ∈ a.multVars then σ.mult k else none) = σ.mult k
  rw [if_pos h]
theorem restrict_mult_none {atoms : List QAtom} {σ : Binding} {k : Var}
    (h : ¬ ∃ a, QAtom.scan a ∈ atoms ∧ k ∈ a.multVars) : (restrict atoms σ).mult k = none := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ k ∈ a.multVars then σ.mult k else none) = none
  rw [if_neg h]
theorem restrict_rest {atoms : List QAtom} {σ : Binding} {r : Var}
    (h : ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.msetRestVars) : (restrict atoms σ).rest r = σ.rest r := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.msetRestVars then σ.rest r else none) = σ.rest r
  rw [if_pos h]
theorem restrict_rest_none {atoms : List QAtom} {σ : Binding} {r : Var}
    (h : ¬ ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.msetRestVars) : (restrict atoms σ).rest r = none := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.msetRestVars then σ.rest r else none) = none
  rw [if_neg h]
theorem restrict_seqRest {atoms : List QAtom} {σ : Binding} {r : Var}
    (h : ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.seqRestVars) :
    (restrict atoms σ).seqRest r = σ.seqRest r := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.seqRestVars then σ.seqRest r else none) = σ.seqRest r
  rw [if_pos h]
theorem restrict_seqRest_none {atoms : List QAtom} {σ : Binding} {r : Var}
    (h : ¬ ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.seqRestVars) : (restrict atoms σ).seqRest r = none := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.seqRestVars then σ.seqRest r else none) = none
  rw [if_neg h]
theorem restrict_finRest {atoms : List QAtom} {σ : Binding} {r : Var}
    (h : ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.setRestVars) :
    (restrict atoms σ).finRest r = σ.finRest r := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.setRestVars then σ.finRest r else none) = σ.finRest r
  rw [if_pos h]
theorem restrict_finRest_none {atoms : List QAtom} {σ : Binding} {r : Var}
    (h : ¬ ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.setRestVars) : (restrict atoms σ).finRest r = none := by
  show (if ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.setRestVars then σ.finRest r else none) = none
  rw [if_neg h]

theorem elem_mem_binds {a : RAtom} {e : Var} (h : e ∈ a.elems) : e ∈ a.binds := by
  simp [RAtom.binds, h]

/-- A satisfied scanning atom stays satisfied under the restriction. -/
theorem atomSat_restrict {G : Graph} {atoms : List QAtom} {σ : Binding} {a : RAtom}
    (ha : QAtom.scan a ∈ atoms) (h : AtomSat G σ a) : AtomSat G (restrict atoms σ) a := by
  obtain ⟨id, nd, hn, hmem, hc, hop, hm⟩ := h
  refine ⟨id, nd, by rw [restrict_node ⟨a, ha, rfl⟩]; exact hn, hmem,
    by rw [restrict_cls ⟨_, ha, Finset.mem_insert_self _ _⟩]; exact hc, hop, ?_⟩
  obtain ⟨n, f, sh⟩ := a
  simp only [RAtom.shallow] at hm ⊢
  have hcls : ∀ e ∈ RAtom.elems ⟨n, f, sh⟩, (restrict atoms σ).cls e = σ.cls e :=
    fun e he => restrict_cls ⟨_, ha, elem_mem_binds he⟩
  cases sh with
  | plain cs =>
      obtain ⟨cs', rfl, hf⟩ := matchN_plain_vars.1 hm
      refine matchN_plain_vars.2 ⟨cs', rfl, ?_⟩
      rw [List.forall₂_iff_zip] at hf ⊢
      refine ⟨hf.1, fun hab => ?_⟩
      rw [hcls _ (List.of_mem_zip hab).1]
      exact hf.2 hab
  | comm x y =>
      obtain ⟨a, b, rfl, hab⟩ := matchN_comm_vars.1 hm
      refine matchN_comm_vars.2 ⟨a, b, rfl, ?_⟩
      rw [hcls x (by simp [RAtom.elems]), hcls y (by simp [RAtom.elems])]
      exact hab
  | assoc pre fx suf =>
      obtain ⟨u, mid, v, rfl, hpre, hsuf, hf⟩ := matchN_assoc_vars.1 hm
      refine matchN_assoc_vars.2 ⟨u, mid, v, rfl, ?_, ?_, ?_⟩
      · cases pre with
        | none => exact hpre
        | some p =>
            simp only [SeqRestOk] at hpre ⊢
            rw [restrict_seqRest ⟨_, ha, by simp [RAtom.seqRestVars]⟩]; exact hpre
      · cases suf with
        | none => exact hsuf
        | some s =>
            simp only [SeqRestOk] at hsuf ⊢
            rw [restrict_seqRest ⟨_, ha, by simp [RAtom.seqRestVars]⟩]; exact hsuf
      · rw [List.forall₂_iff_zip] at hf ⊢
        refine ⟨hf.1, fun hab => ?_⟩
        rw [hcls _ (List.of_mem_zip hab).1]
        exact hf.2 hab
  | ac es rest =>
      obtain ⟨m, taken, rfl, hnd, hlen, hmem', hcl, hmult, hrest⟩ := matchN_ac_vars.1 hm
      refine matchN_ac_vars.2 ⟨m, taken, rfl, hnd, hlen, hmem', ?_, ?_, ?_⟩
      · intro et het
        rw [hcls _ (by simp only [RAtom.elems, List.mem_map]; exact ⟨et.1, (List.of_mem_zip het).1, rfl⟩)]
        exact hcl et het
      · intro et het
        have := hmult et het
        obtain ⟨⟨e, μ⟩, t⟩ := et
        cases μ with
        | exact k => exact this
        | var k lo hi =>
            simp only [MultOk] at this ⊢
            rw [restrict_mult ⟨_, ha, by
              simp only [RAtom.multVars]
              rw [mem_multVars]
              exact ⟨(e, .var k lo hi), (List.of_mem_zip het).1, by simp [Mult.vars]⟩⟩]
            exact this
      · cases rest with
        | none => exact hrest
        | some r =>
            simp only [MsetRestOk] at hrest ⊢
            rw [restrict_rest ⟨_, ha, by simp [RAtom.msetRestVars]⟩]; exact hrest
  | aci es rest =>
      obtain ⟨st, taken, rfl, hnd, hlen, hmem', hcl, hrest⟩ := matchN_aci_vars.1 hm
      refine matchN_aci_vars.2 ⟨st, taken, rfl, hnd, hlen, hmem', ?_, ?_⟩
      · intro et het
        rw [hcls _ (List.of_mem_zip het).1]
        exact hcl et het
      · cases rest with
        | none => exact hrest
        | some r =>
            simp only [SetRestOk] at hrest ⊢
            rw [restrict_finRest ⟨_, ha, by simp [RAtom.setRestVars]⟩]; exact hrest

/-- The restriction of a binding satisfying every scanning atom of a
scan-only list is a `Matches` binding. -/
theorem matches_restrict {G : Graph} {as : List RAtom} {σ : Binding}
    (h : ∀ a ∈ as, AtomSat G σ a) : Matches G (as.map QAtom.scan) (restrict (as.map QAtom.scan) σ) := by
  have hsat : ∀ q ∈ as.map QAtom.scan, QSat G (restrict (as.map QAtom.scan) σ) q := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact atomSat_restrict (List.mem_map_of_mem ha) (h a ha)
  refine { sat := hsat, clsDom := ?_, node := ?_, mult := ?_, rest := ?_, seqRest := ?_, finRest := ?_ }
  · intro x
    constructor
    · rintro ⟨c, hc⟩
      by_contra hx
      rw [restrict_cls_none hx] at hc; cases hc
    · rintro ⟨q, hq, hx⟩
      have := hsat q hq
      rw [List.mem_map] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      simp only [QAtom.binds, RAtom.binds, Finset.mem_insert, List.mem_toFinset] at hx
      rcases hx with rfl | hx
      · obtain ⟨id, nd, -, -, hc, -⟩ := this; exact ⟨_, hc⟩
      · exact AtomSat.elems_bound this x hx
  · intro v
    constructor
    · rintro ⟨id, hid⟩
      by_contra hx
      rw [restrict_node_none hx] at hid; cases hid
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨id, nd, hid, -⟩ := hsat _ ha
      exact ⟨id, hid⟩
  · intro k
    constructor
    · rintro ⟨m, hm⟩
      by_contra hx
      rw [restrict_mult_none hx] at hm; cases hm
    · rintro ⟨a, ha, hk⟩
      exact AtomSat.multVars_bound (hsat _ ha) k hk
  · intro r
    constructor
    · rintro ⟨m, hm⟩
      by_contra hx
      rw [restrict_rest_none hx] at hm; cases hm
    · rintro ⟨a, ha, hr⟩
      exact AtomSat.msetRest_bound (hsat _ ha) r hr
  · intro r
    constructor
    · rintro ⟨u, hu⟩
      by_contra hx
      rw [restrict_seqRest_none hx] at hu; cases hu
    · rintro ⟨a, ha, hr⟩
      exact AtomSat.seqRest_bound (hsat _ ha) r hr
  · intro r
    constructor
    · rintro ⟨s, hs⟩
      by_contra hx
      rw [restrict_finRest_none hx] at hs; cases hs
    · rintro ⟨a, ha, hr⟩
      exact AtomSat.setRest_bound (hsat _ ha) r hr

/-- The root atom of an application pattern has node variable `r`. -/
theorem root_mem_atoms (P : Pat) (r : Var) (hP : P.head.isSome = true) :
    ∃ a ∈ atoms P r, a.node = r := by
  unfold atoms
  generalize P.freshAbove r = fresh
  cases P with
  | var x => simp [Pat.head] at hP
  | plain f args =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      rw [atomsAt_plain f args r fresh h]
      exact ⟨⟨r, f, .plain vs⟩, by simp, rfl⟩
  | comm f p q =>
      rcases h₁ : atomsChild p fresh with ⟨vp, ap, fr₁⟩
      rcases h₂ : atomsChild q fr₁ with ⟨vq, aq, fr₂⟩
      rw [atomsAt_comm f p q r fresh h₁ h₂]
      exact ⟨⟨r, f, .comm vp vq⟩, by simp, rfl⟩
  | assoc f pre args suf =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      rw [atomsAt_assoc f pre args suf r fresh h]
      exact ⟨⟨r, f, .assoc pre vs suf⟩, by simp, rfl⟩
  | ac f elems rest =>
      rcases h : atomsChildrenAC elems fresh with ⟨vs, as, fr⟩
      rw [atomsAt_ac f elems rest r fresh h]
      exact ⟨⟨r, f, .ac vs rest⟩, by simp, rfl⟩
  | aci f elems rest =>
      rcases h : atomsChildren elems fresh with ⟨vs, as, fr⟩
      rw [atomsAt_aci f elems rest r fresh h]
      exact ⟨⟨r, f, .aci vs rest⟩, by simp, rfl⟩

/-- `σ'` is below `σ` on the variables `V`, on every map but `node`. -/
def BelowOn (V : List Var) (σ' σ : Binding) : Prop :=
  ∀ x ∈ V, (∀ c, σ'.cls x = some c → σ.cls x = some c) ∧
    (∀ m, σ'.mult x = some m → σ.mult x = some m) ∧
    (∀ m, σ'.rest x = some m → σ.rest x = some m) ∧
    (∀ u, σ'.seqRest x = some u → σ.seqRest x = some u) ∧
    (∀ s, σ'.finRest x = some s → σ.finRest x = some s)

theorem lt_freshAbove (P : Pat) (r : Var) : r < P.freshAbove r ∧ ∀ x ∈ P.vars, x < P.freshAbove r := by
  obtain ⟨h₁, h₂⟩ := le_foldr_max P.vars r
  unfold Pat.freshAbove
  exact ⟨by vomega, fun x hx => by have := h₂ x hx; vomega⟩

/-- Soundness for patterns: every binding a `PlanOK` plan of `atoms P r`
emits matches `P` at the stored node bound to `r`. -/
theorem engine_plan_sound' {G : Graph} {sig : Sym → Kind} {P : Pat} {r : Var} {plan : Plan}
    {σ : Binding} (hwf : AtomsWF G sig ((atoms P r).map QAtom.scan)) (hP : P.head.isSome = true)
    (h : PlanOK ((atoms P r).map QAtom.scan) plan) (hσ : σ ∈ run G plan Binding.empty) :
    ∃ id n, σ.node r = some id ∧ (id, n) ∈ G.nodes ∧ σ.cls r = some (G.find id) ∧ MatchN G P n σ := by
  rw [plan_matches hwf h] at hσ
  have hall : ∀ a ∈ (atomsAt P r (P.freshAbove r)).1, AtomSat G σ a :=
    fun a ha => hσ.sat _ (List.mem_map_of_mem ha)
  obtain ⟨id, nd, hid, hmem, hc, -, hm⟩ := backOk P hP r _ hall
  exact ⟨id, nd, hid, hmem, hc, hm⟩

/-- Completeness for patterns: every `MatchN` binding at a stored node is
emitted (as a binding below it on the pattern's variables, with the root
node variable bound to that node). -/
theorem engine_plan_complete' {G : Graph} {sig : Sym → Kind} {P : Pat} {r : Var} {plan : Plan}
    {σ : Binding} {id : NodeId} {n : Node}
    (hwf : AtomsWF G sig ((atoms P r).map QAtom.scan)) (hP : P.head.isSome = true) (hr : r ∉ P.vars)
    (h : PlanOK ((atoms P r).map QAtom.scan) plan) (hmem : (id, n) ∈ G.nodes) (hm : MatchN G P n σ) :
    ∃ σ' ∈ run G plan Binding.empty, σ'.node r = some id ∧ BelowOn P.vars σ' σ := by
  obtain ⟨hr', hv⟩ := lt_freshAbove P r
  obtain ⟨σ₁, hk, hid, -, hall⟩ := fwdOk P σ id n r (P.freshAbove r) hmem hm hv hr' hr
  have hall' : ∀ a ∈ atoms P r, AtomSat G σ₁ a := hall
  have hmatch := matches_restrict hall'
  refine ⟨restrict ((atoms P r).map QAtom.scan) σ₁, (plan_matches hwf h _).2 hmatch, ?_, ?_⟩
  · obtain ⟨a, ha, hnode⟩ := root_mem_atoms P r hP
    rw [restrict_node ⟨a, List.mem_map_of_mem ha, hnode⟩]
    exact hid
  · intro x hx
    have hK : x ≠ r ∧ (x < P.freshAbove r ∨ (atomsAt P r (P.freshAbove r)).2 ≤ x) :=
      ⟨fun h' => hr (h' ▸ hx), Or.inl (hv x hx)⟩
    obtain ⟨hnc, hmult, hrest, hseq, hfin⟩ := hk
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      by_cases hb : ∃ q ∈ (atoms P r).map QAtom.scan, x ∈ q.binds
      · rw [restrict_cls hb, (hnc x hK).2] at hc; exact hc
      · rw [restrict_cls_none hb] at hc; cases hc
    · intro m hm'
      by_cases hb : ∃ a, QAtom.scan a ∈ (atoms P r).map QAtom.scan ∧ x ∈ a.multVars
      · rw [restrict_mult hb, hmult] at hm'; exact hm'
      · rw [restrict_mult_none hb] at hm'; cases hm'
    · intro m hm'
      by_cases hb : ∃ a, QAtom.scan a ∈ (atoms P r).map QAtom.scan ∧ x ∈ a.msetRestVars
      · rw [restrict_rest hb, hrest] at hm'; exact hm'
      · rw [restrict_rest_none hb] at hm'; cases hm'
    · intro u hu
      by_cases hb : ∃ a, QAtom.scan a ∈ (atoms P r).map QAtom.scan ∧ x ∈ a.seqRestVars
      · rw [restrict_seqRest hb, hseq] at hu; exact hu
      · rw [restrict_seqRest_none hb] at hu; cases hu
    · intro s hs
      by_cases hb : ∃ a, QAtom.scan a ∈ (atoms P r).map QAtom.scan ∧ x ∈ a.setRestVars
      · rw [restrict_finRest hb, hfin] at hs; exact hs
      · rw [restrict_finRest_none hb] at hs; cases hs

end Semper.EMatch
