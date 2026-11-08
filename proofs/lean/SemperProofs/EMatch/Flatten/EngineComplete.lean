import SemperProofs.EMatch.Flatten.EngineRule

/-!
# `:flatten`: completeness of the engine's demand rule, every kind, any laws

The laws development proves completeness of `acceptsLaws`, whose leaf test
has the opened-class clause for every kind. The engine's `Demand::accepts`
has it for multisets only (`merge_on_close`, `flatten.rs:354`). This file
proves the engine's rule `DemandL.acceptsE` complete as the engine has it:

* multisets: `demand_engine_complete_ac`, by `acceptsE_ac_iff` from
  `demand_laws_complete_ac` (same hypotheses);
* sequences: `demand_engine_complete_assoc`, the laws refold induction
  with the engine's leaf test (`eng_assoc_aux`): the opened-class clause is
  never used for sequences, so the hypotheses are those of
  `demand_laws_complete_assoc`;
* sets: `demand_engine_complete_aci`, under the collapse invariant
  `MembersTwoClassesL` (every filed `f`-member holds two classes less the
  unit) and `NodeTwoClassesL` for the node: closing a leaf whose opened
  class is taken can collapse the set to that one class, a view the engine
  drops (`FixKind.lean`, `TwoClasses`, gives the laws-free witness
  `n = And{X, Z}`, `Z ∋ And{X}`). `twoClassesL_of_members` derives
  `TwoClassesL` (every raw view of the node keeps two classes after the
  unit drop) from the invariant, which the engine's `add` establishes: a
  set node whose normal form is one class is not stored, its class is
  returned (`egraph.rs`, `Normal::Single(g) => find(g)`), and rebuild
  re-normalizes a member whose children merged and merges it into that
  class (`egraph/tests/egg/aci1.egg`: `Z ∋ And{X, s}`, `s ∪ Tru` merges `Z`
  with `X`, then `n = And{X, Z}` with `X`). `elems ≠ []` is not needed.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Multisets -/

/-- **Completeness of the engine's rule, AC, any laws.** -/
theorem demand_engine_complete_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {laws : Laws} {n : Node}
    {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .ac laws v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandL) (rest₀ rest' : Multiset C),
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsE .ac taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ RefoldsACL ctx laws taken rest₀ rest' := by
  obtain ⟨w', d, rest₀, rest', hd, hacc, hm', h0, hR⟩ :=
    demand_laws_complete_ac hκ hv hn helems hne hm
  exact ⟨w', d, rest₀, rest', hd, (DemandL.acceptsE_ac_iff d taken).2 hacc, hm', h0, hR⟩

/-! ## Sequences: the refold induction with the engine's leaf test -/

theorem eng_assoc_aux {ctx : Ctx} {laws : Laws} {n : Node} {f : Sym} {pre suf : Option Var}
    {args : List Pat} {mid : List C} (helems : ∀ p ∈ args, ∃ x, p = Pat.var x)
    (hne : args ≠ []) (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafL) (w : List (C × Nat)) (σ : Binding)
      (u s : List C),
      RawViewL ctx n v ls o → normalize .assoc laws v = .node w →
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid →
      SeqRestOk σ pre u → SeqRestOk σ suf s →
      ∃ (v' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (w' : List (C × Nat))
        (σ' : Binding) (u' s' : List C),
        RawViewL ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ flagLeaves .assoc laws v' ls', l.okE .assoc mid) ∧
        normalize .assoc laws v' = .node w' ∧
        MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
        σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
        σ'.finRest = σ.finRest ∧
        SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
        RefoldsAssocL ctx laws u u' ∧ RefoldsAssocL ctx laws s s' ∧
        (¬ (∀ l ∈ flagLeaves .assoc laws v ls, l.okE .assoc mid) → o' < o ∧
          (Relation.TransGen (RefoldStepAssocL ctx laws) u u' ∨
            Relation.TransGen (RefoldStepAssocL ctx laws) s s')) := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ u s hv hn hm hu hs
  have hn' := hn
  unfold normalize at hn'
  rw [classify_node_iff] at hn'
  obtain ⟨rfl, -, -⟩ := hn'
  rw [ofView_assoc_normalizeList] at hm
  by_cases hall : ∀ l ∈ flagLeaves .assoc laws v ls, l.okE .assoc mid
  · refine ⟨v, ls, o, _, σ, u, s, hv, le_rfl, hall, hn, ?_, rfl, rfl, rfl, rfl, rfl, hu, hs,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, fun h => absurd hall h⟩
    rw [ofView_assoc_normalizeList]
    exact hm
  · simp only [not_forall] at hall
    obtain ⟨lf, hlf, hlok⟩ := hall
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hlf
    rw [LeafF.okE_of_ne_ac (by decide)] at hlok
    simp only [not_or, not_exists, not_and] at hlok
    obtain ⟨hg, hflag⟩ := hlok
    have hflag' : nonInertB .assoc laws v l = false := by simpa using hflag
    obtain ⟨hXu, c₀, hc₀, hc₀u⟩ := (nonInertB_assoc_false_iff laws v l).1 hflag'
    obtain ⟨v₁, v₂, id, m, ls', o', hmem, hL, hveq, hk', hv', ho⟩ := RawViewL.refold hv hl
    -- the non-unit block of the leaf
    set g' := (dropU laws l.L).map Prod.fst with hg'
    have hg'mem : ∀ c, c ∈ g' ↔ c ∈ l.g ∧ laws.unit ≠ some c := by
      intro c
      simp [hg', map_fst_dropU, LeafL.g]
    have hgne : g' ≠ [] := by
      intro h
      have : c₀ ∈ g' := (hg'mem c₀).2 ⟨hc₀, hc₀u⟩
      rw [h] at this
      simp at this
    have hgdis : ∀ c ∈ g', c ∉ mid := fun c hc => hg c ((hg'mem c).1 hc).1
    have hsplit0 : (dropU laws v).map Prod.fst =
        (dropU laws v₁).map Prod.fst ++ g' ++ (dropU laws v₂).map Prod.fst := by
      rw [hveq, dropU_append, dropU_append, List.map_append, List.map_append]
    have hvmap' : (dropU laws (v₁ ++ (l.X, l.k) :: v₂)).map Prod.fst =
        (dropU laws v₁).map Prod.fst ++ l.X :: (dropU laws v₂).map Prod.fst := by
      rw [dropU_append, dropU_cons_of_ne laws hXu, List.map_append, List.map_cons]
    obtain ⟨u₀, s₀, hsplit, hlen, hu₀, hs₀, -⟩ := MatchV.assoc_inv hm
    have hu₀' : u₀ = u := by
      cases pre with
      | none =>
          simp only [SeqRestOk] at hu hu₀
          rw [hu, hu₀]
      | some rp =>
          simp only [SeqRestOk] at hu hu₀
          rw [hu] at hu₀
          exact (Option.some.inj hu₀).symm
    have hs₀' : s₀ = s := by
      cases suf with
      | none =>
          simp only [SeqRestOk] at hs hs₀
          rw [hs, hs₀]
      | some rs =>
          simp only [SeqRestOk] at hs hs₀
          rw [hs] at hs₀
          exact (Option.some.inj hs₀).symm
    subst u₀ s₀
    have hsplit' : (dropU laws v₁).map Prod.fst ++ g' ++ (dropU laws v₂).map Prod.fst =
        u ++ mid ++ s := by
      rw [← hsplit0, hsplit]
    have hmid : mid ≠ [] := by
      rintro rfl
      exact hne (List.length_eq_zero_iff.1 (by simpa using hlen))
    have hmidlen : 0 < mid.length := List.length_pos_of_ne_nil hmid
    -- the refold step's block
    have hblock : ((kids ctx.κ m.children).map Prod.fst).filter
        (fun c => decide (laws.unit ≠ some c)) = g' := by
      rw [hg', map_fst_dropU, hL, map_fst_scale]
    rcases split_block hgne hmid hgdis hsplit' with ⟨b, hub, hv₂⟩ | ⟨a, hv₁, hsa⟩
    · -- the leaf block lies in the prefix rest
      cases pre with
      | none =>
          simp only [SeqRestOk] at hu
          subst hu
          exact absurd (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 hub.symm).1).2 hgne
      | some rp =>
          simp only [SeqRestOk] at hu
          rw [hub] at hu
          have hne' : ∀ rs, suf = some rs → rs ≠ rp := fun rs h => (hdist rp rs rfl h).symm
          obtain ⟨-, hm₁⟩ := refold_assoc_pre (X := l.X) helems hne' hm hu hs
          have hv'map : (dropU laws (v₁ ++ (l.X, l.k) :: v₂)).map Prod.fst =
              ((dropU laws v₁).map Prod.fst ++ l.X :: b) ++ mid ++ s := by
            rw [hvmap', hv₂]; simp
          have hv₂len : 0 < (dropU laws v₂).length := by
            have := congrArg List.length hv₂
            simp only [List.length_map, List.length_append] at this
            omega
          have h2 : 2 ≤ (dropU laws (v₁ ++ (l.X, l.k) :: v₂)).length := by
            rw [dropU_append, dropU_cons_of_ne laws hXu]
            simp only [List.length_append, List.length_cons]; omega
          have hn' := normalize_assoc_node_of_len laws h2
          have hm₁' : MatchV ctx.G (.assoc f (some rp) args suf)
              (ofView .assoc (normalizeList .assoc laws (v₁ ++ (l.X, l.k) :: v₂)))
              (σ.setSeqRest rp ((dropU laws v₁).map Prod.fst ++ l.X :: b)) mid := by
            rw [ofView_assoc_normalizeList, hv'map]
            exact hm₁
          have hu₁ : SeqRestOk (σ.setSeqRest rp ((dropU laws v₁).map Prod.fst ++ l.X :: b))
              (some rp) ((dropU laws v₁).map Prod.fst ++ l.X :: b) := by
            simp [SeqRestOk, Binding.setSeqRest]
          obtain ⟨v'', ls'', o'', w'', σ'', u'', s'', hv'', ho'', hall'', hn'', hm'', hcls, hnode,
              hmult, hrest, hfin, hu'', hs'', hRu, hRs, -⟩ :=
            ih o' (by omega) _ _ _ _ _ _ hv' hn' hm₁' hu₁ (SeqRestOk_setSeqRest hne' hs)
          have hstep : RefoldStepAssocL ctx laws u ((dropU laws v₁).map Prod.fst ++ l.X :: b) :=
            ⟨id, m, l.X, (dropU laws v₁).map Prod.fst, b, hmem, by rw [hub, hblock], rfl⟩
          exact ⟨v'', ls'', o'', w'', σ'', u'', s'', hv'', by omega, hall'', hn'', hm'',
            hcls, hnode, hmult, hrest, hfin, hu'', hs'',
            Relation.ReflTransGen.head hstep hRu, hRs,
            fun _ => ⟨by omega, Or.inl (Relation.TransGen.head' hstep hRu)⟩⟩
    · -- the leaf block lies in the suffix rest
      cases suf with
      | none =>
          simp only [SeqRestOk] at hs
          subst hs
          exact absurd (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 hsa.symm).1).2 hgne
      | some rs =>
          simp only [SeqRestOk] at hs
          rw [hsa] at hs
          have hne' : ∀ rp, pre = some rp → rp ≠ rs := fun rp h => hdist rp rs h rfl
          obtain ⟨-, hm₁⟩ := refold_assoc_suf (X := l.X) helems hne' hm hu hs
          have hv'map : (dropU laws (v₁ ++ (l.X, l.k) :: v₂)).map Prod.fst =
              u ++ mid ++ (a ++ l.X :: (dropU laws v₂).map Prod.fst) := by
            rw [hvmap', hv₁]; simp
          have hv₁len : 0 < (dropU laws v₁).length := by
            have := congrArg List.length hv₁
            simp only [List.length_map, List.length_append] at this
            omega
          have h2 : 2 ≤ (dropU laws (v₁ ++ (l.X, l.k) :: v₂)).length := by
            rw [dropU_append, dropU_cons_of_ne laws hXu]
            simp only [List.length_append, List.length_cons]; omega
          have hn' := normalize_assoc_node_of_len laws h2
          have hm₁' : MatchV ctx.G (.assoc f pre args (some rs))
              (ofView .assoc (normalizeList .assoc laws (v₁ ++ (l.X, l.k) :: v₂)))
              (σ.setSeqRest rs (a ++ l.X :: (dropU laws v₂).map Prod.fst)) mid := by
            rw [ofView_assoc_normalizeList, hv'map]
            exact hm₁
          have hs₁ : SeqRestOk (σ.setSeqRest rs (a ++ l.X :: (dropU laws v₂).map Prod.fst))
              (some rs) (a ++ l.X :: (dropU laws v₂).map Prod.fst) := by
            simp [SeqRestOk, Binding.setSeqRest]
          obtain ⟨v'', ls'', o'', w'', σ'', u'', s'', hv'', ho'', hall'', hn'', hm'', hcls, hnode,
              hmult, hrest, hfin, hu'', hs'', hRu, hRs, -⟩ :=
            ih o' (by omega) _ _ _ _ _ _ hv' hn' hm₁' (SeqRestOk_setSeqRest hne' hu) hs₁
          have hstep : RefoldStepAssocL ctx laws s (a ++ l.X :: (dropU laws v₂).map Prod.fst) :=
            ⟨id, m, l.X, a, (dropU laws v₂).map Prod.fst, hmem, by rw [hsa, hblock], rfl⟩
          exact ⟨v'', ls'', o'', w'', σ'', u'', s'', hv'', by omega, hall'', hn'', hm'',
            hcls, hnode, hmult, hrest, hfin, hu'', hs'',
            hRu, Relation.ReflTransGen.head hstep hRs,
            fun _ => ⟨by omega, Or.inr (Relation.TransGen.head' hstep hRs)⟩⟩

/-- **Completeness of the engine's rule, Assoc, any laws** (the hypotheses of
`demand_laws_complete_assoc`). -/
theorem demand_engine_complete_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) {laws : Laws}
    {n : Node} {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .assoc laws v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s) :
    ∃ (w' : List (C × Nat)) (d : DemandL) (σ' : Binding) (u' s' : List C),
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsE .assoc mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssocL ctx laws u u' ∧ RefoldsAssocL ctx laws s s' := by
  obtain ⟨v', ls', o', w', σ', u', s', hv', -, hok, hn', hm', h1, h2, h3, h4, h5, hu', hs',
    hRu, hRs, -⟩ := eng_assoc_aux helems hne hdist o v ls w σ u s hv hn hm hu hs
  have hok' : ∀ l ∈ flagLeaves ctx.κ laws v' ls', l.okE ctx.κ mid := by rw [hκ]; exact hok
  obtain ⟨d, hd, hacc⟩ := acceptsE_of_tree hv' (by rw [hκ]; exact hn') hok'
  rw [hκ] at hacc
  exact ⟨w', d, σ', u', s', hd, hacc, hm', h1, h2, h3, h4, h5, hu', hs', hRu, hRs⟩

/-! ## Sets -/

/-- The classes of a view less the unit. -/
def classesU (laws : Laws) (v : List (C × Nat)) : Finset C :=
  ((dropU laws v).map Prod.fst).toFinset

theorem classesU_cons (laws : Laws) (X : C) (k : Nat) (v : List (C × Nat)) :
    classesU laws ((X, k) :: v) =
      if laws.unit ≠ some X then insert X (classesU laws v) else classesU laws v := by
  unfold classesU dropU
  rw [List.filter_cons]
  split <;> simp_all

theorem classesU_append (laws : Laws) (a b : List (C × Nat)) :
    classesU laws (a ++ b) = classesU laws a ∪ classesU laws b := by
  simp [classesU, dropU_append]

/-- Every raw view of `n` keeps two classes after the unit drop. -/
def TwoClassesL (laws : Laws) (ctx : Ctx) (n : Node) : Prop :=
  ∀ v ls o, RawViewL ctx n v ls o → 2 ≤ ((dropU laws v).map Prod.fst).toFinset.card

/-- The node `m` holds two classes less the unit. The engine's `add`
normalizes the children of a set node under the laws and stores no node
whose normal form is one class or the unit (`egraph.rs`, `add`:
`Normal::Single(g) => find(g)`, `Normal::Unit => unit_node`), and rebuild
re-normalizes a stored node whose children merged and merges it into that
class (`aci1.egg`: `Z ∋ And{X, s}`, `s ∪ Tru` merges `Z` with `X`). -/
def NodeTwoClassesL (laws : Laws) (ctx : Ctx) (m : Node) : Prop :=
  2 ≤ (classesU laws (kids ctx.κ m.children)).card

/-- The collapse invariant of the stored graph: every filed `f`-member holds
two classes less the unit. -/
def MembersTwoClassesL (laws : Laws) (ctx : Ctx) : Prop :=
  ∀ id m X, ctx.IsMember id m X → NodeTwoClassesL laws ctx m

/-- An opening tree keeps the classes of its positions or holds the classes
of an opened member's view, which has two by the collapse invariant. -/
theorem OTL.twoClasses {laws : Laws} {ctx : Ctx} (hm : MembersTwoClassesL laws ctx)
    {k : Nat} {P : Finset C} {ks v : List (C × Nat)} {ls : List LeafL} {o : Nat}
    (h : OTL ctx k P ks v ls o) :
    classesU laws v = classesU laws ks ∨ 2 ≤ (classesU laws v).card := by
  induction h with
  | nil => exact Or.inl rfl
  | keep _ ih =>
      rcases ih with ih | ih
      · left
        rw [classesU_cons, classesU_cons, ih]
      · right
        refine le_trans ih (Finset.card_le_card ?_)
        rw [classesU_cons]
        split
        · exact Finset.subset_insert _ _
        · exact le_rfl
  | opn _ hmem _ _ ih₁ _ =>
      right
      have h1 : 2 ≤ (classesU laws _).card :=
        ih₁.elim (fun e => e ▸ hm _ _ _ hmem) id
      refine le_trans h1 (Finset.card_le_card ?_)
      rw [classesU_append]
      exact Finset.subset_union_left

/-- **`TwoClassesL` from the collapse invariant**: when every filed
`f`-member and the node itself hold two classes less the unit, so does
every raw view of the node. -/
theorem twoClassesL_of_members {laws : Laws} {ctx : Ctx} {n : Node}
    (hm : MembersTwoClassesL laws ctx) (hn : NodeTwoClassesL laws ctx n) :
    TwoClassesL laws ctx n := by
  intro v ls o hv
  change 2 ≤ (classesU laws v).card
  rcases OTL.twoClasses hm hv with h | h
  · rw [h]; exact hn
  · exact h

/-- The ACI refold induction with the engine's leaf test (no opened-class
clause), under `TwoClassesL`. -/
theorem eng_aci_aux {ctx : Ctx} {laws : Laws} {n : Node} {f : Sym} {elems : List Pat} {r : Var}
    {taken : List C} (htwo : TwoClassesL laws ctx n) (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafL) (w : List (C × Nat)) (σ : Binding),
      RawViewL ctx n v ls o → normalize .aci laws v = .node w →
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken →
      ∃ (v' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (w' : List (C × Nat)) (rest' : Finset C),
        RawViewL ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ flagLeaves .aci laws v' ls', l.okE .aci taken) ∧
        normalize .aci laws v' = .node w' ∧
        MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
        RefoldsACIT ctx taken ((((dropU laws v).map Prod.fst).toFinset).filter (fun c => c ∉ taken))
          rest' := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ hv hn hm
  have hw := normalize_aci_node_eq hn
  subst hw
  have hview : ofView .aci (normalizeList .aci laws v) = .set ((dropU laws v).map Prod.fst).toFinset :=
    ofView_aci_normalizeList laws v
  rw [hview] at hm
  by_cases hall : ∀ l ∈ flagLeaves .aci laws v ls, l.okE .aci taken
  · have hrest := MatchV.aci_rest hm
    refine ⟨v, ls, o, _, _, hv, le_rfl, hall, hn, ?_, Relation.ReflTransGen.refl⟩
    rw [Binding.setSetRest_self hrest, hview]
    exact hm
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨lf, hlf, hlok⟩ := hall
    simp only [flagLeaves, List.mem_map] at hlf
    obtain ⟨l, hl, rfl⟩ := hlf
    rw [LeafF.okE_of_ne_ac (by decide)] at hlok
    simp only [not_or, not_exists, not_and] at hlok
    obtain ⟨hg, hflag⟩ := hlok
    have hflag' : nonInertB .aci laws v l = false := by simpa using hflag
    have hunit : laws.unit ≠ some l.X := (nonInertB_aci_false_iff laws v l).1 hflag'
    obtain ⟨v₁, v₂, id, m, ls', o', hmem, hL, hveq, hk', hv', ho⟩ := RawViewL.refold hv hl
    have hleaf : ∀ e ∈ dropU laws l.L, e.1 ∉ taken := fun e he => hg e.1 (mem_dropU_g he)
    have hd : dropU laws v = dropU laws v₁ ++ dropU laws l.L ++ dropU laws v₂ := by
      rw [hveq, dropU_append, dropU_append]
    have hd' : dropU laws (v₁ ++ (l.X, l.k) :: v₂) = dropU laws v₁ ++ (l.X, l.k) :: dropU laws v₂ := by
      rw [dropU_append, dropU_cons_of_ne laws hunit]
    have hm' : MatchV ctx.G (.aci f elems (some r))
        (.set ((dropU laws v₁ ++ dropU laws l.L ++ dropU laws v₂).map Prod.fst).toFinset)
        σ taken := by
      rw [hd] at hm; exact hm
    have hm₁ := refold_aci (X := l.X) (k' := l.k) helems hm' hleaf
    have hn' := normalize_aci_node_of_card laws (htwo _ _ _ hv')
    have hview' : ofView .aci (normalizeList .aci laws (v₁ ++ (l.X, l.k) :: v₂)) =
        .set ((dropU laws v₁ ++ (l.X, l.k) :: dropU laws v₂).map Prod.fst).toFinset := by
      rw [ofView_aci_normalizeList, hd']
    rw [← hview'] at hm₁
    obtain ⟨v'', ls'', o'', w'', rest'', hv'', ho'', hall'', hn'', hm'', hR''⟩ :=
      ih o' (by omega) _ _ _ _ hv' hn' hm₁
    have hstep : RefoldStepACIT ctx taken
        ((((dropU laws v).map Prod.fst).toFinset).filter (fun c => c ∉ taken))
        ((((dropU laws (v₁ ++ (l.X, l.k) :: v₂)).map Prod.fst).toFinset).filter (fun c => c ∉ taken)) := by
      refine ⟨id, m, l.X,
        (((dropU laws l.L).map Prod.fst).filter
          (fun c => c ∉ (dropU laws v₁ ++ dropU laws v₂).map Prod.fst)).toFinset, hmem, ?_, ?_⟩
      · intro c hc
        rw [List.mem_toFinset] at hc ⊢
        have hc' := (List.mem_filter.1 hc).1
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc'
        have := mem_dropU_g he
        unfold LeafL.g at this
        rw [hL, map_fst_scale] at this
        exact this
      · rw [hd', hd]
        by_cases hX : l.X ∈ taken
        · simp only [hX, ↓reduceIte]
          exact refold_aci_rest_taken hleaf hX
        · simp only [hX, ↓reduceIte]
          exact refold_aci_rest hleaf hX
    refine ⟨v'', ls'', o'', w'', rest'', hv'', by omega, hall'', hn'', ?_,
      Relation.ReflTransGen.head hstep hR''⟩
    rw [Binding.setSetRest_setSetRest] at hm''
    exact hm''

/-- **Completeness of the engine's rule, ACI, any laws**, under the collapse
invariant (`MembersTwoClassesL`, and the node itself). -/
theorem demand_engine_complete_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {laws : Laws} {n : Node}
    (hinv : MembersTwoClassesL laws ctx) (hroot : NodeTwoClassesL laws ctx n)
    {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .aci laws v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x)
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandL) (rest₀ rest' : Finset C),
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsE .aci taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ RefoldsACIT ctx taken rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', hR⟩ :=
    eng_aci_aux (twoClassesL_of_members hinv hroot) helems o v ls w σ hv hn hm
  have hok' : ∀ l ∈ flagLeaves ctx.κ laws v' ls', l.okE ctx.κ taken := by rw [hκ]; exact hok
  obtain ⟨d, hd, hacc⟩ := acceptsE_of_tree hv' (by rw [hκ]; exact hn') hok'
  rw [hκ] at hacc
  refine ⟨w', d, _, rest', hd, hacc, hm', ?_, hR⟩
  rw [normalize_aci_node_eq hn, ofView_aci_normalizeList] at hm
  exact MatchV.aci_rest hm

end Semper.EMatch.Flatten
