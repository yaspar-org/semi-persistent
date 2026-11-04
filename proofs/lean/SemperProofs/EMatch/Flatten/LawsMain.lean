import SemperProofs.EMatch.Flatten.Laws

/-!
# `:flatten` views under laws: completeness of the demand rule with laws

For each kind and any `Laws` (identity, nilpotent, inverse, their
composition), a match of an n-ary atom (item patterns variables, a rest
variable, at least one item) on the canonical view of **any** opening tree
refolds, by closing unsatisfied leaves, to a match on the view of a tree
whose every flagged leaf satisfies `LeafF.okL`; that view is emitted by
`enumerateL` with a demand that `acceptsLaws` the taken classes. The item
bindings are unchanged; the rest is a refolding (`RefoldsACL`, `RefoldsACI`,
`RefoldsAssocL`).

Each refold step closes a leaf the rule rejects: its opened class is not
taken, its group holds no taken class, and the refold is inert
(`InertAC` / `InertACI` / `InertAssoc`, Laws.lean). Inertness is exactly
what the step needs: the taken classes keep their counts
(`refold_ac_inert`), and the closed class survives normalization
(`preNF_refoldCount_ne_zero`), so the refolded view is a node.

Contents: `laws_ac_aux`, `laws_aci_aux`, `laws_assoc_aux` (the refold
inductions), `demand_laws_complete_{ac,aci,assoc}`,
`demand_laws_no_redundancy_{ac,aci,assoc}`.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Reading an unsatisfied flagged leaf -/

theorem not_okL_iff {κ : FlatKind} {laws : Laws} {v : List (C × Nat)} {ls : List LeafL}
    {taken : List C} (h : ¬ ∀ l ∈ flagLeaves κ laws v ls, l.okL taken) :
    ∃ l ∈ ls, l.X ∉ taken ∧ (∀ c ∈ l.g, c ∉ taken) ∧ nonInertB κ laws v l = false := by
  simp only [flagLeaves, List.mem_map, not_forall, exists_prop, forall_exists_index, and_imp] at h
  obtain ⟨_, l, hl, rfl, hnot⟩ := h
  refine ⟨l, hl, ?_, ?_, ?_⟩
  · exact fun h => hnot (Or.inl h)
  · exact fun c hc h => hnot (Or.inr (Or.inl ⟨c, hc, h⟩))
  · simpa using fun h => hnot (Or.inr (Or.inr h))

/-! ## AC -/

theorem normalize_ac_node_eq {laws : Laws} {v w : List (C × Nat)}
    (hn : normalize .ac laws v = .node w) : w = normalizeList .ac laws v := by
  unfold normalize at hn
  rw [classify_node_iff] at hn
  exact hn.1.symm

/-- The AC refold induction under laws. -/
theorem laws_ac_aux {ctx : Ctx} {laws : Laws} {n : Node} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {taken : List C} (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ []) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafL) (w : List (C × Nat)) (σ : Binding),
      RawViewL ctx n v ls o → normalize .ac laws v = .node w →
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken →
      ∃ (v' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (w' : List (C × Nat))
        (rest' : Multiset C),
        RawViewL ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ flagLeaves .ac laws v' ls', l.okL taken) ∧
        normalize .ac laws v' = .node w' ∧
        MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
        RefoldsACL ctx laws taken
          ((ofEntries (normalizeList .ac laws v)).filter (fun c => c ∉ taken)) rest' ∧
        (¬ (∀ l ∈ flagLeaves .ac laws v ls, l.okL taken) → o' < o ∧
          Relation.TransGen (RefoldStepACL ctx laws taken)
            ((ofEntries (normalizeList .ac laws v)).filter (fun c => c ∉ taken)) rest') := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ hv hn hm
  have hw : w = normalizeList .ac laws v := normalize_ac_node_eq hn
  subst hw
  rw [ofView_ac_normalizeList] at hm
  by_cases hall : ∀ l ∈ flagLeaves .ac laws v ls, l.okL taken
  · have hrest := MatchV.ac_rest hm
    refine ⟨v, ls, o, _, _, hv, le_rfl, hall, hn, ?_, Relation.ReflTransGen.refl,
      fun h => absurd hall h⟩
    rw [Binding.setRest_self hrest, ofView_ac_normalizeList]
    exact hm
  · obtain ⟨l, hl, hX, hg, hflag⟩ := not_okL_iff hall
    have hin : InertAC laws v l := (nonInertB_ac_false_iff laws v l).1 hflag
    obtain ⟨v₁, v₂, id, m, ls', o', hmem, hL, hveq, hk, hv', ho⟩ := RawViewL.refold hv hl
    subst hveq
    -- the normal form of the refolded view
    obtain ⟨hagree, hXcnt, -⟩ := refold_ac_inert laws hin
    have hX0 : (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).count l.X ≠ 0 := by
      rw [hXcnt]; exact preNF_refoldCount_ne_zero hin hk
    have hcnt : ∀ t ∈ taken,
        (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).count t =
          (ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂))).count t := by
      intro t ht
      apply hagree
      simp only [LeafL.touched, List.mem_cons, not_or]
      exact ⟨fun h => hX (h ▸ ht), fun h => hg t h ht⟩
    have hm₁ := MatchV.ac_transfer helems hm hcnt
    -- the refolded view is a node: a taken class and `X` are two distinct classes
    obtain ⟨t, ht⟩ := taken_ne_nil_of_match hm₁ hne
    have htv : t ∈ ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂)) :=
      MatchV.ac_mem hm₁ t ht
    have hXv : l.X ∈ ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂)) :=
      Multiset.count_ne_zero.1 hX0
    have htX : t ≠ l.X := fun h => hX (h ▸ ht)
    have hn' := normalize_ac_node_of_two laws htX htv hXv
    rw [← ofView_ac_normalizeList] at hm₁
    obtain ⟨v'', ls'', o'', w'', rest'', hv'', ho'', hall'', hn'', hm'', hR'', -⟩ :=
      ih o' (by omega) _ _ _ _ hv' hn' hm₁
    have hstep : RefoldStepACL ctx laws taken
        ((ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂))).filter (fun c => c ∉ taken))
        ((ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).filter
          (fun c => c ∉ taken)) := by
      refine ⟨id, m, l.X, l.k, ofEntries (v₁ ++ l.L ++ v₂), hmem, hk, ?_, ?_, ?_⟩
      · rw [← hL]
        simp only [ofEntries_append]
        exact le_trans (Multiset.le_add_left _ _) (Multiset.le_add_right _ _)
      · rw [nfAC_ofEntries]
      · rw [← hL, ofEntries_refold, nfAC_ofEntries]
    refine ⟨v'', ls'', o'', w'', rest'', hv'', by omega, hall'', hn'', ?_,
      Relation.ReflTransGen.head hstep hR'',
      fun _ => ⟨by omega, Relation.TransGen.head' hstep hR''⟩⟩
    rw [Binding.setRest_setRest] at hm''
    exact hm''

/-- **Completeness under laws, AC.** Any match of an AC atom (item patterns
variables, at least one item, a rest variable) on the canonical view of any
opening tree of `n`, under any laws, is, up to refolding the rest, a match
on an emitted view whose demand under laws accepts the taken classes. The
item bindings are those of `σ`; `rest'` is a refolding of `σ`'s rest. -/
theorem demand_laws_complete_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {laws : Laws} {n : Node}
    {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .ac laws v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandL) (rest₀ rest' : Multiset C),
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ RefoldsACL ctx laws taken rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', hR, -⟩ :=
    laws_ac_aux helems hne o v ls w σ hv hn hm
  obtain ⟨d, hd, hacc⟩ := acceptsLaws_of_tree hv' (by rw [hκ]; exact hn') (by rw [hκ]; exact hok)
  refine ⟨w', d, _, rest', hd, hacc, hm', ?_, hR⟩
  rw [normalize_ac_node_eq hn, ofView_ac_normalizeList] at hm
  exact MatchV.ac_rest hm

/-- **No redundancy under laws, AC.** The rule rejects a match on a tree
(some flagged leaf not `okL`) only when a proper refolding of it (strictly
fewer openings, at least one refold step on the rest) is a match on a tree
the rule accepts. -/
theorem demand_laws_no_redundancy_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {laws : Laws} {n : Node}
    {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .ac laws v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken)
    (hrej : ¬ ∀ l ∈ flagLeaves .ac laws v ls, l.okL taken) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (d : DemandL)
      (rest₀ rest' : Multiset C),
      RawViewL ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ flagLeaves .ac laws v' ls', l.okL taken) ∧
      normalize .ac laws v' = .node w' ∧
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ Relation.TransGen (RefoldStepACL ctx laws taken) rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', -, hlt⟩ :=
    laws_ac_aux helems hne o v ls w σ hv hn hm
  obtain ⟨hlt, hT⟩ := hlt hrej
  obtain ⟨d, hd, hacc⟩ := acceptsLaws_of_tree hv' (by rw [hκ]; exact hn') (by rw [hκ]; exact hok)
  refine ⟨v', w', ls', o', d, _, rest', hv', hlt, hok, hn', hd, hacc, hm', ?_, hT⟩
  rw [normalize_ac_node_eq hn, ofView_ac_normalizeList] at hm
  exact MatchV.ac_rest hm


/-! ## ACI -/

/-! ## ACI: the refold induction under laws -/

theorem normalize_aci_node_eq {laws : Laws} {v w : List (C × Nat)}
    (hn : normalize .aci laws v = .node w) : w = normalizeList .aci laws v := by
  unfold normalize at hn
  rw [classify_node_iff] at hn
  exact hn.1.symm

theorem mem_dropU_g {laws : Laws} {l : LeafL} {e : C × Nat} (he : e ∈ dropU laws l.L) :
    e.1 ∈ l.g :=
  List.mem_map_of_mem (List.mem_filter.1 he).1

theorem laws_aci_aux {ctx : Ctx} {laws : Laws} {n : Node} {f : Sym} {elems : List Pat} {r : Var}
    {taken : List C} (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) (hne : elems ≠ []) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafL) (w : List (C × Nat)) (σ : Binding),
      RawViewL ctx n v ls o → normalize .aci laws v = .node w →
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken →
      ∃ (v' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (w' : List (C × Nat)) (rest' : Finset C),
        RawViewL ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ flagLeaves .aci laws v' ls', l.okL taken) ∧
        normalize .aci laws v' = .node w' ∧
        MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
        RefoldsACI ctx ((((dropU laws v).map Prod.fst).toFinset).filter (fun c => c ∉ taken)) rest' ∧
        (¬ (∀ l ∈ flagLeaves .aci laws v ls, l.okL taken) → o' < o ∧
          Relation.TransGen (RefoldStepACI ctx)
            ((((dropU laws v).map Prod.fst).toFinset).filter (fun c => c ∉ taken)) rest') := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ hv hn hm
  have hw := normalize_aci_node_eq hn
  subst hw
  have hview : ofView .aci (normalizeList .aci laws v) = .set ((dropU laws v).map Prod.fst).toFinset :=
    ofView_aci_normalizeList laws v
  rw [hview] at hm
  by_cases hall : ∀ l ∈ flagLeaves .aci laws v ls, l.okL taken
  · have hrest := MatchV.aci_rest hm
    refine ⟨v, ls, o, _, _, hv, le_rfl, hall, hn, ?_, Relation.ReflTransGen.refl,
      fun h => absurd hall h⟩
    rw [Binding.setSetRest_self hrest, hview]
    exact hm
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨lf, hlf, hlok⟩ := hall
    simp only [flagLeaves, List.mem_map] at hlf
    obtain ⟨l, hl, rfl⟩ := hlf
    simp only [LeafF.okL, not_or, not_exists, not_and] at hlok
    obtain ⟨hX, hg, hflag⟩ := hlok
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
    obtain ⟨t, ht⟩ := taken_ne_nil_of_match_aci hm₁ hne
    have htv : t ∈ (dropU laws v₁ ++ (l.X, l.k) :: dropU laws v₂).map Prod.fst :=
      List.mem_toFinset.1 (MatchV.aci_mem hm₁ t ht)
    have hXv : l.X ∈ (dropU laws v₁ ++ (l.X, l.k) :: dropU laws v₂).map Prod.fst := by simp
    have htX : t ≠ l.X := fun h => hX (h ▸ ht)
    have hcard : 2 ≤ ((dropU laws (v₁ ++ (l.X, l.k) :: v₂)).map Prod.fst).toFinset.card := by
      rw [hd']
      have hsub : ({t, l.X} : Finset C) ⊆
          ((dropU laws v₁ ++ (l.X, l.k) :: dropU laws v₂).map Prod.fst).toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact List.mem_toFinset.2 htv
        · exact List.mem_toFinset.2 hXv
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair htX] at this
    have hn' := normalize_aci_node_of_card laws hcard
    have hview' : ofView .aci (normalizeList .aci laws (v₁ ++ (l.X, l.k) :: v₂)) =
        .set ((dropU laws v₁ ++ (l.X, l.k) :: dropU laws v₂).map Prod.fst).toFinset := by
      rw [ofView_aci_normalizeList, hd']
    rw [← hview'] at hm₁
    obtain ⟨v'', ls'', o'', w'', rest'', hv'', ho'', hall'', hn'', hm'', hR'', -⟩ :=
      ih o' (by omega) _ _ _ _ hv' hn' hm₁
    have hstep : RefoldStepACI ctx ((((dropU laws v).map Prod.fst).toFinset).filter (fun c => c ∉ taken))
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
        exact refold_aci_rest hleaf hX
    refine ⟨v'', ls'', o'', w'', rest'', hv'', by omega, hall'', hn'', ?_,
      Relation.ReflTransGen.head hstep hR'',
      fun _ => ⟨by omega, Relation.TransGen.head' hstep hR''⟩⟩
    rw [Binding.setSetRest_setSetRest] at hm''
    exact hm''

/-! ## ACI: the main theorems under laws -/

theorem demand_laws_complete_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {laws : Laws} {n : Node}
    {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .aci laws v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandL) (rest₀ rest' : Finset C),
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ RefoldsACI ctx rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', hR, -⟩ :=
    laws_aci_aux helems hne o v ls w σ hv hn hm
  obtain ⟨d, hd, hacc⟩ := acceptsLaws_of_tree hv' (by rw [hκ]; exact hn') (by rw [hκ]; exact hok)
  refine ⟨w', d, _, rest', hd, hacc, hm', ?_, hR⟩
  rw [normalize_aci_node_eq hn, ofView_aci_normalizeList] at hm
  exact MatchV.aci_rest hm

theorem demand_laws_no_redundancy_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {laws : Laws} {n : Node}
    {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .aci laws v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken)
    (hrej : ¬ ∀ l ∈ flagLeaves .aci laws v ls, l.okL taken) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (d : DemandL) (rest₀ rest' : Finset C),
      RawViewL ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ flagLeaves .aci laws v' ls', l.okL taken) ∧
      normalize .aci laws v' = .node w' ∧
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ Relation.TransGen (RefoldStepACI ctx) rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', -, hlt⟩ :=
    laws_aci_aux helems hne o v ls w σ hv hn hm
  obtain ⟨hlt, hT⟩ := hlt hrej
  obtain ⟨d, hd, hacc⟩ := acceptsLaws_of_tree hv' (by rw [hκ]; exact hn') (by rw [hκ]; exact hok)
  refine ⟨v', w', ls', o', d, _, rest', hv', hlt, hok, hn', hd, hacc, hm', ?_, hT⟩
  rw [normalize_aci_node_eq hn, ofView_aci_normalizeList] at hm
  exact MatchV.aci_rest hm


/-! ## Assoc -/

/-! ## Assoc: the refold induction under laws -/

theorem laws_assoc_aux {ctx : Ctx} {laws : Laws} {n : Node} {f : Sym} {pre suf : Option Var}
    {args : List Pat} {mid : List C} (helems : ∀ p ∈ args, ∃ x, p = Pat.var x)
    (hne : args ≠ []) (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafL) (w : List (C × Nat)) (σ : Binding)
      (u s : List C),
      RawViewL ctx n v ls o → normalize .assoc laws v = .node w →
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid →
      SeqRestOk σ pre u → SeqRestOk σ suf s →
      ∃ (v' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (w' : List (C × Nat))
        (σ' : Binding) (u' s' : List C),
        RawViewL ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ flagLeaves .assoc laws v' ls', l.okL mid) ∧
        normalize .assoc laws v' = .node w' ∧
        MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
        σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
        σ'.finRest = σ.finRest ∧
        SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
        RefoldsAssocL ctx laws u u' ∧ RefoldsAssocL ctx laws s s' ∧
        (¬ (∀ l ∈ flagLeaves .assoc laws v ls, l.okL mid) → o' < o ∧
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
  by_cases hall : ∀ l ∈ flagLeaves .assoc laws v ls, l.okL mid
  · refine ⟨v, ls, o, _, σ, u, s, hv, le_rfl, hall, hn, ?_, rfl, rfl, rfl, rfl, rfl, hu, hs,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, fun h => absurd hall h⟩
    rw [ofView_assoc_normalizeList]
    exact hm
  · simp only [not_forall] at hall
    obtain ⟨lf, hlf, hlok⟩ := hall
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hlf
    simp only [LeafF.okL, not_or, not_exists, not_and] at hlok
    obtain ⟨hX, hg, hflag⟩ := hlok
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

/-! ## Assoc: completeness and no redundancy under laws -/

/-- **Completeness, Assoc, under laws.** No `NoNullary` hypothesis: a leaf
whose children are all units is flagged non-inert and accepted. -/
theorem demand_laws_complete_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) {laws : Laws}
    {n : Node} {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .assoc laws v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s) :
    ∃ (w' : List (C × Nat)) (d : DemandL) (σ' : Binding) (u' s' : List C),
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssocL ctx laws u u' ∧ RefoldsAssocL ctx laws s s' := by
  obtain ⟨v', ls', o', w', σ', u', s', hv', -, hok, hn', hm', h1, h2, h3, h4, h5, hu', hs',
    hRu, hRs, -⟩ := laws_assoc_aux helems hne hdist o v ls w σ u s hv hn hm hu hs
  have hok' : ∀ l ∈ flagLeaves ctx.κ laws v' ls', l.okL mid := by rw [hκ]; exact hok
  obtain ⟨d, hd, hacc⟩ := acceptsLaws_of_tree hv' (by rw [hκ]; exact hn') hok'
  exact ⟨w', d, σ', u', s', hd, hacc, hm', h1, h2, h3, h4, h5, hu', hs', hRu, hRs⟩

/-- **No redundancy, Assoc, under laws.** -/
theorem demand_laws_no_redundancy_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) {laws : Laws}
    {n : Node} {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .assoc laws v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s)
    (hrej : ¬ ∀ l ∈ flagLeaves .assoc laws v ls, l.okL mid) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafL) (o' : Nat) (d : DemandL) (σ' : Binding)
      (u' s' : List C),
      RawViewL ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ flagLeaves .assoc laws v' ls', l.okL mid) ∧
      normalize .assoc laws v' = .node w' ∧
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssocL ctx laws u u' ∧ RefoldsAssocL ctx laws s s' ∧
      (Relation.TransGen (RefoldStepAssocL ctx laws) u u' ∨
        Relation.TransGen (RefoldStepAssocL ctx laws) s s') := by
  obtain ⟨v', ls', o', w', σ', u', s', hv', -, hok, hn', hm', h1, h2, h3, h4, h5, hu', hs',
    hRu, hRs, hlt⟩ := laws_assoc_aux helems hne hdist o v ls w σ u s hv hn hm hu hs
  obtain ⟨hlt, hT⟩ := hlt hrej
  have hok' : ∀ l ∈ flagLeaves ctx.κ laws v' ls', l.okL mid := by rw [hκ]; exact hok
  obtain ⟨d, hd, hacc⟩ := acceptsLaws_of_tree hv' (by rw [hκ]; exact hn') hok'
  exact ⟨v', w', ls', o', d, σ', u', s', hv', hlt, hok, hn', hd, hacc, hm', h1, h2, h3, h4, h5,
    hu', hs', hRu, hRs, hT⟩


end Semper.EMatch.Flatten
