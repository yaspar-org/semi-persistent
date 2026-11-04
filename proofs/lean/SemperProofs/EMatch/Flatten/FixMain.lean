import SemperProofs.EMatch.Flatten.Fix

/-!
# `:flatten` views: completeness of the corrected demand rule

For each kind, a match of an n-ary atom (item patterns variables, a rest
variable present, at least one item) on the canonical view of **any**
opening tree refolds, by closing unhit leaves whose opened class is not
taken, to a match on the view of a tree whose every leaf satisfies
`LeafX.ok`; that tree's view is emitted by `enumerateX` with a demand that
`acceptsFix` the taken classes. The item bindings are unchanged and the
rest is a refolding of the original rest (`RefoldsAC` etc.).

Contents: the refold inductions `fix_ac_aux`, `fix_aci_aux`, `fix_assoc_aux`
(the last under `NoNullary`, with the list lemma `split_block`); the
interpreter fragment with the corrected rule (`FEnvX`, `runFStepX`, `runFX`)
and its soundness/completeness against `MatchFlatX`
(`flatten_fix_{sound,complete}_{ac,aci,assoc}`); the main theorems
`demand_fix_complete_{ac,aci,assoc}` and `demand_fix_no_redundancy_{ac,aci,assoc}`;
`accepts_imp_acceptsFix` (the corrected rule accepts whatever the original did).

Degenerate refolds: closing a leaf can only produce a raw view that
normalizes to a non-node when the match has no item (`elems ≠ []` /
`args ≠ []` exclude it: a taken class and the closed class, which carries a
positive multiplicity, are two distinct elements). For Assoc, a nullary
`f`-member (empty leaf group) could sit inside the fixed middle, so
`NoNullary` is assumed. Only `Laws.free` is treated (see the status file for
the laws counterexample).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Normal forms with two distinct classes are nodes -/

theorem normalize_ac_free_node_of_two {v : List (C × Nat)} {a b : C} (hab : a ≠ b)
    (ha : a ∈ ofEntries v) (hb : b ∈ ofEntries v) :
    normalize .ac Laws.free v = .node (coalesce v) := by
  refine normalize_free_node.2 ⟨rfl, ?_, ?_⟩
  · intro h
    have : ofEntries v = 0 := by rw [← ofEntries_coalesce, h]; rfl
    rw [this] at ha
    simp at ha
  · intro c h
    have : ofEntries v = {c} := by rw [← ofEntries_coalesce, h]; simp [ofEntries]
    rw [this] at ha hb
    exact hab ((Multiset.mem_singleton.1 ha).trans (Multiset.mem_singleton.1 hb).symm)

theorem normalize_aci_free_node_of_two {v : List (C × Nat)} {a b : C} (hab : a ≠ b)
    (ha : a ∈ v.map Prod.fst) (hb : b ∈ v.map Prod.fst) :
    normalize .aci Laws.free v = .node (dedupAci v) := by
  have hlen : (dedupAci v).length = (v.map Prod.fst).toFinset.card := by simp [dedupAci]
  have h2 : 2 ≤ (v.map Prod.fst).toFinset.card := by
    have hsub : ({a, b} : Finset C) ⊆ (v.map Prod.fst).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact List.mem_toFinset.2 ha
      · exact List.mem_toFinset.2 hb
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hab] at this
  refine normalize_free_node.2 ⟨rfl, ?_, ?_⟩
  · intro h; rw [h] at hlen; simp at hlen; omega
  · intro c h; rw [h] at hlen; simp at hlen; omega

theorem normalize_assoc_free_node_of_len {v : List (C × Nat)} (h : 2 ≤ v.length) :
    normalize .assoc Laws.free v = .node v := by
  refine normalize_free_node.2 ⟨rfl, ?_, ?_⟩
  · rintro rfl; simp at h
  · rintro c rfl; simp at h

/-! ## Binding helpers -/

theorem Binding.setRest_self {σ : Binding} {r : Var} {m : Multiset C} (h : σ.rest r = some m) :
    σ.setRest r m = σ := by
  cases σ
  simp only [Binding.setRest] at h ⊢
  simp [← h]

theorem Binding.setRest_setRest (σ : Binding) (r : Var) (m m' : Multiset C) :
    (σ.setRest r m).setRest r m' = σ.setRest r m' := by
  simp [Binding.setRest, Function.update_idem]

theorem Binding.setSetRest_self {σ : Binding} {r : Var} {s : Finset C}
    (h : σ.finRest r = some s) : σ.setSetRest r s = σ := by
  cases σ
  simp only [Binding.setSetRest] at h ⊢
  simp [← h]

theorem Binding.setSetRest_setSetRest (σ : Binding) (r : Var) (s s' : Finset C) :
    (σ.setSetRest r s).setSetRest r s' = σ.setSetRest r s' := by
  simp [Binding.setSetRest, Function.update_idem]

/-! ## Multiset helpers -/

theorem filter_ofEntries_leaf {v₁ v₂ leaf : List (C × Nat)} {taken : List C}
    (hleaf : ∀ e ∈ leaf, e.1 ∉ taken) :
    (ofEntries (v₁ ++ leaf ++ v₂)).filter (fun c => c ∉ taken) =
      (ofEntries v₁).filter (fun c => c ∉ taken) + ofEntries leaf +
        (ofEntries v₂).filter (fun c => c ∉ taken) := by
  have hl : (ofEntries leaf).filter (fun c => c ∉ taken) = ofEntries leaf := by
    rw [Multiset.filter_eq_self]
    intro c hc
    obtain ⟨e, he, hec⟩ := exists_mem_ofEntries hc
    rw [← hec]
    exact hleaf e he
  simp only [ofEntries_append, Multiset.filter_add, hl]

theorem leaf_le_filter {v₁ v₂ leaf : List (C × Nat)} {taken : List C}
    (hleaf : ∀ e ∈ leaf, e.1 ∉ taken) :
    ofEntries leaf ≤ (ofEntries (v₁ ++ leaf ++ v₂)).filter (fun c => c ∉ taken) := by
  rw [filter_ofEntries_leaf hleaf]
  exact le_trans (Multiset.le_add_left _ _) (Multiset.le_add_right _ _)

theorem taken_ne_nil_of_match {G : Graph} {f : Sym} {elems : List (Pat × Mult)}
    {rest : Option Var} {ch : Children} {σ : Binding} {taken : List C}
    (hm : MatchV G (.ac f elems rest) ch σ taken) (hne : elems ≠ []) : ∃ t, t ∈ taken := by
  cases hm with
  | ac _ hlen _ _ _ _ =>
    cases taken with
    | nil => exact absurd (List.length_eq_zero_iff.1 hlen) hne
    | cons t _ => exact ⟨t, List.mem_cons_self ..⟩

theorem MatchV.ac_mem {G : Graph} {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var}
    {m : Multiset C} {σ : Binding} {taken : List C}
    (hm : MatchV G (.ac f elems rest) (.mset m) σ taken) : ∀ c ∈ taken, c ∈ m := by
  cases hm with
  | ac _ _ hmem _ _ _ => exact hmem

theorem MatchV.ac_rest {G : Graph} {f : Sym} {elems : List (Pat × Mult)} {r : Var}
    {m : Multiset C} {σ : Binding} {taken : List C}
    (hm : MatchV G (.ac f elems (some r)) (.mset m) σ taken) :
    σ.rest r = some (m.filter (fun c => c ∉ taken)) := by
  cases hm with
  | ac _ _ _ _ _ hrest => exact hrest

/-! ## AC -/

/-- The AC refold induction. Hypotheses: item patterns are variables, at
least one item, a rest variable, laws-free operator. The conclusion gives a
tree with at most as many openings whose every leaf is `ok`, the match on
its view with the same item bindings and a refolded rest, and strictly
fewer openings (with at least one refold step) when the original tree was
not accepted. -/
theorem fix_ac_aux {ctx : Ctx} {n : Node} {f : Sym} {elems : List (Pat × Mult)} {r : Var}
    {taken : List C} (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ []) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafX) (w : List (C × Nat)) (σ : Binding),
      RawViewX ctx n v ls o → normalize .ac Laws.free v = .node w →
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken →
      ∃ (v' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (w' : List (C × Nat))
        (rest' : Multiset C),
        RawViewX ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ ls', l.ok taken) ∧
        normalize .ac Laws.free v' = .node w' ∧
        MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
        RefoldsAC ctx ((ofEntries v).filter (fun c => c ∉ taken)) rest' ∧
        (¬ (∀ l ∈ ls, l.ok taken) → o' < o ∧
          Relation.TransGen (RefoldStepAC ctx) ((ofEntries v).filter (fun c => c ∉ taken)) rest') := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ hv hn hm
  have hview : ofView .ac w = .mset (ofEntries v) := by simp [ofView, ofEntries_free_ac hn]
  rw [hview] at hm
  by_cases hall : ∀ l ∈ ls, l.ok taken
  · have hrest := MatchV.ac_rest hm
    refine ⟨v, ls, o, w, _, hv, le_rfl, hall, hn, ?_, Relation.ReflTransGen.refl,
      fun h => absurd hall h⟩
    rw [Binding.setRest_self hrest, hview]
    exact hm
  · simp only [not_forall] at hall
    obtain ⟨l, hl, hlok⟩ := hall
    have hX : l.1 ∉ taken := fun h => hlok (Or.inl h)
    have hg : ∀ c ∈ l.2, c ∉ taken := fun c hc h => hlok (Or.inr ⟨c, hc, h⟩)
    obtain ⟨v₁, v₂, k', id, m, ls', o', hmem, hgeq, hveq, hk', hv', ho⟩ := RawViewX.refold hv hl
    have hleaf : ∀ e ∈ scale k' (kids ctx.κ m.children), e.1 ∉ taken := by
      intro e he
      apply hg
      rw [hgeq, ← map_fst_scale k']
      exact List.mem_map_of_mem he
    have hm' : MatchV ctx.G (.ac f elems (some r))
        (.mset (ofEntries (v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂))) σ taken := by
      rw [hveq] at hm; exact hm
    obtain ⟨hm₁, hrest₁⟩ := refold_ac helems hm' hleaf hX
    obtain ⟨t, ht⟩ := taken_ne_nil_of_match hm₁ hne
    have htv : t ∈ ofEntries (v₁ ++ (l.1, k') :: v₂) := MatchV.ac_mem hm₁ t ht
    have hXv : l.1 ∈ ofEntries (v₁ ++ (l.1, k') :: v₂) := by
      simp [ofEntries_append, ofEntries_cons, Multiset.mem_replicate, hk'.ne']
    have htX : t ≠ l.1 := fun h => hX (h ▸ ht)
    have hn' := normalize_ac_free_node_of_two htX htv hXv
    have hview' : ofView .ac (coalesce (v₁ ++ (l.1, k') :: v₂)) =
        .mset (ofEntries (v₁ ++ (l.1, k') :: v₂)) := by
      simp [ofView, ofEntries_coalesce]
    rw [← hview'] at hm₁
    obtain ⟨v'', ls'', o'', w'', rest'', hv'', ho'', hall'', hn'', hm'', hR'', -⟩ :=
      ih o' (by omega) _ _ _ _ hv' hn' hm₁
    have hstep : RefoldStepAC ctx ((ofEntries v).filter (fun c => c ∉ taken))
        ((ofEntries (v₁ ++ (l.1, k') :: v₂)).filter (fun c => c ∉ taken)) := by
      refine ⟨id, m, l.1, k', hmem, hk', ?_, ?_⟩
      · rw [hveq]; exact leaf_le_filter hleaf
      · rw [hrest₁, hveq]
    refine ⟨v'', ls'', o'', w'', rest'', hv'', by omega, hall'', hn'', ?_,
      Relation.ReflTransGen.head hstep hR'',
      fun _ => ⟨by omega, Relation.TransGen.head' hstep hR''⟩⟩
    rw [Binding.setRest_setRest] at hm''
    exact hm''


/-! ## ACI: the refold induction -/

theorem taken_ne_nil_of_match_aci {G : Graph} {f : Sym} {elems : List Pat}
    {rest : Option Var} {ch : Children} {σ : Binding} {taken : List C}
    (hm : MatchV G (.aci f elems rest) ch σ taken) (hne : elems ≠ []) : ∃ t, t ∈ taken := by
  cases hm with
  | aci _ hlen _ _ _ =>
    cases taken with
    | nil => exact absurd (List.length_eq_zero_iff.1 hlen) hne
    | cons t _ => exact ⟨t, List.mem_cons_self ..⟩

theorem MatchV.aci_mem {G : Graph} {f : Sym} {elems : List Pat} {rest : Option Var}
    {s : Finset C} {σ : Binding} {taken : List C}
    (hm : MatchV G (.aci f elems rest) (.set s) σ taken) : ∀ c ∈ taken, c ∈ s := by
  cases hm with
  | aci _ _ hmem _ _ => exact hmem

theorem MatchV.aci_rest {G : Graph} {f : Sym} {elems : List Pat} {r : Var}
    {s : Finset C} {σ : Binding} {taken : List C}
    (hm : MatchV G (.aci f elems (some r)) (.set s) σ taken) :
    σ.finRest r = some (s.filter (fun c => c ∉ taken)) := by
  cases hm with
  | aci _ _ _ _ hrest => exact hrest

theorem ofView_aci_free_node {v w : List (C × Nat)}
    (hn : normalize .aci Laws.free v = .node w) :
    ofView .aci w = .set (v.map Prod.fst).toFinset := by
  have hw : w = dedupAci v := (normalize_free_node.1 hn).1
  simp [ofView, hw, dedupAci, Function.comp_def, Finset.sort_toFinset]

theorem fix_aci_aux {ctx : Ctx} {n : Node} {f : Sym} {elems : List Pat} {r : Var}
    {taken : List C} (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) (hne : elems ≠ []) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafX) (w : List (C × Nat)) (σ : Binding),
      RawViewX ctx n v ls o → normalize .aci Laws.free v = .node w →
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken →
      ∃ (v' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (w' : List (C × Nat))
        (rest' : Finset C),
        RawViewX ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ ls', l.ok taken) ∧
        normalize .aci Laws.free v' = .node w' ∧
        MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
        RefoldsACI ctx (((v.map Prod.fst).toFinset).filter (fun c => c ∉ taken)) rest' ∧
        (¬ (∀ l ∈ ls, l.ok taken) → o' < o ∧
          Relation.TransGen (RefoldStepACI ctx)
            (((v.map Prod.fst).toFinset).filter (fun c => c ∉ taken)) rest') := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ hv hn hm
  have hview : ofView .aci w = .set (v.map Prod.fst).toFinset := ofView_aci_free_node hn
  rw [hview] at hm
  by_cases hall : ∀ l ∈ ls, l.ok taken
  · have hrest := MatchV.aci_rest hm
    refine ⟨v, ls, o, w, _, hv, le_rfl, hall, hn, ?_, Relation.ReflTransGen.refl,
      fun h => absurd hall h⟩
    rw [Binding.setSetRest_self hrest, hview]
    exact hm
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨l, hl, hlok⟩ := hall
    have hX : l.1 ∉ taken := fun h => hlok (Or.inl h)
    have hg : ∀ c ∈ l.2, c ∉ taken := fun c hc h => hlok (Or.inr ⟨c, hc, h⟩)
    obtain ⟨v₁, v₂, k', id, m, ls', o', hmem, hgeq, hveq, hk', hv', ho⟩ := RawViewX.refold hv hl
    have hleaf : ∀ e ∈ scale k' (kids ctx.κ m.children), e.1 ∉ taken := by
      intro e he
      apply hg
      rw [hgeq, ← map_fst_scale k']
      exact List.mem_map_of_mem he
    have hm' : MatchV ctx.G (.aci f elems (some r))
        (.set ((v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂).map Prod.fst).toFinset)
        σ taken := by
      rw [hveq] at hm; exact hm
    have hm₁ := refold_aci (X := l.1) (k' := k') helems hm' hleaf
    obtain ⟨t, ht⟩ := taken_ne_nil_of_match_aci hm₁ hne
    have htv : t ∈ (v₁ ++ (l.1, k') :: v₂).map Prod.fst :=
      List.mem_toFinset.1 (MatchV.aci_mem hm₁ t ht)
    have hXv : l.1 ∈ (v₁ ++ (l.1, k') :: v₂).map Prod.fst := by simp
    have htX : t ≠ l.1 := fun h => hX (h ▸ ht)
    have hn' := normalize_aci_free_node_of_two htX htv hXv
    have hview' : ofView .aci (dedupAci (v₁ ++ (l.1, k') :: v₂)) =
        .set ((v₁ ++ (l.1, k') :: v₂).map Prod.fst).toFinset := ofView_aci_free_node hn'
    rw [← hview'] at hm₁
    obtain ⟨v'', ls'', o'', w'', rest'', hv'', ho'', hall'', hn'', hm'', hR'', -⟩ :=
      ih o' (by omega) _ _ _ _ hv' hn' hm₁
    have hstep : RefoldStepACI ctx (((v.map Prod.fst).toFinset).filter (fun c => c ∉ taken))
        ((((v₁ ++ (l.1, k') :: v₂).map Prod.fst).toFinset).filter (fun c => c ∉ taken)) := by
      refine ⟨id, m, l.1,
        (((scale k' (kids ctx.κ m.children)).map Prod.fst).filter
          (fun c => c ∉ (v₁ ++ v₂).map Prod.fst)).toFinset, hmem, ?_, ?_⟩
      · intro c hc
        rw [List.mem_toFinset] at hc ⊢
        rw [map_fst_scale] at hc
        exact (List.mem_filter.1 hc).1
      · rw [refold_aci_rest hleaf hX, hveq]
    refine ⟨v'', ls'', o'', w'', rest'', hv'', by omega, hall'', hn'', ?_,
      Relation.ReflTransGen.head hstep hR'',
      fun _ => ⟨by omega, Relation.TransGen.head' hstep hR''⟩⟩
    rw [Binding.setSetRest_setSetRest] at hm''
    exact hm''


/-! ## Assoc: the refold induction -/

/-!
# `:flatten` views: the Assoc refold induction

The Assoc analogue of `fix_ac_aux`: a match of an assoc atom on the view of
any opening tree refolds, by closing unhit leaves, to a match on the view of
a tree whose every leaf is `LeafX.ok`; the prefix and suffix rests are
refoldings (`RefoldsAssoc`) of the original ones.
-/



/-! ## Contiguous blocks -/

/-- A nonempty contiguous block `g` disjoint from the nonempty contiguous
`mid`, both starting at the front: `g` lies entirely before `mid`. -/
theorem split_block_left {g v₂ u mid w : List C} (hg : g ≠ []) (hmid : mid ≠ [])
    (hdis : ∀ c ∈ g, c ∉ mid) (h : g ++ v₂ = u ++ mid ++ w) :
    ∃ b, u = g ++ b ∧ v₂ = b ++ mid ++ w := by
  induction g generalizing u with
  | nil => exact absurd rfl hg
  | cons c g ih =>
      cases u with
      | nil =>
          cases mid with
          | nil => exact absurd rfl hmid
          | cons d mid =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
              exact absurd (h.1 ▸ List.mem_cons_self ..) (hdis c (List.mem_cons_self ..))
      | cons c' u =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          cases g with
          | nil =>
              simp only [List.nil_append] at h
              exact ⟨u, rfl, h⟩
          | cons c₂ g =>
              obtain ⟨b, rfl, hv⟩ := ih (by simp) (fun x hx => hdis x (List.mem_cons_of_mem _ hx)) h
              exact ⟨b, rfl, hv⟩

/-- A nonempty contiguous block `g` disjoint from `mid`, with `mid` at the
front: `g` lies entirely after `mid`. -/
theorem split_block_right {v₁ g v₂ mid w : List C} (hg : g ≠ []) (hdis : ∀ c ∈ g, c ∉ mid)
    (h : v₁ ++ g ++ v₂ = mid ++ w) :
    ∃ a, v₁ = mid ++ a ∧ w = a ++ g ++ v₂ := by
  induction mid generalizing v₁ with
  | nil =>
      simp only [List.nil_append] at h
      exact ⟨v₁, rfl, h.symm⟩
  | cons d mid ih =>
      cases v₁ with
      | nil =>
          cases g with
          | nil => exact absurd rfl hg
          | cons c g =>
              simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
              exact absurd (h.1 ▸ List.mem_cons_self ..) (hdis c (List.mem_cons_self ..))
      | cons c v₁ =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨a, rfl, hw⟩ := ih (fun x hx hm => hdis x hx (List.mem_cons_of_mem _ hm)) h
          exact ⟨a, rfl, hw⟩

/-- A nonempty contiguous block `g` disjoint from a nonempty contiguous
`mid` lies entirely before or entirely after it. -/
theorem split_block {v₁ g v₂ u mid w : List C} (hg : g ≠ []) (hmid : mid ≠ [])
    (hdis : ∀ c ∈ g, c ∉ mid) (h : v₁ ++ g ++ v₂ = u ++ mid ++ w) :
    (∃ b, u = v₁ ++ g ++ b ∧ v₂ = b ++ mid ++ w) ∨ (∃ a, v₁ = u ++ mid ++ a ∧ w = a ++ g ++ v₂) := by
  induction v₁ generalizing u with
  | nil =>
      simp only [List.nil_append] at h
      obtain ⟨b, rfl, hv⟩ := split_block_left hg hmid hdis h
      exact Or.inl ⟨b, rfl, hv⟩
  | cons c v₁ ih =>
      cases u with
      | nil =>
          simp only [List.nil_append] at h
          obtain ⟨a, ha, hw⟩ := split_block_right hg hdis h
          exact Or.inr ⟨a, by rw [List.nil_append]; exact ha, hw⟩
      | cons c' u =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          rcases ih h with ⟨b, rfl, hv⟩ | ⟨a, rfl, hw⟩
          · exact Or.inl ⟨b, rfl, hv⟩
          · exact Or.inr ⟨a, rfl, hw⟩

/-! ## No nullary members -/

/-- Every `f`-member has at least one child. -/
def NoNullary (ctx : Ctx) : Prop :=
  ∀ id m X, ctx.IsMember id m X → kids ctx.κ m.children ≠ []

/-! ## Assoc -/

/-- The Assoc refold induction (the analogue of `fix_ac_aux`). Closing an
unhit leaf, whose block lies entirely in the prefix rest or entirely in the
suffix rest, is one `RefoldStepAssoc` on that rest; the other rest and the
item bindings are unchanged. -/
theorem fix_assoc_aux {ctx : Ctx} {n : Node} {f : Sym} {pre suf : Option Var} {args : List Pat}
    {mid : List C} (hnn : NoNullary ctx) (helems : ∀ p ∈ args, ∃ x, p = Pat.var x)
    (hne : args ≠ []) (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafX) (w : List (C × Nat)) (σ : Binding)
      (u s : List C),
      RawViewX ctx n v ls o → normalize .assoc Laws.free v = .node w →
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid →
      SeqRestOk σ pre u → SeqRestOk σ suf s →
      ∃ (v' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (w' : List (C × Nat))
        (σ' : Binding) (u' s' : List C),
        RawViewX ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ ls', l.ok mid) ∧
        normalize .assoc Laws.free v' = .node w' ∧
        MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
        σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
        σ'.finRest = σ.finRest ∧
        SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
        RefoldsAssoc ctx u u' ∧ RefoldsAssoc ctx s s' ∧
        (¬ (∀ l ∈ ls, l.ok mid) → o' < o ∧
          (Relation.TransGen (RefoldStepAssoc ctx) u u' ∨
            Relation.TransGen (RefoldStepAssoc ctx) s s')) := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ u s hv hn hm hu hs
  have hw : w = v := (normalize_free_node.1 hn).1
  subst hw
  have hview : ofView .assoc w = .seq (w.map Prod.fst) := rfl
  rw [hview] at hm
  by_cases hall : ∀ l ∈ ls, l.ok mid
  · exact ⟨w, ls, o, w, σ, u, s, hv, le_rfl, hall, hn, hm, rfl, rfl, rfl, rfl, rfl, hu, hs,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, fun h => absurd hall h⟩
  · simp only [not_forall] at hall
    obtain ⟨l, hl, hlok⟩ := hall
    have hX : l.1 ∉ mid := fun h => hlok (Or.inl h)
    have hg : ∀ c ∈ l.2, c ∉ mid := fun c hc h => hlok (Or.inr ⟨c, hc, h⟩)
    obtain ⟨v₁, v₂, k', id, m, ls', o', hmem, hgeq, hveq, hk', hv', ho⟩ := RawViewX.refold hv hl
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
    have hsplit' : v₁.map Prod.fst ++ l.2 ++ v₂.map Prod.fst = u ++ mid ++ s := by
      rw [← hsplit, hveq, List.map_append, List.map_append, map_fst_scale, hgeq]
    have hmid : mid ≠ [] := by
      rintro rfl
      exact hne (List.length_eq_zero_iff.1 (by simpa using hlen))
    have hgne : l.2 ≠ [] := by
      rw [hgeq]
      intro h
      exact hnn id m l.1 hmem (List.map_eq_nil_iff.1 h)
    have hmidlen : 0 < mid.length := List.length_pos_of_ne_nil hmid
    rcases split_block hgne hmid hg hsplit' with ⟨b, hub, hv₂⟩ | ⟨a, hv₁, hsa⟩
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
          obtain ⟨-, hm₁⟩ := refold_assoc_pre (X := l.1) helems hne' hm hu hs
          have hv'map : (v₁ ++ (l.1, k') :: v₂).map Prod.fst =
              (v₁.map Prod.fst ++ l.1 :: b) ++ mid ++ s := by
            simp [hv₂]
          have hv₂len : 0 < v₂.length := by
            have := congrArg List.length hv₂
            simp only [List.length_map, List.length_append] at this
            omega
          have h2 : 2 ≤ (v₁ ++ (l.1, k') :: v₂).length := by
            simp only [List.length_append, List.length_cons]; omega
          have hn' := normalize_assoc_free_node_of_len h2
          have hm₁' : MatchV ctx.G (.assoc f (some rp) args suf)
              (ofView .assoc (v₁ ++ (l.1, k') :: v₂))
              (σ.setSeqRest rp (v₁.map Prod.fst ++ l.1 :: b)) mid := by
            simp only [ofView]
            rw [hv'map]
            exact hm₁
          have hu₁ : SeqRestOk (σ.setSeqRest rp (v₁.map Prod.fst ++ l.1 :: b)) (some rp)
              (v₁.map Prod.fst ++ l.1 :: b) := by
            simp [SeqRestOk, Binding.setSeqRest]
          obtain ⟨v'', ls'', o'', w'', σ'', u'', s'', hv'', ho'', hall'', hn'', hm'', hcls, hnode,
              hmult, hrest, hfin, hu'', hs'', hRu, hRs, -⟩ :=
            ih o' (by omega) _ _ _ _ _ _ hv' hn' hm₁' hu₁ (SeqRestOk_setSeqRest hne' hs)
          have hstep : RefoldStepAssoc ctx u (v₁.map Prod.fst ++ l.1 :: b) :=
            ⟨id, m, l.1, v₁.map Prod.fst, b, hmem, by rw [hub, hgeq], rfl⟩
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
          obtain ⟨-, hm₁⟩ := refold_assoc_suf (X := l.1) helems hne' hm hu hs
          have hv'map : (v₁ ++ (l.1, k') :: v₂).map Prod.fst =
              u ++ mid ++ (a ++ l.1 :: v₂.map Prod.fst) := by
            simp [hv₁]
          have hv₁len : 0 < v₁.length := by
            have := congrArg List.length hv₁
            simp only [List.length_map, List.length_append] at this
            omega
          have h2 : 2 ≤ (v₁ ++ (l.1, k') :: v₂).length := by
            simp only [List.length_append, List.length_cons]; omega
          have hn' := normalize_assoc_free_node_of_len h2
          have hm₁' : MatchV ctx.G (.assoc f pre args (some rs))
              (ofView .assoc (v₁ ++ (l.1, k') :: v₂))
              (σ.setSeqRest rs (a ++ l.1 :: v₂.map Prod.fst)) mid := by
            simp only [ofView]
            rw [hv'map]
            exact hm₁
          have hs₁ : SeqRestOk (σ.setSeqRest rs (a ++ l.1 :: v₂.map Prod.fst)) (some rs)
              (a ++ l.1 :: v₂.map Prod.fst) := by
            simp [SeqRestOk, Binding.setSeqRest]
          obtain ⟨v'', ls'', o'', w'', σ'', u'', s'', hv'', ho'', hall'', hn'', hm'', hcls, hnode,
              hmult, hrest, hfin, hu'', hs'', hRu, hRs, -⟩ :=
            ih o' (by omega) _ _ _ _ _ _ hv' hn' hm₁' (SeqRestOk_setSeqRest hne' hu) hs₁
          have hstep : RefoldStepAssoc ctx s (a ++ l.1 :: v₂.map Prod.fst) :=
            ⟨id, m, l.1, a, v₂.map Prod.fst, hmem, by rw [hsa, hgeq], rfl⟩
          exact ⟨v'', ls'', o'', w'', σ'', u'', s'', hv'', by omega, hall'', hn'', hm'',
            hcls, hnode, hmult, hrest, hfin, hu'', hs'',
            hRu, Relation.ReflTransGen.head hstep hRs,
            fun _ => ⟨by omega, Or.inr (Relation.TransGen.head' hstep hRs)⟩⟩


/-! ## The interpreter fragment with the corrected rule -/

/-- The binding and the view register file, with the corrected demands. -/
structure FEnvX where
  σ : Binding
  views : Nat → Option (List (C × Nat) × DemandX)

def FEnvX.setView (env : FEnvX) (r : Nat) (wd : List (C × Nat) × DemandX) : FEnvX :=
  { env with views := Function.update env.views r (some wd) }

def FEnvX.withBinding (env : FEnvX) (σ : Binding) : FEnvX := { env with σ := σ }

/-- `runFStep` with `enumerateX` and `DemandX.acceptsFixB` in the
decomposition filter. -/
def runFStepX (c : FCtx) : FStep → FEnvX → List FEnvX
  | .base s, env => (runStep c.G s env.σ).map env.withBinding
  | .flatten v f κ out, env =>
      match env.σ.nodeOf c.G v with
      | some n => (enumerateX (c.ctx f κ) (c.laws f) n).map (env.setView out)
      | none => []
  | .decomposeAC _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeAC elems rest w env.σ).filter
            (fun σ' => d.acceptsFixB (takenOf σ' (elems.map Prod.fst)))).map env.withBinding
      | none => []
  | .decomposeACI _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeACI elems rest (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsFixB (takenOf σ' elems))).map env.withBinding
      | none => []
  | .expandA _ pre elems suf r, env =>
      match env.views r with
      | some (w, d) =>
          ((expandA pre elems suf (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsFixB (takenOf σ' elems))).map env.withBinding
      | none => []

/-- Depth-first search over a plan, corrected rule. -/
def runFX (c : FCtx) : List FStep → FEnvX → List FEnvX
  | [], env => [env]
  | s :: ss, env => (runFStepX c s env).flatMap (runFX c ss)

theorem mem_runFX_two {c : FCtx} {s₁ s₂ : FStep} {env env' : FEnvX} :
    env' ∈ runFX c [s₁, s₂] env ↔
      ∃ env₁ ∈ runFStepX c s₁ env, env' ∈ runFStepX c s₂ env₁ := by
  simp [runFX]

theorem mem_flattenX_step {c : FCtx} {v : Var} {f : Sym} {κ : FlatKind} {r : Nat}
    {env env₁ : FEnvX} {n : Node} (hn : env.σ.nodeOf c.G v = some n) :
    env₁ ∈ runFStepX c (.flatten v f κ r) env ↔
      ∃ wd ∈ enumerateX (c.ctx f κ) (c.laws f) n, env₁ = env.setView r wd := by
  simp only [runFStepX, hn, List.mem_map]
  constructor
  · rintro ⟨wd, h, rfl⟩; exact ⟨wd, h, rfl⟩
  · rintro ⟨wd, h, rfl⟩; exact ⟨wd, h, rfl⟩

@[simp] theorem FEnvX.setView_views_self (env : FEnvX) (r : Nat)
    (wd : List (C × Nat) × DemandX) : (env.setView r wd).views r = some wd := by
  simp [FEnvX.setView]

@[simp] theorem FEnvX.setView_σ (env : FEnvX) (r : Nat) (wd : List (C × Nat) × DemandX) :
    (env.setView r wd).σ = env.σ := rfl

@[simp] theorem FEnvX.withBinding_σ (env : FEnvX) (σ : Binding) :
    (env.withBinding σ).σ = σ := rfl

/-! ### Soundness and completeness of the fragment against `MatchFlatX` -/

theorem flatten_fix_sound_ac (c : FCtx) (v v' : Var) (f : Sym) (es : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env env' : FEnvX) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.rest r = none)
    (h : env' ∈ runFX c [.flatten v f .ac r, .decomposeAC v' es rest r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlatX (c.ctx f .ac) (c.laws f) (.ac f (acPats es) rest) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runFX_two.1 h
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flattenX_step hn).1 h₁
  simp only [runFStepX, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
    FEnvX.setView_σ] at h₂
  obtain ⟨σ', ⟨hσ', hacc⟩, rfl⟩ := h₂
  have hviews := views_soundX hwd
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hviews.1
  have hent : Multiset.entries (ofEntries w) = w := normalize_ac_entries hn₀
  rw [← hent] at hσ'
  obtain ⟨hext, taken, hnd, hlen, hmem, hcls, hmult, hrest⟩ :=
    decompose_ac_sound es rest (ofEntries w) env.σ σ' hfresh hσ'
  have htaken : takenOf σ' (es.map Prod.fst) = taken :=
    takenOf_eq_of_zip _ _ (by simpa using hlen.symm) (zip_map_fst hcls)
  refine ⟨hext, w, hviews.1, taken, ?_, ?_⟩
  · exact MatchV.ac hnd (by simpa [acPats] using hlen) hmem (acPats_zip_matchC.2 hcls)
      (acPats_zip_multOk.2 hmult) hrest
  · rw [htaken, DemandX.acceptsFixB_iff] at hacc
    exact (acceptsFix_iff_altsXAccept hwd taken).1 hacc

theorem flatten_fix_complete_ac (c : FCtx) (v v' : Var) (f : Sym) (es : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env : FEnvX) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.rest r = none)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlatX (c.ctx f .ac) (c.laws f) (.ac f (acPats es) rest) n σ') :
    ∃ env'' ∈ runFX c [.flatten v f .ac r, .decomposeAC v' es rest r] env,
      Binding.Extends env''.σ σ' := by
  obtain ⟨w, hw, taken, hmv, halts⟩ := hm
  obtain ⟨d, hwd⟩ := mem_enumerateX_iff.2 hw
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hw
  have hent : Multiset.entries (ofEntries w) = w := normalize_ac_entries hn₀
  cases hmv with
  | ac hnd hlen hmem hcls hmult hrest =>
    have hcls' := acPats_zip_matchC.1 hcls
    have hmult' := acPats_zip_multOk.1 hmult
    obtain ⟨σ'', hσ'', hext'⟩ := decompose_ac_complete es rest (ofEntries w) env.σ σ' taken
      hext hnd (by simpa [acPats] using hlen) hmem hcls' hmult' hrest
    obtain ⟨-, taken'', -, hlen'', -, hcls'', -, -⟩ :=
      decompose_ac_sound es rest (ofEntries w) env.σ σ'' hfresh hσ''
    rw [hent] at hσ''
    refine ⟨(env.setView r (w, d)).withBinding σ'', ?_, hext'⟩
    rw [mem_runFX_two]
    refine ⟨env.setView r (w, d), (mem_flattenX_step hn).2 ⟨(w, d), hwd, rfl⟩, ?_⟩
    simp only [runFStepX, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
      FEnvX.setView_σ]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' (es.map Prod.fst) = taken :=
      taken_unique hext' (by simpa using hlen''.symm) (by simpa [acPats] using hlen.symm)
        (zip_map_fst hcls'') (zip_map_fst hcls')
    rw [htaken, DemandX.acceptsFixB_iff]
    exact (acceptsFix_iff_altsXAccept hwd taken).2 halts

theorem flatten_fix_sound_aci (c : FCtx) (v v' : Var) (f : Sym) (es : List Var)
    (rest : Option Var) (r : Nat) (env env' : FEnvX) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.finRest r = none)
    (h : env' ∈ runFX c [.flatten v f .aci r, .decomposeACI v' es rest r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlatX (c.ctx f .aci) (c.laws f) (.aci f (es.map Pat.var) rest) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runFX_two.1 h
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flattenX_step hn).1 h₁
  simp only [runFStepX, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
    FEnvX.setView_σ] at h₂
  obtain ⟨σ', ⟨hσ', hacc⟩, rfl⟩ := h₂
  have hviews := views_soundX hwd
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hviews.1
  have hsort := normalize_aci_sort hn₀
  rw [← hsort] at hσ'
  obtain ⟨hext, taken, hnd, hlen, hmem, hcls, hrest⟩ :=
    decompose_aci_sound es rest _ env.σ σ' hfresh hσ'
  have htaken : takenOf σ' es = taken := takenOf_eq_of_zip _ _ hlen.symm hcls
  refine ⟨hext, w, hviews.1, taken, ?_, ?_⟩
  · exact MatchV.aci hnd (by simpa using hlen) hmem (varPats_zip_matchC.2 hcls) hrest
  · rw [htaken, DemandX.acceptsFixB_iff] at hacc
    exact (acceptsFix_iff_altsXAccept hwd taken).1 hacc

theorem flatten_fix_complete_aci (c : FCtx) (v v' : Var) (f : Sym) (es : List Var)
    (rest : Option Var) (r : Nat) (env : FEnvX) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.finRest r = none)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlatX (c.ctx f .aci) (c.laws f) (.aci f (es.map Pat.var) rest) n σ') :
    ∃ env'' ∈ runFX c [.flatten v f .aci r, .decomposeACI v' es rest r] env,
      Binding.Extends env''.σ σ' := by
  obtain ⟨w, hw, taken, hmv, halts⟩ := hm
  obtain ⟨d, hwd⟩ := mem_enumerateX_iff.2 hw
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hw
  have hsort := normalize_aci_sort hn₀
  cases hmv with
  | aci hnd hlen hmem hcls hrest =>
    have hcls' := varPats_zip_matchC.1 hcls
    obtain ⟨σ'', hσ'', hext'⟩ := decompose_aci_complete es rest _ env.σ σ' taken
      hext hnd (by simpa using hlen) hmem hcls' hrest
    obtain ⟨-, taken'', -, hlen'', -, hcls'', -⟩ :=
      decompose_aci_sound es rest _ env.σ σ'' hfresh hσ''
    rw [hsort] at hσ''
    refine ⟨(env.setView r (w, d)).withBinding σ'', ?_, hext'⟩
    rw [mem_runFX_two]
    refine ⟨env.setView r (w, d), (mem_flattenX_step hn).2 ⟨(w, d), hwd, rfl⟩, ?_⟩
    simp only [runFStepX, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
      FEnvX.setView_σ]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' es = taken :=
      taken_unique hext' hlen''.symm (by simpa using hlen.symm) hcls'' hcls'
    rw [htaken, DemandX.acceptsFixB_iff]
    exact (acceptsFix_iff_altsXAccept hwd taken).2 halts

theorem flatten_fix_sound_assoc (c : FCtx) (v v' : Var) (f : Sym) (pre suf : Option Var)
    (es : List Var) (r : Nat) (env env' : FEnvX) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n)
    (hpre₀ : ∀ r, pre = some r → env.σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → env.σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (h : env' ∈ runFX c [.flatten v f .assoc r, .expandA v' pre es suf r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlatX (c.ctx f .assoc) (c.laws f) (.assoc f pre (es.map Pat.var) suf) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runFX_two.1 h
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flattenX_step hn).1 h₁
  simp only [runFStepX, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
    FEnvX.setView_σ] at h₂
  obtain ⟨σ', ⟨hσ', hacc⟩, rfl⟩ := h₂
  have hviews := views_soundX hwd
  obtain ⟨hext, u, mid, v₂, heq, hlen, hpre, hsuf, hcls⟩ :=
    expand_a_sound pre suf es _ env.σ σ' hpre₀ hsuf₀ hdist hσ'
  have htaken : takenOf σ' es = mid := takenOf_eq_of_zip _ _ hlen hcls
  refine ⟨hext, w, hviews.1, mid, ?_, ?_⟩
  · have hch : ofView (c.ctx f .assoc).κ w = .seq (u ++ mid ++ v₂) := by
      simp [ofView, FCtx.ctx, heq]
    rw [hch]
    exact MatchV.assoc (by simpa using hlen.symm) hpre hsuf (varPats_zip_matchC.2 hcls)
  · rw [htaken, DemandX.acceptsFixB_iff] at hacc
    exact (acceptsFix_iff_altsXAccept hwd mid).1 hacc

theorem flatten_fix_complete_assoc (c : FCtx) (v v' : Var) (f : Sym) (pre suf : Option Var)
    (es : List Var) (r : Nat) (env : FEnvX) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n)
    (hpre₀ : ∀ r, pre = some r → env.σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → env.σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlatX (c.ctx f .assoc) (c.laws f) (.assoc f pre (es.map Pat.var) suf) n σ') :
    ∃ env'' ∈ runFX c [.flatten v f .assoc r, .expandA v' pre es suf r] env,
      Binding.Extends env''.σ σ' := by
  obtain ⟨w, hw, taken, hmv, halts⟩ := hm
  obtain ⟨d, hwd⟩ := mem_enumerateX_iff.2 hw
  generalize hch : ofView (c.ctx f .assoc).κ w = ch at hmv
  cases hmv with
  | @assoc _ _ _ _ u _ v₂ _ hlen hpre hsuf hargs =>
    simp only [ofView, FCtx.ctx, Children.seq.injEq] at hch
    have hcls' := varPats_zip_matchC.1 hargs
    obtain ⟨σ'', hσ'', hext'⟩ := expand_a_complete pre suf es u taken v₂ env.σ σ' hext
      (by simpa using hlen.symm) hpre hsuf hcls'
    rw [← hch] at hσ''
    obtain ⟨-, u'', mid'', v₂'', -, hlen'', -, -, hcls''⟩ :=
      expand_a_sound pre suf es _ env.σ σ'' hpre₀ hsuf₀ hdist hσ''
    refine ⟨(env.setView r (w, d)).withBinding σ'', ?_, hext'⟩
    rw [mem_runFX_two]
    refine ⟨env.setView r (w, d), (mem_flattenX_step hn).2 ⟨(w, d), hwd, rfl⟩, ?_⟩
    simp only [runFStepX, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
      FEnvX.setView_σ]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' es = taken :=
      taken_unique hext' hlen'' (by simpa using hlen.symm) hcls'' hcls'
    rw [htaken, DemandX.acceptsFixB_iff]
    exact (acceptsFix_iff_altsXAccept hwd taken).2 halts

/-! ## From an accepted tree to an emitted view -/

/-- A tree whose every leaf is `ok` makes its view's emitted demand accept. -/
theorem acceptsFix_of_tree {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List LeafX} {o : Nat} {taken : List C} (hv : RawViewX ctx n v ls o)
    (hn : normalize ctx.κ laws v = .node w) (hok : ∀ l ∈ ls, l.ok taken) :
    ∃ d, (w, d) ∈ enumerateX ctx laws n ∧ d.acceptsFix taken := by
  obtain ⟨d, hd, hu, ha⟩ := views_completeX hv hn
  refine ⟨d, hd, ?_⟩
  by_cases hls : ls = []
  · exact Or.inl (hu hls)
  · rcases ha hls with h | h
    · exact Or.inl h
    · exact Or.inr ⟨ls, h, hok⟩

/-! ## AC: completeness of the corrected rule -/

/-- **Completeness, AC.** Any match of an AC atom (item patterns variables,
at least one item, a rest variable, laws-free operator) on the canonical
view of any opening tree of `n` is, up to refolding the rest, a match on an
emitted view whose corrected demand accepts the taken classes. The item
bindings (classes and multiplicities) are those of `σ` (the binding is
`σ.setRest r rest'`), and `rest'` is a refolding of `σ`'s rest. -/
theorem demand_fix_complete_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {n : Node}
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .ac Laws.free v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (rest₀ rest' : Multiset C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsFix taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ RefoldsAC ctx rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', hR, -⟩ :=
    fix_ac_aux helems hne o v ls w σ hv hn hm
  obtain ⟨d, hd, hacc⟩ := acceptsFix_of_tree hv' (by rw [hκ]; exact hn') hok
  refine ⟨w', d, _, rest', hd, hacc, hm', ?_, hR⟩
  have hview : ofView .ac w = .mset (ofEntries v) := by simp [ofView, ofEntries_free_ac hn]
  rw [hview] at hm
  exact MatchV.ac_rest hm

/-- The same under the engine-level bound hypothesis (unused by the proof,
as for `views_complete_within`). -/
theorem demand_fix_complete_ac_within {W : Nat} {ctx : Ctx} {n : Node}
    (_ : WithinBounds W ctx n) (hκ : ctx.κ = .ac)
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .ac Laws.free v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (rest₀ rest' : Multiset C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsFix taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ RefoldsAC ctx rest₀ rest' :=
  demand_fix_complete_ac hκ hv hn helems hne hm

/-- **No redundancy, AC.** The corrected rule rejects a match on a tree
(some leaf not `ok`) only when a proper refolding of it (strictly fewer
openings, at least one refold step on the rest) is a match on a tree the
rule accepts. -/
theorem demand_fix_no_redundancy_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {n : Node}
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .ac Laws.free v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken)
    (hrej : ¬ ∀ l ∈ ls, l.ok taken) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (d : DemandX)
      (rest₀ rest' : Multiset C),
      RawViewX ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ ls', l.ok taken) ∧
      normalize .ac Laws.free v' = .node w' ∧
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsFix taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ Relation.TransGen (RefoldStepAC ctx) rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', -, hlt⟩ :=
    fix_ac_aux helems hne o v ls w σ hv hn hm
  obtain ⟨hlt, hT⟩ := hlt hrej
  obtain ⟨d, hd, hacc⟩ := acceptsFix_of_tree hv' (by rw [hκ]; exact hn') hok
  refine ⟨v', w', ls', o', d, _, rest', hv', hlt, hok, hn', hd, hacc, hm', ?_, hT⟩
  have hview : ofView .ac w = .mset (ofEntries v) := by simp [ofView, ofEntries_free_ac hn]
  rw [hview] at hm
  exact MatchV.ac_rest hm

/-- The corrected rule recovers the lost match of `demand-gap.egg` in
general: whenever the original rule accepts, so does the corrected one
(`DemandX.accepts_proj_imp`), and every match on any tree is recovered
(`demand_fix_complete_ac`). -/
theorem accepts_imp_acceptsFix {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {d : Demand} {dx : DemandX} (h : (w, d) ∈ enumerate ctx laws n)
    (hx : (w, dx) ∈ enumerateX ctx laws n) {taken : List C} (hacc : d.accepts taken) :
    dx.acceptsFix taken := by
  rw [enumerateX_proj] at h
  obtain ⟨⟨w', dx'⟩, hx', heq⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  rw [enumerateX_demand_unique hx hx']
  exact DemandX.accepts_proj_imp _ _ hacc


/-! ## ACI: completeness of the corrected rule -/

/-- **Completeness, ACI.** As `demand_fix_complete_ac`, with the set rest. -/
theorem demand_fix_complete_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {n : Node}
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .aci Laws.free v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (rest₀ rest' : Finset C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsFix taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ RefoldsACI ctx rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', hR, -⟩ :=
    fix_aci_aux helems hne o v ls w σ hv hn hm
  obtain ⟨d, hd, hacc⟩ := acceptsFix_of_tree hv' (by rw [hκ]; exact hn') hok
  refine ⟨w', d, _, rest', hd, hacc, hm', ?_, hR⟩
  rw [ofView_aci_free_node hn] at hm
  exact MatchV.aci_rest hm

/-- **No redundancy, ACI.** -/
theorem demand_fix_no_redundancy_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {n : Node}
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .aci Laws.free v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken)
    (hrej : ¬ ∀ l ∈ ls, l.ok taken) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (d : DemandX)
      (rest₀ rest' : Finset C),
      RawViewX ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ ls', l.ok taken) ∧
      normalize .aci Laws.free v' = .node w' ∧
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsFix taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ Relation.TransGen (RefoldStepACI ctx) rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', -, hlt⟩ :=
    fix_aci_aux helems hne o v ls w σ hv hn hm
  obtain ⟨hlt, hT⟩ := hlt hrej
  obtain ⟨d, hd, hacc⟩ := acceptsFix_of_tree hv' (by rw [hκ]; exact hn') hok
  refine ⟨v', w', ls', o', d, _, rest', hv', hlt, hok, hn', hd, hacc, hm', ?_, hT⟩
  rw [ofView_aci_free_node hn] at hm
  exact MatchV.aci_rest hm


/-! ## Assoc: completeness of the corrected rule -/

/-- **Completeness, Assoc.** Hypotheses: every `f`-member has a child
(`NoNullary`), item patterns are variables, at least one item, distinct
prefix/suffix rest variables, laws-free operator. The refolded binding
`σ'` agrees with `σ` on every field but the sequence rests, and its two
rests are refoldings of `σ`'s. -/
theorem demand_fix_complete_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) (hnn : NoNullary ctx)
    {n : Node} {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .assoc Laws.free v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (σ' : Binding) (u' s' : List C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsFix mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssoc ctx u u' ∧ RefoldsAssoc ctx s s' := by
  obtain ⟨v', ls', o', w', σ', u', s', hv', -, hok, hn', hm', h1, h2, h3, h4, h5, hu', hs',
    hRu, hRs, -⟩ := fix_assoc_aux hnn helems hne hdist o v ls w σ u s hv hn hm hu hs
  obtain ⟨d, hd, hacc⟩ := acceptsFix_of_tree hv' (by rw [hκ]; exact hn') hok
  exact ⟨w', d, σ', u', s', hd, hacc, hm', h1, h2, h3, h4, h5, hu', hs', hRu, hRs⟩

/-- **No redundancy, Assoc.** -/
theorem demand_fix_no_redundancy_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) (hnn : NoNullary ctx)
    {n : Node} {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .assoc Laws.free v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s)
    (hrej : ¬ ∀ l ∈ ls, l.ok mid) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (d : DemandX) (σ' : Binding)
      (u' s' : List C),
      RawViewX ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ ls', l.ok mid) ∧
      normalize .assoc Laws.free v' = .node w' ∧
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsFix mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssoc ctx u u' ∧ RefoldsAssoc ctx s s' ∧
      (Relation.TransGen (RefoldStepAssoc ctx) u u' ∨
        Relation.TransGen (RefoldStepAssoc ctx) s s') := by
  obtain ⟨v', ls', o', w', σ', u', s', hv', -, hok, hn', hm', h1, h2, h3, h4, h5, hu', hs',
    hRu, hRs, hlt⟩ := fix_assoc_aux hnn helems hne hdist o v ls w σ u s hv hn hm hu hs
  obtain ⟨hlt, hT⟩ := hlt hrej
  obtain ⟨d, hd, hacc⟩ := acceptsFix_of_tree hv' (by rw [hκ]; exact hn') hok
  exact ⟨v', w', ls', o', d, σ', u', s', hv', hlt, hok, hn', hd, hacc, hm', h1, h2, h3, h4, h5,
    hu', hs', hRu, hRs, hT⟩

end Semper.EMatch.Flatten
