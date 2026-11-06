import SemperProofs.EMatch.Flatten.FixMain

/-!
# `:flatten` views: the per-kind demand rule

The engine applies the opened-class clause of the corrected rule
(`LeafX.ok`) to multisets only: `Demand.merge_on_close` is `true` for
`FlatKind::Ac` and `false` for `Aci` and `Assoc`, and a leaf is satisfied
iff it holds a taken class or (`merge_on_close` and its opened class is
taken). This file justifies that choice:

* `demand_orig_complete_aci`, `demand_orig_complete_assoc`: the original
  rule (`LeafX.hit`: every leaf holds a taken class) is complete for sets
  and sequences, by the same refold induction (`refold_aci`,
  `refold_assoc_pre/suf` need no proviso on the opened class). ACI needs
  the hypothesis `TwoClasses ctx n` (no raw view of `n` has a single class):
  without it a single-child member (`Z ∋ And{X}`) makes the refolded view
  degenerate (see the docstring of `orig_aci_aux`).
* `DemandX.acceptsKind κ`: `acceptsFix` for `ac`, `acceptsOrig` (= the
  original `accepts` on the projection) otherwise; `runFK` uses it per
  decomposition step; `flatten_kind_{sound,complete}_*` and
  `demand_kind_complete_*` follow as corollaries.
* No-redundancy for the original rule on ACI/Assoc
  (`demand_orig_no_redundancy_{aci,assoc}`).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## The original per-leaf condition and the per-kind rule -/

/-- The original per-leaf condition: the leaf group holds a taken class. -/
def LeafX.hit (taken : List C) (l : LeafX) : Prop := ∃ c ∈ l.2, c ∈ taken

instance (taken : List C) (l : LeafX) : Decidable (l.hit taken) := by
  unfold LeafX.hit; infer_instance

theorem LeafX.ok_of_hit {taken : List C} {l : LeafX} (h : l.hit taken) : l.ok taken := Or.inr h

/-- The original rule on a `DemandX`. -/
def DemandX.acceptsOrig (d : DemandX) (taken : List C) : Prop :=
  d.unconditional = true ∨ ∃ ls ∈ d.alts, ∀ l ∈ ls, l.hit taken

def DemandX.acceptsOrigB (d : DemandX) (taken : List C) : Bool :=
  d.unconditional || d.alts.any (fun ls => ls.all (fun l => decide (l.hit taken)))

theorem DemandX.acceptsOrigB_iff (d : DemandX) (taken : List C) :
    d.acceptsOrigB taken = true ↔ d.acceptsOrig taken := by
  simp [DemandX.acceptsOrigB, DemandX.acceptsOrig]

/-- The original rule on a `DemandX` is the original rule on its projection. -/
theorem DemandX.acceptsOrig_iff_proj (d : DemandX) (taken : List C) :
    d.acceptsOrig taken ↔ d.proj.accepts taken := by
  unfold DemandX.acceptsOrig DemandX.proj Demand.accepts LeafX.hit
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨ls, hls, hall⟩)
    · exact Or.inl h
    · refine Or.inr ⟨ls.map Prod.snd, ⟨ls, hls, rfl⟩, ?_⟩
      intro g hg
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
      exact hall l hl
  · rintro (h | ⟨g, ⟨ls, hls, rfl⟩, hall⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ls, hls, fun l hl => hall l.2 (List.mem_map_of_mem hl)⟩

theorem DemandX.acceptsFix_of_acceptsOrig {d : DemandX} {taken : List C}
    (h : d.acceptsOrig taken) : d.acceptsFix taken := by
  rcases h with h | ⟨ls, hls, hall⟩
  · exact Or.inl h
  · exact Or.inr ⟨ls, hls, fun l hl => LeafX.ok_of_hit (hall l hl)⟩

/-- `Demand.merge_on_close`: the opened-class clause applies to multisets only. -/
def mergeOnClose : FlatKind → Bool
  | .ac => true
  | .aci => false
  | .assoc => false

/-- The engine's per-leaf condition. -/
def LeafX.okK (κ : FlatKind) (taken : List C) (l : LeafX) : Prop :=
  l.hit taken ∨ (mergeOnClose κ = true ∧ l.1 ∈ taken)

/-- The engine's per-kind rule. -/
def DemandX.acceptsKind (κ : FlatKind) (d : DemandX) (taken : List C) : Prop :=
  d.unconditional = true ∨ ∃ ls ∈ d.alts, ∀ l ∈ ls, l.okK κ taken

def DemandX.acceptsKindB (κ : FlatKind) (d : DemandX) (taken : List C) : Bool :=
  d.unconditional || d.alts.any (fun ls => ls.all (fun l =>
    decide (l.hit taken) || (mergeOnClose κ && decide (l.1 ∈ taken))))

theorem DemandX.acceptsKindB_iff (κ : FlatKind) (d : DemandX) (taken : List C) :
    d.acceptsKindB κ taken = true ↔ d.acceptsKind κ taken := by
  simp [DemandX.acceptsKindB, DemandX.acceptsKind, LeafX.okK]

theorem DemandX.acceptsKind_ac (d : DemandX) (taken : List C) :
    d.acceptsKind .ac taken ↔ d.acceptsFix taken := by
  simp [DemandX.acceptsKind, DemandX.acceptsFix, LeafX.okK, LeafX.ok, LeafX.hit, mergeOnClose,
    or_comm]

theorem DemandX.acceptsKind_aci (d : DemandX) (taken : List C) :
    d.acceptsKind .aci taken ↔ d.acceptsOrig taken := by
  simp [DemandX.acceptsKind, DemandX.acceptsOrig, LeafX.okK, mergeOnClose]

theorem DemandX.acceptsKind_assoc (d : DemandX) (taken : List C) :
    d.acceptsKind .assoc taken ↔ d.acceptsOrig taken := by
  simp [DemandX.acceptsKind, DemandX.acceptsOrig, LeafX.okK, mergeOnClose]

theorem DemandX.acceptsKindB_ac (d : DemandX) (taken : List C) :
    d.acceptsKindB .ac taken = d.acceptsFixB taken := by
  rw [Bool.eq_iff_iff, DemandX.acceptsKindB_iff, DemandX.acceptsFixB_iff, DemandX.acceptsKind_ac]

theorem DemandX.acceptsKindB_aci (d : DemandX) (taken : List C) :
    d.acceptsKindB .aci taken = d.acceptsOrigB taken := by
  simp [DemandX.acceptsKindB, DemandX.acceptsOrigB, mergeOnClose]

theorem DemandX.acceptsKindB_assoc (d : DemandX) (taken : List C) :
    d.acceptsKindB .assoc taken = d.acceptsOrigB taken := by
  simp [DemandX.acceptsKindB, DemandX.acceptsOrigB, mergeOnClose]

/-- The original rule, read through the emitted `DemandX`: `AltsAccept` on the
opening trees of `w`. -/
theorem acceptsOrig_iff_altsAccept {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : DemandX} (h : (w, d) ∈ enumerateX ctx laws n)
    (taken : List C) :
    d.acceptsOrig taken ↔ AltsAccept (Alts ctx laws n w) taken := by
  rw [DemandX.acceptsOrig_iff_proj]
  have h' : (w, d.proj) ∈ enumerate ctx laws n := by
    rw [enumerateX_proj]
    exact List.mem_map.2 ⟨(w, d), h, rfl⟩
  exact accepts_iff_altsAccept h' taken

/-- A tree whose every leaf is hit makes its view's emitted demand accept
under the original rule. -/
theorem acceptsOrig_of_tree {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List LeafX} {o : Nat} {taken : List C} (hv : RawViewX ctx n v ls o)
    (hn : normalize ctx.κ laws v = .node w) (hok : ∀ l ∈ ls, l.hit taken) :
    ∃ d, (w, d) ∈ enumerateX ctx laws n ∧ d.acceptsOrig taken := by
  obtain ⟨d, hd, hu, ha⟩ := views_completeX hv hn
  refine ⟨d, hd, ?_⟩
  by_cases hls : ls = []
  · exact Or.inl (hu hls)
  · rcases ha hls with h | h
    · exact Or.inl h
    · exact Or.inr ⟨ls, h, hok⟩

/-! ## ACI under the original rule -/

/-- No raw view of `n` is a single class. Needed for the original rule on
sets: closing an unhit leaf whose opened class `X` is taken can collapse the
view to `{X}` (e.g. `n = And{X, Z}`, `Z ∋ And{X}`, `X ∋ And{a, b}`: the tree
opening both gives `{a, b, X}`, `(And (X) ..rest)` matches it with
`rest = {a, b}`, the leaf `(X, [a, b])` is unhit, and the refold `{X, X}`
dedups to `Single X` and is dropped; the match is lost under the original
rule and kept under `acceptsFix`). -/
def TwoClasses (ctx : Ctx) (n : Node) : Prop :=
  ∀ v ls o, RawViewX ctx n v ls o → 2 ≤ (v.map Prod.fst).toFinset.card

theorem normalize_aci_free_node_of_card {v : List (C × Nat)}
    (h : 2 ≤ (v.map Prod.fst).toFinset.card) :
    normalize .aci Laws.free v = .node (dedupAci v) := by
  have hlen : (dedupAci v).length = (v.map Prod.fst).toFinset.card := by simp [dedupAci]
  refine normalize_free_node.2 ⟨rfl, ?_, ?_⟩
  · intro h'; rw [h'] at hlen; simp at hlen; omega
  · intro c h'; rw [h'] at hlen; simp at hlen; omega

/-- The ACI rest after a refold whose opened class is taken: the old rest
minus the leaf classes occurring nowhere else. -/
theorem refold_aci_rest_taken {v₁ v₂ leaf : List (C × Nat)} {X : C} {k' : Nat} {taken : List C}
    (hleaf : ∀ e ∈ leaf, e.1 ∉ taken) (hX : X ∈ taken) :
    (((v₁ ++ (X, k') :: v₂).map Prod.fst).toFinset).filter (fun c => c ∉ taken) =
      ((((v₁ ++ leaf ++ v₂).map Prod.fst).toFinset).filter (fun c => c ∉ taken)) \
        ((leaf.map Prod.fst).filter (fun c => c ∉ (v₁ ++ v₂).map Prod.fst)).toFinset := by
  ext c
  have hl : c ∈ leaf.map Prod.fst → c ∉ taken := by
    intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact hleaf e he
  by_cases hcX : c = X
  · subst hcX
    simp [hX]
  · simp only [Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset,
      List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_filter,
      decide_eq_true_eq, hcX, false_or]
    tauto

/-- One ACI refold step on a set rest, relative to `taken`: the leaf classes
occurring nowhere else are removed, and the opened class `X` is inserted
unless it is taken (in which case it is not part of any rest). -/
def RefoldStepACIT (ctx : Ctx) (taken : List C) (s₀ s₁ : Finset C) : Prop :=
  ∃ (id : NodeId) (m : Node) (X : C) (D : Finset C), ctx.IsMember id m X ∧
    D ⊆ ((kids ctx.κ m.children).map Prod.fst).toFinset ∧
    s₁ = if X ∈ taken then s₀ \ D else insert X (s₀ \ D)

def RefoldsACIT (ctx : Ctx) (taken : List C) : Finset C → Finset C → Prop :=
  Relation.ReflTransGen (RefoldStepACIT ctx taken)

/-- The ACI refold induction under the original rule: `refold_aci` needs no
proviso on the opened class, and `TwoClasses` keeps the refolded views
nodes. -/
theorem orig_aci_aux {ctx : Ctx} {n : Node} {f : Sym} {elems : List Pat} {r : Var}
    {taken : List C} (htwo : TwoClasses ctx n)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafX) (w : List (C × Nat)) (σ : Binding),
      RawViewX ctx n v ls o → normalize .aci Laws.free v = .node w →
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken →
      ∃ (v' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (w' : List (C × Nat))
        (rest' : Finset C),
        RawViewX ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ ls', l.hit taken) ∧
        normalize .aci Laws.free v' = .node w' ∧
        MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
        RefoldsACIT ctx taken (((v.map Prod.fst).toFinset).filter (fun c => c ∉ taken)) rest' ∧
        (¬ (∀ l ∈ ls, l.hit taken) → o' < o ∧
          Relation.TransGen (RefoldStepACIT ctx taken)
            (((v.map Prod.fst).toFinset).filter (fun c => c ∉ taken)) rest') := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro v ls w σ hv hn hm
  have hview : ofView .aci w = .set (v.map Prod.fst).toFinset := ofView_aci_free_node hn
  rw [hview] at hm
  by_cases hall : ∀ l ∈ ls, l.hit taken
  · have hrest := MatchV.aci_rest hm
    refine ⟨v, ls, o, w, _, hv, le_rfl, hall, hn, ?_, Relation.ReflTransGen.refl,
      fun h => absurd hall h⟩
    rw [Binding.setSetRest_self hrest, hview]
    exact hm
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨l, hl, hlok⟩ := hall
    have hg : ∀ c ∈ l.2, c ∉ taken := fun c hc h => hlok ⟨c, hc, h⟩
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
    have hn' := normalize_aci_free_node_of_card (htwo _ _ _ hv')
    have hview' : ofView .aci (dedupAci (v₁ ++ (l.1, k') :: v₂)) =
        .set ((v₁ ++ (l.1, k') :: v₂).map Prod.fst).toFinset := ofView_aci_free_node hn'
    rw [← hview'] at hm₁
    obtain ⟨v'', ls'', o'', w'', rest'', hv'', ho'', hall'', hn'', hm'', hR'', -⟩ :=
      ih o' (by omega) _ _ _ _ hv' hn' hm₁
    have hstep : RefoldStepACIT ctx taken
        (((v.map Prod.fst).toFinset).filter (fun c => c ∉ taken))
        ((((v₁ ++ (l.1, k') :: v₂).map Prod.fst).toFinset).filter (fun c => c ∉ taken)) := by
      refine ⟨id, m, l.1,
        (((scale k' (kids ctx.κ m.children)).map Prod.fst).filter
          (fun c => c ∉ (v₁ ++ v₂).map Prod.fst)).toFinset, hmem, ?_, ?_⟩
      · intro c hc
        rw [List.mem_toFinset] at hc ⊢
        rw [map_fst_scale] at hc
        exact (List.mem_filter.1 hc).1
      · by_cases hX : l.1 ∈ taken
        · simp only [hX, ↓reduceIte]
          rw [refold_aci_rest_taken hleaf hX, hveq]
        · simp only [hX, ↓reduceIte]
          rw [refold_aci_rest hleaf hX, hveq]
    refine ⟨v'', ls'', o'', w'', rest'', hv'', by omega, hall'', hn'', ?_,
      Relation.ReflTransGen.head hstep hR'',
      fun _ => ⟨by omega, Relation.TransGen.head' hstep hR''⟩⟩
    rw [Binding.setSetRest_setSetRest] at hm''
    exact hm''

/-! ## Assoc under the original rule -/

/-- The Assoc refold induction (the analogue of `fix_ac_aux`). Closing an
unhit leaf, whose block lies entirely in the prefix rest or entirely in the
suffix rest, is one `RefoldStepAssoc` on that rest; the other rest and the
item bindings are unchanged. -/
theorem orig_assoc_aux {ctx : Ctx} {n : Node} {f : Sym} {pre suf : Option Var} {args : List Pat}
    {mid : List C} (hnn : NoNullary ctx) (helems : ∀ p ∈ args, ∃ x, p = Pat.var x)
    (hne : args ≠ []) (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs) :
    ∀ (o : Nat) (v : List (C × Nat)) (ls : List LeafX) (w : List (C × Nat)) (σ : Binding)
      (u s : List C),
      RawViewX ctx n v ls o → normalize .assoc Laws.free v = .node w →
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid →
      SeqRestOk σ pre u → SeqRestOk σ suf s →
      ∃ (v' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (w' : List (C × Nat))
        (σ' : Binding) (u' s' : List C),
        RawViewX ctx n v' ls' o' ∧ o' ≤ o ∧ (∀ l ∈ ls', l.hit mid) ∧
        normalize .assoc Laws.free v' = .node w' ∧
        MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
        σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
        σ'.finRest = σ.finRest ∧
        SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
        RefoldsAssoc ctx u u' ∧ RefoldsAssoc ctx s s' ∧
        (¬ (∀ l ∈ ls, l.hit mid) → o' < o ∧
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
  by_cases hall : ∀ l ∈ ls, l.hit mid
  · exact ⟨w, ls, o, w, σ, u, s, hv, le_rfl, hall, hn, hm, rfl, rfl, rfl, rfl, rfl, hu, hs,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, fun h => absurd hall h⟩
  · simp only [not_forall] at hall
    obtain ⟨l, hl, hlok⟩ := hall
    have hg : ∀ c ∈ l.2, c ∉ mid := fun c hc h => hlok ⟨c, hc, h⟩
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

/-! ## The main theorems for the original rule on sets and sequences -/

/-- **Completeness of the original rule, ACI** (under `TwoClasses`). -/
theorem demand_orig_complete_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {n : Node}
    (htwo : TwoClasses ctx n)
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .aci Laws.free v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x)
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (rest₀ rest' : Finset C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsOrig taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ RefoldsACIT ctx taken rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', hR, -⟩ :=
    orig_aci_aux htwo helems o v ls w σ hv hn hm
  obtain ⟨d, hd, hacc⟩ := acceptsOrig_of_tree hv' (by rw [hκ]; exact hn') hok
  refine ⟨w', d, _, rest', hd, hacc, hm', ?_, hR⟩
  rw [ofView_aci_free_node hn] at hm
  exact MatchV.aci_rest hm

/-- **No redundancy of the original rule, ACI.** -/
theorem demand_orig_no_redundancy_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {n : Node}
    (htwo : TwoClasses ctx n)
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .aci Laws.free v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x)
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken)
    (hrej : ¬ ∀ l ∈ ls, l.hit taken) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (d : DemandX)
      (rest₀ rest' : Finset C),
      RawViewX ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ ls', l.hit taken) ∧
      normalize .aci Laws.free v' = .node w' ∧
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsOrig taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ Relation.TransGen (RefoldStepACIT ctx taken) rest₀ rest' := by
  obtain ⟨v', ls', o', w', rest', hv', -, hok, hn', hm', -, hlt⟩ :=
    orig_aci_aux htwo helems o v ls w σ hv hn hm
  obtain ⟨hlt, hT⟩ := hlt hrej
  obtain ⟨d, hd, hacc⟩ := acceptsOrig_of_tree hv' (by rw [hκ]; exact hn') hok
  refine ⟨v', w', ls', o', d, _, rest', hv', hlt, hok, hn', hd, hacc, hm', ?_, hT⟩
  rw [ofView_aci_free_node hn] at hm
  exact MatchV.aci_rest hm

/-- **Completeness of the original rule, Assoc.** Same hypotheses as
`demand_fix_complete_assoc`. -/
theorem demand_orig_complete_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) (hnn : NoNullary ctx)
    {n : Node} {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .assoc Laws.free v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (σ' : Binding) (u' s' : List C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsOrig mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssoc ctx u u' ∧ RefoldsAssoc ctx s s' := by
  obtain ⟨v', ls', o', w', σ', u', s', hv', -, hok, hn', hm', h1, h2, h3, h4, h5, hu', hs',
    hRu, hRs, -⟩ := orig_assoc_aux hnn helems hne hdist o v ls w σ u s hv hn hm hu hs
  obtain ⟨d, hd, hacc⟩ := acceptsOrig_of_tree hv' (by rw [hκ]; exact hn') hok
  exact ⟨w', d, σ', u', s', hd, hacc, hm', h1, h2, h3, h4, h5, hu', hs', hRu, hRs⟩

/-- **No redundancy of the original rule, Assoc.** -/
theorem demand_orig_no_redundancy_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) (hnn : NoNullary ctx)
    {n : Node} {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .assoc Laws.free v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s)
    (hrej : ¬ ∀ l ∈ ls, l.hit mid) :
    ∃ (v' w' : List (C × Nat)) (ls' : List LeafX) (o' : Nat) (d : DemandX) (σ' : Binding)
      (u' s' : List C),
      RawViewX ctx n v' ls' o' ∧ o' < o ∧ (∀ l ∈ ls', l.hit mid) ∧
      normalize .assoc Laws.free v' = .node w' ∧
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsOrig mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssoc ctx u u' ∧ RefoldsAssoc ctx s s' ∧
      (Relation.TransGen (RefoldStepAssoc ctx) u u' ∨
        Relation.TransGen (RefoldStepAssoc ctx) s s') := by
  obtain ⟨v', ls', o', w', σ', u', s', hv', -, hok, hn', hm', h1, h2, h3, h4, h5, hu', hs',
    hRu, hRs, hlt⟩ := orig_assoc_aux hnn helems hne hdist o v ls w σ u s hv hn hm hu hs
  obtain ⟨hlt, hT⟩ := hlt hrej
  obtain ⟨d, hd, hacc⟩ := acceptsOrig_of_tree hv' (by rw [hκ]; exact hn') hok
  exact ⟨v', w', ls', o', d, σ', u', s', hv', hlt, hok, hn', hd, hacc, hm', h1, h2, h3, h4, h5,
    hu', hs', hRu, hRs, hT⟩

/-! ## The per-kind interpreter -/

/-- `runFStepX` with the engine's per-kind rule: `acceptsFixB` for the
multiset decomposition, `acceptsOrigB` for the set and sequence ones
(`acceptsKindB` of the step's kind). -/
def runFStepK (c : FCtx) : FStep → FEnvX → List FEnvX
  | .base s, env => (runStep c.G s env.σ).map env.withBinding
  | .flatten v f κ out, env =>
      match env.σ.nodeOf c.G v with
      | some n => (enumerateX (c.ctx f κ) (c.laws f) n).map (env.setView out)
      | none => []
  | .decomposeAC _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeAC elems rest w env.σ).filter
            (fun σ' => d.acceptsKindB .ac (takenOf σ' (elems.map Prod.fst)))).map env.withBinding
      | none => []
  | .decomposeACI _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeACI elems rest (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsKindB .aci (takenOf σ' elems))).map env.withBinding
      | none => []
  | .expandA _ pre elems suf r, env =>
      match env.views r with
      | some (w, d) =>
          ((expandA pre elems suf (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsKindB .assoc (takenOf σ' elems))).map env.withBinding
      | none => []

def runFK (c : FCtx) : List FStep → FEnvX → List FEnvX
  | [], env => [env]
  | s :: ss, env => (runFStepK c s env).flatMap (runFK c ss)

theorem mem_runFK_two {c : FCtx} {s₁ s₂ : FStep} {env env' : FEnvX} :
    env' ∈ runFK c [s₁, s₂] env ↔
      ∃ env₁ ∈ runFStepK c s₁ env, env' ∈ runFStepK c s₂ env₁ := by
  simp [runFK]

theorem runFStepK_flatten (c : FCtx) (v : Var) (f : Sym) (κ : FlatKind) (out : Nat)
    (env : FEnvX) : runFStepK c (.flatten v f κ out) env = runFStepX c (.flatten v f κ out) env :=
  rfl

theorem runFStepK_decomposeAC (c : FCtx) (v : Var) (elems : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env : FEnvX) :
    runFStepK c (.decomposeAC v elems rest r) env = runFStepX c (.decomposeAC v elems rest r) env := by
  cases h : env.views r with
  | none => simp [runFStepK, runFStepX, h]
  | some wd =>
      obtain ⟨w, d⟩ := wd
      simp only [runFStepK, runFStepX, h, DemandX.acceptsKindB_ac]

/-- On the AC fragment the per-kind interpreter is the corrected one. -/
theorem runFK_ac (c : FCtx) (v v' : Var) (f : Sym) (es : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env : FEnvX) :
    runFK c [.flatten v f .ac r, .decomposeAC v' es rest r] env =
      runFX c [.flatten v f .ac r, .decomposeAC v' es rest r] env := by
  simp [runFK, runFX, runFStepK_flatten, runFStepK_decomposeAC]

theorem flatten_kind_sound_ac (c : FCtx) (v v' : Var) (f : Sym) (es : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env env' : FEnvX) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.rest r = none)
    (h : env' ∈ runFK c [.flatten v f .ac r, .decomposeAC v' es rest r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlatX (c.ctx f .ac) (c.laws f) (.ac f (acPats es) rest) n env'.σ :=
  flatten_fix_sound_ac c v v' f es rest r env env' n hn hfresh (by rwa [runFK_ac] at h)

theorem flatten_kind_complete_ac (c : FCtx) (v v' : Var) (f : Sym) (es : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env : FEnvX) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.rest r = none)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlatX (c.ctx f .ac) (c.laws f) (.ac f (acPats es) rest) n σ') :
    ∃ env'' ∈ runFK c [.flatten v f .ac r, .decomposeAC v' es rest r] env,
      Binding.Extends env''.σ σ' := by
  rw [runFK_ac]
  exact flatten_fix_complete_ac c v v' f es rest r env n σ' hn hfresh hext hm

/-- ACI: the per-kind interpreter emits exactly the `MatchFlat` bindings of
the original rule (the opened-class clause is off for sets). -/
theorem flatten_kind_sound_aci (c : FCtx) (v v' : Var) (f : Sym) (es : List Var)
    (rest : Option Var) (r : Nat) (env env' : FEnvX) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.finRest r = none)
    (h : env' ∈ runFK c [.flatten v f .aci r, .decomposeACI v' es rest r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlat (c.ctx f .aci) (c.laws f) (.aci f (es.map Pat.var) rest) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runFK_two.1 h
  rw [runFStepK_flatten] at h₁
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flattenX_step hn).1 h₁
  simp only [runFStepK, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
    FEnvX.setView_σ, DemandX.acceptsKindB_aci] at h₂
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
  · rw [htaken, DemandX.acceptsOrigB_iff] at hacc
    exact (acceptsOrig_iff_altsAccept hwd taken).1 hacc

theorem flatten_kind_complete_aci (c : FCtx) (v v' : Var) (f : Sym) (es : List Var)
    (rest : Option Var) (r : Nat) (env : FEnvX) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.finRest r = none)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlat (c.ctx f .aci) (c.laws f) (.aci f (es.map Pat.var) rest) n σ') :
    ∃ env'' ∈ runFK c [.flatten v f .aci r, .decomposeACI v' es rest r] env,
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
    rw [mem_runFK_two]
    refine ⟨env.setView r (w, d), ?_, ?_⟩
    · rw [runFStepK_flatten]
      exact (mem_flattenX_step hn).2 ⟨(w, d), hwd, rfl⟩
    simp only [runFStepK, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
      FEnvX.setView_σ, DemandX.acceptsKindB_aci]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' es = taken :=
      taken_unique hext' hlen''.symm (by simpa using hlen.symm) hcls'' hcls'
    rw [htaken, DemandX.acceptsOrigB_iff]
    exact (acceptsOrig_iff_altsAccept hwd taken).2 halts

theorem flatten_kind_sound_assoc (c : FCtx) (v v' : Var) (f : Sym) (pre suf : Option Var)
    (es : List Var) (r : Nat) (env env' : FEnvX) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n)
    (hpre₀ : ∀ r, pre = some r → env.σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → env.σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (h : env' ∈ runFK c [.flatten v f .assoc r, .expandA v' pre es suf r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlat (c.ctx f .assoc) (c.laws f) (.assoc f pre (es.map Pat.var) suf) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runFK_two.1 h
  rw [runFStepK_flatten] at h₁
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flattenX_step hn).1 h₁
  simp only [runFStepK, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
    FEnvX.setView_σ, DemandX.acceptsKindB_assoc] at h₂
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
  · rw [htaken, DemandX.acceptsOrigB_iff] at hacc
    exact (acceptsOrig_iff_altsAccept hwd mid).1 hacc

theorem flatten_kind_complete_assoc (c : FCtx) (v v' : Var) (f : Sym) (pre suf : Option Var)
    (es : List Var) (r : Nat) (env : FEnvX) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n)
    (hpre₀ : ∀ r, pre = some r → env.σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → env.σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlat (c.ctx f .assoc) (c.laws f) (.assoc f pre (es.map Pat.var) suf) n σ') :
    ∃ env'' ∈ runFK c [.flatten v f .assoc r, .expandA v' pre es suf r] env,
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
    rw [mem_runFK_two]
    refine ⟨env.setView r (w, d), ?_, ?_⟩
    · rw [runFStepK_flatten]
      exact (mem_flattenX_step hn).2 ⟨(w, d), hwd, rfl⟩
    simp only [runFStepK, FEnvX.setView_views_self, List.mem_map, List.mem_filter,
      FEnvX.setView_σ, DemandX.acceptsKindB_assoc]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' es = taken :=
      taken_unique hext' hlen'' (by simpa using hlen.symm) hcls'' hcls'
    rw [htaken, DemandX.acceptsOrigB_iff]
    exact (acceptsOrig_iff_altsAccept hwd taken).2 halts

/-! ## Completeness of the per-kind rule: corollaries -/

theorem demand_kind_complete_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {n : Node}
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .ac Laws.free v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (rest₀ rest' : Multiset C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsKind .ac taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ RefoldsAC ctx rest₀ rest' := by
  obtain ⟨w', d, rest₀, rest', hd, hacc, hm', hr, hR⟩ :=
    demand_fix_complete_ac hκ hv hn helems hne hm
  exact ⟨w', d, rest₀, rest', hd, (DemandX.acceptsKind_ac d taken).2 hacc, hm', hr, hR⟩

theorem demand_kind_complete_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {n : Node}
    (htwo : TwoClasses ctx n)
    {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym} {elems : List Pat}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .aci Laws.free v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x)
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (rest₀ rest' : Finset C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsKind .aci taken ∧
      MatchV ctx.G (.aci f elems (some r)) (ofView .aci w') (σ.setSetRest r rest') taken ∧
      σ.finRest r = some rest₀ ∧ RefoldsACIT ctx taken rest₀ rest' := by
  obtain ⟨w', d, rest₀, rest', hd, hacc, hm', hr, hR⟩ :=
    demand_orig_complete_aci hκ htwo hv hn helems hm
  exact ⟨w', d, rest₀, rest', hd, (DemandX.acceptsKind_aci d taken).2 hacc, hm', hr, hR⟩

theorem demand_kind_complete_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) (hnn : NoNullary ctx)
    {n : Node} {v w : List (C × Nat)} {ls : List LeafX} {o : Nat} {f : Sym}
    {pre suf : Option Var} {args : List Pat} {σ : Binding} {mid u s : List C}
    (hv : RawViewX ctx n v ls o) (hn : normalize .assoc Laws.free v = .node w)
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x) (hne : args ≠ [])
    (hdist : ∀ rp rs, pre = some rp → suf = some rs → rp ≠ rs)
    (hm : MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w) σ mid)
    (hu : SeqRestOk σ pre u) (hs : SeqRestOk σ suf s) :
    ∃ (w' : List (C × Nat)) (d : DemandX) (σ' : Binding) (u' s' : List C),
      (w', d) ∈ enumerateX ctx Laws.free n ∧ d.acceptsKind .assoc mid ∧
      MatchV ctx.G (.assoc f pre args suf) (ofView .assoc w') σ' mid ∧
      σ'.cls = σ.cls ∧ σ'.node = σ.node ∧ σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧
      σ'.finRest = σ.finRest ∧
      SeqRestOk σ' pre u' ∧ SeqRestOk σ' suf s' ∧
      RefoldsAssoc ctx u u' ∧ RefoldsAssoc ctx s s' := by
  obtain ⟨w', d, σ', u', s', hd, hacc, h⟩ :=
    demand_orig_complete_assoc hκ hnn hv hn helems hne hdist hm hu hs
  exact ⟨w', d, σ', u', s', hd, (DemandX.acceptsKind_assoc d mid).2 hacc, h⟩

end Semper.EMatch.Flatten
