import SemperProofs.EMatch.Engine.Saturate.Actions

/-!
# Transport of bindings and fired instances across a round (spec-actions §D, §E)

Between two snapshots the union-find only merges (`Round.WF.no_split`) and
the stored children of a surviving node are rewritten to their new
representatives by `recanonize_node` (`caches.rs:525-608`, `caches.rs:948-1050`);
a node leaves the index only by subsumption (`index.rs:521`).
`Round.Persist` states this (spec-actions §D). `Round.transport` maps a
binding's classes and rests through the new `find`.

* `den_transport` / `fired_transport`: a consequence present before the
  round is present after it (no subsumption in the round: a `:subsume` of
  another rule can erase exactly the node a consequence is built of,
  `tests/egg/subsume.egg`).
* `matches_transport`: a match before the round is a match after it, at
  the same nodes, provided none of its nodes was subsumed and, for AC/ACI
  atoms, the round merged none of the matched node's children classes
  with each other (`Round.NoCollapse`). Without the last hypothesis the
  statement is false: `(Add x y)` matches `(Add a b)` and not `(Add a:2)`
  under maximum-partition semantics (engine: `scratchpad/sat-probe/ac_collapse.egg`).
-/

namespace Semper.EMatch

/-- `ch'` is `ch` with every class mapped through `f`, in the form the
store keeps: positions kept for tuples and sequences, the pair in either
order (the store sorts it), counts coalesced for a multiset, duplicates
dropped for a set. -/
def CanonCh (f : C → C) : Children → Children → Prop
  | .tuple cs, .tuple cs' => cs' = cs.map f
  | .spair a b, .spair a' b' => (a' = f a ∧ b' = f b) ∨ (a' = f b ∧ b' = f a)
  | .seq cs, .seq cs' => cs' = cs.map f
  | .mset m, .mset m' => m' = m.map f
  | .set s, .set s' => s' = s.image f
  | _, _ => False

namespace Round

/-- What the round guarantees about surviving nodes (spec-actions §D):
the before snapshot has idempotent `find` (it is a rebuilt snapshot), and
a node not subsumed in the round is in the after snapshot with the same
operator and its children recanonicalized. -/
structure Persist (R : Round) : Prop where
  before_find_idem : R.before.FindIdem
  persist : ∀ id n, (id, n) ∈ R.before.nodes → id ∉ R.subsumed →
    ∃ n', (id, n') ∈ R.after.nodes ∧ n'.op = n.op ∧ CanonCh R.after.find n.children n'.children

/-- The binding after the round: classes and rests mapped through the new
`find`; node and multiplicity variables unchanged. -/
def transport (R : Round) (σ : Binding) : Binding where
  cls := fun x => (σ.cls x).map R.after.find
  node := σ.node
  mult := σ.mult
  rest := fun r => (σ.rest r).map (Multiset.map R.after.find)
  seqRest := fun r => (σ.seqRest r).map (List.map R.after.find)
  finRest := fun r => (σ.finRest r).map (Finset.image R.after.find)

@[simp] theorem transport_cls (R : Round) (σ : Binding) (x : Var) :
    (R.transport σ).cls x = (σ.cls x).map R.after.find := rfl
@[simp] theorem transport_node (R : Round) (σ : Binding) (v : Var) :
    (R.transport σ).node v = σ.node v := rfl
@[simp] theorem transport_mult (R : Round) (σ : Binding) (k : Var) :
    (R.transport σ).mult k = σ.mult k := rfl
@[simp] theorem transport_rest (R : Round) (σ : Binding) (r : Var) :
    (R.transport σ).rest r = (σ.rest r).map (Multiset.map R.after.find) := rfl
@[simp] theorem transport_seqRest (R : Round) (σ : Binding) (r : Var) :
    (R.transport σ).seqRest r = (σ.seqRest r).map (List.map R.after.find) := rfl
@[simp] theorem transport_finRest (R : Round) (σ : Binding) (r : Var) :
    (R.transport σ).finRest r = (σ.finRest r).map (Finset.image R.after.find) := rfl

/-- The new `find` of an old representative is the new `find` of the class. -/
theorem find_before {R : Round} (hwf : R.WF) (hb : R.before.FindIdem) (c : C) :
    R.after.find (R.before.find c) = R.after.find c :=
  hwf.no_split _ _ (hb c)

theorem find_comp_before {R : Round} (hwf : R.WF) (hb : R.before.FindIdem) :
    R.after.find ∘ R.before.find = R.after.find :=
  funext (find_before hwf hb)

theorem find_comp_self {R : Round} (hwf : R.WF) :
    R.after.find ∘ R.after.find = R.after.find :=
  funext hwf.find_idem

end Round

/-! ## Transport of `Den` and `Fired` -/

theorem rMultOk_transport (R : Round) (σ : Binding) (μ : Mult) (n : Nat) :
    RMultOk (R.transport σ) μ n ↔ RMultOk σ μ n := by
  cases μ <;> rfl

theorem multOk_transport (R : Round) (σ : Binding) (μ : Mult) (n : Nat) :
    MultOk (R.transport σ) μ n ↔ MultOk σ μ n := by
  cases μ <;> rfl

/-- `Den` is carried by the transported binding: a term built before the
round is built after it, at the same nodes, with the new value. -/
theorem den_transport {R : Round} (hwf : R.WF) (hp : R.Persist) (hsub : R.subsumed = ∅)
    {σ : Binding} {t : Pat} {c : C} (h : Den R.before σ t c) :
    Den R.after (R.transport σ) t (R.after.find c) := by
  have hfb := Round.find_before hwf hp.before_find_idem
  have hfc := Round.find_comp_before hwf hp.before_find_idem
  have hff := Round.find_comp_self hwf
  have hfi : ∀ c, R.after.find (R.after.find c) = R.after.find c := hwf.find_idem
  have hpers : ∀ id n, (id, n) ∈ R.before.nodes →
      ∃ n', (id, n') ∈ R.after.nodes ∧ n'.op = n.op ∧
        CanonCh R.after.find n.children n'.children :=
    fun id n hmem => hp.persist id n hmem (by simp [hsub])
  induction h with
  | var hx =>
      rw [hfb, ← hwf.find_idem]
      exact Den.var (by simp [hx])
  | plain hl hall hmem ih =>
      rename_i f args cs id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      rw [hfb]
      refine Den.plain (by simp [hl]) ?_ hmem'
      intro pc hpc
      rw [List.zip_map_right, List.mem_map] at hpc
      obtain ⟨pc', hpc', rfl⟩ := hpc
      exact ih pc' hpc'
  | comm ha hb hmem iha ihb =>
      rename_i f p q a b id
      rw [hfb]
      rcases hmem with hmem | hmem
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Den.comm iha ihb (Or.inl hmem')
        · exact Den.comm iha ihb (Or.inr hmem')
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Den.comm iha ihb (Or.inr hmem')
        · exact Den.comm iha ihb (Or.inl hmem')
  | assoc hl hall hpre hsuf hmem ih =>
      rename_i f pre suf args cs u v id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      rw [hfb]
      refine Den.assoc (cs := cs.map R.after.find) (u := u.map R.after.find)
        (v := v.map R.after.find) (by simp [hl]) ?_ ?_ ?_ ?_
      · intro pc hpc
        rw [List.zip_map_right, List.mem_map] at hpc
        obtain ⟨pc', hpc', rfl⟩ := hpc
        exact ih pc' hpc'
      · cases pre with
        | none => simp [SeqRestOk] at hpre; simp [SeqRestOk, hpre]
        | some r => simp [SeqRestOk] at hpre; simp [SeqRestOk, hpre]
      · cases suf with
        | none => simp [SeqRestOk] at hsuf; simp [SeqRestOk, hsuf]
        | some r => simp [SeqRestOk] at hsuf; simp [SeqRestOk, hsuf]
      · simpa [List.map_append, List.map_map, hfc, hff] using hmem'
  | ac hl hmult hden hrest hmem ih =>
      rename_i f elems rest cks m₀ id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      rw [hfb]
      refine Den.ac (cks := cks.map fun ck => (R.after.find ck.1, ck.2)) (m₀ := m₀.map R.after.find)
        (by simp [hl]) ?_ ?_ ?_ ?_
      · intro ek hek
        rw [List.zip_map_right, List.mem_map] at hek
        obtain ⟨ek', hek', rfl⟩ := hek
        rw [rMultOk_transport]
        exact hmult ek' hek'
      · intro ek hek hk
        rw [List.zip_map_right, List.mem_map] at hek
        obtain ⟨ek', hek', rfl⟩ := hek
        exact ih ek' hek' hk
      · cases rest with
        | none => simp [MsetRestVal] at hrest; simp [MsetRestVal, hrest]
        | some r => simp [MsetRestVal] at hrest; simp [MsetRestVal, hrest]
      · simpa [Multiset.map_add, Multiset.map_map, acChildren_map, hfc, hff, hfb, hfi] using hmem'
  | aci hl hall hrest hmem ih =>
      rename_i f elems rest cs s₀ id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      rw [hfb]
      refine Den.aci (cs := cs.map R.after.find) (s₀ := s₀.image R.after.find)
        (by simp [hl]) ?_ ?_ ?_
      · intro pc hpc
        rw [List.zip_map_right, List.mem_map] at hpc
        obtain ⟨pc', hpc', rfl⟩ := hpc
        exact ih pc' hpc'
      · cases rest with
        | none => simp [SetRestVal] at hrest; simp [SetRestVal, hrest]
        | some r => simp [SetRestVal] at hrest; simp [SetRestVal, hrest]
      · have htf : (cs.map R.after.find).toFinset = cs.toFinset.image R.after.find := by
          ext c; simp
        simpa [Finset.image_union, Finset.image_image, htf, hfc, hff, hfb, hfi] using hmem'

theorem actFired_transport {R : Round} (hwf : R.WF) (hp : R.Persist) (hsub : R.subsumed = ∅)
    {σ : Binding} {act : Action} (h : ActFired R.before σ act) :
    ActFired R.after (R.transport σ) act := by
  cases act with
  | insert t =>
      obtain ⟨c, hc⟩ := h
      exact ⟨_, den_transport hwf hp hsub hc⟩
  | union a b =>
      obtain ⟨c, ha, hb⟩ := h
      exact ⟨_, den_transport hwf hp hsub ha, den_transport hwf hp hsub hb⟩
  | subsume _ => trivial

/-- A fired instance stays fired: `Fired R.before σ rule → Fired R.after (R.transport σ) rule`. -/
theorem fired_transport {R : Round} (hwf : R.WF) (hp : R.Persist) (hsub : R.subsumed = ∅)
    {σ : Binding} {rule : Rule} (h : Fired R.before σ rule) :
    Fired R.after (R.transport σ) rule :=
  fun act hact => actFired_transport hwf hp hsub (h act hact)

/-! `Den` canonicalizes the binding's classes itself, so on the after
snapshot the transported binding and the original one build the same
terms. -/

theorem den_transport_iff {R : Round} (hwf : R.WF) {σ : Binding} {t : Pat} {c : C} :
    Den R.after (R.transport σ) t c ↔ Den R.after σ t c := by
  have hff := Round.find_comp_self hwf
  have hfi : ∀ c, R.after.find (R.after.find c) = R.after.find c := hwf.find_idem
  constructor
  · intro h
    induction h with
    | var hx =>
        rename_i x c
        simp only [Round.transport_cls, Option.map_eq_some_iff] at hx
        obtain ⟨c₀, hc₀, rfl⟩ := hx
        rw [hwf.find_idem]
        exact Den.var hc₀
    | plain hl hall hmem ih => exact Den.plain hl ih hmem
    | comm ha hb hmem iha ihb => exact Den.comm iha ihb hmem
    | assoc hl hall hpre hsuf hmem ih =>
        rename_i f pre suf args cs u v id
        cases pre with
        | none =>
            simp [SeqRestOk] at hpre; subst hpre
            cases suf with
            | none =>
                simp [SeqRestOk] at hsuf; subst hsuf
                exact Den.assoc hl ih (u := []) (v := []) (by simp [SeqRestOk]) (by simp [SeqRestOk])
                  (by simpa using hmem)
            | some r =>
                simp only [SeqRestOk, Round.transport_seqRest, Option.map_eq_some_iff] at hsuf
                obtain ⟨v₀, hv₀, rfl⟩ := hsuf
                refine Den.assoc hl ih (u := []) (v := v₀) (by simp [SeqRestOk]) hv₀ ?_
                simpa [List.map_map, hff, hfi] using hmem
        | some r =>
            simp only [SeqRestOk, Round.transport_seqRest, Option.map_eq_some_iff] at hpre
            obtain ⟨u₀, hu₀, rfl⟩ := hpre
            cases suf with
            | none =>
                simp [SeqRestOk] at hsuf; subst hsuf
                refine Den.assoc hl ih (u := u₀) (v := []) hu₀ (by simp [SeqRestOk]) ?_
                simpa [List.map_map, hff, hfi] using hmem
            | some r' =>
                simp only [SeqRestOk, Round.transport_seqRest, Option.map_eq_some_iff] at hsuf
                obtain ⟨v₀, hv₀, rfl⟩ := hsuf
                refine Den.assoc hl ih (u := u₀) hu₀ (v := v₀) hv₀ ?_
                simpa [List.map_map, hff] using hmem
    | ac hl hmult hden hrest hmem ih =>
        rename_i f elems rest cks m₀ id
        have hmult' : ∀ ek ∈ elems.zip cks, RMultOk σ ek.1.2 ek.2.2 :=
          fun ek hek => (rMultOk_transport R σ _ _).1 (hmult ek hek)
        cases rest with
        | none =>
            simp [MsetRestVal] at hrest; subst hrest
            exact Den.ac hl hmult' ih (m₀ := 0) (by simp [MsetRestVal]) (by simpa using hmem)
        | some r =>
            simp only [MsetRestVal, Round.transport_rest, Option.map_eq_some_iff] at hrest
            obtain ⟨m, hm, rfl⟩ := hrest
            refine Den.ac hl hmult' ih (m₀ := m) hm ?_
            simpa [Multiset.map_map, hff, hfi] using hmem
    | aci hl hall hrest hmem ih =>
        rename_i f elems rest cs s₀ id
        cases rest with
        | none =>
            simp [SetRestVal] at hrest; subst hrest
            exact Den.aci hl ih (s₀ := ∅) (by simp [SetRestVal]) (by simpa using hmem)
        | some r =>
            simp only [SetRestVal, Round.transport_finRest, Option.map_eq_some_iff] at hrest
            obtain ⟨s, hs, rfl⟩ := hrest
            refine Den.aci hl ih (s₀ := s) hs ?_
            simpa [Finset.image_image, hff, hfi] using hmem
  · intro h
    induction h with
    | var hx =>
        rename_i x c
        rw [← hwf.find_idem]
        exact Den.var (by simp [hx])
    | plain hl hall hmem ih => exact Den.plain hl ih hmem
    | comm ha hb hmem iha ihb => exact Den.comm iha ihb hmem
    | assoc hl hall hpre hsuf hmem ih =>
        rename_i f pre suf args cs u v id
        refine Den.assoc hl ih (u := u.map R.after.find) (v := v.map R.after.find) ?_ ?_ ?_
        · cases pre with
          | none => simp [SeqRestOk] at hpre; simp [SeqRestOk, hpre]
          | some r => simp [SeqRestOk] at hpre; simp [SeqRestOk, hpre]
        · cases suf with
          | none => simp [SeqRestOk] at hsuf; simp [SeqRestOk, hsuf]
          | some r => simp [SeqRestOk] at hsuf; simp [SeqRestOk, hsuf]
        · simpa [List.map_map, hff, hfi] using hmem
    | ac hl hmult hden hrest hmem ih =>
        rename_i f elems rest cks m₀ id
        have hmult' : ∀ ek ∈ elems.zip cks, RMultOk (R.transport σ) ek.1.2 ek.2.2 :=
          fun ek hek => (rMultOk_transport R σ _ _).2 (hmult ek hek)
        refine Den.ac hl hmult' ih (m₀ := m₀.map R.after.find) ?_ ?_
        · cases rest with
          | none => simp [MsetRestVal] at hrest; simp [MsetRestVal, hrest]
          | some r => simp [MsetRestVal] at hrest; simp [MsetRestVal, hrest]
        · simpa [Multiset.map_map, hff, hfi] using hmem
    | aci hl hall hrest hmem ih =>
        rename_i f elems rest cs s₀ id
        refine Den.aci hl ih (s₀ := s₀.image R.after.find) ?_ ?_
        · cases rest with
          | none => simp [SetRestVal] at hrest; simp [SetRestVal, hrest]
          | some r => simp [SetRestVal] at hrest; simp [SetRestVal, hrest]
        · simpa [Finset.image_image, hff, hfi] using hmem

theorem fired_transport_iff {R : Round} (hwf : R.WF) {σ : Binding} {rule : Rule} :
    Fired R.after (R.transport σ) rule ↔ Fired R.after σ rule := by
  unfold Fired
  refine forall_congr' fun act => forall_congr' fun _ => ?_
  cases act with
  | insert t => simp only [ActFired, den_transport_iff hwf]
  | union a b => simp only [ActFired, den_transport_iff hwf]
  | subsume _ => exact Iff.rfl

/-- `fired_transport` for the binding itself: a fired instance of the
before snapshot is fired, as the same binding, in the after snapshot. -/
theorem fired_transport' {R : Round} (hwf : R.WF) (hp : R.Persist) (hsub : R.subsumed = ∅)
    {σ : Binding} {rule : Rule} (h : Fired R.before σ rule) : Fired R.after σ rule :=
  (fired_transport_iff hwf).1 (fired_transport hwf hp hsub h)

/-! ## Transport of matches -/

/-- The round merged none of the matched node's children classes with
each other, for an AC or ACI atom: the new `find` is injective on the
stored multiset's or set's support. Vacuous for the other shapes. -/
def Round.NoCollapse (R : Round) (σ : Binding) (a : RAtom) : Prop :=
  ∀ id n, σ.node a.node = some id → (id, n) ∈ R.before.nodes →
    match n.children with
    | .mset m => Set.InjOn R.after.find {c | c ∈ m}
    | .set s => Set.InjOn R.after.find (↑s : Set C)
    | _ => True

theorem seqRestOk_transport {R : Round} {σ : Binding} {pre : Option Var} {u : List C}
    (h : SeqRestOk σ pre u) : SeqRestOk (R.transport σ) pre (u.map R.after.find) := by
  cases pre with
  | none => simp [SeqRestOk] at h; simp [SeqRestOk, h]
  | some r => simp [SeqRestOk] at h; simp [SeqRestOk, h]

/-- The per-atom transport. -/
theorem atomSat_transport {R : Round} (hwf : R.WF) (hp : R.Persist) {σ : Binding} {a : RAtom}
    (h : AtomSat R.before σ a)
    (hns : ∀ id, σ.node a.node = some id → id ∉ R.subsumed)
    (hnc : R.NoCollapse σ a) :
    AtomSat R.after (R.transport σ) a := by
  obtain ⟨id, n, hid, hmem, hcls, hop, hm⟩ := h
  obtain ⟨⟨op, ch⟩, hmem', hop', hch⟩ := hp.persist id n hmem (hns id hid)
  simp only at hop'
  subst hop'
  have hnc' := hnc id n hid hmem
  refine ⟨id, ⟨n.op, ch⟩, hid, hmem', ?_, hop, ?_⟩
  · simp [hcls, Round.find_before hwf hp.before_find_idem]
  rcases a with ⟨nv, aop, shape⟩
  simp only at hop
  cases shape with
  | plain cs =>
      simp only [RAtom.shallow] at hm ⊢
      rw [matchN_plain_vars] at hm ⊢
      obtain ⟨cs', hn, hall⟩ := hm
      subst hn
      cases ch <;> simp [CanonCh] at hch
      subst hch
      refine ⟨cs'.map R.after.find, rfl, ?_⟩
      rw [List.forall₂_map_right_iff]
      exact hall.imp fun _ _ hx => by simp [hx]
  | comm x y =>
      simp only [RAtom.shallow] at hm ⊢
      rw [matchN_comm_vars] at hm ⊢
      obtain ⟨a, b, hn, hab⟩ := hm
      subst hn
      cases ch <;> simp [CanonCh] at hch
      rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨_, _, rfl, ?_⟩
        rcases hab with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inl ⟨by simp [hx], by simp [hy]⟩
        · exact Or.inr ⟨by simp [hx], by simp [hy]⟩
      · refine ⟨_, _, rfl, ?_⟩
        rcases hab with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inr ⟨by simp [hx], by simp [hy]⟩
        · exact Or.inl ⟨by simp [hx], by simp [hy]⟩
  | assoc pre fx suf =>
      simp only [RAtom.shallow] at hm ⊢
      rw [matchN_assoc_vars] at hm ⊢
      obtain ⟨u, mid, v, hn, hpre, hsuf, hall⟩ := hm
      subst hn
      cases ch <;> simp [CanonCh] at hch
      subst hch
      refine ⟨u.map R.after.find, mid.map R.after.find, v.map R.after.find, by simp,
        seqRestOk_transport hpre, seqRestOk_transport hsuf, ?_⟩
      rw [List.forall₂_map_right_iff]
      exact hall.imp fun _ _ hx => by simp [hx]
  | ac es rest =>
      simp only [RAtom.shallow] at hm ⊢
      rw [matchN_ac_vars] at hm ⊢
      obtain ⟨m, taken, hn, hnd, hl, hmemt, hcls', hmult, hrest⟩ := hm
      subst hn
      cases ch <;> simp [CanonCh] at hch
      subst hch
      try simp only at hnc'
      have hinj : ∀ x ∈ taken, ∀ y ∈ taken, R.after.find x = R.after.find y → x = y :=
        fun x hx y hy hxy => hnc' (hmemt x hx) (hmemt y hy) hxy
      refine ⟨m.map R.after.find, taken.map R.after.find, rfl, hnd.map_on hinj, by simp [hl],
        ?_, ?_, ?_, ?_⟩
      · intro c hc
        rw [List.mem_map] at hc
        obtain ⟨c₀, hc₀, rfl⟩ := hc
        exact Multiset.mem_map_of_mem _ (hmemt c₀ hc₀)
      · intro et het
        rw [List.zip_map_right, List.mem_map] at het
        obtain ⟨et', het', rfl⟩ := het
        simp [hcls' et' het']
      · intro et het
        rw [List.zip_map_right, List.mem_map] at het
        obtain ⟨et', het', rfl⟩ := het
        show MultOk (R.transport σ) et'.1.2 ((m.map R.after.find).count (R.after.find et'.2))
        rw [multOk_transport, Multiset.count_map_eq_count _ _ hnc' _ (hmemt _ (List.of_mem_zip het').2)]
        exact hmult et' het'
      · cases rest with
        | none =>
            simp only [MsetRestOk] at hrest ⊢
            intro c hc
            rw [Multiset.mem_map] at hc
            obtain ⟨c₀, hc₀, rfl⟩ := hc
            exact List.mem_map_of_mem (hrest c₀ hc₀)
        | some r =>
            simp only [MsetRestOk, Round.transport_rest] at hrest ⊢
            have hfilt : (m.map R.after.find).filter (fun c => c ∉ taken.map R.after.find) =
                (m.filter (fun c => c ∉ taken)).map R.after.find := by
              rw [Multiset.filter_map]
              congr 1
              apply Multiset.filter_congr
              intro x hx
              show R.after.find x ∉ taken.map R.after.find ↔ x ∉ taken
              constructor
              · intro h hx'
                exact h (List.mem_map_of_mem hx')
              · intro h hfx
                obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hfx
                exact h (hnc' (hmemt y hy) hx hxy ▸ hy)
            rw [hrest, hfilt]
            rfl
  | aci es rest =>
      simp only [RAtom.shallow] at hm ⊢
      rw [matchN_aci_vars] at hm ⊢
      obtain ⟨s, taken, hn, hnd, hl, hmemt, hcls', hrest⟩ := hm
      subst hn
      cases ch <;> simp [CanonCh] at hch
      subst hch
      try simp only at hnc'
      have hinj : ∀ x ∈ taken, ∀ y ∈ taken, R.after.find x = R.after.find y → x = y :=
        fun x hx y hy hxy => hnc' (Finset.mem_coe.2 (hmemt x hx)) (Finset.mem_coe.2 (hmemt y hy)) hxy
      refine ⟨s.image R.after.find, taken.map R.after.find, rfl, hnd.map_on hinj, by simp [hl],
        ?_, ?_, ?_⟩
      · intro c hc
        rw [List.mem_map] at hc
        obtain ⟨c₀, hc₀, rfl⟩ := hc
        exact Finset.mem_image_of_mem _ (hmemt c₀ hc₀)
      · intro et het
        rw [List.zip_map_right, List.mem_map] at het
        obtain ⟨et', het', rfl⟩ := het
        simp [hcls' et' het']
      · cases rest with
        | none =>
            simp only [SetRestOk] at hrest ⊢
            intro c hc
            rw [Finset.mem_image] at hc
            obtain ⟨c₀, hc₀, rfl⟩ := hc
            exact List.mem_map_of_mem (hrest c₀ hc₀)
        | some r =>
            simp only [SetRestOk, Round.transport_finRest] at hrest ⊢
            have hfilt : (s.image R.after.find).filter (fun c => c ∉ taken.map R.after.find) =
                (s.filter (fun c => c ∉ taken)).image R.after.find := by
              rw [Finset.filter_image]
              congr 1
              apply Finset.filter_congr
              intro x hx
              show R.after.find x ∉ taken.map R.after.find ↔ x ∉ taken
              constructor
              · intro h hx'
                exact h (List.mem_map_of_mem hx')
              · intro h hfx
                obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hfx
                exact h (hnc' (Finset.mem_coe.2 (hmemt y hy)) (Finset.mem_coe.2 hx) hxy ▸ hy)
            rw [hrest, hfilt]
            rfl

/-- `matches_transport`: a match of the before snapshot is a match of the
after snapshot under the transported binding, provided none of its nodes
was subsumed in the round and no AC/ACI atom's node had two of its children
classes merged (`Round.NoCollapse`; spec-actions §E for the counterexample). -/
theorem matches_transport {R : Round} (hwf : R.WF) (hp : R.Persist) {atoms : List QAtom}
    {σ : Binding} (h : Matches R.before atoms σ)
    (hns : ∀ a, QAtom.scan a ∈ atoms → ∀ id, σ.node a.node = some id → id ∉ R.subsumed)
    (hnc : ∀ a, QAtom.scan a ∈ atoms → R.NoCollapse σ a) :
    Matches R.after atoms (R.transport σ) where
  sat q hq := by
    cases q with
    | scan a => exact atomSat_transport hwf hp (h.sat _ hq) (hns a hq) (hnc a hq)
    | eq x y =>
        obtain ⟨c, hx, hy⟩ := h.sat _ hq
        exact ⟨R.after.find c, by simp [hx], by simp [hy]⟩
  clsDom x := by rw [← h.clsDom x]; simp
  node v := by rw [← h.node v]; simp
  mult k := by rw [← h.mult k]; simp
  rest r := by rw [← h.rest r]; simp
  seqRest r := by rw [← h.seqRest r]; simp
  finRest r := by rw [← h.finRest r]; simp

end Semper.EMatch

/-! ## Persistence of the fixed-arity nodes only

`recanonize_node` maps the children of a tuple, pair or sequence node
through `find` and nothing else (`canon.rs`, `PlainCanon`, `CCanon`,
`OrderedCanon`). For a multiset or set node it also drops the unit's class
and clamps the counts (`MSetCanon`, `SetCanon`), and a degenerate result
merges the node's class with a leaf (`degeneracy_pair`). `Round.PersistFixed`
states only the first: it is what every rebuild establishes, and it
carries the instances of the rules whose right-hand sides build no n-ary
term (`fired_transport_fixed'`). The rules that do are re-matched in full
after a round whose rebuild was not literal (`Saturate/Invariant.lean`,
`route`). -/

namespace Semper.EMatch

/-- `CanonCh` of canonical children by the identity. -/
theorem canonCh_self {G : Graph} {ch : Children} (hc : Children.Canon G ch) :
    CanonCh G.find ch ch := by
  cases ch with
  | tuple cs =>
      show cs = cs.map G.find
      have hc' : ∀ c ∈ cs, G.find c = _root_.id c := hc
      rw [List.map_congr_left hc', List.map_id]
  | spair a b => exact Or.inl ⟨hc.1.symm, hc.2.symm⟩
  | seq cs =>
      show cs = cs.map G.find
      have hc' : ∀ c ∈ cs, G.find c = _root_.id c := hc
      rw [List.map_congr_left hc', List.map_id]
  | mset m =>
      show m = m.map G.find
      have hc' : ∀ c ∈ m, G.find c = _root_.id c := hc
      rw [Multiset.map_congr rfl hc', Multiset.map_id]
  | set s =>
      show s = s.image G.find
      have hc' : Set.EqOn G.find _root_.id s := fun x hx => hc x hx
      rw [Finset.image_congr hc', Finset.image_id]

namespace Round

/-- The fixed-arity nodes (tuple, pair) persist literally: what
`recanonize_node` does to them. The guard `isVariadic = false` excludes the
sequence nodes, which `recanonize_node` treats the same way; their case is
`LiteralSeq` (`StorePersistE.seq`, `Fidelity/RecanonComplete.lean`). -/
structure PersistFixed (R : Round) : Prop where
  before_find_idem : R.before.FindIdem
  persist : ∀ id n, (id, n) ∈ R.before.nodes → id ∉ R.subsumed →
    n.children.isVariadic = false →
    ∃ n', (id, n') ∈ R.after.nodes ∧ n'.op = n.op ∧ CanonCh R.after.find n.children n'.children

theorem Persist.toFixed {R : Round} (hp : R.Persist) : R.PersistFixed where
  before_find_idem := hp.before_find_idem
  persist := fun id n hmem hsub _ => hp.persist id n hmem hsub

end Round

/-- `den_transport` for a term without n-ary application: only the
fixed-arity nodes need to persist. -/
theorem den_transport_fixed {R : Round} (hwf : R.WF) (hp : R.PersistFixed)
    (hsub : R.subsumed = ∅) {σ : Binding} {t : Pat} (ht : t.hasNary = false) {c : C}
    (h : Den R.before σ t c) : Den R.after (R.transport σ) t (R.after.find c) := by
  have hfb := Round.find_before hwf hp.before_find_idem
  have hpers : ∀ id n, (id, n) ∈ R.before.nodes → n.children.isVariadic = false →
      ∃ n', (id, n') ∈ R.after.nodes ∧ n'.op = n.op ∧
        CanonCh R.after.find n.children n'.children :=
    fun id n hmem hv => hp.persist id n hmem (by simp [hsub]) hv
  induction h with
  | var hx =>
      rw [hfb, ← hwf.find_idem]
      exact Den.var (by simp [hx])
  | plain hl hall hmem ih =>
      rename_i f args cs id
      have hargs : ∀ p ∈ args, p.hasNary = false :=
        Pat.hasNaryList_eq_false.1 (by simpa [Pat.hasNary] using ht)
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem rfl
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      rw [hfb]
      refine Den.plain (by simp [hl]) ?_ hmem'
      intro pc hpc
      rw [List.zip_map_right, List.mem_map] at hpc
      obtain ⟨pc', hpc', rfl⟩ := hpc
      exact ih pc' hpc' (hargs _ (List.of_mem_zip hpc').1)
  | comm ha hb hmem iha ihb =>
      rename_i f p q a b id
      have hpq : p.hasNary = false ∧ q.hasNary = false := by simpa [Pat.hasNary] using ht
      rw [hfb]
      rcases hmem with hmem | hmem
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem rfl
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Den.comm (iha hpq.1) (ihb hpq.2) (Or.inl hmem')
        · exact Den.comm (iha hpq.1) (ihb hpq.2) (Or.inr hmem')
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := hpers _ _ hmem rfl
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Den.comm (iha hpq.1) (ihb hpq.2) (Or.inr hmem')
        · exact Den.comm (iha hpq.1) (ihb hpq.2) (Or.inl hmem')
  | assoc => simp [Pat.hasNary] at ht
  | ac => simp [Pat.hasNary] at ht
  | aci => simp [Pat.hasNary] at ht

/-- `fired_transport'` for a rule that builds no n-ary term. -/
theorem fired_transport_fixed' {R : Round} (hwf : R.WF) (hp : R.PersistFixed)
    (hsub : R.subsumed = ∅) {σ : Binding} {rule : Rule} (hr : rule.buildsNary = false)
    (h : Fired R.before σ rule) : Fired R.after σ rule := by
  have hr' : ∀ act ∈ rule.actions, act.hasNary = false := by
    simpa [Rule.buildsNary, List.any_eq_false] using hr
  rw [← fired_transport_iff hwf]
  intro act hact
  have hn := hr' act hact
  have := h act hact
  cases act with
  | insert t =>
      obtain ⟨c, hc⟩ := this
      exact ⟨_, den_transport_fixed hwf hp hsub (by simpa [Action.hasNary] using hn) hc⟩
  | union a b =>
      obtain ⟨c, ha, hb⟩ := this
      have hab : a.hasNary = false ∧ b.hasNary = false := by simpa [Action.hasNary] using hn
      exact ⟨_, den_transport_fixed hwf hp hsub hab.1 ha, den_transport_fixed hwf hp hsub hab.2 hb⟩
  | subsume _ => trivial

end Semper.EMatch
