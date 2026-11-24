import SemperProofs.Fidelity.NormalizeSat

/-!
# Soundness of what the actions build (fidelity row: action soundness)

`Saturate.Inv` says every match is fired: the graph holds every consequence
it must. This file gives the other direction at the level of the actions:
what `instantiate` builds denotes the right-hand side. A model is an
algebra `Alg M` (each operator a function of its children's values) and a
valuation `v` of the classes that respects `find` and the stored nodes
(`Models`); the operator laws hold in it (`LawsHold`: the normalization
steps of `add` and the degenerate arities preserve values, the commutative
pair is unordered, a set operator reads its elements only).

* `denN_sound`: the class `add` returns for a right-hand side (`DenN`)
  has, in every such model, the value of the term (`TVal`).
* `firedN_sound`: a fired union holds in every model: both sides have one
  value.
* `union_recorded_sound`: the pair of classes a `Union` action records has
  equal values in every model in which the rule's equation holds at the
  match, so merging it keeps the model (`models_of_merge`).

Not covered here: the rebuild's own merges (congruence, canonical repair,
completion), which `CC/` proves sound for the completion steps
(`completion_sound`); gluing them into one round-level statement is open.
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- Children with values in `M`. A set operator's children are given as a
multiset; `LawsHold.set_ext` makes its value depend on the elements only. -/
inductive MCh (M : Type) where
  | tuple (l : List M)
  | spair (a b : M)
  | seq (l : List M)
  | mset (m : Multiset M)
  | set (m : Multiset M)

variable {M : Type}

/-- The values of stored children. -/
def _root_.Semper.EMatch.Children.val (v : C → M) : Children → MCh M
  | .tuple cs => .tuple (cs.map v)
  | .spair a b => .spair (v a) (v b)
  | .seq cs => .seq (cs.map v)
  | .mset m => .mset (m.map v)
  | .set s => .set (s.val.map v)

/-- An algebra: each operator is a function of its children's values. -/
structure Alg (M : Type) where
  ev : Sym → MCh M → M

/-- `v` is a model of the graph: constant on classes, each stored node's
class has the value of its operator applied to its children. -/
def Models (G : Graph) (A : Alg M) (v : C → M) : Prop :=
  (∀ c, v (G.find c) = v c) ∧ ∀ id n, (id, n) ∈ G.nodes → v id = A.ev n.op (n.children.val v)

/-- The operator laws in the model (`OpLaws`, `:assoc-comm`, `:comm`,
`:assoc`, unit, nilpotent, inverse), stated as what `add` relies on. -/
structure LawsHold (G : Graph) (L : Sym → OpLaws) (A : Alg M) (v : C → M) : Prop where
  comm : ∀ f a b, A.ev f (.spair a b) = A.ev f (.spair b a)
  ac_step : ∀ f m m', ACStep G L f m m' → A.ev f (.mset (m.map v)) = A.ev f (.mset (m'.map v))
  aci_step : ∀ f s s', ACIStep G L f s s' →
    A.ev f (.set (s.val.map v)) = A.ev f (.set (s'.val.map v))
  a_step : ∀ f l l', AStep G L f l l' → A.ev f (.seq (l.map v)) = A.ev f (.seq (l'.map v))
  set_ext : ∀ f m m', (∀ x, x ∈ m ↔ x ∈ m') → A.ev f (.set m) = A.ev f (.set m')
  single_mset : ∀ f x, A.ev f (.mset {x}) = x
  single_set : ∀ f x, A.ev f (.set {x}) = x
  single_seq : ∀ f x, A.ev f (.seq [x]) = x
  unit_mset : ∀ f u, (L f).unit = some u → A.ev f (.mset 0) = v u
  unit_set : ∀ f u, (L f).unit = some u → A.ev f (.set 0) = v u
  unit_seq : ∀ f u, (L f).unit = some u → A.ev f (.seq []) = v u

/-- Counted children with values. -/
def acM : List (M × Nat) → Multiset M
  | [] => 0
  | (x, k) :: xks => k • ({x} : Multiset M) + acM xks

theorem acChildren_map_val (v : C → M) : ∀ cks : List (C × Nat),
    (acChildren cks).map v = acM (cks.map fun ck => (v ck.1, ck.2))
  | [] => by simp [acChildren, acM]
  | (c, k) :: cks => by
      simp only [acChildren, acM, Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton,
        List.map_cons, acChildren_map_val v cks]

/-- `TVal A v σ t x`: the right-hand side `t` has value `x` in the model,
read with the binding `σ` (classes through `v`). -/
inductive TVal (A : Alg M) (v : C → M) (σ : Binding) : Pat → M → Prop
  | var {x : Var} {c : C} : σ.cls x = some c → TVal A v σ (.var x) (v c)
  | plain {f : Sym} {args : List Pat} {ms : List M} :
      args.length = ms.length → (∀ pm ∈ args.zip ms, TVal A v σ pm.1 pm.2) →
      TVal A v σ (.plain f args) (A.ev f (.tuple ms))
  | comm {f : Sym} {p q : Pat} {a b : M} :
      TVal A v σ p a → TVal A v σ q b → TVal A v σ (.comm f p q) (A.ev f (.spair a b))
  | assoc {f : Sym} {pre suf : Option Var} {args : List Pat} {ms : List M} {u w : List C} :
      args.length = ms.length → (∀ pm ∈ args.zip ms, TVal A v σ pm.1 pm.2) →
      SeqRestOk σ pre u → SeqRestOk σ suf w →
      TVal A v σ (.assoc f pre args suf) (A.ev f (.seq (u.map v ++ ms ++ w.map v)))
  | ac {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var} {xks : List (M × Nat)}
      {m₀ : Multiset C} :
      elems.length = xks.length →
      (∀ ek ∈ elems.zip xks, RMultOk σ ek.1.2 ek.2.2) →
      (∀ ek ∈ elems.zip xks, ek.2.2 ≠ 0 → TVal A v σ ek.1.1 ek.2.1) →
      MsetRestVal σ rest m₀ →
      TVal A v σ (.ac f elems rest) (A.ev f (.mset (acM xks + m₀.map v)))
  | aci {f : Sym} {elems : List Pat} {rest : Option Var} {ms : List M} {s₀ : Finset C} :
      elems.length = ms.length → (∀ pm ∈ elems.zip ms, TVal A v σ pm.1 pm.2) →
      SetRestVal σ rest s₀ →
      TVal A v σ (.aci f elems rest) (A.ev f (.set (↑ms + s₀.val.map v)))

section
variable {G : Graph} {L : Sym → OpLaws} {A : Alg M} {v : C → M}

theorem rtg_ev {α : Type} {r : α → α → Prop} (e : α → M) (he : ∀ a b, r a b → e a = e b)
    {a b : α} (h : Relation.ReflTransGen r a b) : e a = e b := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (he _ _ hbc)

/-- `denN_sound`: the class `add` returns for `t` has `t`'s value. -/
theorem denN_sound (hm : Models G A v) (hl : LawsHold G L A v) {σ : Binding} {t : Pat} {c : C}
    (hd : DenN G L σ t c) : TVal A v σ t (v c) := by
  obtain ⟨hfind, hnode⟩ := hm
  induction hd with
  | var hx => rw [hfind]; exact TVal.var hx
  | plain hl' hall hmem ih =>
      rename_i f args cs id
      rw [hfind, hnode _ _ hmem]
      refine TVal.plain (ms := cs.map v) (by simp [hl']) ?_
      intro pm hpm
      rw [List.zip_map_right, List.mem_map] at hpm
      obtain ⟨pc, hpc, rfl⟩ := hpm
      exact ih pc hpc
  | comm ha hb hmem iha ihb =>
      rename_i f p q a b id
      rw [hfind]
      rcases hmem with hmem | hmem
      · rw [hnode _ _ hmem]; exact TVal.comm iha ihb
      · rw [hnode _ _ hmem]; simp only [Children.val]; rw [hl.comm]; exact TVal.comm iha ihb
  | assoc hl' hall hpre hsuf hsteps hfin ih =>
      rename_i f pre suf args cs u w l' c
      have hstep := rtg_ev (fun l => A.ev f (.seq (l.map v))) (fun a b h => hl.a_step f a b h) hsteps
      have hval : v c = A.ev f (.seq (l'.map v)) := by
        rcases hfin with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u₀, hu, rfl⟩
        · rw [hfind, hnode _ _ hmem]; rfl
        · rw [hfind]; simp [hl.single_seq]
        · rw [hfind]; simp [hl.unit_seq f u₀ hu]
      rw [hval, ← hstep]
      have := TVal.assoc (A := A) (v := v) (f := f) (pre := pre) (suf := suf) (args := args) (ms := cs.map v) (u := u) (w := w)
        (by simp [hl']) (fun pm hpm => by
          rw [List.zip_map_right, List.mem_map] at hpm
          obtain ⟨pc, hpc, rfl⟩ := hpm
          exact ih pc hpc) hpre hsuf
      simpa [List.map_append, List.map_map, Function.comp_def, hfind] using this
  | ac hl' hmult hden hrest hsteps hfin ih =>
      rename_i f elems rest cks m₀ m' c
      have hstep := rtg_ev (fun m => A.ev f (.mset (m.map v))) (fun a b h => hl.ac_step f a b h)
        hsteps
      have hval : v c = A.ev f (.mset (m'.map v)) := by
        rcases hfin with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u₀, hu, rfl⟩
        · rw [hfind, hnode _ _ hmem]; rfl
        · rw [hfind]; simp [hl.single_mset]
        · rw [hfind]; simp [hl.unit_mset f u₀ hu]
      rw [hval, ← hstep]
      have := TVal.ac (A := A) (v := v) (f := f) (elems := elems) (rest := rest) (xks := cks.map fun ck => (v ck.1, ck.2))
        (by simp [hl']) (fun ek hek => by
          rw [List.zip_map_right, List.mem_map] at hek
          obtain ⟨ek', hek', rfl⟩ := hek
          exact hmult ek' hek') (fun ek hek hk => by
          rw [List.zip_map_right, List.mem_map] at hek
          obtain ⟨ek', hek', rfl⟩ := hek
          exact ih ek' hek' hk) hrest
      simpa [Multiset.map_add, Multiset.map_map, Function.comp_def, hfind, acChildren_map_val]
        using this
  | aci hl' hall hrest hsteps hfin ih =>
      rename_i f elems rest cs s₀ s' c
      have hstep := rtg_ev (fun s => A.ev f (.set (s.val.map v))) (fun a b h => hl.aci_step f a b h)
        hsteps
      have hval : v c = A.ev f (.set (s'.val.map v)) := by
        rcases hfin with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u₀, hu, rfl⟩
        · rw [hfind, hnode _ _ hmem]; rfl
        · rw [hfind]; simp [hl.single_set]
        · rw [hfind]; simp [hl.unit_set f u₀ hu]
      rw [hval, ← hstep]
      have := TVal.aci (A := A) (v := v) (f := f) (elems := elems) (rest := rest) (ms := cs.map v) (s₀ := s₀)
        (by simp [hl']) (fun pm hpm => by
          rw [List.zip_map_right, List.mem_map] at hpm
          obtain ⟨pc, hpc, rfl⟩ := hpm
          exact ih pc hpc) hrest
      rw [hl.set_ext f _ ((cs.toFinset ∪ Finset.image G.find s₀).val.map v)] at this
      · exact this
      · intro x
        simp only [Multiset.mem_add, Multiset.mem_map, Multiset.mem_coe, List.mem_map,
          Finset.mem_val, Finset.mem_union, List.mem_toFinset, Finset.mem_image]
        constructor
        · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
          · exact ⟨c, Or.inl hc, rfl⟩
          · exact ⟨G.find c, Or.inr ⟨c, hc, rfl⟩, hfind c⟩
        · rintro ⟨c, hc | ⟨c', hc', rfl⟩, rfl⟩
          · exact Or.inl ⟨c, hc, rfl⟩
          · exact Or.inr ⟨c', hc', (hfind c').symm⟩

/-- A fired union holds in every model of the graph and the laws. -/
theorem firedN_sound (hm : Models G A v) (hl : LawsHold G L A v) {σ : Binding} {rule : Rule}
    (hf : FiredN G L σ rule) {a b : Pat} (hab : Action.union a b ∈ rule.actions) :
    ∃ x, TVal A v σ a x ∧ TVal A v σ b x := by
  obtain ⟨c, ha, hb⟩ := hf _ hab
  exact ⟨v c, denN_sound hm hl ha, denN_sound hm hl hb⟩

/-- The rule's equations hold at `σ` in the model: both sides of every union
have one value whenever both have a value. -/
def RuleHolds (A : Alg M) (v : C → M) (σ : Binding) (rule : Rule) : Prop :=
  ∀ a b, Action.union a b ∈ rule.actions → ∀ x y, TVal A v σ a x → TVal A v σ b y → x = y

/-- `union_recorded_sound`: the two classes a `Union` action of a rule
records, built on the live graph `G` (`DenN`), have equal values in every
model of `G` in which the rule holds at the match. -/
theorem union_recorded_sound (hm : Models G A v) (hl : LawsHold G L A v) {σ : Binding}
    {rule : Rule} (hr : RuleHolds A v σ rule) {a b : Pat} (hab : Action.union a b ∈ rule.actions)
    {c₁ c₂ : C} (ha : DenN G L σ a c₁) (hb : DenN G L σ b c₂) : v c₁ = v c₂ :=
  hr a b hab _ _ (denN_sound hm hl ha) (denN_sound hm hl hb)

/-- Merging classes of equal value keeps the model: `G'` has the nodes of
`G` and a coarser `find` that only identifies classes of equal value. -/
theorem models_of_merge {G' : Graph} (hm : Models G A v) (hn : ∀ p, p ∈ G'.nodes ↔ p ∈ G.nodes)
    (hv : ∀ c, v (G'.find c) = v c) : Models G' A v :=
  ⟨hv, fun id n hmem => hm.2 id n ((hn _).1 hmem)⟩

end

end Semper.EMatch.Fidelity
