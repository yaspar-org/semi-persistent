import SemperProofs.EMatch.Engine.Sched

/-!
# The run of a scheduled plan (spec-scheduler §3.2)

The invariant `Inv` holds at every decision point of a `SchedA` plan: the
bound set is exactly the class domain of the binding and the union of the
binds of the used atoms; the used atoms are satisfied; node, rest and
multiplicity maps are bound only on variables of used atoms.

`RunSpec` is what the remaining plan emits from such a state: extensions of
the binding that satisfy every atom, bind the classes of every atom and
nothing else, and write node/multiplicity/rest variables of the unused
atoms only. `schedA_run` proves `runA` emits exactly `RunSpec`.
-/

namespace Semper.EMatch

open Binding (Extends)

/-- Hypotheses on the graph and the atom list (resolve-time checks and the
engine's index invariants): distinct node ids; nodes of an operator have
the shape of its kind and every atom uses that shape; node variables are
linear across scanning atoms; rest variables are linear and the prefix and
suffix rests of an atom are distinct; every `Eq` variable is bound by some
scanning atom (`check_nodes_bindable`). -/
structure AtomsWF (G : Graph) (sig : Sym → Kind) (atoms : List QAtom) : Prop where
  keys : G.KeysNodup
  conf : G.Conforms sig
  wk : ∀ a, QAtom.scan a ∈ atoms → a.WK sig
  nodesDistinct : ∀ (i j : Nat) (a b : RAtom), atoms[i]? = some (.scan a) → atoms[j]? = some (.scan b) →
    a.node = b.node → i = j
  restLinear : ∀ (i j : Nat) (a b : RAtom), atoms[i]? = some (.scan a) → atoms[j]? = some (.scan b) → i ≠ j →
    ∀ r, r ∈ a.restVars → r ∉ b.restVars
  seqNodup : ∀ a, QAtom.scan a ∈ atoms → a.seqRestVars.Nodup
  bindable : ∀ (i : Nat) (x y : Var), atoms[i]? = some (.eq x y) →
    (∃ (j : Nat) (a : RAtom), atoms[j]? = some (.scan a) ∧ x ∈ a.binds) ∧ (∃ (j : Nat) (a : RAtom), atoms[j]? = some (.scan a) ∧ y ∈ a.binds)

/-- The run invariant at a decision point. -/
structure Inv (G : Graph) (isNew : NodeId → Bool) (atoms : List QAtom) (mode : Nat → IndexMode)
    (pre : Finset Var) (used : Finset Nat) (B : Finset Var) (σ : Binding) : Prop where
  clsDom : ClsDom σ B
  bound : ∀ (x : Var), x ∈ B ↔
    x ∈ pre ∨ ∃ (i : Nat) (q : QAtom), atoms[i]? = some q ∧ i ∈ used ∧ x ∈ q.binds
  node : ∀ (v : Var) (id : NodeId), σ.node v = some id → ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∈ used ∧ a.node = v
  sat : ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → i ∈ used → QSat G σ q
  mode : ∀ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) → i ∈ used →
    ∃ id, σ.node a.node = some id ∧ modeOk isNew (mode i) id = true
  rest : ∀ (r : Var) (m), σ.rest r = some m → ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∈ used ∧ r ∈ a.msetRestVars
  seqRest : ∀ (r : Var) (u), σ.seqRest r = some u →
    ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∈ used ∧ r ∈ a.seqRestVars
  finRest : ∀ (r : Var) (s), σ.finRest r = some s →
    ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∈ used ∧ r ∈ a.setRestVars

/-- What the rest of the plan emits from a state `(used, B, σ)`. -/
structure RunSpec (G : Graph) (isNew : NodeId → Bool) (atoms : List QAtom) (mode : Nat → IndexMode)
    (used : Finset Nat) (B : Finset Var) (σ σ' : Binding) : Prop where
  ext : Extends σ σ'
  sat : ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → QSat G σ' q
  mode : ∀ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) →
    ∃ id, σ'.node a.node = some id ∧ modeOk isNew (mode i) id = true
  clsDom : ∀ (x : Var), (∃ c, σ'.cls x = some c) ↔ x ∈ B ∨ ∃ (i : Nat) (q : QAtom), atoms[i]? = some q ∧ i ∉ used ∧ x ∈ q.binds
  node : ∀ (v : Var) (id : NodeId), σ'.node v = some id →
    (∃ id', σ.node v = some id') ∨ ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∉ used ∧ a.node = v
  mult : ∀ (k : Var) (m), σ'.mult k = some m →
    (∃ m', σ.mult k = some m') ∨ ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∉ used ∧ k ∈ a.multVars
  rest : ∀ (r : Var) (m), σ'.rest r = some m →
    (∃ m', σ.rest r = some m') ∨ ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∉ used ∧ r ∈ a.msetRestVars
  seqRest : ∀ (r : Var) (u), σ'.seqRest r = some u →
    (∃ u', σ.seqRest r = some u') ∨ ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∉ used ∧ r ∈ a.seqRestVars
  finRest : ∀ (r : Var) (s), σ'.finRest r = some s →
    (∃ s', σ.finRest r = some s') ∨ ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∉ used ∧ r ∈ a.setRestVars

/-! ## Monotonicity of satisfaction -/

theorem AtomSat.mono {G : Graph} {σ σ' : Binding} {a : RAtom} (h : AtomSat G σ a)
    (hext : Extends σ σ') : AtomSat G σ' a := by
  obtain ⟨id, nd, hn, hmem, hc, hop, hm⟩ := h
  exact ⟨id, nd, hext.2.1 _ _ hn, hmem, hext.1 _ _ hc, hop, hm.mono hext⟩

theorem QSat.mono {G : Graph} {σ σ' : Binding} {q : QAtom} (h : QSat G σ q)
    (hext : Extends σ σ') : QSat G σ' q := by
  cases q with
  | scan a => exact AtomSat.mono h hext
  | eq x y =>
      obtain ⟨c, hx, hy⟩ := h
      exact ⟨c, hext.1 _ _ hx, hext.1 _ _ hy⟩

theorem eagerFree_eq {q : QAtom} {B : Finset Var} (h : q.eagerFree B) : ∃ x y, q = .eq x y := by
  cases q with
  | scan a => simp [QAtom.eagerFree] at h
  | eq x y => exact ⟨x, y, rfl⟩

theorem mem_of_getElem? {atoms : List QAtom} {i : Nat} {q : QAtom} (h : atoms[i]? = some q) :
    q ∈ atoms := List.mem_of_getElem? h

/-! ## Preservation of the invariant -/

theorem Inv.step_eager {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {pre : Finset Var} {used : Finset Nat} {B : Finset Var} {σ σ₁ : Binding} {i : Nat}
    {q : QAtom} (hinv : Inv G isNew atoms mode pre used B σ) (hq : atoms[i]? = some q)
    (hf : q.eagerFree B) (hs : EagerSpec G q B σ σ₁) :
    Inv G isNew atoms mode pre (insert i used) (B ∪ q.binds) σ₁ where
  clsDom := hs.clsDom
  bound x := by
    rw [Finset.mem_union, hinv.bound x]
    constructor
    · rintro ((hp | ⟨j, q', hj, hju, hx⟩) | hx)
      · exact Or.inl hp
      · exact Or.inr ⟨j, q', hj, Finset.mem_insert_of_mem hju, hx⟩
      · exact Or.inr ⟨i, q, hq, Finset.mem_insert_self _ _, hx⟩
    · rintro (hp | ⟨j, q', hj, hju, hx⟩)
      · exact Or.inl (Or.inl hp)
      rw [Finset.mem_insert] at hju
      rcases hju with rfl | hju
      · rw [hq] at hj
        cases Option.some.inj hj
        exact Or.inr hx
      · exact Or.inl (Or.inr ⟨j, q', hj, hju, hx⟩)
  node v id hv := by
    rw [hs.node] at hv
    obtain ⟨j, a, hj, hju, ha⟩ := hinv.node v id hv
    exact ⟨j, a, hj, Finset.mem_insert_of_mem hju, ha⟩
  sat j q' hj hju := by
    rw [Finset.mem_insert] at hju
    rcases hju with rfl | hju
    · rw [hq] at hj
      cases Option.some.inj hj
      exact hs.sat
    · exact (hinv.sat j q' hj hju).mono hs.ext
  mode j a hj hju := by
    rw [Finset.mem_insert] at hju
    rcases hju with rfl | hju
    · obtain ⟨x, y, rfl⟩ := eagerFree_eq hf
      rw [hq] at hj
      cases hj
    · obtain ⟨id, hid, hm⟩ := hinv.mode j a hj hju
      exact ⟨id, by rw [hs.node]; exact hid, hm⟩
  rest r m hr := by
    rw [hs.rest] at hr
    obtain ⟨j, a, hj, hju, ha⟩ := hinv.rest r m hr
    exact ⟨j, a, hj, Finset.mem_insert_of_mem hju, ha⟩
  seqRest r u hr := by
    rw [hs.seqRest] at hr
    obtain ⟨j, a, hj, hju, ha⟩ := hinv.seqRest r u hr
    exact ⟨j, a, hj, Finset.mem_insert_of_mem hju, ha⟩
  finRest r s hr := by
    rw [hs.finRest] at hr
    obtain ⟨j, a, hj, hju, ha⟩ := hinv.finRest r s hr
    exact ⟨j, a, hj, Finset.mem_insert_of_mem hju, ha⟩

theorem Inv.step_pick {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {pre : Finset Var} {used : Finset Nat} {B : Finset Var} {σ σ₁ : Binding} {i : Nat}
    {a : RAtom} (hinv : Inv G isNew atoms mode pre used B σ) (ha : atoms[i]? = some (.scan a))
    (hs : LowerSpec G a B σ σ₁) {id : NodeId} (hid : σ₁.node a.node = some id)
    (hm : modeOk isNew (mode i) id = true) :
    Inv G isNew atoms mode pre (insert i used) (B ∪ a.binds) σ₁ where
  clsDom := hs.clsDom
  bound x := by
    rw [Finset.mem_union, hinv.bound x]
    constructor
    · rintro ((hp | ⟨j, q', hj, hju, hx⟩) | hx)
      · exact Or.inl hp
      · exact Or.inr ⟨j, q', hj, Finset.mem_insert_of_mem hju, hx⟩
      · exact Or.inr ⟨i, .scan a, ha, Finset.mem_insert_self _ _, hx⟩
    · rintro (hp | ⟨j, q', hj, hju, hx⟩)
      · exact Or.inl (Or.inl hp)
      rw [Finset.mem_insert] at hju
      rcases hju with rfl | hju
      · rw [ha] at hj
        cases Option.some.inj hj
        exact Or.inr hx
      · exact Or.inl (Or.inr ⟨j, q', hj, hju, hx⟩)
  node v id' hv := by
    by_cases hva : v = a.node
    · exact ⟨i, a, ha, Finset.mem_insert_self _ _, hva.symm⟩
    · rw [hs.node v hva] at hv
      obtain ⟨j, b, hj, hju, hb⟩ := hinv.node v id' hv
      exact ⟨j, b, hj, Finset.mem_insert_of_mem hju, hb⟩
  sat j q' hj hju := by
    rw [Finset.mem_insert] at hju
    rcases hju with rfl | hju
    · rw [ha] at hj
      cases Option.some.inj hj
      exact hs.sat
    · exact (hinv.sat j q' hj hju).mono hs.ext
  mode j b hj hju := by
    rw [Finset.mem_insert] at hju
    rcases hju with rfl | hju
    · rw [ha] at hj
      cases Option.some.inj hj
      exact ⟨id, hid, hm⟩
    · obtain ⟨id', hid', hm'⟩ := hinv.mode j b hj hju
      exact ⟨id', hs.ext.2.1 _ _ hid', hm'⟩
  rest r m hr := by
    by_cases hra : r ∈ a.msetRestVars
    · exact ⟨i, a, ha, Finset.mem_insert_self _ _, hra⟩
    · rw [hs.rest r hra] at hr
      obtain ⟨j, b, hj, hju, hb⟩ := hinv.rest r m hr
      exact ⟨j, b, hj, Finset.mem_insert_of_mem hju, hb⟩
  seqRest r u hr := by
    by_cases hra : r ∈ a.seqRestVars
    · exact ⟨i, a, ha, Finset.mem_insert_self _ _, hra⟩
    · rw [hs.seqRest r hra] at hr
      obtain ⟨j, b, hj, hju, hb⟩ := hinv.seqRest r u hr
      exact ⟨j, b, hj, Finset.mem_insert_of_mem hju, hb⟩
  finRest r s hr := by
    by_cases hra : r ∈ a.setRestVars
    · exact ⟨i, a, ha, Finset.mem_insert_self _ _, hra⟩
    · rw [hs.finRest r hra] at hr
      obtain ⟨j, b, hj, hju, hb⟩ := hinv.finRest r s hr
      exact ⟨j, b, hj, Finset.mem_insert_of_mem hju, hb⟩

/-- The side conditions of `lower_sound` at a `pick`, from the invariant. -/
theorem Inv.pick_conditions {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {atoms : List QAtom} {mode : Nat → IndexMode} {pre : Finset Var} {used : Finset Nat} {B : Finset Var}
    {σ : Binding} {i : Nat} {a : RAtom} (hwf : AtomsWF G sig atoms) (hinv : Inv G isNew atoms mode pre used B σ)
    (ha : atoms[i]? = some (.scan a)) (hu : i ∉ used) :
    σ.node a.node = none ∧ a.RestFresh σ := by
  constructor
  · rcases h : σ.node a.node with _ | id
    · rfl
    · obtain ⟨j, b, hj, hju, hb⟩ := hinv.node _ _ h
      have := hwf.nodesDistinct j i b a hj ha hb
      subst this
      exact absurd hju hu
  · have hlin : ∀ j b, atoms[j]? = some (.scan b) → j ∈ used → ∀ r, r ∈ a.restVars → r ∉ b.restVars := by
      intro j b hj hju r hr
      exact hwf.restLinear i j a b ha hj (fun h => hu (h ▸ hju)) r hr
    refine ⟨?_, ?_, ?_, hwf.seqNodup a (mem_of_getElem? ha)⟩
    · intro r hr
      rcases h : σ.seqRest r with _ | u
      · rfl
      · obtain ⟨j, b, hj, hju, hb⟩ := hinv.seqRest _ _ h
        exact absurd (by simp [RAtom.restVars, hb]) (hlin j b hj hju r (by simp [RAtom.restVars, hr]))
    · intro r hr
      rcases h : σ.rest r with _ | m
      · rfl
      · obtain ⟨j, b, hj, hju, hb⟩ := hinv.rest _ _ h
        exact absurd (by simp [RAtom.restVars, hb]) (hlin j b hj hju r (by simp [RAtom.restVars, hr]))
    · intro r hr
      rcases h : σ.finRest r with _ | s
      · rfl
      · obtain ⟨j, b, hj, hju, hb⟩ := hinv.finRest _ _ h
        exact absurd (by simp [RAtom.restVars, hb]) (hlin j b hj hju r (by simp [RAtom.restVars, hr]))

/-! ## Transfer of the run specification across one step -/

/-- Forward: from the specification after the step to the one before. -/
theorem RunSpec.of_next {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {used : Finset Nat} {B : Finset Var} {σ σ₁ σ' : Binding} {i : Nat}
    {q : QAtom} (hq : atoms[i]? = some q) (hu : i ∉ used)
    (hext : Extends σ σ₁)
    (hnode : ∀ (v : Var) (id : NodeId), σ₁.node v = some id → (∃ id', σ.node v = some id') ∨ (∃ a, q = .scan a ∧ a.node = v))
    (hmult : ∀ (k : Var) (m), σ₁.mult k = some m → (∃ m', σ.mult k = some m') ∨ (∃ a, q = .scan a ∧ k ∈ a.multVars))
    (hrest : ∀ (r : Var) (m), σ₁.rest r = some m → (∃ m', σ.rest r = some m') ∨ (∃ a, q = .scan a ∧ r ∈ a.msetRestVars))
    (hseq : ∀ (r : Var) (u), σ₁.seqRest r = some u → (∃ u', σ.seqRest r = some u') ∨ (∃ a, q = .scan a ∧ r ∈ a.seqRestVars))
    (hfin : ∀ (r : Var) (s), σ₁.finRest r = some s → (∃ s', σ.finRest r = some s') ∨ (∃ a, q = .scan a ∧ r ∈ a.setRestVars))
    (h : RunSpec G isNew atoms mode (insert i used) (B ∪ q.binds) σ₁ σ') :
    RunSpec G isNew atoms mode used B σ σ' where
  ext := hext.trans h.ext
  sat := h.sat
  mode := h.mode
  clsDom x := by
    rw [h.clsDom x, Finset.mem_union]
    constructor
    · rintro ((hx | hx) | ⟨j, q', hj, hju, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨i, q, hq, hu, hx⟩
      · exact Or.inr ⟨j, q', hj, fun h => hju (Finset.mem_insert_of_mem h), hx⟩
    · rintro (hx | ⟨j, q', hj, hju, hx⟩)
      · exact Or.inl (Or.inl hx)
      · by_cases hji : j = i
        · subst hji
          rw [hq] at hj
          cases Option.some.inj hj
          exact Or.inl (Or.inr hx)
        · exact Or.inr ⟨j, q', hj, by simp [hji, hju], hx⟩
  node v id hv := by
    rcases h.node v id hv with ⟨id', hid'⟩ | ⟨j, a, hj, hju, ha⟩
    · rcases hnode v id' hid' with h' | ⟨a, rfl, ha⟩
      · exact Or.inl h'
      · exact Or.inr ⟨i, a, hq, hu, ha⟩
    · exact Or.inr ⟨j, a, hj, fun h => hju (Finset.mem_insert_of_mem h), ha⟩
  mult k m hm := by
    rcases h.mult k m hm with ⟨m', hm'⟩ | ⟨j, a, hj, hju, ha⟩
    · rcases hmult k m' hm' with h' | ⟨a, rfl, ha⟩
      · exact Or.inl h'
      · exact Or.inr ⟨i, a, hq, hu, ha⟩
    · exact Or.inr ⟨j, a, hj, fun h => hju (Finset.mem_insert_of_mem h), ha⟩
  rest r m hm := by
    rcases h.rest r m hm with ⟨m', hm'⟩ | ⟨j, a, hj, hju, ha⟩
    · rcases hrest r m' hm' with h' | ⟨a, rfl, ha⟩
      · exact Or.inl h'
      · exact Or.inr ⟨i, a, hq, hu, ha⟩
    · exact Or.inr ⟨j, a, hj, fun h => hju (Finset.mem_insert_of_mem h), ha⟩
  seqRest r u hu' := by
    rcases h.seqRest r u hu' with ⟨u', hu''⟩ | ⟨j, a, hj, hju, ha⟩
    · rcases hseq r u' hu'' with h' | ⟨a, rfl, ha⟩
      · exact Or.inl h'
      · exact Or.inr ⟨i, a, hq, hu, ha⟩
    · exact Or.inr ⟨j, a, hj, fun h => hju (Finset.mem_insert_of_mem h), ha⟩
  finRest r s hs := by
    rcases h.finRest r s hs with ⟨s', hs'⟩ | ⟨j, a, hj, hju, ha⟩
    · rcases hfin r s' hs' with h' | ⟨a, rfl, ha⟩
      · exact Or.inl h'
      · exact Or.inr ⟨i, a, hq, hu, ha⟩
    · exact Or.inr ⟨j, a, hj, fun h => hju (Finset.mem_insert_of_mem h), ha⟩

/-- Backward: from the specification before the step to the one after,
given the intermediate binding lies between. -/
theorem RunSpec.to_next {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {used : Finset Nat} {B : Finset Var} {σ σ₁ σ' : Binding} {i : Nat}
    {q : QAtom} (hq : atoms[i]? = some q)
    (hext : Extends σ σ₁) (hext₁ : Extends σ₁ σ')
    (hdom₁ : ClsDom σ₁ (B ∪ q.binds))
    (hnode : ∀ a, q = .scan a → ∃ id, σ₁.node a.node = some id)
    (hmult : ∀ a, q = .scan a → ∀ k ∈ a.multVars, ∃ m, σ₁.mult k = some m)
    (hrest : ∀ a, q = .scan a → ∀ r ∈ a.msetRestVars, ∃ m, σ₁.rest r = some m)
    (hseq : ∀ a, q = .scan a → ∀ r ∈ a.seqRestVars, ∃ u, σ₁.seqRest r = some u)
    (hfin : ∀ a, q = .scan a → ∀ r ∈ a.setRestVars, ∃ s, σ₁.finRest r = some s)
    (h : RunSpec G isNew atoms mode used B σ σ') :
    RunSpec G isNew atoms mode (insert i used) (B ∪ q.binds) σ₁ σ' where
  ext := hext₁
  sat := h.sat
  mode := h.mode
  clsDom x := by
    rw [h.clsDom x]
    constructor
    · rintro (hx | ⟨j, q', hj, hju, hx⟩)
      · exact Or.inl (Finset.mem_union_left _ hx)
      · by_cases hji : j = i
        · subst hji
          rw [hq] at hj
          cases Option.some.inj hj
          exact Or.inl (Finset.mem_union_right _ hx)
        · exact Or.inr ⟨j, q', hj, by simp [hji, hju], hx⟩
    · rintro (hx | ⟨j, q', hj, hju, hx⟩)
      · rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact Or.inl hx
        · obtain ⟨c, hc⟩ := (hdom₁ x).1 (Finset.mem_union_right _ hx)
          have := hext₁.1 _ _ hc
          exact (h.clsDom x).1 ⟨c, this⟩
      · exact Or.inr ⟨j, q', hj, fun h' => hju (Finset.mem_insert_of_mem h'), hx⟩
  node v id hv := by
    rcases h.node v id hv with ⟨id', hid'⟩ | ⟨j, a, hj, hju, ha⟩
    · exact Or.inl ⟨id', hext.2.1 _ _ hid'⟩
    · by_cases hji : j = i
      · subst hji
        rw [hq] at hj
        cases Option.some.inj hj
        exact Or.inl (ha ▸ hnode a rfl)
      · exact Or.inr ⟨j, a, hj, by simp [hji, hju], ha⟩
  mult k m hm := by
    rcases h.mult k m hm with ⟨m', hm'⟩ | ⟨j, a, hj, hju, ha⟩
    · exact Or.inl ⟨m', hext.2.2.1 _ _ hm'⟩
    · by_cases hji : j = i
      · subst hji
        rw [hq] at hj
        cases Option.some.inj hj
        exact Or.inl (hmult a rfl k ha)
      · exact Or.inr ⟨j, a, hj, by simp [hji, hju], ha⟩
  rest r m hm := by
    rcases h.rest r m hm with ⟨m', hm'⟩ | ⟨j, a, hj, hju, ha⟩
    · exact Or.inl ⟨m', hext.2.2.2.1 _ _ hm'⟩
    · by_cases hji : j = i
      · subst hji
        rw [hq] at hj
        cases Option.some.inj hj
        exact Or.inl (hrest a rfl r ha)
      · exact Or.inr ⟨j, a, hj, by simp [hji, hju], ha⟩
  seqRest r u hu := by
    rcases h.seqRest r u hu with ⟨u', hu'⟩ | ⟨j, a, hj, hju, ha⟩
    · exact Or.inl ⟨u', hext.2.2.2.2.1 _ _ hu'⟩
    · by_cases hji : j = i
      · subst hji
        rw [hq] at hj
        cases Option.some.inj hj
        exact Or.inl (hseq a rfl r ha)
      · exact Or.inr ⟨j, a, hj, by simp [hji, hju], ha⟩
  finRest r s hs := by
    rcases h.finRest r s hs with ⟨s', hs'⟩ | ⟨j, a, hj, hju, ha⟩
    · exact Or.inl ⟨s', hext.2.2.2.2.2 _ _ hs'⟩
    · by_cases hji : j = i
      · subst hji
        rw [hq] at hj
        cases Option.some.inj hj
        exact Or.inl (hfin a rfl r ha)
      · exact Or.inr ⟨j, a, hj, by simp [hji, hju], ha⟩

/-! ## The terminal state -/

/-- At `done`, with bindable `Eq` atoms, every atom is used. -/
theorem all_used {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {pre : Finset Var} {used : Finset Nat} {B : Finset Var} {σ : Binding}
    (hwf : AtomsWF G sig atoms) (hinv : Inv G isNew atoms mode pre used B σ)
    (h₁ : ∀ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) → i ∈ used)
    (h₂ : ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → i ∉ used → ¬ q.eagerFree B) :
    ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → i ∈ used := by
  intro i q hq
  by_contra hu
  cases q with
  | scan a => exact hu (h₁ i a hq)
  | eq x y =>
      obtain ⟨⟨j, a, hj, hx⟩, -⟩ := hwf.bindable i x y hq
      have hxB : x ∈ B := (hinv.bound x).2 (Or.inr ⟨j, .scan a, hj, h₁ j a hj, hx⟩)
      exact h₂ i _ hq hu (Or.inl hxB)

theorem runSpec_done {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {pre : Finset Var} {used : Finset Nat} {B : Finset Var} {σ σ' : Binding}
    (hwf : AtomsWF G sig atoms) (hinv : Inv G isNew atoms mode pre used B σ)
    (h₁ : ∀ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) → i ∈ used)
    (h₂ : ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → i ∉ used → ¬ q.eagerFree B) :
    σ' = σ ↔ RunSpec G isNew atoms mode used B σ σ' := by
  have hall := all_used hwf hinv h₁ h₂
  constructor
  · rintro rfl
    exact {
      ext := Extends.refl _
      sat := fun i q hq => hinv.sat i q hq (hall i q hq)
      mode := fun i a ha => hinv.mode i a ha (h₁ i a ha)
      clsDom := fun x => by
        rw [← hinv.clsDom x]
        constructor
        · exact Or.inl
        · rintro (hx | ⟨j, q, hj, hju, -⟩)
          · exact hx
          · exact absurd (hall j q hj) hju
      node := fun v id hv => Or.inl ⟨id, hv⟩
      mult := fun k m hm => Or.inl ⟨m, hm⟩
      rest := fun r m hm => Or.inl ⟨m, hm⟩
      seqRest := fun r u hu => Or.inl ⟨u, hu⟩
      finRest := fun r s hs => Or.inl ⟨s, hs⟩ }
  · intro h
    have hnone : ∀ j q, atoms[j]? = some q → j ∉ used → False := fun j q hj hju => hju (hall j q hj)
    refine Binding.ext' ?_ ?_ ?_ ?_ ?_ ?_
    · intro x
      rcases hx : σ.cls x with _ | c
      · rcases hx' : σ'.cls x with _ | c'
        · rfl
        · rcases (h.clsDom x).1 ⟨c', hx'⟩ with hB | ⟨j, q, hj, hju, -⟩
          · obtain ⟨c, hc⟩ := (hinv.clsDom x).1 hB
            rw [hc] at hx; cases hx
          · exact absurd hju (fun h' => hnone j q hj h')
      · exact (h.ext.1 x c hx)
    · intro v
      rcases hv : σ.node v with _ | id
      · rcases hv' : σ'.node v with _ | id'
        · rfl
        · rcases h.node v id' hv' with ⟨id'', h''⟩ | ⟨j, a, hj, hju, -⟩
          · rw [hv] at h''; cases h''
          · exact absurd hju (fun h' => hnone j _ hj h')
      · exact (h.ext.2.1 v id hv)
    · intro k
      rcases hk : σ.mult k with _ | m
      · rcases hk' : σ'.mult k with _ | m'
        · rfl
        · rcases h.mult k m' hk' with ⟨m'', h''⟩ | ⟨j, a, hj, hju, -⟩
          · rw [hk] at h''; cases h''
          · exact absurd hju (fun h' => hnone j _ hj h')
      · exact (h.ext.2.2.1 k m hk)
    · intro r
      rcases hr : σ.rest r with _ | m
      · rcases hr' : σ'.rest r with _ | m'
        · rfl
        · rcases h.rest r m' hr' with ⟨m'', h''⟩ | ⟨j, a, hj, hju, -⟩
          · rw [hr] at h''; cases h''
          · exact absurd hju (fun h' => hnone j _ hj h')
      · exact (h.ext.2.2.2.1 r m hr)
    · intro r
      rcases hr : σ.seqRest r with _ | u
      · rcases hr' : σ'.seqRest r with _ | u'
        · rfl
        · rcases h.seqRest r u' hr' with ⟨u'', h''⟩ | ⟨j, a, hj, hju, -⟩
          · rw [hr] at h''; cases h''
          · exact absurd hju (fun h' => hnone j _ hj h')
      · exact (h.ext.2.2.2.2.1 r u hr)
    · intro r
      rcases hr : σ.finRest r with _ | s
      · rcases hr' : σ'.finRest r with _ | s'
        · rfl
        · rcases h.finRest r s' hr' with ⟨s'', h''⟩ | ⟨j, a, hj, hju, -⟩
          · rw [hr] at h''; cases h''
          · exact absurd hju (fun h' => hnone j _ hj h')
      · exact (h.ext.2.2.2.2.2 r s hr)

/-! ## One scheduling step, for any continuation -/

/-- An eager step followed by a continuation that is characterised by
`RunSpec` from every state satisfying the invariant. -/
theorem step_eager_iff {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {pre : Finset Var} {used : Finset Nat} {B : Finset Var} {σ : Binding}
    {i : Nat} {q : QAtom} (_hwf : AtomsWF G sig atoms) (hinv : Inv G isNew atoms mode pre used B σ)
    (hq : atoms[i]? = some q) (hu : i ∉ used) (hf : q.eagerFree B)
    (cont : Binding → List Binding)
    (ih : ∀ σ₁, Inv G isNew atoms mode pre (insert i used) (B ∪ q.binds) σ₁ →
      ∀ σ', σ' ∈ cont σ₁ ↔ RunSpec G isNew atoms mode (insert i used) (B ∪ q.binds) σ₁ σ') :
    ∀ σ', σ' ∈ (run G (q.eagerLower B) σ).flatMap cont ↔ RunSpec G isNew atoms mode used B σ σ' := by
  intro σ'
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨σ₁, h₁, h⟩
    have hs := eager_sound hinv.clsDom hf h₁
    have hinv₁ := hinv.step_eager hq hf hs
    have hspec := (ih σ₁ hinv₁ σ').1 h
    obtain ⟨x, y, rfl⟩ := eagerFree_eq hf
    refine RunSpec.of_next hq hu hs.ext ?_ ?_ ?_ ?_ ?_ hspec
    · intro v id hv; rw [hs.node] at hv; exact Or.inl ⟨id, hv⟩
    · intro k m hm; rw [hs.mult] at hm; exact Or.inl ⟨m, hm⟩
    · intro r m hm; rw [hs.rest] at hm; exact Or.inl ⟨m, hm⟩
    · intro r u hu'; rw [hs.seqRest] at hu'; exact Or.inl ⟨u, hu'⟩
    · intro r s hs'; rw [hs.finRest] at hs'; exact Or.inl ⟨s, hs'⟩
  · intro hspec
    obtain ⟨σ₁, h₁, hext₁⟩ := eager_complete hinv.clsDom hf hspec.ext (hspec.sat i q hq)
    have hs := eager_sound hinv.clsDom hf h₁
    have hinv₁ := hinv.step_eager hq hf hs
    refine ⟨σ₁, h₁, (ih σ₁ hinv₁ σ').2 ?_⟩
    obtain ⟨x, y, rfl⟩ := eagerFree_eq hf
    exact RunSpec.to_next hq hs.ext hext₁ hs.clsDom (fun a h => by cases h) (fun a h => by cases h)
      (fun a h => by cases h) (fun a h => by cases h) (fun a h => by cases h) hspec

/-- A pick step: the lowering, filtered by the mode of the atom, followed
by a continuation characterised by `RunSpec`. -/
theorem step_pick_iff {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {pre : Finset Var} {used : Finset Nat} {B : Finset Var} {σ : Binding}
    {i : Nat} {a : RAtom} (hwf : AtomsWF G sig atoms) (hinv : Inv G isNew atoms mode pre used B σ)
    (ha : atoms[i]? = some (.scan a)) (hu : i ∉ used)
    (L : List Binding)
    (hL : ∀ σ₁, σ₁ ∈ L ↔ σ₁ ∈ run G (lower a B) σ ∧
      ∃ id, σ₁.node a.node = some id ∧ modeOk isNew (mode i) id = true)
    (cont : Binding → List Binding)
    (ih : ∀ σ₁, Inv G isNew atoms mode pre (insert i used) (B ∪ a.binds) σ₁ →
      ∀ σ', σ' ∈ cont σ₁ ↔ RunSpec G isNew atoms mode (insert i used) (B ∪ a.binds) σ₁ σ') :
    ∀ σ', σ' ∈ L.flatMap cont ↔ RunSpec G isNew atoms mode used B σ σ' := by
  intro σ'
  rw [List.mem_flatMap]
  simp only [hL]
  obtain ⟨hn, hrf⟩ := hinv.pick_conditions hwf ha hu
  have hwk := hwf.wk a (mem_of_getElem? ha)
  constructor
  · rintro ⟨σ₁, ⟨h₁, id, hid, hm⟩, h⟩
    have hs := lower_sound hwf.keys hwf.conf hwk hinv.clsDom hn hrf h₁
    have hinv₁ := hinv.step_pick ha hs hid hm
    have hspec := (ih σ₁ hinv₁ σ').1 h
    refine RunSpec.of_next ha hu hs.ext ?_ ?_ ?_ ?_ ?_ hspec
    · intro v id hv
      by_cases hva : v = a.node
      · exact Or.inr ⟨a, rfl, hva.symm⟩
      · rw [hs.node v hva] at hv; exact Or.inl ⟨id, hv⟩
    · intro k m hm
      by_cases hka : k ∈ a.multVars
      · exact Or.inr ⟨a, rfl, hka⟩
      · rw [hs.mult k hka] at hm; exact Or.inl ⟨m, hm⟩
    · intro r m hm
      by_cases hra : r ∈ a.msetRestVars
      · exact Or.inr ⟨a, rfl, hra⟩
      · rw [hs.rest r hra] at hm; exact Or.inl ⟨m, hm⟩
    · intro r u hu'
      by_cases hra : r ∈ a.seqRestVars
      · exact Or.inr ⟨a, rfl, hra⟩
      · rw [hs.seqRest r hra] at hu'; exact Or.inl ⟨u, hu'⟩
    · intro r s hs'
      by_cases hra : r ∈ a.setRestVars
      · exact Or.inr ⟨a, rfl, hra⟩
      · rw [hs.finRest r hra] at hs'; exact Or.inl ⟨s, hs'⟩
  · intro hspec
    obtain ⟨σ₁, h₁, hext₁⟩ := lower_complete hwf.keys hinv.clsDom hspec.ext (hspec.sat i _ ha)
    have hs := lower_sound hwf.keys hwf.conf hwk hinv.clsDom hn hrf h₁
    obtain ⟨id, hid', hm⟩ := hspec.mode i a ha
    obtain ⟨id₁, -, hid₁, -⟩ := hs.sat
    have hid : σ₁.node a.node = some id := by
      have := hext₁.2.1 _ _ hid₁
      rw [hid'] at this
      rw [hid₁, Option.some.inj this]
    have hinv₁ := hinv.step_pick ha hs hid hm
    refine ⟨σ₁, ⟨h₁, id, hid, hm⟩, (ih σ₁ hinv₁ σ').2 ?_⟩
    refine RunSpec.to_next ha hs.ext hext₁ hs.clsDom ?_ ?_ ?_ ?_ ?_ hspec
    · rintro b hb; cases hb; exact ⟨id, hid⟩
    · rintro b hb; cases hb; exact hs.sat.multVars_bound
    · rintro b hb; cases hb; exact hs.sat.msetRest_bound
    · rintro b hb; cases hb; exact hs.sat.seqRest_bound
    · rintro b hb; cases hb; exact hs.sat.setRest_bound

/-! ## The main theorem -/

theorem schedA_run {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {pre : Finset Var} (hwf : AtomsWF G sig atoms) :
    ∀ {used : Finset Nat} {B : Finset Var} {ap : APlan}, SchedA atoms used B ap →
    ∀ σ, Inv G isNew atoms mode pre used B σ →
    ∀ σ', σ' ∈ runA G isNew mode ap σ ↔ RunSpec G isNew atoms mode used B σ σ' := by
  intro used B ap h
  induction h with
  | done h₁ h₂ =>
      intro σ hinv σ'
      simp only [runA, List.mem_singleton]
      exact runSpec_done hwf hinv h₁ h₂
  | @eager used B i q rest hq hu hf _ ih =>
      intro σ hinv σ'
      rw [runA_append, runA_eager]
      exact step_eager_iff hwf hinv hq hu hf _ ih σ'
  | @pick used B i a rest ha hu _ ih =>
      intro σ hinv σ'
      rw [runA_append]
      exact step_pick_iff hwf hinv ha hu _ (fun σ₁ => mem_runA_lower) _ ih σ'

end Semper.EMatch
