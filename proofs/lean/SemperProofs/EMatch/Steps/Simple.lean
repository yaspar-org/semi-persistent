import SemperProofs.EMatch.Steps.Interp
import SemperProofs.EMatch.Main

/-!
# The simple steps (A.1 to A.7): atoms, lowering, soundness and completeness

Each simple step implements one declarative atom (`Atom.Holds`): `Eq` has
three lowerings (`CheckEq`, `CopyBinding` either way), `EqGlobal` two
(`CheckEqGlobal`, `BindGlobal`), the others one. `lower` is the table
(check vs bind mode by boundness); `*_sound`/`*_complete` characterise each
step's output, and `lower_sound`/`lower_complete` sum them up.
-/

namespace Semper.EMatch.Steps

open Semper.EMatch

/-- The atoms the simple steps implement (`RAtom`). -/
inductive Atom where
  | eq (x y : Var)
  | neq (x y : Var)
  | eqGlobal (x : Var) (g : GVar)
  | lit (v : Var) (c : LVal)
  | litBind (v : Var) (l : Var)
  | pred (p : PredExpr)

/-- The declarative constraint of an atom (spec A.1 to A.7). -/
def Atom.Holds (X : XGraph) (Γ : GVar → C) (M : PredModel) : Atom → XBinding → Prop
  | .eq x y, σ => ∃ c, σ.base.cls x = some c ∧ σ.base.cls y = some c
  | .neq x y, σ => ∃ a b, σ.base.cls x = some a ∧ σ.base.cls y = some b ∧ a ≠ b
  | .eqGlobal x g, σ => σ.base.cls x = some (Γ g)
  | .lit v c, σ => ∃ id, σ.base.node v = some id ∧ (X.litOf id).map X.litVal = some c
  | .litBind v l, σ => ∃ id x, σ.base.node v = some id ∧ X.litOf id = some x ∧ σ.lit l = some x
  | .pred p, σ => ∃ v, evalPred X M σ p = some v ∧ M.truthy v = true

/-- The lowering table (`schedule.rs:1418-1485`, `1119-1128`): check mode
when the read variables are bound, bind mode when exactly the target is
unbound, no eager lowering otherwise (a join, out of scope). -/
def lower (B Bl : List Var) : Atom → Option XStep
  | .eq x y =>
      if x ∈ B then
        (if y ∈ B then some (.core (.checkEq x y)) else some (.copyBinding y x))
      else if y ∈ B then some (.copyBinding x y) else none
  | .neq x y => if x ∈ B ∧ y ∈ B then some (.checkNeq x y) else none
  | .eqGlobal x g => if x ∈ B then some (.checkEqGlobal x g) else some (.bindGlobal x g)
  | .lit v c => if v ∈ B then some (.checkLit v c) else none
  | .litBind v l => if v ∈ B then some (.extractLitVal v l) else none
  | .pred p => if ∀ l ∈ p.litVars, l ∈ Bl then some (.checkPred p) else none

variable {X : XGraph} {Γ : GVar → C} {M : PredModel}

/-! ## Binding facts -/

theorem setCls_base (σ : XBinding) (x : Var) (c : C) :
    (σ.setCls x c).base = σ.base.setCls x c := rfl

theorem setCls_lit (σ : XBinding) (x : Var) (c : C) : (σ.setCls x c).lit = σ.lit := rfl
theorem setCls_litSeq (σ : XBinding) (x : Var) (c : C) : (σ.setCls x c).litSeq = σ.litSeq := rfl

theorem cls_setCls (σ : XBinding) (x : Var) (c : C) (y : Var) :
    (σ.setCls x c).base.cls y = if y = x then some c else σ.base.cls y := by
  simp [XBinding.setCls, XBinding.withBase, Binding.setCls, Function.update_apply]

theorem lit_setLit (σ : XBinding) (l : Var) (x : Lit) (l' : Var) :
    (σ.setLit l x).lit l' = if l' = l then some x else σ.lit l' := by
  simp [XBinding.setLit, Function.update_apply]

theorem setLit_base (σ : XBinding) (l : Var) (x : Lit) : (σ.setLit l x).base = σ.base := rfl
theorem setLit_litSeq (σ : XBinding) (l : Var) (x : Lit) : (σ.setLit l x).litSeq = σ.litSeq := rfl

/-- Setting a class variable to the value it must have in `σ'` keeps the
extension; the variable itself may be unbound or already equal in `σ`. -/
theorem extends_setCls {σ σ' : XBinding} (h : XBinding.Extends σ σ') {x : Var} {c : C}
    (hx : σ'.base.cls x = some c) : XBinding.Extends (σ.setCls x c) σ' := by
  refine ⟨⟨?_, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2⟩, h.2.1, h.2.2⟩
  intro y d hy
  rw [setCls_base, Binding.setCls] at hy
  simp only [Function.update_apply] at hy
  split at hy
  · subst_vars; cases hy; exact hx
  · exact h.1.1 y d hy

theorem extends_setLit {σ σ' : XBinding} (h : XBinding.Extends σ σ') {l : Var} {x : Lit}
    (hx : σ'.lit l = some x) : XBinding.Extends (σ.setLit l x) σ' := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro l' y hy
  rw [lit_setLit] at hy
  split at hy
  · subst_vars; cases hy; exact hx
  · exact h.2.1 l' y hy

/-- `σ.setCls x c` extends `σ` when `x` is unbound (or already `c`). -/
theorem extends_self_setCls {σ : XBinding} {x : Var} {c : C}
    (hx : σ.base.cls x = none ∨ σ.base.cls x = some c) :
    XBinding.Extends σ (σ.setCls x c) := by
  refine ⟨⟨?_, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩,
    fun _ _ h => h, fun _ _ h => h⟩
  intro y d hy
  rw [setCls_base, Binding.setCls]
  simp only [Function.update_apply]
  split
  · subst_vars
    rcases hx with hx | hx <;> rw [hx] at hy
    · cases hy
    · exact hy
  · exact hy

theorem extends_self_setLit {σ : XBinding} {l : Var} {x : Lit}
    (hx : σ.lit l = none ∨ σ.lit l = some x) : XBinding.Extends σ (σ.setLit l x) := by
  refine ⟨Binding.Extends.refl _, ?_, fun _ _ h => h⟩
  intro l' y hy
  rw [lit_setLit]
  split
  · subst_vars
    rcases hx with hx | hx <;> rw [hx] at hy
    · cases hy
    · exact hy
  · exact hy

/-! ## A.1 `CheckNeq` -/

theorem checkNeq_iff {x y : Var} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.checkNeq x y) σ ↔ σ' = σ ∧ Atom.Holds X Γ M (.neq x y) σ := by
  simp only [stepList, Atom.Holds]
  cases hx : σ.base.cls x <;> cases hy : σ.base.cls y <;> simp
  rename_i a b
  constructor
  · rintro ⟨hab, rfl⟩; exact ⟨rfl, hab⟩
  · rintro ⟨rfl, hab⟩; exact ⟨hab, rfl⟩

theorem checkNeq_sound {x y : Var} {σ σ' : XBinding}
    (h : σ' ∈ stepList X Γ M (.checkNeq x y) σ) : σ' = σ ∧ Atom.Holds X Γ M (.neq x y) σ :=
  checkNeq_iff.1 h

theorem checkNeq_complete {x y : Var} {σ : XBinding} (h : Atom.Holds X Γ M (.neq x y) σ) :
    σ ∈ stepList X Γ M (.checkNeq x y) σ :=
  checkNeq_iff.2 ⟨rfl, h⟩

/-! ## A.2 `CheckEqGlobal` -/

theorem checkEqGlobal_iff {x : Var} {g : GVar} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.checkEqGlobal x g) σ ↔ σ' = σ ∧ Atom.Holds X Γ M (.eqGlobal x g) σ := by
  simp only [stepList, Atom.Holds]
  cases hx : σ.base.cls x <;> simp [hx]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by simp_all, by simp_all⟩

theorem checkEqGlobal_sound {x : Var} {g : GVar} {σ σ' : XBinding}
    (h : σ' ∈ stepList X Γ M (.checkEqGlobal x g) σ) :
    σ' = σ ∧ Atom.Holds X Γ M (.eqGlobal x g) σ :=
  checkEqGlobal_iff.1 h

theorem checkEqGlobal_complete {x : Var} {g : GVar} {σ : XBinding}
    (h : Atom.Holds X Γ M (.eqGlobal x g) σ) : σ ∈ stepList X Γ M (.checkEqGlobal x g) σ :=
  checkEqGlobal_iff.2 ⟨rfl, h⟩

/-! ## A.3 `BindGlobal` -/

theorem bindGlobal_iff {x : Var} {g : GVar} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.bindGlobal x g) σ ↔ σ' = σ.setCls x (Γ g) := by
  simp [stepList]

/-- Every output binds the atom; it extends `σ` when `x` was unbound. -/
theorem bindGlobal_sound {x : Var} {g : GVar} {σ σ' : XBinding}
    (h : σ' ∈ stepList X Γ M (.bindGlobal x g) σ) :
    Atom.Holds X Γ M (.eqGlobal x g) σ' ∧
      (σ.base.cls x = none → XBinding.Extends σ σ') := by
  rw [bindGlobal_iff] at h
  subst h
  refine ⟨?_, fun hx => extends_self_setCls (Or.inl hx)⟩
  simp [Atom.Holds, cls_setCls]

theorem bindGlobal_complete {x : Var} {g : GVar} {σ σ' : XBinding}
    (hext : XBinding.Extends σ σ') (h : Atom.Holds X Γ M (.eqGlobal x g) σ') :
    ∃ σ'' ∈ stepList X Γ M (.bindGlobal x g) σ, XBinding.Extends σ'' σ' :=
  ⟨σ.setCls x (Γ g), bindGlobal_iff.2 rfl, extends_setCls hext h⟩

/-! ## A.4 `CopyBinding` -/

theorem copyBinding_iff {x y : Var} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.copyBinding x y) σ ↔
      ∃ c, σ.base.cls y = some c ∧ σ' = σ.setCls x c := by
  simp only [stepList]
  cases hy : σ.base.cls y <;> simp

theorem copyBinding_sound {x y : Var} {σ σ' : XBinding}
    (h : σ' ∈ stepList X Γ M (.copyBinding x y) σ) :
    Atom.Holds X Γ M (.eq x y) σ' ∧ (σ.base.cls x = none → XBinding.Extends σ σ') := by
  obtain ⟨c, hy, rfl⟩ := copyBinding_iff.1 h
  refine ⟨⟨c, ?_, ?_⟩, fun hx => extends_self_setCls (Or.inl hx)⟩
  · simp [cls_setCls]
  · rw [cls_setCls]; split <;> simp_all

theorem copyBinding_complete {x y : Var} {σ σ' : XBinding}
    (hext : XBinding.Extends σ σ') (hy : (σ.base.cls y).isSome)
    (h : Atom.Holds X Γ M (.eq x y) σ') :
    ∃ σ'' ∈ stepList X Γ M (.copyBinding x y) σ, XBinding.Extends σ'' σ' := by
  obtain ⟨c, hx', hy'⟩ := h
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hy
  have := hext.1.1 y d hd
  rw [hy'] at this
  cases this
  exact ⟨σ.setCls x c, copyBinding_iff.2 ⟨c, hd, rfl⟩, extends_setCls hext hx'⟩

/-! ## A.5 `ExtractLitVal` -/

theorem extractLitVal_iff {v l : Var} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.extractLitVal v l) σ ↔
      ∃ id x, σ.base.node v = some id ∧ X.litOf id = some x ∧ σ' = σ.setLit l x := by
  simp only [stepList]
  cases hv : σ.base.node v
  · simp
  · rename_i id
    cases hl : X.litOf id <;> simp [hl]

theorem extractLitVal_sound {v l : Var} {σ σ' : XBinding}
    (h : σ' ∈ stepList X Γ M (.extractLitVal v l) σ) :
    Atom.Holds X Γ M (.litBind v l) σ' ∧ (σ.lit l = none → XBinding.Extends σ σ') := by
  obtain ⟨id, x, hv, hl, rfl⟩ := extractLitVal_iff.1 h
  refine ⟨⟨id, x, hv, hl, by simp [lit_setLit]⟩, fun hx => extends_self_setLit (Or.inl hx)⟩

theorem extractLitVal_complete {v l : Var} {σ σ' : XBinding}
    (hext : XBinding.Extends σ σ') (hv : (σ.base.node v).isSome)
    (h : Atom.Holds X Γ M (.litBind v l) σ') :
    ∃ σ'' ∈ stepList X Γ M (.extractLitVal v l) σ, XBinding.Extends σ'' σ' := by
  obtain ⟨id, x, hv', hl, hx⟩ := h
  obtain ⟨id', hid⟩ := Option.isSome_iff_exists.1 hv
  have := hext.1.2.1 v id' hid
  rw [hv'] at this
  cases this
  exact ⟨σ.setLit l x, extractLitVal_iff.2 ⟨id, x, hid, hl, rfl⟩, extends_setLit hext hx⟩

/-! ## A.6 `CheckLit` -/

theorem checkLit_iff {v : Var} {c : LVal} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.checkLit v c) σ ↔ σ' = σ ∧ Atom.Holds X Γ M (.lit v c) σ := by
  simp only [stepList, Atom.Holds]
  cases hv : σ.base.node v <;> simp [hv]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨h, rfl⟩

theorem checkLit_sound {v : Var} {c : LVal} {σ σ' : XBinding}
    (h : σ' ∈ stepList X Γ M (.checkLit v c) σ) : σ' = σ ∧ Atom.Holds X Γ M (.lit v c) σ :=
  checkLit_iff.1 h

theorem checkLit_complete {v : Var} {c : LVal} {σ : XBinding}
    (h : Atom.Holds X Γ M (.lit v c) σ) : σ ∈ stepList X Γ M (.checkLit v c) σ :=
  checkLit_iff.2 ⟨rfl, h⟩

/-! ## A.7 `CheckPred` -/

theorem checkPred_iff {p : PredExpr} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.checkPred p) σ ↔ σ' = σ ∧ Atom.Holds X Γ M (.pred p) σ := by
  simp only [stepList, Atom.Holds]
  cases h : evalPred X M σ p with
  | none => simp
  | some w => by_cases ht : M.truthy w = true <;> simp [ht]

theorem checkPred_sound {p : PredExpr} {σ σ' : XBinding}
    (h : σ' ∈ stepList X Γ M (.checkPred p) σ) : σ' = σ ∧ Atom.Holds X Γ M (.pred p) σ :=
  checkPred_iff.1 h

theorem checkPred_complete {p : PredExpr} {σ : XBinding} (h : Atom.Holds X Γ M (.pred p) σ) :
    σ ∈ stepList X Γ M (.checkPred p) σ :=
  checkPred_iff.2 ⟨rfl, h⟩

/-- The fault of a guard: the guard is undefined on the binding. -/
theorem checkPred_fault {p : PredExpr} {σ : XBinding} :
    stepFault X Γ M (.checkPred p) σ = true ↔ evalPred X M σ p = none := by
  simp [stepFault]

/-- Only `CheckPred` faults among the simple steps. -/
theorem stepFault_simple (s : XStep) (σ : XBinding)
    (hs : ∀ p, s ≠ .checkPred p) (hc : ∀ v S, s ≠ .collect v S) :
    stepFault X Γ M s σ = false := by
  cases s <;> first | rfl | exact absurd rfl (hs _) | exact absurd rfl (hc _ _)

/-- The core `CheckEq` step implements `Eq` in check mode. -/
theorem checkEq_iff {x y : Var} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.core (.checkEq x y)) σ ↔ σ' = σ ∧ Atom.Holds X Γ M (.eq x y) σ := by
  rw [mem_stepList_core]
  simp only [runStep, Atom.Holds]
  cases hx : σ.base.cls x <;> cases hy : σ.base.cls y <;> simp [hx, hy]
  constructor
  · rintro ⟨⟨rfl, hb⟩, hl, hls⟩
    refine ⟨?_, rfl⟩
    cases σ'; cases σ; simp_all
  · rintro ⟨rfl, h⟩
    simp [h]

/-! ## Pattern-level literal forms (`Pat.lit`, `Pat.litBind`, A.5/A.6) -/

/-- The join's binding of the node variable: node and class (`joinBind`). -/
def XBinding.joinBind (X : XGraph) (σ : XBinding) (v : Var) (id : NodeId) : XBinding :=
  σ.withBase (Semper.EMatch.joinBind X.G σ.base v id)

theorem joinBind_base (σ : XBinding) (v : Var) (id : NodeId) :
    (σ.joinBind X v id).base = Semper.EMatch.joinBind X.G σ.base v id := rfl

theorem node_joinBind (σ : XBinding) (v : Var) (id : NodeId) :
    (σ.joinBind X v id).base.node v = some id := by
  rw [joinBind_base]; simp

theorem mem_join_byOp {v : Var} {f : Sym} {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.core (.join v [.byOp f])) σ ↔
      ∃ id n, σ' = σ.joinBind X v id ∧ (id, n) ∈ X.G.nodes ∧ n.op = f := by
  rw [mem_stepList_core]
  simp only [runStep, List.mem_map]
  constructor
  · rintro ⟨⟨id, hid, hb⟩, hl, hls⟩
    have hj := (join_complete X.G σ.base [.byOp f] id).1 hid
    obtain ⟨-, hp⟩ := hj
    obtain ⟨n, hn, hop⟩ := hp _ (List.mem_singleton_self _)
    refine ⟨id, n, ?_, hn, hop⟩
    cases σ'
    simp only [XBinding.joinBind, XBinding.withBase] at *
    subst hl hls hb; rfl
  · rintro ⟨id, n, rfl, hn, hop⟩
    refine ⟨⟨id, ?_, rfl⟩, rfl, rfl⟩
    exact (join_complete X.G σ.base [.byOp f] id).2
      ⟨⟨n, hn⟩, fun l hl => by
        rw [List.mem_singleton] at hl; subst hl; exact ⟨n, hn, hop⟩⟩

/-- `Pat.lit f c` at the root: a literal node of head `f` with value `c`. -/
theorem lit_pattern_iff {v : Var} {f : Sym} {c : LVal} {σ σ' : XBinding} :
    σ' ∈ runXL X Γ M [.core (.join v [.byOp f]), .checkLit v c] σ ↔
      ∃ id n, σ' = σ.joinBind X v id ∧ (id, n) ∈ X.G.nodes ∧ n.op = f ∧
        (X.litOf id).map X.litVal = some c := by
  rw [mem_runXL_cons]
  constructor
  · rintro ⟨τ, hτ, hσ'⟩
    rw [mem_runXL_cons] at hσ'
    obtain ⟨τ', hτ', hσ'⟩ := hσ'
    simp only [runXL, List.mem_singleton] at hσ'
    subst hσ'
    obtain ⟨rfl, id', hid, hlit⟩ := checkLit_iff.1 hτ'
    obtain ⟨id, n, rfl, hn, hop⟩ := mem_join_byOp.1 hτ
    rw [node_joinBind] at hid
    cases hid
    exact ⟨_, n, rfl, hn, hop, hlit⟩
  · rintro ⟨id, n, rfl, hn, hop, hlit⟩
    refine ⟨σ.joinBind X v id, mem_join_byOp.2 ⟨id, n, rfl, hn, hop⟩, ?_⟩
    rw [mem_runXL_cons]
    refine ⟨σ.joinBind X v id, checkLit_iff.2 ⟨rfl, id, node_joinBind _ _ _, hlit⟩, ?_⟩
    simp [runXL]

/-- `Pat.litBind f l` at the root: a literal node of head `f`, its payload
bound to `l`. -/
theorem litBind_pattern_iff {v l : Var} {f : Sym} {σ σ' : XBinding} :
    σ' ∈ runXL X Γ M [.core (.join v [.byOp f]), .extractLitVal v l] σ ↔
      ∃ id n x, σ' = (σ.joinBind X v id).setLit l x ∧ (id, n) ∈ X.G.nodes ∧ n.op = f ∧
        X.litOf id = some x := by
  rw [mem_runXL_cons]
  constructor
  · rintro ⟨τ, hτ, hσ'⟩
    rw [mem_runXL_cons] at hσ'
    obtain ⟨τ', hτ', hσ'⟩ := hσ'
    simp only [runXL, List.mem_singleton] at hσ'
    subst hσ'
    obtain ⟨id', x, hid, hlit, rfl⟩ := extractLitVal_iff.1 hτ'
    obtain ⟨id, n, rfl, hn, hop⟩ := mem_join_byOp.1 hτ
    rw [node_joinBind] at hid
    cases hid
    exact ⟨_, n, x, rfl, hn, hop, hlit⟩
  · rintro ⟨id, n, x, rfl, hn, hop, hlit⟩
    refine ⟨σ.joinBind X v id, mem_join_byOp.2 ⟨id, n, rfl, hn, hop⟩, ?_⟩
    rw [mem_runXL_cons]
    refine ⟨_, extractLitVal_iff.2 ⟨id, x, node_joinBind _ _ _, hlit, rfl⟩, ?_⟩
    simp [runXL]

/-! ## The lowering table, generically -/

/-- The class variable a bind-mode step writes, if any. -/
def XStep.bindTarget : XStep → Option Var
  | .bindGlobal x _ => some x
  | .copyBinding x _ => some x
  | _ => none

/-- The literal variable a step writes, if any. -/
def XStep.litTarget : XStep → Option Var
  | .extractLitVal _ l => some l
  | _ => none

/-- The node variables an atom reads (the literal atoms' node). -/
def Atom.nodeReads : Atom → List Var
  | .lit v _ => [v]
  | .litBind v _ => [v]
  | _ => []

/-- A guard reads only its literal variables. -/
theorem evalPred_congr {σ σ' : XBinding} :
    ∀ p : PredExpr, (∀ l ∈ p.litVars, σ.lit l = σ'.lit l) →
      evalPred X M σ p = evalPred X M σ' p
  | .val l, h => by simp [evalPred, h l (by simp [PredExpr.litVars])]
  | .const c, _ => rfl
  | .app f args, h => by
      simp only [evalPred]
      rw [evalPreds_congr args (by simpa [PredExpr.litVars] using h)]
termination_by p => sizeOf p
where
  evalPreds_congr : ∀ args : List PredExpr,
      (∀ l ∈ PredExpr.litVarsList args, σ.lit l = σ'.lit l) →
      evalPreds X M σ args = evalPreds X M σ' args
  | [], _ => rfl
  | a :: as, h => by
      simp only [evalPreds]
      rw [evalPred_congr a (fun l hl => h l (by simp [PredExpr.litVarsList, hl])),
        evalPreds_congr as (fun l hl => h l (by simp [PredExpr.litVarsList, hl]))]
  termination_by args => sizeOf args

/-- Soundness of the lowering: every output of the lowered step extends the
input and satisfies the atom. The bind-mode target must be unbound on
entry (`hfresh`), as the scheduler guarantees (it is marked bound only
after the step). -/
theorem lower_sound {B Bl : List Var} {a : Atom} {s : XStep} {σ σ' : XBinding}
    (hl : lower B Bl a = some s)
    (hfresh : ∀ x, s.bindTarget = some x → σ.base.cls x = none)
    (hfreshLit : ∀ l, s.litTarget = some l → σ.lit l = none)
    (h : σ' ∈ stepList X Γ M s σ) :
    XBinding.Extends σ σ' ∧ Atom.Holds X Γ M a σ' := by
  cases a with
  | eq x y =>
      simp only [lower] at hl
      split_ifs at hl with hx hy hy <;> cases hl
      · obtain ⟨rfl, hh⟩ := checkEq_iff.1 h
        exact ⟨XBinding.Extends.refl _, hh⟩
      · obtain ⟨hh, hext⟩ := copyBinding_sound h
        obtain ⟨c, h1, h2⟩ := hh
        exact ⟨hext (hfresh y rfl), c, h2, h1⟩
      · obtain ⟨hh, hext⟩ := copyBinding_sound h
        exact ⟨hext (hfresh x rfl), hh⟩
  | neq x y =>
      simp only [lower] at hl
      split_ifs at hl <;> cases hl
      obtain ⟨rfl, hh⟩ := checkNeq_sound h
      exact ⟨XBinding.Extends.refl _, hh⟩
  | eqGlobal x g =>
      simp only [lower] at hl
      split_ifs at hl <;> cases hl
      · obtain ⟨rfl, hh⟩ := checkEqGlobal_sound h
        exact ⟨XBinding.Extends.refl _, hh⟩
      · obtain ⟨hh, hext⟩ := bindGlobal_sound h
        exact ⟨hext (hfresh x rfl), hh⟩
  | lit v c =>
      simp only [lower] at hl
      split_ifs at hl <;> cases hl
      obtain ⟨rfl, hh⟩ := checkLit_sound h
      exact ⟨XBinding.Extends.refl _, hh⟩
  | litBind v l =>
      simp only [lower] at hl
      split_ifs at hl <;> cases hl
      obtain ⟨id, x, hv, hx, rfl⟩ := extractLitVal_iff.1 h
      -- `ExtractLitVal` overwrites `lit_vals[l]` (no undo, A.5); the output
      -- extends the input only when `l` was unbound or already equal. Without
      -- that hypothesis the output agrees with the input on every other slot.
      exact ⟨extends_self_setLit (Or.inl (hfreshLit l rfl)), id, x, hv, hx, by simp [lit_setLit]⟩
  | pred p =>
      simp only [lower] at hl
      split_ifs at hl <;> cases hl
      obtain ⟨rfl, hh⟩ := checkPred_sound h
      exact ⟨XBinding.Extends.refl _, hh⟩


/-- The value a bound variable of `σ` has in an extension. -/
theorem cls_of_extends {σ σ' : XBinding} (hext : XBinding.Extends σ σ') {x : Var}
    (hx : (σ.base.cls x).isSome) {c : C} (hc : σ'.base.cls x = some c) :
    σ.base.cls x = some c := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hx
  have := hext.1.1 x d hd
  rw [hc] at this
  cases this
  exact hd

theorem lit_of_extends {σ σ' : XBinding} (hext : XBinding.Extends σ σ') {l : Var}
    (hl : (σ.lit l).isSome) : σ.lit l = σ'.lit l := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hl
  rw [hd, hext.2.1 l d hd]

/-- Completeness of the lowering: every extension satisfying the atom is
reached by the lowered step, given that the variables the table counted as
bound are bound in `σ` (`hB` classes, `hBl` literals, `hN` the literal
atoms' node variable). -/
theorem lower_complete {B Bl : List Var} {a : Atom} {s : XStep} {σ σ' : XBinding}
    (hl : lower B Bl a = some s)
    (hB : ∀ x ∈ B, (σ.base.cls x).isSome) (hBl : ∀ l ∈ Bl, (σ.lit l).isSome)
    (hN : ∀ v ∈ a.nodeReads, (σ.base.node v).isSome)
    (hext : XBinding.Extends σ σ') (h : Atom.Holds X Γ M a σ') :
    ∃ σ'' ∈ stepList X Γ M s σ, XBinding.Extends σ'' σ' := by
  cases a with
  | eq x y =>
      simp only [lower] at hl
      obtain ⟨c, hx', hy'⟩ := h
      split_ifs at hl with hx hy hy <;> cases hl
      · refine ⟨σ, ?_, hext⟩
        rw [mem_stepList_core]
        refine ⟨?_, rfl, rfl⟩
        simp [runStep, cls_of_extends hext (hB x hx) hx', cls_of_extends hext (hB y hy) hy']
      · exact copyBinding_complete hext (hB x hx) ⟨c, hy', hx'⟩
      · exact copyBinding_complete hext (hB y hy) ⟨c, hx', hy'⟩
  | neq x y =>
      simp only [lower] at hl
      split_ifs at hl with hxy <;> cases hl
      obtain ⟨a, b, hx', hy', hab⟩ := h
      exact ⟨σ, checkNeq_complete ⟨a, b, cls_of_extends hext (hB x hxy.1) hx',
        cls_of_extends hext (hB y hxy.2) hy', hab⟩, hext⟩
  | eqGlobal x g =>
      simp only [lower] at hl
      split_ifs at hl with hx <;> cases hl
      · exact ⟨σ, checkEqGlobal_complete (cls_of_extends hext (hB x hx) h), hext⟩
      · exact bindGlobal_complete hext h
  | lit v c =>
      simp only [lower] at hl
      split_ifs at hl <;> cases hl
      obtain ⟨id, hv', hlit⟩ := h
      obtain ⟨id', hid⟩ := Option.isSome_iff_exists.1 (hN v (by simp [Atom.nodeReads]))
      have := hext.1.2.1 v id' hid
      rw [hv'] at this
      cases this
      exact ⟨σ, checkLit_complete ⟨_, hid, hlit⟩, hext⟩
  | litBind v l =>
      simp only [lower] at hl
      split_ifs at hl <;> cases hl
      exact extractLitVal_complete hext (hN v (by simp [Atom.nodeReads])) h
  | pred p =>
      simp only [lower] at hl
      split_ifs at hl with hp <;> cases hl
      obtain ⟨w, hw, ht⟩ := h
      refine ⟨σ, checkPred_complete ⟨w, ?_, ht⟩, hext⟩
      rw [evalPred_congr p (fun l hl => lit_of_extends hext (hBl l (hp l hl)))]
      exact hw

end Semper.EMatch.Steps
