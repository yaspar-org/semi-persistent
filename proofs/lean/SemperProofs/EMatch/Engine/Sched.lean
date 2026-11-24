import SemperProofs.EMatch.Engine.Lower

/-!
# The scheduler (spec-scheduler §3, §4, §6)

The plan grammar `Sched` (spec §3.1): starting from a used set and a bound
set, either every scanning atom is used and no eager atom is lowerable
(`done`), or an unused eager atom whose operands allow it is lowered
(`eager`), or any unused scanning atom is lowered (`pick`). The engine's
static scheduler and its runtime scheduler both produce `Sched` plans; the
selectivity estimate only decides which `pick` is taken.

`SchedA` is the same grammar on plans whose steps carry the index of the
atom they came from; `runA` interprets such a plan under a per-atom
`IndexMode` (spec §6: `full`, `delta`, `fullMinusDelta`), the join of atom
`i` keeping only the candidates its mode admits. With the constant mode
`full` this is the plain interpreter `run`.

The main theorem `schedA_run` characterises `runA` on any `SchedA` plan from
any state satisfying the run invariant `Inv`; `plan_matches` (§3.2),
`runND_*` (§4) and `variant_partition` (§6) are its corollaries.
-/

namespace Semper.EMatch

open Binding (Extends)

/-! ## Query atoms: scanning atoms and the root-binding equalities -/

/-- A query atom: a scanning atom, or an `Eq` between two class variables
(the only eager atom this development covers). -/
inductive QAtom where
  | scan (a : RAtom)
  | eq (x y : Var)
  deriving DecidableEq

namespace QAtom

def scanning : QAtom → Prop
  | .scan _ => True
  | .eq _ _ => False

/-- The variables the atom's lowering binds. -/
def binds : QAtom → Finset Var
  | .scan a => a.binds
  | .eq x y => {x, y}

/-- `try_eager_lower` accepts the atom (`S:1417-1436`): an `Eq` with at
least one bound side. -/
def eagerFree : QAtom → Finset Var → Prop
  | .scan _, _ => False
  | .eq x y, B => x ∈ B ∨ y ∈ B

/-- The eager lowering of an `Eq` (`S:1418-1436`): both bound → `checkEq`;
one bound → `copyBinding` into the other. -/
def eagerLower : QAtom → Finset Var → Plan
  | .scan _, _ => []
  | .eq x y, B =>
      if x ∈ B then (if y ∈ B then [.checkEq x y] else [.copyBinding y x])
      else [.copyBinding x y]

end QAtom

/-- Semantics of a query atom. -/
def QSat (G : Graph) (σ : Binding) : QAtom → Prop
  | .scan a => AtomSat G σ a
  | .eq x y => ∃ c, σ.cls x = some c ∧ σ.cls y = some c

/-! ## The grammar -/

/-- Spec §3.1. `Sched atoms used B plan`: `plan` is a valid continuation
from the state where the atoms in `used` have been lowered and the class
variables in `B` are bound. -/
inductive Sched (atoms : List QAtom) : Finset Nat → Finset Var → Plan → Prop
  | done {used : Finset Nat} {B : Finset Var} :
      (∀ i a, atoms[i]? = some (.scan a) → i ∈ used) →
      (∀ i q, atoms[i]? = some q → i ∉ used → ¬ q.eagerFree B) →
      Sched atoms used B []
  | eager {used : Finset Nat} {B : Finset Var} {i : Nat} {q : QAtom} {rest : Plan} :
      atoms[i]? = some q → i ∉ used → q.eagerFree B →
      Sched atoms (insert i used) (B ∪ q.binds) rest →
      Sched atoms used B (q.eagerLower B ++ rest)
  | pick {used : Finset Nat} {B : Finset Var} {i : Nat} {a : RAtom} {rest : Plan} :
      atoms[i]? = some (.scan a) → i ∉ used →
      Sched atoms (insert i used) (B ∪ a.binds) rest →
      Sched atoms used B (lower a B ++ rest)

/-- `PlanOK atoms plan`: a plan the engine can produce for `atoms`. -/
def PlanOK (atoms : List QAtom) (plan : Plan) : Prop := Sched atoms ∅ ∅ plan

/-- Seeded plans (spec §3.3): the bound set starts at `pre`. -/
def PlanOKFrom (atoms : List QAtom) (pre : Finset Var) (plan : Plan) : Prop :=
  Sched atoms ∅ pre plan

/-! ## Annotated plans and index modes -/

/-- Lookup modes of the semi-naive variants (spec §6). -/
inductive IndexMode where
  | full
  | delta
  | fullMinusDelta
  deriving DecidableEq

/-- Which node ids a mode admits, for a "new" predicate on ids. -/
def modeOk (isNew : NodeId → Bool) : IndexMode → NodeId → Bool
  | .full, _ => true
  | .delta, id => isNew id
  | .fullMinusDelta, id => !isNew id

/-- A plan whose steps carry the index of the atom that produced them. -/
abbrev APlan := List (Nat × Step)

/-- `Step::Join` consults the mode of its atom (`E:2864-2874`); every other
step is mode-blind. -/
def runStepA (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) :
    Nat × Step → Binding → List Binding
  | (i, .join t ls), σ =>
      ((candidates G σ ls).filter (fun id => modeOk isNew (mode i) id)).map (joinBind G σ t)
  | (_, s), σ => runStep G s σ

def runA (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) : APlan → Binding → List Binding
  | [], σ => [σ]
  | s :: ss, σ => (runStepA G isNew mode s σ).flatMap (runA G isNew mode ss)

/-- The annotated grammar: the same rules, each emitted step tagged with its
atom's index. -/
inductive SchedA (atoms : List QAtom) : Finset Nat → Finset Var → APlan → Prop
  | done {used : Finset Nat} {B : Finset Var} :
      (∀ i a, atoms[i]? = some (.scan a) → i ∈ used) →
      (∀ i q, atoms[i]? = some q → i ∉ used → ¬ q.eagerFree B) →
      SchedA atoms used B []
  | eager {used : Finset Nat} {B : Finset Var} {i : Nat} {q : QAtom} {rest : APlan} :
      atoms[i]? = some q → i ∉ used → q.eagerFree B →
      SchedA atoms (insert i used) (B ∪ q.binds) rest →
      SchedA atoms used B ((q.eagerLower B).map (i, ·) ++ rest)
  | pick {used : Finset Nat} {B : Finset Var} {i : Nat} {a : RAtom} {rest : APlan} :
      atoms[i]? = some (.scan a) → i ∉ used →
      SchedA atoms (insert i used) (B ∪ a.binds) rest →
      SchedA atoms used B ((lower a B).map (i, ·) ++ rest)

theorem schedA_of_sched {atoms : List QAtom} {used : Finset Nat} {B : Finset Var} {plan : Plan}
    (h : Sched atoms used B plan) : ∃ ap : APlan, SchedA atoms used B ap ∧ ap.map (·.2) = plan := by
  induction h with
  | done h₁ h₂ => exact ⟨[], SchedA.done h₁ h₂, rfl⟩
  | eager hq hu hf _ ih =>
      obtain ⟨ap, hap, rfl⟩ := ih
      exact ⟨_, SchedA.eager hq hu hf hap, by simp⟩
  | pick ha hu _ ih =>
      obtain ⟨ap, hap, rfl⟩ := ih
      exact ⟨_, SchedA.pick ha hu hap, by simp⟩

theorem sched_of_schedA {atoms : List QAtom} {used : Finset Nat} {B : Finset Var} {ap : APlan}
    (h : SchedA atoms used B ap) : Sched atoms used B (ap.map (·.2)) := by
  induction h with
  | done h₁ h₂ => exact Sched.done h₁ h₂
  | eager hq hu hf _ ih => simpa using Sched.eager hq hu hf ih
  | pick ha hu _ ih => simpa using Sched.pick ha hu ih

/-- With the constant mode `full`, `runA` is `run` on the erased plan. -/
theorem runA_full (G : Graph) (isNew : NodeId → Bool) :
    ∀ (ap : APlan) (σ : Binding), runA G isNew (fun _ => .full) ap σ = run G (ap.map (·.2)) σ := by
  intro ap
  induction ap with
  | nil => intro σ; rfl
  | cons s ss ih =>
      intro σ
      obtain ⟨i, s⟩ := s
      have hs : runStepA G isNew (fun _ => .full) (i, s) σ = runStep G s σ := by
        cases s <;> first | rfl | simp [runStepA, runStep, modeOk]
      simp only [runA, List.map_cons, run, hs]
      congr 1
      funext σ'
      exact ih σ'

theorem runA_append (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) (a b : APlan)
    (σ : Binding) : runA G isNew mode (a ++ b) σ = (runA G isNew mode a σ).flatMap (runA G isNew mode b) := by
  induction a generalizing σ with
  | nil => simp [runA]
  | cons s ss ih =>
      simp only [List.cons_append, runA, List.flatMap_assoc]
      congr 1
      funext σ'
      exact ih σ'

theorem mem_runA_append {G : Graph} {isNew : NodeId → Bool} {mode : Nat → IndexMode} {a b : APlan}
    {σ σ' : Binding} :
    σ' ∈ runA G isNew mode (a ++ b) σ ↔ ∃ σm ∈ runA G isNew mode a σ, σ' ∈ runA G isNew mode b σm := by
  rw [runA_append, List.mem_flatMap]

/-- A plan without joins is mode-blind. -/
theorem runA_map_of_no_join (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) (i : Nat) :
    ∀ (plan : Plan) (σ : Binding), (∀ s ∈ plan, ∀ t ls, s ≠ .join t ls) →
    runA G isNew mode (plan.map (i, ·)) σ = run G plan σ := by
  intro plan
  induction plan with
  | nil => intro σ _; rfl
  | cons s ss ih =>
      intro σ hnj
      simp only [List.map_cons, runA, run]
      have : runStepA G isNew mode (i, s) σ = runStep G s σ := by
        cases s with
        | join t ls => exact absurd rfl (hnj _ (List.mem_cons_self ..) t ls)
        | _ => rfl
      rw [this]
      congr 1
      funext σ'
      exact ih σ' (fun s' hs' => hnj s' (List.mem_cons_of_mem _ hs'))

theorem lowerBody_no_join (a : RAtom) (B : Finset Var) :
    ∀ s ∈ lowerBody a B, ∀ t ls, s ≠ .join t ls := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | plain cs =>
      simp only [lowerBody]
      generalize insert n B = B'
      generalize 0 = i
      induction cs generalizing i B' with
      | nil => simp [childSteps]
      | cons c cs ih =>
          intro s hs t ls
          simp only [childSteps] at hs
          split at hs
          · rw [List.mem_cons] at hs
            rcases hs with rfl | hs
            · simp
            · exact ih _ _ s hs t ls
          · rw [List.mem_cons] at hs
            rcases hs with rfl | hs
            · simp
            · exact ih _ _ s hs t ls
  | comm x y => simp [lowerBody]
  | assoc pre fx suf => simp [lowerBody]
  | ac es rest => simp [lowerBody]
  | aci es rest => simp [lowerBody]

theorem childSteps_node {G : Graph} {n : Var} :
    ∀ (cs : List Var) (i : Nat) (B : Finset Var) (σ σ' : Binding),
    σ' ∈ run G (childSteps n cs i B) σ → σ'.node = σ.node := by
  intro cs
  induction cs with
  | nil => intro i B σ σ' h; simp [childSteps, run] at h; rw [h]
  | cons c cs ih =>
      intro i B σ σ' h
      simp only [childSteps] at h
      split at h
      · rw [mem_run_cons] at h
        obtain ⟨σm, hm, h⟩ := h
        obtain ⟨rfl, -⟩ := runStep_checkChildEq_mem hm
        exact ih _ _ _ _ h
      · rw [mem_run_cons] at h
        obtain ⟨σm, hm, h⟩ := h
        obtain ⟨-, -, -, -, -, -, hfr⟩ := runStep_extractChild_mem hm
        rw [ih _ _ _ _ h, hfr.node]

/-- The body of a lowering never writes the node map. -/
theorem lowerBody_node {G : Graph} {a : RAtom} {B : Finset Var} {σ σ' : Binding}
    (h : σ' ∈ run G (lowerBody a B) σ) : σ'.node = σ.node := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | plain cs => exact childSteps_node cs 0 _ σ σ' h
  | comm x y =>
      simp only [lowerBody] at h
      rw [mem_run_cons] at h
      obtain ⟨σm, hm, h⟩ := h
      simp only [run, List.mem_singleton] at h
      subst h
      obtain ⟨_, _, _, -, hd⟩ := runStep_decomposeComm_mem hm
      exact (frame_decomposeComm hd).node
  | assoc pre fx suf =>
      simp only [lowerBody] at h
      rw [mem_run_cons] at h
      obtain ⟨σm, hm, h⟩ := h
      simp only [run, List.mem_singleton] at h
      subst h
      obtain ⟨_, _, -, hd⟩ := runStep_expandA_mem hm
      exact (frame_expandA hd).node
  | ac es rest =>
      simp only [lowerBody] at h
      rw [mem_run_cons] at h
      obtain ⟨σm, hm, h⟩ := h
      simp only [run, List.mem_singleton] at h
      subst h
      obtain ⟨_, _, -, hd⟩ := runStep_decomposeAC_mem hm
      exact (frame_decomposeAC _ _ _ _ _ hd).node
  | aci es rest =>
      simp only [lowerBody] at h
      rw [mem_run_cons] at h
      obtain ⟨σm, hm, h⟩ := h
      simp only [run, List.mem_singleton] at h
      subst h
      obtain ⟨_, _, -, hd⟩ := runStep_decomposeACI_mem hm
      exact (frame_decomposeACI _ _ _ _ _ hd).node

/-- The annotated run of a lowering: the plain run, filtered by the mode of
the atom on the joined node. -/
theorem mem_runA_lower {G : Graph} {isNew : NodeId → Bool} {mode : Nat → IndexMode} {i : Nat}
    {a : RAtom} {B : Finset Var} {σ σ' : Binding} :
    σ' ∈ runA G isNew mode ((lower a B).map (i, ·)) σ ↔
      σ' ∈ run G (lower a B) σ ∧ ∃ id, σ'.node a.node = some id ∧ modeOk isNew (mode i) id = true := by
  have hb : ∀ σ, runA G isNew mode ((lowerBody a B).map (i, ·)) σ = run G (lowerBody a B) σ :=
    fun σ => runA_map_of_no_join G isNew mode i _ σ (lowerBody_no_join a B)
  simp only [lower, List.map_cons, runA, run, List.mem_flatMap, hb]
  constructor
  · rintro ⟨σ₁, h₁, h⟩
    simp only [runStepA, List.mem_map, List.mem_filter] at h₁
    obtain ⟨id, ⟨hid, hmode⟩, rfl⟩ := h₁
    refine ⟨⟨_, by simp [runStep, List.mem_map]; exact ⟨id, hid, rfl⟩, h⟩, id, ?_, hmode⟩
    rw [lowerBody_node h]
    simp
  · rintro ⟨⟨σ₁, h₁, h⟩, id, hid, hmode⟩
    simp only [runStep, List.mem_map] at h₁
    obtain ⟨id', hid', rfl⟩ := h₁
    rw [lowerBody_node h] at hid
    simp only [joinBind_node_self] at hid
    obtain rfl := Option.some.inj hid
    refine ⟨_, ?_, h⟩
    simp only [runStepA, List.mem_map, List.mem_filter]
    exact ⟨_, ⟨hid', hmode⟩, rfl⟩

theorem eagerLower_no_join (q : QAtom) (B : Finset Var) :
    ∀ s ∈ q.eagerLower B, ∀ t ls, s ≠ .join t ls := by
  intro s hs t ls
  cases q with
  | scan a => simp [QAtom.eagerLower] at hs
  | eq x y =>
      simp only [QAtom.eagerLower] at hs
      split at hs <;> (try split at hs) <;> simp only [List.mem_singleton] at hs <;> subst hs <;> simp

theorem runA_eager (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) (i : Nat)
    (q : QAtom) (B : Finset Var) (σ : Binding) :
    runA G isNew mode ((q.eagerLower B).map (i, ·)) σ = run G (q.eagerLower B) σ :=
  runA_map_of_no_join G isNew mode i _ σ (eagerLower_no_join q B)

theorem mem_runA_eager {G : Graph} {isNew : NodeId → Bool} {mode : Nat → IndexMode} {i : Nat}
    {q : QAtom} {B : Finset Var} {σ σ' : Binding} :
    σ' ∈ runA G isNew mode ((q.eagerLower B).map (i, ·)) σ ↔ σ' ∈ run G (q.eagerLower B) σ := by
  rw [runA_eager]

/-! ## The eager step -/

/-- The specification of an eager `Eq` lowering: like `LowerSpec` with
nothing written but the two class variables. -/
structure EagerSpec (G : Graph) (q : QAtom) (B : Finset Var) (σ σ' : Binding) : Prop where
  ext : Extends σ σ'
  clsDom : ClsDom σ' (B ∪ q.binds)
  node : σ'.node = σ.node
  mult : σ'.mult = σ.mult
  rest : σ'.rest = σ.rest
  seqRest : σ'.seqRest = σ.seqRest
  finRest : σ'.finRest = σ.finRest
  sat : QSat G σ' q

theorem runStep_copyBinding_mem {G : Graph} {t o : Var} {σ σ' : Binding}
    (h : σ' ∈ runStep G (.copyBinding t o) σ) :
    ∃ c, σ.cls o = some c ∧ σ'.cls t = some c ∧ (σ' = σ ∨ (σ.cls t = none ∧ σ' = σ.setCls t c)) := by
  simp only [runStep] at h
  split at h
  · rename_i c hc
    split at h
    · rename_i c' hc'
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨c, hc, by rw [hc']; congr, Or.inl rfl⟩
      · simp at h
    · rename_i hnone
      simp only [List.mem_singleton] at h
      subst h
      exact ⟨c, hc, by simp, Or.inr ⟨hnone, rfl⟩⟩
  · simp at h

theorem clsDom_setCls {σ : Binding} {B : Finset Var} {x : Var} {c : C} (hdom : ClsDom σ B) :
    ClsDom (σ.setCls x c) (insert x B) := by
  intro w
  rw [Finset.mem_insert]
  by_cases hw : w = x
  · subst hw; simp
  · rw [setCls_cls_of_ne _ _ _ _ hw, hdom w]; simp [hw]

theorem clsDom_eq_of_mem {σ : Binding} {B : Finset Var} (hdom : ClsDom σ B) {x : Var} (hx : x ∈ B) :
    ClsDom σ (insert x B) := by
  intro w; rw [Finset.mem_insert, hdom w]
  constructor
  · rintro (rfl | h)
    · exact (hdom _).1 hx
    · exact h
  · exact Or.inr

/-- Soundness and completeness of the eager step. -/
theorem eager_sound {G : Graph} {q : QAtom} {B : Finset Var} {σ σ' : Binding}
    (hdom : ClsDom σ B) (hf : q.eagerFree B) (h : σ' ∈ run G (q.eagerLower B) σ) :
    EagerSpec G q B σ σ' := by
  cases q with
  | scan a => simp [QAtom.eagerFree] at hf
  | eq x y =>
      simp only [QAtom.eagerLower] at h
      have hbinds : B ∪ QAtom.binds (.eq x y) = insert y (insert x B) := by
        ext w; simp [QAtom.binds]; tauto
      split at h
      · rename_i hx
        split at h
        · rename_i hy
          rw [mem_run_cons] at h
          obtain ⟨σm, hm, h⟩ := h
          simp only [run, List.mem_singleton] at h
          subst h
          have := runStep_checkEq_mem hm
          subst this
          obtain ⟨c, hc⟩ := (hdom x).1 hx
          obtain ⟨c', hc'⟩ := (hdom y).1 hy
          have hcc : c = c' := by
            simp only [runStep, hc, hc'] at hm
            split at hm
            · assumption
            · simp at hm
          subst hcc
          have hd' : ClsDom σ' (B ∪ QAtom.binds (.eq x y)) := by
            rw [hbinds]
            exact clsDom_eq_of_mem (clsDom_eq_of_mem hdom hx) (Finset.mem_insert_of_mem hy)
          exact ⟨Extends.refl _, hd', rfl, rfl, rfl, rfl, rfl, c, hc, hc'⟩
        · rename_i hy
          rw [mem_run_cons] at h
          obtain ⟨σm, hm, h⟩ := h
          simp only [run, List.mem_singleton] at h
          subst h
          obtain ⟨c, hco, hct, hcase⟩ := runStep_copyBinding_mem hm
          rcases hcase with rfl | ⟨hnone, rfl⟩
          · exact absurd ((hdom y).2 ⟨c, hct⟩) hy
          · refine ⟨extends_setCls_of_none hnone, ?_, rfl, rfl, rfl, rfl, rfl, c, ?_, hct⟩
            · rw [hbinds]; exact clsDom_setCls (clsDom_eq_of_mem hdom hx)
            · rw [setCls_cls_of_ne _ _ _ _ (by rintro rfl; exact hy hx)]; exact hco
      · rename_i hx
        have hy : y ∈ B := by
          simp only [QAtom.eagerFree] at hf
          rcases hf with h' | h'
          · exact absurd h' hx
          · exact h'
        rw [mem_run_cons] at h
        obtain ⟨σm, hm, h⟩ := h
        simp only [run, List.mem_singleton] at h
        subst h
        obtain ⟨c, hco, hct, hcase⟩ := runStep_copyBinding_mem hm
        rcases hcase with rfl | ⟨hnone, rfl⟩
        · exact absurd ((hdom x).2 ⟨c, hct⟩) hx
        · refine ⟨extends_setCls_of_none hnone, ?_, rfl, rfl, rfl, rfl, rfl, c, hct, ?_⟩
          · rw [hbinds, Finset.insert_comm]
            exact clsDom_setCls (clsDom_eq_of_mem hdom hy)
          · rw [setCls_cls_of_ne _ _ _ _ (by rintro rfl; exact hx hy)]; exact hco

theorem eager_complete {G : Graph} {q : QAtom} {B : Finset Var} {σ σ' : Binding}
    (hdom : ClsDom σ B) (hf : q.eagerFree B) (hext : Extends σ σ') (hsat : QSat G σ' q) :
    ∃ σ₁ ∈ run G (q.eagerLower B) σ, Extends σ₁ σ' := by
  cases q with
  | scan a => simp [QAtom.eagerFree] at hf
  | eq x y =>
      obtain ⟨c, hx', hy'⟩ := hsat
      simp only [QAtom.eagerLower]
      split
      · rename_i hx
        obtain ⟨cx, hcx⟩ := (hdom x).1 hx
        have hcx' := hext.1 _ _ hcx
        rw [hx'] at hcx'
        obtain rfl := Option.some.inj hcx'
        split
        · rename_i hy
          obtain ⟨cy, hcy⟩ := (hdom y).1 hy
          have hcy' := hext.1 _ _ hcy
          rw [hy'] at hcy'
          obtain rfl := Option.some.inj hcy'
          exact ⟨σ, by simp [run, runStep, hcx, hcy], hext⟩
        · rename_i hy
          have hnone : σ.cls y = none := by
            rcases h : σ.cls y with _ | c'
            · rfl
            · exact absurd ((hdom y).2 ⟨c', h⟩) hy
          refine ⟨σ.setCls y c, by simp [run, runStep, hcx, hnone], ?_⟩
          refine ⟨?_, hext.2.1, hext.2.2.1, hext.2.2.2.1, hext.2.2.2.2.1, hext.2.2.2.2.2⟩
          intro w c' hw
          by_cases hwy : w = y
          · subst hwy; rw [setCls_cls_self] at hw; rw [← hw]; exact hy'
          · rw [setCls_cls_of_ne _ _ _ _ hwy] at hw; exact hext.1 w c' hw
      · rename_i hx
        have hy : y ∈ B := by
          simp only [QAtom.eagerFree] at hf
          rcases hf with h' | h'
          · exact absurd h' hx
          · exact h'
        obtain ⟨cy, hcy⟩ := (hdom y).1 hy
        have hcy' := hext.1 _ _ hcy
        rw [hy'] at hcy'
        obtain rfl := Option.some.inj hcy'
        have hnone : σ.cls x = none := by
          rcases h : σ.cls x with _ | c'
          · rfl
          · exact absurd ((hdom x).2 ⟨c', h⟩) hx
        refine ⟨σ.setCls x c, by simp [run, runStep, hcy, hnone], ?_⟩
        refine ⟨?_, hext.2.1, hext.2.2.1, hext.2.2.2.1, hext.2.2.2.2.1, hext.2.2.2.2.2⟩
        intro w c' hw
        by_cases hwx : w = x
        · subst hwx; rw [setCls_cls_self] at hw; rw [← hw]; exact hx'
        · rw [setCls_cls_of_ne _ _ _ _ hwx] at hw; exact hext.1 w c' hw

end Semper.EMatch
