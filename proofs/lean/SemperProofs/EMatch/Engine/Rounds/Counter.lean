import SemperProofs.EMatch.Engine.Rounds.Delta

/-!
# Where delta completeness fails (spec-semi-naive-rounds §C, §E)

Two counter-models, each the Lean form of an `.egg` program.

* `delta_incomplete_global`: a rule with a global reference, i.e. a class
  variable constrained to the class of a fixed node that no atom scans.
  With tracking on, the absorbed class's members enter the delta, but the
  rule scans none of them; the parent's stored child is the surviving
  representative, so nothing is recanonicalized. This is the engine's
  second exception (`saturate.rs:592-602`, fixture
  `semi_recanon_parent_delta.egg`) when the global is in a child
  position, and the confirmed gap `eq_global_local.egg` when the global
  is equated to a child variable by a `(= x g)` fact (`EqGlobal` on a
  non-node variable, which `needs_naive_match` does not catch).
* `delta_incomplete_untracked`: with tracking off, a merge that absorbs a
  nested atom's class into the class its parent already stores creates a
  match with no touched node (`semi_merge_membership_delta.egg`). This is
  why `track_merge_members` exists; the free function
  `saturate::saturate_semi` runs with it off.
-/

namespace Semper.EMatch

/-- A constraint of a resolved query with globals: an atom of the model,
or a global reference `x = class(gid)` (`PatVar::Global`, `EqGlobal`). -/
inductive RConstraint where
  | atom (q : QAtom)
  | global (x : Var) (gid : NodeId)

/-- Satisfaction: a global reads the round's representative of its node. -/
def RSat (G : Graph) (σ : Binding) : RConstraint → Prop
  | .atom q => QSat G σ q
  | .global x gid => σ.cls x = some (G.find gid)

/-! ## Counter-model 1: a global (symbols: 0 = `a`, 1 = `b`, 2 = `h`) -/

/-- Nodes `0 = (a)`, `1 = (b)`, `2 = (h (b))`; the round merges `a`'s class
into `b`'s with `b` surviving; `(h (b))` keeps its stored child `1`. -/
def gRound : Round where
  before := ⟨[(0, ⟨0, .tuple []⟩), (1, ⟨1, .tuple []⟩), (2, ⟨2, .tuple [1]⟩)], id⟩
  after := ⟨[(0, ⟨0, .tuple []⟩), (1, ⟨1, .tuple []⟩), (2, ⟨2, .tuple [1]⟩)],
    fun id => if id = 0 then 1 else id⟩
  added := ∅
  unions := [(0, 1)]
  subsumed := ∅
  touched := ∅
  mergeDelta := {0}
  tracking := true

/-- `(h x)` with `x` the global `g = (a)`: node variable `10`, child
variable `11`. -/
def gAtoms : List RConstraint := [.atom (.scan ⟨10, 2, .plain [11]⟩), .global 11 0]

/-- The match after the round: `(h (b))`, `x = class(b) = class(g)`. -/
def gσ : Binding where
  cls := fun x => if x = 10 then some 2 else if x = 11 then some 1 else none
  node := fun x => if x = 10 then some 2 else none
  mult := fun _ => none
  rest := fun _ => none
  seqRest := fun _ => none
  finRest := fun _ => none

theorem gRound_wf : gRound.WF where
  created_added := by
    rintro id ⟨⟨n', h⟩, hno⟩
    exact (hno n' h).elim
  added_touched := by simp [gRound]
  recanon_touched := by
    rintro id ⟨n, n', hn, hn', hne⟩
    simp [gRound] at hn hn'
    rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  subsumed_touched := by simp [gRound]
  absorbed_delta := by
    rintro - id ⟨n', h⟩ habs
    simp [gRound] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [Round.Absorbed, gRound] at habs ⊢
  no_split := by
    intro id id' h
    simp [gRound] at h
    subst h
    rfl
  children_canon := by
    simp [gRound, Graph.ChildrenCanon, Children.Canon]
  find_idem := by
    intro id
    by_cases h : id = 0 <;> simp [gRound, h]
  dedup := by
    intro id₁ id₂ n h₁ h₂
    simp [gRound] at h₁ h₂
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h₂ with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all

/-- The global counter-model: tracking on, the match is new, and no
scanning atom's node is new. -/
theorem delta_incomplete_global :
    ∃ (R : Round) (cs : List RConstraint) (σ' : Binding),
      R.WF ∧ R.tracking = true ∧ (∀ c ∈ cs, RSat R.after σ' c) ∧
      ¬ (∀ c ∈ cs, RSat R.before σ' c) ∧
      ∀ a : RAtom, RConstraint.atom (.scan a) ∈ cs →
        ∀ id, σ'.node a.node = some id → R.isNew id = false := by
  refine ⟨gRound, gAtoms, gσ, gRound_wf, rfl, ?_, ?_, ?_⟩
  · intro c hc
    simp [gAtoms] at hc
    rcases hc with rfl | rfl
    · refine ⟨2, ⟨2, .tuple [1]⟩, by simp [gσ], by simp [gRound], by simp [gσ, gRound], rfl, ?_⟩
      show MatchN _ (.plain 2 ([11].map .var)) _ _
      exact matchN_plain_vars.2 ⟨[1], rfl, List.Forall₂.cons (by simp [gσ]) List.Forall₂.nil⟩
    · simp [RSat, gσ, gRound]
  · intro h
    have := h (.global 11 0) (by simp [gAtoms])
    simp [RSat, gσ, gRound] at this
  · intro a ha id hid
    simp [gAtoms] at ha
    subst ha
    simp [gσ] at hid
    subst hid
    simp [Round.isNew, gRound]

/-! ## Counter-model 2: tracking off (symbols: 0 = `c`, 1 = `b`, 2 = `h`, 3 = `k`) -/

/-- Nodes `0 = (c)`, `1 = (k (c))`, `2 = (b)`, `3 = (h (b))`; the round
merges `(k (c))`'s class into `(b)`'s with `(b)` surviving; `(h (b))`
keeps its stored child `2`; nothing is touched. -/
def uRound : Round where
  before := ⟨[(0, ⟨0, .tuple []⟩), (1, ⟨3, .tuple [0]⟩), (2, ⟨1, .tuple []⟩),
    (3, ⟨2, .tuple [2]⟩)], id⟩
  after := ⟨[(0, ⟨0, .tuple []⟩), (1, ⟨3, .tuple [0]⟩), (2, ⟨1, .tuple []⟩),
    (3, ⟨2, .tuple [2]⟩)], fun id => if id = 1 then 2 else id⟩
  added := ∅
  unions := [(1, 2)]
  subsumed := ∅
  touched := ∅
  mergeDelta := ∅
  tracking := false

/-- `(h (k x))`: the `k` atom (node variable `10`, child `12`) and the `h`
atom (node variable `11`, child `10`). -/
def uAtoms : List QAtom := [.scan ⟨10, 3, .plain [12]⟩, .scan ⟨11, 2, .plain [10]⟩]

/-- The match after the round: `(h (b))` with `(k (c))` in `b`'s class. -/
def uσ : Binding where
  cls := fun x => if x = 10 then some 2 else if x = 11 then some 3 else
    if x = 12 then some 0 else none
  node := fun x => if x = 10 then some 1 else if x = 11 then some 3 else none
  mult := fun _ => none
  rest := fun _ => none
  seqRest := fun _ => none
  finRest := fun _ => none

theorem uRound_wf : uRound.WF where
  created_added := by
    rintro id ⟨⟨n', h⟩, hno⟩
    exact (hno n' h).elim
  added_touched := by simp [uRound]
  recanon_touched := by
    rintro id ⟨n, n', hn, hn', hne⟩
    simp [uRound] at hn hn'
    rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  subsumed_touched := by simp [uRound]
  absorbed_delta := by
    intro h
    simp [uRound] at h
  no_split := by
    intro id id' h
    simp [uRound] at h
    subst h
    rfl
  children_canon := by
    simp [uRound, Graph.ChildrenCanon, Children.Canon]
  find_idem := by
    intro id
    by_cases h : id = 1 <;> simp [uRound, h]
  dedup := by
    intro id₁ id₂ n h₁ h₂
    simp [uRound] at h₁ h₂
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h₂ with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all

/-- The untracked counter-model: scanning atoms only, the match is new,
and no scanning atom's node is touched. -/
theorem delta_incomplete_untracked :
    ∃ (R : Round) (atoms : List QAtom) (σ' : Binding),
      R.WF ∧ R.tracking = false ∧ (∀ q ∈ atoms, QSat R.after σ' q) ∧
      ¬ (∀ q ∈ atoms, QSat R.before σ' q) ∧
      ∀ a : RAtom, QAtom.scan a ∈ atoms →
        ∀ id, σ'.node a.node = some id → R.isNew id = false := by
  refine ⟨uRound, uAtoms, uσ, uRound_wf, rfl, ?_, ?_, ?_⟩
  · intro q hq
    simp [uAtoms] at hq
    rcases hq with rfl | rfl
    · refine ⟨1, ⟨3, .tuple [0]⟩, by simp [uσ], by simp [uRound], by simp [uσ, uRound], rfl, ?_⟩
      show MatchN _ (.plain 3 ([12].map .var)) _ _
      exact matchN_plain_vars.2 ⟨[0], rfl, List.Forall₂.cons (by simp [uσ]) List.Forall₂.nil⟩
    · refine ⟨3, ⟨2, .tuple [2]⟩, by simp [uσ], by simp [uRound], by simp [uσ, uRound], rfl, ?_⟩
      show MatchN _ (.plain 2 ([10].map .var)) _ _
      exact matchN_plain_vars.2 ⟨[2], rfl, List.Forall₂.cons (by simp [uσ]) List.Forall₂.nil⟩
  · intro h
    have := h (.scan ⟨10, 3, .plain [12]⟩) (by simp [uAtoms])
    obtain ⟨id, n, hid, hmem, hcls, -, -⟩ := this
    simp [uσ] at hid
    subst hid
    simp [uσ, uRound] at hcls
  · intro a ha id hid
    simp [uAtoms] at ha
    rcases ha with rfl | rfl <;> simp [uσ] at hid <;> subst hid <;> simp [Round.isNew, uRound]

end Semper.EMatch
