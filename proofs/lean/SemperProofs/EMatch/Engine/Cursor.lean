import SemperProofs.EMatch.Ref

/-!
# The cursor matcher's decomposition frames (fidelity: `MatchIterator`)

`run_query_iter` (`egraph/src/ematch.rs`) drives a stack-based matcher, `MatchIterator`,
whose AC and ACI decompositions are resumable frames (`FrameKind::ACDecompose`,
`FrameKind::ACIDecompose`). A frame holds the residual entries of the node, one entry
index per element (`ri_at`), one flag per element saying whether its scan bound the
element variable (`bound`), and the position `ei` of the search. The search is a
depth-first walk over the entries in index order: `ac_find_first` moves forward through
the elements, taking for each the first entry from `ri_at[ei]` its scan accepts
(`ac_scan`), and on a failure undoes the previous element (`ac_undo`), advances its index
and resumes there; `ac_advance`, called by `backtrack` after a yield, undoes the last
element, advances its index and runs `ac_find_first` from it. The ACI twins
(`aci_find_first`, `aci_scan`, `aci_undo`, `aci_advance`) differ in the entry bookkeeping
only: a `used` bit per entry in place of a count.

This file transcribes the frame as a state machine over a generic entry store, proves
that its loops terminate (Theorem A, `findLoop_terminates`, `advance_terminates`) by the
measure `pos`, which every step increases and which the entry indices bound, and that the
sequence of states the frame yields, from the first search through repeated advances to
exhaustion, is the enumeration `enum` in entry order (Theorem B, `drive_eq_enum`). The AC
instance (`acOps`) and the ACI instance (`aciOps`) then connect `enum` to the recursive
executor's decompositions `decomposeAC` and `decomposeACI` (`EMatch/Ref.lean`):
`acFrame_eq_decomposeAC` and `aciFrame_eq_decomposeACI` say the frame's yields, with the
rest pushed and the exact check applied, are the executor's list of bindings, element for
element, and `decomposeAC_nodup`, `decomposeACI_nodup` say that list has no duplicates.

The resume index is the point of the termination proof. Before commit `4e267030`,
`ac_find_first` scanned every element but the first from entry 0, so after a backward
move the element re-took the entry just undone: `findStep false` is that version, and
`preFix_cycles` exhibits a two-state cycle on which `findLoop false` returns for no fuel.
The fixed version scans from `ri_at[ei]`, which the backward move has advanced, and
`findStep_pos_lt` shows the measure increases on every move.

`ac_advance` before this change completed the later elements greedily and undid the moved
element twice; `cursor_shapes.rs`, `decompositions_with_a_bound_element`, is the failing
shape. The transcription below is of the fixed engine, where `ac_advance` resumes
through `ac_find_first`.
-/

namespace Semper.EMatch.Cursor

/-! ## The generic frame

The entry store `α` is the frame's mutable data other than the indices: for AC, the
environment, the residual counts and the `bound` flags; for ACI, the environment, the
`used` bits and the `bound` flags. `accept a e ri` says element `e` can take entry `ri`
in store `a`, `apply a e ri` is the store after it does (`ac_scan`'s body at a hit), and
`undo a e ri` restores the store (`ac_undo`). -/

structure Ops (α : Type) where
  /-- `elems.len()`. -/
  n : Nat
  /-- `residual.len()`. -/
  len : Nat
  accept : α → Nat → Nat → Bool
  apply : α → Nat → Nat → α
  undo : α → Nat → Nat → α

/-- The frame's search state: the store, `ri_at` and `ei`. -/
structure State (α : Type) where
  a : α
  riAt : List Nat
  ei : Nat

variable {α : Type} (ops : Ops α)

namespace Ops

/-- The loop `for ri in start..residual.len()` of `ac_scan` and `aci_scan`: the first entry
from `start` the element accepts, with the store after taking it. `k` is the number of
entries left to look at, `len - start`. -/
def scanFrom : Nat → α → Nat → Nat → Option (Nat × α)
  | 0, _, _, _ => none
  | k + 1, a, e, start =>
      if ops.accept a e start then some (start, ops.apply a e start)
      else scanFrom k a e (start + 1)

/-- `ac_scan(elems, residual, ei, start, bound)`. -/
def scan (a : α) (e start : Nat) : Option (Nat × α) :=
  scanFrom ops (ops.len - start) a e start

/-- One iteration of the `while ei < elems.len()` loop of `ac_find_first`. `fixed` selects
the scan's start: the fixed engine starts at `ri_at[ei]`; the engine before commit
`4e267030` started there for the element the search was entered at (`from`) and at 0 for
every other. -/
inductive Step (α : Type) where
  | cont (s : State α)
  | done (ok : Bool) (s : State α)

def findStep (fixed : Bool) (from_ : Nat) (s : State α) : Step α :=
  if s.ei < ops.n then
    -- `let start = ri_at[ei];` (before the fix: `if ei == from { ri_at[ei] } else { 0 }`)
    let start := if fixed || s.ei = from_ then s.riAt.getD s.ei 0 else 0
    match ops.scan s.a s.ei start with
    | some (ri, a') =>
        -- `ri_at[ei] = ri; ei += 1; if ei < elems.len() { ri_at[ei] = 0; }`
        -- (`List.set` past the end is the identity, as the guard makes the store.)
        .cont ⟨a', (s.riAt.set s.ei ri).set (s.ei + 1) 0, s.ei + 1⟩
    | none =>
        -- `ri_at[ei] = 0; if ei == 0 { return false; }`
        let riAt := s.riAt.set s.ei 0
        if s.ei = 0 then .done false ⟨s.a, riAt, 0⟩
        else
          -- `ei -= 1; self.ac_undo(elems, residual, ei, ri_at[ei], bound); ri_at[ei] += 1;`
          let e := s.ei - 1
          let r := riAt.getD e 0
          .cont ⟨ops.undo s.a e r, riAt.set e (r + 1), e⟩
  else .done true s

/-- The loop of `ac_find_first`, with fuel: `none` when the fuel runs out. -/
def findLoop (fixed : Bool) (from_ : Nat) : Nat → State α → Option (Bool × State α)
  | 0, _ => none
  | k + 1, s =>
      match ops.findStep fixed from_ s with
      | .done ok s' => some (ok, s')
      | .cont s' => findLoop fixed from_ k s'

/-- The fuel `findLoop` is given: more than the measure `pos` can take. -/
def fuel : Nat := (ops.len + 1) ^ ops.n * (ops.n + 1) + 1

/-- `ac_find_first(elems, residual, ri_at, bound, from)` of the fixed engine: the loop runs
to its end (Theorem A), and `none` stands for the fuel running out. -/
def findFirst (from_ : Nat) (s : State α) : Option (Bool × State α) :=
  ops.findLoop true from_ ops.fuel s

/-- The first half of `ac_advance`: undo the last element and advance its index. -/
def postYield (s : State α) : State α :=
  let e := ops.n - 1
  let r := s.riAt.getD e 0
  ⟨ops.undo s.a e r, s.riAt.set e (r + 1), e⟩

/-- `ac_advance(elems, residual, ri_at, bound, ei)`: from a complete assignment
(`ei == elems.len()`), undo the last element, advance its index and resume the search
from it; `*ei = 0` on exhaustion. -/
def advance (s : State α) : Option (Bool × State α) :=
  if ops.n = 0 ∨ s.ei ≠ ops.n then some (false, s)
  else
    match ops.findFirst (ops.n - 1) (ops.postYield s) with
    | some (true, s') => some (true, s')
    | some (false, s') => some (false, { s' with ei := 0 })
    | none => none

/-- The states a frame yields: the first search, then one `advance` per yield, until the
search fails. `k` bounds the number of yields. -/
def drive : Nat → State α → List α
  | 0, _ => []
  | k + 1, s =>
      match ops.findFirst 0 s with
      | some (true, s') => s'.a :: drive k (ops.postYield s')
      | _ => []

/-- The frame's initial state: `ri_at = vec![0; n]`, `ei = 0`. -/
def init (a₀ : α) : State α := ⟨a₀, List.replicate ops.n 0, 0⟩

/-! ## The measure -/

/-- The entry indices as one number in base `len + 1`, most significant first. -/
def code (B : Nat) (l : List Nat) : Nat := l.foldl (fun acc r => acc * B + r) 0

/-- The measure: every move of the search increases it. -/
def pos (s : State α) : Nat := code (ops.len + 1) s.riAt * (ops.n + 1) + s.ei

/-- The index invariant: `ri_at` has one entry per element, each at most `len` (a scan
result is below `len`, an advanced index at most `len`), `ei` is at most `n`, and the
entries past `ei` are 0 (the forward move resets them). -/
structure IdxInv (s : State α) : Prop where
  length : s.riAt.length = ops.n
  le : ∀ r ∈ s.riAt, r ≤ ops.len
  lt : ∀ j, j < s.ei → s.riAt.getD j 0 < ops.len
  ei_le : s.ei ≤ ops.n
  zero : ∀ j, s.ei < j → s.riAt.getD j 0 = 0

theorem foldl_code (B : Nat) (l : List Nat) :
    ∀ c, l.foldl (fun acc r => acc * B + r) c =
      c * B ^ l.length + l.foldl (fun acc r => acc * B + r) 0 := by
  induction l with
  | nil => intro c; simp
  | cons r l ih =>
      intro c
      simp only [List.foldl_cons, List.length_cons, pow_succ]
      rw [ih (c * B + r), ih (0 * B + r)]
      ring

theorem code_append (B : Nat) (l₁ l₂ : List Nat) :
    code B (l₁ ++ l₂) = code B l₁ * B ^ l₂.length + code B l₂ := by
  unfold code
  rw [List.foldl_append]
  exact foldl_code B l₂ _

theorem code_cons (B r : Nat) (l : List Nat) : code B (r :: l) = r * B ^ l.length + code B l := by
  unfold code
  simp only [List.foldl_cons]
  rw [foldl_code B l (0 * B + r)]
  ring

theorem code_lt (B : Nat) (l : List Nat) (h : ∀ r ∈ l, r < B) : code B l < B ^ l.length := by
  induction l with
  | nil => simp [code]
  | cons r l ih =>
      have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hr := h r (List.mem_cons_self ..)
      rw [code_cons, List.length_cons, pow_succ]
      calc r * B ^ l.length + code B l < r * B ^ l.length + B ^ l.length := by omega
        _ = (r + 1) * B ^ l.length := by ring
        _ ≤ B * B ^ l.length := Nat.mul_le_mul_right _ hr
        _ = B ^ l.length * B := by ring

theorem code_zeros (B k : Nat) : code B (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have := code_append B [0] (List.replicate k 0)
      simp only [List.singleton_append, ← List.replicate_succ] at this
      rw [this, ih]; simp [code]

/-- Advancing one index and zeroing the later ones increases the code, when the later
indices are below the base. -/
theorem code_lt_advance (B : Nat) (l₁ l₂ l₂' : List Nat) (r r' : Nat) (hr : r < r')
    (hl : l₂'.length = l₂.length) (h : ∀ x ∈ l₂, x < B) :
    code B (l₁ ++ r :: l₂) < code B (l₁ ++ r' :: l₂') := by
  rw [code_append, code_append, code_cons, code_cons]
  simp only [List.length_cons, hl]
  have := code_lt B l₂ h
  calc code B l₁ * B ^ (l₂.length + 1) + (r * B ^ l₂.length + code B l₂)
      < code B l₁ * B ^ (l₂.length + 1) + (r + 1) * B ^ l₂.length := by
        rw [add_mul, one_mul]; omega
    _ ≤ code B l₁ * B ^ (l₂.length + 1) + r' * B ^ l₂.length :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _
    _ ≤ code B l₁ * B ^ (l₂.length + 1) + (r' * B ^ l₂.length + code B l₂') := by omega

theorem pos_lt_fuel (s : State α) (h : IdxInv ops s) : ops.pos s < ops.fuel := by
  unfold pos fuel
  have hc := code_lt (ops.len + 1) s.riAt (fun r hr => Nat.lt_succ_of_le (h.le r hr))
  rw [h.length] at hc
  have hei := h.ei_le
  have : code (ops.len + 1) s.riAt * (ops.n + 1) + s.ei
      < (code (ops.len + 1) s.riAt + 1) * (ops.n + 1) := by nlinarith
  calc _ < (code (ops.len + 1) s.riAt + 1) * (ops.n + 1) := this
    _ ≤ (ops.len + 1) ^ ops.n * (ops.n + 1) := Nat.mul_le_mul_right _ hc
    _ < _ := Nat.lt_succ_self _

/-! ### Scan facts -/

theorem scanFrom_some {k : Nat} {a a' : α} {e start ri : Nat}
    (h : ops.scanFrom k a e start = some (ri, a')) :
    start ≤ ri ∧ ri < start + k ∧ ops.accept a e ri = true ∧ a' = ops.apply a e ri ∧
      ∀ j, start ≤ j → j < ri → ops.accept a e j = false := by
  induction k generalizing start with
  | zero => simp [scanFrom] at h
  | succ k ih =>
      simp only [scanFrom] at h
      split at h
      · rename_i hacc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨le_rfl, by omega, hacc, rfl, fun j h1 h2 => by omega⟩
      · rename_i hacc
        obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
        refine ⟨by omega, by omega, h3, h4, fun j hj1 hj2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
        · simpa using hacc
        · exact h5 j hlt hj2

theorem scanFrom_none {k : Nat} {a : α} {e start : Nat}
    (h : ops.scanFrom k a e start = none) :
    ∀ j, start ≤ j → j < start + k → ops.accept a e j = false := by
  induction k generalizing start with
  | zero => intro j _ _; omega
  | succ k ih =>
      simp only [scanFrom] at h
      split at h
      · simp at h
      · rename_i hacc
        intro j hj1 hj2
        rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
        · simpa using hacc
        · exact ih h j hlt (by omega)

theorem scan_some {a a' : α} {e start ri : Nat} (h : ops.scan a e start = some (ri, a')) :
    start ≤ ri ∧ ri < ops.len ∧ ops.accept a e ri = true ∧ a' = ops.apply a e ri ∧
      ∀ j, start ≤ j → j < ri → ops.accept a e j = false := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ops.scanFrom_some h
  exact ⟨h1, by omega, h3, h4, h5⟩

theorem scan_none {a : α} {e start : Nat} (h : ops.scan a e start = none) :
    ∀ j, start ≤ j → j < ops.len → ops.accept a e j = false := fun j h1 h2 =>
  ops.scanFrom_none h j h1 (by unfold scan at h; omega)

/-! ### Theorem A: termination -/

theorem getD_set_self (l : List Nat) (i v : Nat) (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]

theorem getD_set_ne (l : List Nat) (i j v : Nat) (hij : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

/-- A list as its prefix, the entry at `i` and the suffix. -/
theorem list_split (l : List Nat) (i : Nat) (hi : i < l.length) :
    l = l.take i ++ l.getD i 0 :: l.drop (i + 1) := by
  have h1 := List.take_append_drop i l
  rw [List.drop_eq_getElem_cons hi] at h1
  rw [List.getD_eq_getElem l 0 hi]
  exact h1.symm

theorem drop_zero_of_inv (s : State α) (h : IdxInv ops s) (i : Nat) (hi : s.ei ≤ i) :
    s.riAt.drop (i + 1) = List.replicate (s.riAt.length - (i + 1)) 0 := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_drop, List.getElem_replicate]
    have := h.zero (i + 1 + j) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hj; omega)] at this
    simpa using this

/-- The fixed search increases the measure on every move and keeps the index invariant. -/
theorem findStep_pos_lt (from_ : Nat) (s s' : State α) (h : IdxInv ops s)
    (hs : ops.findStep true from_ s = .cont s') : ops.pos s < ops.pos s' ∧ IdxInv ops s' := by
  unfold findStep at hs
  split at hs
  · rename_i hlt
    simp only [Bool.true_or, ite_true] at hs
    split at hs
    · rename_i ri a' hscan
      simp only [Step.cont.injEq] at hs
      subst hs
      obtain ⟨h1, h2, _, _, _⟩ := ops.scan_some hscan
      have hlen : s.riAt.length = ops.n := h.length
      have hei : s.ei < s.riAt.length := by omega
      have hinv : IdxInv ops ⟨a', (s.riAt.set s.ei ri).set (s.ei + 1) 0, s.ei + 1⟩ := by
        refine ⟨by simp [hlen], ?_, ?_, by dsimp only; omega, ?_⟩
        · intro r hr
          dsimp only at hr
          rcases List.mem_or_eq_of_mem_set hr with hr | rfl
          · rcases List.mem_or_eq_of_mem_set hr with hr | rfl
            · exact h.le r hr
            · omega
          · omega
        · intro j hj
          dsimp only at hj ⊢
          rw [getD_set_ne _ _ _ _ (by omega)]
          by_cases hje : j = s.ei
          · subst hje; rw [getD_set_self _ _ _ hei]; exact h2
          · rw [getD_set_ne _ _ _ _ (Ne.symm hje)]
            exact h.lt j (by omega)
        · intro j hj
          dsimp only at hj ⊢
          rw [getD_set_ne _ _ _ _ (by omega), getD_set_ne _ _ _ _ (by omega)]
          exact h.zero j (by omega)
      refine ⟨?_, hinv⟩
      unfold pos
      simp only
      rcases Nat.eq_or_lt_of_le h1 with rfl | hgt
      · -- the index is unchanged, the position moves on
        have : (s.riAt.set s.ei (s.riAt.getD s.ei 0)).set (s.ei + 1) 0 = s.riAt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hei]
          simp only [Option.getD_some, List.set_getElem_self]
          by_cases hj : s.ei + 1 < s.riAt.length
          · have := h.zero (s.ei + 1) (by omega)
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at this
            simp only [Option.getD_some] at this
            rw [← this, List.set_getElem_self]
          · exact List.set_eq_of_length_le (by omega)
        rw [this]; omega
      · -- the index advances: the code increases
        have hsplit := list_split s.riAt s.ei hei
        have hdrop := ops.drop_zero_of_inv s h s.ei le_rfl
        have hset : (s.riAt.set s.ei ri).set (s.ei + 1) 0 =
            s.riAt.take s.ei ++ ri :: List.replicate (s.riAt.length - (s.ei + 1)) 0 := by
          rw [← hdrop]
          conv_lhs => rw [hsplit]
          rw [List.set_append_right _ _ (by simp [min_eq_left hei.le]), List.set_append_right _ _ (by simp [min_eq_left hei.le])]
          simp only [List.length_take, min_eq_left hei.le, Nat.sub_self, List.set_cons_zero, Nat.add_sub_cancel_left,
            List.set_cons_succ]
          congr 2
          rw [hdrop]
          rcases hk : s.riAt.length - (s.ei + 1) with _ | k
          · rfl
          · simp [List.replicate_succ]
        have hlt' : code (ops.len + 1) s.riAt < code (ops.len + 1) ((s.riAt.set s.ei ri).set (s.ei + 1) 0) := by
          rw [hset]
          conv_lhs => rw [hsplit, hdrop]
          exact code_lt_advance _ _ _ _ _ _ hgt (by simp) (by simp)
        nlinarith
    · rename_i hscan
      split at hs
      · simp at hs
      · rename_i hne
        simp only [Step.cont.injEq] at hs
        subst hs
        have hlen : s.riAt.length = ops.n := h.length
        have hei : s.ei < s.riAt.length := by omega
        have hei1 : s.ei - 1 < s.riAt.length := by omega
        set e := s.ei - 1 with he
        have hr : (s.riAt.set s.ei 0).getD e 0 = s.riAt.getD e 0 := getD_set_ne _ _ _ _ (by omega)
        -- the index advanced is a scan result, so below `len`
        have hrlt : s.riAt.getD e 0 < ops.len := h.lt e (by omega)
        have hinv : IdxInv ops ⟨ops.undo s.a e ((s.riAt.set s.ei 0).getD e 0),
            (s.riAt.set s.ei 0).set e ((s.riAt.set s.ei 0).getD e 0 + 1), e⟩ := by
          refine ⟨by simp [hlen], ?_, ?_, by dsimp only; omega, ?_⟩
          · intro r hr'
            dsimp only at hr'
            rcases List.mem_or_eq_of_mem_set hr' with hr' | rfl
            · rcases List.mem_or_eq_of_mem_set hr' with hr' | rfl
              · exact h.le r hr'
              · omega
            · rw [hr]; omega
          · intro j hj
            dsimp only at hj ⊢
            rw [getD_set_ne _ _ _ _ (by omega), getD_set_ne _ _ _ _ (by omega)]
            exact h.lt j (by omega)
          · intro j hj
            dsimp only at hj ⊢
            rw [getD_set_ne _ _ _ _ (by omega)]
            by_cases hje : j = s.ei
            · subst hje; exact getD_set_self _ _ _ hei
            · rw [getD_set_ne _ _ _ _ (Ne.symm hje)]
              exact h.zero j (by omega)
        refine ⟨?_, hinv⟩
        unfold pos
        dsimp only
        rw [hr]
        -- `riAt = l₁ ++ r :: x :: zeros` with `|l₁| = e`; the new list is `l₁ ++ (r + 1) :: 0 :: zeros`
        have hdrop := ops.drop_zero_of_inv s h s.ei le_rfl
        have hdrop1 : s.riAt.drop (e + 1) =
            s.riAt.getD s.ei 0 :: List.replicate (s.riAt.length - (s.ei + 1)) 0 := by
          rw [← hdrop, show e + 1 = s.ei by omega, List.drop_eq_getElem_cons hei, List.getD_eq_getElem s.riAt 0 hei]
        obtain ⟨l₁, hl₁, hsp⟩ : ∃ l₁ : List Nat, l₁.length = e ∧ s.riAt = l₁ ++ s.riAt.getD e 0 ::
            s.riAt.getD s.ei 0 :: List.replicate (s.riAt.length - (s.ei + 1)) 0 :=
          ⟨s.riAt.take e, by simp [min_eq_left hei1.le], by rw [← hdrop1]; exact list_split s.riAt e hei1⟩
        set r := s.riAt.getD e 0 with hr0
        set x := s.riAt.getD s.ei 0 with hx0
        set Z := List.replicate (s.riAt.length - (s.ei + 1)) 0 with hZ
        have hset : (s.riAt.set s.ei 0).set e (r + 1) = l₁ ++ (r + 1) :: 0 :: Z := by
          rw [hsp, List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega)]
          simp only [hl₁, show s.ei - e = 1 by omega, Nat.sub_self, List.set_cons_succ, List.set_cons_zero]
        have hlt' : code (ops.len + 1) s.riAt < code (ops.len + 1) ((s.riAt.set s.ei 0).set e (r + 1)) := by
          rw [hset, hsp]
          refine code_lt_advance _ _ _ _ _ _ (Nat.lt_succ_self _) (by simp) ?_
          intro y hy
          simp only [List.mem_cons, hZ, List.mem_replicate] at hy
          rcases hy with rfl | ⟨_, rfl⟩
          · have := h.le x (by rw [hsp]; simp); omega
          · omega
        have hn : s.ei ≤ ops.n := h.ei_le
        nlinarith
  · simp at hs

/-- Theorem A, the search: on an invariant state the fixed loop ends within its fuel. -/
theorem findLoop_terminates (from_ : Nat) (s : State α) (h : IdxInv ops s) :
    ∀ k, ops.fuel ≤ ops.pos s + k → ∃ r, ops.findLoop true from_ k s = some r := by
  intro k
  induction k generalizing s with
  | zero => intro hk; have := ops.pos_lt_fuel s h; omega
  | succ k ih =>
      intro hk
      cases hs : ops.findStep true from_ s with
      | cont s' =>
          obtain ⟨hpos, hinv⟩ := ops.findStep_pos_lt from_ s s' h hs
          simp only [findLoop, hs]
          exact ih s' hinv (by omega)
      | done ok s' => simp [findLoop, hs]

theorem findFirst_terminates (from_ : Nat) (s : State α) (h : IdxInv ops s) :
    ∃ r, ops.findFirst from_ s = some r :=
  ops.findLoop_terminates from_ s h ops.fuel (by omega)

theorem postYield_inv (s : State α) (h : IdxInv ops s) (hn : 0 < ops.n) (hei : s.ei = ops.n) :
    IdxInv ops (ops.postYield s) := by
  have hlen := h.length
  have he : ops.n - 1 < s.riAt.length := by omega
  have hlt := h.lt (ops.n - 1) (by omega)
  refine ⟨by simp [postYield, hlen], ?_, ?_, by simp [postYield], ?_⟩
  · intro r hr
    simp only [postYield] at hr
    rcases List.mem_or_eq_of_mem_set hr with hr | rfl
    · exact h.le r hr
    · omega
  · intro j hj
    simp only [postYield] at hj ⊢
    rw [getD_set_ne _ (ops.n - 1) j _ (Nat.ne_of_gt hj)]
    exact h.lt j (by omega)
  · intro j hj
    simp only [postYield] at hj ⊢
    rw [getD_set_ne _ (ops.n - 1) j _ (Nat.ne_of_lt hj)]
    rcases Nat.lt_or_ge ops.n j with hj' | hj'
    · exact h.zero j (by omega)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- Theorem A, the advance: `ac_advance` returns on every complete assignment. -/
theorem advance_terminates (s : State α) (h : IdxInv ops s) : ∃ r, ops.advance s = some r := by
  unfold advance
  split
  · exact ⟨_, rfl⟩
  · rename_i hc
    push Not at hc
    obtain ⟨⟨ok, s'⟩, hr⟩ := ops.findFirst_terminates (ops.n - 1) (ops.postYield s)
      (ops.postYield_inv s h (by omega) hc.2)
    rw [hr]
    cases ok <;> exact ⟨_, rfl⟩

theorem init_inv (a₀ : α) : IdxInv ops (ops.init a₀) :=
  ⟨by simp [init], fun r hr => by simp [init] at hr; omega, fun j hj => by simp [init] at hj,
    by simp [init], fun j _ => by simp [init]⟩


/-! ### Theorem B: the yields are the enumeration in entry order

`rest e a start` lists the complete assignments of elements `e..n-1` from store `a`
with element `e` taking an entry from `start` on, in entry order; `enum e a` is
`rest e a 0`, the recursive executor's enumeration. `remaining a₀ s` is what the frame
has left to yield from state `s`: the completions from the position, then, for each
element below it, the completions from the entry after the one it holds. The frame's
invariant `Inv` says the store is the replay of the indices below `ei` from the initial
store, and every move preserves `remaining` (`findStep_cont_remaining`). -/

/-- `k` is `n - e`. -/
def restF : Nat → Nat → α → Nat → List α
  | 0, _, a, _ => [a]
  | k + 1, e, a, start =>
      (List.range' start (ops.len - start)).flatMap fun ri =>
        if ops.accept a e ri then restF k (e + 1) (ops.apply a e ri) 0 else []

def rest (e : Nat) (a : α) (start : Nat) : List α := ops.restF (ops.n - e) e a start

/-- The complete assignments from store `a` at element `e`, in entry order. -/
def enum (e : Nat) (a : α) : List α := ops.rest e a 0

theorem rest_n (a : α) (start : Nat) : ops.rest ops.n a start = [a] := by
  simp [rest, restF]

theorem rest_lt {e : Nat} (he : e < ops.n) (a : α) (start : Nat) :
    ops.rest e a start = (List.range' start (ops.len - start)).flatMap fun ri =>
      if ops.accept a e ri then ops.rest (e + 1) (ops.apply a e ri) 0 else [] := by
  unfold rest
  obtain ⟨k, hk⟩ : ∃ k, ops.n - e = k + 1 := ⟨ops.n - e - 1, by omega⟩
  have hk' : ops.n - (e + 1) = k := by omega
  rw [hk, hk', restF]

theorem range'_split (start ri len : Nat) (h1 : start ≤ ri) (h2 : ri < len) :
    List.range' start (len - start) = List.range' start (ri - start) ++ ri :: List.range' (ri + 1) (len - (ri + 1)) := by
  have h4 : len - start = (ri - start) + (len - (ri + 1) + 1) := by omega
  rw [h4, ← List.range'_append_1, List.range'_succ, show start + (ri - start) = ri by omega]

/-- The completions from `start` split at the first entry the element accepts. -/
theorem rest_scan_some {e : Nat} (he : e < ops.n) {a a' : α} {start ri : Nat}
    (h : ops.scan a e start = some (ri, a')) :
    ops.rest e a start = ops.rest (e + 1) a' 0 ++ ops.rest e a (ri + 1) := by
  obtain ⟨h1, h2, hacc, rfl, hnone⟩ := ops.scan_some h
  rw [ops.rest_lt he, ops.rest_lt he, range'_split start ri ops.len h1 h2, List.flatMap_append,
    List.flatMap_cons, hacc]
  have : (List.range' start (ri - start)).flatMap (fun ri =>
      if ops.accept a e ri = true then ops.rest (e + 1) (ops.apply a e ri) 0 else []) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro j hj
    rw [List.mem_range'_1] at hj
    rw [hnone j hj.1 (by omega)]; rfl
  rw [this]; rfl

theorem rest_scan_none {e : Nat} (he : e < ops.n) {a : α} {start : Nat}
    (h : ops.scan a e start = none) : ops.rest e a start = [] := by
  rw [ops.rest_lt he, List.flatMap_eq_nil_iff]
  intro j hj
  rw [List.mem_range'_1] at hj
  rw [ops.scan_none h j hj.1 (by omega)]; rfl

/-- The store after elements `< e` took the entries `riAt` names, when each accepted
its entry. -/
def replay (a₀ : α) (riAt : List Nat) : Nat → Option α
  | 0 => some a₀
  | e + 1 => (replay a₀ riAt e).bind fun a =>
      if ops.accept a e (riAt.getD e 0) then some (ops.apply a e (riAt.getD e 0)) else none

def restOpt (o : Option α) (e start : Nat) : List α :=
  match o with
  | some a => ops.rest e a start
  | none => []

@[simp] theorem restOpt_some (a : α) (e start : Nat) : ops.restOpt (some a) e start = ops.rest e a start := rfl
@[simp] theorem restOpt_none (e start : Nat) : ops.restOpt none e start = [] := rfl

/-- The completions left for the elements below `e`: for each, from the entry after
the one it holds, deepest first. -/
def stackRest (a₀ : α) (riAt : List Nat) : Nat → List α
  | 0 => []
  | e + 1 => ops.restOpt (ops.replay a₀ riAt e) e (riAt.getD e 0 + 1) ++ stackRest a₀ riAt e

/-- What the frame has left to yield from `s`. -/
def remaining (a₀ : α) (s : State α) : List α :=
  ops.restOpt (ops.replay a₀ s.riAt s.ei) s.ei (s.riAt.getD s.ei 0) ++ ops.stackRest a₀ s.riAt s.ei

/-- The store laws the correctness proof needs: on a good store, `undo` reverses `apply`
and `apply` keeps the store good. `good e a` is the AC frame's reachability condition
(the `bound` flags from `e` on are clear, a multiplicity variable is bound only by an
earlier element). -/
structure Laws (good : Nat → α → Prop) : Prop where
  undo_apply : ∀ a e ri, good e a → ops.accept a e ri = true → ops.undo (ops.apply a e ri) e ri = a
  good_apply : ∀ a e ri, good e a → ops.accept a e ri = true → good (e + 1) (ops.apply a e ri)

structure Inv (good : Nat → α → Prop) (a₀ : α) (s : State α) : Prop extends IdxInv ops s where
  replay : ops.replay a₀ s.riAt s.ei = some s.a
  good₀ : good 0 a₀

theorem replay_congr (a₀ : α) {riAt riAt' : List Nat} (e : Nat)
    (h : ∀ j, j < e → riAt.getD j 0 = riAt'.getD j 0) :
    ops.replay a₀ riAt e = ops.replay a₀ riAt' e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      simp only [replay]
      rw [ih (fun j hj => h j (by omega)), h e (by omega)]

theorem stackRest_congr (a₀ : α) {riAt riAt' : List Nat} (e : Nat)
    (h : ∀ j, j < e → riAt.getD j 0 = riAt'.getD j 0) :
    ops.stackRest a₀ riAt e = ops.stackRest a₀ riAt' e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      simp only [stackRest]
      rw [ih (fun j hj => h j (by omega)), ops.replay_congr a₀ e (fun j hj => h j (by omega)),
        h e (by omega)]

theorem replay_succ {a₀ : α} {riAt : List Nat} {e : Nat} {a' : α}
    (h : ops.replay a₀ riAt (e + 1) = some a') :
    ∃ a, ops.replay a₀ riAt e = some a ∧ ops.accept a e (riAt.getD e 0) = true ∧
      a' = ops.apply a e (riAt.getD e 0) := by
  simp only [replay] at h
  rcases hr : ops.replay a₀ riAt e with _ | a
  · rw [hr] at h; simp at h
  · rw [hr] at h
    simp only [Option.bind_some] at h
    split at h
    · simp only [Option.some.injEq] at h; exact ⟨a, rfl, by assumption, h.symm⟩
    · simp at h

theorem replay_good {good : Nat → α → Prop} (hl : ops.Laws good) {a₀ : α} (h₀ : good 0 a₀)
    (riAt : List Nat) : ∀ e a, ops.replay a₀ riAt e = some a → good e a := by
  intro e
  induction e with
  | zero => intro a h; simp only [replay, Option.some.injEq] at h; subst h; exact h₀
  | succ e ih =>
      intro a' h
      obtain ⟨a, hr, hacc, rfl⟩ := ops.replay_succ h
      exact hl.good_apply a e _ (ih a hr) hacc

theorem getD_set_zero (l : List Nat) (i : Nat) : (l.set i 0).getD i 0 = 0 := by
  by_cases hi : i < l.length
  · exact getD_set_self l i 0 hi
  · rw [List.set_eq_of_length_le (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega)]; rfl

/-- A forward or backward move keeps the invariant and what is left to yield. -/
theorem findStep_cont_remaining {good : Nat → α → Prop} (hl : ops.Laws good) {a₀ : α}
    (from_ : Nat) {s s' : State α} (h : ops.Inv good a₀ s)
    (hs : ops.findStep true from_ s = .cont s') :
    ops.Inv good a₀ s' ∧ ops.remaining a₀ s' = ops.remaining a₀ s := by
  have hidx := ops.findStep_pos_lt from_ s s' h.toIdxInv hs
  unfold findStep at hs
  split at hs
  · rename_i hlt
    simp only [Bool.true_or, ite_true] at hs
    split at hs
    · rename_i ri a' hscan
      simp only [Step.cont.injEq] at hs
      subst hs
      obtain ⟨h1, h2, hacc, rfl, _⟩ := ops.scan_some hscan
      have hei : s.ei < s.riAt.length := by rw [h.length]; exact hlt
      have hcongr : ∀ j, j < s.ei → s.riAt.getD j 0 = ((s.riAt.set s.ei ri).set (s.ei + 1) 0).getD j 0 := by
        intro j hj
        rw [getD_set_ne _ _ _ _ (by omega), getD_set_ne _ _ _ _ (by omega)]
      have hri : ((s.riAt.set s.ei ri).set (s.ei + 1) 0).getD s.ei 0 = ri := by
        rw [getD_set_ne _ _ _ _ (by omega), getD_set_self _ _ _ hei]
      have hreplay : ops.replay a₀ ((s.riAt.set s.ei ri).set (s.ei + 1) 0) (s.ei + 1) =
          some (ops.apply s.a s.ei ri) := by
        simp only [replay]
        rw [← ops.replay_congr a₀ s.ei hcongr, h.replay, hri]
        simp [hacc]
      refine ⟨⟨hidx.2, hreplay, h.good₀⟩, ?_⟩
      simp only [remaining, hreplay, h.replay, restOpt_some, stackRest, getD_set_zero]
      rw [← ops.replay_congr a₀ s.ei hcongr, h.replay, restOpt_some, ← ops.stackRest_congr a₀ s.ei hcongr,
        hri, ops.rest_scan_some hlt hscan, List.append_assoc]
    · rename_i hscan
      split at hs
      · simp at hs
      · rename_i hne
        simp only [Step.cont.injEq] at hs
        subst hs
        obtain ⟨e, he⟩ : ∃ e, s.ei = e + 1 := ⟨s.ei - 1, by omega⟩
        have hei : s.ei < s.riAt.length := by rw [h.length]; exact hlt
        obtain ⟨a, hr, hacc, ha⟩ := ops.replay_succ (he ▸ h.replay)
        have hgood := ops.replay_good hl h.good₀ s.riAt e a hr
        have hundo : ops.undo s.a e (s.riAt.getD e 0) = a := by
          rw [ha]; exact hl.undo_apply a e _ hgood hacc
        simp only [he, Nat.add_sub_cancel]
        have hr' : (s.riAt.set (e + 1) 0).getD e 0 = s.riAt.getD e 0 := getD_set_ne _ _ _ _ (by omega)
        rw [hr', hundo]
        have hcongr : ∀ j, j < e → s.riAt.getD j 0 =
            ((s.riAt.set (e + 1) 0).set e (s.riAt.getD e 0 + 1)).getD j 0 := by
          intro j hj
          rw [getD_set_ne _ _ _ _ (by omega), getD_set_ne _ _ _ _ (by omega)]
        have hre : ((s.riAt.set (e + 1) 0).set e (s.riAt.getD e 0 + 1)).getD e 0 = s.riAt.getD e 0 + 1 :=
          getD_set_self _ _ _ (by simp; omega)
        have hreplay : ops.replay a₀ ((s.riAt.set (e + 1) 0).set e (s.riAt.getD e 0 + 1)) e = some a := by
          rw [← ops.replay_congr a₀ e hcongr]; exact hr
        have hidx' := hidx.2
        simp only [he, Nat.add_sub_cancel, hr', hundo] at hidx'
        refine ⟨⟨hidx', hreplay, h.good₀⟩, ?_⟩
        have hrep := h.replay
        rw [he] at hrep hlt hscan
        simp only [remaining, hreplay, restOpt_some, hre, he, hrep, stackRest, hr]
        rw [← ops.stackRest_congr a₀ e hcongr, ops.rest_scan_none hlt hscan, List.nil_append]
  · simp at hs

/-- A failed search leaves nothing to yield. -/
theorem findStep_done_false_remaining {good : Nat → α → Prop} {a₀ : α}
    (from_ : Nat) {s s' : State α} (h : ops.Inv good a₀ s)
    (hs : ops.findStep true from_ s = .done false s') : ops.remaining a₀ s = [] := by
  unfold findStep at hs
  split at hs
  · rename_i hlt
    simp only [Bool.true_or, ite_true] at hs
    split at hs
    · simp at hs
    · rename_i hscan
      split at hs
      · rename_i h0
        have hrep := h.replay
        rw [h0] at hrep hscan hlt
        simp only [remaining, h0, hrep, restOpt, stackRest, List.append_nil]
        exact ops.rest_scan_none hlt hscan
      · simp at hs
  · simp at hs

theorem findStep_done_true {from_ : Nat} {s s' : State α}
    (hs : ops.findStep true from_ s = .done true s') : s' = s ∧ ops.n ≤ s.ei := by
  unfold findStep at hs
  split at hs
  · simp only [Bool.true_or, ite_true] at hs
    split at hs
    · simp at hs
    · split at hs <;> simp at hs
  · simp only [Step.done.injEq, true_and] at hs
    exact ⟨hs.symm, by omega⟩

/-- At a complete assignment, the store is the first yield and `postYield` leaves the
rest. -/
theorem remaining_complete {good : Nat → α → Prop} (hl : ops.Laws good) {a₀ : α} {s : State α}
    (h : ops.Inv good a₀ s) (hn : 0 < ops.n) (hei : s.ei = ops.n) :
    ops.remaining a₀ s = s.a :: ops.remaining a₀ (ops.postYield s) ∧
      ops.Inv good a₀ (ops.postYield s) := by
  obtain ⟨e, he⟩ : ∃ e, ops.n = e + 1 := ⟨ops.n - 1, by omega⟩
  have hr := h.replay
  rw [hei, he] at hr
  obtain ⟨a, hra, hacc, ha⟩ := ops.replay_succ hr
  have hgood := ops.replay_good hl h.good₀ s.riAt e a hra
  have hundo : ops.undo s.a e (s.riAt.getD e 0) = a := by
    rw [ha]; exact hl.undo_apply a e _ hgood hacc
  have hlen : e < s.riAt.length := by rw [h.length]; omega
  have hcongr : ∀ j, j < e → s.riAt.getD j 0 = (s.riAt.set e (s.riAt.getD e 0 + 1)).getD j 0 :=
    fun j hj => (getD_set_ne _ _ _ _ (by omega)).symm
  have hreplay : ops.replay a₀ (s.riAt.set e (s.riAt.getD e 0 + 1)) e = some a := by
    rw [← ops.replay_congr a₀ e hcongr]; exact hra
  have hpy : ops.postYield s = ⟨a, s.riAt.set e (s.riAt.getD e 0 + 1), e⟩ := by
    simp only [postYield, he, Nat.add_sub_cancel, hundo]
  refine ⟨?_, ?_⟩
  · rw [hpy]
    have hrn : ops.rest (e + 1) s.a (s.riAt.getD (e + 1) 0) = [s.a] := he ▸ ops.rest_n s.a _
    simp only [remaining, hreplay, restOpt_some, hei, he, hr, hrn, stackRest, hra,
      getD_set_self _ _ _ hlen, List.singleton_append]
    rw [← ops.stackRest_congr a₀ e hcongr]
  · have hidx := ops.postYield_inv s h.toIdxInv hn hei
    rw [hpy] at hidx ⊢
    exact ⟨hidx, hreplay, h.good₀⟩

theorem findLoop_remaining {good : Nat → α → Prop} (hl : ops.Laws good) {a₀ : α} (from_ : Nat) :
    ∀ (k : Nat) (s : State α), ops.Inv good a₀ s →
      ∀ ok s', ops.findLoop true from_ k s = some (ok, s') →
        (ok = true → s'.ei = ops.n ∧ ops.Inv good a₀ s' ∧ ops.remaining a₀ s' = ops.remaining a₀ s) ∧
        (ok = false → ops.remaining a₀ s = []) := by
  intro k
  induction k with
  | zero => intro s _ ok s' h; simp [findLoop] at h
  | succ k ih =>
      intro s h ok s' hk
      cases hs : ops.findStep true from_ s with
      | cont s₁ =>
          simp only [findLoop, hs] at hk
          obtain ⟨hinv, hrem⟩ := ops.findStep_cont_remaining hl from_ h hs
          obtain ⟨h1, h2⟩ := ih s₁ hinv ok s' hk
          exact ⟨fun hok => ⟨(h1 hok).1, (h1 hok).2.1, hrem ▸ (h1 hok).2.2⟩, fun hok => hrem ▸ h2 hok⟩
      | done ok₁ s₁ =>
          simp only [findLoop, hs, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          cases ok₁ with
          | false => exact ⟨fun h => by simp at h, fun _ => ops.findStep_done_false_remaining from_ h hs⟩
          | true =>
              obtain ⟨rfl, hn⟩ := ops.findStep_done_true hs
              exact ⟨fun _ => ⟨le_antisymm h.ei_le hn, h, rfl⟩, fun h => by simp at h⟩

/-- Theorem B, generic: from an invariant state the frame yields what is left, in order. -/
theorem drive_eq_take {good : Nat → α → Prop} (hl : ops.Laws good) {a₀ : α} (hn : 0 < ops.n) :
    ∀ (k : Nat) (s : State α), ops.Inv good a₀ s → ops.drive k s = (ops.remaining a₀ s).take k := by
  intro k
  induction k with
  | zero => intro s _; rfl
  | succ k ih =>
      intro s h
      obtain ⟨⟨ok, s'⟩, hf⟩ := ops.findFirst_terminates 0 s h.toIdxInv
      obtain ⟨h1, h2⟩ := ops.findLoop_remaining hl 0 ops.fuel s h ok s' hf
      simp only [drive, findFirst] at hf ⊢
      rw [hf]
      cases ok with
      | false => rw [h2 rfl]; rfl
      | true =>
          obtain ⟨hei, hinv, hrem⟩ := h1 rfl
          obtain ⟨hc, hinv'⟩ := ops.remaining_complete hl hinv hn hei
          rw [← hrem, hc, List.take_succ_cons]
          show s'.a :: ops.drive k (ops.postYield s') = _
          rw [ih _ hinv']

theorem remaining_init (a₀ : α) : ops.remaining a₀ (ops.init a₀) = ops.enum 0 a₀ := by
  simp [remaining, init, replay, restOpt, stackRest, enum]

theorem init_Inv {good : Nat → α → Prop} {a₀ : α} (h₀ : good 0 a₀) : ops.Inv good a₀ (ops.init a₀) :=
  ⟨ops.init_inv a₀, rfl, h₀⟩

/-- Theorem B, generic: the frame yields the enumeration, element by element; with fuel
for every yield it is the enumeration itself. -/
theorem drive_eq_enum {good : Nat → α → Prop} (hl : ops.Laws good) {a₀ : α} (h₀ : good 0 a₀)
    (hn : 0 < ops.n) (k : Nat) : ops.drive k (ops.init a₀) = (ops.enum 0 a₀).take k := by
  rw [ops.drive_eq_take hl hn k _ (ops.init_Inv h₀), ops.remaining_init]

theorem drive_full {good : Nat → α → Prop} (hl : ops.Laws good) {a₀ : α} (h₀ : good 0 a₀)
    (hn : 0 < ops.n) : ops.drive (ops.enum 0 a₀).length (ops.init a₀) = ops.enum 0 a₀ := by
  rw [ops.drive_eq_enum hl h₀ hn, List.take_length]

end Ops


/-! ## The AC frame (`FrameKind::ACDecompose`)

The store is the environment, the residual `(class, count)` entries and the `bound`
flags. The engine's environment keeps a multiplicity cell at `ZERO` for unbound
(`bound_mult_val`), which the model's `Option` reads as `none`: `set_mult(mv, ZERO)` is
`clearMult`. -/

structure ACStore where
  σ : Binding
  res : List (C × Nat)
  bound : List Bool

/-- `self.env.clear(vid)`. -/
def clearCls (σ : Binding) (x : Var) : Binding := { σ with cls := Function.update σ.cls x none }

/-- `self.env.set_mult(mv, Cfg::M::ZERO)`. -/
def clearMult (σ : Binding) (k : Var) : Binding := { σ with mult := Function.update σ.mult k none }

/-- The default element, never read for an index below `elems.len()`. -/
def defElem : Var × Mult := (0, .exact 1)

/-- Whether an element below `e` carries the multiplicity variable `k`
(`elems[..ei].iter().any(...)` in `ac_undo`). -/
def usesMult (elems : List (Var × Mult)) (e : Nat) (k : Var) : Bool :=
  (elems.take e).any fun p => match p.2 with | .var k' _ _ => k' == k | .exact _ => false

/-- `ac_scan`'s test of one entry: on the bound-repr path `residual[ri].0 == repr &&
mult_matches(...)`, otherwise `mult_matches(mult, avail, bound_mult_val(mult, &self.env))`.
The model's `multMatches` is `mult_matches` with the binding of a multiplicity variable
folded in. An element index past the end accepts nothing (the loop guard `ei < elems.len()`). -/
def acAccept (elems : List (Var × Mult)) (a : ACStore) (e ri : Nat) : Bool :=
  match elems[e]? with
  | none => false
  | some (x, μ) =>
      match a.σ.cls x with
      | some c' => decide ((a.res.getD ri (0, 0)).1 = c') && (multMatches a.σ μ (a.res.getD ri (0, 0)).2).isSome
      | none => (multMatches a.σ μ (a.res.getD ri (0, 0)).2).isSome

/-- `ac_scan`'s body at a hit: on the bound-repr path the variable is left alone and
`bound[ei]` stays `false`; otherwise `self.env.set(vid, repr); bound[ei] = true`. Then
`RMult::Var { var: mv, .. } => self.env.set_mult(*mv, residual[ri].1)` and
`residual[ri].1 = avail.saturating_sub(take)` with `take = avail`. -/
def acApply (elems : List (Var × Mult)) (a : ACStore) (e ri : Nat) : ACStore :=
  let x := (elems.getD e defElem).1
  let μ := (elems.getD e defElem).2
  let c := (a.res.getD ri (0, 0)).1
  let m := (a.res.getD ri (0, 0)).2
  let σ₁ := match a.σ.cls x with
    | some _ => a.σ
    | none => a.σ.setCls x c
  let b := match a.σ.cls x with
    | some _ => false
    | none => true
  let σ₂ := match μ with
    | .exact _ => σ₁
    | .var k _ _ => σ₁.setMult k m
  ⟨σ₂, a.res.set ri (c, 0), a.bound.set e b⟩

/-- `ac_undo(elems, residual, ei, ri, bound)`: `residual[ri].1 += restore`, where
`restore` is the literal of an exact annotation or `env.get_mult(mv)`; `env.clear(vid)` if
`bound[ei]`; `bound[ei] = false`; and `set_mult(mv, ZERO)` unless an earlier element uses
the same multiplicity variable. -/
def acUndo (elems : List (Var × Mult)) (a : ACStore) (e ri : Nat) : ACStore :=
  let x := (elems.getD e defElem).1
  let μ := (elems.getD e defElem).2
  let c := (a.res.getD ri (0, 0)).1
  let m := (a.res.getD ri (0, 0)).2
  let restore := match μ with
    | .exact k => k
    | .var k _ _ => (a.σ.mult k).getD 0
  let σ₁ := if a.bound.getD e false then clearCls a.σ x else a.σ
  let σ₂ := match μ with
    | .exact _ => σ₁
    | .var k _ _ => if usesMult elems e k then σ₁ else clearMult σ₁ k
  ⟨σ₂, a.res.set ri (c, m + restore), a.bound.set e false⟩

/-- The AC frame over `elems`, on a node with `len` residual entries. -/
def acOps (elems : List (Var × Mult)) (len : Nat) : Ops ACStore :=
  ⟨elems.length, len, acAccept elems, acApply elems, acUndo elems⟩

/-- The leaf of the frame: `enter_ac` and `backtrack` push the live entries as the rest
(`residual.iter().filter(|(_, m)| m > zero)`), or require every entry consumed when there
is no rest (`residual.iter().all(|(_, m)| m == zero)`), in which case the assignment is
yielded as it stands and otherwise skipped. -/
def acLeaf (rest : Option Var) (a : ACStore) : Option Binding :=
  let left := a.res.filter (fun e => e.2 ≠ 0)
  match rest with
  | none => if left.isEmpty then some a.σ else none
  | some r => some (a.σ.setRest r (ofEntries left))

/-- An annotation that never accepts count 0: `mult_matches` rejects `avail == ZERO` for
a variable, and the resolver emits no `exact 0` (`EnvAtomsWF`). -/
def MultPos : Mult → Prop
  | .exact m => m ≠ 0
  | .var _ lo _ => 1 ≤ lo

/-- The multiplicity variables of the elements. -/
def multVars (elems : List (Var × Mult)) : List Var :=
  elems.filterMap fun p => match p.2 with | .var k _ _ => some k | .exact _ => none

/-- The reachable stores at element `e`: `bound` is clear from `e` on, the residual keeps
its length and its classes, and a multiplicity variable of the elements is bound exactly
when an earlier element carries it. -/
structure ACGood (elems : List (Var × Mult)) (res₀ : List (C × Nat)) (e : Nat) (a : ACStore) : Prop where
  bound_len : a.bound.length = elems.length
  bound_clear : ∀ j, e ≤ j → a.bound.getD j false = false
  res_len : a.res.length = res₀.length
  res_cls : a.res.map Prod.fst = res₀.map Prod.fst
  mult_free : ∀ k ∈ multVars elems, usesMult elems e k = false → a.σ.mult k = none
  mult_bound : ∀ k, usesMult elems e k = true → (a.σ.mult k).isSome

theorem multMatches_zero {σ : Binding} {μ : Mult} (h : MultPos μ) : multMatches σ μ 0 = none := by
  cases μ with
  | exact m => simp only [MultPos] at h; simp [multMatches, Ne.symm h]
  | var k lo hi => simp only [MultPos] at h; simp [multMatches, inInterval, show ¬ lo ≤ 0 by omega]

/-- The cursor's write of a multiplicity variable. -/
def multApply (σ : Binding) : Mult → Nat → Binding
  | .exact _, _ => σ
  | .var k _ _, m => σ.setMult k m

theorem setMult_self {σ : Binding} {k : Var} {m : Nat} (h : σ.mult k = some m) : σ.setMult k m = σ := by
  unfold Binding.setMult
  rw [← h, Function.update_eq_self]

theorem multMatches_some {σ σ' : Binding} {μ : Mult} {m : Nat} (h : multMatches σ μ m = some σ') :
    σ' = multApply σ μ m := by
  cases μ with
  | exact k =>
      simp only [multMatches] at h
      split at h <;> simp_all [multApply]
  | var k lo hi =>
      simp only [multMatches] at h
      split at h
      · split at h
        · rename_i m' hm
          split at h
          · rename_i hmm
            simp only [Option.some.injEq] at h
            subst h; subst hmm
            simp [multApply, setMult_self hm]
          · simp at h
        · simp only [Option.some.injEq] at h; subst h; rfl
      · simp at h

theorem multMatches_bound {σ σ' : Binding} {k : Var} {lo : Nat} {hi : Option Nat} {m m' : Nat}
    (h : multMatches σ (.var k lo hi) m = some σ') (hm : σ.mult k = some m') : m' = m := by
  simp only [multMatches, hm] at h
  split at h
  · split at h
    · assumption
    · simp at h
  · simp at h

@[simp] theorem setCls_mult (σ : Binding) (x : Var) (c : C) (k : Var) : (σ.setCls x c).mult k = σ.mult k := rfl
@[simp] theorem setMult_cls (σ : Binding) (k : Var) (m : Nat) (x : Var) : (σ.setMult k m).cls x = σ.cls x := rfl
@[simp] theorem setMult_mult_self (σ : Binding) (k : Var) (m : Nat) : (σ.setMult k m).mult k = some m := by
  simp [Binding.setMult]
@[simp] theorem setMult_mult_ne (σ : Binding) (k : Var) (m : Nat) (k' : Var) (h : k' ≠ k) :
    (σ.setMult k m).mult k' = σ.mult k' := by
  simp [Binding.setMult, Function.update_of_ne h]
@[simp] theorem setCls_cls_self' (σ : Binding) (x : Var) (c : C) : (σ.setCls x c).cls x = some c := by
  simp [Binding.setCls]
theorem setCls_cls_ne (σ : Binding) (x : Var) (c : C) (y : Var) (h : y ≠ x) : (σ.setCls x c).cls y = σ.cls y := by
  simp [Binding.setCls, Function.update_of_ne h]

theorem clearCls_setCls {σ : Binding} {x : Var} {c : C} (h : σ.cls x = none) : clearCls (σ.setCls x c) x = σ := by
  unfold clearCls Binding.setCls
  simp only [Function.update_idem]
  rw [← h, Function.update_eq_self]

theorem clearMult_setMult {σ : Binding} {k : Var} {m : Nat} (h : σ.mult k = none) : clearMult (σ.setMult k m) k = σ := by
  unfold clearMult Binding.setMult
  simp only [Function.update_idem]
  rw [← h, Function.update_eq_self]

theorem clearCls_setMult (σ : Binding) (x k : Var) (m : Nat) : clearCls (σ.setMult k m) x = (clearCls σ x).setMult k m := rfl
theorem clearMult_setCls (σ : Binding) (x k : Var) (c : C) : clearMult (σ.setCls x c) k = (clearMult σ k).setCls x c := rfl

theorem usesMult_succ (elems : List (Var × Mult)) (e : Nat) (k : Var) (he : e < elems.length) :
    usesMult elems (e + 1) k =
      (usesMult elems e k || match (elems[e]'he).2 with | .var k' _ _ => k' == k | .exact _ => false) := by
  unfold usesMult
  rw [List.take_add_one, List.getElem?_eq_getElem he]
  simp only [Option.toList_some, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem mem_multVars {elems : List (Var × Mult)} {e : Nat} {x k : Var} {lo : Nat} {hi : Option Nat}
    (h : elems[e]? = some (x, .var k lo hi)) : k ∈ multVars elems := by
  unfold multVars
  rw [List.mem_filterMap]
  exact ⟨(x, .var k lo hi), List.mem_of_getElem? h, rfl⟩

/-- A hit names an element and a live entry. -/
theorem acAccept_some {elems : List (Var × Mult)} {a : ACStore} {e ri : Nat}
    (hpos : ∀ p ∈ elems, MultPos p.2) (h : acAccept elems a e ri = true) :
    ∃ x μ, elems[e]? = some (x, μ) ∧ e < elems.length ∧ ri < a.res.length ∧
      ∃ σ', multMatches a.σ μ (a.res.getD ri (0, 0)).2 = some σ' ∧
        (∀ c', a.σ.cls x = some c' → (a.res.getD ri (0, 0)).1 = c') := by
  unfold acAccept at h
  split at h
  · simp at h
  · rename_i x μ hx
    have he : e < elems.length := by
      by_contra hc; push Not at hc
      rw [List.getElem?_eq_none hc] at hx; simp at hx
    have hμ : MultPos μ := hpos (x, μ) (List.mem_of_getElem? hx)
    have hri : ri < a.res.length := by
      by_contra hc; push Not at hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc] at h
      simp only [Option.getD_none, multMatches_zero hμ] at h
      split at h <;> simp at h
    refine ⟨x, μ, hx, he, hri, ?_⟩
    split at h
    · rename_i c' hc'
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
      obtain ⟨hceq, σ', hσ'⟩ := h
      exact ⟨σ', hσ', fun c'' hc'' => by rw [hc'] at hc''; simp only [Option.some.injEq] at hc''; subst hc''; exact hceq⟩
    · rename_i hc
      simp only [Option.isSome_iff_exists] at h
      obtain ⟨σ', hσ'⟩ := h
      exact ⟨σ', hσ', fun c'' hc'' => by rw [hc] at hc''; simp at hc''⟩

theorem acLaws (elems : List (Var × Mult)) (res₀ : List (C × Nat)) (hpos : ∀ p ∈ elems, MultPos p.2) :
    (acOps elems res₀.length).Laws (ACGood elems res₀) := by
  constructor
  · intro a e ri hg hacc
    obtain ⟨x, μ, hx, he, hri, σ', hmm, hcls⟩ := acAccept_some hpos hacc
    have hxg : elems.getD e defElem = (x, μ) := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    rcases hres : a.res.getD ri (0, 0) with ⟨c, m⟩
    simp only [hres] at hmm hcls
    have hres' : a.res[ri] = (c, m) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri] at hres; exact hres
    have hbe : e < a.bound.length := by rw [hg.bound_len]; exact he
    have hb : a.bound[e] = false := by
      have := hg.bound_clear e le_rfl
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbe] at this; exact this
    -- the residual: the entry is set to 0 and restored to `m`
    have hget : (a.res.set ri (c, 0))[ri]? = some (c, 0) := List.getElem?_set_self hri
    have hrestore : ∀ restore : Nat, restore = m →
        (a.res.set ri (c, 0)).set ri (c, 0 + restore) = a.res := by
      intro restore hr
      rw [hr, List.set_set, Nat.zero_add, ← hres', List.set_getElem_self hri]
    have hbset : ∀ b, (a.bound.set e b).set e false = a.bound := by
      intro b
      rw [List.set_set, ← hb, List.set_getElem_self hbe]
    have hbt : (a.bound.set e true)[e]? = some true := List.getElem?_set_self hbe
    have hbf : (a.bound.set e false)[e]? = some false := List.getElem?_set_self hbe
    simp only [acOps, acApply, acUndo, hxg, hres, List.getD_eq_getElem?_getD, hget, Option.getD_some]
    rcases hcx : a.σ.cls x with _ | c₀
    · -- unbound: the variable is bound and `bound[e]` set; the undo clears both
      cases μ with
      | exact k =>
          have hk : m = k := by
            simp only [multMatches] at hmm; split at hmm <;> simp_all
          simp only [hbt, Option.getD_some, ite_true, hbset, clearCls_setCls hcx, hrestore k hk.symm]
      | var k lo hi =>
          have hk : k ∈ multVars elems := mem_multVars hx
          simp only [hbt, Option.getD_some, ite_true, hbset, setMult_mult_self, clearCls_setMult,
            clearCls_setCls hcx, hrestore m rfl]
          rcases hu : usesMult elems e k with _ | _
          · have hnone := hg.mult_free k hk hu
            simp only [Bool.false_eq_true, ite_false, clearMult_setMult hnone]
          · obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 (hg.mult_bound k hu)
            have := multMatches_bound hmm hm'
            subst this
            simp only [ite_true, setMult_self hm']
    · -- bound: the variable is checked and left alone
      cases μ with
      | exact k =>
          have hk : m = k := by
            simp only [multMatches] at hmm; split at hmm <;> simp_all
          simp only [hbf, Option.getD_some, Bool.false_eq_true, ite_false, hbset, hrestore k hk.symm]
      | var k lo hi =>
          have hk : k ∈ multVars elems := mem_multVars hx
          simp only [hbf, Option.getD_some, Bool.false_eq_true, ite_false, hbset, setMult_mult_self,
            hrestore m rfl]
          rcases hu : usesMult elems e k with _ | _
          · have hnone := hg.mult_free k hk hu
            simp only [Bool.false_eq_true, ite_false, clearMult_setMult hnone]
          · obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 (hg.mult_bound k hu)
            have := multMatches_bound hmm hm'
            subst this
            simp only [ite_true, setMult_self hm']
  · intro a e ri hg hacc
    obtain ⟨x, μ, hx, he, hri, σ', hmm, hcls⟩ := acAccept_some hpos hacc
    have hxg : elems.getD e defElem = (x, μ) := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    have hxe : elems[e] = (x, μ) := by rw [List.getElem?_eq_getElem he] at hx; simpa using hx
    rcases hres : a.res.getD ri (0, 0) with ⟨c, m⟩
    have hres' : a.res[ri] = (c, m) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri] at hres; exact hres
    have hcls' : (a.res.set ri (c, 0)).map Prod.fst = res₀.map Prod.fst := by
      rw [List.map_set, ← hg.res_cls]
      have : (a.res.map Prod.fst)[ri]'(by simpa using hri) = c := by simp [hres']
      rw [← this, List.set_getElem_self]
    have hbc : ∀ j, e + 1 ≤ j → ∀ b, (a.bound.set e b).getD j false = false := by
      intro j hj b
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hg.bound_clear j (by omega)
    simp only [acOps, acApply, hxg, hres]
    rcases μ with k | ⟨k, lo, hi⟩
    · -- exact: the multiplicity cells are unchanged
      have hσ : ∀ k', (match a.σ.cls x with | some _ => a.σ | none => a.σ.setCls x c).mult k' = a.σ.mult k' := by
        intro k'; split <;> rfl
      refine ⟨by simp [hg.bound_len], fun j hj => hbc j hj _, by simp [hg.res_len], hcls', ?_, ?_⟩
      · intro k' hk' hu
        rw [usesMult_succ elems e k' he, hxe, Bool.or_eq_false_iff] at hu
        dsimp only; rw [hσ]; exact hg.mult_free k' hk' hu.1
      · intro k' hu
        rw [usesMult_succ elems e k' he, hxe] at hu
        dsimp only at hu
        simp only [Bool.or_false] at hu
        dsimp only; rw [hσ]; exact hg.mult_bound k' hu
    · -- variable: the cell `k` is written
      have hσ : ∀ k', ((match a.σ.cls x with | some _ => a.σ | none => a.σ.setCls x c).setMult k m).mult k' =
          if k' = k then some m else a.σ.mult k' := by
        intro k'
        by_cases hk : k' = k
        · subst hk; simp
        · rw [setMult_mult_ne _ _ _ _ hk]; simp only [hk, ↓reduceIte]; split <;> rfl
      refine ⟨by simp [hg.bound_len], fun j hj => hbc j hj _, by simp [hg.res_len], hcls', ?_, ?_⟩
      · intro k' hk' hu
        rw [usesMult_succ elems e k' he, hxe, Bool.or_eq_false_iff] at hu
        dsimp only at hu
        have hne : k' ≠ k := by
          intro h; subst h; simp at hu
        dsimp only; rw [hσ]; simp only [hne, ↓reduceIte]; exact hg.mult_free k' hk' hu.1
      · intro k' hu
        rw [usesMult_succ elems e k' he, hxe, Bool.or_eq_true] at hu
        dsimp only at hu
        dsimp only; rw [hσ]
        by_cases hk : k' = k
        · simp [hk]
        · simp only [hk, ↓reduceIte]
          rcases hu with hu | hu
          · exact hg.mult_bound k' hu
          · simp only [beq_iff_eq] at hu; exact absurd hu.symm hk


/-! ### The AC frame yields `decomposeAC` -/

theorem flatMap_range_getD {β γ : Type} (l : List β) (d : β) (g : β → List γ) :
    (List.range l.length).flatMap (fun i => g (l.getD i d)) = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [List.getD_cons_zero, List.getD_cons_succ, ih, List.flatMap_cons]

theorem flatMap_range_single {γ : Type} (f : Nat → List γ) (len ri : Nat) (hri : ri < len)
    (h : ∀ j, j < len → j ≠ ri → f j = []) : (List.range len).flatMap f = f ri := by
  induction len with
  | zero => omega
  | succ len ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rcases Nat.lt_or_ge ri len with hlt | hge
      · rw [ih hlt (fun j hj hne => h j (by omega) hne), h len (by omega) (by omega), List.append_nil]
      · have : ri = len := by omega
        subst this
        rw [List.flatMap_eq_nil_iff.2 (fun j hj => h j (by simp at hj; omega) (by simp at hj; omega)),
          List.nil_append]

/-- The entry a class names, under distinct classes: at most one index. -/
theorem cls_index_unique {res : List (C × Nat)} (hnd : (res.map Prod.fst).Nodup) {i j : Nat}
    (hi : i < res.length) (hj : j < res.length) (h : res[i].1 = res[j].1) : i = j := by
  have hinj := @List.Nodup.getElem_inj_iff _ _ hnd i (by simpa using hi) j (by simpa using hj)
  rw [List.getElem_map, List.getElem_map] at hinj
  exact hinj.1 h

/-- With distinct classes, zeroing the class of entry `ri` is setting entry `ri`. -/
theorem zeroEntry_eq_set {res : List (C × Nat)} (hnd : (res.map Prod.fst).Nodup) {ri : Nat}
    (hri : ri < res.length) : zeroEntry res[ri].1 res = res.set ri (res[ri].1, 0) := by
  apply List.ext_getElem
  · simp [zeroEntry]
  · intro j hj hj'
    have hj2 : j < res.length := by rw [zeroEntry, List.length_map] at hj; exact hj
    simp only [zeroEntry, List.getElem_map]
    by_cases hjr : j = ri
    · subst hjr; simp
    · rw [List.getElem_set_ne (Ne.symm hjr)]
      have : res[j].1 ≠ res[ri].1 := fun heq => hjr (cls_index_unique hnd hj2 hri heq)
      simp [this]

theorem multMatches_isSome_of_ne_zero {σ : Binding} {μ : Mult} {m : Nat} (hpos : MultPos μ)
    (h : (multMatches σ μ m).isSome = true) : m ≠ 0 := by
  rintro rfl; rw [multMatches_zero hpos] at h; simp at h

/-- The cursor's apply agrees with the executor's step on the entry: the residual with the
entry zeroed and the environment `multMatches` returns, the element bound if it was free. -/
theorem acApply_eq {elems : List (Var × Mult)} {a : ACStore} {e ri : Nat} {x : Var} {μ : Mult} {σ' : Binding}
    (hx : elems[e]? = some (x, μ)) (hri : ri < a.res.length)
    (hmm : multMatches a.σ μ a.res[ri].2 = some σ') :
    (acApply elems a e ri).res = a.res.set ri (a.res[ri].1, 0) ∧
      (acApply elems a e ri).σ = (match a.σ.cls x with | some _ => σ' | none => σ'.setCls x a.res[ri].1) := by
  have hxg : elems.getD e defElem = (x, μ) := by rw [List.getD_eq_getElem?_getD, hx]; rfl
  have hres : a.res.getD ri (0, 0) = a.res[ri] := List.getD_eq_getElem a.res (0, 0) hri
  constructor
  · simp only [acApply, hxg, hres]
  · rw [multMatches_some hmm]
    cases μ <;> simp only [acApply, multApply, hxg, hres] <;> split <;> rfl

theorem flatMap_range_congr {γ : Type} (f g : Nat → List γ) (n : Nat) (h : ∀ i, i < n → f i = g i) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega)),
        List.flatMap_singleton, List.flatMap_singleton, h n (by omega)]

/-- `ac_scan`'s test at an in-range entry, by the state of the element variable. -/
theorem acAccept_eq {elems : List (Var × Mult)} {a : ACStore} {e ri : Nat} {x : Var} {μ : Mult}
    (hx : elems[e]? = some (x, μ)) (hri : ri < a.res.length) :
    acAccept elems a e ri = (match a.σ.cls x with
      | some c' => decide (a.res[ri].1 = c') && (multMatches a.σ μ a.res[ri].2).isSome
      | none => (multMatches a.σ μ a.res[ri].2).isSome) := by
  have hres : a.res.getD ri (0, 0) = a.res[ri] := List.getD_eq_getElem a.res (0, 0) hri
  simp only [acAccept, hx, hres]

/-- The frame's enumeration from element `e` is the executor's decomposition of the
elements from `e`, after the leaf. -/
theorem enum_eq_decomposeAC (elems : List (Var × Mult)) (rest : Option Var) (res₀ : List (C × Nat))
    (hnd : (res₀.map Prod.fst).Nodup) (hpos : ∀ p ∈ elems, MultPos p.2) :
    ∀ (k e : Nat) (a : ACStore), elems.length - e = k → ACGood elems res₀ e a →
      decomposeAC (elems.drop e) rest a.res a.σ =
        ((acOps elems res₀.length).enum e a).filterMap (acLeaf rest) := by
  intro k
  induction k with
  | zero =>
      intro e a hk hg
      have he : elems.length ≤ e := by omega
      have hn : (acOps elems res₀.length).n = elems.length := rfl
      rw [List.drop_eq_nil_of_le he]
      have : (acOps elems res₀.length).enum e a = [a] := by
        unfold Ops.enum Ops.rest
        rw [hn, Nat.sub_eq_zero_of_le he]; rfl
      rw [this]
      cases rest with
      | none =>
          simp only [decomposeAC, acLeaf, List.filterMap_cons, List.filterMap_nil]
          split <;> simp_all
      | some r => simp [decomposeAC, acLeaf]
  | succ k ih =>
      intro e a hk hg
      have he : e < elems.length := by omega
      rcases hp : elems[e] with ⟨x, μ⟩
      have hxe : elems[e]? = some (x, μ) := by rw [List.getElem?_eq_getElem he, hp]
      have hμ : MultPos μ := hpos (x, μ) (hp ▸ List.getElem_mem he)
      have hlen : a.res.length = res₀.length := hg.res_len
      have hnd' : (a.res.map Prod.fst).Nodup := hg.res_cls ▸ hnd
      rw [List.drop_eq_getElem_cons he, hp]
      have henum : (acOps elems res₀.length).enum e a = (List.range a.res.length).flatMap fun ri =>
          if acAccept elems a e ri then (acOps elems res₀.length).enum (e + 1) (acApply elems a e ri) else [] := by
        unfold Ops.enum
        rw [Ops.rest_lt _ he, Nat.sub_zero, ← List.range_eq_range',
          show (acOps elems res₀.length).len = res₀.length from rfl, ← hlen]
        rfl
      rw [henum, List.filterMap_flatMap]
      -- the recursive call under the invariant
      have hrec : ∀ ri, acAccept elems a e ri = true →
          ((acOps elems res₀.length).enum (e + 1) (acApply elems a e ri)).filterMap (acLeaf rest) =
            decomposeAC (elems.drop (e + 1)) rest (acApply elems a e ri).res (acApply elems a e ri).σ :=
        fun ri hacc => (ih (e + 1) _ (by omega) ((acLaws elems res₀ hpos).good_apply a e ri hg hacc)).symm
      simp only [decomposeAC]
      rcases hcx : a.σ.cls x with _ | c₀
      · -- unbound: both branch over the entries in order
        rw [← flatMap_range_getD a.res (0, 0)]
        apply flatMap_range_congr
        intro ri hri
        rw [List.getD_eq_getElem a.res (0, 0) hri, acAccept_eq hxe hri, hcx]
        simp only
        by_cases hm : a.res[ri].2 = 0
        · rw [hm, multMatches_zero hμ]; simp
        · simp only [hm, ↓reduceIte]
          rcases hmm : multMatches a.σ μ a.res[ri].2 with _ | σ'
          · simp
          · have hacc : acAccept elems a e ri = true := by
              rw [acAccept_eq hxe hri, hcx, hmm]; rfl
            simp only [Option.isSome_some, ↓reduceIte]
            rw [hrec ri hacc]
            obtain ⟨hres, hσ⟩ := acApply_eq hxe hri hmm
            rw [hres, hσ, hcx, zeroEntry_eq_set hnd' hri]
      · -- bound: at most one entry has the class
        dsimp only
        split
        · rename_i en hfind
          obtain ⟨hc, hm⟩ : en.1 = c₀ ∧ en.2 ≠ 0 := by simpa using List.find?_some hfind
          obtain ⟨ri, hri, hen⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some hfind)
          rw [flatMap_range_single _ a.res.length ri hri]
          · rw [acAccept_eq hxe hri, hcx, hen]
            simp only [hc, decide_true, Bool.true_and]
            rcases hmm : multMatches a.σ μ en.2 with _ | σ'
            · simp
            · have hacc : acAccept elems a e ri = true := by
                rw [acAccept_eq hxe hri, hcx, hen, hmm]; simp [hc]
              simp only [Option.isSome_some, ↓reduceIte]
              rw [hrec ri hacc]
              obtain ⟨hres, hσ⟩ := acApply_eq hxe hri (hen ▸ hmm)
              rw [hres, hσ, hcx, ← hc, ← hen, zeroEntry_eq_set hnd' hri]
          · intro j hj hne
            rw [acAccept_eq hxe hj, hcx]
            have : a.res[j].1 ≠ c₀ := fun h => hne (cls_index_unique hnd' hj hri (by rw [h, hen, hc]))
            simp [this]
        · rename_i hfind
          symm
          rw [List.flatMap_eq_nil_iff]
          intro ri hri
          rw [List.mem_range] at hri
          have hnone := List.find?_eq_none.1 hfind a.res[ri] (List.getElem_mem hri)
          simp only [decide_eq_true_eq, not_and, not_not] at hnone
          rw [acAccept_eq hxe hri, hcx]
          simp only
          by_cases hc : a.res[ri].1 = c₀
          · rw [hnone hc, multMatches_zero hμ]; simp
          · simp [hc]

/-- `enter_ac`'s frame store: the environment, the node's entries, `bound = vec![false; n]`. -/
def acInit (elems : List (Var × Mult)) (res₀ : List (C × Nat)) (σ₀ : Binding) : ACStore :=
  ⟨σ₀, res₀, List.replicate elems.length false⟩

theorem acGood_init (elems : List (Var × Mult)) (res₀ : List (C × Nat)) (σ₀ : Binding)
    (hμ : ∀ k ∈ multVars elems, σ₀.mult k = none) : ACGood elems res₀ 0 (acInit elems res₀ σ₀) := by
  refine ⟨by simp [acInit], ?_, rfl, rfl, fun k hk _ => hμ k hk, ?_⟩
  · intro j _
    simp only [acInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  · intro k hu
    simp [usesMult] at hu

/-- Theorem B for AC: the frame's yields, after the leaf, are the executor's decomposition
`decomposeAC`, element for element, for every fuel: the first `k` yields are the first `k`
of the executor's list, and with fuel for every yield the lists are equal. -/
theorem acFrame_eq_decomposeAC (elems : List (Var × Mult)) (rest : Option Var)
    (res₀ : List (C × Nat)) (σ₀ : Binding) (hnd : (res₀.map Prod.fst).Nodup)
    (hpos : ∀ p ∈ elems, MultPos p.2) (hμ : ∀ k ∈ multVars elems, σ₀.mult k = none)
    (hne : elems ≠ []) :
    (∀ k, ((acOps elems res₀.length).drive k ((acOps elems res₀.length).init (acInit elems res₀ σ₀))).filterMap
        (acLeaf rest) = (((acOps elems res₀.length).enum 0 (acInit elems res₀ σ₀)).take k).filterMap (acLeaf rest)) ∧
    ∀ k, ((acOps elems res₀.length).enum 0 (acInit elems res₀ σ₀)).length ≤ k →
      ((acOps elems res₀.length).drive k ((acOps elems res₀.length).init (acInit elems res₀ σ₀))).filterMap
        (acLeaf rest) = decomposeAC elems rest res₀ σ₀ := by
  have hn : 0 < (acOps elems res₀.length).n := by
    show 0 < elems.length; exact List.length_pos_iff.2 hne
  have hl := acLaws elems res₀ hpos
  have h0 := acGood_init elems res₀ σ₀ hμ
  have hdec : decomposeAC elems rest res₀ σ₀ =
      ((acOps elems res₀.length).enum 0 (acInit elems res₀ σ₀)).filterMap (acLeaf rest) :=
    enum_eq_decomposeAC elems rest res₀ hnd hpos _ 0 _ rfl h0
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [Ops.drive_eq_enum _ hl h0 hn]
  · rw [Ops.drive_eq_enum _ hl h0 hn, List.take_of_length_le hk, hdec]

/-! ### No duplicates -/

theorem multMatches_cls {σ σ' : Binding} {μ : Mult} {m : Nat} (h : multMatches σ μ m = some σ') :
    σ'.cls = σ.cls := by
  rw [multMatches_some h]; cases μ <;> rfl

/-- The decomposition keeps a class binding it starts with. -/
theorem decomposeAC_cls (es : List (Var × Mult)) (rest : Option Var) :
    ∀ (res : List (C × Nat)) (σ σ' : Binding) (x : Var) (c : C),
      σ' ∈ decomposeAC es rest res σ → σ.cls x = some c → σ'.cls x = some c := by
  induction es with
  | nil =>
      intro res σ σ' x c h hx
      simp only [decomposeAC] at h
      cases rest with
      | none =>
          dsimp only at h
          split at h <;> simp at h
          exact h ▸ hx
      | some r => simp at h; subst h; exact hx
  | cons p es ih =>
      obtain ⟨y, μ⟩ := p
      intro res σ σ' x c h hx
      simp only [decomposeAC] at h
      split at h
      · split at h
        · split at h
          · exact ih _ _ _ x c h (by rw [multMatches_cls (by assumption)]; exact hx)
          · simp at h
        · simp at h
      · rename_i hy
        rw [List.mem_flatMap] at h
        obtain ⟨en, _, h⟩ := h
        split at h
        · simp at h
        · split at h
          · rename_i σ₁ hmm
            have hxy : x ≠ y := fun hxy => by subst hxy; rw [hy] at hx; simp at hx
            refine ih _ _ _ x c h ?_
            rw [setCls_cls_ne _ _ _ _ hxy, multMatches_cls hmm]; exact hx
          · simp at h

theorem zeroEntry_map_fst (c : C) (res : List (C × Nat)) : (zeroEntry c res).map Prod.fst = res.map Prod.fst := by
  simp only [zeroEntry, List.map_map]
  congr 1
  funext e
  simp only [Function.comp]
  split <;> simp_all

/-- The executor's decomposition has no duplicate bindings when the entries' classes are
distinct: two assignments differ at the first element that takes different entries. -/
theorem decomposeAC_nodup (es : List (Var × Mult)) (rest : Option Var) :
    ∀ (res : List (C × Nat)) (σ : Binding), (res.map Prod.fst).Nodup → (decomposeAC es rest res σ).Nodup := by
  induction es with
  | nil =>
      intro res σ _
      simp only [decomposeAC]
      cases rest with
      | none => dsimp only; split <;> simp
      | some r => simp
  | cons p es ih =>
      obtain ⟨y, μ⟩ := p
      intro res σ hnd
      simp only [decomposeAC]
      split
      · split
        · split
          · exact ih _ _ (by rw [zeroEntry_map_fst]; exact hnd)
          · exact List.nodup_nil
        · exact List.nodup_nil
      · rename_i hy
        rw [List.nodup_flatMap]
        constructor
        · intro en _
          split
          · exact List.nodup_nil
          · split
            · exact ih _ _ (by rw [zeroEntry_map_fst]; exact hnd)
            · exact List.nodup_nil
        · have hp : res.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.1 hnd
          refine hp.imp ?_
          intro a b hab
          simp only [Function.onFun, List.disjoint_left]
          intro σ' ha hb
          -- `σ'` binds `y` to `a.1` and to `b.1`
          have hcls : ∀ en : C × Nat, σ' ∈ (if en.2 = 0 then [] else
              match multMatches σ μ en.2 with
              | some σ'' => decomposeAC es rest (zeroEntry en.1 res) (σ''.setCls y en.1)
              | none => []) → σ'.cls y = some en.1 := by
            intro en h
            split at h
            · simp at h
            · split at h
              · exact decomposeAC_cls es rest _ _ _ y en.1 h (setCls_cls_self' _ _ _)
              · simp at h
          have h1 := hcls a ha
          have h2 := hcls b hb
          rw [h1] at h2
          exact hab (Option.some.inj h2)


/-! ## The ACI frame (`FrameKind::ACIDecompose`)

The store is the environment, one `used` bit per entry and the `bound` flags; the entries
`res₀` themselves are read-only. -/

structure ACIStore where
  σ : Binding
  used : List Bool
  bound : List Bool

/-- The entries not yet used, from index `i` on:
`residual.iter().enumerate().filter(|(i, _)| !used.test(i))`. -/
def remainingFrom (used : List Bool) : Nat → List C → List C
  | _, [] => []
  | i, c :: cs =>
      if used.getD i false then remainingFrom used (i + 1) cs else c :: remainingFrom used (i + 1) cs

def remainingOf (res₀ : List C) (used : List Bool) : List C := remainingFrom used 0 res₀

/-- `aci_scan`'s test of one entry: `!used.test(ri)`, and on the bound-repr path
`residual[ri] == repr`. An element index past the end accepts nothing. -/
def aciAccept (elems : List Var) (res₀ : List C) (a : ACIStore) (e ri : Nat) : Bool :=
  match elems[e]? with
  | none => false
  | some x =>
      !a.used.getD ri true &&
        (match a.σ.cls x with
          | some c => decide (res₀.getD ri 0 = c)
          | none => true)

/-- `aci_scan`'s body at a hit: `self.env.set(vid, residual[ri]); bound[ei] = true` on the
unbound path, and `used.set(ri)`. -/
def aciApply (elems : List Var) (res₀ : List C) (a : ACIStore) (e ri : Nat) : ACIStore :=
  let x := elems.getD e 0
  let c := res₀.getD ri 0
  ⟨match a.σ.cls x with | some _ => a.σ | none => a.σ.setCls x c,
    a.used.set ri true,
    a.bound.set e (match a.σ.cls x with | some _ => false | none => true)⟩

/-- `aci_undo(elems, used, ei, ri, bound)`: `used.clear(ri)`, `env.clear(vid)` if
`bound[ei]`, `bound[ei] = false`. -/
def aciUndo (elems : List Var) (a : ACIStore) (e ri : Nat) : ACIStore :=
  let x := elems.getD e 0
  ⟨if a.bound.getD e false then clearCls a.σ x else a.σ, a.used.set ri false, a.bound.set e false⟩

/-- The ACI frame over `elems` on a node with the set children `res₀`. -/
def aciOps (elems : List Var) (res₀ : List C) : Ops ACIStore :=
  ⟨elems.length, res₀.length, aciAccept elems res₀, aciApply elems res₀, aciUndo elems⟩

/-- The leaf: `enter_aci` and `backtrack` push the unused entries as the rest, or require
every entry used (`(0..residual.len()).all(|i| used.test(i))`, which is the unused list
being empty) when there is no rest. -/
def aciLeaf (res₀ : List C) (rest : Option Var) (a : ACIStore) : Option Binding :=
  let rem := remainingOf res₀ a.used
  match rest with
  | none => if rem.isEmpty then some a.σ else none
  | some r => some (a.σ.setSetRest r rem.toFinset)

/-- The reachable stores at element `e`: `bound` is clear from `e` on and `used` has one
bit per entry. -/
structure ACIGood (elems : List Var) (res₀ : List C) (e : Nat) (a : ACIStore) : Prop where
  bound_len : a.bound.length = elems.length
  bound_clear : ∀ j, e ≤ j → a.bound.getD j false = false
  used_len : a.used.length = res₀.length

/-- `enter_aci`'s frame store: `used = BitSet::new(residual.len())`, `bound = vec![false; n]`. -/
def aciInit (elems : List Var) (res₀ : List C) (σ₀ : Binding) : ACIStore :=
  ⟨σ₀, List.replicate res₀.length false, List.replicate elems.length false⟩

/-! ### The unused entries -/

theorem getD_set_ne_bool (l : List Bool) (i j : Nat) (v : Bool) (hij : i ≠ j) :
    (l.set i v).getD j false = l.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

theorem flatMap_congr_mem {β γ : Type} {l : List β} {f g : β → List γ} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [List.flatMap_cons]
      rw [h b (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem remainingFrom_congr {used used' : List Bool} (cs : List C) :
    ∀ i, (∀ j, i ≤ j → j < i + cs.length → used.getD j false = used'.getD j false) →
      remainingFrom used i cs = remainingFrom used' i cs := by
  induction cs with
  | nil => intros; rfl
  | cons c cs ih =>
      intro i h
      simp only [remainingFrom]
      rw [h i le_rfl (by simp), ih (i + 1) (fun j hj1 hj2 => h j (by omega) (by simp at hj2 ⊢; omega))]

theorem remainingFrom_sublist (used : List Bool) (cs : List C) : ∀ i, (remainingFrom used i cs).Sublist cs := by
  induction cs with
  | nil => intro i; simp [remainingFrom]
  | cons c cs ih =>
      intro i
      simp only [remainingFrom]
      split
      · exact (ih (i + 1)).cons c
      · exact (ih (i + 1)).cons_cons c

theorem remainingFrom_mem {used : List Bool} {cs : List C} {c : C} :
    ∀ i, c ∈ remainingFrom used i cs ↔ ∃ j, j < cs.length ∧ cs.getD j 0 = c ∧ used.getD (i + j) false = false := by
  induction cs with
  | nil => intro i; simp [remainingFrom]
  | cons d cs ih =>
      intro i
      simp only [remainingFrom]
      constructor
      · intro h
        split at h
        · obtain ⟨j, hj, hc, hu⟩ := (ih (i + 1)).1 h
          exact ⟨j + 1, by simp; omega, by simpa using hc, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hu⟩
        · rename_i hu
          rcases List.mem_cons.1 h with rfl | h
          · exact ⟨0, by simp, rfl, by simpa using hu⟩
          · obtain ⟨j, hj, hc, hu⟩ := (ih (i + 1)).1 h
            exact ⟨j + 1, by simp; omega, by simpa using hc, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hu⟩
      · rintro ⟨j, hj, hc, hu⟩
        cases j with
        | zero =>
            simp only [List.getD_cons_zero] at hc
            simp only [Nat.add_zero] at hu
            rw [hu]; simp [hc]
        | succ j =>
            simp only [List.getD_cons_succ] at hc
            have hu' : used.getD (i + 1 + j) false = false := by rw [show i + 1 + j = i + (j + 1) by omega]; exact hu
            have hmem : c ∈ remainingFrom used (i + 1) cs := (ih (i + 1)).2 ⟨j, by simp at hj; omega, hc, hu'⟩
            split
            · exact hmem
            · exact List.mem_cons_of_mem _ hmem

/-- Using one more entry erases its class from the unused list. -/
theorem remainingFrom_set_erase {used : List Bool} {cs : List C} (hnd : cs.Nodup) :
    ∀ i ri, i ≤ ri → ri < i + cs.length → ri < used.length → used.getD ri false = false →
      remainingFrom (used.set ri true) i cs = (remainingFrom used i cs).erase (cs.getD (ri - i) 0) := by
  induction cs with
  | nil => intro i ri h1 h2; simp at h2; omega
  | cons c cs ih =>
      intro i ri h1 h2 hlen hu
      have hnd' := List.nodup_cons.1 hnd
      simp only [remainingFrom]
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · -- the entry used is this one
        have ht : (used.set i true).getD i false = true := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]; rfl
        rw [ht, hu, Nat.sub_self, List.getD_cons_zero]
        simp only [ite_true, Bool.false_eq_true, ite_false, List.erase_cons_head]
        exact remainingFrom_congr cs (i + 1) (fun j hj _ => getD_set_ne_bool _ _ _ _ (by omega))
      · have hne : (used.set ri true).getD i false = used.getD i false := getD_set_ne_bool _ _ _ _ (by omega)
        rw [hne]
        have hsub : ri - i = (ri - (i + 1)) + 1 := by omega
        rw [hsub, List.getD_cons_succ]
        have hih := ih hnd'.2 (i + 1) ri (by omega) (by simp at h2 ⊢; omega) hlen hu
        split
        · exact hih
        · rw [hih]
          have hmem : cs.getD (ri - (i + 1)) 0 ∈ cs := by
            rw [List.getD_eq_getElem cs 0 (by simp at h2; omega)]; exact List.getElem_mem _
          have : ¬ (c == cs.getD (ri - (i + 1)) 0) := by
            simp only [beq_iff_eq]
            intro h; exact hnd'.1 (h ▸ hmem)
          rw [List.erase_cons_tail this]

theorem remainingFrom_flatMap {γ : Type} (used : List Bool) (g : C → List γ) (cs : List C) :
    ∀ i, (remainingFrom used i cs).flatMap g =
      (List.range' i cs.length).flatMap fun ri => if used.getD ri false then [] else g (cs.getD (ri - i) 0) := by
  induction cs with
  | nil => intro i; rfl
  | cons c cs ih =>
      intro i
      simp only [remainingFrom, List.length_cons, List.range'_succ, List.flatMap_cons, Nat.sub_self,
        List.getD_cons_zero]
      have hcongr : ((List.range' (i + 1) cs.length).flatMap fun ri =>
          if used.getD ri false then [] else g ((c :: cs).getD (ri - i) 0)) =
          (List.range' (i + 1) cs.length).flatMap fun ri =>
            if used.getD ri false then [] else g (cs.getD (ri - (i + 1)) 0) := by
        apply flatMap_congr_mem
        intro ri hri
        rw [List.mem_range'_1] at hri
        rw [show ri - i = (ri - (i + 1)) + 1 by omega, List.getD_cons_succ]
      rw [hcongr, ← ih (i + 1)]
      split <;> simp

theorem remainingOf_flatMap {γ : Type} (res₀ : List C) (used : List Bool) (g : C → List γ) :
    (remainingOf res₀ used).flatMap g =
      (List.range res₀.length).flatMap fun ri => if used.getD ri false then [] else g (res₀.getD ri 0) := by
  unfold remainingOf
  rw [remainingFrom_flatMap, List.range_eq_range']
  simp only [Nat.sub_zero]

theorem remainingOf_replicate (res₀ : List C) : remainingOf res₀ (List.replicate res₀.length false) = res₀ := by
  unfold remainingOf
  suffices h : ∀ (cs : List C) (i : Nat), remainingFrom (List.replicate res₀.length false) i cs = cs from h res₀ 0
  intro cs
  induction cs with
  | nil => intro i; rfl
  | cons c cs ih =>
      intro i
      simp only [remainingFrom]
      have : (List.replicate res₀.length false).getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      rw [this, ih]; simp

/-! ### The ACI frame yields `decomposeACI` -/

/-- A hit names an element and an unused entry of the class the variable holds. -/
theorem aciAccept_some {elems : List Var} {res₀ : List C} {a : ACIStore} {e ri : Nat}
    (h : aciAccept elems res₀ a e ri = true) :
    ∃ x, elems[e]? = some x ∧ e < elems.length ∧ ri < a.used.length ∧ a.used.getD ri false = false ∧
      ∀ c, a.σ.cls x = some c → res₀.getD ri 0 = c := by
  unfold aciAccept at h
  split at h
  · simp at h
  · rename_i x hx
    have he : e < elems.length := by
      by_contra hc; push Not at hc
      rw [List.getElem?_eq_none hc] at hx; simp at hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have hri : ri < a.used.length := by
      by_contra hc; push Not at hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc] at h; simp at h
    refine ⟨x, hx, he, hri, ?_, ?_⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri] at h ⊢; exact h.1
    · intro c hc
      rw [hc] at h
      simpa using h.2

theorem aciLaws (elems : List Var) (res₀ : List C) : (aciOps elems res₀).Laws (ACIGood elems res₀) := by
  constructor
  · intro a e ri hg hacc
    obtain ⟨x, hx, he, hri, hu, _⟩ := aciAccept_some hacc
    have hxg : elems.getD e 0 = x := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    have hbe : e < a.bound.length := by rw [hg.bound_len]; exact he
    have hb : a.bound[e] = false := by
      have := hg.bound_clear e le_rfl
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbe] at this; exact this
    have hu' : a.used[ri] = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri] at hu; exact hu
    have hused : (a.used.set ri true).set ri false = a.used := by
      rw [List.set_set, ← hu', List.set_getElem_self hri]
    have hbset : ∀ b, (a.bound.set e b).set e false = a.bound := by
      intro b; rw [List.set_set, ← hb, List.set_getElem_self hbe]
    have hbt : (a.bound.set e true)[e]? = some true := List.getElem?_set_self hbe
    have hbf : (a.bound.set e false)[e]? = some false := List.getElem?_set_self hbe
    simp only [aciOps, aciApply, aciUndo, hxg, hused, List.getD_eq_getElem?_getD]
    rcases hcx : a.σ.cls x with _ | c₀
    · simp only [hbt, Option.getD_some, ite_true, hbset, clearCls_setCls hcx]
    · simp only [hbf, Option.getD_some, Bool.false_eq_true, ite_false, hbset]
  · intro a e ri hg hacc
    obtain ⟨x, hx, he, hri, hu, _⟩ := aciAccept_some hacc
    refine ⟨by simp [aciOps, aciApply, hg.bound_len], ?_, by simp [aciOps, aciApply, hg.used_len]⟩
    intro j hj
    simp only [aciOps, aciApply]
    rw [getD_set_ne_bool _ _ _ _ (by omega)]
    exact hg.bound_clear j (by omega)

theorem aciGood_init (elems : List Var) (res₀ : List C) (σ₀ : Binding) :
    ACIGood elems res₀ 0 (aciInit elems res₀ σ₀) := by
  refine ⟨by simp [aciInit], ?_, by simp [aciInit]⟩
  intro j _
  simp only [aciInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- `aci_scan`'s test at an in-range entry, by the state of the element variable. -/
theorem aciAccept_eq {elems : List Var} {res₀ : List C} {a : ACIStore} {e ri : Nat} {x : Var}
    (hx : elems[e]? = some x) (hri : ri < a.used.length) :
    aciAccept elems res₀ a e ri = (!a.used.getD ri false &&
      (match a.σ.cls x with | some c => decide (res₀.getD ri 0 = c) | none => true)) := by
  simp only [aciAccept, hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri, Option.getD_some]

/-- The index of a class in a list without duplicates is unique. -/
theorem nodup_getD_inj {res₀ : List C} (hnd : res₀.Nodup) {i j : Nat} (hi : i < res₀.length)
    (hj : j < res₀.length) (h : res₀.getD i 0 = res₀.getD j 0) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h

/-- The frame's enumeration from element `e` is the executor's decomposition of the
elements from `e` over the unused entries, after the leaf. -/
theorem enum_eq_decomposeACI (elems : List Var) (rest : Option Var) (res₀ : List C) (hnd : res₀.Nodup) :
    ∀ (k e : Nat) (a : ACIStore), elems.length - e = k → ACIGood elems res₀ e a →
      decomposeACI (elems.drop e) rest (remainingOf res₀ a.used) a.σ =
        ((aciOps elems res₀).enum e a).filterMap (aciLeaf res₀ rest) := by
  intro k
  induction k with
  | zero =>
      intro e a hk hg
      have he : elems.length ≤ e := by omega
      rw [List.drop_eq_nil_of_le he]
      have : (aciOps elems res₀).enum e a = [a] := by
        unfold Ops.enum Ops.rest
        rw [show (aciOps elems res₀).n = elems.length from rfl, Nat.sub_eq_zero_of_le he]; rfl
      rw [this]
      cases rest with
      | none =>
          simp only [decomposeACI, aciLeaf, List.filterMap_cons, List.filterMap_nil]
          split <;> simp_all
      | some r => simp [decomposeACI, aciLeaf]
  | succ k ih =>
      intro e a hk hg
      have he : e < elems.length := by omega
      obtain ⟨x, hx⟩ : ∃ x, elems[e] = x := ⟨_, rfl⟩
      have hxe : elems[e]? = some x := by rw [List.getElem?_eq_getElem he, hx]
      have hlen : a.used.length = res₀.length := hg.used_len
      rw [List.drop_eq_getElem_cons he, hx]
      have henum : (aciOps elems res₀).enum e a = (List.range res₀.length).flatMap fun ri =>
          if aciAccept elems res₀ a e ri then (aciOps elems res₀).enum (e + 1) (aciApply elems res₀ a e ri) else [] := by
        unfold Ops.enum
        rw [Ops.rest_lt _ he, Nat.sub_zero, ← List.range_eq_range']
        rfl
      rw [henum, List.filterMap_flatMap]
      have hrec : ∀ ri, aciAccept elems res₀ a e ri = true →
          ((aciOps elems res₀).enum (e + 1) (aciApply elems res₀ a e ri)).filterMap (aciLeaf res₀ rest) =
            decomposeACI (elems.drop (e + 1)) rest (remainingOf res₀ (aciApply elems res₀ a e ri).used)
              (aciApply elems res₀ a e ri).σ :=
        fun ri hacc => (ih (e + 1) _ (by omega) ((aciLaws elems res₀).good_apply a e ri hg hacc)).symm
      have hxg : elems.getD e 0 = x := by rw [List.getD_eq_getElem?_getD, hxe]; rfl
      -- the unused list after using entry `ri`
      have herase : ∀ ri, ri < res₀.length → a.used.getD ri false = false →
          remainingOf res₀ (a.used.set ri true) = (remainingOf res₀ a.used).erase (res₀.getD ri 0) := by
        intro ri hri hu
        unfold remainingOf
        rw [remainingFrom_set_erase hnd 0 ri (Nat.zero_le _) (by omega) (by omega) hu, Nat.sub_zero]
      simp only [decomposeACI]
      rcases hcx : a.σ.cls x with _ | c₀
      · -- unbound: both branch over the unused entries in order
        rw [remainingOf_flatMap]
        apply flatMap_range_congr
        intro ri hri
        rw [aciAccept_eq hxe (hlen ▸ hri), hcx]
        simp only [Bool.and_true]
        rcases hu : a.used.getD ri false with _ | _
        · have hacc : aciAccept elems res₀ a e ri = true := by
            rw [aciAccept_eq hxe (hlen ▸ hri), hcx, hu]; rfl
          simp only [Bool.not_false, ↓reduceIte]
          rw [hrec ri hacc]
          simp only [aciApply, hxg, hcx, herase ri hri hu, Bool.false_eq_true, ite_false]
        · simp
      · -- bound: at most one entry has the class
        dsimp only
        by_cases hc : c₀ ∈ res₀
        · obtain ⟨ri₀, hri₀, hc0'⟩ := List.getElem_of_mem hc
          have hc0 : res₀.getD ri₀ 0 = c₀ := by rw [List.getD_eq_getElem _ _ hri₀]; exact hc0'
          have hmem : c₀ ∈ remainingOf res₀ a.used ↔ a.used.getD ri₀ false = false := by
            unfold remainingOf
            rw [remainingFrom_mem]
            constructor
            · rintro ⟨j, hj, hcj, hu⟩
              have := nodup_getD_inj hnd hj hri₀ (hcj.trans hc0.symm)
              subst this; simpa using hu
            · intro hu; exact ⟨ri₀, hri₀, hc0, by simpa using hu⟩
          rw [flatMap_range_single _ res₀.length ri₀ hri₀]
          · rw [aciAccept_eq hxe (hlen ▸ hri₀), hcx, hc0]
            simp only [decide_true, Bool.and_true]
            rcases hu : a.used.getD ri₀ false with _ | _
            · have hacc : aciAccept elems res₀ a e ri₀ = true := by
                rw [aciAccept_eq hxe (hlen ▸ hri₀), hcx, hc0, hu]; simp
              simp only [hmem.2 hu, ↓reduceIte, Bool.not_false]
              rw [hrec ri₀ hacc]
              simp only [aciApply, hxg, hcx, herase ri₀ hri₀ hu, hc0]
            · have : c₀ ∉ remainingOf res₀ a.used := fun h => by
                rw [hmem] at h; rw [h] at hu; exact Bool.false_ne_true hu
              simp only [this, ↓reduceIte, Bool.not_true, Bool.false_eq_true, List.filterMap_nil]
          · intro j hj hne
            rw [aciAccept_eq hxe (hlen ▸ hj), hcx]
            have : res₀.getD j 0 ≠ c₀ := fun h => hne (nodup_getD_inj hnd hj hri₀ (h.trans hc0.symm))
            rw [List.getD_eq_getElem?_getD] at this
            simp [this]
        · have hno : c₀ ∉ remainingOf res₀ a.used := fun h => hc ((remainingFrom_sublist _ _ 0).subset h)
          simp only [hno, ↓reduceIte]
          symm
          rw [List.flatMap_eq_nil_iff]
          intro ri hri
          rw [List.mem_range] at hri
          rw [aciAccept_eq hxe (hlen ▸ hri), hcx]
          have : res₀.getD ri 0 ≠ c₀ := fun h => hc (h ▸ (by rw [List.getD_eq_getElem _ _ hri]; exact List.getElem_mem _))
          rw [List.getD_eq_getElem?_getD] at this
          simp [this]

/-- Theorem B for ACI: the frame's yields, after the leaf, are the executor's `decomposeACI`,
element for element, for every fuel, and with fuel for every yield the lists are equal. -/
theorem aciFrame_eq_decomposeACI (elems : List Var) (rest : Option Var) (res₀ : List C) (σ₀ : Binding)
    (hnd : res₀.Nodup) (hne : elems ≠ []) :
    (∀ k, ((aciOps elems res₀).drive k ((aciOps elems res₀).init (aciInit elems res₀ σ₀))).filterMap
        (aciLeaf res₀ rest) =
        (((aciOps elems res₀).enum 0 (aciInit elems res₀ σ₀)).take k).filterMap (aciLeaf res₀ rest)) ∧
    ∀ k, ((aciOps elems res₀).enum 0 (aciInit elems res₀ σ₀)).length ≤ k →
      ((aciOps elems res₀).drive k ((aciOps elems res₀).init (aciInit elems res₀ σ₀))).filterMap
        (aciLeaf res₀ rest) = decomposeACI elems rest res₀ σ₀ := by
  have hn : 0 < (aciOps elems res₀).n := by
    show 0 < elems.length; exact List.length_pos_iff.2 hne
  have hl := aciLaws elems res₀
  have h0 := aciGood_init elems res₀ σ₀
  have hdec : decomposeACI elems rest res₀ σ₀ =
      ((aciOps elems res₀).enum 0 (aciInit elems res₀ σ₀)).filterMap (aciLeaf res₀ rest) := by
    have := enum_eq_decomposeACI elems rest res₀ hnd _ 0 _ rfl h0
    rw [List.drop_zero] at this
    simpa [aciInit, remainingOf_replicate] using this
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [Ops.drive_eq_enum _ hl h0 hn]
  · rw [Ops.drive_eq_enum _ hl h0 hn, List.take_of_length_le hk, hdec]

/-- The set decomposition keeps a class binding it starts with. -/
theorem decomposeACI_cls (es : List Var) (rest : Option Var) :
    ∀ (res : List C) (σ σ' : Binding) (x : Var) (c : C),
      σ' ∈ decomposeACI es rest res σ → σ.cls x = some c → σ'.cls x = some c := by
  induction es with
  | nil =>
      intro res σ σ' x c h hx
      simp only [decomposeACI] at h
      cases rest with
      | none =>
          dsimp only at h
          split at h <;> simp at h
          exact h ▸ hx
      | some r => simp at h; subst h; exact hx
  | cons y es ih =>
      intro res σ σ' x c h hx
      simp only [decomposeACI] at h
      split at h
      · split at h
        · exact ih _ _ _ x c h hx
        · simp at h
      · rename_i hy
        rw [List.mem_flatMap] at h
        obtain ⟨d, _, h⟩ := h
        have hxy : x ≠ y := fun hxy => by subst hxy; rw [hy] at hx; simp at hx
        exact ih _ _ _ x c h (by rw [setCls_cls_ne _ _ _ _ hxy]; exact hx)

/-- The executor's set decomposition has no duplicate bindings when the entries are
distinct. -/
theorem decomposeACI_nodup (es : List Var) (rest : Option Var) :
    ∀ (res : List C) (σ : Binding), res.Nodup → (decomposeACI es rest res σ).Nodup := by
  induction es with
  | nil =>
      intro res σ _
      simp only [decomposeACI]
      cases rest with
      | none => dsimp only; split <;> simp
      | some r => simp
  | cons y es ih =>
      intro res σ hnd
      simp only [decomposeACI]
      split
      · split
        · exact ih _ _ (hnd.erase _)
        · exact List.nodup_nil
      · rw [List.nodup_flatMap]
        refine ⟨fun d _ => ih _ _ (hnd.erase _), ?_⟩
        refine hnd.imp ?_
        intro a b hab
        simp only [Function.onFun, List.disjoint_left]
        intro σ' ha hb
        have h1 := decomposeACI_cls es rest _ _ _ y a ha (setCls_cls_self' _ _ _)
        have h2 := decomposeACI_cls es rest _ _ _ y b hb (setCls_cls_self' _ _ _)
        rw [h1] at h2
        exact hab (Option.some.inj h2)

/-! ### The pre-fix search does not terminate

Three elements over two entries, each element accepting any entry not yet taken, no
rest. The store is the list of taken flags. After `[0, 1]` are taken the third element
finds nothing, the search undoes the second element and advances its index to 2; the
pre-fix scan restarts the second element from 0 and re-takes entry 1. -/

/-- The counterexample's store: three free elements over two entries. -/
def preFixOps : Ops (List Bool) where
  n := 3
  len := 2
  accept a _ ri := !a.getD ri true
  apply a _ ri := a.set ri true
  undo a _ ri := a.set ri false

theorem preFix_cycles :
    preFixOps.findStep false 0 ⟨[true, true], [0, 1, 0], 2⟩ = .cont ⟨[true, false], [0, 2, 0], 1⟩ ∧
    preFixOps.findStep false 0 ⟨[true, false], [0, 2, 0], 1⟩ = .cont ⟨[true, true], [0, 1, 0], 2⟩ := by
  constructor <;> rfl

/-- The pre-fix loop returns for no fuel on the cycle. -/
theorem preFix_diverges (k : Nat) :
    preFixOps.findLoop false 0 k ⟨[true, true], [0, 1, 0], 2⟩ = none ∧
    preFixOps.findLoop false 0 k ⟨[true, false], [0, 2, 0], 1⟩ = none := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := preFix_cycles
      constructor
      · simp only [Ops.findLoop, h1]; exact ih.2
      · simp only [Ops.findLoop, h2]; exact ih.1

/-- The fixed loop ends on the same state (the search fails: no third entry exists). -/
theorem preFix_fixed_ends :
    ∃ r, preFixOps.findFirst 0 ⟨[true, true], [0, 1, 0], 2⟩ = some r :=
  preFixOps.findFirst_terminates 0 _
    ⟨rfl, by decide,
      fun j hj => by dsimp only at hj; interval_cases j <;> decide, by decide,
      fun j hj => by
        dsimp only at hj
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl⟩

end Semper.EMatch.Cursor
