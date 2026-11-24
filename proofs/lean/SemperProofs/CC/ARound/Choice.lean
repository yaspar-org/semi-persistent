import SemperProofs.CC.ARound.Basic

/-!
# `a_round`: orientation, the least spelling and the choice of occurrence

The engine (`egraph.rs`, `fn a_round`) groups the sequence nodes of an
operator by class, canonicalizes each node's children with `find`, takes the
class's least spelling under `shortlex` (shorter first, ties broken
element-wise by class id), and orients every other spelling `l` of the class
into the rule `l → r`, `r` the least one (`shortlex l r = Greater`). For each
sequence node `buf` it then tries the rules in turn and applies the first one
that has an allowed occurrence: the least offset for `Both`, offset `0` for
`Left`, offset `len buf - len l` for `Right`; it applies one rewrite per node
per round.

This file proves:

* `isLeastSpelling_exists`, `isLeastSpelling_unique`: a nonempty set of
  spellings has exactly one least spelling, so the right-hand side is a
  function of the class; `rule_of_ne_least`: every other spelling is oriented
  towards it;
* `rewriteAt_shortlex`: a rewrite by an oriented rule strictly decreases the
  sequence in `shortlex`, and `orientedRewrite_wf`: chains of such rewrites
  are finite (`shortlex` is well-founded when the class ids are);
* `chooseOffset_sound`, `chooseOffset_complete`, `chooseOffset_first`: the
  engine's choice of offset is an allowed occurrence, exists whenever one
  does, and is the least one; `engineRewrite_aRStep`: the chosen rewrite is an
  instance of `ARStep`, so `aRStep_theq` applies to it;
* `firstRule_aRStep`, `firstRule_complete`: the same for the choice of the
  first rule with an occurrence.
-/

namespace SemperProofs.CC.ARound

variable {C : Type}

/-! ## Orientation -/

section Orientation

variable [LinearOrder C]

/-- The engine's order on canonical spellings (`fn shortlex`). -/
abbrev SL (s t : List C) : Prop := List.Shortlex (· < ·) s t

/-- `r` is the least spelling of the class whose spellings are `sps`. -/
def IsLeastSpelling (sps : Set (List C)) (r : List C) : Prop :=
  r ∈ sps ∧ ∀ t ∈ sps, ¬ SL t r

/-- The rules of a class: every spelling above the least one, oriented
towards it. -/
def ClassRules (sps : Set (List C)) : Set (List C × List C) :=
  {p | p.1 ∈ sps ∧ IsLeastSpelling sps p.2 ∧ SL p.2 p.1}

theorem sl_length_le {s t : List C} (h : SL s t) : s.length ≤ t.length := by
  rcases List.shortlex_def.mp h with h | ⟨h, -⟩ <;> omega

theorem sl_trichotomous (s t : List C) : SL s t ∨ s = t ∨ SL t s := by
  by_contra hc
  simp only [not_or] at hc
  exact hc.2.1 (Std.Trichotomous.trichotomous (r := List.Shortlex (· < · : C → C → Prop))
    s t hc.1 hc.2.2)

/-- **The least spelling exists**: every nonempty set of spellings has one,
when the class ids are well-ordered. -/
theorem isLeastSpelling_exists [WellFoundedLT C] {sps : Set (List C)} (h : sps.Nonempty) :
    ∃ r, IsLeastSpelling sps r := by
  obtain ⟨r, hr, hmin⟩ := (List.Shortlex.wf (wellFounded_lt (α := C))).has_min sps h
  exact ⟨r, hr, hmin⟩

/-- **The least spelling is unique**, so the rules are a function of the
class. -/
theorem isLeastSpelling_unique {sps : Set (List C)} {r r' : List C}
    (h : IsLeastSpelling sps r) (h' : IsLeastSpelling sps r') : r = r' := by
  rcases sl_trichotomous r r' with hl | he | hl
  · exact absurd hl (h'.2 r h.1)
  · exact he
  · exact absurd hl (h.2 r' h'.1)

/-- Every spelling other than the least one is the left-hand side of a rule
of its class. -/
theorem rule_of_ne_least {sps : Set (List C)} {l r : List C} (hr : IsLeastSpelling sps r)
    (hl : l ∈ sps) (hne : l ≠ r) : (l, r) ∈ ClassRules sps := by
  refine ⟨hl, hr, ?_⟩
  rcases sl_trichotomous r l with h | h | h
  · exact h
  · exact absurd h.symm hne
  · exact absurd h (hr.2 l hl)

theorem lex_append_right_of_length_eq {x y : List C} (hlen : x.length = y.length)
    (h : List.Lex (· < ·) x y) (t : List C) : List.Lex (· < ·) (x ++ t) (y ++ t) := by
  induction h with
  | nil => simp at hlen
  | cons _ ih => exact List.Lex.cons (ih (by simpa using hlen))
  | rel h => exact List.Lex.rel h

theorem sl_append_right {x y : List C} (h : SL x y) (t : List C) : SL (x ++ t) (y ++ t) := by
  rcases List.shortlex_def.mp h with h | ⟨hl, h⟩
  · exact List.Shortlex.of_length_lt (by simp; omega)
  · exact List.Shortlex.of_lex (by simp [hl]) (lex_append_right_of_length_eq hl h t)

/-- **An oriented rewrite decreases the sequence**: rewriting an occurrence
of `l` by `r` with `r` below `l` gives a sequence below `buf`. -/
theorem rewriteAt_shortlex {buf l r out : List C} {s : ℕ} (hlr : SL r l)
    (h : rewriteAt buf l r s = some out) : SL out buf := by
  obtain ⟨hb, ho⟩ := rewriteAt_split h
  rw [hb, ho]
  exact sl_append_right (List.Shortlex.append_left hlr _) _

/-- An oriented rewrite does not lengthen the sequence. -/
theorem rewriteAt_length_le {buf l r out : List C} {s : ℕ} (hlr : r.length ≤ l.length)
    (h : rewriteAt buf l r s = some out) : out.length ≤ buf.length := by
  obtain ⟨hb, ho⟩ := rewriteAt_split h
  have h1 := congrArg List.length hb
  have h2 := congrArg List.length ho
  simp only [List.length_append] at h1 h2
  omega

/-- **Rewriting terminates**: there is no infinite chain of rewrites by
oriented rules, whatever the rules and offsets. -/
theorem orientedRewrite_wf [WellFoundedLT C] :
    WellFounded (fun out buf : List C => ∃ l r s, SL r l ∧ rewriteAt buf l r s = some out) :=
  Subrelation.wf (fun ⟨_, _, _, hlr, h⟩ => rewriteAt_shortlex hlr h)
    (List.Shortlex.wf (wellFounded_lt (α := C)))

end Orientation

/-! ## The choice of occurrence -/

variable [DecidableEq C]

/-- `l` occurs in `buf` at offset `s`. -/
def OccAt (buf l : List C) (s : ℕ) : Prop := (buf.drop s).take l.length = l

instance (buf l : List C) (s : ℕ) : Decidable (OccAt buf l s) :=
  inferInstanceAs (Decidable (_ = _))

theorem rewriteAt_eq_some_iff {buf l r out : List C} {s : ℕ} :
    rewriteAt buf l r s = some out ↔
      OccAt buf l s ∧ out = buf.take s ++ r ++ buf.drop (s + l.length) := by
  unfold rewriteAt OccAt
  split_ifs with h <;> simp [h, eq_comm]

theorem rewriteAt_isSome_iff {buf l r : List C} {s : ℕ} :
    (rewriteAt buf l r s).isSome ↔ OccAt buf l s := by
  unfold rewriteAt OccAt
  split_ifs with h <;> simp [h]

omit [DecidableEq C] in
/-- An occurrence lies inside the sequence. -/
theorem OccAt.length_le {buf l : List C} {s : ℕ} (h : OccAt buf l s) :
    l.length ≤ buf.length - s := by
  have := congrArg List.length h
  simp only [List.length_take, List.length_drop] at this
  omega

/-- The least offset `i, i+1, …, i+fuel-1` at which `l` occurs. -/
def firstOcc (buf l : List C) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | i, fuel + 1 => if OccAt buf l i then some i else firstOcc buf l (i + 1) fuel

theorem firstOcc_spec {buf l : List C} {i fuel s : ℕ} (h : firstOcc buf l i fuel = some s) :
    i ≤ s ∧ s < i + fuel ∧ OccAt buf l s ∧ ∀ j, i ≤ j → j < s → ¬ OccAt buf l j := by
  induction fuel generalizing i with
  | zero => simp [firstOcc] at h
  | succ fuel ih =>
      simp only [firstOcc] at h
      split_ifs at h with ho
      · cases h; exact ⟨le_rfl, by omega, ho, fun j h1 h2 => by omega⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih h
        refine ⟨by omega, by omega, h3, fun j hj hjs => ?_⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · exact ho
        · exact h4 j hj hjs

theorem firstOcc_isSome {buf l : List C} {i fuel j : ℕ} (hij : i ≤ j) (hj : j < i + fuel)
    (h : OccAt buf l j) : (firstOcc buf l i fuel).isSome := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
      simp only [firstOcc]
      split_ifs with ho
      · rfl
      · rcases Nat.eq_or_lt_of_le hij with rfl | hij
        · exact absurd h ho
        · exact ih hij (by omega)

/-- The offset `a_round` rewrites (`found` in `fn a_round`): the first
occurrence for `Both`, the prefix for `Left`, the suffix for `Right`; none
when `l` is longer than `buf`. -/
def chooseOffset : Dir → List C → List C → Option ℕ
  | .both, buf, l =>
      if l.length ≤ buf.length then firstOcc buf l 0 (buf.length - l.length + 1) else none
  | .left, buf, l => if l.length ≤ buf.length ∧ OccAt buf l 0 then some 0 else none
  | .right, buf, l =>
      if l.length ≤ buf.length ∧ OccAt buf l (buf.length - l.length) then
        some (buf.length - l.length) else none

/-- The engine's rewrite of `buf` by `l → r`. -/
def engineRewrite (d : Dir) (buf l r : List C) : Option (List C) :=
  (chooseOffset d buf l).bind (rewriteAt buf l r)

/-- **The chosen offset is an allowed occurrence.** -/
theorem chooseOffset_sound {d : Dir} {buf l : List C} {s : ℕ}
    (h : chooseOffset d buf l = some s) : Allowed d buf.length l.length s ∧ OccAt buf l s := by
  cases d with
  | left =>
      simp only [chooseOffset] at h
      split_ifs at h with hc; cases h; exact ⟨rfl, hc.2⟩
  | right =>
      simp only [chooseOffset] at h
      split_ifs at h with hc; cases h; exact ⟨rfl, hc.2⟩
  | both =>
      simp only [chooseOffset] at h
      split_ifs at h
      exact ⟨trivial, (firstOcc_spec h).2.2.1⟩

/-- **An allowed occurrence is found**: if `l` occurs at an allowed offset,
the engine chooses some offset. -/
theorem chooseOffset_complete {d : Dir} {buf l : List C} {s : ℕ}
    (hs : Allowed d buf.length l.length s) (ho : OccAt buf l s) :
    (chooseOffset d buf l).isSome := by
  have hlen := ho.length_le
  cases d with
  | left =>
      cases hs
      have hc : l.length ≤ buf.length ∧ OccAt buf l 0 := ⟨by omega, ho⟩
      simp [chooseOffset, hc]
  | right =>
      cases hs
      have hc : l.length ≤ buf.length ∧ OccAt buf l (buf.length - l.length) := ⟨by omega, ho⟩
      simp [chooseOffset, hc]
  | both =>
      have hc : l.length ≤ buf.length := by omega
      simp only [chooseOffset, hc, ↓reduceIte]
      by_cases hsn : s ≤ buf.length - l.length
      · exact firstOcc_isSome (Nat.zero_le s) (by omega) ho
      · -- past the end only the empty sequence occurs, and it occurs at `0`
        have hl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hl
        exact firstOcc_isSome (j := 0) le_rfl (by omega) (by simp [OccAt])

/-- **First occurrence**: for `Both` the chosen offset is the least offset
at which `l` occurs. -/
theorem chooseOffset_first {buf l : List C} {s : ℕ} (h : chooseOffset .both buf l = some s) :
    ∀ j < s, ¬ OccAt buf l j := by
  simp only [chooseOffset] at h
  split_ifs at h
  exact fun j hj => (firstOcc_spec h).2.2.2 j (Nat.zero_le j) hj

/-- **The engine's rewrite is an `ARStep`.** -/
theorem engineRewrite_aRStep {d : Dir} {buf l r out : List C}
    (h : engineRewrite d buf l r = some out) : ARStep d buf l r out := by
  simp only [engineRewrite, Option.bind_eq_some_iff] at h
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, (chooseOffset_sound hs).1, h⟩

/-- **The engine rewrites whenever a step exists.** -/
theorem engineRewrite_complete {d : Dir} {buf l r out : List C} (h : ARStep d buf l r out) :
    ∃ out', engineRewrite d buf l r = some out' := by
  obtain ⟨s, hs, h⟩ := h
  have ho : OccAt buf l s := rewriteAt_isSome_iff.mp (by rw [h]; rfl)
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (chooseOffset_complete hs ho)
  obtain ⟨-, ho'⟩ := chooseOffset_sound hs'
  obtain ⟨out', h'⟩ := Option.isSome_iff_exists.mp (rewriteAt_isSome_iff (r := r).mpr ho')
  exact ⟨out', by simp [engineRewrite, hs', h']⟩

/-- For a fold the step is deterministic: the engine's rewrite is the
step. -/
theorem engineRewrite_fold {d : Dir} (hd : d ≠ .both) {buf l r out : List C}
    (h : ARStep d buf l r out) : engineRewrite d buf l r = some out := by
  obtain ⟨out', h'⟩ := engineRewrite_complete h
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨s', hs', h''⟩ := engineRewrite_aRStep h'
  cases d with
  | both => exact absurd rfl hd
  | left => cases hs; cases hs'; rw [h', ← h'', h]
  | right => cases hs; cases hs'; rw [h', ← h'', h]

/-- The rewrite by the first rule of `rules` that has an allowed occurrence
in `buf`: the loop over `rules` in `fn a_round`, which `break`s after one
rewrite. -/
def firstRule (d : Dir) (rules : List (List C × List C)) (buf : List C) : Option (List C) :=
  rules.findSome? (fun p => engineRewrite d buf p.1 p.2)

/-- **The first-rule rewrite is an `ARStep` by one of the rules.** -/
theorem firstRule_aRStep {d : Dir} {rules : List (List C × List C)} {buf out : List C}
    (h : firstRule d rules buf = some out) : ∃ p ∈ rules, ARStep d buf p.1 p.2 out := by
  obtain ⟨p, hp, h⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨p, hp, engineRewrite_aRStep h⟩

/-- **The engine rewrites `buf` whenever some rule has a step.** -/
theorem firstRule_complete {d : Dir} {rules : List (List C × List C)} {buf out : List C}
    {p : List C × List C} (hp : p ∈ rules) (h : ARStep d buf p.1 p.2 out) :
    (firstRule d rules buf).isSome := by
  obtain ⟨out', h'⟩ := engineRewrite_complete h
  simp only [firstRule, List.findSome?_isSome_iff]
  exact ⟨p, hp, by rw [h']; rfl⟩

/-- The first-rule rewrite by rules theory-equal under `S` is theory-equal
to `buf`. -/
theorem firstRule_theq {d : Dir} {S : Set (List C × List C)} {rules : List (List C × List C)}
    {buf out : List C} (hrules : ∀ p ∈ rules, Theq d S p.1 p.2)
    (h : firstRule d rules buf = some out) : Theq d S buf out := by
  obtain ⟨p, hp, h⟩ := firstRule_aRStep h
  exact aRStep_theq (hrules p hp) h

end SemperProofs.CC.ARound
