import Mathlib

/-!
# A-only inter-reduction (`a_round`): the step and the fold direction

`a_round` (`egraph.rs`, `fn a_round`) is completion's pass over sequence
nodes of an associative, non-commutative operator. Two sequence nodes of one
class give a ground string rule `l → r` (`r` the class's shortlex-least
spelling); an occurrence of `l` inside another sequence node `buf` of the same
operator is replaced by `r`, the result is added, and it is merged with `buf`.

The operator's `AssocDir` fixes what a sequence denotes and so where an
occurrence spells a subterm (commit `7beed39f`):

* `Both` (`:assoc`): the operator is associative, every contiguous run is a
  subterm, and any offset is rewritten;
* `Left` (`:assoc-left`): `[x₁, …, xₖ]` is the left fold `(…(x₁ x₂) …) xₖ`,
  only a prefix is a subterm, and only offset `0` is rewritten;
* `Right` (`:assoc-right`): the right fold `x₁ (… (xₖ₋₁ xₖ))`, only a suffix
  is a subterm, and only offset `len buf - len l` is rewritten.

This file proves:

* `rewrite_left_sound`, `rewrite_right_sound`: in every magma, the spine
  rewrite of a fold preserves the denotation of `buf` under any valuation
  under which `l` and `r` denote the same element;
* `rewrite_both_sound`: in every semigroup, the rewrite at any offset does;
* `den_both_eq_foldR`: in a semigroup the left and right fold agree, so the
  `Both` reading does not depend on the bracketing;
* `left_off_spine_unsound`, `right_off_spine_unsound`: for every length and
  every offset off the spine there is a sequence, a rule and a magma model
  (`ℤ` with `a - b`, resp. `b - a`) in which the rewrite changes the value;
  `aRStepAny_unsound_left`, `aRStepAny_unsound_right`: so the unrestricted
  step, the engine before `7beed39f` (fixture `ac_fold_completion_spine.egg`),
  is unsound;
* `aRound_sound`, `aRound_reachable_sound`: the invariant I2 of
  `completion_sound` (nodes of one class are theory-equal) is preserved by an
  `a_round` merge with the spine restriction.
-/

namespace SemperProofs.CC.ARound

/-- The associativity direction of an A-only operator (`AssocDir`). -/
inductive Dir where
  | left
  | right
  | both
  deriving DecidableEq, Repr

/-! ## Folds -/

section Folds

variable {α : Type*} [Mul α]

/-- The left fold of a nonempty list: `[x₁, …, xₖ] ↦ (…(x₁ x₂) …) xₖ`. -/
def foldL : List α → Option α
  | [] => none
  | x :: xs => some (xs.foldl (· * ·) x)

/-- The right fold of a nonempty list: `[x₁, …, xₖ] ↦ x₁ (… (xₖ₋₁ xₖ))`. -/
def foldR : List α → Option α
  | [] => none
  | [x] => some x
  | x :: y :: ys => (foldR (y :: ys)).map (x * ·)

@[simp] theorem foldL_nil : foldL ([] : List α) = none := rfl

@[simp] theorem foldR_nil : foldR ([] : List α) = none := rfl

theorem foldL_eq_none {xs : List α} : foldL xs = none ↔ xs = [] := by
  cases xs <;> simp [foldL]

theorem foldR_eq_none {xs : List α} : foldR xs = none ↔ xs = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp [foldR]
      | cons y ys => simp [foldR, ih]

theorem foldR_cons {x : α} {ys : List α} (h : ys ≠ []) :
    foldR (x :: ys) = (foldR ys).map (x * ·) := by
  cases ys with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- A left fold continues over an appended tail. -/
theorem foldL_append {xs : List α} (h : xs ≠ []) (ys : List α) :
    foldL (xs ++ ys) = (foldL xs).map (fun a => ys.foldl (· * ·) a) := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs => simp [foldL, List.foldl_append]

/-- A right fold continues over a prepended head. -/
theorem foldR_append (pre : List α) {ys : List α} (h : ys ≠ []) :
    foldR (pre ++ ys) = (foldR ys).map (fun a => pre.foldr (· * ·) a) := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
      rw [List.cons_append, foldR_cons (by simp [h]), ih, Option.map_map]
      rfl

end Folds

/-- Partial multiplication on `Option`: `none` is a unit. -/
def omul {α : Type*} [Mul α] : Option α → Option α → Option α
  | none, b => b
  | some a, none => some a
  | some a, some b => some (a * b)

section Semigroup

variable {α : Type*} [Semigroup α]

theorem foldl_mul_left (a b : α) (l : List α) :
    l.foldl (· * ·) (a * b) = a * l.foldl (· * ·) b := by
  induction l generalizing b with
  | nil => rfl
  | cons z l ih => simp only [List.foldl_cons, mul_assoc, ih]

/-- In a semigroup the left fold of a concatenation is the product of the
folds. -/
theorem foldL_append_semi (xs ys : List α) :
    foldL (xs ++ ys) = omul (foldL xs) (foldL ys) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases ys with
      | nil => simp [foldL, omul]
      | cons y ys =>
          simp only [List.cons_append, foldL, omul, List.foldl_append, List.foldl_cons]
          rw [foldl_mul_left]

/-- In a semigroup the left and the right fold agree. -/
theorem foldL_eq_foldR (xs : List α) : foldL xs = foldR xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          rw [foldR_cons (by simp), ← ih,
            show x :: y :: ys = [x] ++ y :: ys from rfl, foldL_append_semi]
          simp [foldL, omul]

end Semigroup

/-! ## Sequences of classes and the rewrite step -/

variable {C : Type}

/-- The element a sequence of classes denotes under the valuation `v`. -/
def den {α : Type*} [Mul α] : Dir → (C → α) → List C → Option α
  | .left, v, s => foldL (s.map v)
  | .right, v, s => foldR (s.map v)
  | .both, v, s => foldL (s.map v)

/-- `Both` reads a sequence under any bracketing: in a semigroup its
denotation is also the right fold. -/
theorem den_both_eq_foldR {α : Type*} [Semigroup α] (v : C → α) (s : List C) :
    den .both v s = foldR (s.map v) :=
  foldL_eq_foldR _

variable [DecidableEq C]

/-- Replace the occurrence of `l` at offset `s` of `buf` by `r`, if `l`
occurs there (`buf[s..s+len l] == l`). -/
def rewriteAt (buf l r : List C) (s : ℕ) : Option (List C) :=
  if (buf.drop s).take l.length = l then
    some (buf.take s ++ r ++ buf.drop (s + l.length))
  else none

/-- The offsets `a_round` rewrites for each direction (commit `7beed39f`). -/
def Allowed : Dir → ℕ → ℕ → ℕ → Prop
  | .both, _, _, _ => True
  | .left, _, _, s => s = 0
  | .right, n, k, s => s = n - k

/-- One `a_round` rewrite of `buf` by the rule `l → r`. -/
def ARStep (d : Dir) (buf l r out : List C) : Prop :=
  ∃ s, Allowed d buf.length l.length s ∧ rewriteAt buf l r s = some out

/-- The unrestricted step of the engine before `7beed39f`: any offset. -/
def ARStepAny (buf l r out : List C) : Prop :=
  ∃ s, rewriteAt buf l r s = some out

theorem rewriteAt_split {buf l r out : List C} {s : ℕ} (h : rewriteAt buf l r s = some out) :
    buf = buf.take s ++ l ++ buf.drop (s + l.length) ∧
      out = buf.take s ++ r ++ buf.drop (s + l.length) := by
  unfold rewriteAt at h
  split_ifs at h with hm
  refine ⟨?_, (Option.some.inj h).symm⟩
  conv_lhs => rw [← List.take_append_drop s buf, ← List.take_append_drop l.length (buf.drop s)]
  rw [hm, List.drop_drop, List.append_assoc]

/-! ## Soundness of the step -/

section Sound

variable {α : Type*}

/-- **Left fold, prefix rewrite**: in every magma, rewriting the prefix `l`
of `buf` to `r` preserves the left fold when `l` and `r` agree. -/
theorem rewrite_left_sound [Mul α] (v : C → α) {buf l r out : List C}
    (hlr : den .left v l = den .left v r) (h : rewriteAt buf l r 0 = some out) :
    den .left v out = den .left v buf := by
  obtain ⟨hb, ho⟩ := rewriteAt_split h
  simp only [List.take_zero, List.nil_append, zero_add] at hb ho
  rw [hb, ho]
  simp only [den, List.map_append] at hlr ⊢
  by_cases hl : l = []
  · subst hl
    have hr : r = [] := by simpa [foldL_eq_none] using hlr.symm
    subst hr; rfl
  · have hr : r ≠ [] := by
      intro hr; subst hr; simp [foldL_eq_none, hl] at hlr
    rw [foldL_append (by simpa using hr), foldL_append (by simpa using hl), hlr]

/-- **Right fold, suffix rewrite**: in every magma, rewriting the suffix `l`
of `buf` to `r` preserves the right fold when `l` and `r` agree. -/
theorem rewrite_right_sound [Mul α] (v : C → α) {buf l r out : List C}
    (hlr : den .right v l = den .right v r)
    (h : rewriteAt buf l r (buf.length - l.length) = some out) :
    den .right v out = den .right v buf := by
  obtain ⟨hb, ho⟩ := rewriteAt_split h
  have hlen := congrArg List.length hb
  simp only [List.length_append, List.length_take, List.length_drop] at hlen
  have hd : buf.drop (buf.length - l.length + l.length) = [] := by
    simp only [List.drop_eq_nil_iff]; omega
  rw [hd, List.append_nil] at hb ho
  rw [hb, ho]
  simp only [den, List.map_append] at hlr ⊢
  by_cases hl : l = []
  · subst hl
    have hr : r = [] := by simpa [foldR_eq_none] using hlr.symm
    subst hr; rfl
  · have hr : r ≠ [] := by
      intro hr; subst hr; simp [foldR_eq_none, hl] at hlr
    rw [foldR_append _ (by simpa using hr), foldR_append _ (by simpa using hl), hlr]

/-- **Associative operator, any offset**: in every semigroup, rewriting any
occurrence of `l` in `buf` to `r` preserves the denotation when `l` and `r`
agree. -/
theorem rewrite_both_sound [Semigroup α] (v : C → α) {buf l r out : List C} {s : ℕ}
    (hlr : den .both v l = den .both v r) (h : rewriteAt buf l r s = some out) :
    den .both v out = den .both v buf := by
  obtain ⟨hb, ho⟩ := rewriteAt_split h
  rw [hb, ho]
  simp only [den, List.map_append, foldL_append_semi] at hlr ⊢
  rw [hlr]

/-- The restricted step is sound in every model of its direction: every
magma for a fold, every semigroup for `Both`. -/
theorem aRStep_sound_left [Mul α] (v : C → α) {buf l r out : List C}
    (hlr : den .left v l = den .left v r) (h : ARStep .left buf l r out) :
    den .left v out = den .left v buf := by
  obtain ⟨s, hs, h⟩ := h
  cases hs
  exact rewrite_left_sound v hlr h

theorem aRStep_sound_right [Mul α] (v : C → α) {buf l r out : List C}
    (hlr : den .right v l = den .right v r) (h : ARStep .right buf l r out) :
    den .right v out = den .right v buf := by
  obtain ⟨s, hs, h⟩ := h
  cases hs
  exact rewrite_right_sound v hlr h

theorem aRStep_sound_both [Semigroup α] (v : C → α) {buf l r out : List C}
    (hlr : den .both v l = den .both v r) (h : ARStep .both buf l r out) :
    den .both v out = den .both v buf := by
  obtain ⟨s, -, h⟩ := h
  exact rewrite_both_sound v hlr h

end Sound

/-! ## Theory equality -/

/-- The valuation `v` satisfies the asserted sequence equations `S`. -/
def Sat {α : Type*} [Mul α] (d : Dir) (v : C → α) (S : Set (List C × List C)) : Prop :=
  ∀ p ∈ S, den d v p.1 = den d v p.2

/-- Theory equality of two sequences of an operator of direction `d` under
the asserted equations `S`: equal denotation in every model of `S`, where a
model is a magma for a fold and a semigroup for `Both`. -/
def Theq (d : Dir) (S : Set (List C × List C)) (s t : List C) : Prop :=
  match d with
  | .left => ∀ (α : Type) [Mul α] (v : C → α), Sat .left v S → den .left v s = den .left v t
  | .right => ∀ (α : Type) [Mul α] (v : C → α), Sat .right v S → den .right v s = den .right v t
  | .both => ∀ (α : Type) [Semigroup α] (v : C → α), Sat .both v S → den .both v s = den .both v t

omit [DecidableEq C] in
theorem Theq.refl (d : Dir) (S : Set (List C × List C)) (s : List C) : Theq d S s s := by
  cases d <;> intro _ _ _ _ <;> rfl

omit [DecidableEq C] in
theorem Theq.symm {d : Dir} {S : Set (List C × List C)} {s t : List C}
    (h : Theq d S s t) : Theq d S t s := by
  cases d <;> intro α _ v hv <;> exact (h α v hv).symm

omit [DecidableEq C] in
theorem Theq.trans {d : Dir} {S : Set (List C × List C)} {s t u : List C}
    (h₁ : Theq d S s t) (h₂ : Theq d S t u) : Theq d S s u := by
  cases d <;> intro α _ v hv <;> exact (h₁ α v hv).trans (h₂ α v hv)

/-- The restricted step relates theory-equal sequences. -/
theorem aRStep_theq {d : Dir} {S : Set (List C × List C)} {buf l r out : List C}
    (hlr : Theq d S l r) (h : ARStep d buf l r out) : Theq d S buf out := by
  cases d
  · intro α _ v hv; exact (aRStep_sound_left v (hlr α v hv) h).symm
  · intro α _ v hv; exact (aRStep_sound_right v (hlr α v hv) h).symm
  · intro α _ v hv; exact (aRStep_sound_both v (hlr α v hv) h).symm

/-! ## Counter-models: rewriting a fold off its spine -/

/-- `ℤ` with `a * b = a - b`: a magma in which the left fold of `[x, a, b]`
is `x - a - b`. -/
@[ext] structure SubL where
  val : ℤ

instance : Mul SubL := ⟨fun a b => ⟨a.val - b.val⟩⟩

@[simp] theorem SubL.mul_val (a b : SubL) : (a * b).val = a.val - b.val := rfl

/-- `ℤ` with `a * b = b - a`: a magma in which the right fold of
`[a, b, x]` is `x - b - a`. -/
@[ext] structure SubR where
  val : ℤ

instance : Mul SubR := ⟨fun a b => ⟨b.val - a.val⟩⟩

@[simp] theorem SubR.mul_val (a b : SubR) : (a * b).val = b.val - a.val := rfl

/-- Class `i` has the `i`-th value of `xs`, `0` past its end. -/
def valOf (xs : List ℤ) (i : ℕ) : ℤ := xs.getD i 0

/-- The left-fold witness valuation: `A, B, C, D = 5, 3, 2, 0` (classes
`1..4`), `0` for class `0`. -/
def vL (i : ℕ) : SubL := ⟨valOf [0, 5, 3, 2, 0] i⟩

/-- The right-fold witness valuation: `A, B, C, D = 3, 5, 0, 2`. -/
def vR (i : ℕ) : SubR := ⟨valOf [0, 3, 5, 0, 2] i⟩

theorem subL_foldl_zero (a : SubL) (k : ℕ) :
    (List.replicate k (⟨0⟩ : SubL)).foldl (· * ·) a = a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      ext; simp

theorem subR_foldr_zero (a : SubR) (k : ℕ) :
    (List.replicate k (⟨0⟩ : SubR)).foldr (· * ·) a = a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.foldr_cons, ih]
      ext; simp

theorem subR_foldR_zero (k : ℕ) :
    foldR (List.replicate (k + 1) (⟨0⟩ : SubR)) = some ⟨0⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, foldR_cons (by simp), ih]
      congr 1

theorem rewriteAt_mid (s k : ℕ) (a b : ℕ) (r : List ℕ) :
    rewriteAt (List.replicate s 0 ++ [a, b] ++ List.replicate k 0) [a, b] r s =
      some (List.replicate s 0 ++ r ++ List.replicate k 0) := by
  have h1 : (List.replicate s 0 ++ [a, b] ++ List.replicate k 0).drop s =
      [a, b] ++ List.replicate k 0 := by
    rw [List.append_assoc, List.drop_left' (by simp)]
  have h2 : (List.replicate s 0 ++ [a, b] ++ List.replicate k 0).take s = List.replicate s 0 := by
    rw [List.append_assoc, List.take_left' (by simp)]
  have h3 : (List.replicate s 0 ++ [a, b] ++ List.replicate k 0).drop (s + 2) =
      List.replicate k 0 := by
    rw [← List.drop_drop, h1]; rfl
  change (if (_ : List ℕ).take 2 = [a, b] then
    some (List.take s _ ++ r ++ List.drop (s + 2) _) else none) = _
  rw [h1, h2, h3]
  simp

/-- **A left fold rewritten off its spine is unsound**: for every length
`n` and every offset `s ≠ 0` with room for a two-element rule, there are a
sequence `buf` of length `n` and a rule `l → r` whose rewrite at `s` relates
sequences that are not theory-equal under `l = r`. The witness model is `ℤ`
with subtraction and `A, B, C, D = 5, 3, 2, 0` (`A - B = C - D`), the zero
class elsewhere: `buf` folds to `p - 8`, the rewrite to `p - 2`. -/
theorem left_off_spine_unsound (n s : ℕ) (hs : s ≠ 0) (hn : s + 2 ≤ n) :
    ∃ buf l r out : List ℕ, buf.length = n ∧ rewriteAt buf l r s = some out ∧
      ¬ Theq .left {(l, r)} buf out := by
  obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + k := ⟨n - (s + 2), by omega⟩
  refine ⟨List.replicate s 0 ++ [1, 2] ++ List.replicate k 0, [1, 2], [3, 4],
    List.replicate s 0 ++ [3, 4] ++ List.replicate k 0, by simp; omega,
    rewriteAt_mid s k 1 2 [3, 4], ?_⟩
  intro h
  have hv : Sat .left vL {(([1, 2] : List ℕ), ([3, 4] : List ℕ))} := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    simp only [den, List.map, foldL, List.foldl, Option.some.injEq]
    ext; simp [vL, valOf]
  have key := h SubL vL hv
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  simp only [den, List.map_append, List.map_replicate, show vL 0 = ⟨0⟩ from rfl] at key
  rw [foldL_append (by simp), foldL_append (by simp), foldL_append (by simp),
    foldL_append (by simp)] at key
  simp only [List.replicate_succ, foldL, Option.map_some, subL_foldl_zero,
    Option.some.injEq] at key
  have := congrArg (fun x => x.val) key
  simp [vL, valOf] at this

/-- **A right fold rewritten off its spine is unsound**: for every length
`n` and every offset `s` other than `n - 2`, the last one for a two-element
rule, there are a sequence of length `n` and a rule whose rewrite at `s`
relates sequences that are not theory-equal. The witness model is `ℤ` with
`a * b = b - a` and `A, B, C, D = 3, 5, 0, 2`: `buf` folds to `q - 8`, the
rewrite to `q - 2`. -/
theorem right_off_spine_unsound (n s : ℕ) (hs : s + 2 < n) :
    ∃ buf l r out : List ℕ, buf.length = n ∧ rewriteAt buf l r s = some out ∧
      ¬ Theq .right {(l, r)} buf out := by
  obtain ⟨k, rfl⟩ : ∃ k, n = s + 2 + (k + 1) := ⟨n - (s + 3), by omega⟩
  refine ⟨List.replicate s 0 ++ [1, 2] ++ List.replicate (k + 1) 0, [1, 2], [3, 4],
    List.replicate s 0 ++ [3, 4] ++ List.replicate (k + 1) 0, by simp; omega,
    rewriteAt_mid s (k + 1) 1 2 [3, 4], ?_⟩
  intro h
  have hv : Sat .right vR {(([1, 2] : List ℕ), ([3, 4] : List ℕ))} := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    simp only [den, List.map, foldR, Option.map_some, Option.some.injEq]
    ext; simp [vR, valOf]
  have key := h SubR vR hv
  simp only [den, List.map_append, List.map_replicate, show vR 0 = ⟨0⟩ from rfl] at key
  rw [List.append_assoc, List.append_assoc, foldR_append _ (by simp),
    foldR_append _ (by simp), foldR_append _ (by simp), foldR_append _ (by simp),
    subR_foldR_zero] at key
  simp only [Option.map_some, subR_foldr_zero, Option.some.injEq] at key
  have := congrArg (fun x => x.val) key
  simp [vR, valOf] at this

/-- The unrestricted step (any offset, the engine before `7beed39f`) is
unsound for a left fold: `[X, A, B]` rewritten by `A B → C D`. -/
theorem aRStepAny_unsound_left :
    ∃ buf l r out : List ℕ, ARStepAny buf l r out ∧ ¬ Theq .left {(l, r)} buf out := by
  obtain ⟨buf, l, r, out, -, h, hn⟩ := left_off_spine_unsound 3 1 one_ne_zero le_rfl
  exact ⟨buf, l, r, out, ⟨1, h⟩, hn⟩

/-- The same for a right fold: `[A, B, X]` rewritten by `A B → C D`. -/
theorem aRStepAny_unsound_right :
    ∃ buf l r out : List ℕ, ARStepAny buf l r out ∧ ¬ Theq .right {(l, r)} buf out := by
  obtain ⟨buf, l, r, out, -, h, hn⟩ := right_off_spine_unsound 3 0 (by norm_num)
  exact ⟨buf, l, r, out, ⟨0, h⟩, hn⟩

/-! ## The completion invariant -/

/-- The sequence nodes of one A-only operator in a completion state: the
union-find `find` and the nodes as pairs `(children, class)`, as in
`SemperProofs.CC.State`. -/
structure AState (C : Type) where
  find : C → C
  nodes : Set (List C × C)

namespace AState

variable (st : AState C)

def merge (a b : C) : AState C :=
  { st with find := fun x => if st.find x = st.find a then st.find b else st.find x }

def addNode (s : List C) (c : C) : AState C :=
  { st with nodes := insert (s, c) st.nodes }

/-- A class is fresh when no node is in it. -/
def Fresh (e : C) : Prop := ∀ s c, (s, c) ∈ st.nodes → st.find c ≠ st.find e

end AState

/-- I2 for the sequence nodes: two nodes of one class are theory-equal. -/
def I2 (d : Dir) (S : Set (List C × List C)) (st : AState C) : Prop :=
  ∀ s c s' c', (s, c) ∈ st.nodes → (s', c') ∈ st.nodes → st.find c = st.find c' → Theq d S s s'

/-- One `a_round` merge with the spine restriction: the rule `l → r` comes
from two nodes of one class, `buf` is a node, `out` its rewrite; `out` is
added (to a fresh class `e`, or it is already the node `(out, e)`) and `e`
is merged with `buf`'s class. -/
inductive ARoundStep (d : Dir) : AState C → AState C → Prop
  | merge {st : AState C} {l r buf out : List C} {c₁ c₂ g e : C} :
      (l, c₁) ∈ st.nodes → (r, c₂) ∈ st.nodes → st.find c₁ = st.find c₂ →
      (buf, g) ∈ st.nodes → ARStep d buf l r out → (st.Fresh e ∨ (out, e) ∈ st.nodes) →
      ARoundStep d st ((st.addNode out e).merge e g)

/-- **An `a_round` merge preserves I2.** -/
theorem aRound_sound {d : Dir} {S : Set (List C × List C)} {st st' : AState C}
    (hstep : ARoundStep d st st') (h : I2 d S st) : I2 d S st' := by
  obtain ⟨hl, hr, hc, hb, hstep, he⟩ := hstep
  rename_i l r buf out c₁ c₂ g e
  have hbo : Theq d S buf out := aRStep_theq (h _ _ _ _ hl hr hc) hstep
  -- a node of the new state in `e`'s class is theory-equal to `out`
  have hE : ∀ s c, (s, c) ∈ insert (out, e) st.nodes → st.find c = st.find e →
      Theq d S s out := by
    intro s c hsc hce
    rcases Set.mem_insert_iff.mp hsc with heq | hsc
    · cases heq; exact Theq.refl _ _ _
    · rcases he with hf | hin
      · exact absurd hce (hf s c hsc)
      · exact h _ _ _ _ hsc hin hce
  -- a node of the new state outside `e`'s class is an old node
  have hO : ∀ s c, (s, c) ∈ insert (out, e) st.nodes → st.find c ≠ st.find e →
      (s, c) ∈ st.nodes := by
    intro s c hsc hce
    rcases Set.mem_insert_iff.mp hsc with heq | hsc
    · cases heq; exact absurd rfl hce
    · exact hsc
  intro s c s' c' hsc hsc' hcc
  simp only [AState.merge, AState.addNode] at hsc hsc' hcc
  by_cases h1 : st.find c = st.find e <;> by_cases h2 : st.find c' = st.find e <;>
    simp only [h1, h2, ↓reduceIte] at hcc
  · exact (hE s c hsc h1).trans (hE s' c' hsc' h2).symm
  · exact (hE s c hsc h1).trans (hbo.symm.trans (h _ _ _ _ hb (hO s' c' hsc' h2) hcc))
  · exact (h _ _ _ _ (hO s c hsc h1) hb hcc).trans (hbo.trans (hE s' c' hsc' h2).symm)
  · exact h _ _ _ _ (hO s c hsc h1) (hO s' c' hsc' h2) hcc

/-- I2 holds in every state a sequence of `a_round` merges reaches. -/
theorem aRound_reachable_sound {d : Dir} {S : Set (List C × List C)} {st₀ st : AState C}
    (hreach : Relation.ReflTransGen (ARoundStep d) st₀ st) (h₀ : I2 d S st₀) : I2 d S st := by
  induction hreach with
  | refl => exact h₀
  | tail _ hs ih => exact aRound_sound hs ih

end SemperProofs.CC.ARound
