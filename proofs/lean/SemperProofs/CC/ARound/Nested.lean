import SemperProofs.CC.ARound.Basic

/-!
# Nested same-operator children and build-time splicing

A child of an `f`-sequence is a class. When every member of that class is an
`f`-sequence node (`pure_seq_node`), the class is an `f`-node child, and the
engine splices it at build time (`flatten_seq_children`): the child is
replaced by the children of the least such node, at the first position for
`Left`, the last for `Right`, any position for `Both`, to a fixpoint.

Here `sp p = some u` says that the class `p` is pure with spelling `u`. A
model of an `f`-node child gives it the value of its spelling: the equations
`SpEqs sp` (`[p] = u`). A splice is then the rewrite of `[p]` by `u` at an
allowed offset, an `ARStep` with the rule `[p] → u`, and the soundness of the
step applies to it.

This file proves:

* `splice_den_left`, `splice_den_right`, `splice_den_both`: splicing an
  `f`-node child on the spine preserves the denotation, under every valuation
  that gives each pure class the value of its spelling (every magma for a
  fold, every semigroup for `Both`);
* `splice_theq`, `spliceStar_theq`: so a spliced sequence is theory-equal to
  the written one, and `aRound_spliced_sound`: an `a_round` rewrite of a
  spliced node, followed by the splicing in `add`, relates theory-equal
  sequences;
* `aRStep_spineImpure`, `spineImpure_no_splice`: when the spine of `buf` and
  of the least spelling `r` hold no pure class (the state after build-time
  splicing), neither does the spine of `out`, so `add` splices nothing in the
  rewritten sequence;
* `splice_off_spine_unsound_left`, `splice_off_spine_unsound_right`: splicing
  a nested child off the spine of a fold is unsound (`ℤ` with `a - b`, resp.
  `b - a`). The same failure for the e-matching views is
  `Semper.EMatch.Flatten.fold_open_off_spine_unsound`.
-/

namespace SemperProofs.CC.ARound

variable {C : Type} [DecidableEq C]

/-- The equations of the `f`-node children: a pure class equals its
spelling. -/
def SpEqs (sp : C → Option (List C)) : Set (List C × List C) :=
  {q | ∃ p, sp p = some q.2 ∧ q.1 = [p]}

/-- One build-time splice of an `f`-node child at an allowed position. -/
def Splice (d : Dir) (sp : C → Option (List C)) (s t : List C) : Prop :=
  ∃ p u, sp p = some u ∧ ARStep d s [p] u t

/-- **Left fold**: splicing the first child preserves the left fold, in every
magma, when each pure class has the value of its spelling. -/
theorem splice_den_left {α : Type*} [Mul α] {sp : C → Option (List C)} (v : C → α)
    (hv : ∀ p u, sp p = some u → den .left v u = some (v p)) {s t : List C}
    (h : Splice .left sp s t) : den .left v t = den .left v s := by
  obtain ⟨p, u, hp, h⟩ := h
  exact aRStep_sound_left v (by rw [hv p u hp]; rfl) h

/-- **Right fold**: splicing the last child preserves the right fold. -/
theorem splice_den_right {α : Type*} [Mul α] {sp : C → Option (List C)} (v : C → α)
    (hv : ∀ p u, sp p = some u → den .right v u = some (v p)) {s t : List C}
    (h : Splice .right sp s t) : den .right v t = den .right v s := by
  obtain ⟨p, u, hp, h⟩ := h
  exact aRStep_sound_right v (by rw [hv p u hp]; rfl) h

/-- **Associative operator**: splicing any child preserves the
denotation, in every semigroup. -/
theorem splice_den_both {α : Type*} [Semigroup α] {sp : C → Option (List C)} (v : C → α)
    (hv : ∀ p u, sp p = some u → den .both v u = some (v p)) {s t : List C}
    (h : Splice .both sp s t) : den .both v t = den .both v s := by
  obtain ⟨p, u, hp, h⟩ := h
  exact aRStep_sound_both v (by rw [hv p u hp]; rfl) h

theorem splice_theq {d : Dir} {sp : C → Option (List C)} {S : Set (List C × List C)}
    (hS : SpEqs sp ⊆ S) {s t : List C} (h : Splice d sp s t) : Theq d S s t := by
  obtain ⟨p, u, hp, h⟩ := h
  have hpu : Theq d S [p] u := by
    have hm : ([p], u) ∈ S := hS ⟨p, hp, rfl⟩
    cases d <;> intro α _ v hv <;> exact hv _ hm
  exact aRStep_theq hpu h

/-- Splicing to a fixpoint yields a theory-equal sequence. -/
theorem spliceStar_theq {d : Dir} {sp : C → Option (List C)} {S : Set (List C × List C)}
    (hS : SpEqs sp ⊆ S) {s t : List C} (h : Relation.ReflTransGen (Splice d sp) s t) :
    Theq d S s t := by
  induction h with
  | refl => exact Theq.refl _ _ _
  | tail _ hst ih => exact ih.trans (splice_theq hS hst)

/-- **`a_round` on spliced sequences is sound**: `buf` is the spliced form of
the written `buf₀`, `out` is its rewrite by a rule `l → r` of theory-equal
sides, and `out'` the spliced form `add` stores; then `buf₀` and `out'` are
theory-equal. -/
theorem aRound_spliced_sound {d : Dir} {sp : C → Option (List C)}
    {S : Set (List C × List C)} (hS : SpEqs sp ⊆ S) {buf₀ buf l r out out' : List C}
    (h₀ : Relation.ReflTransGen (Splice d sp) buf₀ buf) (hlr : Theq d S l r)
    (hstep : ARStep d buf l r out) (h₁ : Relation.ReflTransGen (Splice d sp) out out') :
    Theq d S buf₀ out' :=
  (spliceStar_theq hS h₀).trans ((aRStep_theq hlr hstep).trans (spliceStar_theq hS h₁))

/-- The spine of `s` holds no pure class: its first element for `Left`, its
last for `Right`, every element for `Both`. -/
def SpineImpure (d : Dir) (sp : C → Option (List C)) (s : List C) : Prop :=
  match d with
  | .left => ∀ x ∈ s.head?, sp x = none
  | .right => ∀ x ∈ s.getLast?, sp x = none
  | .both => ∀ x ∈ s, sp x = none

/-- A sequence whose spine holds no pure class is not spliced. -/
theorem spineImpure_no_splice {d : Dir} {sp : C → Option (List C)} {s t : List C}
    (h : SpineImpure d sp s) : ¬ Splice d sp s t := by
  rintro ⟨p, u, hp, s', hs', hr⟩
  obtain ⟨hb, -⟩ := rewriteAt_split hr
  cases d with
  | left =>
      cases hs'
      have : s.head? = some p := by rw [hb]; simp
      simp [h p this] at hp
  | right =>
      cases hs'
      have hlen := congrArg List.length hb
      simp only [List.length_append, List.length_take, List.length_drop,
        List.length_singleton] at hlen
      have hd : s.drop (s.length - 1 + 1) = [] := by simp only [List.drop_eq_nil_iff]; omega
      rw [List.length_singleton, hd, List.append_nil] at hb
      have : s.getLast? = some p := by rw [hb]; simp
      simp [h p this] at hp
  | both =>
      have : p ∈ s := by rw [hb]; simp
      simp [h p this] at hp

/-- **The rewritten sequence needs no splicing**: if the spines of `buf`
and of the nonempty right-hand side `r` hold no pure class, neither does the
spine of `out`. -/
theorem aRStep_spineImpure {d : Dir} {sp : C → Option (List C)} {buf l r out : List C}
    (hr0 : r ≠ []) (hb : SpineImpure d sp buf) (hr : SpineImpure d sp r)
    (h : ARStep d buf l r out) : SpineImpure d sp out := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨hbuf, ho⟩ := rewriteAt_split h
  cases d with
  | left =>
      cases hs
      simp only [List.take_zero, List.nil_append, zero_add] at ho
      intro x hx
      rw [ho, List.head?_append_of_ne_nil _ hr0] at hx
      exact hr x hx
  | right =>
      cases hs
      have hlen := congrArg List.length hbuf
      simp only [List.length_append, List.length_take, List.length_drop] at hlen
      have hd : buf.drop (buf.length - l.length + l.length) = [] := by
        simp only [List.drop_eq_nil_iff]; omega
      rw [hd, List.append_nil] at ho
      intro x hx
      rw [ho, List.getLast?_append_of_ne_nil _ hr0] at hx
      exact hr x hx
  | both =>
      intro x hx
      rw [ho] at hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hb x (List.mem_of_mem_take hx)
      · exact hr x hx
      · exact hb x (List.mem_of_mem_drop hx)

/-! ## Counter-models: splicing off the spine of a fold -/

/-- Class `2` is pure with spelling `[3, 4]`. -/
def spEx : ℕ → Option (List ℕ) := fun p => if p = 2 then some [3, 4] else none

theorem spEqs_spEx : SpEqs spEx = {(([2] : List ℕ), ([3, 4] : List ℕ))} := by
  ext ⟨a, b⟩
  simp only [SpEqs, spEx, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    split_ifs at hp with h
    · subst h; cases hp; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨2, by simp, rfl⟩

/-- **Splicing a left fold off its spine is unsound**: `[x, p]` is
`x (p)`, and splicing `p = a b` at offset `1` gives `[x, a, b]`, the term
`(x a) b`. In `ℤ` with `a - b`, `x, a, b = 0, 5, 3`: `0 - 2 ≠ 0 - 5 - 3`. -/
theorem splice_off_spine_unsound_left :
    rewriteAt [1, 2] [2] [3, 4] 1 = some [1, 3, 4] ∧ spEx 2 = some [3, 4] ∧
      ¬ Theq .left (SpEqs spEx) [1, 2] [1, 3, 4] := by
  refine ⟨by decide, rfl, fun h => ?_⟩
  let v : ℕ → SubL := fun i => ⟨valOf [0, 0, 2, 5, 3] i⟩
  have hv : Sat .left v (SpEqs spEx) := by
    rw [spEqs_spEx]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    simp only [den, List.map, foldL, List.foldl, Option.some.injEq]
    ext; simp [v, valOf]
  have key := h SubL v hv
  simp only [den, List.map, foldL, List.foldl, Option.some.injEq] at key
  have := congrArg SubL.val key
  simp [v, valOf] at this

/-- **Splicing a right fold off its spine is unsound**: `[p, x]` is `(p) x`,
and splicing `p = a b` at offset `0` gives `[a, b, x]`, the term `a (b x)`.
In `ℤ` with `a * b = b - a`, `x, a, b = 0, 5, 3`. -/
theorem splice_off_spine_unsound_right :
    rewriteAt [2, 1] [2] [3, 4] 0 = some [3, 4, 1] ∧ spEx 2 = some [3, 4] ∧
      ¬ Theq .right (SpEqs spEx) [2, 1] [3, 4, 1] := by
  refine ⟨by decide, rfl, fun h => ?_⟩
  let v : ℕ → SubR := fun i => ⟨valOf [0, 0, -2, 5, 3] i⟩
  have hv : Sat .right v (SpEqs spEx) := by
    rw [spEqs_spEx]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    simp only [den, List.map, foldR, Option.map_some, Option.some.injEq]
    ext; simp [v, valOf]
  have key := h SubR v hv
  simp only [den, List.map, foldR, Option.map_some, Option.some.injEq] at key
  have := congrArg SubR.val key
  simp [v, valOf] at this

end SemperProofs.CC.ARound
