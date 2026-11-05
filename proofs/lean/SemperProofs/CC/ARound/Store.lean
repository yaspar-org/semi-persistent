import SemperProofs.CC.ARound.Choice

/-!
# `a_round` over a hash-consed node store

The engine adds the rewritten sequence with `add`, which hash-conses: when a
node with the same (canonical) children exists, `add` returns its class and
mints nothing. `a_round` merges the returned class with `buf`'s class when
they differ (`find(nid) != find(g)`); otherwise the rewrite changes nothing.

Here the node store of one operator is a partial function from sequences to
classes (`HState.store`), so a sequence has at most one node, and
`HState.add` returns the existing class when the sequence is present. The step
`ARoundH` takes any rule `l → r` between two nodes of one class with `r` below
`l` in `shortlex`. The engine's rules (`ClassRules`: `r` the least spelling)
are such rules, and stay such rules while a round runs on rules computed at
its start, since merges only coarsen classes and nodes persist. `ARoundH` also
puts no bound on the number of rewrites per node per round, so the engine's
schedule is one of its runs and the results below hold for it.

This file proves:

* `aRoundH_toA`: an `ARoundH` step is an `ARoundStep` of the node-set view,
  in both cases of `add` (fresh node, or existing node merged with its
  class); `aRoundH_sound`, `aRoundH_reachable_sound`: so I2 is preserved;
* `aRoundH_potential_lt`: every step strictly shrinks a finite potential, the
  set of pairs of short sequences over the alphabet that are not two nodes of
  one class; `aRoundH_wf`: so there is no infinite chain of `a_round`
  merges from a finite node set, and the fixpoint loop over rounds (each round
  that reports a change makes at least one merge) terminates.

As in `ARound/Basic.lean`, the sequences are compared as stored: the
recanonicalization of children after a merge belongs to rebuild and is not
part of this model, and the alphabet is fixed because `a_round` only copies
elements of existing nodes.
-/

namespace SemperProofs.CC.ARound

variable {C : Type}

/-- The sequence nodes of one A-only operator as a hash-consed store: the
union-find `find`, and the class of the node spelled by each sequence. -/
structure HState (C : Type) where
  find : C → C
  store : List C → Option C

namespace HState

variable [LinearOrder C] (st : HState C)

/-- The node-set view. -/
def toA : AState C := ⟨st.find, {p | st.store p.1 = some p.2}⟩

def merge (a b : C) : HState C :=
  { st with find := fun x => if st.find x = st.find a then st.find b else st.find x }

/-- A class is fresh when no node is in it. -/
def Fresh (e : C) : Prop := ∀ s c, st.store s = some c → st.find c ≠ st.find e

/-- Hash-consed insertion: the existing class when `s` is a node, otherwise a
new node `(s, e)`. -/
def add (s : List C) (e : C) : HState C × C :=
  match st.store s with
  | some c => (st, c)
  | none => ({ st with store := Function.update st.store s (some e) }, e)

theorem add_find (s : List C) (e : C) : (st.add s e).1.find = st.find := by
  unfold add; split <;> rfl

end HState

variable [LinearOrder C]

/-- One `a_round` merge over the hash-consed store: an oriented rule
`l → r` between two nodes of one class (`r` below `l`), a node `buf` of
class `g`, an allowed rewrite `out`, its hash-consed insertion (a fresh class
`e` when `out` is new), and the merge of the returned class `c` with `g` when
they differ. -/
inductive ARoundH (d : Dir) : HState C → HState C → Prop
  | step {st st₁ : HState C} {l r buf out : List C} {c₁ c₂ g e c : C} :
      st.store l = some c₁ → st.store r = some c₂ → st.find c₁ = st.find c₂ →
      SL r l →
      st.store buf = some g → ARStep d buf l r out →
      (st.store out = none → st.Fresh e) → st.add out e = (st₁, c) →
      st.find c ≠ st.find g →
      ARoundH d st (st₁.merge c g)

section Sound

/-- **An `ARoundH` step is an `a_round` merge of the node-set view.** -/
theorem aRoundH_toA {d : Dir} {st st' : HState C} (h : ARoundH d st st') :
    ARoundStep d st.toA st'.toA := by
  obtain ⟨hl, hr, hc, -, hb, hstep, hfresh, hadd, -⟩ := h
  rename_i st₁ l r buf out c₁ c₂ g e c
  unfold HState.add at hadd
  split at hadd
  · rename_i c' hout
    obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
    subst st₁ c'
    have heq : (st.merge c g).toA = (st.toA.addNode out c).merge c g := by
      simp only [HState.toA, HState.merge, AState.addNode, AState.merge, AState.mk.injEq]
      exact ⟨rfl, (Set.insert_eq_of_mem (a := (out, c))
        (show (out, c) ∈ {p : List C × C | st.store p.1 = some p.2} from hout)).symm⟩
    rw [heq]
    exact ARoundStep.merge hl hr hc hb hstep (Or.inr hout)
  · rename_i hout
    obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
    subst st₁ e
    have hf : st.toA.Fresh c := fun s c' hs => hfresh hout s c' hs
    have heq : ({ st with store := Function.update st.store out (some c) }.merge c g).toA =
        (st.toA.addNode out c).merge c g := by
      simp only [HState.toA, HState.merge, AState.addNode, AState.merge, AState.mk.injEq]
      refine ⟨rfl, ?_⟩
      ext ⟨s, c'⟩
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Prod.mk.injEq]
      by_cases hs : s = out
      · subst hs; simp [hout, eq_comm]
      · simp [hs]
    rw [heq]
    exact ARoundStep.merge hl hr hc hb hstep (Or.inl hf)

/-- I2 for the hash-consed store. -/
def I2H (d : Dir) (S : Set (List C × List C)) (st : HState C) : Prop := I2 d S st.toA

/-- **An `a_round` merge over the hash-consed store preserves I2**, both when
`out` is new and when it is an existing node merged with its class. -/
theorem aRoundH_sound {d : Dir} {S : Set (List C × List C)} {st st' : HState C}
    (h : ARoundH d st st') (hI : I2H d S st) : I2H d S st' :=
  aRound_sound (aRoundH_toA h) hI

theorem aRoundH_reachable_sound {d : Dir} {S : Set (List C × List C)} {st₀ st : HState C}
    (hreach : Relation.ReflTransGen (ARoundH d) st₀ st) (h₀ : I2H d S st₀) : I2H d S st := by
  induction hreach with
  | refl => exact h₀
  | tail _ hs ih => exact aRoundH_sound hs ih

end Sound

/-! ## Termination -/

section Termination

/-- Two sequences are nodes of one class. -/
def Same (st : HState C) (s t : List C) : Prop :=
  ∃ c c', st.store s = some c ∧ st.store t = some c' ∧ st.find c = st.find c'

/-- Every node is a sequence of length at most `L` over the alphabet `A`. -/
def Bounded (A : Set C) (L : ℕ) (st : HState C) : Prop :=
  ∀ s c, st.store s = some c → s.length ≤ L ∧ ∀ x ∈ s, x ∈ A

/-- The sequences of length at most `L` over `A`. -/
def Words (A : Set C) (L : ℕ) : Set (List C) := {s | s.length ≤ L ∧ ∀ x ∈ s, x ∈ A}

omit [LinearOrder C] in
theorem words_finite {A : Set C} (hA : A.Finite) (L : ℕ) : (Words A L).Finite := by
  have : Finite A := hA.to_subtype
  refine ((List.finite_length_le A L).image (List.map Subtype.val)).subset ?_
  rintro s ⟨hl, hs⟩
  refine ⟨s.pmap Subtype.mk hs, by simpa using hl, ?_⟩
  simp [List.map_pmap]

/-- The potential: pairs of words that are not two nodes of one class. -/
def Pot (A : Set C) (L : ℕ) (st : HState C) : Set (List C × List C) :=
  {p | p.1 ∈ Words A L ∧ p.2 ∈ Words A L ∧ ¬ Same st p.1 p.2}

omit [LinearOrder C] in
theorem pot_finite {A : Set C} (hA : A.Finite) (L : ℕ) (st : HState C) :
    (Pot A L st).Finite :=
  ((words_finite hA L).prod (words_finite hA L)).subset fun _ hp => ⟨hp.1, hp.2.1⟩

theorem merge_find_eq {st : HState C} {a b x y : C} (h : st.find x = st.find y) :
    (st.merge a b).find x = (st.merge a b).find y := by
  show (if st.find x = st.find a then _ else _) = (if st.find y = st.find a then _ else _)
  rw [h]

/-- The rewrite stays in the alphabet and does not grow. -/
theorem aRStep_words {d : Dir} {A : Set C} {L : ℕ} {buf l r out : List C}
    (hbuf : buf ∈ Words A L) (hr : ∀ x ∈ r, x ∈ A) (hlr : r.length ≤ l.length)
    (h : ARStep d buf l r out) : out ∈ Words A L := by
  obtain ⟨s, -, h⟩ := h
  refine ⟨(rewriteAt_length_le hlr h).trans hbuf.1, ?_⟩
  obtain ⟨hb, ho⟩ := rewriteAt_split h
  intro x hx
  rw [ho] at hx
  simp only [List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact hbuf.2 x (List.mem_of_mem_take hx)
  · exact hr x hx
  · exact hbuf.2 x (List.mem_of_mem_drop hx)

/-- **Each `a_round` merge strictly shrinks the potential** and keeps the
nodes bounded. -/
theorem aRoundH_potential_lt {d : Dir} {A : Set C} {L : ℕ} {st st' : HState C}
    (h : ARoundH d st st') (hB : Bounded A L st) :
    Pot A L st' ⊂ Pot A L st ∧ Bounded A L st' := by
  obtain ⟨hl, hr, -, hlr, hb, hstep, hfresh, hadd, hne⟩ := h
  rename_i st₁ l r buf out c₁ c₂ g e c
  have hbW : buf ∈ Words A L := hB _ _ hb
  have hoW : out ∈ Words A L := aRStep_words hbW (hB _ _ hr).2 (sl_length_le hlr) hstep
  -- old pairs of one class stay so
  have hmono : ∀ s t, Same st s t → Same (st₁.merge c g) s t := by
    rintro s t ⟨a, b, hs, ht, hab⟩
    unfold HState.add at hadd
    split at hadd
    · rename_i c' _
      obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
      subst st₁ c'
      exact ⟨a, b, hs, ht, merge_find_eq hab⟩
    · rename_i hout
      obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
      subst st₁ e
      have hso : s ≠ out := by rintro rfl; simp [hout] at hs
      have hto : t ≠ out := by rintro rfl; simp [hout] at ht
      exact ⟨a, b, by simpa [HState.merge, Function.update_of_ne hso] using hs,
        by simpa [HState.merge, Function.update_of_ne hto] using ht, merge_find_eq hab⟩
  -- the pair `(buf, out)` is new
  have hnew : Same (st₁.merge c g) buf out ∧ ¬ Same st buf out := by
    unfold HState.add at hadd
    split at hadd
    · rename_i c' hout
      obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
      subst st₁ c'
      refine ⟨⟨g, c, hb, hout, ?_⟩, ?_⟩
      · simp [HState.merge, Ne.symm hne]
      · rintro ⟨a, b, ha, hb', hab⟩
        rw [hb] at ha; rw [hout] at hb'
        cases ha; cases hb'
        exact hne hab.symm
    · rename_i hout
      obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
      subst st₁ e
      have hbo : buf ≠ out := by rintro rfl; simp [hout] at hb
      refine ⟨⟨g, c, by simpa [HState.merge, Function.update_of_ne hbo] using hb,
        by simp [HState.merge], ?_⟩, ?_⟩
      · simp [HState.merge, Ne.symm hne]
      · rintro ⟨a, b, -, hb', -⟩
        rw [hout] at hb'; cases hb'
  refine ⟨⟨fun p hp => ⟨hp.1, hp.2.1, fun hs => hp.2.2 (hmono _ _ hs)⟩, fun hsub => ?_⟩, ?_⟩
  · exact (@hsub (buf, out) ⟨hbW, hoW, hnew.2⟩).2.2 hnew.1
  · intro s c' hs
    unfold HState.add at hadd
    split at hadd
    · rename_i c'' _
      obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
      subst st₁ c''
      exact hB s c' hs
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hadd
      subst st₁ e
      by_cases hso : s = out
      · subst hso; exact hoW
      · exact hB s c' (by simpa [HState.merge, Function.update_of_ne hso] using hs)

/-- **Repeated `a_round` merges terminate**: from a store whose nodes are
sequences of length at most `L` over a finite alphabet (every finite node
set), there is no infinite chain of `ARoundH` steps. The number of steps is
bounded by the size of the initial potential. -/
theorem aRoundH_wf {d : Dir} {A : Set C} (hA : A.Finite) (L : ℕ) :
    WellFounded (fun st' st : {st : HState C // Bounded A L st} => ARoundH d st.1 st'.1) :=
  Subrelation.wf
    (fun {st' st} h => by
      show (Pot A L st'.1).ncard < (Pot A L st.1).ncard
      exact Set.ncard_lt_ncard (aRoundH_potential_lt h st.2).1 (pot_finite hA L st.1))
    (InvImage.wf (fun st : {st : HState C // Bounded A L st} => (Pot A L st.1).ncard)
      wellFounded_lt)

/-- A chain of `n` merges from a bounded store has `n` at most the size of
the initial potential. -/
theorem aRoundH_chain_bound {d : Dir} {A : Set C} (hA : A.Finite) {L : ℕ}
    (f : ℕ → HState C) (h0 : Bounded A L (f 0)) (n : ℕ)
    (hf : ∀ i < n, ARoundH d (f i) (f (i + 1))) : n ≤ (Pot A L (f 0)).ncard := by
  have key : ∀ i ≤ n, Bounded A L (f i) ∧ (Pot A L (f i)).ncard + i ≤ (Pot A L (f 0)).ncard := by
    intro i
    induction i with
    | zero => intro _; exact ⟨h0, by simp⟩
    | succ i ih =>
        intro hi
        obtain ⟨hB, hle⟩ := ih (by omega)
        obtain ⟨hlt, hB'⟩ := aRoundH_potential_lt (hf i (by omega)) hB
        have := Set.ncard_lt_ncard hlt (pot_finite hA L _)
        exact ⟨hB', by omega⟩
  have := (key n le_rfl).2
  omega

end Termination

end SemperProofs.CC.ARound
