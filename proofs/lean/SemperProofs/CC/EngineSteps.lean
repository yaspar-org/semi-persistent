import SemperProofs.CC.Laws.InvRules

/-!
# The engine's completion merges are `Infer` runs

`egraph.rs` `cc_round` merges nodes that are not reducts of nodes: the (B)
superposition loop materializes the normal forms of both reducts of the lcm
of two overlapping left-hand sides (the lcm is no node) and merges them; the
law-instance axiom pairs and the cancellation closure (C1, C2, and the
per-constant closure of an emptied side) do the same with pairs built from
one or two rules; `inverse_cancel_repair` merges a node with the monomial
left after removing its `{x, inv x}` pairs. This file states each as a state
change and proves the change is reached by `Infer` steps.

* `Materialize st N st' c`: the engine's `materialize` of `N`, a hash-cons
  hit on an existing node `(N, c)` (`st' = st`) or a node in a fresh class.
* `Normalize L inv st`: the engine's normalization of a pair side before it
  materializes it: rewriting by the state's rules (`normalize_ms`) and
  removing `{x, inv x}` pairs (`group_cancel_pairs`).
* `superpose_infer`, `axiomPair_infer`, `cancelClose_infer`,
  `inverseRepair_infer`: the four engine steps, each a `Reachable` run.
* `superpose_example`: rules `{x, y} → {p}`, `{y, z} → {q}`; the merge of
  `{z, p}` and `{x, q}`, neither a reduct of a node, is an `Infer` run.

No hypothesis mentions I2 or soundness: soundness of the result is
`completion_sound` applied to the run.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-! ## Monotonicity of the state's equalities -/

theorem State.eqs_mono {st st' : State n} (hn : st.nodes ⊆ st'.nodes)
    (hf : st'.find = st.find) : st.eqs ⊆ st'.eqs := by
  rintro ⟨M, N⟩ ⟨c, c', h₁, h₂, h₃⟩
  exact ⟨c, c', hn h₁, hn h₂, by rw [hf]; exact h₃⟩

theorem State.child_mono {st st' : State n} (hn : st.nodes ⊆ st'.nodes) {x : Fin n}
    (h : st.Child x) : st'.Child x := by
  obtain ⟨M, c, hM, hx⟩ := h
  exact ⟨M, c, hn hM, hx⟩

/-! ## Materialization -/

/-- The engine's `materialize` of `N`: a hash-cons hit returns the class of
an existing node; a miss registers `N` in a fresh class. -/
inductive Materialize (st : State n) (N : Monomial n) : State n → Fin n → Prop
  | hit {c : Fin n} : (N, c) ∈ st.nodes → Materialize st N st c
  | fresh {d : Fin n} : st.Fresh d → Materialize st N (st.addNode N d) d

namespace Materialize

variable {st st' : State n} {N : Monomial n} {c : Fin n}

theorem nodes_sub (h : Materialize st N st' c) : st.nodes ⊆ st'.nodes := by
  cases h with
  | hit _ => exact subset_rfl
  | fresh _ => exact Set.subset_insert _ _

theorem find_eq (h : Materialize st N st' c) : st'.find = st.find := by
  cases h <;> rfl

theorem mem (h : Materialize st N st' c) : (N, c) ∈ st'.nodes := by
  cases h with
  | hit h => exact h
  | fresh _ => exact Set.mem_insert _ _

theorem reach {L : Laws n} (hN : ∀ x ∈ N, st.Child x) (h : Materialize st N st' c) :
    Reachable L st st' := by
  cases h with
  | hit _ => exact ReflTransGen.refl
  | fresh hd => exact ReflTransGen.single (Infer.mint hN hd)

end Materialize

/-- Materialize two monomials whose children occur in the state and which
the state derives equal, then merge their classes: an `Infer` run. Every
engine step below is an instance. -/
theorem materialize_merge_infer {L : Laws n} {st st₁ st₂ : State n} {N₁ N₂ : Monomial n}
    {c₁ c₂ : Fin n} (hN₁ : ∀ x ∈ N₁, st.Child x) (hN₂ : ∀ x ∈ N₂, st.Child x)
    (hE : E L st.eqs N₁ N₂) (hm₁ : Materialize st N₁ st₁ c₁)
    (hm₂ : Materialize st₁ N₂ st₂ c₂) : Reachable L st (st₂.merge c₁ c₂) := by
  have hr₁ := hm₁.reach (L := L) hN₁
  have hr₂ := hm₂.reach (L := L) fun x hx => State.child_mono hm₁.nodes_sub (hN₂ x hx)
  have hsub : st.nodes ⊆ st₂.nodes := hm₁.nodes_sub.trans hm₂.nodes_sub
  have hf : st₂.find = st.find := hm₂.find_eq.trans hm₁.find_eq
  exact (hr₁.trans hr₂).tail
    (Infer.joinMerge (hm₂.nodes_sub hm₁.mem) hm₂.mem (E.mono (State.eqs_mono hsub hf) hE))

/-! ## Children and derivations of rule sides -/

theorem rule_lhs_child {st : State n} {A B : Monomial n} (h : (A, B) ∈ st.rules) :
    ∀ x ∈ A, st.Child x := by
  obtain ⟨c, -, hA, -⟩ := h
  exact fun x hx => ⟨A, c, hA.1, hx⟩

theorem rule_rhs_child {st : State n} {A B : Monomial n} (h : (A, B) ∈ st.rules) :
    ∀ x ∈ B, st.Child x := by
  obtain ⟨-, c', -, -, -, hBn, -⟩ := h
  exact fun x hx => ⟨B, c', hBn, hx⟩

theorem child_of_le {st : State n} {M N : Monomial n} (hle : N ≤ M)
    (hM : ∀ x ∈ M, st.Child x) : ∀ x ∈ N, st.Child x :=
  fun x hx => hM x (Multiset.mem_of_le hle hx)

theorem child_add {st : State n} {M N : Monomial n} (hM : ∀ x ∈ M, st.Child x)
    (hN : ∀ x ∈ N, st.Child x) : ∀ x ∈ M + N, st.Child x := by
  intro x hx
  rcases Multiset.mem_add.1 hx with hx | hx
  · exact hM x hx
  · exact hN x hx

theorem child_clamp {L : Laws n} {st : State n} {M : Monomial n} (hM : ∀ x ∈ M, st.Child x) :
    ∀ x ∈ L.clamp M, st.Child x :=
  child_of_le (L.clamp_le M) hM

/-- Rewriting by a rule inside a context: `clamp((U − A) + B) =_E U` from the
state's classes, for `A ≤ U`. -/
theorem E_rule_ctx {L : Laws n} {st : State n} {A B U : Monomial n} (h : (A, B) ∈ st.rules)
    (hA : A ≤ U) : E L st.eqs (L.clamp ((U - A) + B)) U := by
  refine (E_clamp L st.eqs _).trans ?_
  have h₁ : E L st.eqs ((U - A) + B) ((U - A) + A) :=
    E.congr_left (U - A) (E.symm (E.ax (rules_eqs h)))
  rwa [tsub_add_cancel_of_le hA] at h₁

/-! ## Normalization of a pair side -/

/-- `inverse_cancel_repair` and `group_cancel_pairs`: remove one pair
`{x, inv x}`. -/
def InvCancel (inv : Fin n → Option (Fin n)) (M N : Monomial n) : Prop :=
  ∃ x y, inv x = some y ∧ ({x, y} : Monomial n) ≤ M ∧ N = M - {x, y}

/-- The engine's normalization of a pair side: rewrite steps by the state's
rules and removals of `{x, inv x}` pairs. -/
def Normalize (L : Laws n) (inv : Fin n → Option (Fin n)) (st : State n) :
    Monomial n → Monomial n → Prop :=
  ReflTransGen fun M N => Rw L st.rules M N ∨ InvCancel inv M N

/-- With no inverse operator there is no pair to remove. -/
theorem Laws.hasInv_none (L : Laws n) : L.HasInv (fun _ => none) := by
  intro x y h
  cases h

theorem InvCancel_E {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    {S : Set (Monomial n × Monomial n)} {M N : Monomial n} (h : InvCancel inv M N) :
    E L S M N := by
  obtain ⟨x, y, hxy, hle, rfl⟩ := h
  have h₁ : E L S ((M - {x, y}) + {x, y}) ((M - {x, y}) + 0) :=
    E.congr_left _ (E.law (hinv x y hxy))
  rwa [tsub_add_cancel_of_le hle, add_zero] at h₁

theorem Rw_child {L : Laws n} {st : State n} {M N : Monomial n} (hM : ∀ x ∈ M, st.Child x)
    (h : Rw L st.rules M N) : ∀ x ∈ N, st.Child x := by
  obtain ⟨A, B, hAB, -, rfl⟩ := h
  exact child_clamp (child_add (child_of_le tsub_le_self hM) (rule_rhs_child hAB))

theorem Normalize.child {L : Laws n} {inv : Fin n → Option (Fin n)} {st : State n}
    {M N : Monomial n} (hM : ∀ x ∈ M, st.Child x) (h : Normalize L inv st M N) :
    ∀ x ∈ N, st.Child x := by
  induction h with
  | refl => exact hM
  | tail _ hs ih =>
    rcases hs with hs | ⟨x, y, -, -, rfl⟩
    · exact Rw_child ih hs
    · exact child_of_le tsub_le_self ih

theorem Normalize.E {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    {st : State n} {M N : Monomial n} (h : Normalize L inv st M N) : E L st.eqs M N := by
  induction h with
  | refl => exact E.refl _
  | tail _ hs ih =>
    rcases hs with hs | hs
    · exact ih.trans (Rw_sound (fun A B h => E.ax (rules_eqs h)) hs)
    · exact ih.trans (InvCancel_E hinv hs)

/-- The general shape: two pair sides the state derives equal, with children
in the state, are normalized, materialized and merged. -/
theorem pair_infer {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    {st st₁ st₂ : State n} {P₁ P₂ N₁ N₂ : Monomial n} {c₁ c₂ : Fin n}
    (hP₁ : ∀ x ∈ P₁, st.Child x) (hP₂ : ∀ x ∈ P₂, st.Child x) (hP : E L st.eqs P₁ P₂)
    (hN₁ : Normalize L inv st P₁ N₁) (hN₂ : Normalize L inv st P₂ N₂)
    (hm₁ : Materialize st N₁ st₁ c₁) (hm₂ : Materialize st₁ N₂ st₂ c₂) :
    Reachable L st (st₂.merge c₁ c₂) :=
  materialize_merge_infer (hN₁.child hP₁) (hN₂.child hP₂)
    ((hN₁.E hinv).symm.trans (hP.trans (hN₂.E hinv))) hm₁ hm₂

/-! ## (B) superposition -/

/-- The (B) step of `cc_round` (`egraph.rs`, superposition loop and the
materialize-and-merge of nontrivial pairs): for two rules of the state, the
two reducts of the lcm of their left-hand sides (`criticalPair`) are
normalized, materialized and merged. The lcm need not be a node, and the
left-hand sides need not overlap. -/
theorem superpose_infer {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    {st st₁ st₂ : State n} {r₁ r₂ : Monomial n × Monomial n} {N₁ N₂ : Monomial n}
    {c₁ c₂ : Fin n} (h₁ : r₁ ∈ st.rules) (h₂ : r₂ ∈ st.rules)
    (hN₁ : Normalize L inv st (criticalPair L r₁ r₂).1 N₁)
    (hN₂ : Normalize L inv st (criticalPair L r₁ r₂).2 N₂)
    (hm₁ : Materialize st N₁ st₁ c₁) (hm₂ : Materialize st₁ N₂ st₂ c₂) :
    Reachable L st (st₂.merge c₁ c₂) := by
  obtain ⟨A, a⟩ := r₁
  obtain ⟨B, b⟩ := r₂
  have hU : ∀ x ∈ A ∪ B, st.Child x := by
    intro x hx
    rcases Multiset.mem_union.1 hx with hx | hx
    · exact rule_lhs_child h₁ x hx
    · exact rule_lhs_child h₂ x hx
  refine pair_infer hinv ?_ ?_ ?_ hN₁ hN₂ hm₁ hm₂
  · exact child_clamp (child_add (child_of_le tsub_le_self hU) (rule_rhs_child h₁))
  · exact child_clamp (child_add (child_of_le tsub_le_self hU) (rule_rhs_child h₂))
  · exact (E_rule_ctx h₁ Multiset.le_union_left).trans
      (E_rule_ctx h₂ Multiset.le_union_right).symm

/-! ## The law-instance axiom pairs -/

/-- `{x, x} → {x}` is a law instance for every class (idempotence). -/
def Laws.HasIdem (L : Laws n) : Prop :=
  ∀ x : Fin n, L.lawRel ({x, x} : Monomial n) {x}

/-- The axiom pairs `cc_round` builds per rule `A → B` (`egraph.rs`,
"Per-rule axiom critical pairs" and the group-law pairs):

* `idem`: `x ∘ x = x`, `a ∈ A`: `(clamp(B ⊎ {a}), B)`;
* `nil`: `xᵏ = e`, `a` with count `m ≤ k` in `A`: `(clamp(B ⊎ a^(k−m)), A − a^m)`;
* `invLeft`: `a ∈ A`, the inverse of `a` in class `y`: `(clamp(B ⊎ {y}), A − {a})`;
* `invRight`: `y ∈ A` the class of the inverse of `x`: `(clamp(B ⊎ {x}), A − {y})`.

The class of an inverse node is a child of its atomic node `{y}` (the
model's reading of an atomic class, `InvNodes.atom_class`), hence the
`Child` premise. -/
inductive AxiomPair (L : Laws n) (inv : Fin n → Option (Fin n)) (k : ℕ) (st : State n) :
    Monomial n → Monomial n → Prop
  | idem {A B : Monomial n} {a : Fin n} :
      L.HasIdem → (A, B) ∈ st.rules → a ∈ A → AxiomPair L inv k st (L.clamp (B + {a})) B
  | nil {A B : Monomial n} {a : Fin n} :
      L.HasNil k → (A, B) ∈ st.rules → a ∈ A → A.count a ≤ k →
      AxiomPair L inv k st (L.clamp (B + Multiset.replicate (k - A.count a) a))
        (A - Multiset.replicate (A.count a) a)
  | invLeft {A B : Monomial n} {a y : Fin n} :
      (A, B) ∈ st.rules → a ∈ A → inv a = some y → st.Child y →
      AxiomPair L inv k st (L.clamp (B + {y})) (A.erase a)
  | invRight {A B : Monomial n} {x y : Fin n} :
      (A, B) ∈ st.rules → y ∈ A → inv x = some y → st.Child x →
      AxiomPair L inv k st (L.clamp (B + {x})) (A.erase y)

/-- `B ⊎ X =_E A ⊎ X` from a rule `A → B` of the state. -/
theorem E_rule_add {L : Laws n} {st : State n} {A B : Monomial n} (h : (A, B) ∈ st.rules)
    (X : Monomial n) : E L st.eqs (B + X) (A + X) :=
  E.congr X (E.symm (E.ax (rules_eqs h)))

theorem AxiomPair.child {L : Laws n} {inv : Fin n → Option (Fin n)} {k : ℕ} {st : State n}
    {P Q : Monomial n} (h : AxiomPair L inv k st P Q) :
    (∀ x ∈ P, st.Child x) ∧ ∀ x ∈ Q, st.Child x := by
  cases h with
  | idem _ hAB ha =>
    refine ⟨child_clamp (child_add (rule_rhs_child hAB) ?_), rule_rhs_child hAB⟩
    intro x hx
    rw [Multiset.mem_singleton.1 hx]
    exact rule_lhs_child hAB _ ha
  | nil _ hAB ha _ =>
    refine ⟨child_clamp (child_add (rule_rhs_child hAB) ?_),
      child_of_le tsub_le_self (rule_lhs_child hAB)⟩
    intro x hx
    rw [Multiset.eq_of_mem_replicate hx]
    exact rule_lhs_child hAB _ ha
  | invLeft hAB _ _ hy =>
    refine ⟨child_clamp (child_add (rule_rhs_child hAB) ?_),
      child_of_le (Multiset.erase_le _ _) (rule_lhs_child hAB)⟩
    intro x hx
    rw [Multiset.mem_singleton.1 hx]
    exact hy
  | invRight hAB _ _ hx' =>
    refine ⟨child_clamp (child_add (rule_rhs_child hAB) ?_),
      child_of_le (Multiset.erase_le _ _) (rule_lhs_child hAB)⟩
    intro x hx
    rw [Multiset.mem_singleton.1 hx]
    exact hx'

/-- `R ⊎ P =_E R` for a law instance `P → ∅`. -/
theorem E_drop {L : Laws n} {S : Set (Monomial n × Monomial n)} {P : Monomial n}
    (hP : L.lawRel P 0) (R : Monomial n) : E L S (R + P) R := by
  have h := E.congr_left (S := S) R (E.law hP)
  rwa [add_zero] at h

theorem AxiomPair.derive {L : Laws n} {inv : Fin n → Option (Fin n)} {k : ℕ} {st : State n}
    (hinv : L.HasInv inv) {P Q : Monomial n} (h : AxiomPair L inv k st P Q) :
    SemperProofs.CC.E L st.eqs P Q := by
  cases h with
  | @idem A B a hidem hAB ha =>
    have hA : A = {a} + A.erase a := by rw [Multiset.singleton_add, Multiset.cons_erase ha]
    have key : E L st.eqs (A + {a}) A := by
      have h₁ := E.congr_left (S := st.eqs) (A.erase a) (E.law (hidem a))
      rw [pair_eq_add] at h₁
      have e₁ : A.erase a + ({a} + {a}) = A + {a} := by (conv_rhs => rw [hA]); abel
      have e₂ : A.erase a + {a} = A := by (conv_rhs => rw [hA]); abel
      rwa [e₁, e₂] at h₁
    exact (E_clamp L _ _).trans ((E_rule_add hAB {a}).trans (key.trans (E.ax (rules_eqs hAB))))
  | @nil A B a hnil hAB _ hk =>
    have hle : Multiset.replicate (A.count a) a ≤ A := Multiset.le_count_iff_replicate_le.1 le_rfl
    have hk' : Multiset.replicate k a =
        Multiset.replicate (A.count a) a + Multiset.replicate (k - A.count a) a := by
      rw [← Multiset.replicate_add, Nat.add_sub_cancel' hk]
    have e : A + Multiset.replicate (k - A.count a) a =
        (A - Multiset.replicate (A.count a) a) + Multiset.replicate k a := by
      rw [hk', ← add_assoc, tsub_add_cancel_of_le hle]
    refine (E_clamp L _ _).trans ((E_rule_add hAB _).trans ?_)
    rw [e]
    exact E_drop (hnil a) _
  | @invLeft A B a y hAB ha hay _ =>
    have e : A + {y} = A.erase a + {a, y} := by
      conv_lhs => rw [← Multiset.cons_erase ha]
      rw [pair_eq_add, ← Multiset.singleton_add]; abel
    refine (E_clamp L _ _).trans ((E_rule_add hAB _).trans ?_)
    rw [e]
    exact E_drop (hinv a y hay) _
  | @invRight A B x y hAB hy hxy _ =>
    have e : A + {x} = A.erase y + {x, y} := by
      conv_lhs => rw [← Multiset.cons_erase hy]
      rw [pair_eq_add, ← Multiset.singleton_add]; abel
    refine (E_clamp L _ _).trans ((E_rule_add hAB _).trans ?_)
    rw [e]
    exact E_drop (hinv x y hxy) _

/-- The axiom-pair step of `cc_round`: the two sides of a rule's pair with a
law instance are normalized, materialized and merged. -/
theorem axiomPair_infer {L : Laws n} {inv : Fin n → Option (Fin n)} {k : ℕ}
    (hinv : L.HasInv inv) {st st₁ st₂ : State n} {P₁ P₂ N₁ N₂ : Monomial n} {c₁ c₂ : Fin n}
    (hp : AxiomPair L inv k st P₁ P₂)
    (hN₁ : Normalize L inv st P₁ N₁) (hN₂ : Normalize L inv st P₂ N₂)
    (hm₁ : Materialize st N₁ st₁ c₁) (hm₂ : Materialize st₁ N₂ st₂ c₂) :
    Reachable L st (st₂.merge c₁ c₂) :=
  pair_infer hinv hp.child.1 hp.child.2 (hp.derive hinv) hN₁ hN₂ hm₁ hm₂

/-! ## The cancellation closure -/

/-- The pairs of the cancellation closure (`egraph.rs`, "Cancelative facet"):

* `c1`: a rule `A → B`, `C = A ∩ B`: `(A − C, B − C)`;
* `c2`: two rules, the disjoint join `A₁ ⊎ A₂ = B₁ ⊎ B₂` cancel-closed;
* `constant`: a pair whose right side emptied, without a unit:
  `(M ⊎ {g}, {g})` for every class `g` of the summand pool. -/
inductive CancelPair (st : State n) : Monomial n → Monomial n → Prop
  | c1 {A B : Monomial n} : (A, B) ∈ st.rules → CancelPair st (A - A ∩ B) (B - A ∩ B)
  | c2 {A₁ B₁ A₂ B₂ : Monomial n} : (A₁, B₁) ∈ st.rules → (A₂, B₂) ∈ st.rules →
      CancelPair st (A₁ + A₂ - (A₁ + A₂) ∩ (B₁ + B₂)) (B₁ + B₂ - (A₁ + A₂) ∩ (B₁ + B₂))
  | constant {M : Monomial n} {g : Fin n} : CancelPair st M 0 → st.Child g →
      CancelPair st (M + {g}) {g}

/-- Cancel the common part `C ≤ P, Q` of an equation `P = Q`. -/
theorem E_cancel_common {L : Laws n} {S : Set (Monomial n × Monomial n)} (hc : L.cancellative)
    {P Q C : Monomial n} (hP : C ≤ P) (hQ : C ≤ Q) (h : E L S P Q) : E L S (P - C) (Q - C) := by
  refine E.cancel (X := C) hc ?_
  rwa [tsub_add_cancel_of_le hP, tsub_add_cancel_of_le hQ]

theorem CancelPair.child_E {L : Laws n} (hc : L.cancellative) {st : State n} {P Q : Monomial n}
    (h : CancelPair st P Q) :
    (∀ x ∈ P, st.Child x) ∧ (∀ x ∈ Q, st.Child x) ∧ E L st.eqs P Q := by
  induction h with
  | c1 hAB =>
    exact ⟨child_of_le tsub_le_self (rule_lhs_child hAB),
      child_of_le tsub_le_self (rule_rhs_child hAB),
      E_cancel_common hc Multiset.inter_le_left Multiset.inter_le_right (E.ax (rules_eqs hAB))⟩
  | c2 h₁ h₂ =>
    refine ⟨child_of_le tsub_le_self (child_add (rule_lhs_child h₁) (rule_lhs_child h₂)),
      child_of_le tsub_le_self (child_add (rule_rhs_child h₁) (rule_rhs_child h₂)),
      E_cancel_common hc Multiset.inter_le_left Multiset.inter_le_right ?_⟩
    exact (E.congr _ (E.ax (rules_eqs h₁))).trans (E.congr_left _ (E.ax (rules_eqs h₂)))
  | @constant M g _ hg ih =>
    obtain ⟨hM, -, hE⟩ := ih
    have hsing : ∀ x ∈ ({g} : Monomial n), st.Child x := by
      intro x hx
      rw [Multiset.mem_singleton.1 hx]
      exact hg
    refine ⟨child_add hM hsing, hsing, ?_⟩
    have h := E.congr {g} hE
    rwa [zero_add] at h

/-- The cancellation-closure step of `cc_round` (C1, C2 and the per-constant
closure): the two sides of a cancel pair are normalized, materialized and
merged. -/
theorem cancelClose_infer {L : Laws n} {inv : Fin n → Option (Fin n)} (hc : L.cancellative)
    (hinv : L.HasInv inv) {st st₁ st₂ : State n} {P₁ P₂ N₁ N₂ : Monomial n} {c₁ c₂ : Fin n}
    (hp : CancelPair st P₁ P₂)
    (hN₁ : Normalize L inv st P₁ N₁) (hN₂ : Normalize L inv st P₂ N₂)
    (hm₁ : Materialize st N₁ st₁ c₁) (hm₂ : Materialize st₁ N₂ st₂ c₂) :
    Reachable L st (st₂.merge c₁ c₂) :=
  let h := hp.child_E (L := L) hc
  pair_infer hinv h.1 h.2.1 h.2.2 hN₁ hN₂ hm₁ hm₂

/-! ## The inverse repair -/

/-- `inverse_cancel_repair` (`egraph.rs`): a node `(M, g)` whose monomial
holds pairs `{x, inv x}` is merged with the monomial left after removing
them (`add_monomial`, then `repair_merge`). The removal is a law-instance
step, not a rewrite by a rule. -/
theorem inverseRepair_infer {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    {st st' : State n} {M M' : Monomial n} {g c : Fin n} (hM : (M, g) ∈ st.nodes)
    (hcancel : ReflTransGen (InvCancel inv) M M') (hm : Materialize st M' st' c) :
    Reachable L st (st'.merge c g) := by
  have hN : Normalize L inv st M M' := by
    clear hm
    induction hcancel with
    | refl => exact ReflTransGen.refl
    | tail _ h ih => exact ih.tail (Or.inr h)
  have hMc : ∀ x ∈ M, st.Child x := fun x hx => ⟨M, g, hM, hx⟩
  exact materialize_merge_infer (hN.child hMc) hMc (hN.E hinv).symm hm (Materialize.hit
    (hm.nodes_sub hM))

/-! ## A concrete superposition

Classes `x = 0`, `y = 1`, `z = 2`, `p = 3`, `q = 4`; `5` and `6` are fresh.
The nodes `{x, y}` and `{p}` share class `3`, `{y, z}` and `{q}` class `4`,
so the rules are `{x, y} → {p}` and `{y, z} → {q}`. The lcm `{x, y, z}` is
no node; the engine materializes `{z, p}` and `{x, q}` and merges them. -/

/-- The state before the (B) step. -/
def exSt : State 7 where
  find := id
  nodes := {(({0, 1} : Monomial 7), 3), ({3}, 3), ({1, 2}, 4), ({4}, 4)}
  retired := ∅
  rhs := fun c => if c = 3 then {3} else if c = 4 then {4} else 0

theorem exSt_rule₁ : (({0, 1} : Monomial 7), ({3} : Monomial 7)) ∈ exSt.rules :=
  ⟨3, 3, ⟨by simp [exSt], by simp [exSt]⟩, by simp [exSt], by decide, by simp [exSt], rfl⟩

theorem exSt_rule₂ : (({1, 2} : Monomial 7), ({4} : Monomial 7)) ∈ exSt.rules :=
  ⟨4, 4, ⟨by simp [exSt], by simp [exSt]⟩, by simp [exSt], by decide, by simp [exSt], rfl⟩

/-- The critical pair of the two rules is `({z, p}, {x, q})`. -/
theorem exSt_criticalPair :
    criticalPair (Laws.plainAC 7) ({0, 1}, {3}) ({1, 2}, {4}) = ({2, 3}, {0, 4}) := by
  decide

theorem exSt_fresh₅ : exSt.Fresh 5 := by
  intro M c h
  simp only [exSt, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

theorem exSt_fresh₆ : (exSt.addNode {2, 3} 5).Fresh 6 := by
  intro M c h
  simp only [State.addNode, exSt, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] at h
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

/-- The (B) step on `exSt` is an `Infer` run: mint `{z, p}` in class `5`,
mint `{x, q}` in class `6`, merge `5` and `6`. -/
theorem superpose_example :
    Reachable (Laws.plainAC 7) exSt
      (((exSt.addNode {2, 3} 5).addNode {0, 4} 6).merge 5 6) := by
  have h₁ : Normalize (Laws.plainAC 7) (fun _ => none) exSt
      (criticalPair (Laws.plainAC 7) ({0, 1}, {3}) ({1, 2}, {4})).1 {2, 3} := by
    rw [exSt_criticalPair]; exact ReflTransGen.refl
  have h₂ : Normalize (Laws.plainAC 7) (fun _ => none) exSt
      (criticalPair (Laws.plainAC 7) ({0, 1}, {3}) ({1, 2}, {4})).2 {0, 4} := by
    rw [exSt_criticalPair]; exact ReflTransGen.refl
  exact superpose_infer (Laws.hasInv_none _) exSt_rule₁ exSt_rule₂ h₁ h₂
    (Materialize.fresh exSt_fresh₅) (Materialize.fresh exSt_fresh₆)

end SemperProofs.CC
