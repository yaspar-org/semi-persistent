import SemperProofs.EMatch.Flatten.Main

/-!
# `:flatten` views: the corrected demand rule

The demand rule of `Views.lean` (`Demand.accepts`) accepts a match on a
view iff some opening tree giving the view has every leaf group hit by a
taken class. `Refold.lean` shows that its justification (close an unhit
leaf, the match survives with a refolded rest) fails for AC when the class
the leaf opens is itself taken (`refold_ac`, hypothesis `hX`), and the
engine loses matches for that reason (`demand-gap.egg`).

This file defines the corrected rule and the data it needs:

* opening trees that record, per leaf group, the class the leaf opened
  (`OTX`, with the number of openings as an index, used as the induction
  measure of the completeness proof), and their relation to `OT`
  (`OTX.toOT`, `OT.toOTX`);
* the per-leaf condition `LeafX.ok`: a leaf group counts as satisfied when
  it contains a taken class **or its opened class is taken**;
* the demand `DemandX`/`DemandX.acceptsFix` and the enumerator
  `enumerateX` producing it (the reference enumerator with the opened
  class recorded per leaf);
* the refolding relations `RefoldsAC`/`RefoldsACI`/`RefoldsAssoc` on rests;
* the tree surgery `OTX.refold` (closing one leaf, one opening fewer) with
  the positivity of multiplicities it needs.

`FixMain.lean` proves the completeness of the corrected rule.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Opening trees with the opened class per leaf -/

/-- A leaf group with the class whose opening produced it. -/
abbrev LeafX := C × List C

/-- A raw view with its leaf data. -/
abbrev RawX := List (C × Nat) × List LeafX

/-- `leafify` with the opened class recorded. -/
def leafifyX (X : C) (v : List (C × Nat)) (ls : List LeafX) : List LeafX :=
  if ls = [] then [(X, v.map Prod.fst)] else ls

/-- `OT` with the opened class per leaf and the number of openings as the
last index. -/
inductive OTX (ctx : Ctx) : Nat → Finset C → List (C × Nat) → List (C × Nat) →
    List LeafX → Nat → Prop
  | nil {k : Nat} {P : Finset C} : OTX ctx k P [] [] [] 0
  | keep {k : Nat} {P : Finset C} {X : C} {j : Nat} {rest v₂ : List (C × Nat)}
      {l₂ : List LeafX} {o : Nat} :
      OTX ctx k P rest v₂ l₂ o → OTX ctx k P ((X, j) :: rest) ((X, k * j) :: v₂) l₂ o
  | opn {k : Nat} {P : Finset C} {X : C} {j : Nat} {rest : List (C × Nat)}
      {id : NodeId} {m : Node} {v₁ v₂ : List (C × Nat)} {l₁ l₂ : List LeafX} {o₁ o₂ : Nat} :
      X ∉ P → ctx.IsMember id m X →
      OTX ctx (k * j) (insert X P) (kids ctx.κ m.children) v₁ l₁ o₁ →
      OTX ctx k P rest v₂ l₂ o₂ →
      OTX ctx k P ((X, j) :: rest) (v₁ ++ v₂) (leafifyX X v₁ l₁ ++ l₂) (o₁ + o₂ + 1)

/-- The view of node `m` with leaf data. -/
def ViewNodeX (ctx : Ctx) (m : Node) (k : Nat) (P : Finset C) (v : List (C × Nat))
    (ls : List LeafX) (o : Nat) : Prop :=
  OTX ctx k P (kids ctx.κ m.children) v ls o

/-- The options of one child position, with leaf data. -/
def ViewOptX (ctx : Ctx) (X : C) (k : Nat) (P : Finset C) (v : List (C × Nat))
    (ls : List LeafX) (o : Nat) : Prop :=
  (v = [(X, k)] ∧ ls = [] ∧ o = 0) ∨
    (X ∉ P ∧ ∃ id m l₁ o₁, ctx.IsMember id m X ∧
      ViewNodeX ctx m k (insert X P) v l₁ o₁ ∧ ls = leafifyX X v l₁ ∧ o = o₁ + 1)

/-- A raw view of the root `n` with leaf data and `o` openings. -/
def RawViewX (ctx : Ctx) (n : Node) (v : List (C × Nat)) (ls : List LeafX) (o : Nat) : Prop :=
  ViewNodeX ctx n 1 ∅ v ls o

theorem leafifyX_ne_nil (X : C) (v : List (C × Nat)) (ls : List LeafX) :
    leafifyX X v ls ≠ [] := by
  unfold leafifyX
  split <;> simp_all

theorem leafifyX_map_snd (X : C) (v : List (C × Nat)) (ls : List LeafX) :
    (leafifyX X v ls).map Prod.snd = leafify v (ls.map Prod.snd) := by
  unfold leafifyX leafify
  by_cases h : ls = []
  · subst h; simp
  · simp [h]

/-- Forgetting the opened classes gives an `OT`. -/
theorem OTX.toOT {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (h : OTX ctx k P ks v ls o) :
    OT ctx k P ks v (ls.map Prod.snd) := by
  induction h with
  | nil => exact OT.nil
  | keep _ ih => exact OT.keep ih
  | opn hX hmem _ _ ih₁ ih₂ =>
      rw [List.map_append, leafifyX_map_snd]
      exact OT.opn hX hmem ih₁ ih₂

/-- Every `OT` is the projection of some `OTX`. -/
theorem OT.toOTX {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List (List C)} (h : OT ctx k P ks v ls) :
    ∃ (lsx : List LeafX) (o : Nat), OTX ctx k P ks v lsx o ∧ lsx.map Prod.snd = ls := by
  induction h with
  | nil => exact ⟨[], 0, OTX.nil, rfl⟩
  | keep _ ih =>
      obtain ⟨lsx, o, h, rfl⟩ := ih
      exact ⟨lsx, o, OTX.keep h, rfl⟩
  | @opn _ _ X _ _ _ _ v₁ _ _ _ hX hmem _ _ ih₁ ih₂ =>
      obtain ⟨lsx₁, o₁, h₁, rfl⟩ := ih₁
      obtain ⟨lsx₂, o₂, h₂, rfl⟩ := ih₂
      exact ⟨leafifyX X v₁ lsx₁ ++ lsx₂, o₁ + o₂ + 1, OTX.opn hX hmem h₁ h₂,
        by rw [List.map_append, leafifyX_map_snd]⟩

theorem RawViewX.toRawView {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List LeafX}
    {o : Nat} (h : RawViewX ctx n v ls o) : RawView ctx n v (ls.map Prod.snd) :=
  OTX.toOT h

theorem RawView.toRawViewX {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List (List C)}
    (h : RawView ctx n v ls) :
    ∃ (lsx : List LeafX) (o : Nat), RawViewX ctx n v lsx o ∧ lsx.map Prod.snd = ls :=
  OT.toOTX h

/-! ## Multiplicities are positive -/

/-- The counts the walk reads are positive. -/
theorem kids_pos (κ : FlatKind) (ch : Children) : ∀ e ∈ kids κ ch, 0 < e.2 := by
  intro e he
  cases κ <;> cases ch <;> simp only [kids, List.not_mem_nil] at he
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 he; exact Nat.one_pos
  · obtain ⟨c, hc, rfl⟩ : ∃ a ∈ _, (a, Multiset.count a _) = e := by
      simpa [Multiset.entries] using he
    exact Multiset.count_pos.2 hc
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 he; exact Nat.one_pos

theorem OTX.pos {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (h : OTX ctx k P ks v ls o) (hk : 0 < k)
    (hks : ∀ e ∈ ks, 0 < e.2) : ∀ e ∈ v, 0 < e.2 := by
  induction h with
  | nil => simp
  | @keep k P X j rest v₂ l₂ o _ ih =>
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Nat.mul_pos hk (hks (X, j) (List.mem_cons_self ..))
      · exact ih hk (fun e he => hks e (List.mem_cons_of_mem _ he)) e he
  | @opn k P X j rest id m v₁ v₂ l₁ l₂ o₁ o₂ _ _ _ _ ih₁ ih₂ =>
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact ih₁ (Nat.mul_pos hk (hks (X, j) (List.mem_cons_self ..))) (kids_pos _ _) e he
      · exact ih₂ hk (fun e he => hks e (List.mem_cons_of_mem _ he)) e he

theorem RawViewX.pos {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List LeafX} {o : Nat}
    (h : RawViewX ctx n v ls o) : ∀ e ∈ v, 0 < e.2 :=
  OTX.pos h Nat.one_pos (kids_pos _ _)

/-! ## Tree facts -/

theorem OTX.all_kept_aux {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (h : OTX ctx k P ks v ls o) (hls : ls = []) :
    v = scale k ks ∧ o = 0 := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | keep _ ih =>
      subst hls
      obtain ⟨h1, h2⟩ := ih rfl
      exact ⟨by simp [scale, h1], h2⟩
  | opn _ _ _ _ _ _ =>
      exact absurd (List.append_eq_nil_iff.mp hls).1 (leafifyX_ne_nil _ _ _)

/-- A tree with no leaf opens nothing. -/
theorem OTX.all_kept {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)} {o : Nat}
    (h : OTX ctx k P ks v [] o) : v = scale k ks ∧ o = 0 :=
  OTX.all_kept_aux h rfl

/-- A tree with openings has a leaf. -/
theorem OTX.ne_nil_of_pos {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (h : OTX ctx k P ks v ls o) (ho : 0 < o) : ls ≠ [] := by
  rintro rfl
  have := (OTX.all_kept h).2
  omega

/-- Closing the leaf `l = (X, g)`: it is an `opn` node whose subtree has no
leaf, so it kept all of `m`'s children scaled by some `k' > 0`; replacing
it by `keep` gives a tree over the same positions with one opening fewer. -/
theorem OTX.refold {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} {l : LeafX} (h : OTX ctx k P ks v ls o) (hl : l ∈ ls)
    (hk : 0 < k) (hks : ∀ e ∈ ks, 0 < e.2) :
    ∃ (v₁ v₂ : List (C × Nat)) (k' : Nat) (id : NodeId) (m : Node) (ls' : List LeafX)
      (o' : Nat),
      ctx.IsMember id m l.1 ∧ l.2 = (kids ctx.κ m.children).map Prod.fst ∧
      v = v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂ ∧ 0 < k' ∧
      OTX ctx k P ks (v₁ ++ (l.1, k') :: v₂) ls' o' ∧ o = o' + 1 := by
  induction h with
  | nil => simp at hl
  | @keep k P X j rest v₂ l₂ o _ ih =>
      obtain ⟨v₁', v₂', k'', id, m, ls', o', hmem, hgeq, hv, hk', ht, ho⟩ :=
        ih hl hk (fun e he => hks e (List.mem_cons_of_mem _ he))
      refine ⟨(X, k * j) :: v₁', v₂', k'', id, m, ls', o', hmem, hgeq, ?_, hk', ?_, ho⟩
      · subst hv; simp
      · exact OTX.keep ht
  | @opn k P X j rest id m v₁ v₂ l₁ l₂ o₁ o₂ hXP hmem h₁ h₂ ih₁ ih₂ =>
      have hkj : 0 < k * j := Nat.mul_pos hk (hks (X, j) (List.mem_cons_self ..))
      rcases List.mem_append.mp hl with hl₁ | hl₂
      · by_cases hl₁' : l₁ = []
        · subst hl₁'
          simp only [leafifyX, ite_true, List.mem_singleton] at hl₁
          subst hl₁
          obtain ⟨hv₁, ho₁⟩ := OTX.all_kept h₁
          subst ho₁
          refine ⟨[], v₂, k * j, id, m, l₂, o₂, hmem, ?_, ?_, hkj, ?_, by omega⟩
          · rw [hv₁, map_fst_scale]
          · rw [hv₁]; rfl
          · exact OTX.keep h₂
        · simp only [leafifyX, hl₁', ↓reduceIte] at hl₁
          obtain ⟨v₁', v₂', k'', id', m', ls', o', hmem', hgeq, hv, hk', ht, ho⟩ :=
            ih₁ hl₁ hkj (kids_pos _ _)
          refine ⟨v₁', v₂' ++ v₂, k'', id', m',
            leafifyX X (v₁' ++ (l.1, k'') :: v₂') ls' ++ l₂, o' + o₂ + 1, hmem', hgeq, ?_, hk',
            ?_, by omega⟩
          · subst hv; simp
          · have := OTX.opn hXP hmem ht h₂
            simpa using this
      · obtain ⟨v₁', v₂', k'', id', m', ls', o', hmem', hgeq, hv, hk', ht, ho⟩ :=
          ih₂ hl₂ hk (fun e he => hks e (List.mem_cons_of_mem _ he))
        refine ⟨v₁ ++ v₁', v₂', k'', id', m', leafifyX X v₁ l₁ ++ ls', o₁ + o' + 1, hmem', hgeq,
          ?_, hk', ?_, by omega⟩
        · subst hv; simp
        · have := OTX.opn hXP hmem h₁ ht
          simpa using this

theorem RawViewX.refold {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List LeafX}
    {o : Nat} {l : LeafX} (h : RawViewX ctx n v ls o) (hl : l ∈ ls) :
    ∃ (v₁ v₂ : List (C × Nat)) (k' : Nat) (id : NodeId) (m : Node) (ls' : List LeafX)
      (o' : Nat),
      ctx.IsMember id m l.1 ∧ l.2 = (kids ctx.κ m.children).map Prod.fst ∧
      v = v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂ ∧ 0 < k' ∧
      RawViewX ctx n (v₁ ++ (l.1, k') :: v₂) ls' o' ∧ o = o' + 1 :=
  OTX.refold h hl Nat.one_pos (kids_pos _ _)

/-! ## The corrected demand -/

/-- The corrected per-leaf condition: the leaf group contains a taken class,
or the class the leaf opened is itself taken. -/
def LeafX.ok (taken : List C) (l : LeafX) : Prop :=
  l.1 ∈ taken ∨ ∃ c ∈ l.2, c ∈ taken

instance (taken : List C) (l : LeafX) : Decidable (l.ok taken) := by
  unfold LeafX.ok; infer_instance

/-- `Demand` with the opened class per leaf. -/
structure DemandX where
  unconditional : Bool
  alts : List (List LeafX)
  deriving DecidableEq

/-- Forgetting the opened classes. -/
def DemandX.proj (d : DemandX) : Demand := ⟨d.unconditional, d.alts.map (List.map Prod.snd)⟩

/-- The corrected demand rule: unconditional, or some opening tree has every
leaf satisfied in the sense of `LeafX.ok`. -/
def DemandX.acceptsFix (d : DemandX) (taken : List C) : Prop :=
  d.unconditional = true ∨ ∃ ls ∈ d.alts, ∀ l ∈ ls, l.ok taken

/-- The executable form of `DemandX.acceptsFix`. -/
def DemandX.acceptsFixB (d : DemandX) (taken : List C) : Bool :=
  d.unconditional || d.alts.any (fun ls => ls.all (fun l => decide (l.ok taken)))

theorem DemandX.acceptsFixB_iff (d : DemandX) (taken : List C) :
    d.acceptsFixB taken = true ↔ d.acceptsFix taken := by
  simp [DemandX.acceptsFixB, DemandX.acceptsFix]

/-- The original rule is at most as permissive as the corrected one. -/
theorem DemandX.accepts_proj_imp (d : DemandX) (taken : List C)
    (h : d.proj.accepts taken) : d.acceptsFix taken := by
  rcases h with h | ⟨ls, hls, hall⟩
  · exact Or.inl h
  · obtain ⟨lsx, hlsx, rfl⟩ := List.mem_map.1 hls
    refine Or.inr ⟨lsx, hlsx, fun l hl => Or.inr ?_⟩
    exact hall l.2 (List.mem_map_of_mem hl)

/-- The opening trees giving `w`, with leaf data. -/
def AltsX (ctx : Ctx) (laws : Laws) (n : Node) (w : List (C × Nat)) : Set (List LeafX) :=
  { ls | ∃ v o, RawViewX ctx n v ls o ∧ normalize ctx.κ laws v = .node w }

/-- The corrected rule on the set of opening trees of a view. -/
def AltsXAccept (A : Set (List LeafX)) (taken : List C) : Prop :=
  [] ∈ A ∨ ∃ ls ∈ A, ∀ l ∈ ls, l.ok taken

/-- `MatchFlat` with the corrected rule. -/
def MatchFlatX (ctx : Ctx) (laws : Laws) (P : Pat) (n : Node) (σ : Binding) : Prop :=
  ∃ w ∈ Views ctx laws n, ∃ taken,
    MatchV ctx.G P (ofView ctx.κ w) σ taken ∧ AltsXAccept (AltsX ctx laws n w) taken

/-! ## The reference enumerator with leaf data -/

def kidsOfX (opt : C → Nat → Finset C → List RawX) :
    List (C × Nat) → Nat → Finset C → List RawX
  | [], _, _ => [([], [])]
  | (X, j) :: rest, k, P =>
      (opt X (k * j) P).flatMap (fun r₁ =>
        (kidsOfX opt rest k P).map (fun r₂ => (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2)))

def rawOptX (ctx : Ctx) : Nat → C → Nat → Finset C → List RawX
  | 0, X, k, _ => [([(X, k)], [])]
  | fuel + 1, X, k, P =>
      ([(X, k)], []) ::
        (if X ∈ P then []
         else (ctx.members X).flatMap (fun p =>
           (kidsOfX (rawOptX ctx fuel) (kids ctx.κ p.2.children) k (insert X P)).map
             (fun r => (r.1, leafifyX X r.1 r.2))))

def rawNodeX (ctx : Ctx) (fuel : Nat) (m : Node) (k : Nat) (P : Finset C) : List RawX :=
  kidsOfX (rawOptX ctx fuel) (kids ctx.κ m.children) k P

def rawRecordsX (ctx : Ctx) (laws : Laws) (n : Node) : List RawX :=
  (rawNodeX ctx (fuelOf ctx.G) n 1 ∅).filterMap (fun r =>
    match normalize ctx.κ laws r.1 with
    | .node w => some (w, r.2)
    | _ => none)

def altsOfX (recs : List RawX) (w : List (C × Nat)) : List (List LeafX) :=
  (recs.filter (fun r => r.1 = w)).map Prod.snd

def demandOfX (recs : List RawX) (w : List (C × Nat)) : DemandX :=
  if [] ∈ altsOfX recs w then ⟨true, []⟩ else ⟨false, altsOfX recs w⟩

def enumerateFromX (recs : List RawX) : List (List (C × Nat) × DemandX) :=
  (recs.map Prod.fst).dedup.map (fun w => (w, demandOfX recs w))

/-- `enumerate` with the opened class recorded per leaf. -/
def enumerateX (ctx : Ctx) (laws : Laws) (n : Node) : List (List (C × Nat) × DemandX) :=
  enumerateFromX (rawRecordsX ctx laws n)

/-- The projection of a record. -/
def RawX.proj (r : RawX) : Raw := (r.1, r.2.map Prod.snd)

/-! ## Refolding a rest -/

/-- One AC refold step on a rest: the children of an `f`-member `m` of `X`,
scaled by `k' > 0`, are replaced by `k'` copies of `X`. -/
def RefoldStepAC (ctx : Ctx) (m₀ m₁ : Multiset C) : Prop :=
  ∃ (id : NodeId) (m : Node) (X : C) (k' : Nat), ctx.IsMember id m X ∧ 0 < k' ∧
    ofEntries (scale k' (kids ctx.κ m.children)) ≤ m₀ ∧
    m₁ = m₀ - ofEntries (scale k' (kids ctx.κ m.children)) + Multiset.replicate k' X

/-- Zero or more AC refold steps. -/
def RefoldsAC (ctx : Ctx) : Multiset C → Multiset C → Prop :=
  Relation.ReflTransGen (RefoldStepAC ctx)

/-- One ACI refold step on a set rest: some of the children of an
`f`-member `m` of `X` (those occurring nowhere else in the view) are removed
and `X` is inserted. -/
def RefoldStepACI (ctx : Ctx) (s₀ s₁ : Finset C) : Prop :=
  ∃ (id : NodeId) (m : Node) (X : C) (D : Finset C), ctx.IsMember id m X ∧
    D ⊆ ((kids ctx.κ m.children).map Prod.fst).toFinset ∧ s₁ = insert X (s₀ \ D)

def RefoldsACI (ctx : Ctx) : Finset C → Finset C → Prop :=
  Relation.ReflTransGen (RefoldStepACI ctx)

/-- One Assoc refold step on a sequence rest: a contiguous block equal to
the children of an `f`-member `m` of `X` is replaced by `X`. -/
def RefoldStepAssoc (ctx : Ctx) (l₀ l₁ : List C) : Prop :=
  ∃ (id : NodeId) (m : Node) (X : C) (a b : List C), ctx.IsMember id m X ∧
    l₀ = a ++ (kids ctx.κ m.children).map Prod.fst ++ b ∧ l₁ = a ++ X :: b

def RefoldsAssoc (ctx : Ctx) : List C → List C → Prop :=
  Relation.ReflTransGen (RefoldStepAssoc ctx)


/-! ## The enumerator with leaf data: soundness, completeness, projection

The theorems of `Enum.lean` for the `X` variants above, and the projection
of `enumerateX` onto `enumerate` (`enumerateX_proj`). -/


/-! ## The spec's constructor shapes, recovered -/

theorem OTX.cons_opt {ctx : Ctx} {k j : Nat} {P : Finset C} {X : C}
    {rest v₁ v₂ : List (C × Nat)} {l₁ l₂ : List LeafX} {o₁ o₂ : Nat}
    (h₁ : ViewOptX ctx X (k * j) P v₁ l₁ o₁) (h₂ : OTX ctx k P rest v₂ l₂ o₂) :
    OTX ctx k P ((X, j) :: rest) (v₁ ++ v₂) (l₁ ++ l₂) (o₁ + o₂) := by
  rcases h₁ with ⟨rfl, rfl, rfl⟩ | ⟨hX, id, m, l, o, hmem, hm, rfl, rfl⟩
  · simpa using OTX.keep h₂
  · rw [show o + 1 + o₂ = o + o₂ + 1 by omega]
    exact OTX.opn hX hmem hm h₂

theorem OTX.cons_inv {ctx : Ctx} {k j : Nat} {P : Finset C} {X : C}
    {rest v : List (C × Nat)} {ls : List LeafX} {o : Nat}
    (h : OTX ctx k P ((X, j) :: rest) v ls o) :
    ∃ v₁ l₁ o₁ v₂ l₂ o₂, v = v₁ ++ v₂ ∧ ls = l₁ ++ l₂ ∧ o = o₁ + o₂ ∧
      ViewOptX ctx X (k * j) P v₁ l₁ o₁ ∧ OTX ctx k P rest v₂ l₂ o₂ := by
  cases h with
  | keep h₂ => exact ⟨_, [], 0, _, _, _, rfl, rfl, by simp, Or.inl ⟨rfl, rfl, rfl⟩, h₂⟩
  | opn hX hmem hm h₂ =>
      exact ⟨_, _, _, _, _, _, rfl, rfl, by omega,
        Or.inr ⟨hX, _, _, _, _, hmem, hm, rfl, rfl⟩, h₂⟩

theorem ViewOptX.keep {ctx : Ctx} {X : C} {k : Nat} {P : Finset C} :
    ViewOptX ctx X k P [(X, k)] [] 0 := Or.inl ⟨rfl, rfl, rfl⟩

theorem ViewOptX.opn {ctx : Ctx} {X : C} {k : Nat} {P : Finset C} {id : NodeId}
    {m : Node} {v : List (C × Nat)} {ls : List LeafX} {o : Nat}
    (hX : X ∉ P) (hmem : ctx.IsMember id m X)
    (h : ViewNodeX ctx m k (insert X P) v ls o) :
    ViewOptX ctx X k P v (leafifyX X v ls) (o + 1) :=
  Or.inr ⟨hX, id, m, ls, o, hmem, h, rfl, rfl⟩

/-! ## Soundness of the walk -/

theorem kidsOfX_sound_of {ctx : Ctx} (opt : C → Nat → Finset C → List RawX)
    (hopt : ∀ X k P r, r ∈ opt X k P → ∃ o, ViewOptX ctx X k P r.1 r.2 o) :
    ∀ (ks : List (C × Nat)) (k : Nat) (P : Finset C) (r : RawX),
      r ∈ kidsOfX opt ks k P → ∃ o, OTX ctx k P ks r.1 r.2 o := by
  intro ks
  induction ks with
  | nil =>
      intro k P r hr
      simp only [kidsOfX, List.mem_singleton] at hr
      subst hr
      exact ⟨0, OTX.nil⟩
  | cons e rest ih =>
      intro k P r hr
      obtain ⟨X, j⟩ := e
      simp only [kidsOfX, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr
      obtain ⟨o₁, h₁⟩ := hopt _ _ _ _ hr₁
      obtain ⟨o₂, h₂⟩ := ih _ _ _ hr₂
      exact ⟨_, OTX.cons_opt h₁ h₂⟩

theorem rawOptX_sound (ctx : Ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (r : RawX),
      r ∈ rawOptX ctx fuel X k P → ∃ o, ViewOptX ctx X k P r.1 r.2 o := by
  intro fuel
  induction fuel with
  | zero =>
      intro X k P r hr
      simp only [rawOptX, List.mem_singleton] at hr
      subst hr
      exact ⟨0, ViewOptX.keep⟩
  | succ fuel ih =>
      intro X k P r hr
      simp only [rawOptX, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨0, ViewOptX.keep⟩
      · split at hr
        · simp at hr
        · next hX =>
          simp only [List.mem_flatMap, List.mem_map] at hr
          obtain ⟨p, hp, r', hr', rfl⟩ := hr
          have hmem := Ctx.mem_members.1 hp
          obtain ⟨o, ho⟩ := kidsOfX_sound_of _ ih _ _ _ _ hr'
          exact ⟨_, ViewOptX.opn hX hmem ho⟩

theorem rawNodeX_sound {ctx : Ctx} {fuel : Nat} {m : Node} {k : Nat} {P : Finset C}
    {r : RawX} (hr : r ∈ rawNodeX ctx fuel m k P) : ∃ o, ViewNodeX ctx m k P r.1 r.2 o :=
  kidsOfX_sound_of _ (rawOptX_sound ctx fuel) _ _ _ _ hr

/-! ## Completeness of the walk -/

theorem kidsOfX_complete_of {ctx : Ctx} (fuel : Nat) (opt : C → Nat → Finset C → List RawX)
    (hopt : ∀ X k P v ls o, ViewOptX ctx X k P v ls o → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → (v, ls) ∈ opt X k P)
    {ks : List (C × Nat)} {k : Nat} {P : Finset C} {v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (h : OTX ctx k P ks v ls o)
    (hP : P ⊆ classesOf ctx.G) (hfuel : (classesOf ctx.G).card - P.card ≤ fuel) :
    (v, ls) ∈ kidsOfX opt ks k P := by
  induction h with
  | nil => simp [kidsOfX]
  | keep h₂ ih =>
      simp only [kidsOfX, List.mem_flatMap, List.mem_map]
      exact ⟨_, hopt _ _ _ _ _ _ ViewOptX.keep hP hfuel, _, ih hP hfuel, rfl⟩
  | opn hX hmem hm h₂ ih₁ ih₂ =>
      simp only [kidsOfX, List.mem_flatMap, List.mem_map]
      exact ⟨_, hopt _ _ _ _ _ _ (ViewOptX.opn hX hmem hm) hP hfuel, _, ih₂ hP hfuel, rfl⟩

theorem rawOptX_complete (ctx : Ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (v : List (C × Nat))
      (ls : List LeafX) (o : Nat), ViewOptX ctx X k P v ls o → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → (v, ls) ∈ rawOptX ctx fuel X k P := by
  intro fuel
  induction fuel with
  | zero =>
      intro X k P v ls o h hP hfuel
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨hX, id, m, l₁, o₁, hmem, hm, rfl, rfl⟩
      · simp [rawOptX]
      · exfalso
        have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hmem
        have hlt : P.card < (classesOf ctx.G).card :=
          Finset.card_lt_card ⟨hP, fun hsub => hX (hsub hXc)⟩
        omega
  | succ fuel ih =>
      intro X k P v ls o h hP hfuel
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨hX, id, m, l₁, o₁, hmem, hm, rfl, rfl⟩
      · simp [rawOptX]
      · simp only [rawOptX, List.mem_cons]
        right
        simp only [hX, ↓reduceIte]
        simp only [List.mem_flatMap, List.mem_map]
        refine ⟨(id, m), Ctx.mem_members.2 hmem, (v, l₁), ?_, rfl⟩
        have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hmem
        have hP' : insert X P ⊆ classesOf ctx.G := Finset.insert_subset hXc hP
        have hcard : (insert X P).card = P.card + 1 := Finset.card_insert_of_notMem hX
        exact kidsOfX_complete_of fuel _ ih hm hP' (by omega)

theorem rawNodeX_complete {ctx : Ctx} {m : Node} {k : Nat} {P : Finset C}
    {v : List (C × Nat)} {ls : List LeafX} {o : Nat} (h : ViewNodeX ctx m k P v ls o)
    (hP : P ⊆ classesOf ctx.G) {fuel : Nat}
    (hfuel : (classesOf ctx.G).card - P.card ≤ fuel) :
    (v, ls) ∈ rawNodeX ctx fuel m k P :=
  kidsOfX_complete_of fuel _ (rawOptX_complete ctx fuel) h hP hfuel

theorem rawViewX_mem_rawNodeX {ctx : Ctx} {n : Node} {v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (h : RawViewX ctx n v ls o) :
    (v, ls) ∈ rawNodeX ctx (fuelOf ctx.G) n 1 ∅ :=
  rawNodeX_complete h (Finset.empty_subset _) (by simp [fuelOf])

/-! ## Records, demands, the distinct views -/

theorem mem_rawRecordsX {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {ls : List LeafX} :
    (w, ls) ∈ rawRecordsX ctx laws n ↔
      ∃ v o, RawViewX ctx n v ls o ∧ normalize ctx.κ laws v = .node w := by
  simp only [rawRecordsX, List.mem_filterMap]
  constructor
  · rintro ⟨⟨v, ls'⟩, hr, hn⟩
    revert hn
    split
    · next w' hw' =>
      intro hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨o, ho⟩ := rawNodeX_sound hr
      exact ⟨v, o, ho, hw'⟩
    · intro hn
      exact absurd hn (by simp)
  · rintro ⟨v, o, hv, hn⟩
    refine ⟨(v, ls), rawViewX_mem_rawNodeX hv, ?_⟩
    simp only
    rw [hn]

theorem mem_enumerateFromX {recs : List RawX} {w : List (C × Nat)} {d : DemandX} :
    (w, d) ∈ enumerateFromX recs ↔ (∃ ls, (w, ls) ∈ recs) ∧ d = demandOfX recs w := by
  simp only [enumerateFromX, List.mem_map, List.mem_dedup, Prod.mk.injEq]
  constructor
  · rintro ⟨w', hw', rfl, rfl⟩
    obtain ⟨⟨w'', ls⟩, hr, rfl⟩ := hw'
    exact ⟨⟨ls, hr⟩, rfl⟩
  · rintro ⟨⟨ls, hr⟩, rfl⟩
    exact ⟨w, ⟨(w, ls), hr, rfl⟩, rfl, rfl⟩

theorem mem_altsOfX {recs : List RawX} {w : List (C × Nat)} {ls : List LeafX} :
    ls ∈ altsOfX recs w ↔ (w, ls) ∈ recs := by
  simp only [altsOfX, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨w', ls'⟩, ⟨hr, hw⟩, hls⟩
    simp only at hw hls
    subst hw; subst hls
    exact hr
  · intro hr
    exact ⟨(w, ls), ⟨hr, rfl⟩, rfl⟩

theorem demandOfX_unconditional {recs : List RawX} {w : List (C × Nat)} :
    (demandOfX recs w).unconditional = true ↔ (w, []) ∈ recs := by
  by_cases h0 : [] ∈ altsOfX recs w
  · simp only [demandOfX, h0, ↓reduceIte, true_iff]
    exact mem_altsOfX.1 h0
  · simp only [demandOfX, h0, ↓reduceIte, Bool.false_eq_true, false_iff]
    exact fun hr => h0 (mem_altsOfX.2 hr)

theorem demandOfX_alts {recs : List RawX} {w : List (C × Nat)}
    (h : (demandOfX recs w).unconditional = false) (ls : List LeafX) :
    ls ∈ (demandOfX recs w).alts ↔ (w, ls) ∈ recs := by
  by_cases h0 : [] ∈ altsOfX recs w
  · simp [demandOfX, h0] at h
  · simp only [demandOfX, h0, ↓reduceIte]
    exact mem_altsOfX

/-- `DemandX.acceptsFix` on a record list's demand: some record of the view
has every leaf satisfied (the no-opening record vacuously). -/
theorem acceptsFix_demandOfX {recs : List RawX} {w : List (C × Nat)} {taken : List C} :
    (demandOfX recs w).acceptsFix taken ↔
      ∃ ls, (w, ls) ∈ recs ∧ ∀ l ∈ ls, l.ok taken := by
  unfold DemandX.acceptsFix
  by_cases hu : (demandOfX recs w).unconditional = true
  · simp only [hu, true_or, true_iff]
    exact ⟨[], demandOfX_unconditional.1 hu, by simp⟩
  · have hu' : (demandOfX recs w).unconditional = false := by simpa using hu
    simp only [hu', Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨ls, hls, hall⟩
      exact ⟨ls, (demandOfX_alts hu' ls).1 hls, hall⟩
    · rintro ⟨ls, hls, hall⟩
      exact ⟨ls, (demandOfX_alts hu' ls).2 hls, hall⟩

/-! ## Soundness and completeness of `enumerateX` -/

theorem views_soundX {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {d : DemandX} (h : (w, d) ∈ enumerateX ctx laws n) :
    w ∈ Views ctx laws n ∧
      (d.unconditional = true ↔ [] ∈ AltsX ctx laws n w) ∧
      (d.unconditional = false → ∀ ls, ls ∈ d.alts ↔ ls ∈ AltsX ctx laws n w) := by
  obtain ⟨⟨ls, hr⟩, rfl⟩ := mem_enumerateFromX.1 h
  obtain ⟨v, o, hv, hn⟩ := mem_rawRecordsX.1 hr
  refine ⟨⟨v, ls.map Prod.snd, hv.toRawView, hn⟩, ?_, ?_⟩
  · rw [demandOfX_unconditional, mem_rawRecordsX]
    rfl
  · intro hu ls'
    rw [demandOfX_alts hu, mem_rawRecordsX]
    rfl

theorem views_completeX {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (hv : RawViewX ctx n v ls o)
    (hn : normalize ctx.κ laws v = .node w) :
    ∃ d, (w, d) ∈ enumerateX ctx laws n ∧
      (ls = [] → d.unconditional = true) ∧
      (ls ≠ [] → d.unconditional = true ∨ ls ∈ d.alts) := by
  have hr : (w, ls) ∈ rawRecordsX ctx laws n := mem_rawRecordsX.2 ⟨v, o, hv, hn⟩
  refine ⟨demandOfX (rawRecordsX ctx laws n) w, mem_enumerateFromX.2 ⟨⟨ls, hr⟩, rfl⟩, ?_, ?_⟩
  · rintro rfl
    exact demandOfX_unconditional.2 hr
  · intro _
    by_cases hu : (demandOfX (rawRecordsX ctx laws n) w).unconditional = true
    · exact Or.inl hu
    · right
      exact (demandOfX_alts (by simpa using hu) ls).2 hr

/-- The emitted view set is exactly `Views`. -/
theorem mem_enumerateX_iff {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)} :
    (∃ d, (w, d) ∈ enumerateX ctx laws n) ↔ w ∈ Views ctx laws n := by
  constructor
  · rintro ⟨d, hd⟩
    exact (views_soundX hd).1
  · rintro ⟨v, ls, hv, hn⟩
    obtain ⟨lsx, o, hvx, -⟩ := hv.toRawViewX
    obtain ⟨d, hd, -⟩ := views_completeX hvx hn
    exact ⟨d, hd⟩

/-- One demand per emitted view. -/
theorem enumerateX_demand_unique {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d d' : DemandX} (h : (w, d) ∈ enumerateX ctx laws n)
    (h' : (w, d') ∈ enumerateX ctx laws n) : d = d' := by
  rw [(mem_enumerateFromX.1 h).2, (mem_enumerateFromX.1 h').2]

/-- The corrected rule, read through the emitted demand: `AltsXAccept` on
the opening trees of `w`. -/
theorem acceptsFix_iff_altsXAccept {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : DemandX} (h : (w, d) ∈ enumerateX ctx laws n)
    (taken : List C) :
    d.acceptsFix taken ↔ AltsXAccept (AltsX ctx laws n w) taken := by
  obtain ⟨-, rfl⟩ := mem_enumerateFromX.1 h
  rw [acceptsFix_demandOfX]
  unfold AltsXAccept
  constructor
  · rintro ⟨ls, hr, hall⟩
    obtain ⟨v, o, hv, hn⟩ := mem_rawRecordsX.1 hr
    exact Or.inr ⟨ls, ⟨v, o, hv, hn⟩, hall⟩
  · rintro (⟨v, o, hv, hn⟩ | ⟨ls, ⟨v, o, hv, hn⟩, hall⟩)
    · exact ⟨[], mem_rawRecordsX.2 ⟨v, o, hv, hn⟩, by simp⟩
    · exact ⟨ls, mem_rawRecordsX.2 ⟨v, o, hv, hn⟩, hall⟩

/-! ## Projection onto the original enumerator -/

theorem kidsOfX_proj (opt : C → Nat → Finset C → List Raw)
    (optX : C → Nat → Finset C → List RawX)
    (hopt : ∀ X k P, opt X k P = (optX X k P).map RawX.proj) :
    ∀ (ks : List (C × Nat)) (k : Nat) (P : Finset C),
      kidsOf opt ks k P = (kidsOfX optX ks k P).map RawX.proj := by
  intro ks
  induction ks with
  | nil => intro k P; simp [kidsOf, kidsOfX, RawX.proj]
  | cons e rest ih =>
      intro k P
      obtain ⟨X, j⟩ := e
      simp only [kidsOf, kidsOfX, hopt, ih, List.flatMap_map, List.map_flatMap, List.map_map]
      congr 1
      funext r₁
      congr 1
      funext r₂
      simp [RawX.proj]

theorem rawOptX_proj (ctx : Ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C),
      rawOpt ctx fuel X k P = (rawOptX ctx fuel X k P).map RawX.proj := by
  intro fuel
  induction fuel with
  | zero => intro X k P; simp [rawOpt, rawOptX, RawX.proj]
  | succ fuel ih =>
      intro X k P
      simp only [rawOpt, rawOptX, List.map_cons]
      congr 1
      split
      · simp
      · simp only [List.map_flatMap, List.map_map]
        congr 1
        funext p
        rw [kidsOfX_proj _ _ ih, List.map_map]
        congr 1
        funext r
        simp [RawX.proj, leafifyX_map_snd]

theorem rawRecordsX_proj (ctx : Ctx) (laws : Laws) (n : Node) :
    rawRecords ctx laws n = (rawRecordsX ctx laws n).map RawX.proj := by
  unfold rawRecords rawRecordsX rawNode rawNodeX
  rw [kidsOfX_proj _ _ (rawOptX_proj ctx (fuelOf ctx.G)), List.filterMap_map,
    List.map_filterMap]
  congr 1
  funext r
  simp only [Function.comp, RawX.proj]
  cases normalize ctx.κ laws r.1 <;> simp [RawX.proj]

theorem altsOfX_proj (recs : List RawX) (w : List (C × Nat)) :
    altsOf (recs.map RawX.proj) w = (altsOfX recs w).map (List.map Prod.snd) := by
  unfold altsOf altsOfX
  rw [List.filter_map, List.map_map, List.map_map]
  rfl

theorem demandOfX_proj (recs : List RawX) (w : List (C × Nat)) :
    demandOf (recs.map RawX.proj) w = (demandOfX recs w).proj := by
  have hnil : [] ∈ altsOf (recs.map RawX.proj) w ↔ [] ∈ altsOfX recs w := by
    rw [altsOfX_proj]
    simp only [List.mem_map, List.map_eq_nil_iff]
    constructor
    · rintro ⟨ls, hls, rfl⟩; exact hls
    · intro h; exact ⟨[], h, rfl⟩
  unfold demandOf demandOfX
  by_cases h0 : [] ∈ altsOfX recs w
  · simp [hnil.2 h0, h0, DemandX.proj]
  · simp [h0, DemandX.proj, altsOfX_proj]

theorem enumerateX_proj (ctx : Ctx) (laws : Laws) (n : Node) :
    enumerate ctx laws n = (enumerateX ctx laws n).map (fun wd => (wd.1, wd.2.proj)) := by
  unfold enumerate enumerateX enumerateFrom enumerateFromX
  rw [rawRecordsX_proj, List.map_map, List.map_map]
  have hfst : (Prod.fst ∘ RawX.proj) = (Prod.fst : RawX → List (C × Nat)) := by
    funext r; rfl
  rw [hfst]
  congr 1
  funext w
  simp [demandOfX_proj]

end Semper.EMatch.Flatten
