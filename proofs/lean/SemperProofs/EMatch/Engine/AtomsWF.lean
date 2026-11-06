import SemperProofs.EMatch.Engine.SchedRun

/-!
# Well-formedness of the flattened atoms (`AtomsWF`)

The atoms `atoms P r` of a well-kinded pattern `P` with duplicate-free rest
variables form an `AtomsWF` list: every atom is well-kinded, node variables
are pairwise distinct (the root is `r`, nested nodes are drawn from the
fresh counter), rest variables are split among the atoms without repetition,
and no `.eq` atom occurs.

The specification of the mutual flattening `atomsAt` / `atomsChild` /
`atomsChildren` / `atomsChildrenAC` is `AtomsWFProof.Out`, proved by strong
induction on `sizeOf`.
-/

namespace Semper.EMatch

open scoped List

namespace AtomsWFProof

/-! ## Unfolding the mutual flattening -/

theorem atomsAt_var (x n : Var) (fresh : Nat) : atomsAt (.var x) n fresh = ([], fresh) := by
  rw [atomsAt]

theorem atomsAt_plain (f : Sym) (args : List Pat) (n : Var) (fresh : Nat)
    {vs : List Var} {as : List RAtom} {fr : Nat} (h : atomsChildren args fresh = (vs, as, fr)) :
    atomsAt (.plain f args) n fresh = (as ++ [⟨n, f, .plain vs⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsAt_comm (f : Sym) (p q : Pat) (n : Var) (fresh : Nat)
    {vp vq : Var} {ap aq : List RAtom} {fr₁ fr₂ : Nat}
    (h₁ : atomsChild p fresh = (vp, ap, fr₁)) (h₂ : atomsChild q fr₁ = (vq, aq, fr₂)) :
    atomsAt (.comm f p q) n fresh = (ap ++ aq ++ [⟨n, f, .comm vp vq⟩], fr₂) := by
  rw [atomsAt]; simp [h₁, h₂]

theorem atomsAt_assoc (f : Sym) (pre : Option Var) (args : List Pat) (suf : Option Var)
    (n : Var) (fresh : Nat) {vs : List Var} {as : List RAtom} {fr : Nat}
    (h : atomsChildren args fresh = (vs, as, fr)) :
    atomsAt (.assoc f pre args suf) n fresh = (as ++ [⟨n, f, .assoc pre vs suf⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsAt_ac (f : Sym) (elems : List (Pat × Mult)) (rest : Option Var) (n : Var)
    (fresh : Nat) {vs : List (Var × Mult)} {as : List RAtom} {fr : Nat}
    (h : atomsChildrenAC elems fresh = (vs, as, fr)) :
    atomsAt (.ac f elems rest) n fresh = (as ++ [⟨n, f, .ac vs rest⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsAt_aci (f : Sym) (elems : List Pat) (rest : Option Var) (n : Var) (fresh : Nat)
    {vs : List Var} {as : List RAtom} {fr : Nat} (h : atomsChildren elems fresh = (vs, as, fr)) :
    atomsAt (.aci f elems rest) n fresh = (as ++ [⟨n, f, .aci vs rest⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsChild_var (x : Var) (fresh : Nat) : atomsChild (.var x) fresh = (x, [], fresh) := by
  rw [atomsChild]

/-- A child application is flattened at the fresh variable with the counter
advanced. -/
theorem atomsChild_app (p : Pat) (fresh : Nat) (hp : p.head.isSome = true)
    {as : List RAtom} {fr : Nat} (h : atomsAt p fresh (fresh + 1) = (as, fr)) :
    atomsChild p fresh = (fresh, as, fr) := by
  cases p with
  | var x => simp [Pat.head] at hp
  | plain f args => rw [atomsChild]; simp [h]
  | comm f p q => rw [atomsChild]; simp [h]
  | assoc f pre args suf => rw [atomsChild]; simp [h]
  | ac f elems rest => rw [atomsChild]; simp [h]
  | aci f elems rest => rw [atomsChild]; simp [h]

theorem atomsChildren_nil (fresh : Nat) : atomsChildren [] fresh = ([], [], fresh) := by
  rw [atomsChildren]

theorem atomsChildren_cons (p : Pat) (ps : List Pat) (fresh : Nat)
    {v : Var} {ap : List RAtom} {fr₁ : Nat} {vs : List Var} {as : List RAtom} {fr₂ : Nat}
    (h₁ : atomsChild p fresh = (v, ap, fr₁)) (h₂ : atomsChildren ps fr₁ = (vs, as, fr₂)) :
    atomsChildren (p :: ps) fresh = (v :: vs, ap ++ as, fr₂) := by
  rw [atomsChildren]; simp [h₁, h₂]

theorem atomsChildrenAC_nil (fresh : Nat) : atomsChildrenAC [] fresh = ([], [], fresh) := by
  rw [atomsChildrenAC]

theorem atomsChildrenAC_cons (p : Pat) (μ : Mult) (es : List (Pat × Mult)) (fresh : Nat)
    {v : Var} {ap : List RAtom} {fr₁ : Nat} {vs : List (Var × Mult)} {as : List RAtom}
    {fr₂ : Nat} (h₁ : atomsChild p fresh = (v, ap, fr₁))
    (h₂ : atomsChildrenAC es fr₁ = (vs, as, fr₂)) :
    atomsChildrenAC ((p, μ) :: es) fresh = ((v, μ) :: vs, ap ++ as, fr₂) := by
  rw [atomsChildrenAC]; simp [h₁, h₂]

/-! ## The output specification -/

/-- What a list of flattened atoms satisfies: node variables in `N`, pairwise
distinct; the concatenated rest variables a sub-permutation of `rest`; every
atom well-kinded for `sig`. -/
structure Out (sig : Sym → Kind) (N : Var → Prop) (rest : List Var) (as : List RAtom) : Prop where
  nodes : ∀ a ∈ as, N a.node
  nodup : (as.map RAtom.node).Nodup
  rest : as.flatMap RAtom.restVars <+~ rest
  wk : ∀ a ∈ as, a.WK sig

theorem Out.nil {sig : Sym → Kind} {N : Var → Prop} {rest : List Var} : Out sig N rest [] :=
  ⟨by simp, by simp, by simp, by simp⟩

theorem Out.mono {sig : Sym → Kind} {N N' : Var → Prop} {rest rest' : List Var} {as : List RAtom}
    (h : Out sig N rest as) (hN : ∀ v, N v → N' v) (hr : rest <+~ rest') : Out sig N' rest' as :=
  ⟨fun a ha => hN _ (h.nodes a ha), h.nodup, h.rest.trans hr, h.wk⟩

theorem Out.append {sig : Sym → Kind} {N₁ N₂ : Var → Prop} {r₁ r₂ : List Var}
    {as₁ as₂ : List RAtom} (h₁ : Out sig N₁ r₁ as₁) (h₂ : Out sig N₂ r₂ as₂)
    (hd : ∀ v, N₁ v → N₂ v → False) :
    Out sig (fun v => N₁ v ∨ N₂ v) (r₁ ++ r₂) (as₁ ++ as₂) where
  nodes a ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact Or.inl (h₁.nodes a ha)
    · exact Or.inr (h₂.nodes a ha)
  nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨h₁.nodup, h₂.nodup, ?_⟩
    intro v hv w hw hvw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hw
    exact hd _ (h₁.nodes a ha) (hvw ▸ h₂.nodes b hb)
  rest := by rw [List.flatMap_append]; exact h₁.rest.append h₂.rest
  wk a ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact h₁.wk a ha
    · exact h₂.wk a ha

theorem Out.single {sig : Sym → Kind} {rest : List Var} (a : RAtom) (hr : a.restVars <+~ rest)
    (hwk : a.WK sig) : Out sig (fun v => v = a.node) rest [a] :=
  ⟨by simp, by simp, by simpa using hr, by simpa using hwk⟩

/-- The specification of `atomsAt P n fresh` for `n < fresh`: the counter
advances, every node is `n` or lies in `[fresh, fr)`, nodes are distinct,
rest variables come from `P.restVars` without repetition, atoms are
well-kinded. -/
def AtSpec (sig : Sym → Kind) (P : Pat) : Prop :=
  PatWK sig P → ∀ (n : Var) (fresh : Nat) (as : List RAtom) (fr : Nat), n < fresh →
    atomsAt P n fresh = (as, fr) →
    fresh ≤ fr ∧ Out sig (fun v => v = n ∨ (fresh ≤ v ∧ v < fr)) P.restVars as

theorem childSpec {sig : Sym → Kind} {p : Pat} (hp : AtSpec sig p) (hwk : PatWK sig p)
    {fresh : Nat} {v : Var} {as : List RAtom} {fr : Nat}
    (h : atomsChild p fresh = (v, as, fr)) :
    fresh ≤ fr ∧ Out sig (fun x => fresh ≤ x ∧ x < fr) p.restVars as := by
  by_cases hhead : p.head.isSome = true
  · rcases hA : atomsAt p fresh (fresh + 1) with ⟨as', fr'⟩
    rw [atomsChild_app p fresh hhead hA] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hle, hout⟩ := hp hwk fresh (fresh + 1) as' fr' (by vomega) hA
    refine ⟨by vomega, hout.mono ?_ (List.Subperm.refl _)⟩
    intro x hx
    rcases hx with rfl | hx <;> constructor <;> vomega
  · cases p with
    | var x =>
        rw [atomsChild_var] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨le_refl _, Out.nil⟩
    | _ => simp [Pat.head] at hhead

theorem childrenSpec {sig : Sym → Kind} (ps : List Pat) (ih : ∀ p ∈ ps, AtSpec sig p)
    (hwk : ∀ p ∈ ps, PatWK sig p) :
    ∀ (fresh : Nat) (vs : List Var) (as : List RAtom) (fr : Nat),
      atomsChildren ps fresh = (vs, as, fr) →
      fresh ≤ fr ∧ vs.length = ps.length ∧
        Out sig (fun x => fresh ≤ x ∧ x < fr) (Pat.restVarsList ps) as := by
  induction ps with
  | nil =>
      intro fresh vs as fr h
      rw [atomsChildren_nil] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨le_refl _, rfl, Out.nil⟩
  | cons p ps ihl =>
      intro fresh vs as fr h
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildren ps fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildren_cons p ps fresh h₁ h₂] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hle₁, hout₁⟩ := childSpec (ih p (by simp)) (hwk p (by simp)) h₁
      obtain ⟨hle₂, hlen, hout₂⟩ :=
        ihl (fun q hq => ih q (by simp [hq])) (fun q hq => hwk q (by simp [hq])) fr₁ vs' as' fr₂ h₂
      refine ⟨by vomega, by simp [hlen], ?_⟩
      rw [restVarsList_cons]
      refine (hout₁.append hout₂ (fun x hx₁ hx₂ => by vomega)).mono ?_ (List.Subperm.refl _)
      intro x hx
      rcases hx with hx | hx <;> constructor <;> vomega

theorem childrenACSpec {sig : Sym → Kind} (es : List (Pat × Mult))
    (ih : ∀ e ∈ es, AtSpec sig e.1) (hwk : ∀ e ∈ es, PatWK sig e.1) :
    ∀ (fresh : Nat) (vs : List (Var × Mult)) (as : List RAtom) (fr : Nat),
      atomsChildrenAC es fresh = (vs, as, fr) →
      fresh ≤ fr ∧ Out sig (fun x => fresh ≤ x ∧ x < fr) (Pat.restVarsElems es) as := by
  induction es with
  | nil =>
      intro fresh vs as fr h
      rw [atomsChildrenAC_nil] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨le_refl _, Out.nil⟩
  | cons e es ihl =>
      intro fresh vs as fr h
      obtain ⟨p, μ⟩ := e
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildrenAC es fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildrenAC_cons p μ es fresh h₁ h₂] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hle₁, hout₁⟩ := childSpec (ih (p, μ) (by simp)) (hwk (p, μ) (by simp)) h₁
      obtain ⟨hle₂, hout₂⟩ :=
        ihl (fun q hq => ih q (by simp [hq])) (fun q hq => hwk q (by simp [hq])) fr₁ vs' as' fr₂ h₂
      refine ⟨by vomega, ?_⟩
      rw [restVarsElems_cons]
      refine (hout₁.append hout₂ (fun x hx₁ hx₂ => by vomega)).mono ?_ (List.Subperm.refl _)
      intro x hx
      rcases hx with hx | hx <;> constructor <;> vomega

/-- Rest variables of the root atoms, by shape. -/
@[simp] theorem restVars_mk_plain (n : Var) (f : Sym) (vs : List Var) :
    RAtom.restVars ⟨n, f, .plain vs⟩ = [] := by
  simp [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars]
@[simp] theorem restVars_mk_comm (n : Var) (f : Sym) (x y : Var) :
    RAtom.restVars ⟨n, f, .comm x y⟩ = [] := by
  simp [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars]
@[simp] theorem restVars_mk_assoc (n : Var) (f : Sym) (pre : Option Var) (vs : List Var)
    (suf : Option Var) : RAtom.restVars ⟨n, f, .assoc pre vs suf⟩ = pre.toList ++ suf.toList := by
  simp [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars]
@[simp] theorem restVars_mk_ac (n : Var) (f : Sym) (vs : List (Var × Mult)) (rest : Option Var) :
    RAtom.restVars ⟨n, f, .ac vs rest⟩ = rest.toList := by
  simp [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars]
@[simp] theorem restVars_mk_aci (n : Var) (f : Sym) (vs : List Var) (rest : Option Var) :
    RAtom.restVars ⟨n, f, .aci vs rest⟩ = rest.toList := by
  simp [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars]

/-- Children atoms followed by the root atom: the root node `n` is below the
fresh range. -/
theorem Out.root {sig : Sym → Kind} {n : Var} {fresh fr : Nat} {rc : List Var} {as : List RAtom}
    (hout : Out sig (fun x => fresh ≤ x ∧ x < fr) rc as) (hn : n < fresh) (a : RAtom)
    (ha : a.node = n) {rest : List Var} (hr : rc ++ a.restVars <+~ rest) (hwk : a.WK sig) :
    Out sig (fun v => v = n ∨ (fresh ≤ v ∧ v < fr)) rest (as ++ [a]) := by
  refine (hout.append (Out.single a (List.Subperm.refl _) hwk) (fun x hx₁ hx₂ => by vomega)).mono
    ?_ hr
  intro x hx
  rcases hx with hx | hx
  · exact Or.inr hx
  · exact Or.inl (hx.trans ha)

theorem atSpec_of_sub {sig : Sym → Kind} (P : Pat)
    (ih : ∀ p, sizeOf p < sizeOf P → AtSpec sig p) : AtSpec sig P := by
  intro hwk n fresh as fr hn h
  cases P with
  | var x =>
      rw [atomsAt_var] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨le_refl _, Out.nil⟩
  | plain f args =>
      cases hwk with
      | plain hf hargs =>
      rcases hC : atomsChildren args fresh with ⟨vs, as', fr'⟩
      rw [atomsAt_plain f args n fresh hC] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle, hlen, hout⟩ :=
        childrenSpec args (fun p hp => ih p (sizeOf_lt_plain hp f)) hargs fresh vs as' _ hC
      refine ⟨hle, hout.root hn ⟨n, f, .plain vs⟩ rfl (by simpa using List.Subperm.refl _) ?_⟩
      simp [RAtom.WK, Shape.kind, hf, hlen]
  | comm f p q =>
      cases hwk with
      | comm hf hp hq =>
      rcases h₁ : atomsChild p fresh with ⟨vp, ap, fr₁⟩
      rcases h₂ : atomsChild q fr₁ with ⟨vq, aq, fr₂⟩
      rw [atomsAt_comm f p q n fresh h₁ h₂] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle₁, hout₁⟩ := childSpec (ih p (sizeOf_lt_comm_left f p q)) hp h₁
      obtain ⟨hle₂, hout₂⟩ := childSpec (ih q (sizeOf_lt_comm_right f p q)) hq h₂
      have hout : Out sig (fun x => fresh ≤ x ∧ x < fr₂) (p.restVars ++ q.restVars) (ap ++ aq) := by
        refine (hout₁.append hout₂ (fun x hx₁ hx₂ => by vomega)).mono ?_ (List.Subperm.refl _)
        intro x hx
        rcases hx with hx | hx <;> constructor <;> vomega
      refine ⟨by vomega, ?_⟩
      rw [restVars_comm]
      exact hout.root hn ⟨n, f, .comm vp vq⟩ rfl (by simpa using List.Subperm.refl _) (by simp [RAtom.WK, Shape.kind, hf])
  | assoc f pre args suf =>
      cases hwk with
      | assoc hf hargs =>
      rcases hC : atomsChildren args fresh with ⟨vs, as', fr'⟩
      rw [atomsAt_assoc f pre args suf n fresh hC] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle, _, hout⟩ :=
        childrenSpec args (fun p hp => ih p (sizeOf_lt_assoc hp f pre suf)) hargs fresh vs as' _ hC
      refine ⟨hle, hout.root hn ⟨n, f, .assoc pre vs suf⟩ rfl ?_ (by simp [RAtom.WK, Shape.kind, hf])⟩
      rw [restVars_assoc, restVars_mk_assoc]
      exact List.perm_append_comm.subperm
  | ac f elems rest =>
      cases hwk with
      | ac hf helems =>
      rcases hC : atomsChildrenAC elems fresh with ⟨vs, as', fr'⟩
      rw [atomsAt_ac f elems rest n fresh hC] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle, hout⟩ :=
        childrenACSpec elems (fun e he => ih e.1 (sizeOf_lt_ac he f rest)) helems fresh vs as' _ hC
      refine ⟨hle, hout.root hn ⟨n, f, .ac vs rest⟩ rfl ?_ (by simp [RAtom.WK, Shape.kind, hf])⟩
      rw [restVars_ac, restVars_mk_ac]
      exact List.perm_append_comm.subperm
  | aci f elems rest =>
      cases hwk with
      | aci hf helems =>
      rcases hC : atomsChildren elems fresh with ⟨vs, as', fr'⟩
      rw [atomsAt_aci f elems rest n fresh hC] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle, _, hout⟩ :=
        childrenSpec elems (fun p hp => ih p (sizeOf_lt_aci hp f rest)) helems fresh vs as' _ hC
      refine ⟨hle, hout.root hn ⟨n, f, .aci vs rest⟩ rfl ?_ (by simp [RAtom.WK, Shape.kind, hf])⟩
      rw [restVars_aci, restVars_mk_aci]
      exact List.perm_append_comm.subperm

theorem atSpec_all {sig : Sym → Kind} : ∀ (k : Nat) (P : Pat), sizeOf P = k → AtSpec sig P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro P hP
      exact atSpec_of_sub P (fun p hp => ih _ (hP ▸ hp) p rfl)

/-- The flattening specification. -/
theorem atomsAt_spec {sig : Sym → Kind} {P : Pat} (hwk : PatWK sig P) {n : Var} {fresh : Nat}
    {as : List RAtom} {fr : Nat} (hn : n < fresh) (h : atomsAt P n fresh = (as, fr)) :
    fresh ≤ fr ∧ Out sig (fun v => v = n ∨ (fresh ≤ v ∧ v < fr)) P.restVars as :=
  atSpec_all _ P rfl hwk n fresh as fr hn h

/-! ## From the specification to `AtomsWF` -/

theorem le_foldr_max (l : List Nat) (r : Nat) : r ≤ l.foldr max r := by
  induction l with
  | nil => exact le_refl _
  | cons x l ih => exact ih.trans (le_max_right _ _)

theorem lt_freshAbove (P : Pat) (r : Var) : r < P.freshAbove r := by
  unfold Pat.freshAbove
  have := le_foldr_max P.vars r
  vomega

theorem Subperm.nodup_of {α : Type*} {l₁ l₂ : List α} (h : l₁ <+~ l₂) (hn : l₂.Nodup) :
    l₁.Nodup := by
  obtain ⟨l, p, s⟩ := h
  exact p.nodup_iff.1 (hn.sublist s)

theorem getElem?_scan {l : List RAtom} {i : Nat} {a : RAtom}
    (h : (l.map QAtom.scan)[i]? = some (.scan a)) : l[i]? = some a := by
  rw [List.getElem?_map] at h
  obtain ⟨b, hb, hba⟩ := Option.map_eq_some_iff.1 h
  cases hba
  exact hb

theorem nodup_getElem?_inj {α : Type*} {l : List α} (h : l.Nodup) {i j : Nat} {x : α}
    (hi : l[i]? = some x) (hj : l[j]? = some x) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hj', hx⟩ := List.getElem?_eq_some_iff.1 hj
  exact ((h.getElem_inj_iff).1 hx).symm

theorem flatMap_nodup_disjoint {α β : Type*} {f : α → List β} : ∀ {l : List α},
    (l.flatMap f).Nodup → ∀ {i j : Nat} {a b : α}, l[i]? = some a → l[j]? = some b → i ≠ j →
    ∀ r ∈ f a, r ∉ f b := by
  intro l
  induction l with
  | nil => intro _ i j a b hi; simp at hi
  | cons x xs ih =>
      intro h i j a b hi hj hij r hr hrb
      rw [List.flatMap_cons, List.nodup_append] at h
      obtain ⟨hx, hxs, hd⟩ := h
      cases i with
      | zero =>
          cases j with
          | zero => exact hij rfl
          | succ j =>
              simp at hi; subst hi
              simp at hj
              exact hd r hr r (List.mem_flatMap.2 ⟨b, List.mem_of_getElem? hj, hrb⟩) rfl
      | succ i =>
          cases j with
          | zero =>
              simp at hj; subst hj
              simp at hi
              exact hd r hrb r (List.mem_flatMap.2 ⟨a, List.mem_of_getElem? hi, hr⟩) rfl
          | succ j =>
              simp at hi hj
              exact ih hxs hi hj (fun h => hij (by rw [h])) r hr hrb

theorem sublist_flatMap_of_mem' {α β : Type*} {f : α → List β} {a : α} : ∀ {l : List α},
    a ∈ l → f a <+ l.flatMap f := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x xs ih =>
      intro h
      rw [List.flatMap_cons]
      rcases List.mem_cons.1 h with rfl | h
      · exact List.sublist_append_left _ _
      · exact (ih h).trans (List.sublist_append_right _ _)

end AtomsWFProof

set_option linter.unusedVariables false in
open AtomsWFProof in
/-- The flattened atoms of a well-kinded pattern with duplicate-free rest
variables are a well-formed atom list. `hr` and `hP` are not needed: nested
node variables are drawn from `P.freshAbove r > r` whatever `r` is, and a
variable root simply has no atom. -/
theorem atoms_atomsWF (G : Graph) (sig : Sym → Kind) (P : Pat) (r : Var)
    (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : PatWK sig P)
    (hnd : P.restVars.Nodup) (hr : r ∉ P.vars) (hP : P.head.isSome = true) :
    AtomsWF G sig ((atoms P r).map QAtom.scan) := by
  rcases hA : atomsAt P r (P.freshAbove r) with ⟨as, fr⟩
  have hatoms : atoms P r = as := by simp [atoms, hA]
  rw [hatoms]
  obtain ⟨_, hout⟩ := atomsAt_spec hwk (lt_freshAbove P r) hA
  have hrest : (as.flatMap RAtom.restVars).Nodup := Subperm.nodup_of hout.rest hnd
  have hmem : ∀ a, QAtom.scan a ∈ as.map QAtom.scan → a ∈ as := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := List.mem_map.1 ha
    cases hba
    exact hb
  refine ⟨hk, hconf, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact hout.wk a (hmem a ha)
  · intro i j a b hi hj hab
    have hi' := getElem?_scan hi
    have hj' := getElem?_scan hj
    refine nodup_getElem?_inj hout.nodup (x := a.node) ?_ ?_
    · rw [List.getElem?_map, hi']; rfl
    · rw [List.getElem?_map, hj', hab]; rfl
  · intro i j a b hi hj hij
    exact flatMap_nodup_disjoint hrest (getElem?_scan hi) (getElem?_scan hj) hij
  · intro a ha
    have hsub₁ : List.Sublist a.seqRestVars a.restVars :=
      (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
    have hsub : List.Sublist a.seqRestVars (as.flatMap RAtom.restVars) :=
      hsub₁.trans (sublist_flatMap_of_mem' (f := RAtom.restVars) (hmem a ha))
    exact hrest.sublist hsub
  · intro i x y h
    rw [List.getElem?_map] at h
    obtain ⟨b, _, hb⟩ := Option.map_eq_some_iff.1 h
    cases hb

end Semper.EMatch
