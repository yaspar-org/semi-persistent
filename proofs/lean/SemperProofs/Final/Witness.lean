import SemperProofs.Final.Store
import SemperProofs.Final.Closed
import SemperProofs.CC.AtomsWitness

/-!
# A run that meets every hypothesis of the final theorem

The program, over the AC operator `+` with leaf constants `a, b, c, d` and
a plain binary operator `g`:

```
(union (+ a b) c)
(let t (+ a b d))
(let u (+ c d))
(rewrite (+ x y) (g x y))
(rewrite (+ x y z) k)
```

The completion state is the one of `CC/AtomsWitness.lean` (`wst`, with the
asserted equation `a + b = c` and the stored `+`-nodes `{a, b}` in `c`'s
class and `{a, b, d}`, `{c, d}` in class 4, the first retired by the
reducibility pass), for which `witness_complete` proves `CompleteAtoms`.
The e-graph stores the four leaf constants, the three `+`-nodes (the
retired `{a, b, d}` stays in the graph and matchable: `FLAG_AC_COLLAPSED`
removes it from completion only), and, after round 0, the four `g`-nodes
the first rewrite builds, `g(a, b)`, `g(b, a)` in `c`'s class and
`g(c, d)`, `g(d, c)` in class 4, and the constant `k` the second rewrite
builds, in class 4. The first rewrite matches `{a, b}` and `{c, d}` in
both orders, and `{a, b, d}` not at all (the pattern has two elements and
no rest); the second matches `{a, b, d}` only, in six orders, and reads
the retired node as its root.

Symbols: `+ = 0`, `g = 1`, `a, b, c, d = 2, 3, 4, 5`, `k = 6`. Classes:
`a, b, c, d` are `0, 1, 2, 3`, the class of `t` and `u` is `4`. Node ids:
the leaf constants are `0` to `3`, the `+`-nodes `10, 11, 12`, the
`g`-nodes `20` to `23`, the `k`-node `30`.

Round 0 matches on the initial store and builds the `g`-nodes; round 1
matches on the result, builds nothing new and is the fixpoint. Both rounds
emit every naive match. `witness_saturation_modulo_complete` instantiates
`saturation_modulo_complete_store_atoms` with this run: every hypothesis is
proved, none assumed. The rewrite's right-hand side is a `g`-node, which
the former final theorem (`represents` as the whole graph, literal `Den`)
could not hold. `witness_fires_modulo` reads the conclusion at the match
`x ↦ c, y ↦ d` rooted at `{c, d}`. The active `+`-nodes `act` are `{a, b}`
and `{c, d}`; the retired `{a, b, d}` is not among them, so the theorem
says nothing about a match rooted at it, and the covering form
`saturation_modulo_complete_store_cover` does not apply to this store: its
`FCover` requires every `+`-node of the index to be active, and the
collapsed node is not. `witness_saturation_modulo_complete_retired` is
`saturation_modulo_complete_store_retired_atoms` on the same run, with the
retired node in `ret`, `SubRepR` and `FCover` over `act ∪ ret` proved
(`hyp_subR`, `hyp_coverR`), `I2` and `I3` on the completion view
(`witness_I2`, `witness_I3`), and `witness_fires_retired` reads it at the
match `x ↦ a, y ↦ b, z ↦ d` of the second rewrite rooted at `{a, b, d}`:
the instance is fired, the root binds the class of the active `{c, d}`,
`=_E`-equal to `{a, b, d}` under `a + b = c`.
-/

namespace SemperProofs.Final.Witness

open Semper.EMatch Semper.EMatch.Fidelity SemperProofs.CC SemperProofs.CC.Bridge
  SemperProofs.CC.AtomsWitness

/-! ## The e-graph -/

/-- The kinds: `+` is AC, `g` plain binary, the constants (`a` to `d` and
`k`) plain nullary. -/
def sig : Sym → Kind := fun s => if s = 0 then .ac else if s = 1 then .plain 2 else .plain 0

/-- The stored `+`-nodes of `wst`; `p₂` is retired. -/
def p₁ : Monomial 5 × Fin 5 := ({0, 1}, 2)
def p₂ : Monomial 5 × Fin 5 := ({0, 1, 3}, 4)
def p₃ : Monomial 5 × Fin 5 := ({2, 3}, 4)

/-- The active `+`-nodes. -/
def act : Finset (Monomial 5 × Fin 5) := {p₁, p₃}

/-- The retired `+`-node. -/
def ret : Finset (Monomial 5 × Fin 5) := {p₂}

/-- The ids of the `+`-nodes. -/
def ι (p : Monomial 5 × Fin 5) : NodeId := if p = p₁ then 10 else if p = p₂ then 11 else 12

/-- The leaf constants and the three `+`-nodes. -/
def nodes₀ : List (NodeId × Node) :=
  [(0, ⟨2, .tuple []⟩), (1, ⟨3, .tuple []⟩), (2, ⟨4, .tuple []⟩), (3, ⟨5, .tuple []⟩),
   (10, ⟨0, .mset {0, 1}⟩), (11, ⟨0, .mset {0, 1, 3}⟩), (12, ⟨0, .mset {2, 3}⟩)]

/-- The `g`-nodes the first rewrite builds. -/
def gNodes : List (NodeId × Node) :=
  [(20, ⟨1, .tuple [0, 1]⟩), (21, ⟨1, .tuple [1, 0]⟩), (22, ⟨1, .tuple [2, 3]⟩),
   (23, ⟨1, .tuple [3, 2]⟩)]

/-- The constant `k` the second rewrite builds. -/
def kNodes : List (NodeId × Node) := [(30, ⟨6, .tuple []⟩)]

def nodes₁ : List (NodeId × Node) := nodes₀ ++ (gNodes ++ kNodes)

/-- The union-find: a class is named by its representative `0` to `4`. -/
def wfind (id : NodeId) : C :=
  if id = 10 ∨ id = 20 ∨ id = 21 then 2
  else if id = 11 ∨ id = 12 ∨ id = 22 ∨ id = 23 ∨ id = 30 then 4
  else id

theorem wfind_cases (id : NodeId) : wfind id = 2 ∨ wfind id = 4 ∨ wfind id = id := by
  unfold wfind; split_ifs <;> simp

theorem wfind_idem (id : NodeId) : wfind (wfind id) = wfind id := by
  rcases wfind_cases id with h | h | h <;> rw [h]
  · rfl
  · rfl
  · exact h

/-- No node is skipped: nothing subsumed, no shield, every class matchable. -/
def noSkip : SkipFlags := ⟨fun _ => false, false, fun _ => false, fun _ => true⟩

def S₀ : Store := ⟨nodes₀, wfind, noSkip⟩
def S₁ : Store := ⟨nodes₁, wfind, noSkip⟩

def G₀ : Graph := ⟨nodes₀, wfind⟩
def G₁ : Graph := ⟨nodes₁, wfind⟩

theorem index_noSkip (S : Store) (h : S.flags = noSkip) : S.index = S.graph := by
  have : S.nodes.filter (fun p => !S.skip p.1) = S.nodes :=
    List.filter_eq_self.2 (fun p _ => by simp [Store.skip, h, noSkip])
  simp only [Store.index, Store.graph, this]

@[simp] theorem S₀_index : S₀.index = G₀ := index_noSkip S₀ rfl
@[simp] theorem S₁_index : S₁.index = G₁ := index_noSkip S₁ rfl
@[simp] theorem S₁_graph : S₁.graph = G₁ := rfl

theorem keys₀ : G₀.KeysNodup := by
  show (nodes₀.map (·.1)).Nodup; decide
theorem keys₁ : G₁.KeysNodup := by
  show (nodes₁.map (·.1)).Nodup; decide

theorem conf₀ : G₀.Conforms sig := by
  show ∀ p ∈ nodes₀, p.2.children.kind = sig p.2.op; decide
theorem conf₁ : G₁.Conforms sig := by
  show ∀ p ∈ nodes₁, p.2.children.kind = sig p.2.op; decide

theorem canon₁ : G₁.ChildrenCanon := by
  intro p hp
  simp only [G₁, nodes₁, nodes₀, gNodes, kNodes, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Children.Canon, G₁, wfind]

/-- Distinct contents. -/
theorem contents₁ : (nodes₁.map (·.2)).Nodup := by decide

theorem dedup₁ : ∀ id₁ id₂ n, (id₁, n) ∈ G₁.nodes → (id₂, n) ∈ G₁.nodes →
    G₁.find id₁ = G₁.find id₂ := by
  intro id₁ id₂ n h₁ h₂
  have := List.inj_on_of_nodup_map contents₁ h₁ h₂ rfl
  rw [(Prod.mk.inj this).1]

/-! ## The rewrite `(rewrite (+ x y) (g x y))` -/

/-- The left-hand side `(+ x y)`, `x = 0`, `y = 1`. -/
def pat : Pat := .ac 0 [(.var 0, .exact 1), (.var 1, .exact 1)] none

/-- The right-hand side `(g x y)`. -/
def rhs : Pat := .plain 1 [.var 0, .var 1]

/-- The one atom of the left-hand side, at the root node variable `2`. -/
def atom : RAtom := ⟨2, 0, .ac [(0, .exact 1), (1, .exact 1)] none⟩

theorem atoms_pat : atoms pat 2 = [atom] := by
  simp [pat, atom, atoms, atomsAt, atomsChildrenAC, atomsChild, Pat.freshAbove]

/-- The scheduler's plan for the atom. -/
def plan : APlan := (lower atom ∅).map (0, ·) ++ []

/-- The rewrite: its atom, the static matcher of the scheduler's plan, and
the action `union (var root) rhs` (`apply.rs:377-384`). -/
def rule : Rule where
  atoms := [.scan atom]
  matcher := .static plan
  actions := [.union (.var 2) rhs]

/-! ## The rewrite `(rewrite (+ x y z) k)` -/

/-- The left-hand side `(+ x y z)`, `x = 0`, `y = 1`, `z = 2`. -/
def pat₂ : Pat := .ac 0 [(.var 0, .exact 1), (.var 1, .exact 1), (.var 2, .exact 1)] none

/-- The right-hand side `k`. -/
def rhs₂ : Pat := .plain 6 []

/-- The one atom of the left-hand side, at the root node variable `3`. -/
def atom₂ : RAtom := ⟨3, 0, .ac [(0, .exact 1), (1, .exact 1), (2, .exact 1)] none⟩

theorem atoms_pat₂ : atoms pat₂ 3 = [atom₂] := by
  simp [pat₂, atom₂, atoms, atomsAt, atomsChildrenAC, atomsChild, Pat.freshAbove]

/-- The scheduler's plan for the atom. -/
def plan₂ : APlan := (lower atom₂ ∅).map (0, ·) ++ []

/-- The second rewrite: its atom, the static matcher of the scheduler's
plan, and the action `union (var root) k`. -/
def rule₂ : Rule where
  atoms := [.scan atom₂]
  matcher := .static plan₂
  actions := [.union (.var 3) rhs₂]

def rules : List Rule := [rule, rule₂]

theorem mem_rules {r : Rule} (hr : r ∈ rules) : r = rule ∨ r = rule₂ := by
  simpa [rules] using hr

theorem rule_atoms : rule.atoms = (atoms pat 2).map QAtom.scan := by rw [atoms_pat]; rfl

theorem rule₂_atoms : rule₂.atoms = (atoms pat₂ 3).map QAtom.scan := by rw [atoms_pat₂]; rfl

theorem plan_schedA : SchedA rule.atoms ∅ ∅ plan := by
  refine SchedA.pick (i := 0) rfl (by simp) (SchedA.done ?_ ?_)
  · intro i a hi
    match i, hi with
    | 0, _ => simp
  · intro i q hi hu
    match i, hi with
    | 0, _ => simp at hu

theorem atomsWF {G : Graph} (hk : G.KeysNodup) (hc : G.Conforms sig) :
    AtomsWF G sig rule.atoms where
  keys := hk
  conf := hc
  wk := by
    intro a ha
    simp only [rule, List.mem_singleton, QAtom.scan.injEq] at ha
    subst ha; rfl
  nodesDistinct := by
    intro i j a b hi hj _
    match i, hi, j, hj with
    | 0, _, 0, _ => rfl
  restLinear := by
    intro i j a b hi hj hij
    match i, hi, j, hj with
    | 0, _, 0, _ => exact absurd rfl hij
  seqNodup := by
    intro a ha
    simp only [rule, List.mem_singleton, QAtom.scan.injEq] at ha
    subst ha; simp [RAtom.seqRestVars, atom]
  bindable := by
    intro i x y hi
    match i, hi with
    | 0, hi => simp [rule] at hi

theorem plan₂_schedA : SchedA rule₂.atoms ∅ ∅ plan₂ := by
  refine SchedA.pick (i := 0) rfl (by simp) (SchedA.done ?_ ?_)
  · intro i a hi
    match i, hi with
    | 0, _ => simp
  · intro i q hi hu
    match i, hi with
    | 0, _ => simp at hu

theorem atomsWF₂ {G : Graph} (hk : G.KeysNodup) (hc : G.Conforms sig) :
    AtomsWF G sig rule₂.atoms where
  keys := hk
  conf := hc
  wk := by
    intro a ha
    simp only [rule₂, List.mem_singleton, QAtom.scan.injEq] at ha
    subst ha; rfl
  nodesDistinct := by
    intro i j a b hi hj _
    match i, hi, j, hj with
    | 0, _, 0, _ => rfl
  restLinear := by
    intro i j a b hi hj hij
    match i, hi, j, hj with
    | 0, _, 0, _ => exact absurd rfl hij
  seqNodup := by
    intro a ha
    simp only [rule₂, List.mem_singleton, QAtom.scan.injEq] at ha
    subst ha; simp [RAtom.seqRestVars, atom₂]
  bindable := by
    intro i x y hi
    match i, hi with
    | 0, hi => simp [rule₂] at hi

theorem rulesWF₀ : RulesWF sig G₀ rules := by
  intro r hr
  rcases mem_rules hr with rfl | rfl
  · exact atomsWF keys₀ conf₀
  · exact atomsWF₂ keys₀ conf₀

theorem rulesWF₁ : RulesWF sig G₁ rules := by
  intro r hr
  rcases mem_rules hr with rfl | rfl
  · exact atomsWF keys₁ conf₁
  · exact atomsWF₂ keys₁ conf₁

/-! ## The matches -/

/-- The `+`-nodes of the e-graph. -/
def plusNodes : List (NodeId × Node) :=
  [(10, ⟨0, .mset {0, 1}⟩), (11, ⟨0, .mset {0, 1, 3}⟩), (12, ⟨0, .mset {2, 3}⟩)]

theorem plus_of_mem₁ {id : NodeId} {nd : Node} (h : (id, nd) ∈ nodes₁) (hop : nd.op = 0) :
    (id, nd) ∈ plusNodes := by
  simp only [nodes₁, nodes₀, gNodes, kNodes, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp_all [plusNodes]

theorem plus_of_mem₀ {id : NodeId} {nd : Node} (h : (id, nd) ∈ nodes₀) (hop : nd.op = 0) :
    (id, nd) ∈ plusNodes :=
  plus_of_mem₁ (List.mem_append_left _ h) hop

/-- Every match of the first rewrite: the root is `{a, b}` or `{c, d}`, the
elements in either order. -/
theorem match_cases {nodes : List (NodeId × Node)}
    (hplus : ∀ id nd, (id, nd) ∈ nodes → nd.op = 0 → (id, nd) ∈ plusNodes) {σ : Binding}
    (hm : Matches ⟨nodes, wfind⟩ rule.atoms σ) :
    (σ.node 2 = some 10 ∧ σ.cls 2 = some 2 ∧
      ((σ.cls 0 = some 0 ∧ σ.cls 1 = some 1) ∨ (σ.cls 0 = some 1 ∧ σ.cls 1 = some 0))) ∨
    (σ.node 2 = some 12 ∧ σ.cls 2 = some 4 ∧
      ((σ.cls 0 = some 2 ∧ σ.cls 1 = some 3) ∨ (σ.cls 0 = some 3 ∧ σ.cls 1 = some 2))) := by
  obtain ⟨id, nd, hid, hmem, hcls, hop, hmn⟩ := hm.sat (.scan atom) (by simp [rule])
  have hp := hplus id nd hmem hop
  obtain ⟨m, taken, rfl, hnd, hlen, hin, hcl, -, hrest⟩ := matchN_ac_vars.1 hmn
  match taken, hnd, hlen, hin, hcl, hrest with
  | [t₀, t₁], hnd, _, hin, hcl, hrest =>
    have h0 : σ.cls 0 = some t₀ := hcl ((0, .exact 1), t₀) (by simp)
    have h1 : σ.cls 1 = some t₁ := hcl ((1, .exact 1), t₁) (by simp)
    have hne : t₀ ≠ t₁ := by simpa using hnd
    simp only [MsetRestOk, List.mem_cons, List.not_mem_nil, or_false] at hrest
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
    simp only [plusNodes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      Node.mk.injEq, Children.mset.injEq] at hp
    rcases hp with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hin hrest
      refine Or.inl ⟨hid, by simpa [wfind, atom] using hcls, ?_⟩
      rcases hin with ⟨h₀ | h₀, h₁ | h₁⟩ <;> subst h₀ <;> subst h₁
      · exact absurd rfl hne
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact absurd rfl hne
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hrest
      have ha : 0 = t₀ ∨ 0 = t₁ := hrest 0 (by simp)
      have hb : 1 = t₀ ∨ 1 = t₁ := hrest 1 (by simp)
      have hd : 3 = t₀ ∨ 3 = t₁ := hrest 3 (by simp)
      exfalso
      rcases ha with h | h <;> rcases hb with h' | h' <;> rcases hd with h'' | h'' <;>
        first
          | exact absurd (h.trans h'.symm) (by decide)
          | exact absurd (h.trans h''.symm) (by decide)
          | exact absurd (h'.trans h''.symm) (by decide)
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hin hrest
      refine Or.inr ⟨hid, by simpa [wfind, atom] using hcls, ?_⟩
      rcases hin with ⟨h₀ | h₀, h₁ | h₁⟩ <;> subst h₀ <;> subst h₁
      · exact absurd rfl hne
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact absurd rfl hne

/-- Every match of the second rewrite is rooted at the retired `{a, b, d}`:
the pattern takes three distinct elements, which no two-element node
holds. -/
theorem match_cases₂ {nodes : List (NodeId × Node)}
    (hplus : ∀ id nd, (id, nd) ∈ nodes → nd.op = 0 → (id, nd) ∈ plusNodes) {σ : Binding}
    (hm : Matches ⟨nodes, wfind⟩ rule₂.atoms σ) :
    σ.node 3 = some 11 ∧ σ.cls 3 = some 4 := by
  obtain ⟨id, nd, hid, hmem, hcls, hop, hmn⟩ := hm.sat (.scan atom₂) (by simp [rule₂])
  have hp := hplus id nd hmem hop
  obtain ⟨m, taken, rfl, hnd, hlen, hin, -, -, -⟩ := matchN_ac_vars.1 hmn
  match taken, hnd, hlen, hin with
  | [t₀, t₁, t₂], hnd, _, hin =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
    simp only [plusNodes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      Node.mk.injEq, Children.mset.injEq] at hp
    rcases hp with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
    · exfalso
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hin
      obtain ⟨h₀, h₁, h₂⟩ := hin
      rcases h₀ with rfl | rfl <;> rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
        exact absurd hnd (by decide)
    · exact ⟨hid, by simpa [wfind, atom₂] using hcls⟩
    · exfalso
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hin
      obtain ⟨h₀, h₁, h₂⟩ := hin
      rcases h₀ with rfl | rfl <;> rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
        exact absurd hnd (by decide)

/-! ## The consequences: the `g`-nodes and `k` -/

/-- No unit, no nilpotent count, no inverse. -/
def ops : Sym → OpLaws := fun _ => ⟨none, none, none⟩

theorem matchersOK : MatchersOK rules := by
  intro r hr
  rcases mem_rules hr with rfl | rfl
  · exact matcherOK_static plan_schedA
  · exact matcherOK_static plan₂_schedA

theorem rule_matcher_ok : MatcherOK rule.atoms rule.matcher := matchersOK rule (by simp [rules])

/-- `(g x y)` is built: the `g`-node over the two classes. -/
theorem den_rhs {σ : Binding} {t₀ t₁ : C} (h0 : σ.cls 0 = some t₀) (h1 : σ.cls 1 = some t₁)
    (hc0 : wfind t₀ = t₀) (hc1 : wfind t₁ = t₁) {gid : NodeId}
    (hmem : (gid, ⟨1, .tuple [t₀, t₁]⟩) ∈ nodes₁) : DenN G₁ ops σ rhs (wfind gid) := by
  have hmem' : (gid, (⟨1, .tuple [G₁.find t₀, G₁.find t₁]⟩ : Node)) ∈ G₁.nodes := by
    show (gid, (⟨1, .tuple [wfind t₀, wfind t₁]⟩ : Node)) ∈ nodes₁
    rw [hc0, hc1]; exact hmem
  refine DenN.plain (cs := [G₁.find t₀, G₁.find t₁]) rfl ?_ hmem'
  intro pc hpc
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hpc
  rcases hpc with rfl | rfl
  · exact DenN.var h0
  · exact DenN.var h1

/-- `k` is built: the `k`-node, in class 4. -/
theorem den_k {σ : Binding} : DenN G₁ ops σ rhs₂ (wfind 30) :=
  DenN.plain (f := 6) (args := []) (cs := []) (id := 30) rfl (fun _ h => by simp at h)
    (by simp [G₁, nodes₁, kNodes])

/-- The root's value. -/
theorem den_root {σ : Binding} {v : Var} {c : C} (h : σ.cls v = some c) (hc : wfind c = c) :
    DenN G₁ ops σ (.var v) c := by
  have := DenN.var (G := G₁) (L := ops) h
  rwa [show G₁.find c = c from hc] at this

/-- Every match of the first rewrite on either snapshot has its right-hand
side built in the class of its root, after round 0. -/
theorem unions_ok {nodes : List (NodeId × Node)}
    (hplus : ∀ id nd, (id, nd) ∈ nodes → nd.op = 0 → (id, nd) ∈ plusNodes)
    {σ : Binding} (hm : Matches ⟨nodes, wfind⟩ rule.atoms σ) :
    ∃ c₁ c₂, DenN G₁ ops σ (.var 2) c₁ ∧ DenN G₁ ops σ rhs c₂ ∧
      (c₁, c₂) ∈ [((2 : C), (2 : C)), (4, 4)] := by
  rcases match_cases hplus hm with ⟨-, hr, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩ | ⟨-, hr, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩
  · exact ⟨2, wfind 20, den_root hr rfl, den_rhs h0 h1 rfl rfl (by simp [nodes₁, gNodes]),
      by simp [wfind]⟩
  · exact ⟨2, wfind 21, den_root hr rfl, den_rhs h0 h1 rfl rfl (by simp [nodes₁, gNodes]),
      by simp [wfind]⟩
  · exact ⟨4, wfind 22, den_root hr rfl, den_rhs h0 h1 rfl rfl (by simp [nodes₁, gNodes]),
      by simp [wfind]⟩
  · exact ⟨4, wfind 23, den_root hr rfl, den_rhs h0 h1 rfl rfl (by simp [nodes₁, gNodes]),
      by simp [wfind]⟩

/-- Every match of the second rewrite has `k` in the class of its root,
after round 0. -/
theorem unions_ok₂ {nodes : List (NodeId × Node)}
    (hplus : ∀ id nd, (id, nd) ∈ nodes → nd.op = 0 → (id, nd) ∈ plusNodes)
    {σ : Binding} (hm : Matches ⟨nodes, wfind⟩ rule₂.atoms σ) :
    ∃ c₁ c₂, DenN G₁ ops σ (.var 3) c₁ ∧ DenN G₁ ops σ rhs₂ c₂ ∧
      (c₁, c₂) ∈ [((2 : C), (2 : C)), (4, 4)] := by
  obtain ⟨-, hr⟩ := match_cases₂ hplus hm
  exact ⟨4, wfind 30, den_root hr rfl, den_k, by simp [wfind]⟩

/-! ## The rounds -/

/-- Every id of the final store. -/
def ids₁ : Finset NodeId := (nodes₁.map Prod.fst).toFinset

theorem mem_ids₁ {id : NodeId} {nd : Node} (h : (id, nd) ∈ nodes₁) : id ∈ ids₁ :=
  List.mem_toFinset.2 (List.mem_map.2 ⟨_, h, rfl⟩)

/-- The matcher's round from the store `Sb` to `S₁`: every id of `S₁` is
logged, the unions are recorded with their after classes, nothing is
subsumed, tracking is on. -/
def mkRound (Sb : Store) : Round where
  before := Sb.index
  after := S₁.index
  added := ids₁
  unions := [(2, 2), (4, 4)]
  subsumed := ∅
  touched := ids₁
  mergeDelta := ids₁
  tracking := true

theorem mkRound_wf (Sb : Store) (hb : Sb.index.find = wfind) : (mkRound Sb).WF where
  created_added := by
    rintro id ⟨⟨n', hn'⟩, -⟩
    simp only [mkRound, S₁_index] at hn'
    exact mem_ids₁ hn'
  added_touched := fun _ h => h
  recanon_touched := by
    rintro id ⟨n, n', -, hn', -⟩
    simp only [mkRound, S₁_index] at hn'
    exact mem_ids₁ hn'
  subsumed_touched := by simp [mkRound]
  absorbed_delta := by
    rintro - id ⟨n', hn'⟩ -
    simp only [mkRound, S₁_index] at hn'
    exact mem_ids₁ hn'
  no_split := by
    intro id id' h
    simp only [mkRound, S₁_index] at h ⊢
    rw [hb] at h
    exact h
  children_canon := by simp only [mkRound, S₁_index]; exact canon₁
  find_idem := by simp only [mkRound, S₁_index]; exact wfind_idem
  dedup := by simp only [mkRound, S₁_index]; exact dedup₁

/-- The store persists: every node of `Sb` is a node of `S₁`, with its
children (they are canonical), and `find` does not move. -/
theorem persist (Sb : Store) (hb : Sb.find = wfind) (hsub : ∀ p ∈ Sb.nodes, p ∈ nodes₁) :
    StorePersist Sb S₁ where
  before_idem := by intro id; show Sb.find (Sb.find id) = Sb.find id; rw [hb]; exact wfind_idem id
  after_idem := wfind_idem
  no_split := by intro id id' h; rw [hb] at h; exact h
  children_canon := canon₁
  dedup := dedup₁
  persist := by
    intro id n hn
    refine ⟨n, hsub _ hn, rfl, ?_⟩
    have hc := canon₁ _ (hsub _ hn)
    obtain ⟨op, ch⟩ := n
    cases ch with
    | tuple cs =>
        show cs = cs.map wfind
        have hc' : ∀ c ∈ cs, wfind c = _root_.id c := hc
        rw [List.map_congr_left hc', List.map_id]
    | spair a b => exact Or.inl ⟨hc.1.symm, hc.2.symm⟩
    | seq cs =>
        show cs = cs.map wfind
        have hc' : ∀ c ∈ cs, wfind c = _root_.id c := hc
        rw [List.map_congr_left hc', List.map_id]
    | mset m =>
        show m = m.map wfind
        have hc' : ∀ c ∈ m, wfind c = _root_.id c := hc
        rw [Multiset.map_congr rfl hc', Multiset.map_id]
    | set s =>
        show s = s.image wfind
        have hc' : Set.EqOn wfind _root_.id s := fun x hx => hc x hx
        rw [Finset.image_congr hc', Finset.image_id]

/-- One round on stores applying every naive match of both rewrites. -/
def mkActRound (Sb : Store) {nodes : List (NodeId × Node)}
    (hidx : Sb.index = ⟨nodes, wfind⟩)
    (hplus : ∀ id nd, (id, nd) ∈ nodes → nd.op = 0 → (id, nd) ∈ plusNodes)
    (hwf : RulesWF sig Sb.index rules) : SActRoundN ops where
  R := mkRound Sb
  Sb := Sb
  Sa := S₁
  before_eq := rfl
  after_eq := rfl
  emitted := fun r σ => r ∈ rules ∧ σ ∈ r.matcher.naive Sb.index
  inserts := by
    rintro r σ ⟨hr, -⟩ t ht
    rcases mem_rules hr with rfl | rfl <;> simp [rule, rule₂] at ht
  unions := by
    rintro r σ ⟨hr, hσ⟩ a b hab
    have hm := (MatcherOK.naive_iff (matchersOK r hr) (hwf r hr) σ).1 hσ
    rw [hidx] at hm
    rcases mem_rules hr with rfl | rfl
    · simp only [rule, List.mem_singleton, Action.union.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      exact unions_ok hplus hm
    · simp only [rule₂, List.mem_singleton, Action.union.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      exact unions_ok₂ hplus hm
  subsumes := by
    rintro r σ ⟨hr, -⟩ x hx
    rcases mem_rules hr with rfl | rfl <;> simp [rule, rule₂] at hx
  unions_merged := by
    intro u hu
    simp only [mkRound, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> rfl

/-- Round 0: from the initial store to the store with the `g`-nodes. -/
def A₀ : SActRoundN ops :=
  mkActRound S₀ S₀_index (fun _ _ h hop => plus_of_mem₀ h hop) (by rw [S₀_index]; exact rulesWF₀)

/-- Round 1: on the store with the `g`-nodes; it builds nothing new. -/
def A₁ : SActRoundN ops :=
  mkActRound S₁ S₁_index (fun _ _ h hop => plus_of_mem₁ h hop) (by rw [S₁_index]; exact rulesWF₁)

/-- Both rules are routed to the naive matcher. -/
def naive : Rule → Bool := fun _ => true

/-! ## Every hypothesis -/

theorem hyp_h₀ : RulesWF sig A₀.R.before rules := by
  show RulesWF sig S₀.index rules
  rw [S₀_index]; exact rulesWF₀

theorem hyp_ok : ∀ A ∈ [A₀, A₁], RoundOKN sig rules A := by
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl
  · exact ⟨mkRound_wf S₀ (by rw [S₀_index]; rfl), rfl,
      (persist S₀ rfl (fun p hp => List.mem_append_left _ hp)).toN ops,
      by show RulesWF sig S₁.index rules; rw [S₁_index]; exact rulesWF₁⟩
  · exact ⟨mkRound_wf S₁ (by rw [S₁_index]; rfl), rfl, (persist S₁ rfl (fun p hp => hp)).toN ops,
      by show RulesWF sig S₁.index rules; rw [S₁_index]; exact rulesWF₁⟩

theorem hyp_emit₀ : EmitsAllN A₀ rules := fun _ hr _ hσ => ⟨hr, hσ⟩

theorem hyp_chain : SChainN naive rules A₀ [A₁] := by
  refine ⟨rfl, ⟨true, fun _ => rfl, ?_⟩, trivial⟩
  intro r hr
  refine ⟨fun _ σ hσ => ⟨hr, hσ⟩, fun h => absurd h (by simp [route, naive])⟩

theorem hyp_fix : A₁.Unchanged := ⟨fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl⟩

theorem mem_act {p : Monomial 5 × Fin 5} (hp : p ∈ act) : p = p₁ ∨ p = p₃ := by
  simpa [act] using hp

theorem mem_ret {p : Monomial 5 × Fin 5} (hp : p ∈ ret) : p = p₂ := by
  simpa [ret] using hp

/-- The retired node is a stored node. -/
theorem hyp_ret : Stored wst ret := by
  intro p hp
  rw [mem_ret hp]
  exact Or.inr (Or.inl rfl)

theorem hyp_within : Within wst act := by
  intro p hp
  rcases mem_act hp with rfl | rfl
  · exact stored_active (Or.inl ⟨rfl, rfl⟩)
  · exact stored_active (Or.inr ⟨rfl, rfl⟩)

theorem ι₁ : ι p₁ = 10 := by simp [ι]
theorem ι₂ : ι p₂ = 11 := by simp [ι, show p₂ ≠ p₁ by decide]
theorem ι₃ : ι p₃ = 12 := by simp [ι, show p₃ ≠ p₁ by decide, show p₃ ≠ p₂ by decide]

theorem mkNode₁ : mkNode wst 0 p₁ = ⟨0, .mset {0, 1}⟩ := by simp [mkNode, wst, clsId, p₁]
theorem mkNode₂ : mkNode wst 0 p₂ = ⟨0, .mset {0, 1, 3}⟩ := by simp [mkNode, wst, clsId, p₂]
theorem mkNode₃ : mkNode wst 0 p₃ = ⟨0, .mset {2, 3}⟩ := by simp [mkNode, wst, clsId, p₃]

/-- The `+`-part of the final index is the graph of `+` read from `wst`. -/
theorem hyp_sub : SubRep A₁.Sa.index wst 0 act ι := by
  show SubRep S₁.index wst 0 act ι
  rw [S₁_index]
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases mem_act hp with rfl | rfl
    · rw [ι₁, mkNode₁]; simp [G₁, nodes₁, nodes₀]
    · rw [ι₃, mkNode₃]; simp [G₁, nodes₁, nodes₀]
  · intro p hp
    rcases mem_act hp with rfl | rfl
    · rw [ι₁]; rfl
    · rw [ι₃]; rfl

/-- The `+`-part of the final index, retired node included, is the graph of
`+` read from `wst`. -/
theorem hyp_subR : SubRepR A₁.Sa.index wst 0 act ret ι := by
  refine ⟨hyp_sub, ?_, ?_⟩
  · intro p hp
    rw [mem_ret hp, ι₂, mkNode₂]
    show _ ∈ S₁.index.nodes
    rw [S₁_index]; simp [G₁, nodes₁, nodes₀]
  · intro p hp
    rw [mem_ret hp, ι₂]; rfl

/-- Every `+`-node of the final index is an active or the retired node. -/
theorem hyp_coverR : FCover A₁.Sa.index 0 (act ∪ ret) ι := by
  show FCover S₁.index 0 (act ∪ ret) ι
  rw [S₁_index]
  intro id nd hmem hop
  have hp := plus_of_mem₁ hmem hop
  simp only [plusNodes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨p₁, by simp [act, ret], ι₁.symm⟩
  · exact ⟨p₂, by simp [act, ret], ι₂.symm⟩
  · exact ⟨p₃, by simp [act, ret], ι₃.symm⟩

/-- The retired node `{a, b, d}` is a `+`-node of the index that is not
active: `FCover` fails, so the covering form of the final theorem does not
apply to a store in which completion collapsed a node. -/
theorem not_cover : ¬ FCover A₁.Sa.index 0 act ι := by
  show ¬ FCover S₁.index 0 act ι
  rw [S₁_index]
  intro h
  obtain ⟨p, hp, hι⟩ := h 11 ⟨0, .mset {0, 1, 3}⟩ (by simp [G₁, nodes₁, nodes₀]) rfl
  rcases mem_act hp with rfl | rfl
  · rw [ι₁] at hι; exact absurd hι (by decide)
  · rw [ι₃] at hι; exact absurd hι (by decide)

/-! ## The final theorem, instantiated -/

/-- **Non-vacuity of the final theorem.** `saturation_modulo_complete_store_atoms`
applied to the two rounds of the program above, the completion state `wst`
with leaf constants, and the rewrite `(rewrite (+ x y) (g x y))`, whose
right-hand side builds a node of another operator: every hypothesis is
proved here. -/
theorem witness_saturation_modulo_complete :
    ∀ r ∈ rules, ∀ (P : Pat) (root : Var), r.atoms = (atoms P root).map QAtom.scan →
      P.head = some 0 →
      ∀ p ∈ act, ∀ p' ∈ act, E (Laws.plainAC 5) wS p.1 p'.1 →
      ∀ σ, Matches A₁.Sa.index r.atoms σ → σ.node root = some (ι p') →
        FiredN A₁.Sa.graph ops σ r ∧
        σ.cls root = some (A₁.Sa.find (ι p)) ∧
        MatchC A₁.Sa.index P (A₁.Sa.find (ι p)) σ ∧
        MatchN A₁.Sa.index P (mkNode wst 0 p') σ :=
  saturation_modulo_complete_store_atoms (naive := naive) A₀ [A₁] matchersOK hyp_h₀ hyp_ok
    hyp_emit₀ hyp_chain (A := A₁) (by simp) hyp_fix witness_complete hyp_within hyp_sub

/-- The same run with the atomic set derived from the `atomic` bit
(`witness_complete_atomic`: `atomicOf wst = wA`). -/
theorem witness_saturation_modulo_complete_atomic :
    ∀ r ∈ rules, ∀ (P : Pat) (root : Var), r.atoms = (atoms P root).map QAtom.scan →
      P.head = some 0 →
      ∀ p ∈ act, ∀ p' ∈ act, E (Laws.plainAC 5) wS p.1 p'.1 →
      ∀ σ, Matches A₁.Sa.index r.atoms σ → σ.node root = some (ι p') →
        FiredN A₁.Sa.graph ops σ r ∧
        σ.cls root = some (A₁.Sa.find (ι p)) ∧
        MatchC A₁.Sa.index P (A₁.Sa.find (ι p)) σ ∧
        MatchN A₁.Sa.index P (mkNode wst 0 p') σ :=
  saturation_modulo_complete_store_atomic (naive := naive) A₀ [A₁] matchersOK hyp_h₀ hyp_ok
    hyp_emit₀ hyp_chain (A := A₁) (by simp) hyp_fix witness_complete_atomic hyp_within hyp_sub

/-! ## A match the conclusion speaks about -/

/-- The match `x ↦ c, y ↦ d` of `(+ x y)` at the node `{c, d}`. -/
def σcd : Binding where
  cls := fun v => if v = 0 then some 2 else if v = 1 then some 3 else if v = 2 then some 4
    else none
  node := fun v => if v = 2 then some 12 else none
  mult := fun _ => none
  rest := fun _ => none
  seqRest := fun _ => none
  finRest := fun _ => none

theorem σcd_matches : Matches A₁.Sa.index rule.atoms σcd := by
  show Matches S₁.index rule.atoms σcd
  rw [S₁_index]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    simp only [rule, List.mem_singleton] at hq
    subst hq
    refine ⟨12, ⟨0, .mset {2, 3}⟩, rfl, by simp [G₁, nodes₁, nodes₀], rfl, rfl, ?_⟩
    refine matchN_ac_vars.2 ⟨{2, 3}, [2, 3], rfl, by decide, rfl, by decide, ?_, ?_, ?_⟩
    · intro et het
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at het
      rcases het with rfl | rfl <;> rfl
    · intro et het
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at het
      rcases het with rfl | rfl <;> (simp only [MultOk]; decide)
    · show ∀ c ∈ ({2, 3} : Multiset C), c ∈ [2, 3]
      decide
  · intro x
    simp only [rule, List.mem_singleton, exists_eq_left, QAtom.binds, RAtom.binds, atom,
      RAtom.elems, σcd]
    by_cases h0 : x = 0
    · subst h0; simp
    by_cases h1 : x = 1
    · subst h1; simp
    by_cases h2 : x = 2
    · subst h2; simp
    simp [h0, h1, h2]
  · intro v
    simp only [rule, List.mem_singleton, σcd, atom]
    by_cases h : v = 2
    · subst h; simp
    · simp [h, eq_comm]
  · intro k
    simp [rule, σcd, RAtom.multVars, atom, multVars, Mult.vars]
  · intro r
    simp [rule, σcd, RAtom.msetRestVars, atom]
  · intro r
    simp [rule, σcd, RAtom.seqRestVars, atom]
  · intro r
    simp [rule, σcd, RAtom.setRestVars, atom]

/-- **The conclusion at a match.** The rewrite matched at `{c, d}` is fired
(`g(c, d)` is in the class of the root), its root class is the class of
`{c, d}`, where the rewrite matches at the class level, and it matches at
the represented node. The only active node theory-equal to `{c, d}` is
itself: `{a, b, d}`, theory-equal to it under `a + b = c`, is retired, and
the theorem quantifies over active nodes. Its class is that of `{c, d}` by
the construction of `wfind` (`wfind 11 = 4`), which records the merge
completion made before retiring it. -/
theorem witness_fires_modulo :
    FiredN A₁.Sa.graph ops σcd rule ∧
      σcd.cls 2 = some (A₁.Sa.find (ι p₃)) ∧
      MatchC A₁.Sa.index pat (A₁.Sa.find (ι p₃)) σcd ∧
      MatchN A₁.Sa.index pat (mkNode wst 0 p₃) σcd :=
  witness_saturation_modulo_complete rule (by simp [rules]) pat 2 rule_atoms rfl p₃
    (by simp [act]) p₃ (by simp [act]) (E.refl _) σcd σcd_matches (by rw [ι₃]; rfl)

/-- The retired node's class is the root class of the match, by the store's
union-find. -/
theorem retired_class : A₁.Sa.find (ι p₂) = A₁.Sa.find (ι p₃) := by
  rw [ι₂, ι₃]; rfl

/-! ## The final theorem at the retired root -/

/-- `{a, b, d} =_E {c, d}` under `a + b = c`. -/
theorem E_abd_cd : E (Laws.plainAC 5) wS p₂.1 p₃.1 := by
  show E (Laws.plainAC 5) wS {0, 1, 3} {2, 3}
  have h : E (Laws.plainAC 5) wS ({0, 1} + {3}) ({2} + {3}) := E.congr {3} (E.ax rfl)
  have e₁ : ({0, 1} : Monomial 5) + {3} = {0, 1, 3} := by decide
  have e₂ : ({2} : Monomial 5) + {3} = {2, 3} := by decide
  rwa [e₁, e₂] at h

/-- The nodes of the completion view: the three stored `+`-nodes and the
implicit nodes of the four leaf constants. -/
theorem view_nodes {M : Monomial 5} {c : Fin 5} (h : (M, c) ∈ wv.nodes) :
    (M = {0, 1} ∧ c = 2) ∨ (M = {0, 1, 3} ∧ c = 4) ∨ (M = {2, 3} ∧ c = 4) ∨
      (c.val < 4 ∧ M = {c}) := by
  rcases h with h | h
  · simp only [wst, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases h with ⟨hc, hM⟩ | ⟨h, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hc, hM⟩))
    · exact absurd h.symm (Option.some_ne_none c)

/-- Soundness of the view: two nodes of one class are `=_E`-equal. The
pairs are `{a, b}` with `c`, and `{a, b, d}` with `{c, d}`. -/
theorem witness_I2 : I2 (Laws.plainAC 5) wS wv := by
  intro M c M' c' h h' hcc
  have hcc' : c = c' := hcc
  subst hcc'
  rcases view_nodes h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hc, rfl⟩ <;>
  rcases view_nodes h' with ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩ | ⟨hc', rfl⟩ <;>
  first
    | exact E.refl _
    | exact absurd h₂ (by decide)
    | exact absurd hc' (by decide)
    | exact E.ax rfl
    | exact E_abd_cd
    | exact E.symm E_abd_cd
    | (subst h₂; exact E.symm (E.ax rfl))
    | (subst h₂; exact absurd hc (by decide))

/-- **The final theorem at a retired root, instantiated.**
`saturation_modulo_complete_store_retired_atoms` applied to the two rounds
of the program above, with the retired `{a, b, d}` in `ret`, the
correspondence and the cover over active and retired nodes together, and
`I2`, `I3` on the completion view: every hypothesis is proved here. -/
theorem witness_saturation_modulo_complete_retired :
    ∀ r ∈ rules, ∀ (P : Pat) (root : Var), r.atoms = (atoms P root).map QAtom.scan →
      P.head = some 0 →
      ∀ σ, Matches A₁.Sa.index r.atoms σ →
        FiredN A₁.Sa.graph ops σ r ∧
        ∃ p' ∈ act ∪ ret, σ.node root = some (ι p') ∧ MatchN A₁.Sa.index P (mkNode wst 0 p') σ ∧
          ∃ q ∈ wv.active, E (Laws.plainAC 5) wS p'.1 q.1 ∧ wst.find q.2 = wst.find p'.2 ∧
            σ.cls root = some (clsId (wst.find q.2)) ∧
            MatchC A₁.Sa.index P (clsId (wst.find q.2)) σ ∧
            ∀ p ∈ act, E (Laws.plainAC 5) wS p.1 p'.1 →
              σ.cls root = some (A₁.Sa.find (ι p)) ∧ MatchC A₁.Sa.index P (A₁.Sa.find (ι p)) σ :=
  saturation_modulo_complete_store_retired_atoms (naive := naive) A₀ [A₁] matchersOK hyp_h₀
    hyp_ok hyp_emit₀ hyp_chain (A := A₁) (by simp) hyp_fix witness_complete witness_I2 witness_I3
    hyp_within hyp_ret hyp_subR hyp_coverR

/-- The match `x ↦ a, y ↦ b, z ↦ d` of `(+ x y z)` at the retired node
`{a, b, d}`. -/
def σabd : Binding where
  cls := fun v => if v = 0 then some 0 else if v = 1 then some 1 else if v = 2 then some 3
    else if v = 3 then some 4 else none
  node := fun v => if v = 3 then some 11 else none
  mult := fun _ => none
  rest := fun _ => none
  seqRest := fun _ => none
  finRest := fun _ => none

theorem σabd_matches : Matches A₁.Sa.index rule₂.atoms σabd := by
  show Matches S₁.index rule₂.atoms σabd
  rw [S₁_index]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    simp only [rule₂, List.mem_singleton] at hq
    subst hq
    refine ⟨11, ⟨0, .mset {0, 1, 3}⟩, rfl, by simp [G₁, nodes₁, nodes₀], rfl, rfl, ?_⟩
    refine matchN_ac_vars.2 ⟨{0, 1, 3}, [0, 1, 3], rfl, by decide, rfl, by decide, ?_, ?_, ?_⟩
    · intro et het
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at het
      rcases het with rfl | rfl | rfl <;> rfl
    · intro et het
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at het
      rcases het with rfl | rfl | rfl <;> (simp only [MultOk]; decide)
    · show ∀ c ∈ ({0, 1, 3} : Multiset C), c ∈ [0, 1, 3]
      decide
  · intro x
    simp only [rule₂, List.mem_singleton, exists_eq_left, QAtom.binds, RAtom.binds, atom₂,
      RAtom.elems, σabd]
    by_cases h0 : x = 0
    · subst h0; simp
    by_cases h1 : x = 1
    · subst h1; simp
    by_cases h2 : x = 2
    · subst h2; simp
    by_cases h3 : x = 3
    · subst h3; simp
    simp [h0, h1, h2, h3]
  · intro v
    simp only [rule₂, List.mem_singleton, σabd, atom₂]
    by_cases h : v = 3
    · subst h; simp
    · simp [h, eq_comm]
  · intro k
    simp [rule₂, σabd, RAtom.multVars, atom₂, multVars, Mult.vars]
  · intro r
    simp [rule₂, σabd, RAtom.msetRestVars, atom₂]
  · intro r
    simp [rule₂, σabd, RAtom.seqRestVars, atom₂]
  · intro r
    simp [rule₂, σabd, RAtom.setRestVars, atom₂]

/-- **The conclusion at the match rooted at the retired node.** The second
rewrite matched at `{a, b, d}` is fired (`k` is in the class of the root),
its root class is the class of the active node `{c, d}`, `=_E`-equal to
`{a, b, d}` under `a + b = c`, where the rewrite matches at the class
level, and it matches at the represented node of `{a, b, d}`. The theorem
reaches `{c, d}` through the rules of the completion state (`{a, b, d}`
rewrites to it by `{a, b} → {c}`, `witness_I3`), not through the store's
union-find (`retired_class`). -/
theorem witness_fires_retired :
    FiredN A₁.Sa.graph ops σabd rule₂ ∧
      σabd.cls 3 = some (A₁.Sa.find (ι p₃)) ∧
      MatchC A₁.Sa.index pat₂ (A₁.Sa.find (ι p₃)) σabd ∧
      MatchN A₁.Sa.index pat₂ (mkNode wst 0 p₂) σabd := by
  obtain ⟨hf, p', hp', hid, hmn, -, -, -, -, -, -, hall⟩ :=
    witness_saturation_modulo_complete_retired rule₂ (by simp [rules]) pat₂ 3 rule₂_atoms rfl
      σabd σabd_matches
  have h11 : 11 = ι p' := Option.some.inj ((show σabd.node 3 = some 11 from rfl).symm.trans hid)
  have hp₂ : p' = p₂ := by
    rcases Finset.mem_union.1 hp' with h | h
    · rcases mem_act h with rfl | rfl
      · rw [ι₁] at h11; exact absurd h11 (by decide)
      · rw [ι₃] at h11; exact absurd h11 (by decide)
    · exact mem_ret h
  subst hp₂
  obtain ⟨hcls, hmc⟩ := hall p₃ (by simp [act]) (E.symm E_abd_cd)
  exact ⟨hf, hcls, hmc, hmn⟩

/-! ## The store closed under the theory, derived -/

/-- `hyp_ok` with the sequence nodes literal (`RoundOKE`): the store
persists literally in both rounds. -/
theorem hyp_okE : ∀ A ∈ [A₀, A₁], RoundOKE sig rules A := by
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl
  · exact ⟨mkRound_wf S₀ (by rw [S₀_index]; rfl), rfl,
      (persist S₀ rfl (fun p hp => List.mem_append_left _ hp)).toE ops,
      by show RulesWF sig S₁.index rules; rw [S₁_index]; exact rulesWF₁⟩
  · exact ⟨mkRound_wf S₁ (by rw [S₁_index]; rfl), rfl, (persist S₁ rfl (fun p hp => hp)).toE ops,
      by show RulesWF sig S₁.index rules; rw [S₁_index]; exact rulesWF₁⟩

/-- The three `+`-nodes are nodes of the state. -/
theorem hyp_stored : Stored wst (act ∪ ret) := fun p hp =>
  (Finset.mem_union.1 hp).elim (fun h => (hyp_within p h).1) (hyp_ret p)

/-- The correspondence on the store (no node is skipped, so the store is
the index). -/
theorem hyp_subG : SubRep A₁.Sa.graph wst 0 (act ∪ ret) ι := by
  have h := hyp_subR.union
  rwa [show A₁.Sa.index = G₁ from S₁_index] at h

theorem hyp_coverG : FCover A₁.Sa.graph 0 (act ∪ ret) ι := by
  have h := hyp_coverR
  rwa [show A₁.Sa.index = G₁ from S₁_index] at h

/-- Every summand of the three `+`-nodes is a leaf constant. -/
theorem hyp_summands : ∀ p ∈ act ∪ ret, ∀ y ∈ p.1, y ∈ wA := by
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · rcases mem_act h with rfl | rfl <;> decide
  · rw [mem_ret h]; decide

/-- `+` has no law in the store and none in the state. -/
theorem hyp_laws : LawsRead A₁.Sa ops 0 wv (Laws.plainAC 5) := LawsRead.of_none rfl rfl rfl

/-- No pair node is stored. -/
theorem hyp_sorted : PairsSorted A₁.Sa := by
  intro id f a b h
  change _ ∈ nodes₁ at h
  simp [nodes₁, nodes₀, gNodes, kNodes] at h

/-- The remainder: `+` is the only AC operator, and no ACI or A node is
stored. -/
theorem hyp_rest : TheoryClosedRest A₁.Sa ops 0 where
  mset g hg := closedAC_of_absent
    (fun id m h => by change _ ∈ nodes₁ at h; simp [nodes₁, nodes₀, gNodes, kNodes, hg] at h) rfl rfl rfl
  set g := closedACI_of_absent (fun id s h => by change _ ∈ nodes₁ at h; simp [nodes₁, nodes₀, gNodes, kNodes] at h) rfl
  seq g := closedA_of_absent (fun id l h => by change _ ∈ nodes₁ at h; simp [nodes₁, nodes₀, gNodes, kNodes] at h) rfl

/-- **The store of the fixpoint round is closed under the theory**, derived
from the completion state through the correspondence
(`theoryClosed_of_complete`). -/
theorem witness_theoryClosed : TheoryClosed A₁.Sa ops :=
  theoryClosed_of_complete (CompleteHyps.ofAtoms witness_complete) witness_I2 witness_I3 keys₁
    (Stored.withAtoms hyp_stored wA none) (hyp_subG.withAtoms wA none) hyp_coverG
    (summandsAtomic_withAtoms hyp_summands) hyp_laws dedup₁ hyp_sorted hyp_rest

/-- **Saturation with completion on, instantiated.**
`saturation_complete_closed_of_complete_atoms` on the two rounds of the
program above, with every hypothesis proved: at the fixpoint every match
is fired modulo the theory, and every union a rule asks for holds between
any values of its two sides. -/
theorem witness_saturation_complete_closed :
    ∀ r ∈ rules, ∀ σ, Matches A₁.Sa.index r.atoms σ →
      FiredE A₁.Sa.graph ops σ r ∧
      ∀ a b, Action.union a b ∈ r.actions →
        ∀ c₁ c₂, DenN A₁.Sa.graph ops σ a c₁ → DenN A₁.Sa.graph ops σ b c₂ → c₁ = c₂ :=
  saturation_complete_closed_of_complete_atoms A₀ [A₁] matchersOK hyp_h₀ hyp_okE hyp_emit₀
    (SChainN.toE hyp_chain) (A := A₁) (by simp) hyp_fix witness_complete witness_I2 witness_I3
    keys₁ hyp_stored hyp_subG hyp_coverG hyp_summands hyp_laws hyp_sorted hyp_rest

end SemperProofs.Final.Witness
