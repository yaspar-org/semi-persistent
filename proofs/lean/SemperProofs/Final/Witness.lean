import SemperProofs.Final.Store
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
```

The completion state is the one of `CC/AtomsWitness.lean` (`wst`, with the
asserted equation `a + b = c` and the stored `+`-nodes `{a, b}` in `c`'s
class and `{a, b, d}`, `{c, d}` in class 4), for which `witness_complete`
proves `CompleteAtoms`. The e-graph stores the four leaf constants, the
three `+`-nodes, and, after round 0, the four `g`-nodes the rewrite builds:
`g(a, b)`, `g(b, a)` in `c`'s class and `g(c, d)`, `g(d, c)` in class 4.
The rewrite matches `{a, b}` and `{c, d}` in both orders, and `{a, b, d}`
not at all (the pattern has two elements and no rest).

Symbols: `+ = 0`, `g = 1`, `a, b, c, d = 2, 3, 4, 5`. Classes: `a, b, c, d`
are `0, 1, 2, 3`, the class of `t` and `u` is `4`. Node ids: the leaf
constants are `0` to `3`, the `+`-nodes `10, 11, 12`, the `g`-nodes `20` to
`23`.

Round 0 matches on the initial store and builds the `g`-nodes; round 1
matches on the result, builds nothing new and is the fixpoint. Both rounds
emit every naive match. `witness_saturation_modulo_complete` instantiates
`saturation_modulo_complete_store_atoms` with this run: every hypothesis is
proved, none assumed. The rewrite's right-hand side is a `g`-node, which
the former final theorem (`represents` as the whole graph, literal `Den`)
could not hold. `witness_fires_modulo` reads the conclusion at the match
`x ↦ c, y ↦ d` rooted at `{c, d}` and the theory-equal node `{a, b, d}`.
-/

namespace SemperProofs.Final.Witness

open Semper.EMatch Semper.EMatch.Fidelity SemperProofs.CC SemperProofs.CC.Bridge
  SemperProofs.CC.AtomsWitness

/-! ## The e-graph -/

/-- The kinds: `+` is AC, `g` plain binary, the constants plain nullary. -/
def sig : Sym → Kind := fun s => if s = 0 then .ac else if s = 1 then .plain 2 else .plain 0

/-- The stored active `+`-nodes of `wst`. -/
def p₁ : Monomial 5 × Fin 5 := ({0, 1}, 2)
def p₂ : Monomial 5 × Fin 5 := ({0, 1, 3}, 4)
def p₃ : Monomial 5 × Fin 5 := ({2, 3}, 4)

def act : Finset (Monomial 5 × Fin 5) := {p₁, p₂, p₃}

/-- The ids of the `+`-nodes. -/
def ι (p : Monomial 5 × Fin 5) : NodeId := if p = p₁ then 10 else if p = p₂ then 11 else 12

/-- The leaf constants and the three `+`-nodes. -/
def nodes₀ : List (NodeId × Node) :=
  [(0, ⟨2, .tuple []⟩), (1, ⟨3, .tuple []⟩), (2, ⟨4, .tuple []⟩), (3, ⟨5, .tuple []⟩),
   (10, ⟨0, .mset {0, 1}⟩), (11, ⟨0, .mset {0, 1, 3}⟩), (12, ⟨0, .mset {2, 3}⟩)]

/-- The `g`-nodes the rewrite builds. -/
def gNodes : List (NodeId × Node) :=
  [(20, ⟨1, .tuple [0, 1]⟩), (21, ⟨1, .tuple [1, 0]⟩), (22, ⟨1, .tuple [2, 3]⟩),
   (23, ⟨1, .tuple [3, 2]⟩)]

def nodes₁ : List (NodeId × Node) := nodes₀ ++ gNodes

/-- The union-find: a class is named by its representative `0` to `4`. -/
def wfind (id : NodeId) : C :=
  if id = 10 ∨ id = 20 ∨ id = 21 then 2
  else if id = 11 ∨ id = 12 ∨ id = 22 ∨ id = 23 then 4
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
  simp only [G₁, nodes₁, nodes₀, gNodes, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
  simp [pat, atom, atoms, atomsAt, atomsChildrenAC, atomsChild, Pat.freshAbove, Pat.vars]

/-- The rewrite: its atom, the scheduler's plan for it, and the action
`union (var root) rhs` (`apply.rs:377-384`). -/
def rule : Rule where
  atoms := [.scan atom]
  plan := (lower atom ∅).map (0, ·) ++ []
  actions := [.union (.var 2) rhs]

def rules : List Rule := [rule]

theorem rule_atoms : rule.atoms = (atoms pat 2).map QAtom.scan := by rw [atoms_pat]; rfl

theorem plansOK : PlansOK rules := by
  intro r hr
  simp only [rules, List.mem_singleton] at hr
  subst hr
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

theorem rulesWF₀ : RulesWF sig G₀ rules := by
  intro r hr; simp only [rules, List.mem_singleton] at hr; subst hr; exact atomsWF keys₀ conf₀

theorem rulesWF₁ : RulesWF sig G₁ rules := by
  intro r hr; simp only [rules, List.mem_singleton] at hr; subst hr; exact atomsWF keys₁ conf₁

/-! ## The matches -/

/-- The `+`-nodes of the e-graph. -/
def plusNodes : List (NodeId × Node) :=
  [(10, ⟨0, .mset {0, 1}⟩), (11, ⟨0, .mset {0, 1, 3}⟩), (12, ⟨0, .mset {2, 3}⟩)]

theorem plus_of_mem₁ {id : NodeId} {nd : Node} (h : (id, nd) ∈ nodes₁) (hop : nd.op = 0) :
    (id, nd) ∈ plusNodes := by
  simp only [nodes₁, nodes₀, gNodes, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp_all [plusNodes]

theorem plus_of_mem₀ {id : NodeId} {nd : Node} (h : (id, nd) ∈ nodes₀) (hop : nd.op = 0) :
    (id, nd) ∈ plusNodes :=
  plus_of_mem₁ (List.mem_append_left _ h) hop

/-- Every match of the rewrite: the root is `{a, b}` or `{c, d}`, the
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

/-! ## The consequences: the `g`-nodes -/

/-- No unit, no nilpotent count, no inverse. -/
def ops : Sym → OpLaws := fun _ => ⟨none, none, none⟩

theorem rule_plan_ok : SchedA rule.atoms ∅ ∅ rule.plan := plansOK rule (by simp [rules])

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

/-- The root's value. -/
theorem den_root {σ : Binding} {c : C} (h : σ.cls 2 = some c) (hc : wfind c = c) :
    DenN G₁ ops σ (.var 2) c := by
  have := DenN.var (G := G₁) (L := ops) h
  rwa [show G₁.find c = c from hc] at this

/-- Every match of the rewrite on either snapshot has its right-hand side
built in the class of its root, after round 0. -/
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

/-- One round on stores applying every naive match of the rewrite. -/
def mkActRound (Sb : Store) {nodes : List (NodeId × Node)}
    (hidx : Sb.index = ⟨nodes, wfind⟩)
    (hplus : ∀ id nd, (id, nd) ∈ nodes → nd.op = 0 → (id, nd) ∈ plusNodes)
    (hwf : AtomsWF Sb.index sig rule.atoms) : SActRoundN ops where
  R := mkRound Sb
  Sb := Sb
  Sa := S₁
  before_eq := rfl
  after_eq := rfl
  emitted := fun r σ => r = rule ∧ σ ∈ runNaive Sb.index r.plan
  inserts := by
    rintro r σ ⟨rfl, -⟩ t ht
    simp [rule] at ht
  unions := by
    rintro r σ ⟨rfl, hσ⟩ a b hab
    simp only [rule, List.mem_singleton, Action.union.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    have hm := (mem_runNaive_iff hwf rule_plan_ok σ).1 hσ
    rw [hidx] at hm
    exact unions_ok hplus hm
  subsumes := by
    rintro r σ ⟨rfl, -⟩ x hx
    simp [rule] at hx
  unions_merged := by
    intro u hu
    simp only [mkRound, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> rfl

/-- Round 0: from the initial store to the store with the `g`-nodes. -/
def A₀ : SActRoundN ops :=
  mkActRound S₀ S₀_index (fun _ _ h hop => plus_of_mem₀ h hop)
    (by rw [S₀_index]; exact atomsWF keys₀ conf₀)

/-- Round 1: on the store with the `g`-nodes; it builds nothing new. -/
def A₁ : SActRoundN ops :=
  mkActRound S₁ S₁_index (fun _ _ h hop => plus_of_mem₁ h hop)
    (by rw [S₁_index]; exact atomsWF keys₁ conf₁)

/-- Every rule is routed to the naive matcher. -/
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

theorem hyp_emit₀ : EmitsAllN A₀ rules := by
  intro r hr σ hσ
  simp only [rules, List.mem_singleton] at hr
  exact ⟨hr, hσ⟩

theorem hyp_chain : SChainN naive rules A₀ [A₁] := by
  refine ⟨rfl, ⟨true, fun _ => rfl, ?_⟩, trivial⟩
  intro r hr
  simp only [rules, List.mem_singleton] at hr
  refine ⟨fun _ σ hσ => ⟨hr, hσ⟩, fun h => absurd h (by simp [route, naive])⟩

theorem hyp_fix : A₁.Unchanged := ⟨fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl⟩

theorem mem_act {p : Monomial 5 × Fin 5} (hp : p ∈ act) : p = p₁ ∨ p = p₂ ∨ p = p₃ := by
  simpa [act] using hp

theorem hyp_within : Within wst act := by
  intro p hp
  rcases mem_act hp with rfl | rfl | rfl
  · exact stored_active (Or.inl ⟨rfl, rfl⟩)
  · exact stored_active (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact stored_active (Or.inr (Or.inr ⟨rfl, rfl⟩))

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
    rcases mem_act hp with rfl | rfl | rfl
    · rw [ι₁, mkNode₁]; simp [G₁, nodes₁, nodes₀]
    · rw [ι₂, mkNode₂]; simp [G₁, nodes₁, nodes₀]
    · rw [ι₃, mkNode₃]; simp [G₁, nodes₁, nodes₀]
  · intro p hp
    rcases mem_act hp with rfl | rfl | rfl
    · rw [ι₁]; rfl
    · rw [ι₂]; rfl
    · rw [ι₃]; rfl

theorem hyp_cover : FCover A₁.Sa.index 0 act ι := by
  show FCover S₁.index 0 act ι
  rw [S₁_index]
  intro id nd hmem hop
  have := plus_of_mem₁ hmem hop
  simp only [plusNodes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
  rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨p₁, by simp [act], ι₁.symm⟩
  · exact ⟨p₂, by simp [act], ι₂.symm⟩
  · exact ⟨p₃, by simp [act], ι₃.symm⟩

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
  saturation_modulo_complete_store_atoms (naive := naive) A₀ [A₁] plansOK hyp_h₀ hyp_ok
    hyp_emit₀ hyp_chain (A := A₁) (by simp) hyp_fix witness_complete hyp_within hyp_sub

/-- The covering form, with the same run: every match of the rewrite at the
fixpoint is fired and lands in the class of every theory-equal stored
`+`-node. -/
theorem witness_saturation_modulo_complete_cover :
    ∀ r ∈ rules, ∀ (P : Pat) (root : Var), r.atoms = (atoms P root).map QAtom.scan →
      P.head = some 0 →
      ∀ σ, Matches A₁.Sa.index r.atoms σ →
        FiredN A₁.Sa.graph ops σ r ∧
        ∃ p' ∈ act, σ.node root = some (ι p') ∧
          ∀ p ∈ act, E (Laws.plainAC 5) wS p.1 p'.1 →
            σ.cls root = some (A₁.Sa.find (ι p)) ∧
              MatchC A₁.Sa.index P (A₁.Sa.find (ι p)) σ :=
  saturation_modulo_complete_store_cover (naive := naive) A₀ [A₁] plansOK hyp_h₀ hyp_ok
    hyp_emit₀ hyp_chain (A := A₁) (by simp) hyp_fix witness_complete hyp_within hyp_sub
    hyp_cover

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

/-- `{a, b, d}` and `{c, d}` are theory-equal under `a + b = c`. -/
theorem E₂₃ : E (Laws.plainAC 5) wS p₂.1 p₃.1 := by
  have h := E.congr (L := Laws.plainAC 5) ({3} : Monomial 5) (E.ax (S := wS) rfl)
  have e₁ : ({0, 1} : Monomial 5) + {3} = {0, 1, 3} := by decide
  have e₂ : ({2} : Monomial 5) + {3} = {2, 3} := by decide
  rw [e₁, e₂] at h
  exact h

/-- **The conclusion at a match.** The rewrite matched at `{c, d}` is fired
(`g(c, d)` is in the class of the root), and its root class is the class
of the theory-equal node `{a, b, d}`, where the rewrite also matches at the
class level. -/
theorem witness_fires_modulo :
    FiredN A₁.Sa.graph ops σcd rule ∧
      σcd.cls 2 = some (A₁.Sa.find (ι p₂)) ∧
      MatchC A₁.Sa.index pat (A₁.Sa.find (ι p₂)) σcd ∧
      MatchN A₁.Sa.index pat (mkNode wst 0 p₃) σcd :=
  witness_saturation_modulo_complete rule (by simp [rules]) pat 2 rule_atoms rfl p₂
    (by simp [act]) p₃ (by simp [act]) E₂₃ σcd σcd_matches (by rw [ι₃]; rfl)

end SemperProofs.Final.Witness
