import SemperProofs.CC.Main
import SemperProofs.EMatch.Engine.Main
import SemperProofs.EMatch.Env.Snapshot

/-!
# Bridge: the e-matching graph of a completion state

The congruence-closure development (`SemperProofs.CC`) works on one AC
operator: a node is a pair `(M, c)` of a monomial `M : Multiset (Fin n)`
(the canonical child multiset) and a class `c : Fin n`, the partition is
`st.find`. The e-matching development (`Semper.EMatch`) works on a `Graph`:
a list of identified nodes with `mset` children over `C = Nat` and a
representative map `find : NodeId → C`.

`represents st f A` is the graph of the operator `f` read from the state
`st`: one `mset` node per active node `p ∈ A`, where the finset `A`
enumerates `st.active` (`Enumerates st A`; `State.nodes` is a `Set`, so an
enumeration must be supplied). Node ids are `n + encode p`, the classes are
the values of `st.find` and the children are the representatives of the
monomial's summands, so that the graph's `find` is idempotent and its
children are canonical whenever `st.find` is idempotent.

The well-formedness facts the engine theorems need (`KeysNodup`,
`Conforms`, `ChildrenCanon`, `FindIdem`) are proved here.
-/

namespace SemperProofs.CC.Bridge

open Semper.EMatch

variable {n : ℕ}

/-! ## The graph -/

/-- The class id of a class of the state: the embedding `Fin n → Nat`. -/
def clsId (c : Fin n) : C := c.val

/-- The node id of a state node: `n + encode (M, c)`. The offset reserves
`0 .. n-1` for the class ids, so that `findId` can be idempotent. -/
def nodeId (p : Monomial n × Fin n) : NodeId := n + Encodable.encode p

/-- The `mset` node of a state node: head `f`, children the representatives
of the summands. -/
def mkNode (st : State n) (f : Sym) (p : Monomial n × Fin n) : Node :=
  ⟨f, .mset (p.1.map fun x => clsId (st.find x))⟩

/-- The representative map of the graph: on a class id, `st.find`; on a node
id, `st.find` of the node's class; the identity elsewhere. -/
def findId (st : State n) (id : NodeId) : C :=
  if h : id < n then clsId (st.find ⟨id, h⟩)
  else
    match (Encodable.decode (id - n) : Option (Monomial n × Fin n)) with
    | some p => clsId (st.find p.2)
    | none => id

/-- The e-matching graph of the operator `f` read from the state `st`,
with `A` enumerating the active nodes. -/
noncomputable def represents (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n)) : Graph :=
  ⟨A.toList.map fun p => (nodeId p, mkNode st f p), findId st⟩

/-- `A` enumerates the active nodes of the state. -/
def Enumerates (st : State n) (A : Finset (Monomial n × Fin n)) : Prop :=
  ∀ p, p ∈ A ↔ p ∈ st.active

/-- Every node of `A` is an active node of the state. The bridge theorems
need only this half of `Enumerates`; it is what a state's completion view
(`State.withAtoms`, which adds the implicit nodes of the leaf constants)
and an enumeration of the stored active nodes satisfy. -/
def Within (st : State n) (A : Finset (Monomial n × Fin n)) : Prop :=
  ∀ p ∈ A, p ∈ st.active

theorem Enumerates.within {st : State n} {A : Finset (Monomial n × Fin n)}
    (h : Enumerates st A) : Within st A :=
  fun p hp => (h p).1 hp

/-- `st.find` returns representatives. The `State` development does not
state this invariant (`merge` preserves it); it is taken as a hypothesis
where the graph's canonicity is needed. -/
def FindIdem (st : State n) : Prop := ∀ x, st.find (st.find x) = st.find x

/-! ## Basic lemmas -/

theorem nodeId_injective : Function.Injective (nodeId (n := n)) := by
  intro p q h
  exact Encodable.encode_injective (Nat.add_left_cancel h)

theorem findId_nodeId (st : State n) (p : Monomial n × Fin n) :
    findId st (nodeId p) = clsId (st.find p.2) := by
  have h : ¬ nodeId p < n := Nat.not_lt.2 (Nat.le_add_right _ _)
  have h2 : nodeId p - n = Encodable.encode p := Nat.add_sub_cancel_left _ _
  simp [findId, h, h2, Encodable.encodek]

theorem findId_clsId (st : State n) (c : Fin n) : findId st (clsId c) = clsId (st.find c) := by
  simp [findId, clsId]

theorem represents_find (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n))
    (p : Monomial n × Fin n) :
    (represents st f A).find (nodeId p) = clsId (st.find p.2) :=
  findId_nodeId st p

theorem mem_represents {st : State n} {f : Sym} {A : Finset (Monomial n × Fin n)}
    {id : NodeId} {nd : Node} :
    (id, nd) ∈ (represents st f A).nodes ↔ ∃ p ∈ A, id = nodeId p ∧ nd = mkNode st f p := by
  simp only [represents, List.mem_map, Finset.mem_toList, Prod.mk.injEq]
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, hp, h1.symm, h2.symm⟩
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, hp, h1.symm, h2.symm⟩

theorem node_mem_represents {st : State n} {f : Sym} {A : Finset (Monomial n × Fin n)}
    {p : Monomial n × Fin n} (hp : p ∈ A) :
    (nodeId p, mkNode st f p) ∈ (represents st f A).nodes :=
  mem_represents.2 ⟨p, hp, rfl, rfl⟩

/-! ## Well-formedness -/

/-- Node ids are distinct. -/
theorem represents_keysNodup (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n)) :
    (represents st f A).KeysNodup := by
  unfold Graph.KeysNodup represents
  simp only [List.map_map]
  have : ((fun x : NodeId × Node => x.1) ∘ fun p : Monomial n × Fin n => (nodeId p, mkNode st f p))
      = nodeId := by funext p; rfl
  rw [this]
  exact A.nodup_toList.map nodeId_injective

/-- Every node is an `mset` node of the operator `f`, so the graph conforms
to any signature that declares `f` AC. -/
theorem represents_conforms (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n))
    (sig : Sym → Kind) (hf : sig f = .ac) : (represents st f A).Conforms sig := by
  intro p hp
  obtain ⟨q, _, _, h2⟩ := (mem_represents (id := p.1) (nd := p.2)).1 hp
  rw [h2]
  simp [mkNode, Children.kind, hf]

/-- Every node has head `f`. -/
theorem represents_op {st : State n} {f : Sym} {A : Finset (Monomial n × Fin n)}
    {id : NodeId} {nd : Node} (h : (id, nd) ∈ (represents st f A).nodes) : nd.op = f := by
  obtain ⟨p, _, _, h2⟩ := mem_represents.1 h
  subst h2; rfl

/-- Children are representatives (spec D, H2) when `st.find` is idempotent. -/
theorem represents_childrenCanon (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n))
    (hidem : FindIdem st) : (represents st f A).ChildrenCanon := by
  intro p hp
  obtain ⟨q, _, _, h2⟩ := (mem_represents (id := p.1) (nd := p.2)).1 hp
  rw [h2]
  simp only [mkNode, Children.Canon, Multiset.mem_map]
  rintro c ⟨x, _, rfl⟩
  show findId st (clsId (st.find x)) = clsId (st.find x)
  rw [findId_clsId, hidem]

/-- `findId` returns a class id of the state or is the identity. -/
theorem findId_cases (st : State n) (id : NodeId) :
    (∃ c, findId st id = clsId (st.find c)) ∨ findId st id = id := by
  unfold findId
  by_cases h : id < n
  · exact Or.inl ⟨⟨id, h⟩, by simp [h]⟩
  · rcases hd : (Encodable.decode (id - n) : Option (Monomial n × Fin n)) with _ | p
    · exact Or.inr (by simp [h])
    · exact Or.inl ⟨p.2, by simp [h]⟩

/-- The graph's `find` is idempotent (spec D, H1) when `st.find` is. -/
theorem represents_findIdem (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n))
    (hidem : FindIdem st) : (represents st f A).FindIdem := by
  intro id
  show findId st (findId st id) = findId st id
  rcases findId_cases st id with ⟨c, hc⟩ | hc
  · rw [hc, findId_clsId, hidem]
  · rw [hc]; exact hc

/-- The graph's `find` on a node id is the class of the state node. -/
theorem represents_find_mem {st : State n} {f : Sym} {A : Finset (Monomial n × Fin n)}
    {id : NodeId} {nd : Node} (h : (id, nd) ∈ (represents st f A).nodes) :
    ∃ p ∈ A, id = nodeId p ∧ nd = mkNode st f p ∧
      (represents st f A).find id = clsId (st.find p.2) := by
  obtain ⟨p, hp, h1, h2⟩ := mem_represents.1 h
  exact ⟨p, hp, h1, h2, h1 ▸ represents_find st f A p⟩

end SemperProofs.CC.Bridge
