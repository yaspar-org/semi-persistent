import SemperProofs.CC.Bridge.Modulo

/-!
# Bridge: the represented graph as a part of a larger graph

`represents st f A` is a graph with one `mset` node per active node and no
other node. The engine's index also holds leaf nodes, nodes of other
operators, and the nodes the actions build. `SubRep G st f A ι` says the
represented nodes sit inside an arbitrary graph `G`: the active node
`p ∈ A` is stored in `G` under the id `ι p` with the children of
`mkNode st f p`, and `G`'s `find` reads it as its class in `st`. Nothing is
said of `G`'s other nodes. `FCover G f A ι` adds that every `f`-node of `G`
is one of them.

The bridge theorems of `Modulo.lean` hold on the part: two theory-equal
active nodes are in one class of `G` (`ac_equal_same_class_sub`), and a
match at one is a class-level match at the other
(`matches_closed_under_theory_sub`). `represents` is the case
`G = represents st f A`, `ι = nodeId` (`represents_subRep`).
-/

namespace SemperProofs.CC.Bridge

open Semper.EMatch

variable {n : ℕ}

/-- The graph of `f` read from `st` is a part of `G`, the active node `p`
stored under the id `ι p`. -/
structure SubRep (G : Graph) (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n))
    (ι : Monomial n × Fin n → NodeId) : Prop where
  nodes : ∀ p ∈ A, (ι p, mkNode st f p) ∈ G.nodes
  find : ∀ p ∈ A, G.find (ι p) = clsId (st.find p.2)

/-- Every `f`-node of `G` is the node of some `p ∈ A`. -/
def FCover (G : Graph) (f : Sym) (A : Finset (Monomial n × Fin n))
    (ι : Monomial n × Fin n → NodeId) : Prop :=
  ∀ id nd, (id, nd) ∈ G.nodes → nd.op = f → ∃ p ∈ A, id = ι p

/-- The represented graph is a part of itself. -/
theorem represents_subRep (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n)) :
    SubRep (represents st f A) st f A nodeId :=
  ⟨fun _ hp => node_mem_represents hp, fun p _ => represents_find st f A p⟩

theorem represents_fcover (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n)) :
    FCover (represents st f A) f A nodeId := by
  intro id nd hmem _
  obtain ⟨p, hp, rfl, -⟩ := mem_represents.1 hmem
  exact ⟨p, hp, rfl⟩

/-- The completion view reads the same nodes and classes. -/
theorem SubRep.withAtoms {G : Graph} {st : State n} {f : Sym} {A : Finset (Monomial n × Fin n)}
    {ι : Monomial n × Fin n → NodeId} (h : SubRep G st f A ι) (X : Set (Fin n))
    (u : Option (Fin n)) : SubRep G (st.withAtoms X u) f A ι :=
  ⟨h.nodes, h.find⟩

/-- Two `=_E`-equal active nodes of a converged state are in one class of
any graph the represented graph is a part of. -/
theorem ac_equal_same_class_sub {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} {G : Graph} {f : Sym}
    {ι : Monomial n × Fin n → NodeId} (h : CompleteHyps L S st) (hA : Within st A)
    (hs : SubRep G st f A ι) {p q : Monomial n × Fin n} (hp : p ∈ A) (hq : q ∈ A)
    (hpq : E L S p.1 q.1) : G.find (ι p) = G.find (ι q) := by
  rw [hs.find p hp, hs.find q hq]
  exact congrArg clsId (ac_equal_same_class h (hA p hp) (hA q hq) hpq)

/-- A node of `G` stored under `ι p'` is the represented node. -/
theorem SubRep.node_eq {G : Graph} {st : State n} {f : Sym} {A : Finset (Monomial n × Fin n)}
    {ι : Monomial n × Fin n → NodeId} (hs : SubRep G st f A ι) (hk : G.KeysNodup)
    {p : Monomial n × Fin n} (hp : p ∈ A) {nd : Node} (hmem : (ι p, nd) ∈ G.nodes) :
    nd = mkNode st f p := by
  have h1 := lookupNode_of_mem hk hmem
  have h2 := lookupNode_of_mem hk (hs.nodes p hp)
  rw [h1] at h2
  exact Option.some.inj h2

/-- Matches are closed under the theory on any graph the represented
graph is a part of, at the class level: a match at the node of `p'` is a
match at the class of every active `p` theory-equal to `p'`. -/
theorem matches_closed_under_theory_sub {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} {G : Graph} {f : Sym}
    {ι : Monomial n × Fin n → NodeId} (h : CompleteHyps L S st) (hA : Within st A)
    (hs : SubRep G st f A ι) {p p' : Monomial n × Fin n} (hp : p ∈ A) (hp' : p' ∈ A)
    (hE : E L S p.1 p'.1) {P : Pat} (hhead : P.head = some f) {σ : Binding}
    (hm : MatchN G P (mkNode st f p') σ) :
    MatchC G P (G.find (ι p)) σ := by
  rw [ac_equal_same_class_sub h hA hs hp hp' hE]
  exact MatchC.app (hs.nodes p' hp') rfl hhead hm

end SemperProofs.CC.Bridge
