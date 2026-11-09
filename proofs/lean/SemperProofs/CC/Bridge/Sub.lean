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

The engine keeps a collapsed node (`FLAG_AC_COLLAPSED`, retired in the
model) in the index and matchable. `SubRepR G st f A R ι` extends the
correspondence to a set `R` of stored nodes, the retired ones: they too
sit in `G` under `ι`, with the children of `mkNode` and the class of
`st`. A match rooted at a retired node is read at the class of an active
node the retired one rewrites to, which `I3` provides
(`node_reduces_active`).

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

/-! ## Retired nodes -/

/-- Every node of `R` is a stored node of the state, active or retired. -/
def Stored (st : State n) (R : Finset (Monomial n × Fin n)) : Prop :=
  ∀ p ∈ R, p ∈ st.nodes

/-- The graph of `f` read from `st` is a part of `G`, with the active nodes
`A` and the retired nodes `R` both stored under `ι`. -/
structure SubRepR (G : Graph) (st : State n) (f : Sym) (A R : Finset (Monomial n × Fin n))
    (ι : Monomial n × Fin n → NodeId) : Prop where
  active : SubRep G st f A ι
  retired : SubRep G st f R ι

/-- Both parts together are a `SubRep` of their union. -/
theorem SubRepR.union {G : Graph} {st : State n} {f : Sym} {A R : Finset (Monomial n × Fin n)}
    {ι : Monomial n × Fin n → NodeId} (h : SubRepR G st f A R ι) : SubRep G st f (A ∪ R) ι :=
  ⟨fun p hp => (Finset.mem_union.1 hp).elim (h.active.nodes p) (h.retired.nodes p),
   fun p hp => (Finset.mem_union.1 hp).elim (h.active.find p) (h.retired.find p)⟩

/-- The completion view reads the same nodes and classes. -/
theorem SubRepR.withAtoms {G : Graph} {st : State n} {f : Sym}
    {A R : Finset (Monomial n × Fin n)} {ι : Monomial n × Fin n → NodeId}
    (h : SubRepR G st f A R ι) (X : Set (Fin n)) (u : Option (Fin n)) :
    SubRepR G (st.withAtoms X u) f A R ι :=
  ⟨h.active.withAtoms X u, h.retired.withAtoms X u⟩

/-- Every stored node rewrites to an active node of its class: an active
node is its own reduct, and a retired node rewrites to a node of its
class (`I3`), smaller under `≫`, so well-founded induction on `→_R`
(`Rw_wf`) reaches an active one. -/
theorem node_reduces_active {L : Laws n} {st : State n} (h3 : I3 L st) :
    ∀ M c, (M, c) ∈ st.nodes →
      ∃ M' c', Relation.ReflTransGen (Rw L st.rules) M M' ∧ (M', c') ∈ st.active ∧
        st.find c' = st.find c := by
  have hwf := (Rw_wf (L := L) (R := st.rules) (rules_oriented st)).transGen
  intro M
  induction M using hwf.induction with
  | _ M ih =>
    intro c hM
    by_cases hr : (M, c) ∈ st.retired
    · obtain ⟨M', c', hMM', hM', hc'⟩ := h3 M c hr
      obtain ⟨M'', c'', h₁, h₂, h₃⟩ := ih M' (Relation.transGen_swap.2 hMM') c' hM'
      exact ⟨M'', c'', hMM'.to_reflTransGen.trans h₁, h₂, h₃.trans hc'⟩
    · exact ⟨M, c, Relation.ReflTransGen.refl, ⟨hM, hr⟩, rfl⟩

/-- On a sound state (`I2`), a stored node is `=_E`-equal to an active node
of its class. -/
theorem node_equal_active {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h2 : I2 L S st) (h3 : I3 L st) {M : Monomial n} {c : Fin n} (hM : (M, c) ∈ st.nodes) :
    ∃ q ∈ st.active, E L S M q.1 ∧ st.find q.2 = st.find c := by
  obtain ⟨M', c', hrw, hact, hc⟩ := node_reduces_active h3 M c hM
  exact ⟨(M', c'), hact, Rw_rtg_sound (rules_sound h2) hrw, hc⟩

end SemperProofs.CC.Bridge
