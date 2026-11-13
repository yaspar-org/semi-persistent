import SemperProofs.CC.Bridge.Modulo
import SemperProofs.CC.Reactivate

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
node `=_E`-equal to it, which `RetiredCovered` and `I2` provide
(`node_equal_active_covered`, `CC/Lemmas.lean`).

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

/-- Every stored node reduces to an active node of its class: an active
node is its own reduct, and a retired node reduces, by the rules and the
laws, to a node of its class (`I3`), smaller under `≫`, so well-founded
induction on the step relation (`RwL_wf`) reaches an active one. -/
theorem node_reduces_active {L : Laws n} {st : State n} (h3 : I3 L st) :
    ∀ M c, (M, c) ∈ st.nodes →
      ∃ M' c', Relation.ReflTransGen (st.RwL L) M M' ∧ (M', c') ∈ st.active ∧
        st.find c' = st.find c := by
  have hwf := (RwL_wf L st).transGen
  intro M
  induction M using hwf.induction with
  | _ M ih =>
    intro c hM
    by_cases hr : (M, c) ∈ st.retired
    · obtain ⟨M', c', hMM', hM', hc'⟩ := h3 M c hr
      obtain ⟨M'', c'', h₁, h₂, h₃⟩ := ih M' (Relation.transGen_swap.2 hMM') c' hM'
      exact ⟨M'', c'', hMM'.to_reflTransGen.trans h₁, h₂, h₃.trans hc'⟩
    · exact ⟨M, c, Relation.ReflTransGen.refl, ⟨hM, hr⟩, rfl⟩

/-! ## `I3` from the reactivation pass -/

/-- **`I3` from the reactivation pass, on the packaged hypotheses.** At a
converged state (`CompleteHyps`) that is sound (`I2`), that the
reactivation pass leaves unchanged (`hreact`: the engine's state when the
completion loop reports a fixpoint, `reactivate_idem`) and whose retired
nodes are stored nodes of classes holding an active node (`hcov`), every
retired node reduces to a node of its class. `hcancel` is the hypothesis of
`completion_complete_at_convergence`: joinability cancels a common summand
when the operator is cancellative, and it is vacuous otherwise. For a
cancellative operator `CompleteHyps` goes through lattice closure and does
not give it (`Lattice.hcancel_not_derivable`), nor the critical pairs
involving a law instance (`CompleteHyps.hcp_ax` is required for a
non-cancellative operator only), which `hax` supplies. -/
theorem I3_of_reactivate_fixed_complete {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} (hcomp : CompleteHyps L S st) (h2 : I2 L S st)
    (hreact : st.reactivate L = st) (hcov : RetiredCovered st)
    (hax : L.cancellative → AxiomCP L st.rules)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N) : I3 L st := by
  obtain ⟨ss₀, ss, h5₀, hrun, ha⟩ := hcomp.slots
  have h5 : I5 st := SlotState.state_I5_of_slot (SlotState.reachable_I5 h5₀ hrun) ha
  have hax' : AxiomCP L st.rules := by
    by_cases hc : L.cancellative
    · exact hax hc
    · exact hcomp.hcp_ax hc
  exact I3_of_reactivate_fixed hreact hcov h2 hcomp.h0 h5 hcomp.hcanon hcomp.hfix hcomp.hlaw
    hcomp.hnf_ax (hcp_of_fixed hcomp.hfix hax') hcomp.hS hcancel

/-- `node_reduces_active` with `I3` derived from the reactivation pass. -/
theorem node_reduces_active_reactivate {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} (hcomp : CompleteHyps L S st) (h2 : I2 L S st)
    (hreact : st.reactivate L = st) (hcov : RetiredCovered st)
    (hax : L.cancellative → AxiomCP L st.rules)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N) :
    ∀ M c, (M, c) ∈ st.nodes →
      ∃ M' c', Relation.ReflTransGen (st.RwL L) M M' ∧ (M', c') ∈ st.active ∧
        st.find c' = st.find c :=
  node_reduces_active (I3_of_reactivate_fixed_complete hcomp h2 hreact hcov hax hcancel)

end SemperProofs.CC.Bridge
