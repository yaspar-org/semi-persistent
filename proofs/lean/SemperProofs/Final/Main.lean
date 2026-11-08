import SemperProofs.EMatch.Engine.Saturate.Invariant
import SemperProofs.CC.Bridge.Sub

/-!
# The final theorem: saturation is complete modulo the AC theory

Composes the fixpoint theorem of the saturation loop
(`saturation_complete`: at a round that changed nothing every match of
every rule is fired) with the bridge to AC completion
(`matches_closed_under_theory`: on the graph of a converged completion
state, a match at a node is a match at the class of every node
`=_E`-equal to it).

* `matches_at_active`: a binding satisfying the atoms of a pattern on the
  represented graph binds the root to the node of some active `p'`, binds
  the root's class to that node's class and matches the pattern there.
* `saturation_modulo_complete`: at the fixpoint, for a rule whose pattern
  has head `f` and two theory-equal active nodes `p`, `p'`, every binding
  matching the rule at the node of `p'` is fired, and its root class is
  the class of `p`.
* `saturation_modulo_sound`: every binding the naive run of a rule's plan
  emits (what the loop fires on) is a match, at the node of some active
  `p'`, and a class-level match for every active `p` theory-equal to `p'`.
* `saturation_modulo_complete_sub`: the completeness statement on any
  after snapshot that holds the represented graph as a part (`SubRep`),
  so that other operators, leaf constants and the nodes the right-hand
  sides build may be stored; `saturation_modulo_complete_within` is its
  case `A.R.after = represents st f act`.

With `A.R.after = represents st f act` and literal right-hand sides
(`Den`), `saturation_modulo_complete` and `saturation_modulo_complete_atoms`
hold vacuously for a rule set with a match whose right-hand side builds
any node other than an active `f`-multiset node: `saturation_complete`
derives `Fired` for it, and the represented graph has no such node. The
statement over the store with normalized right-hand sides is
`saturation_modulo_complete_store_atoms` (`Final/Store.lean`), and
`Final/Witness.lean` exhibits a run that meets all of its hypotheses.
-/

namespace SemperProofs.Final

open Semper.EMatch SemperProofs.CC SemperProofs.CC.Bridge

variable {n : ℕ}

/-- A binding satisfying every atom of `atoms P r` on the represented graph
binds `r` to the node of some active `p'`, binds `r`'s class to that
node's class, and matches `P` at that node (the reconstruction `backOk`,
read on `represents`). -/
theorem matches_at_active {st : State n} {f : Sym} {act : Finset (Monomial n × Fin n)}
    {P : Pat} {r : Var} (hhead : P.head = some f) {σ : Binding}
    (hm : Matches (represents st f act) ((atoms P r).map QAtom.scan) σ) :
    ∃ p' ∈ act, σ.node r = some (nodeId p') ∧
      σ.cls r = some ((represents st f act).find (nodeId p')) ∧
      MatchN (represents st f act) P (mkNode st f p') σ := by
  have hP : P.head.isSome = true := by rw [hhead]; rfl
  have hall : ∀ a ∈ (atomsAt P r (P.freshAbove r)).1, AtomSat (represents st f act) σ a :=
    fun a ha => hm.sat _ (List.mem_map_of_mem ha)
  obtain ⟨id, nd, hid, hmem, hcls, -, hmn⟩ := backOk P hP r _ hall
  obtain ⟨p', hp', rfl, rfl⟩ := mem_represents.1 hmem
  exact ⟨p', hp', hid, hcls, hmn⟩

/-- A binding satisfying the atoms of a pattern with head `f` on any graph
the represented graph is a part of, rooted at the id `ι p'` of an active
node, binds the root's class to that node's class and matches the pattern
at the represented node. -/
theorem matches_at_sub {G : Graph} {st : State n} {f : Sym} {act : Finset (Monomial n × Fin n)}
    {ι : Monomial n × Fin n → NodeId} (hs : SubRep G st f act ι) (hk : G.KeysNodup)
    {P : Pat} {r : Var} (hhead : P.head = some f) {σ : Binding}
    (hm : Matches G ((atoms P r).map QAtom.scan) σ) {p' : Monomial n × Fin n} (hp' : p' ∈ act)
    (hroot : σ.node r = some (ι p')) :
    σ.cls r = some (G.find (ι p')) ∧ MatchN G P (mkNode st f p') σ := by
  have hP : P.head.isSome = true := by rw [hhead]; rfl
  have hall : ∀ a ∈ (atomsAt P r (P.freshAbove r)).1, AtomSat G σ a :=
    fun a ha => hm.sat _ (List.mem_map_of_mem ha)
  obtain ⟨id, nd, hid, hmem, hcls, -, hmn⟩ := backOk P hP r _ hall
  rw [hroot] at hid
  obtain rfl := Option.some.inj hid
  obtain rfl := hs.node_eq hk hp' hmem
  exact ⟨hcls, hmn⟩

/-- **Saturation is complete modulo the AC theory, on a graph holding the
represented graph as a part.** `saturation_modulo_complete` with the
after snapshot any graph that holds the active `f`-nodes of `st` under the
ids `ι` (`SubRep`), so that leaf constants, other operators and the nodes
the right-hand sides build may be stored. The conclusion adds that the
matched node is the represented node of `p'`. Literal right-hand sides
(`Den`); `Fidelity` / `Final/Store.lean` has the normalized ones. -/
theorem saturation_modulo_complete_sub {sig : Sym → Kind} {naive : Rule → Bool}
    {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st)
    (hw : Within st act) {f : Sym} {ι : Monomial n × Fin n → NodeId}
    (hs : SubRep A.R.after st f act ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.R.after rule.atoms σ → σ.node r = some (ι p') →
        Fired A.R.after σ rule ∧
        σ.cls r = some (A.R.after.find (ι p)) ∧
        MatchC A.R.after P (A.R.after.find (ι p)) σ ∧
        MatchN A.R.after P (mkNode st f p') σ := by
  intro rule hr P r hatoms hhead p hp p' hp' hE σ hm hroot
  have hinv := (saturation_complete A₀ As hplan h₀ hok hemit₀ hchain hA hfix).2
  have hk : A.R.after.KeysNodup := ((hok A hA).atoms rule hr).keys
  refine ⟨hinv rule hr σ hm, ?_⟩
  rw [hatoms] at hm
  obtain ⟨hcls, hmn⟩ := matches_at_sub hs hk hhead hm hp' hroot
  refine ⟨?_, matches_closed_under_theory_sub hcomp hw hs hp hp' hE hhead hmn, hmn⟩
  rw [hcls, ac_equal_same_class_sub hcomp hw hs hp' hp (E.symm hE)]

/-- `saturation_modulo_complete` with `act` within the active nodes
(`Within`) instead of enumerating them; the form the leaf-constant
statement instantiates. -/
theorem saturation_modulo_complete_within {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st)
    (hw : Within st act) {f : Sym} (hG : A.R.after = represents st f act) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.R.after rule.atoms σ → σ.node r = some (nodeId p') →
        Fired A.R.after σ rule ∧
        σ.cls r = some (A.R.after.find (nodeId p)) ∧
        MatchC A.R.after P (A.R.after.find (nodeId p)) σ := by
  intro rule hr P r hatoms hhead p hp p' hp' hE σ hm hroot
  have hs : SubRep A.R.after st f act nodeId := hG ▸ represents_subRep st f act
  obtain ⟨h1, h2, h3, -⟩ := saturation_modulo_complete_sub A₀ As hplan h₀ hok hemit₀ hchain hA
    hfix hcomp hw hs rule hr P r hatoms hhead p hp p' hp' hE σ hm hroot
  exact ⟨h1, h2, h3⟩

/-- **Saturation is complete modulo the AC theory.**

Setting. A run of the saturation loop is a first round `A₀` (every rule
naive on the frozen snapshot) followed by a chain `As` of semi-naive rounds
(`AChain`); each round `A` matches on the snapshot `A.R.before`, applies
its actions, and the next snapshot is `A.R.after`. The round `A` of the
run is the fixpoint: it changed nothing (`A.R.Unchanged`), so its after
snapshot `G = A.R.after` is where the loop stops. `G` is the e-matching
graph of the operator `f` read from a completion state `st` that has
converged (`hG : A.R.after = represents st f act`, `act` enumerating the
active nodes of `st`).

Hypotheses, in engine terms.

(a) Round facts that rebuild establishes, per round (`RoundOK`): the
round is well formed (`Round.WF`: the snapshots are well-formed graphs,
the merge record splits no class, the added ids are the new nodes),
`track_merge_members` is on (`tracking = true`, needed by the delta of
the tracked rules), the fixed-arity nodes persist through the round
(`Round.PersistFixed`: every tuple, pair or sequence node of `before` not
subsumed has a node of `after` with the same operator and canonicalised
children; `recanonize_node`), nothing is subsumed (`subsumed = ∅`: no
`:subsume` rule fires), and every rule's
atoms are well formed on each snapshot (`RulesWF`: distinct keys, nodes
conform to the kind signature, atoms well kinded, node variables
distinct, rest variables linear).

(b) The scheduler: every rule's annotated plan is a scheduled plan of its
atoms (`PlansOK`, the grammar `SchedA`), and the rule's atoms are the
flattening of its pattern `P` at the root node variable `r`
(`rule.atoms = (atoms P r).map QAtom.scan`) with `P.head = some f`.

(c) Emission: round 0 applies every binding of the naive run of every
rule (`EmitsAll`); a later round applies, for a rule routed naive, every
binding of the naive run on the frozen snapshot, and for a tracked rule,
every binding of every variant reading the previous round's delta
(`EmitsRound`, inside `AChain`). `naive : Rule → Bool` is the routing
`needs_naive_match`, widened to the rules that build an n-ary term after a
round whose rebuild did not persist every node literally (`route`, the
engine's `respelled`); both branches are covered.

(d) Completion has converged (`CompleteHyps L S st`): the slot invariant
`I5` holds at an initial slot state and the refresh `OpsStar` leads to a
slot state the completion state agrees with; every class holding an
active node has an active node as right-hand side (`I0Active`; a leaf
constant, with no node, is unconstrained, and
`saturation_modulo_complete_atoms` reads it as its one-element monomial); the right-hand sides are clamped; the round is fixed
(`RoundFixed L st`: every normal form present, no rule's left-hand side
reducible by another rule, every critical pair of two overlapping,
non-containing rules joinable); the law relation is `degLex`-decreasing,
no clamped monomial rewrites by an axiom rule, the critical pairs that
involve an axiom rule are joinable (`AxiomCP`; the rule-rule pairs follow
from the fixed round, `hcp_of_fixed`);
congruence holds on the active nodes (`hcc`: two active nodes with the
same monomial are in one class); every asserted equation of `S` is present between
active nodes of one class (`hS`); for a cancellative operator, lattice
closure (`hlat`: two active nodes whose vectors differ by a member of the
state's lattice are in one class, what `lattice_round` establishes at its
fixpoint; `hcancel_not_derivable` shows the engine does not establish the
former hypothesis `hcancel`). `Enumerates st act` says `act` is the set of active
nodes.

(e) The fixpoint: `A.R.Unchanged` (same nodes, same `find` before and
after the round: the loop's `changes == 0`).

Conclusion. For every rule, every pair of active nodes `p`, `p'` with
`E L S p.1 p'.1` (theory-equal monomials under the laws `L` and the
asserted equations `S`), and every binding `σ` that matches the rule's
atoms in `G` at the node of `p'` (`σ.node r = some (nodeId p')`): the
instance `(rule, σ)` is fired in `G` (every `insert` consequence is a
present node, every `union` consequence a merged pair, `Fired`), the root
class of `σ` is the class of `p` (`σ.cls r = some (G.find (nodeId p))`)
and `σ` matches `P` at that class. So the instances fired at a class
cover every theory-equal node of the class: at the fixpoint a rule has
fired on every instance modulo the theory.

Known limits.
1. A term theory-equal to a present node but absent from the graph (no
   active node spells its flat form) has no node and is matched through
   the class only: the root binds the class, which is the class of every
   present theory-equal term. The per-node form (a binding at `p` yields
   one at `p'`) is false: `per_node_form_fails`.
2. Maximum-partition semantics for AC/ACI matching (`MatchN.ac`: a
   pattern element takes a child class with its full multiplicity) is a
   semantics choice; a merge of two children of one node can lose a match
   (`Round.NoCollapse`). The fixpoint theorem does not need the transport
   of matches across such a merge (it case-splits on whether a match
   existed before the round), so no `NoCollapse` hypothesis appears.
3. The hypotheses are contradictory for a rule with a match whose
   right-hand side builds a node other than an active `f`-multiset node of
   `act` (another operator, a leaf constant, a one-element `(f x)`):
   `Fired` asks for it in `represents st f act`, which has no such node.
   `saturation_modulo_complete_store_atoms` (`Final/Store.lean`) is the
   statement without this restriction. -/
theorem saturation_modulo_complete {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st)
    (henum : Enumerates st act) {f : Sym} (hG : A.R.after = represents st f act) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.R.after rule.atoms σ → σ.node r = some (nodeId p') →
        Fired A.R.after σ rule ∧
        σ.cls r = some (A.R.after.find (nodeId p)) ∧
        MatchC A.R.after P (A.R.after.find (nodeId p)) σ :=
  saturation_modulo_complete_within A₀ As hplan h₀ hok hemit₀ hchain hA hfix hcomp henum.within hG

/-- **Saturation is complete modulo the AC theory, with leaf constants.**
`saturation_modulo_complete` for a completion state whose atomic classes
`X` (the leaf constants among them) are read as their one-element monomials
and whose unit class `u`, if any, as the empty monomial (`State.withAtoms`,
`CC/Atoms.lean`): the hypotheses are those of
`completion_complete_atoms` (`CompleteAtoms`), `act` enumerates the stored
active nodes and the graph is the one of the stored nodes. The asserted
equations `S` and the theory may relate a node to a constant (`a + b = c`);
the conclusion is about the stored nodes `p`, `p'` of `act`. The graph has
no node for a leaf constant, so the vacuity of `saturation_modulo_complete`
(limit 3) holds here too, and a right-hand side naming a leaf constant
also makes the hypotheses contradictory; see
`saturation_modulo_complete_store_atoms`. -/
theorem saturation_modulo_complete_atoms {sig : Sym → Kind} {naive : Rule → Bool}
    {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act : Finset (Monomial n × Fin n)} (hcomp : CompleteAtoms L S st X u)
    (henum : Enumerates st act) {f : Sym} (hG : A.R.after = represents st f act) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.R.after rule.atoms σ → σ.node r = some (nodeId p') →
        Fired A.R.after σ rule ∧
        σ.cls r = some (A.R.after.find (nodeId p)) ∧
        MatchC A.R.after P (A.R.after.find (nodeId p)) σ :=
  saturation_modulo_complete_within (st := st.withAtoms X u) A₀ As hplan h₀ hok hemit₀ hchain hA
    hfix (CompleteHyps.ofAtoms hcomp) (henum.within_withAtoms X u) hG

/-- **Soundness modulo the theory, matching side.**

Every binding the naive run of a rule's plan emits on the represented
graph `G` (the bindings the loop fires on, `EmitsAll` / `EmitsRound`) is
a match of the rule's atoms, binds the root `r` to the node of some
active `p'`, binds its class to `find p'`, matches `P` at that node, and
is a class-level match for every active `p` theory-equal to `p'`.

Soundness of the *actions* (every node or merge present after a round
came from a fired instance or from completion) is not in the model: an
`ActRound` records what the emitted bindings' actions produced
(`inserts`, `unions`, `subsumes`) and `Fired` asks only that a
consequence is present, which a hash-cons hit or a completion-minted
node can also account for. Only the matching side is stated. -/
theorem saturation_modulo_sound {sig : Sym → Kind} {rules : List Rule}
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st)
    (henum : Enumerates st act) {f : Sym} {G : Graph} (hG : G = represents st f act)
    (hwf : RulesWF sig G rules) (hplan : PlansOK rules) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ ∈ runNaive G rule.plan,
        Matches G rule.atoms σ ∧
        ∃ p' ∈ act, σ.node r = some (nodeId p') ∧
          σ.cls r = some (G.find (nodeId p')) ∧
          MatchN G P (mkNode st f p') σ ∧
          ∀ p ∈ act, E L S p.1 p'.1 → MatchC G P (G.find (nodeId p)) σ := by
  subst hG
  intro rule hr P r hatoms hhead σ hσ
  have hm : Matches _ rule.atoms σ := (mem_runNaive_iff (hwf rule hr) (hplan rule hr) σ).1 hσ
  refine ⟨hm, ?_⟩
  rw [hatoms] at hm
  obtain ⟨p', hp', hroot, hcls, hmn⟩ := matches_at_active hhead hm
  exact ⟨p', hp', hroot, hcls, hmn,
    fun p hp hE => matches_closed_under_theory hcomp henum.within hp hp' hE hhead hmn⟩

end SemperProofs.Final
