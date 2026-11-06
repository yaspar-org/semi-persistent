import SemperProofs.EMatch.Engine.Saturate.Invariant
import SemperProofs.CC.Bridge.Modulo

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
  have hinv := (saturation_complete A₀ As hplan h₀ hok hemit₀ hchain hA hfix).2
  refine ⟨hinv rule hr σ hm, ?_⟩
  rw [hG] at hm ⊢
  rw [hatoms] at hm
  obtain ⟨q, hq, hroot', hcls, hmn⟩ := matches_at_active hhead hm
  rw [hroot] at hroot'
  obtain rfl : q = p' := nodeId_injective (Option.some.inj hroot').symm
  refine ⟨?_, matches_closed_under_theory hcomp hw hp hq hE hhead hmn⟩
  rw [hcls, ac_equal_same_class_graph hcomp hw f hp hq hE]

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
the tracked rules), nodes persist through the round (`Round.Persist`:
every node of `before` not subsumed has a node of `after` with the same
operator and canonicalised children; `recanonize_node`), nothing is
subsumed (`subsumed = ∅`: no `:subsume` rule fires), and every rule's
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
`needs_naive_match`; both branches are covered.

(d) Completion has converged (`CompleteHyps L S st`): the slot invariant
`I5` holds at an initial slot state and the refresh `OpsStar` leads to a
slot state the completion state agrees with; every class holding an
active node has an active node as right-hand side (`I0Active`; a leaf
constant, with no node, is unconstrained, and
`saturation_modulo_complete_atoms` reads it as its one-element monomial); the right-hand sides are clamped; the round is fixed
(`RoundFixed L st`, no rule to add, no critical pair left); the law
relation is `degLex`-decreasing, no clamped monomial rewrites by an axiom
rule, the critical pairs of the rules and axiom rules are joinable;
congruence holds on the active nodes (`hcc`: two active nodes with the
same monomial are in one class); every asserted equation of `S` is present between
active nodes of one class (`hS`); cancellation (`hcancel`, under
`L.cancellative`). `Enumerates st act` says `act` is the set of active
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
   existed before the round), so no `NoCollapse` hypothesis appears. -/
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
the conclusion is about the stored nodes `p`, `p'` of `act`. -/
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
