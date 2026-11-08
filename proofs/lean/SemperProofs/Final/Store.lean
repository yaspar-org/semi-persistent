import SemperProofs.Final.Main
import SemperProofs.Fidelity.StopTest

/-!
# The final theorem over the store, with normalized right-hand sides

`saturation_modulo_complete` reads the fixpoint snapshot as the graph
`represents st f act` and the right-hand sides literally (`Den`). The
represented graph has active `f`-multiset nodes only, so a rule with a
match whose right-hand side builds any other node (another operator, a
leaf constant, a one-element `(f x)`) makes its hypotheses contradictory.

Here the run is the store model of `Fidelity/` (`SActRoundN`): matches are
read on the index (`Store.index`, the store filtered by the skip
predicates), consequences on the store as the normal forms `add` builds
(`DenN`, `FiredN`), and `:subsume` is allowed. The completion state enters
only through the `f`-part of the index: the active nodes of `st` are
stored in the index under the ids `ι` (`SubRep`), and every other node is
unconstrained.

* `saturation_modulo_complete_store`: at the fixpoint, for a rule whose
  query is one pattern with head `f`, two theory-equal active nodes
  `p`, `p'` and a match rooted at `p'`'s node, the instance is fired in
  the store, its root class is `p`'s class, it matches the pattern at that
  class, and it matches at the represented node of `p'`.
* `saturation_modulo_complete_store_atoms`: the same with leaf constants
  (`CompleteAtoms`).
* `saturation_modulo_complete_store_engine`: the leaf-constant form at the
  round where the engine's stop test holds, in place of `Unchanged`.

`Final/Witness.lean` exhibits a run, a completion state with leaf
constants and a rule `(rewrite (+ x y) (g x y))` that meet every hypothesis
of `saturation_modulo_complete_store_atoms` together.
-/

namespace SemperProofs.Final

open Semper.EMatch Semper.EMatch.Fidelity SemperProofs.CC SemperProofs.CC.Bridge

variable {n : ℕ}

/-- **Saturation is complete modulo the AC theory, on the store.**

A run of store rounds with normalized right-hand sides (`SActRoundN`:
round 0 naive, then a chain of semi-naive rounds, `:subsume` allowed), a
round `A` that changed nothing, and a converged completion state `st`
whose active `f`-nodes `act` are stored in the index after `A` under the
ids `ι` (`SubRep A.Sa.index st f act ι`; the index may hold any other
node). For every rule whose query is one pattern `P` with head `f`, every
pair of active nodes `p`, `p'` with `E L S p.1 p'.1`, and every match `σ`
of the rule on the index rooted at the node of `p'`: the instance is fired
in the store (`FiredN`), the root class of `σ` is the class of `p`, `σ`
matches `P` at that class, and `σ` matches `P` at the represented node of
`p'`. -/
theorem saturation_modulo_complete_store {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st)
    (hw : Within st act) {f : Sym} {ι : Monomial n × Fin n → NodeId}
    (hs : SubRep A.Sa.index st f act ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.Sa.index rule.atoms σ → σ.node r = some (ι p') →
        FiredN A.Sa.graph ops σ rule ∧
        σ.cls r = some (A.Sa.find (ι p)) ∧
        MatchC A.Sa.index P (A.Sa.find (ι p)) σ ∧
        MatchN A.Sa.index P (mkNode st f p') σ := by
  intro rule hr P r hatoms hhead p hp p' hp' hE σ hm hroot
  have hinv := saturation_complete_N A₀ As hplan h₀ hok hemit₀ hchain hA hfix
  have hk : A.Sa.index.KeysNodup := by
    have := ((hok A hA).atoms rule hr).keys
    rwa [A.after_eq] at this
  refine ⟨hinv rule hr σ hm, ?_⟩
  rw [hatoms] at hm
  obtain ⟨hcls, hmn⟩ := matches_at_sub hs hk hhead hm hp' hroot
  refine ⟨?_, matches_closed_under_theory_sub hcomp hw hs hp hp' hE hhead hmn, hmn⟩
  rw [hcls, Store.index_find, ← Store.index_find, ac_equal_same_class_sub hcomp hw hs hp' hp
    (E.symm hE), Store.index_find]

/-- **Saturation is complete modulo the AC theory, on the store, with leaf
constants.** `saturation_modulo_complete_store` for a completion state with
leaf constants (`CompleteAtoms`, the hypotheses of
`completion_complete_atoms`); `act` is any set of stored active nodes. The
leaf constants and the nodes the right-hand sides build are nodes of the
store like any other. -/
theorem saturation_modulo_complete_store_atoms {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act : Finset (Monomial n × Fin n)} (hcomp : CompleteAtoms L S st X u)
    (hw : Within st act) {f : Sym} {ι : Monomial n × Fin n → NodeId}
    (hs : SubRep A.Sa.index st f act ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.Sa.index rule.atoms σ → σ.node r = some (ι p') →
        FiredN A.Sa.graph ops σ rule ∧
        σ.cls r = some (A.Sa.find (ι p)) ∧
        MatchC A.Sa.index P (A.Sa.find (ι p)) σ ∧
        MatchN A.Sa.index P (mkNode st f p') σ :=
  saturation_modulo_complete_store (st := st.withAtoms X u) A₀ As hplan h₀ hok hemit₀ hchain hA
    hfix (CompleteHyps.ofAtoms hcomp) (fun p hp => State.active_withAtoms (hw p hp))
    (hs.withAtoms X u)

/-- `saturation_modulo_complete_store_atoms` at the round where the
engine's stop test holds (no reported change, an unmoved size stamp) and
the round matched on a completion fixpoint (`EnginePhase.before_fixed`: the
previous rebuild converged), in place of `Unchanged`. -/
theorem saturation_modulo_complete_store_engine {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) {K : Completion} (Eng : EnginePhase K A.Sb A.Sa)
    (hstop : Eng.Stop)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act : Finset (Monomial n × Fin n)} (hcomp : CompleteAtoms L S st X u)
    (hw : Within st act) {f : Sym} {ι : Monomial n × Fin n → NodeId}
    (hs : SubRep A.Sa.index st f act ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.Sa.index rule.atoms σ → σ.node r = some (ι p') →
        FiredN A.Sa.graph ops σ rule ∧
        σ.cls r = some (A.Sa.find (ι p)) ∧
        MatchC A.Sa.index P (A.Sa.find (ι p)) σ ∧
        MatchN A.Sa.index P (mkNode st f p') σ :=
  saturation_modulo_complete_store_atoms A₀ As hplan h₀ hok hemit₀ hchain hA
    (engine_stop_unchanged_N A Eng hstop) hcomp hw hs

/-- With the `f`-part covering every `f`-node of the index (`FCover`), the
root may be any match: it is the node of some active `p'`. -/
theorem saturation_modulo_complete_store_cover {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act : Finset (Monomial n × Fin n)} (hcomp : CompleteAtoms L S st X u)
    (hw : Within st act) {f : Sym} {ι : Monomial n × Fin n → NodeId}
    (hs : SubRep A.Sa.index st f act ι) (hcov : FCover A.Sa.index f act ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ, Matches A.Sa.index rule.atoms σ →
        FiredN A.Sa.graph ops σ rule ∧
        ∃ p' ∈ act, σ.node r = some (ι p') ∧
          ∀ p ∈ act, E L S p.1 p'.1 →
            σ.cls r = some (A.Sa.find (ι p)) ∧ MatchC A.Sa.index P (A.Sa.find (ι p)) σ := by
  intro rule hr P r hatoms hhead σ hm
  have hm' := hm
  rw [hatoms] at hm'
  have hP : P.head.isSome = true := by rw [hhead]; rfl
  obtain ⟨id, nd, hid, hmem, -, hop, -⟩ :=
    backOk P hP r _ (fun a ha => hm'.sat _ (List.mem_map_of_mem ha))
  obtain ⟨p', hp', rfl⟩ := hcov id nd hmem (by rw [hhead] at hop; exact (Option.some.inj hop).symm)
  have hmain := saturation_modulo_complete_store_atoms A₀ As hplan h₀ hok hemit₀ hchain hA hfix
    hcomp hw hs rule hr P r hatoms hhead
  refine ⟨(hmain p' hp' p' hp' (E.refl _) σ hm hid).1, p', hp', hid, fun p hp hE => ?_⟩
  obtain ⟨-, h2, h3, -⟩ := hmain p hp p' hp' hE σ hm hid
  exact ⟨h2, h3⟩

end SemperProofs.Final
