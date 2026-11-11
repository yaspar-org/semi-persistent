import SemperProofs.Final.Main
import SemperProofs.Fidelity.StopTest
import SemperProofs.CC.AtomicOf

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
* `saturation_modulo_complete_store_cover`: with `FCover` (every `f`-node
  of the index is the node of an active `p`), for every match whatever its
  root. The engine keeps a collapsed node (`FLAG_AC_COLLAPSED`, retired in
  the model) in the index and matchable, so `FCover` fails on every run in
  which completion collapsed a node (`Final/Witness.lean`, `not_cover`).
* `saturation_modulo_complete_store_retired`: the correspondence extended
  to the retired nodes (`SubRepR`), `FCover` over active and retired nodes
  together, and for every match: the instance is fired, and the root's
  class is the class of an active node `q` of `st` whose monomial is
  `=_E`-equal to the matched node's, the retired node rewriting to it
  (`I3`, `node_reduces_active`) and the rewrite being sound (`I2`).

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
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
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
  have hinv := saturation_complete_N A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
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
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
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
  saturation_modulo_complete_store (st := st.withAtoms X u) A₀ As hmatch h₀ hok hemit₀ hchain hA
    hfix (CompleteHyps.ofAtoms hcomp) (fun p hp => State.active_withAtoms (hw p hp))
    (hs.withAtoms X u)

/-- `saturation_modulo_complete_store_atoms` with the atomic set the
engine's `atomic` bit defines (`atomicOf st`, `CC/AtomicOf.lean`) in place
of the parameter `X`. -/
theorem saturation_modulo_complete_store_atomic {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {u : Option (Fin n)} {act : Finset (Monomial n × Fin n)} (hcomp : CompleteAtomic L S st u)
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
  saturation_modulo_complete_store_atoms A₀ As hmatch h₀ hok hemit₀ hchain hA hfix hcomp hw hs

/-- `saturation_modulo_complete_store_atoms` at the round where the
engine's stop test holds (no reported change, an unmoved size stamp) and
the round matched on a completion fixpoint (`EnginePhase.before_fixed`: the
previous rebuild converged), in place of `Unchanged`. -/
theorem saturation_modulo_complete_store_engine {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
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
  saturation_modulo_complete_store_atoms A₀ As hmatch h₀ hok hemit₀ hchain hA
    (engine_stop_unchanged_N A Eng hstop) hcomp hw hs

/-- With the `f`-part covering every `f`-node of the index (`FCover`), the
root may be any match: it is the node of some active `p'`. -/
theorem saturation_modulo_complete_store_cover {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
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
  have hmain := saturation_modulo_complete_store_atoms A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
    hcomp hw hs rule hr P r hatoms hhead
  refine ⟨(hmain p' hp' p' hp' (E.refl _) σ hm hid).1, p', hp', hid, fun p hp hE => ?_⟩
  obtain ⟨-, h2, h3, -⟩ := hmain p hp p' hp' hE σ hm hid
  exact ⟨h2, h3⟩

/-- The retired-root theorem from any proof that each node of `ret` is
`=_E`-equal to an active node of its class (`heq`). -/
theorem saturation_modulo_complete_store_retired_of {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act ret : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st) (hw : Within st act)
    (heq : ∀ p ∈ ret, ∃ q ∈ st.active, E L S p.1 q.1 ∧ st.find q.2 = st.find p.2) {f : Sym}
    {ι : Monomial n × Fin n → NodeId} (hs : SubRepR A.Sa.index st f act ret ι)
    (hcov : FCover A.Sa.index f (act ∪ ret) ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ, Matches A.Sa.index rule.atoms σ →
        FiredN A.Sa.graph ops σ rule ∧
        ∃ p' ∈ act ∪ ret, σ.node r = some (ι p') ∧ MatchN A.Sa.index P (mkNode st f p') σ ∧
          ∃ q ∈ st.active, E L S p'.1 q.1 ∧ st.find q.2 = st.find p'.2 ∧
            σ.cls r = some (clsId (st.find q.2)) ∧
            MatchC A.Sa.index P (clsId (st.find q.2)) σ ∧
            ∀ p ∈ act, E L S p.1 p'.1 →
              σ.cls r = some (A.Sa.find (ι p)) ∧ MatchC A.Sa.index P (A.Sa.find (ι p)) σ := by
  intro rule hr P r hatoms hhead σ hm
  have hinv := saturation_complete_N A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
  have hk : A.Sa.index.KeysNodup := by
    have := ((hok A hA).atoms rule hr).keys
    rwa [A.after_eq] at this
  refine ⟨hinv rule hr σ hm, ?_⟩
  rw [hatoms] at hm
  have hP : P.head.isSome = true := by rw [hhead]; rfl
  obtain ⟨id, nd, hid, hmem, -, hop, -⟩ :=
    backOk P hP r _ (fun a ha => hm.sat _ (List.mem_map_of_mem ha))
  obtain ⟨p', hp', rfl⟩ := hcov id nd hmem (by rw [hhead] at hop; exact (Option.some.inj hop).symm)
  obtain ⟨hcls, hmn⟩ := matches_at_sub hs.union hk hhead hm hp' hid
  have hfind : A.Sa.index.find (ι p') = clsId (st.find p'.2) := hs.union.find p' hp'
  have hnode := hs.union.nodes p' hp'
  obtain ⟨q, hq, hE, hqc⟩ : ∃ q ∈ st.active, E L S p'.1 q.1 ∧ st.find q.2 = st.find p'.2 := by
    rcases Finset.mem_union.1 hp' with h | h
    · exact ⟨p', hw p' h, E.refl _, rfl⟩
    · exact heq p' h
  refine ⟨p', hp', hid, hmn, q, hq, hE, hqc, ?_, ?_, ?_⟩
  · rw [hcls, hfind, hqc]
  · rw [hqc, ← hfind]; exact MatchC.app hnode rfl hhead hmn
  · intro p hp hpE
    have hpq : st.find p.2 = st.find q.2 := ac_equal_same_class hcomp (hw p hp) hq (hpE.trans hE)
    have hfp : A.Sa.find (ι p) = clsId (st.find p.2) := hs.active.find p hp
    refine ⟨?_, ?_⟩
    · rw [hcls, hfind, hfp, hpq, hqc]
    · rw [hfp, hpq, hqc, ← hfind]; exact MatchC.app hnode rfl hhead hmn

/-- **Saturation is complete modulo the AC theory, on the store, at a
retired root.** The correspondence `SubRepR` stores the active nodes `act`
and the stored nodes `ret` (the retired ones) of the sound (`I2`) and
retirement-disciplined (`I3`) converged state `st` in the index, and
`FCover` over `act ∪ ret` makes every `f`-node of the index one of them. For
every match `σ` of a rule whose query is one pattern `P` with head `f`: the
instance is fired in the store, the root is the node of some `p'`, active or
retired, where `σ` matches `P`, and there is an active node `q` of `st`, in
`p'`'s class and `=_E`-equal to it (`p'` itself when active, a reduct of
`p'` by the rules when retired), whose class the root binds and at which
`P` matches at the class level. Every active `p ∈ act` `=_E`-equal to `p'`
gives the same class, read in the index as `A.Sa.find (ι p)`. -/
theorem saturation_modulo_complete_store_retired {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act ret : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st) (h2 : I2 L S st)
    (h3 : I3 L st) (hw : Within st act) (hret : Stored st ret) {f : Sym}
    {ι : Monomial n × Fin n → NodeId} (hs : SubRepR A.Sa.index st f act ret ι)
    (hcov : FCover A.Sa.index f (act ∪ ret) ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ, Matches A.Sa.index rule.atoms σ →
        FiredN A.Sa.graph ops σ rule ∧
        ∃ p' ∈ act ∪ ret, σ.node r = some (ι p') ∧ MatchN A.Sa.index P (mkNode st f p') σ ∧
          ∃ q ∈ st.active, E L S p'.1 q.1 ∧ st.find q.2 = st.find p'.2 ∧
            σ.cls r = some (clsId (st.find q.2)) ∧
            MatchC A.Sa.index P (clsId (st.find q.2)) σ ∧
            ∀ p ∈ act, E L S p.1 p'.1 →
              σ.cls r = some (A.Sa.find (ι p)) ∧ MatchC A.Sa.index P (A.Sa.find (ι p)) σ :=
  saturation_modulo_complete_store_retired_of A₀ As hmatch h₀ hok hemit₀ hchain hA hfix hcomp hw
    (fun p hp => node_equal_active h2 h3 (hret p hp)) hs hcov

/-- **`saturation_modulo_complete_store_retired` without `I3`.** A retired
root needs only an active node of its class `=_E`-equal to it, which
`RetiredCovered` and `I2` give (`node_equal_active_covered`); no reduction,
no confluence, no `hcancel`. `RetiredCovered` holds of every state reachable
from one with no retired node (`retiredCovered_of_reachable`). -/
theorem saturation_modulo_complete_store_retired_covered {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act ret : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st) (h2 : I2 L S st)
    (hrc : RetiredCovered st) (hw : Within st act) (hret : Stored st ret) {f : Sym}
    {ι : Monomial n × Fin n → NodeId} (hs : SubRepR A.Sa.index st f act ret ι)
    (hcov : FCover A.Sa.index f (act ∪ ret) ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ, Matches A.Sa.index rule.atoms σ →
        FiredN A.Sa.graph ops σ rule ∧
        ∃ p' ∈ act ∪ ret, σ.node r = some (ι p') ∧ MatchN A.Sa.index P (mkNode st f p') σ ∧
          ∃ q ∈ st.active, E L S p'.1 q.1 ∧ st.find q.2 = st.find p'.2 ∧
            σ.cls r = some (clsId (st.find q.2)) ∧
            MatchC A.Sa.index P (clsId (st.find q.2)) σ ∧
            ∀ p ∈ act, E L S p.1 p'.1 →
              σ.cls r = some (A.Sa.find (ι p)) ∧ MatchC A.Sa.index P (A.Sa.find (ι p)) σ :=
  saturation_modulo_complete_store_retired_of A₀ As hmatch h₀ hok hemit₀ hchain hA hfix hcomp hw
    (fun p hp => node_equal_active_covered h2 hrc (hret p hp)) hs hcov

/-- `saturation_modulo_complete_store_retired` for a completion state with
leaf constants. `I2` and `I3` are taken on the completion view
`st.withAtoms X u`: the view's rules include `M → {x}` for an atomic class,
so the stored `I3` lifts to it (`I3_withAtoms`), and `I2` on the view also
states that a stored node in an atom's class is `=_E`-equal to the
constant, which the stored state does not record. The active node `q` is an
active node of the view: a stored active node or an implicit node of a leaf
constant (`State.mem_active_withAtoms`). -/
theorem saturation_modulo_complete_store_retired_atoms {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act ret : Finset (Monomial n × Fin n)}
    (hcomp : CompleteAtoms L S st X u) (h2 : I2 L S (st.withAtoms X u))
    (h3 : I3 L (st.withAtoms X u)) (hw : Within st act) (hret : Stored st ret) {f : Sym}
    {ι : Monomial n × Fin n → NodeId} (hs : SubRepR A.Sa.index st f act ret ι)
    (hcov : FCover A.Sa.index f (act ∪ ret) ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ, Matches A.Sa.index rule.atoms σ →
        FiredN A.Sa.graph ops σ rule ∧
        ∃ p' ∈ act ∪ ret, σ.node r = some (ι p') ∧ MatchN A.Sa.index P (mkNode st f p') σ ∧
          ∃ q ∈ (st.withAtoms X u).active, E L S p'.1 q.1 ∧ st.find q.2 = st.find p'.2 ∧
            σ.cls r = some (clsId (st.find q.2)) ∧
            MatchC A.Sa.index P (clsId (st.find q.2)) σ ∧
            ∀ p ∈ act, E L S p.1 p'.1 →
              σ.cls r = some (A.Sa.find (ι p)) ∧ MatchC A.Sa.index P (A.Sa.find (ι p)) σ :=
  saturation_modulo_complete_store_retired A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
    (CompleteHyps.ofAtoms hcomp) h2 h3 (fun p hp => State.active_withAtoms (hw p hp))
    (fun p hp => Or.inl (hret p hp)) (hs.withAtoms X u) hcov

/-- **`saturation_modulo_complete_store_retired_atoms` without `I3`**:
`RetiredCovered` of the stored state, carried to the view
(`RetiredCovered.withAtoms`), and `I2` on the view. -/
theorem saturation_modulo_complete_store_retired_atoms_covered {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act ret : Finset (Monomial n × Fin n)}
    (hcomp : CompleteAtoms L S st X u) (h2 : I2 L S (st.withAtoms X u))
    (hrc : RetiredCovered st) (hw : Within st act) (hret : Stored st ret) {f : Sym}
    {ι : Monomial n × Fin n → NodeId} (hs : SubRepR A.Sa.index st f act ret ι)
    (hcov : FCover A.Sa.index f (act ∪ ret) ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ, Matches A.Sa.index rule.atoms σ →
        FiredN A.Sa.graph ops σ rule ∧
        ∃ p' ∈ act ∪ ret, σ.node r = some (ι p') ∧ MatchN A.Sa.index P (mkNode st f p') σ ∧
          ∃ q ∈ (st.withAtoms X u).active, E L S p'.1 q.1 ∧ st.find q.2 = st.find p'.2 ∧
            σ.cls r = some (clsId (st.find q.2)) ∧
            MatchC A.Sa.index P (clsId (st.find q.2)) σ ∧
            ∀ p ∈ act, E L S p.1 p'.1 →
              σ.cls r = some (A.Sa.find (ι p)) ∧ MatchC A.Sa.index P (A.Sa.find (ι p)) σ :=
  saturation_modulo_complete_store_retired_covered A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
    (CompleteHyps.ofAtoms hcomp) h2 (RetiredCovered.withAtoms hrc X u) (fun p hp => State.active_withAtoms (hw p hp))
    (fun p hp => Or.inl (hret p hp)) (hs.withAtoms X u) hcov

end SemperProofs.Final
