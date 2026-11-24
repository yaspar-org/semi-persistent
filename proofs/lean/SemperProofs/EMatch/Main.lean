import SemperProofs.EMatch.Lemmas
import SemperProofs.EMatch.Proofs.JoinCommA
import SemperProofs.EMatch.Proofs.DecomposeAC
import SemperProofs.EMatch.Proofs.CompileWF
import SemperProofs.EMatch.Proofs.Interp

/-!
# E-matching: final theorems

Re-exports the proved lemmas of `Proofs/` under the names of the lemma
list in `notes-ematch-proof.md`, part (h). Every theorem here is a
one-line application of its primed proof; the statements are the corrected
ones (see the pointer comments in `Lemmas.lean`).

The two headline theorems are `ematch_sound` and `ematch_complete`: the
reference interpreter, run on the reference compiler's left-to-right plan
for a pattern, emits exactly the bindings of the maximum-partition
matching relation `MatchN` at a stored node.
-/

namespace Semper.EMatch

/-- Lemma 3: the candidate set of a join is exactly the identified nodes
that satisfy every lookup's predicate. -/
theorem join_complete (G : Graph) (σ : Binding) (ls : List Lookup) (id : NodeId) :
    id ∈ candidates G σ ls ↔
      (∃ n, (id, n) ∈ G.nodes) ∧ ∀ l ∈ ls, l.pred G σ id :=
  join_complete' G σ ls id

/-- Lemma 7: a commutative pair is matched in one of the two orders. -/
theorem decompose_comm_sound (x y : Var) (a b : C) (σ σ' : Binding)
    (h : σ' ∈ decomposeComm x y a b σ) :
    Binding.Extends σ σ' ∧
      ((σ'.cls x = some a ∧ σ'.cls y = some b) ∨
        (σ'.cls x = some b ∧ σ'.cls y = some a)) :=
  decompose_comm_sound' x y a b σ σ' h

/-- Lemma 7: both orders of a commutative pair are enumerated. -/
theorem decompose_comm_complete (x y : Var) (a b : C) (σ σ' : Binding)
    (hext : Binding.Extends σ σ')
    (h : (σ'.cls x = some a ∧ σ'.cls y = some b) ∨
      (σ'.cls x = some b ∧ σ'.cls y = some a)) :
    ∃ σ'' ∈ decomposeComm x y a b σ, Binding.Extends σ'' σ' :=
  decompose_comm_complete' x y a b σ σ' hext h

/-- Lemma 7: every split the associative expansion emits is a split of the
children into prefix, fixed middle and suffix, with the rest variables
bound to the two sides. Hypotheses: the rest variables are unbound on
entry and distinct, as the compiler guarantees. -/
theorem expand_a_sound (pre suf : Option Var) (elems : List Var) (cs : List C)
    (σ σ' : Binding)
    (hpre₀ : ∀ r, pre = some r → σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (h : σ' ∈ expandA pre elems suf cs σ) :
    Binding.Extends σ σ' ∧
      ∃ u mid v : List C, cs = u ++ mid ++ v ∧ mid.length = elems.length ∧
        SeqRestOk σ' pre u ∧ SeqRestOk σ' suf v ∧
        ∀ ec ∈ elems.zip mid, σ'.cls ec.1 = some ec.2 :=
  expand_a_sound' pre suf elems cs σ σ' hpre₀ hsuf₀ hdist h

/-- Lemma 7: every split of the children consistent with the rest
variables is enumerated by the associative expansion. -/
theorem expand_a_complete (pre suf : Option Var) (elems : List Var)
    (u mid v : List C) (σ σ' : Binding)
    (hext : Binding.Extends σ σ')
    (hlen : mid.length = elems.length)
    (hpre : SeqRestOk σ' pre u) (hsuf : SeqRestOk σ' suf v)
    (hcls : ∀ ec ∈ elems.zip mid, σ'.cls ec.1 = some ec.2) :
    ∃ σ'' ∈ expandA pre elems suf (u ++ mid ++ v) σ,
      Binding.Extends σ'' σ' :=
  expand_a_complete' pre suf elems u mid v σ σ' hext hlen hpre hsuf hcls

/-- Lemma 5: every binding the AC decomposition emits is an injection from
the element patterns to distinct children taking their whole counts, with
the rest bound to the untaken children. Hypothesis: the rest variable is
unbound on entry. -/
theorem decompose_ac_sound (elems : List (Var × Mult)) (rest : Option Var)
    (m : Multiset C) (σ σ' : Binding)
    (hfresh : ∀ r ∈ rest, σ.rest r = none)
    (h : σ' ∈ decomposeAC elems rest (Multiset.entries m) σ) :
    Binding.Extends σ σ' ∧
      ∃ taken : List C, taken.Nodup ∧ elems.length = taken.length ∧
        (∀ c ∈ taken, c ∈ m) ∧
        (∀ et ∈ elems.zip taken, σ'.cls et.1.1 = some et.2) ∧
        (∀ et ∈ elems.zip taken, MultOk σ' et.1.2 (m.count et.2)) ∧
        MsetRestOk σ' rest m taken :=
  decompose_ac_sound' elems rest m σ σ' hfresh h

/-- Lemma 6: every injection satisfying the AC clause is enumerated by the
decomposition. -/
theorem decompose_ac_complete (elems : List (Var × Mult)) (rest : Option Var)
    (m : Multiset C) (σ σ' : Binding) (taken : List C)
    (hext : Binding.Extends σ σ')
    (hnd : taken.Nodup) (hlen : elems.length = taken.length)
    (hmem : ∀ c ∈ taken, c ∈ m)
    (hcls : ∀ et ∈ elems.zip taken, σ'.cls et.1.1 = some et.2)
    (hmult : ∀ et ∈ elems.zip taken, MultOk σ' et.1.2 (m.count et.2))
    (hrest : MsetRestOk σ' rest m taken) :
    ∃ σ'' ∈ decomposeAC elems rest (Multiset.entries m) σ,
      Binding.Extends σ'' σ' :=
  decompose_ac_complete' elems rest m σ σ' taken hext hnd hlen hmem hcls hmult hrest

/-- Lemma 7: the set analogue of `decompose_ac_sound`. -/
theorem decompose_aci_sound (elems : List Var) (rest : Option Var)
    (s : Finset C) (σ σ' : Binding)
    (hfresh : ∀ r ∈ rest, σ.finRest r = none)
    (h : σ' ∈ decomposeACI elems rest (s.sort (· ≤ ·)) σ) :
    Binding.Extends σ σ' ∧
      ∃ taken : List C, taken.Nodup ∧ elems.length = taken.length ∧
        (∀ c ∈ taken, c ∈ s) ∧
        (∀ et ∈ elems.zip taken, σ'.cls et.1 = some et.2) ∧
        SetRestOk σ' rest s taken :=
  decompose_aci_sound' elems rest s σ σ' hfresh h

/-- Lemma 7: the set analogue of `decompose_ac_complete`. -/
theorem decompose_aci_complete (elems : List Var) (rest : Option Var)
    (s : Finset C) (σ σ' : Binding) (taken : List C)
    (hext : Binding.Extends σ σ')
    (hnd : taken.Nodup) (hlen : elems.length = taken.length)
    (hmem : ∀ c ∈ taken, c ∈ s)
    (hcls : ∀ et ∈ elems.zip taken, σ'.cls et.1 = some et.2)
    (hrest : SetRestOk σ' rest s taken) :
    ∃ σ'' ∈ decomposeACI elems rest (s.sort (· ≤ ·)) σ,
      Binding.Extends σ'' σ' :=
  decompose_aci_complete' elems rest s σ σ' taken hext hnd hlen hmem hcls hrest

/-- Lemma 10: the compiler's plan binds every variable before a step reads
it. -/
theorem compile_wf (P : Pat) (fresh : Nat) (hf : ∀ x ∈ P.vars, x < fresh) :
    PlanWF [] (compile P fresh) :=
  compile_wf' P fresh hf

/-- Soundness of e-matching (lemma 11). Every binding the interpreter emits
for the compiled plan of an application pattern `P` satisfies the
maximum-partition relation `MatchN` at a stored node, the one bound to the
root node variable `fresh`. Hypotheses, in engine terms: node ids are
distinct (`hkeys`); every node's children have the shape of its operator's
kind and the pattern uses the constructor of its head's kind (`hconf`,
`hwk`: the engine keys `by_op` per operator with one fixed shape); the
pattern's rest variables are distinct (`hnd`: a rest variable is bound
once); the pattern's variables lie below the fresh counter. -/
theorem ematch_sound (G : Graph) (sig : Sym → Kind) (P : Pat) (fresh : Nat) (σ : Binding)
    (hkeys : G.KeysNodup) (hconf : G.Conforms sig) (hwk : PatWK sig P)
    (hP : P.head.isSome = true) (hf : ∀ x ∈ P.vars, x < fresh) (hnd : P.restVars.Nodup)
    (h : σ ∈ run G (compile P fresh) Binding.empty) :
    ∃ id n, σ.node fresh = some id ∧ (id, n) ∈ G.nodes ∧ MatchN G P n σ :=
  interp_sound' G sig P fresh σ hkeys hconf hwk hP hf hnd h

/-- Completeness of e-matching (lemma 12). Every binding `σ` that satisfies
`MatchN` at a stored node is emitted by the interpreter for the compiled
plan, as a binding that agrees with `σ` on every pattern variable (the
emitted binding also carries the plan's fresh node and class variables,
which `σ` need not bind). Hypotheses: distinct node ids, distinct rest
variables, pattern variables below the fresh counter. -/
theorem ematch_complete (G : Graph) (P : Pat) (fresh : Nat) (σ : Binding)
    (id : NodeId) (n : Node)
    (hkeys : G.KeysNodup) (hP : P.head.isSome = true)
    (hf : ∀ x ∈ P.vars, x < fresh) (hnd : P.restVars.Nodup)
    (hmem : (id, n) ∈ G.nodes) (hm : MatchN G P n σ) :
    ∃ σ' ∈ run G (compile P fresh) Binding.empty,
      σ'.node fresh = some id ∧ ExtendsBelow fresh σ' σ :=
  interp_complete' G P fresh σ id n hkeys hP hf hnd hmem hm

end Semper.EMatch
