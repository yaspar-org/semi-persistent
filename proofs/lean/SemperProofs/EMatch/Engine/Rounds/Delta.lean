import SemperProofs.EMatch.Engine.Rounds.AtomDelta

/-!
# Delta completeness of one round (spec-semi-naive-rounds §D)

For a rule made of scanning atoms and equalities between class variables
(the atoms the engine's `needs_naive_match`, `saturate.rs:582-616`, does
not route to naive matching, minus `:flatten` and globals, which this
model does not have), every binding that satisfies the atoms on the
snapshot after the round and did not satisfy them on the snapshot before
it binds some scanning atom's node variable to a new id. The proof is by
contraposition over the atoms: if no scanning atom's node is new, every
scanning atom was satisfied before (`atomSat_before_of_not_new`), and
every equality is graph-independent (`qsat_eq_iff`).
-/

namespace Semper.EMatch

/-- The core statement: on the atoms' satisfaction alone. -/
theorem delta_complete_sat {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {atoms : List QAtom} {σ' : Binding}
    (hafter : ∀ q ∈ atoms, QSat R.after σ' q)
    (hbefore : ¬ ∀ q ∈ atoms, QSat R.before σ' q) :
    ∃ a : RAtom, QAtom.scan a ∈ atoms ∧ ∃ id, σ'.node a.node = some id ∧ R.isNew id = true := by
  by_contra hno
  push Not at hno
  apply hbefore
  intro q hq
  cases q with
  | scan a =>
      refine atomSat_before_of_not_new hwf htr (hafter _ hq) ?_
      intro id hid
      have := hno a hq id hid
      simpa using this
  | eq x y => exact (qsat_eq_iff R.after R.before σ' x y).1 (hafter _ hq)

/-- `delta_complete`: a match of the rule after the round that is not a
match before it binds some join atom to a new id (touched, or named by the
merge-membership delta). Stated on `Matches`, the characterization of the
naive run's emitted set (`plan_matches`). -/
theorem delta_complete {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {atoms : List QAtom} {σ' : Binding}
    (hafter : Matches R.after atoms σ') (hbefore : ¬ Matches R.before atoms σ') :
    ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧
      ∃ id, σ'.node ak.node = some id ∧ R.isNew id = true := by
  have hsat : ¬ ∀ q ∈ atoms, QSat R.before σ' q := by
    intro hs
    exact hbefore { hafter with sat := hs }
  obtain ⟨a, ha, id, hid, hnew⟩ := delta_complete_sat hwf htr hafter.sat hsat
  obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
  exact ⟨k, a, hk, id, hid, hnew⟩

/-- The stronger hypothesis of the informal statement: no binding agreeing
with `σ'` on the variables `V` satisfied the atoms before the round. It
implies the hypothesis of `delta_complete_sat` (take the binding itself),
so the conclusion is the same. -/
theorem delta_complete_agree {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {atoms : List QAtom} {σ' : Binding} (V : List Var)
    (hafter : ∀ q ∈ atoms, QSat R.after σ' q)
    (hbefore : ∀ σ, AgreeOn V σ σ' → ¬ ∀ q ∈ atoms, QSat R.before σ q) :
    ∃ a : RAtom, QAtom.scan a ∈ atoms ∧ ∃ id, σ'.node a.node = some id ∧ R.isNew id = true :=
  delta_complete_sat hwf htr hafter (hbefore σ' (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩))

/-- Equalities between node variables need no exception under tracking:
an instance of `delta_complete` with an `eq` between the node variables of
two scanning atoms (the engine's third exception, `saturate.rs:603-615`,
measured before the merge-membership delta existed). -/
theorem delta_complete_eq_nodes {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {a b : RAtom} {rest : List QAtom} {σ' : Binding}
    (hafter : Matches R.after (.scan a :: .scan b :: .eq a.node b.node :: rest) σ')
    (hbefore : ¬ Matches R.before (.scan a :: .scan b :: .eq a.node b.node :: rest) σ') :
    ∃ (k : Nat) (ak : RAtom), (.scan a :: .scan b :: .eq a.node b.node :: rest)[k]? = some (.scan ak) ∧
      ∃ id, σ'.node ak.node = some id ∧ R.isNew id = true :=
  delta_complete hwf htr hafter hbefore

end Semper.EMatch
