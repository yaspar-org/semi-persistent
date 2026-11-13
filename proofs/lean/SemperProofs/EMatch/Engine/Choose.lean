import SemperProofs.EMatch.Engine.Runtime

/-!
# The engine's choice of the next atom (fidelity: `choose_atom`)

At a decision point of a runtime-scheduled query, `advance`
(`ematch.rs:1549-1600`) first lowers the eager atoms to fixpoint and then
calls `choose_atom` (`ematch.rs:1609-1659`), which prices every unused
scanning atom by the length of the shortest bucket its join would open
under the current bindings (`cursor_len`, `ematch.rs:1673-1705`) and takes
the cheapest, lowest index first on a tie. `chooseEngine` transcribes that
rule; `chooseEngine_mem` says it is a choice function `runND` accepts (it
picks an unused scanning atom when one exists, so the `min'` fallback of
`runND` never fires); `runEngine_matches` instantiates `runND_matches` with
it.

The rule, line by line:

* the candidates are `costed & !used` (`:1623`): the unused atoms that are
  not equalities or guards (`Adaptive::new`, `:1435-1448`), which in this
  development are the unused scanning atoms, `unusedScan atoms used`;
* a single candidate is taken without pricing (`:1628-1633`); the general
  scan below gives the same answer, so it is not a separate case here;
* the scan runs over `0..atoms.len()` in index order (`:1635-1644`); a
  candidate's price is `cursor_len` of the block `segment(ai, bound, used)`
  lowers it to, which starts with its join (`emit_atom`); the first
  candidate is kept, and a later one replaces it only if strictly cheaper
  (`is_none_or(|(b, _)| len < b)`), so ties keep the lowest index;
* `cursor_len` (`:1690-1703`) reads one bucket per lookup of the join in
  the store the atom's mode selects (`delta` for `Delta`, `full` for `Full`
  and `FullMinusDelta`, `:1693-1696`) and keeps the smallest length,
  starting from `usize::MAX`; a block that does not start with a join is
  priced `usize::MAX` (`:1687-1689`), which never happens for a scanning
  atom (`lower` starts with the join).

What the model reads for a bucket is `Lookup.bucket`; the delta store is
modelled as the full bucket restricted to the new nodes (`isNew`). The
lookups priced are those of the join `emit_atom` emits
(`engineJoinLookups`: `joinLookups`, plus the `byContains` lookups of a
`:comm` atom that `lower` omits). The bound set the engine carries in
`exec.bound` is read from the environment: `boundSet` is the atoms' class
variables bound in `σ`, and `boundSet_eq` says it is the scheduler's bound
set at every decision point (`Inv`).

The price is a function of the bindings and the atom numbering only
(`choose_atom`'s contract), and the emitted set does not depend on it
(`runEngine_indep`). The test `atom_choice_agrees_with_the_model_on_the_rounds_corpus`
(`ematch.rs`) checks, on every decision of the `conform-rounds` corpus, that
`choose_atom` picks the atom a transliteration of `chooseEngine` picks from
the same bindings and bucket lengths.
-/

namespace Semper.EMatch

/-- `usize::MAX`. -/
def usizeMax : Nat := 2 ^ 64 - 1

/-- The length of the bucket a lookup reads in the store a mode selects
(`cursor_len`, `ematch.rs:1693-1701`): the delta store for `delta`, the
full store for `full` and `fullMinusDelta`. An unbound key reads no bucket
(the scheduler never emits one: `joinLookups` reads the bound set). -/
def bucketLen (G : Graph) (isNew : NodeId → Bool) (m : IndexMode) (σ : Binding) (l : Lookup) : Nat :=
  match l.bucket G σ with
  | none => 0
  | some b =>
      match m with
      | .delta => (b.filter isNew).length
      | .full => b.length
      | .fullMinusDelta => b.length

/-- `cursor_len` (`ematch.rs:1697-1704`): the shortest bucket among the
join's lookups, from `usize::MAX`. -/
def cursorLen (G : Graph) (isNew : NodeId → Bool) (m : IndexMode) (σ : Binding) (ls : List Lookup) : Nat :=
  ls.foldl (fun best l => let len := bucketLen G isNew m σ l; if len < best then len else best) usizeMax

/-- The class variables of the atoms. -/
def atomsVars (atoms : List QAtom) : Finset Var := atoms.foldr (fun q acc => q.binds ∪ acc) ∅

theorem mem_atomsVars {atoms : List QAtom} {x : Var} :
    x ∈ atomsVars atoms ↔ ∃ q ∈ atoms, x ∈ q.binds := by
  induction atoms with
  | nil => simp [atomsVars]
  | cons q qs ih =>
      simp only [atomsVars, List.foldr_cons, Finset.mem_union, List.mem_cons]
      rw [show (qs.foldr (fun q acc => q.binds ∪ acc) ∅) = atomsVars qs from rfl, ih]
      constructor
      · rintro (h | ⟨q', hq', hx⟩)
        · exact ⟨q, Or.inl rfl, h⟩
        · exact ⟨q', Or.inr hq', hx⟩
      · rintro ⟨q', (rfl | hq'), hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨q', hq', hx⟩

/-- The bound set the scheduler carries (`exec.bound`), read from the
environment: the atoms' class variables bound in `σ`. -/
def boundSet (atoms : List QAtom) (σ : Binding) : Finset Var :=
  (atomsVars atoms).filter (fun x => (σ.cls x).isSome)

/-- At every decision point of a run from the empty binding, the bound set
read from the environment is the scheduler's bound set. -/
theorem boundSet_eq {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom} {mode : Nat → IndexMode}
    {used : Finset Nat} {B : Finset Var} {σ : Binding} (hinv : Inv G isNew atoms mode ∅ used B σ) :
    boundSet atoms σ = B := by
  ext x
  simp only [boundSet, Finset.mem_filter, Option.isSome_iff_exists]
  constructor
  · rintro ⟨-, c, hc⟩
    exact (hinv.clsDom x).2 ⟨c, hc⟩
  · intro hx
    refine ⟨?_, (hinv.clsDom x).1 hx⟩
    rcases (hinv.bound x).1 hx with h | ⟨i, q, hq, -, hxq⟩
    · simp at h
    · exact mem_atomsVars.2 ⟨q, mem_of_getElem? hq, hxq⟩

/-- The lookups of the join `emit_atom` emits for the atom under the bound
set `B`: `joinLookups a B`, except that a `:comm` atom is joined as a
two-element multiset (`emit_variadic_join`, `schedule.rs:1526-1531`), with
a `byContains` lookup per bound element, which `lower` omits (`Lower.lean`:
the model's `byContains` files variadic nodes only, the engine also files
sorted pairs, `index.rs:569-579`). The price reads these lookups; the
emitted set does not depend on them (`lower_sound_complete` holds for
`lower`, `runND_indep` for the price). -/
def engineJoinLookups (a : RAtom) (B : Finset Var) : List Lookup :=
  match a.shape with
  | .comm x y => if a.node ∈ B then [.byRepr a.node, .byOp a.op]
      else .byOp a.op :: containsLookups [x, y] B
  | _ => joinLookups a B

/-- The price of candidate `i` (`cursor_len` of its block): the shortest
bucket of its join under the bound set read from `σ`; `usize::MAX` for an
index that is not a scanning atom (never a candidate). -/
def atomCost (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) (atoms : List QAtom)
    (σ : Binding) (i : Nat) : Nat :=
  match atoms[i]? with
  | some (.scan a) => cursorLen G isNew (mode i) σ (engineJoinLookups a (boundSet atoms σ))
  | _ => usizeMax

/-- One iteration of the scan of `choose_atom` (`ematch.rs:1636-1644`):
skip a non-candidate; take the first candidate; replace the best so far
only by a strictly cheaper one. -/
def chooseStep (S : Finset Nat) (cost : Nat → Nat) (best : Option (Nat × Nat)) (i : Nat) :
    Option (Nat × Nat) :=
  if i ∈ S then
    let len := cost i
    match best with
    | none => some (len, i)
    | some (b, j) => if len < b then some (len, i) else some (b, j)
  else best

/-- `choose_atom` (`ematch.rs:1609-1659`): the cheapest candidate of `S`
(the unused scanning atoms) in index order, lowest index first on a tie.
The result is read only when `S` is nonempty (`chooseEngine_mem`); `0` is
the value of an empty scan. -/
def chooseEngine (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) (atoms : List QAtom)
    (σ : Binding) (S : Finset Nat) : Nat :=
  match (List.range atoms.length).foldl (chooseStep S (atomCost G isNew mode atoms σ)) none with
  | some (_, i) => i
  | none => 0

/-! ## `chooseEngine` is a choice function -/

/-- The best so far, if any, is a candidate. -/
def BestOk (S : Finset Nat) : Option (Nat × Nat) → Prop
  | none => True
  | some (_, i) => i ∈ S

theorem chooseStep_bestOk {S : Finset Nat} {cost : Nat → Nat} {best : Option (Nat × Nat)} {i : Nat}
    (h : BestOk S best) : BestOk S (chooseStep S cost best i) := by
  unfold chooseStep
  split
  · rename_i hi
    cases best with
    | none => exact hi
    | some p =>
        obtain ⟨b, j⟩ := p
        simp only
        split
        · exact hi
        · exact h
  · exact h

theorem chooseStep_isSome {S : Finset Nat} {cost : Nat → Nat} {best : Option (Nat × Nat)} {i : Nat}
    (h : best.isSome = true) : (chooseStep S cost best i).isSome = true := by
  unfold chooseStep
  split
  · cases best with
    | none => rfl
    | some p => obtain ⟨b, j⟩ := p; simp only; split <;> rfl
  · exact h

theorem chooseStep_mem_isSome {S : Finset Nat} {cost : Nat → Nat} {best : Option (Nat × Nat)} {i : Nat}
    (hi : i ∈ S) : (chooseStep S cost best i).isSome = true := by
  unfold chooseStep
  simp only [hi, ↓reduceIte]
  cases best with
  | none => rfl
  | some p => obtain ⟨b, j⟩ := p; simp only; split <;> rfl

theorem foldl_chooseStep_bestOk (S : Finset Nat) (cost : Nat → Nat) :
    ∀ (l : List Nat) (best : Option (Nat × Nat)), BestOk S best →
      BestOk S (l.foldl (chooseStep S cost) best) := by
  intro l
  induction l with
  | nil => intro best h; exact h
  | cons i l ih => intro best h; exact ih _ (chooseStep_bestOk h)

theorem foldl_chooseStep_isSome (S : Finset Nat) (cost : Nat → Nat) :
    ∀ (l : List Nat) (best : Option (Nat × Nat)), best.isSome = true →
      (l.foldl (chooseStep S cost) best).isSome = true := by
  intro l
  induction l with
  | nil => intro best h; exact h
  | cons i l ih => intro best h; exact ih _ (chooseStep_isSome h)

theorem foldl_chooseStep_some (S : Finset Nat) (cost : Nat → Nat) :
    ∀ (l : List Nat) (best : Option (Nat × Nat)), (∃ i ∈ l, i ∈ S) →
      (l.foldl (chooseStep S cost) best).isSome = true := by
  intro l
  induction l with
  | nil => rintro best ⟨i, hi, -⟩; simp at hi
  | cons j l ih =>
      rintro best ⟨i, hi, hiS⟩
      simp only [List.mem_cons] at hi
      simp only [List.foldl_cons]
      rcases hi with rfl | hi
      · exact foldl_chooseStep_isSome S cost l _ (chooseStep_mem_isSome hiS)
      · exact ih _ ⟨i, hi, hiS⟩

/-- `chooseEngine` picks a candidate when there is one: it is a choice
function in the sense of `runND`, whose fallback never fires with it. -/
theorem chooseEngine_mem {G : Graph} {isNew : NodeId → Bool} {mode : Nat → IndexMode}
    {atoms : List QAtom} {σ : Binding} {S : Finset Nat} (hS : S.Nonempty)
    (hsub : ∀ i ∈ S, i < atoms.length) : chooseEngine G isNew mode atoms σ S ∈ S := by
  unfold chooseEngine
  obtain ⟨i, hi⟩ := hS
  have hsome := foldl_chooseStep_some S (atomCost G isNew mode atoms σ) (List.range atoms.length) none
    ⟨i, List.mem_range.2 (hsub i hi), hi⟩
  have hok := foldl_chooseStep_bestOk S (atomCost G isNew mode atoms σ) (List.range atoms.length) none
    trivial
  revert hsome hok
  cases List.foldl (chooseStep S (atomCost G isNew mode atoms σ)) none (List.range atoms.length) with
  | none => intro h; simp at h
  | some p => obtain ⟨b, j⟩ := p; intro _ hok; exact hok

/-- On the candidate set `runND` passes, `chooseEngine` is taken as is. -/
theorem chooseEngine_unusedScan {G : Graph} {isNew : NodeId → Bool} {mode : Nat → IndexMode}
    {atoms : List QAtom} {σ : Binding} {used : Finset Nat} (hS : (unusedScan atoms used).Nonempty) :
    (if chooseEngine G isNew mode atoms σ (unusedScan atoms used) ∈ unusedScan atoms used
      then chooseEngine G isNew mode atoms σ (unusedScan atoms used)
      else (unusedScan atoms used).min' hS) =
    chooseEngine G isNew mode atoms σ (unusedScan atoms used) := by
  have hmem : chooseEngine G isNew mode atoms σ (unusedScan atoms used) ∈ unusedScan atoms used :=
    chooseEngine_mem hS (fun i hi =>
      (List.getElem?_eq_some_iff.1 (mem_unusedScan.1 hi).2.choose_spec).1)
  simp only [hmem, ↓reduceIte]

/-! ## The engine's run -/

/-- The adaptive scheduler with the engine's choice function, from the
empty binding, under the modes of a variant (`fun _ => .full` for the
naive run). -/
def runEngine (G : Graph) (isNew : NodeId → Bool) (mode : Nat → IndexMode) (atoms : List QAtom) :
    List Binding :=
  runNDA G isNew mode atoms (chooseEngine G isNew mode atoms) atoms.length ∅ ∅ Binding.empty

/-- `runND_matches` with the engine's choice function: the engine's
runtime-scheduled run emits exactly the matches the modes admit. -/
theorem runEngine_matches {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {mode : Nat → IndexMode} {atoms : List QAtom} (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runEngine G isNew mode atoms ↔ Matches G atoms σ' ∧ ModeOk isNew atoms mode σ' :=
  runNDA_matches _ hwf

/-- The naive run of the engine's scheduler emits exactly `Matches`. -/
theorem runEngine_naive_matches {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {atoms : List QAtom} (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runEngine G isNew (fun _ => .full) atoms ↔ Matches G atoms σ' := by
  intro σ'
  rw [runEngine_matches hwf]
  exact ⟨And.left, fun hm => ⟨hm, modeOk_full _ _ _ hm⟩⟩

/-- `runND_indep` with the engine's choice function: any other choice
function emits the same set. -/
theorem runEngine_indep {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {mode : Nat → IndexMode} {atoms : List QAtom} (choose : Binding → Finset Nat → Nat)
    (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runEngine G isNew mode atoms ↔
      σ' ∈ runNDA G isNew mode atoms choose atoms.length ∅ ∅ Binding.empty := by
  intro σ'
  rw [runEngine_matches hwf, runNDA_matches choose hwf]

/-- The engine's run and every `SchedA` plan emit the same set. -/
theorem runEngine_eq_plan {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {mode : Nat → IndexMode} {atoms : List QAtom} {ap : APlan} (hwf : AtomsWF G sig atoms)
    (h : SchedA atoms ∅ ∅ ap) :
    ∀ σ', σ' ∈ runEngine G isNew mode atoms ↔ σ' ∈ runA G isNew mode ap Binding.empty :=
  runNDA_eq_runA _ hwf h

end Semper.EMatch
