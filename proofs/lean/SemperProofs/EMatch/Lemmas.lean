import SemperProofs.EMatch.Ref

/-!
# E-matching: lemma statements (sketch part (h))

Numbering follows the lemma list in `notes-ematch-proof.md`, part (h).
Proved here: lemma 1 (`index_exact`, four families) and lemma 4
(`mult_matches`, soundness and completeness). Lemmas 3, 5, 6, 7, 10, 11
and 12 are proved in `Proofs/{JoinCommA,DecomposeAC,CompileWF,Interp}.lean`
under primed names and re-exported by `Main.lean`; the pointer comments
below record each statement change relative to the original stub.

Not stated in this phase: lemma 2 (the leapfrog cursor procedure; the
reference interpreter intersects by `List.filter`, so lemma 3 does not
depend on it), lemmas 8 and 9 (flatten views and the demand refolding),
and lemma 13 (the binary corollary, which needs `represents` from the
congruence-closure development).
-/

namespace Semper.EMatch

/-! ## Lemma 1: index exactness -/

/-- Lemma 1 (`index_exact`), `by_op`. -/
theorem index_exact_byOp (G : Graph) (f : Sym) (id : NodeId) :
    id ∈ G.byOp f ↔ ∃ n, (id, n) ∈ G.nodes ∧ n.op = f := by
  simp only [Graph.byOp, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨id', n⟩, ⟨hmem, hop⟩, rfl⟩
    exact ⟨n, hmem, hop⟩
  · rintro ⟨n, hmem, hop⟩
    exact ⟨(id, n), ⟨hmem, hop⟩, rfl⟩

/-- Lemma 1 (`index_exact`), `by_repr`. -/
theorem index_exact_byRepr (G : Graph) (c : C) (id : NodeId) :
    id ∈ G.byRepr c ↔ ∃ n, (id, n) ∈ G.nodes ∧ G.find id = c := by
  simp only [Graph.byRepr, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨id', n⟩, ⟨hmem, hf⟩, rfl⟩
    exact ⟨n, hmem, hf⟩
  · rintro ⟨n, hmem, hf⟩
    exact ⟨(id, n), ⟨hmem, hf⟩, rfl⟩

/-- Lemma 1 (`index_exact`), `by_child_pos`. -/
theorem index_exact_byChildPos (G : Graph) (pos : Nat) (c : C) (id : NodeId) :
    id ∈ G.byChildPos pos c ↔
      ∃ n, (id, n) ∈ G.nodes ∧ n.children.childAt pos = some c := by
  simp only [Graph.byChildPos, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨id', n⟩, ⟨hmem, hc⟩, rfl⟩
    exact ⟨n, hmem, hc⟩
  · rintro ⟨n, hmem, hc⟩
    exact ⟨(id, n), ⟨hmem, hc⟩, rfl⟩

/-- Lemma 1 (`index_exact`), `by_contains`. -/
theorem index_exact_byContains (G : Graph) (c : C) (id : NodeId) :
    id ∈ G.byContains c ↔
      ∃ n, (id, n) ∈ G.nodes ∧ n.children.isVariadic = true ∧
        n.children.containsClass c = true := by
  simp only [Graph.byContains, List.mem_map, List.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨id', n⟩, ⟨hmem, hv, hc⟩, rfl⟩
    exact ⟨n, hmem, hv, hc⟩
  · rintro ⟨n, hmem, hv, hc⟩
    exact ⟨(id, n), ⟨hmem, hv, hc⟩, rfl⟩

/-! ## Lemma 3: join -/

/-! Lemma 3 (`join_complete`): proved as `join_complete'` in
`Proofs/JoinCommA.lean`, statement unchanged. -/

/-! ## Lemma 4: multiplicity constraints -/

theorem inInterval_iff (lo : Nat) (hi : Option Nat) (m : Nat) :
    inInterval lo hi m = true ↔ lo ≤ m ∧ ∀ h ∈ hi, m ≤ h := by
  cases hi <;> simp [inInterval]

/-- Lemma 4 (`mult_matches_spec`), soundness: an accepted count satisfies
the annotation in the returned binding, which extends the input. -/
theorem mult_matches_sound (σ σ' : Binding) (μ : Mult) (m : Nat)
    (h : multMatches σ μ m = some σ') :
    MultOk σ' μ m ∧ Binding.Extends σ σ' := by
  cases μ with
  | exact k =>
      simp only [multMatches] at h
      split at h
      · cases h
        exact ⟨by simpa [MultOk], Binding.Extends.refl _⟩
      · cases h
  | var k lo hi =>
      simp only [multMatches] at h
      split at h
      · rename_i hin
        rw [inInterval_iff] at hin
        split at h
        · rename_i m' hm'
          split at h
          · cases h
            rename_i heq
            subst heq
            exact ⟨⟨hm', hin.1, hin.2⟩, Binding.Extends.refl _⟩
          · cases h
        · rename_i hnone
          cases h
          refine ⟨⟨?_, hin.1, hin.2⟩, ?_⟩
          · simp [Binding.setMult]
          · refine ⟨fun _ _ h => h, fun _ _ h => h, ?_, fun _ _ h => h,
              fun _ _ h => h, fun _ _ h => h⟩
            intro k' m'' hk'
            have hne : k' ≠ k := by
              intro heq
              subst heq
              rw [hnone] at hk'
              cases hk'
            simp [Binding.setMult, Function.update_of_ne hne, hk']
      · cases h

/-- Lemma 4 (`mult_matches_spec`), completeness: if a binding `σ'`
extending `σ` satisfies the annotation for count `m`, then `multMatches`
accepts `m` from `σ` with a binding below `σ'`. -/
theorem mult_matches_complete (σ σ' : Binding) (μ : Mult) (m : Nat)
    (hok : MultOk σ' μ m) (hext : Binding.Extends σ σ') :
    ∃ σ'', multMatches σ μ m = some σ'' ∧ Binding.Extends σ'' σ' := by
  cases μ with
  | exact k =>
      simp only [MultOk] at hok
      exact ⟨σ, by simp [multMatches, hok], hext⟩
  | var k lo hi =>
      obtain ⟨hk, hlo, hhi⟩ := hok
      have hin : inInterval lo hi m = true := (inInterval_iff lo hi m).2 ⟨hlo, hhi⟩
      cases hσ : σ.mult k with
      | some m' =>
          have : m' = m := by
            have h1 := hext.2.2.1 k m' hσ
            rw [hk] at h1
            cases h1
            rfl
          subst this
          exact ⟨σ, by simp [multMatches, hin, hσ], hext⟩
      | none =>
          refine ⟨σ.setMult k m, by simp [multMatches, hin, hσ], ?_⟩
          refine ⟨hext.1, hext.2.1, ?_, hext.2.2.2.1, hext.2.2.2.2.1,
            hext.2.2.2.2.2⟩
          intro k' m'' hk'
          by_cases hkk : k' = k
          · subst hkk
            simp [Binding.setMult] at hk'
            rw [← hk']
            exact hk
          · simp [Binding.setMult, Function.update_of_ne hkk] at hk'
            exact hext.2.2.1 k' m'' hk'

/-! ## Lemmas 5 and 6: AC decomposition -/

/-! Lemmas 5 and 6: proved in `Proofs/DecomposeAC.lean`.
`decompose_ac_sound'` adds `hfresh : ∀ r ∈ rest, σ.rest r = none`: the
reference interpreter writes the rest variable unconditionally, so a rest
already bound to another value yields a result that does not extend `σ`.
`decompose_ac_complete'` has the original statement. -/

/-! Lemma 7: proved in `Proofs/DecomposeAC.lean` and `Proofs/JoinCommA.lean`.
`decompose_aci_sound'` adds `hfresh : ∀ r ∈ rest, σ.finRest r = none`, for
the reason above; `decompose_aci_complete'` is unchanged.
`expand_a_sound'` adds `hpre₀`, `hsuf₀` (the rest variables are unbound in
`σ`) and `hdist` (prefix and suffix rests are distinct variables): `bindSeq`
writes a rest unconditionally, and with one variable for both rests the
second write erases the first. `expand_a_complete'`,
`decompose_comm_sound'` and `decompose_comm_complete'` are unchanged. -/

/-! ## Lemma 10: plan well-formedness of the compiler's output -/

/-! Lemma 10 (`plan_wf`): proved as `compile_wf'` in `Proofs/CompileWF.lean`,
statement unchanged. -/

/-! ## Lemmas 11 and 12: the interpreter -/

/-- Keys of the node list are distinct, so `lookupNode` is a function of
the membership relation. -/
def Graph.KeysNodup (G : Graph) : Prop := (G.nodes.map (·.1)).Nodup

/-! Lemmas 11 and 12: proved in `Proofs/Interp.lean`.
`interp_sound'` adds a kind signature `sig` with `G.Conforms sig` and
`PatWK sig P` (a node has the children shape of its operator's kind, the
pattern uses the constructor of its head's kind): without it a plain
pattern with no arguments is emitted for a multiset node of the same
operator, which `MatchN` rejects. It also adds `P.restVars.Nodup`: the
interpreter overwrites a rest variable bound twice.
`interp_complete'` adds `P.restVars.Nodup` and concludes
`ExtendsBelow fresh σ' σ` instead of `Binding.Extends σ' σ`: the emitted
binding also binds the plan's fresh node and class variables, which the
match witness need not bind. -/

end Semper.EMatch
