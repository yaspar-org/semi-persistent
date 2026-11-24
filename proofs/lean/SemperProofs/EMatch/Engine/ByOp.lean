import SemperProofs.EMatch.Lemmas
import SemperProofs.EMatch.Proofs.JoinCommA
import SemperProofs.EMatch.Proofs.Interp

/-!
# ByOp demotion (spec §5)

`candidates` is a chain of filters over the node ids, one per lookup, so
it is a single filter by the conjunction of the bucket memberships
(`candidates_eq`), and the `byOp` lookup, whose bucket is always present,
can be taken out of the join and applied as a filter afterwards
(`byOp_demotion`), equivalently as the test `op(n) = f` on the node table
under distinct keys (`byOp_demotion_op`).
-/

namespace Semper.EMatch

/-- The operator of a stored node. -/
def Graph.op (G : Graph) (id : NodeId) : Option Sym := (G.lookupNode id).map (·.op)

/-- A filter commutes with the join's fold. -/
theorem foldl_joinStepFn_filter (G : Graph) (σ : Binding) (p : NodeId → Bool) :
    ∀ (ls : List Lookup) (acc : List NodeId),
    ls.foldl (joinStepFn G σ) (acc.filter p) = (ls.foldl (joinStepFn G σ) acc).filter p
  | [], acc => rfl
  | l :: ls, acc => by
      simp only [List.foldl_cons]
      cases hb : l.bucket G σ with
      | some b =>
          have h1 : joinStepFn G σ (acc.filter p) l =
              (acc.filter (fun id => decide (id ∈ b))).filter p := by
            unfold joinStepFn
            rw [hb]
            simp only [List.filter_filter]
            congr 1
            funext id
            exact Bool.and_comm _ _
          have h2 : joinStepFn G σ acc l = acc.filter (fun id => decide (id ∈ b)) := by
            unfold joinStepFn
            rw [hb]
          rw [h1, h2, foldl_joinStepFn_filter G σ p ls]
      | none =>
          have h1 : joinStepFn G σ (acc.filter p) l = [] := by
            unfold joinStepFn
            rw [hb]
          have h2 : joinStepFn G σ acc l = [] := by
            unfold joinStepFn
            rw [hb]
          rw [h1, h2, foldl_joinStepFn_nil]
          rfl

theorem foldl_joinStepFn_eq (G : Graph) (σ : Binding) :
    ∀ (ls : List Lookup) (acc : List NodeId),
    ls.foldl (joinStepFn G σ) acc =
      if ∀ l ∈ ls, (l.bucket G σ).isSome then
        acc.filter (fun id => decide (∀ l ∈ ls, ∀ b ∈ l.bucket G σ, id ∈ b))
      else []
  | [], acc => by simp
  | l :: ls, acc => by
      simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
      cases hb : l.bucket G σ with
      | some b =>
          have h2 : joinStepFn G σ acc l = acc.filter (fun id => decide (id ∈ b)) := by
            unfold joinStepFn
            rw [hb]
          rw [h2, foldl_joinStepFn_eq G σ ls]
          simp only [Option.isSome_some, true_and, Option.mem_def, Option.some.injEq]
          split
          · rw [List.filter_filter]
            congr 1
            funext id
            rw [Bool.and_comm, ← Bool.decide_and]
            congr 1
            apply propext
            simp only [Option.mem_def, Option.some.injEq]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨fun _ h => h ▸ h1, h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1 b rfl, h2⟩
          · rfl
      | none =>
          have h2 : joinStepFn G σ acc l = [] := by
            unfold joinStepFn
            rw [hb]
          rw [h2, foldl_joinStepFn_nil]
          simp

/-- The join as one filter: when every lookup has a bucket, the node ids
in every bucket, in node order; otherwise nothing. -/
theorem candidates_eq (G : Graph) (σ : Binding) (ls : List Lookup) :
    candidates G σ ls =
      if ∀ l ∈ ls, (l.bucket G σ).isSome then
        (G.nodes.map (·.1)).filter (fun id => decide (∀ l ∈ ls, ∀ b ∈ l.bucket G σ, id ∈ b))
      else [] := by
  rw [candidates_eq_foldl, foldl_joinStepFn_eq]

/-- The join depends on the lookups only as a set. -/
theorem candidates_perm (G : Graph) (σ : Binding) {ls ls' : List Lookup}
    (h : ls.Perm ls') : candidates G σ ls = candidates G σ ls' := by
  rw [candidates_eq, candidates_eq]
  simp only [h.mem_iff]

theorem candidates_cons_byOp (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym) :
    candidates G σ (.byOp f :: ls) =
      (candidates G σ ls).filter (fun id => decide (id ∈ G.byOp f)) := by
  rw [candidates_eq_foldl, candidates_eq_foldl, List.foldl_cons]
  have h : joinStepFn G σ (G.nodes.map (·.1)) (.byOp f) =
      (G.nodes.map (·.1)).filter (fun id => decide (id ∈ G.byOp f)) := rfl
  rw [h, foldl_joinStepFn_filter]

/-- ByOp demotion (spec §5): the `byOp` lookup leaves the join and becomes
a filter on its result, as lists. -/
theorem byOp_demotion (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym)
    (hop : Lookup.byOp f ∈ ls) :
    candidates G σ ls =
      (candidates G σ (ls.erase (.byOp f))).filter (fun id => decide (id ∈ G.byOp f)) := by
  rw [candidates_perm G σ (List.perm_cons_erase hop), candidates_cons_byOp]

/-- Membership form of `byOp_demotion`. -/
theorem mem_byOp_demotion (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym)
    (hop : Lookup.byOp f ∈ ls) (id : NodeId) :
    id ∈ candidates G σ ls ↔
      id ∈ candidates G σ (ls.erase (.byOp f)) ∧ id ∈ G.byOp f := by
  rw [byOp_demotion G σ ls f hop, List.mem_filter, decide_eq_true_eq]

/-- Under distinct keys, `op(id) = f` is membership in the node table with
operator `f`. -/
theorem Graph.op_eq_iff {G : Graph} (hk : G.KeysNodup) (id : NodeId) (f : Sym) :
    G.op id = some f ↔ ∃ n, (id, n) ∈ G.nodes ∧ n.op = f := by
  unfold Graph.op
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨n, hl, rfl⟩
    exact ⟨n, mem_of_lookupNode hl, rfl⟩
  · rintro ⟨n, hmem, rfl⟩
    exact ⟨n, lookupNode_of_mem hk hmem, rfl⟩

theorem mem_byOp_iff_op {G : Graph} (hk : G.KeysNodup) (id : NodeId) (f : Sym) :
    id ∈ G.byOp f ↔ G.op id = some f := by
  rw [index_exact_byOp, Graph.op_eq_iff hk]

/-- ByOp demotion against the node-op table (spec §5). -/
theorem byOp_demotion_op (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym)
    (hk : G.KeysNodup) (hop : Lookup.byOp f ∈ ls) :
    candidates G σ ls =
      (candidates G σ (ls.erase (.byOp f))).filter (fun id => decide (G.op id = some f)) := by
  rw [byOp_demotion G σ ls f hop]
  congr 1
  funext id
  simp only [mem_byOp_iff_op hk]


end Semper.EMatch
