import SemperProofs.EMatch.Lemmas

/-!
# E-matching proofs: join, commutative pair, associative split

Proves in full the primed versions of `join_complete`,
`decompose_comm_sound`, `decompose_comm_complete`, `expand_a_sound` and
`expand_a_complete` from `Lemmas.lean`.

`expand_a_sound` is false as stated in `Lemmas.lean`: `bindSeq` overwrites
an already bound rest variable, and a pattern whose prefix and suffix rest
are the same variable cannot satisfy both `SeqRestOk` conjuncts. The primed
version adds the hypotheses that the rest variables are unbound in the input
binding and distinct from each other; both hold for the compiler's plans.
-/

namespace Semper.EMatch

/-! ## Binding helpers -/

theorem extends_setCls_of_none {σ : Binding} {x : Var} {c : C}
    (h : σ.cls x = none) : Binding.Extends σ (σ.setCls x c) := by
  refine ⟨?_, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h⟩
  intro y d hy
  have hne : y ≠ x := by
    rintro rfl
    rw [h] at hy
    cases hy
  simp [Binding.setCls, Function.update_of_ne hne, hy]

theorem extends_setCls_left {σ σ' : Binding} {x : Var} {c : C}
    (hext : Binding.Extends σ σ') (hx : σ'.cls x = some c) :
    Binding.Extends (σ.setCls x c) σ' := by
  refine ⟨?_, hext.2.1, hext.2.2.1, hext.2.2.2.1, hext.2.2.2.2.1,
    hext.2.2.2.2.2⟩
  intro y d hy
  by_cases hyx : y = x
  · subst hyx
    simp [Binding.setCls] at hy
    subst hy
    exact hx
  · simp [Binding.setCls, Function.update_of_ne hyx] at hy
    exact hext.1 y d hy

theorem extends_setSeqRest_of_none {σ : Binding} {r : Var} {u : List C}
    (h : σ.seqRest r = none) : Binding.Extends σ (σ.setSeqRest r u) := by
  refine ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, ?_,
    fun _ _ h => h⟩
  intro y d hy
  have hne : y ≠ r := by
    rintro rfl
    rw [h] at hy
    cases hy
  simp [Binding.setSeqRest, Function.update_of_ne hne, hy]

theorem extends_setSeqRest_left {σ σ' : Binding} {r : Var} {u : List C}
    (hext : Binding.Extends σ σ') (hr : σ'.seqRest r = some u) :
    Binding.Extends (σ.setSeqRest r u) σ' := by
  refine ⟨hext.1, hext.2.1, hext.2.2.1, hext.2.2.2.1, ?_, hext.2.2.2.2.2⟩
  intro y d hy
  by_cases hyr : y = r
  · subst hyr
    simp [Binding.setSeqRest] at hy
    subst hy
    exact hr
  · simp [Binding.setSeqRest, Function.update_of_ne hyr] at hy
    exact hext.2.2.2.2.1 y d hy

/-! ## `bindElems` -/

theorem bindElems_sound : ∀ (xs : List Var) (cs : List C) (σ σ' : Binding),
    bindElems xs cs σ = some σ' →
    Binding.Extends σ σ' ∧ xs.length = cs.length ∧
      ∀ ec ∈ xs.zip cs, σ'.cls ec.1 = some ec.2
  | [], [], σ, σ', h => by
      simp only [bindElems, Option.some.injEq] at h
      subst h
      exact ⟨Binding.Extends.refl _, rfl, by simp⟩
  | x :: xs, c :: cs, σ, σ', h => by
      simp only [bindElems] at h
      split at h
      · rename_i c' hc'
        split at h
        · rename_i heq
          subst heq
          obtain ⟨hext, hlen, hall⟩ := bindElems_sound xs cs σ σ' h
          refine ⟨hext, by simp [hlen], ?_⟩
          intro ec hec
          rw [List.zip_cons_cons, List.mem_cons] at hec
          rcases hec with rfl | hec
          · exact hext.1 x c' hc'
          · exact hall ec hec
        · cases h
      · rename_i hnone
        obtain ⟨hext, hlen, hall⟩ := bindElems_sound xs cs _ σ' h
        refine ⟨(extends_setCls_of_none hnone).trans hext, by simp [hlen], ?_⟩
        intro ec hec
        rw [List.zip_cons_cons, List.mem_cons] at hec
        rcases hec with rfl | hec
        · exact hext.1 x c (by simp [Binding.setCls])
        · exact hall ec hec
  | [], _ :: _, σ, σ', h => by simp [bindElems] at h
  | _ :: _, [], σ, σ', h => by simp [bindElems] at h

theorem bindElems_complete : ∀ (xs : List Var) (cs : List C) (σ σ' : Binding),
    Binding.Extends σ σ' → xs.length = cs.length →
    (∀ ec ∈ xs.zip cs, σ'.cls ec.1 = some ec.2) →
    ∃ σ'', bindElems xs cs σ = some σ'' ∧ Binding.Extends σ'' σ'
  | [], [], σ, σ', hext, _, _ => ⟨σ, rfl, hext⟩
  | x :: xs, c :: cs, σ, σ', hext, hlen, hall => by
      have hx : σ'.cls x = some c := hall (x, c) (by simp)
      have hlen' : xs.length = cs.length := by simpa using hlen
      have hall' : ∀ ec ∈ xs.zip cs, σ'.cls ec.1 = some ec.2 :=
        fun ec h => hall ec (by simp [h])
      cases hc : σ.cls x with
      | none =>
          simp only [bindElems, hc]
          exact bindElems_complete xs cs _ σ' (extends_setCls_left hext hx) hlen' hall'
      | some c' =>
          have hcc : c' = c := by
            have := hext.1 x c' hc
            rw [this] at hx
            exact Option.some.inj hx
          subst hcc
          simp only [bindElems, hc, ite_true]
          exact bindElems_complete xs cs σ σ' hext hlen' hall'
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen

theorem bindElems_seqRest : ∀ (xs : List Var) (cs : List C) (σ σ' : Binding),
    bindElems xs cs σ = some σ' → σ'.seqRest = σ.seqRest
  | [], [], σ, σ', h => by
      simp only [bindElems, Option.some.injEq] at h
      subst h
      rfl
  | x :: xs, c :: cs, σ, σ', h => by
      simp only [bindElems] at h
      split at h
      · split at h
        · exact bindElems_seqRest xs cs σ σ' h
        · cases h
      · exact (bindElems_seqRest xs cs _ σ' h).trans rfl
  | [], _ :: _, σ, σ', h => by simp [bindElems] at h
  | _ :: _, [], σ, σ', h => by simp [bindElems] at h

/-! ## Lemma 3: join -/

/-- The fold step of `candidates`, named. -/
def joinStepFn (G : Graph) (σ : Binding) (acc : List NodeId) (l : Lookup) :
    List NodeId :=
  match l.bucket G σ with
  | some b => acc.filter (fun id => decide (id ∈ b))
  | none => []

theorem candidates_eq_foldl (G : Graph) (σ : Binding) (ls : List Lookup) :
    candidates G σ ls = ls.foldl (joinStepFn G σ) (G.nodes.map (·.1)) := rfl

theorem lookup_bucket_iff (G : Graph) (σ : Binding) (l : Lookup) (b : List NodeId)
    (hb : l.bucket G σ = some b) (id : NodeId) : id ∈ b ↔ l.pred G σ id := by
  cases l with
  | byOp f =>
      simp only [Lookup.bucket, Option.some.injEq] at hb
      subst hb
      exact index_exact_byOp G f id
  | byRepr x =>
      simp only [Lookup.bucket] at hb
      cases hx : σ.cls x with
      | none => rw [hx] at hb; cases hb
      | some c =>
          rw [hx] at hb
          simp only [Option.map_some, Option.some.injEq] at hb
          subst hb
          simp only [Lookup.pred, index_exact_byRepr]
          constructor
          · rintro ⟨n, hmem, hf⟩
            exact ⟨⟨n, hmem⟩, by rw [hx, hf]⟩
          · rintro ⟨⟨n, hmem⟩, hf⟩
            rw [hx] at hf
            exact ⟨n, hmem, (Option.some.inj hf).symm⟩
  | byChildPos pos x =>
      simp only [Lookup.bucket] at hb
      cases hx : σ.cls x with
      | none => rw [hx] at hb; cases hb
      | some c =>
          rw [hx] at hb
          simp only [Option.map_some, Option.some.injEq] at hb
          subst hb
          simp only [Lookup.pred, index_exact_byChildPos]
          constructor
          · rintro ⟨n, hmem, hc⟩
            exact ⟨n, c, hmem, hx, hc⟩
          · rintro ⟨n, c', hmem, hx', hc⟩
            rw [hx] at hx'
            cases hx'
            exact ⟨n, hmem, hc⟩
  | byContains x =>
      simp only [Lookup.bucket] at hb
      cases hx : σ.cls x with
      | none => rw [hx] at hb; cases hb
      | some c =>
          rw [hx] at hb
          simp only [Option.map_some, Option.some.injEq] at hb
          subst hb
          simp only [Lookup.pred, index_exact_byContains]
          constructor
          · rintro ⟨n, hmem, hv, hc⟩
            exact ⟨n, c, hmem, hx, hv, hc⟩
          · rintro ⟨n, c', hmem, hx', hv, hc⟩
            rw [hx] at hx'
            cases hx'
            exact ⟨n, hmem, hv, hc⟩

theorem lookup_bucket_none (G : Graph) (σ : Binding) (l : Lookup)
    (hb : l.bucket G σ = none) (id : NodeId) : ¬ l.pred G σ id := by
  cases l with
  | byOp f => simp [Lookup.bucket] at hb
  | byRepr x =>
      simp only [Lookup.bucket, Option.map_eq_none_iff] at hb
      rintro ⟨_, hx⟩
      rw [hb] at hx
      cases hx
  | byChildPos pos x =>
      simp only [Lookup.bucket, Option.map_eq_none_iff] at hb
      rintro ⟨_, _, _, hx, _⟩
      rw [hb] at hx
      cases hx
  | byContains x =>
      simp only [Lookup.bucket, Option.map_eq_none_iff] at hb
      rintro ⟨_, _, _, hx, _⟩
      rw [hb] at hx
      cases hx

theorem foldl_joinStepFn_nil (G : Graph) (σ : Binding) :
    ∀ (ls : List Lookup), ls.foldl (joinStepFn G σ) [] = []
  | [] => rfl
  | l :: ls => by
      simp only [List.foldl_cons]
      have : joinStepFn G σ [] l = [] := by
        unfold joinStepFn
        cases l.bucket G σ <;> simp
      rw [this]
      exact foldl_joinStepFn_nil G σ ls

theorem candidates_aux (G : Graph) (σ : Binding) :
    ∀ (ls : List Lookup) (acc : List NodeId) (id : NodeId),
    id ∈ ls.foldl (joinStepFn G σ) acc ↔ id ∈ acc ∧ ∀ l ∈ ls, l.pred G σ id
  | [], acc, id => by simp
  | l :: ls, acc, id => by
      simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
      cases hb : l.bucket G σ with
      | some b =>
          have hstep : joinStepFn G σ acc l = acc.filter (fun id => decide (id ∈ b)) := by
            unfold joinStepFn
            rw [hb]
          rw [hstep, candidates_aux G σ ls]
          simp only [List.mem_filter, decide_eq_true_eq]
          rw [lookup_bucket_iff G σ l b hb id]
          tauto
      | none =>
          have hstep : joinStepFn G σ acc l = [] := by
            unfold joinStepFn
            rw [hb]
          rw [hstep, foldl_joinStepFn_nil]
          simp only [List.not_mem_nil, false_iff, not_and]
          intro _ hp _
          exact lookup_bucket_none G σ l hb id hp

/-- Lemma 3 (`join_complete`), proved. -/
theorem join_complete' (G : Graph) (σ : Binding) (ls : List Lookup) (id : NodeId) :
    id ∈ candidates G σ ls ↔
      (∃ n, (id, n) ∈ G.nodes) ∧ ∀ l ∈ ls, l.pred G σ id := by
  rw [candidates_eq_foldl, candidates_aux]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨⟨id', n⟩, hmem, rfl⟩, hall⟩
    exact ⟨⟨n, hmem⟩, hall⟩
  · rintro ⟨⟨n, hmem⟩, hall⟩
    exact ⟨⟨(id, n), hmem, rfl⟩, hall⟩

/-! ## Lemma 7: commutative pair -/

/-- Lemma 7 (`decompose_comm_sound`), proved. -/
theorem decompose_comm_sound' (x y : Var) (a b : C) (σ σ' : Binding)
    (h : σ' ∈ decomposeComm x y a b σ) :
    Binding.Extends σ σ' ∧
      ((σ'.cls x = some a ∧ σ'.cls y = some b) ∨
        (σ'.cls x = some b ∧ σ'.cls y = some a)) := by
  unfold decomposeComm at h
  rw [List.mem_append, Option.mem_toList, Option.mem_toList] at h
  rcases h with h | h
  · obtain ⟨hext, -, hall⟩ := bindElems_sound _ _ _ _ h
    exact ⟨hext, Or.inl ⟨hall (x, a) (by simp), hall (y, b) (by simp)⟩⟩
  · obtain ⟨hext, -, hall⟩ := bindElems_sound _ _ _ _ h
    exact ⟨hext, Or.inr ⟨hall (x, b) (by simp), hall (y, a) (by simp)⟩⟩

/-- Lemma 7 (`decompose_comm_complete`), proved. -/
theorem decompose_comm_complete' (x y : Var) (a b : C) (σ σ' : Binding)
    (hext : Binding.Extends σ σ')
    (h : (σ'.cls x = some a ∧ σ'.cls y = some b) ∨
      (σ'.cls x = some b ∧ σ'.cls y = some a)) :
    ∃ σ'' ∈ decomposeComm x y a b σ, Binding.Extends σ'' σ' := by
  unfold decomposeComm
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · obtain ⟨σ'', hbe, hext'⟩ := bindElems_complete [x, y] [a, b] σ σ' hext rfl (by
      intro ec hec
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at hec
      rcases hec with rfl | rfl
      · exact hx
      · exact hy)
    exact ⟨σ'', by rw [List.mem_append, Option.mem_toList]; exact Or.inl hbe, hext'⟩
  · obtain ⟨σ'', hbe, hext'⟩ := bindElems_complete [x, y] [b, a] σ σ' hext rfl (by
      intro ec hec
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at hec
      rcases hec with rfl | rfl
      · exact hx
      · exact hy)
    exact ⟨σ'', by rw [List.mem_append, Option.mem_toList, Option.mem_toList]; exact Or.inr hbe,
      hext'⟩

/-! ## Lemma 7: associative split -/

theorem bindSeq_cls (r : Option Var) (u : List C) (σ : Binding) :
    (bindSeq r u σ).cls = σ.cls := by
  cases r <;> rfl

theorem bindSeq_seqRest_of_ne (r : Option Var) (u : List C) (σ : Binding) (y : Var)
    (hy : ∀ r', r = some r' → y ≠ r') : (bindSeq r u σ).seqRest y = σ.seqRest y := by
  cases r with
  | none => rfl
  | some r' => simp [bindSeq, Binding.setSeqRest, Function.update_of_ne (hy r' rfl)]

/-- Lemma 7 (`expand_a_sound`), corrected. The statement in `Lemmas.lean`
is false: with `pre = some r` and `σ.seqRest r = some [5]`, `expandA` with
`cs = []` emits a binding with `seqRest r = some []`, which does not extend
`σ`; and with `pre = suf = some r`, `elems = []`, `cs = [1]`, the split
`u = []`, `v = [1]` binds `r` to `[1]` and `SeqRestOk σ' pre []` fails.
The hypotheses `hpre₀`, `hsuf₀` (rests unbound in `σ`) and `hdist` (the
two rests are distinct variables) exclude both; the compiler's plans
satisfy them because a rest variable is bound once. -/
theorem expand_a_sound' (pre suf : Option Var) (elems : List Var) (cs : List C)
    (σ σ' : Binding)
    (hpre₀ : ∀ r, pre = some r → σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (h : σ' ∈ expandA pre elems suf cs σ) :
    Binding.Extends σ σ' ∧
      ∃ u mid v : List C, cs = u ++ mid ++ v ∧ mid.length = elems.length ∧
        SeqRestOk σ' pre u ∧ SeqRestOk σ' suf v ∧
        ∀ ec ∈ elems.zip mid, σ'.cls ec.1 = some ec.2 := by
  unfold expandA at h
  rw [List.mem_flatMap] at h
  obtain ⟨k, -, hk⟩ := h
  simp only at hk
  split_ifs at hk with h1 h2 h3
  all_goals try (simp only [List.not_mem_nil] at hk)
  cases hbe : bindElems elems ((cs.drop k).take elems.length) σ with
  | none => rw [hbe] at hk; simp at hk
  | some σ'' =>
      rw [hbe] at hk
      simp only [List.mem_singleton] at hk
      subst hk
      obtain ⟨hext, hlen, hall⟩ := bindElems_sound _ _ _ _ hbe
      have hsr := bindElems_seqRest _ _ _ _ hbe
      have hpre₁ : ∀ r, pre = some r → σ''.seqRest r = none := by
        intro r hr; rw [hsr]; exact hpre₀ r hr
      have hsuf₁ : ∀ r, suf = some r → (bindSeq pre (cs.take k) σ'').seqRest r = none := by
        intro r hr
        rw [bindSeq_seqRest_of_ne pre _ σ'' r (fun r' hr' heq => hdist r (heq ▸ hr') hr)]
        rw [hsr]; exact hsuf₀ r hr
      have hext₁ : Binding.Extends σ'' (bindSeq pre (cs.take k) σ'') := by
        cases pre with
        | none => exact Binding.Extends.refl _
        | some r => exact extends_setSeqRest_of_none (hpre₁ r rfl)
      have hext₂ : Binding.Extends (bindSeq pre (cs.take k) σ'')
          (bindSeq suf ((cs.drop k).drop elems.length) (bindSeq pre (cs.take k) σ'')) := by
        cases suf with
        | none => exact Binding.Extends.refl _
        | some r => exact extends_setSeqRest_of_none (hsuf₁ r rfl)
      refine ⟨hext.trans (hext₁.trans hext₂), cs.take k, (cs.drop k).take elems.length,
        (cs.drop k).drop elems.length, ?_, by omega, ?_, ?_, ?_⟩
      · rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
      · -- SeqRestOk for the prefix
        cases hp : pre with
        | none =>
            simp only [SeqRestOk]
            subst hp
            exact by_contra fun hne => h2 ⟨rfl, hne⟩
        | some r =>
            subst hp
            simp only [SeqRestOk]
            rw [bindSeq_seqRest_of_ne suf _ _ r (fun r' hr' heq => hdist r rfl (heq ▸ hr'))]
            simp [bindSeq, Binding.setSeqRest]
      · -- SeqRestOk for the suffix
        cases hs : suf with
        | none =>
            simp only [SeqRestOk]
            subst hs
            exact by_contra fun hne => h3 ⟨rfl, hne⟩
        | some r =>
            subst hs
            simp only [SeqRestOk]
            simp [bindSeq, Binding.setSeqRest]
      · intro ec hec
        rw [bindSeq_cls, bindSeq_cls]
        exact hall ec hec

/-- Lemma 7 (`expand_a_complete`), proved. -/
theorem expand_a_complete' (pre suf : Option Var) (elems : List Var)
    (u mid v : List C) (σ σ' : Binding)
    (hext : Binding.Extends σ σ')
    (hlen : mid.length = elems.length)
    (hpre : SeqRestOk σ' pre u) (hsuf : SeqRestOk σ' suf v)
    (hcls : ∀ ec ∈ elems.zip mid, σ'.cls ec.1 = some ec.2) :
    ∃ σ'' ∈ expandA pre elems suf (u ++ mid ++ v) σ,
      Binding.Extends σ'' σ' := by
  obtain ⟨σ₁, hbe, hext₁⟩ := bindElems_complete elems mid σ σ' hext hlen.symm hcls
  refine ⟨bindSeq suf v (bindSeq pre u σ₁), ?_, ?_⟩
  · unfold expandA
    rw [List.mem_flatMap]
    refine ⟨u.length, by simp, ?_⟩
    have hu : (u ++ mid ++ v).take u.length = u := by
      rw [List.append_assoc, List.take_left]
    have hd : (u ++ mid ++ v).drop u.length = mid ++ v := by
      rw [List.append_assoc, List.drop_left]
    have hm : (mid ++ v).take elems.length = mid := by
      rw [← hlen, List.take_left]
    have hv : (mid ++ v).drop elems.length = v := by
      rw [← hlen, List.drop_left]
    have hpu : ¬ (pre.isNone ∧ u ≠ []) := by
      cases pre with
      | none => simp only [SeqRestOk] at hpre; simp [hpre]
      | some r => simp
    have hsv : ¬ (suf.isNone ∧ v ≠ []) := by
      cases suf with
      | none => simp only [SeqRestOk] at hsuf; simp [hsuf]
      | some r => simp
    simp only [hu, hd, hm, hv, hlen, ne_eq, not_true_eq_false, ite_false, hpu, hsv, hbe,
      List.mem_singleton]
  · have h₁ : Binding.Extends (bindSeq pre u σ₁) σ' := by
      cases pre with
      | none => exact hext₁
      | some r => exact extends_setSeqRest_left hext₁ hpre
    cases suf with
    | none => exact h₁
    | some r => exact extends_setSeqRest_left h₁ hsuf

end Semper.EMatch
