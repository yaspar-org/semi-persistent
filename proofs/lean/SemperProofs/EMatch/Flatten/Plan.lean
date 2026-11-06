import SemperProofs.EMatch.Flatten.PlanDefs
import SemperProofs.EMatch.Engine.SchedRun

/-!
# `:flatten` plans with several view registers: soundness and completeness

`flatten_plan_sound` / `flatten_plan_complete`: for any order of the
scanning atoms of a query (the scheduler's choice), the flattened plan
`planF` (every n-ary atom joined without `by_contains`, flattened into its
own register with the engine's pruning, decomposed on the register's view
and filtered by the engine's `Demand::accepts`) emits exactly the bindings
satisfying every atom under `AtomSatF`: an n-ary atom matches on some
canonical view of a stored node of its class whose demand accepts its item
classes, independently of the other atoms' views; a plain or `Comm` atom on
its stored node.

Per atom: `lowerF_sound` (an emitted binding satisfies `LowerSpecF`: the
lowering's frame and `AtomSatF`) and `lowerF_complete` (every extension
satisfying `AtomSatF` is reached, up to extension). The pruning is
discharged by `prune_engine` with `takenOf_takeable`: the classes a
decomposition takes lie within the `takeable` set the `Flatten` step
computed from its items.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch
open Binding (Extends)

/-! ## The interpreter -/

theorem mem_runE_cons {E : Enumerator} {c : FCtx} {s : EStep} {ss : List EStep}
    {env env' : EEnv} :
    env' ∈ runEG E c (s :: ss) env ↔ ∃ env₁ ∈ runEStepG E c s env, env' ∈ runEG E c ss env₁ := by
  simp [runEG]

theorem mem_runE_append {E : Enumerator} {c : FCtx} :
    ∀ (xs ys : List EStep) (env env' : EEnv),
      env' ∈ runEG E c (xs ++ ys) env ↔ ∃ env₁ ∈ runEG E c xs env, env' ∈ runEG E c ys env₁
  | [], ys, env, env' => by simp [runEG]
  | s :: xs, ys, env, env' => by
      simp only [List.cons_append, mem_runE_cons, mem_runE_append xs ys]
      constructor
      · rintro ⟨e1, h1, e2, h2, h3⟩; exact ⟨e2, ⟨e1, h1, h2⟩, h3⟩
      · rintro ⟨e2, ⟨e1, h1, h2⟩, h3⟩; exact ⟨e1, h1, e2, h2, h3⟩

@[simp] theorem EEnv.withBinding_σ (env : EEnv) (σ : Binding) : (env.withBinding σ).σ = σ := rfl
@[simp] theorem EEnv.setView_σ (env : EEnv) (r : Nat) (wd : List (C × Nat) × DemandL) :
    (env.setView r wd).σ = env.σ := rfl
@[simp] theorem EEnv.setView_self (env : EEnv) (r : Nat) (wd : List (C × Nat) × DemandL) :
    (env.setView r wd).views r = some wd := by simp [EEnv.setView]
@[simp] theorem EEnv.withBinding_self (env : EEnv) : env.withBinding env.σ = env := rfl
@[simp] theorem EEnv.withBinding_withBinding (env : EEnv) (σ σ' : Binding) :
    (env.withBinding σ).withBinding σ' = env.withBinding σ' := rfl

/-- A plan of reference steps runs as `run` on the binding. -/
theorem mem_runE_base {E : Enumerator} {c : FCtx} :
    ∀ (pl : Plan) (env env' : EEnv),
      env' ∈ runEG E c (pl.map .base) env ↔ ∃ σ' ∈ run c.G pl env.σ, env' = env.withBinding σ'
  | [], env, env' => by
      simp only [List.map_nil, runEG, List.mem_singleton, run]
      constructor
      · intro h; subst h; exact ⟨_, rfl, rfl⟩
      · rintro ⟨σ', h1, h2⟩; subst h1; subst h2; rfl
  | s :: pl, env, env' => by
      simp only [List.map_cons, mem_runE_cons, runEStepG, List.mem_map, mem_run_cons]
      constructor
      · rintro ⟨_, ⟨σ₁, h₁, rfl⟩, h⟩
        obtain ⟨σ', h', rfl⟩ := (mem_runE_base pl _ _).1 h
        exact ⟨σ', ⟨σ₁, h₁, h'⟩, rfl⟩
      · rintro ⟨σ', ⟨σ₁, h₁, h'⟩, rfl⟩
        exact ⟨env.withBinding σ₁, ⟨σ₁, h₁, rfl⟩, (mem_runE_base pl _ _).2 ⟨σ', h', rfl⟩⟩

/-! ## The join, `takeable`, the pruned enumeration -/

/-- The flattened join is the reference join of an atom with no element. -/
theorem flatJoin_eq (a : RAtom) (B : Finset Var) :
    flatJoin a B = joinLookups ⟨a.node, a.op, .ac [] none⟩ B := by
  unfold flatJoin joinLookups
  split <;> simp [extraLookups, containsLookups, RAtom.elems]

theorem takenOf_of_mapM {σ : Binding} :
    ∀ {xs : List Var} {bound : List C}, xs.mapM σ.cls = some bound → takenOf σ xs = bound
  | [], bound, h => by simp at h; subst h; rfl
  | x :: xs, bound, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind] at h
      cases hx : σ.cls x with
      | none => simp [hx] at h
      | some b =>
          cases hxs : xs.mapM σ.cls with
          | none => simp [hx, hxs] at h
          | some bs =>
              simp [hx, hxs] at h
              subst h
              simp [takenOf, hx, ← takenOf_of_mapM hxs]

theorem bound_of_mapM {σ : Binding} :
    ∀ {xs : List Var} {bound : List C}, xs.mapM σ.cls = some bound → ∀ x ∈ xs, ∃ c, σ.cls x = some c
  | [], _, _ => by simp
  | x :: xs, bound, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind] at h
      cases hx : σ.cls x with
      | none => simp [hx] at h
      | some b =>
          cases hxs : xs.mapM σ.cls with
          | none => simp [hx, hxs] at h
          | some bs =>
              intro y hy
              rcases List.mem_cons.1 hy with rfl | hy
              · exact ⟨b, hx⟩
              · exact bound_of_mapM hxs y hy

/-- The classes a decomposition takes lie in the `takeable` set the
`Flatten` step computed before it (`ematch.rs:1937-1944`). -/
theorem takenOf_takeable {σ σ' : Binding} (hext : Extends σ σ') {items : List Var}
    (hb : ∀ x ∈ items, ∃ c, σ'.cls x = some c) :
    ∀ c ∈ takenOf σ' items, takeableOf σ items c = true := by
  intro c hc
  cases h : items.mapM σ.cls with
  | none => simp [takeableOf, h]
  | some bound =>
    rw [← takenOf_extends hext items (bound_of_mapM h), takenOf_of_mapM h] at hc
    simpa [takeableOf, h] using hc

theorem mem_enumeratePrunedE {T : C → Bool} {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumeratePrunedE T ctx laws n) :
    ∃ v ls o, RawViewL ctx n v ls o ∧ normalize ctx.κ laws v = .node w := by
  unfold enumeratePrunedE at h
  obtain ⟨⟨ls, hr⟩, -⟩ := mem_enumerateFromL.1 h
  obtain ⟨v, ls', o, hv, hn, -⟩ := mem_rawRecordsL.1 (List.mem_filter.1 hr).1
  exact ⟨v, ls', o, hv, hn⟩

/-- Soundness of the pruned view: it is a view of the full enumeration with a
demand accepting the same `taken`. -/
theorem pruned_to_full {T : C → Bool} {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : DemandL} {taken : List C} (hT : ∀ c ∈ taken, T c = true)
    (h : (w, d) ∈ enumeratePrunedE T ctx laws n) (hacc : d.acceptsE ctx.κ taken) :
    ∃ d', (w, d') ∈ enumerateL ctx laws n ∧ d'.acceptsE ctx.κ taken :=
  (prune_engine T ctx laws n w taken hT).1 ⟨d, h, hacc⟩

theorem full_to_pruned {T : C → Bool} {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : DemandL} {taken : List C} (hT : ∀ c ∈ taken, T c = true)
    (h : (w, d) ∈ enumerateL ctx laws n) (hacc : d.acceptsE ctx.κ taken) :
    ∃ d', (w, d') ∈ enumeratePrunedE T ctx laws n ∧ d'.acceptsE ctx.κ taken :=
  (prune_engine T ctx laws n w taken hT).2 ⟨d, h, hacc⟩

/-- What the plan theorems need of an enumeration: every view is a
normalization result, and the pruned enumeration accepts a `taken` set of
classes bound to the items exactly when the full one does. -/
structure Enumerator.Spec (E : Enumerator) : Prop where
  normal : ∀ {ctx : Ctx} {laws : Laws} {items : List Var} {n : Node} {w : List (C × Nat)}
    {d : DemandL}, (w, d) ∈ E.full ctx laws items n → ∃ v, normalize ctx.κ laws v = .node w
  normalP : ∀ {ctx : Ctx} {laws : Laws} {σ : Binding} {items : List Var} {n : Node}
    {w : List (C × Nat)} {d : DemandL}, (w, d) ∈ E.pruned ctx laws σ items n →
      ∃ v, normalize ctx.κ laws v = .node w
  to_full : ∀ {ctx : Ctx} {laws : Laws} {σ σ' : Binding} {items : List Var} {n : Node}
    {w : List (C × Nat)} {d : DemandL}, Extends σ σ' → (∀ x ∈ items, ∃ c, σ'.cls x = some c) →
      (w, d) ∈ E.pruned ctx laws σ items n → d.acceptsE ctx.κ (takenOf σ' items) →
      ∃ d', (w, d') ∈ E.full ctx laws items n ∧ d'.acceptsE ctx.κ (takenOf σ' items)
  to_pruned : ∀ {ctx : Ctx} {laws : Laws} {σ σ' : Binding} {items : List Var} {n : Node}
    {w : List (C × Nat)} {d : DemandL}, Extends σ σ' → (∀ x ∈ items, ∃ c, σ'.cls x = some c) →
      (w, d) ∈ E.full ctx laws items n → d.acceptsE ctx.κ (takenOf σ' items) →
      ∃ d', (w, d') ∈ E.pruned ctx laws σ items n ∧ d'.acceptsE ctx.κ (takenOf σ' items)

/-- The opening walk meets the specification (`prune_engine`, `takenOf_takeable`). -/
theorem Enumerator.base_spec : Enumerator.base.Spec where
  normal h := by
    obtain ⟨v, -, -, hn⟩ := (views_soundL h).1
    exact ⟨v, hn⟩
  normalP h := by
    obtain ⟨v, -, -, -, hn⟩ := mem_enumeratePrunedE h
    exact ⟨v, hn⟩
  to_full hext hb h hacc := pruned_to_full (takenOf_takeable hext hb) h hacc
  to_pruned hext hb h hacc := full_to_pruned (takenOf_takeable hext hb) h hacc

/-! ## The specification of one flattened lowering -/

/-- `LowerSpec` with the flattened semantics of the atom. -/
structure LowerSpecF (E : Enumerator) (c : FCtx) (a : RAtom) (B : Finset Var) (σ σ' : Binding) : Prop where
  ext : Extends σ σ'
  clsDom : ClsDom σ' (B ∪ a.binds)
  node : ∀ v, v ≠ a.node → σ'.node v = σ.node v
  mult : ∀ k, k ∉ a.multVars → σ'.mult k = σ.mult k
  rest : ∀ r, r ∉ a.msetRestVars → σ'.rest r = σ.rest r
  seqRest : ∀ r, r ∉ a.seqRestVars → σ'.seqRest r = σ.seqRest r
  finRest : ∀ r, r ∉ a.setRestVars → σ'.finRest r = σ.finRest r
  sat : AtomSatG E c σ' a

theorem atomSatF_of_none {E : Enumerator} {c : FCtx} {σ : Binding} {a : RAtom}
    (h : a.shape.flatKind = none) : AtomSatG E c σ a ↔ AtomSat c.G σ a := by
  unfold AtomSatG; rw [h]

theorem LowerSpec.toF {E : Enumerator} {c : FCtx} {a : RAtom} {B : Finset Var} {σ σ' : Binding}
    (h : LowerSpec c.G a B σ σ') (hk : a.shape.flatKind = none) : LowerSpecF E c a B σ σ' :=
  ⟨h.ext, h.clsDom, h.node, h.mult, h.rest, h.seqRest, h.finRest, (atomSatF_of_none hk).2 h.sat⟩

/-- The frame part of a flattened n-ary lowering (`lowerSpec_of_frame`
without the satisfaction). -/
theorem lowerSpecF_of_frame {E : Enumerator} {c : FCtx} {σ σ' : Binding} {n : Var} {f : Sym} {sh : Shape}
    {B : Finset Var} {id : NodeId} {ks rs ss fs : List Var}
    (hdom : ClsDom σ B) (hn : σ.node n = none)
    (hc : σ.cls n = none ∨ σ.cls n = some (c.G.find id))
    (hfr : Frame (RAtom.elems ⟨n, f, sh⟩) ks rs ss fs (joinBind c.G σ n id) σ')
    (hks : ∀ k ∈ ks, k ∈ RAtom.multVars ⟨n, f, sh⟩)
    (hrs : ∀ r ∈ rs, r ∈ RAtom.msetRestVars ⟨n, f, sh⟩)
    (hss : ∀ r ∈ ss, r ∈ RAtom.seqRestVars ⟨n, f, sh⟩)
    (hfs : ∀ r ∈ fs, r ∈ RAtom.setRestVars ⟨n, f, sh⟩)
    (hext : Extends (joinBind c.G σ n id) σ')
    (hall : ∀ x ∈ RAtom.elems ⟨n, f, sh⟩, ∃ c', σ'.cls x = some c')
    (hsat : AtomSatG E c σ' ⟨n, f, sh⟩) :
    LowerSpecF E c ⟨n, f, sh⟩ B σ σ' where
  ext := (extends_joinBind_of_cls hn hc).trans hext
  clsDom := clsDom_congr (clsDom_of_frame hfr (clsDom_joinBind hdom) hall) (binds_eq n f sh B).symm
  node v hv := by rw [hfr.node, joinBind_node_of_ne _ _ _ _ _ hv]
  mult k hk := hfr.mult k (fun h => hk (hks k h))
  rest r hr := hfr.rest r (fun h => hr (hrs r h))
  seqRest r hr := hfr.seqRest r (fun h => hr (hss r h))
  finRest r hr := hfr.finRest r (fun h => hr (hfs r h))
  sat := hsat

/-- The three steps of a flattened n-ary lowering, unfolded. -/
theorem mem_lowerF_nary {E : Enumerator} {c : FCtx} {env env' : EEnv} {n : Var} {f : Sym} {B : Finset Var}
    {κ : FlatKind} {r : Nat} {items : List Var} {s : EStep} :
    env' ∈ runEG E c [.base (.join n (flatJoin ⟨n, f, .ac [] none⟩ B)), .flatten n f κ r items, s]
        env ↔
      ∃ id ∈ candidates c.G env.σ (joinLookups ⟨n, f, .ac [] none⟩ B),
        ∃ n' wd, (joinBind c.G env.σ n id).nodeOf c.G n = some n' ∧
          wd ∈ E.pruned (c.ctx f κ) (c.laws f) (joinBind c.G env.σ n id) items n' ∧
          env' ∈ runEStepG E c s ((env.withBinding (joinBind c.G env.σ n id)).setView r wd) := by
  have hj : flatJoin ⟨n, f, .ac [] none⟩ B = joinLookups ⟨n, f, .ac [] none⟩ B := flatJoin_eq _ _
  rw [mem_runE_cons]
  constructor
  · rintro ⟨env₁, h₁, h⟩
    rw [mem_runE_cons] at h
    obtain ⟨env₂, h₂, h⟩ := h
    rw [mem_runE_cons] at h
    obtain ⟨env₃, h₃, h⟩ := h
    simp only [runEG, List.mem_singleton] at h
    subst h
    simp only [runEStepG, List.mem_map] at h₁
    obtain ⟨σ₁, hσ₁, rfl⟩ := h₁
    rw [runStep_join_mem, hj] at hσ₁
    obtain ⟨id, hid, rfl⟩ := hσ₁
    simp only [runEStepG, EEnv.withBinding_σ] at h₂
    revert h₂
    cases hn' : (joinBind c.G env.σ n id).nodeOf c.G n with
    | none => simp
    | some n' =>
        intro h₂
        obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 h₂
        exact ⟨id, hid, n', wd, hn', hwd, h₃⟩
  · rintro ⟨id, hid, n', wd, hn', hwd, h₃⟩
    refine ⟨env.withBinding (joinBind c.G env.σ n id), ?_, ?_⟩
    · simp only [runEStepG, List.mem_map]
      exact ⟨_, by rw [runStep_join_mem, hj]; exact ⟨id, hid, rfl⟩, rfl⟩
    · rw [mem_runE_cons]
      refine ⟨(env.withBinding (joinBind c.G env.σ n id)).setView r wd, ?_, ?_⟩
      · simp only [runEStepG, EEnv.withBinding_σ, hn']
        exact List.mem_map.2 ⟨wd, hwd, rfl⟩
      · rw [mem_runE_cons]
        exact ⟨env', h₃, by simp [runEG]⟩

/-! ## AC -/

theorem lowerF_sound_ac {E : Enumerator} (hE : E.Spec) {c : FCtx} {env env' : EEnv} {n : Var} {f : Sym} {es : List (Var × Mult)}
    {rest : Option Var} {B : Finset Var} {r : Nat} (hk : c.G.KeysNodup) (hdom : ClsDom env.σ B)
    (hn : env.σ.node n = none) (hrf : RAtom.RestFresh ⟨n, f, .ac es rest⟩ env.σ)
    (h : env' ∈ runEG E c (lowerF ⟨n, f, .ac es rest⟩ B r) env) :
    LowerSpecF E c ⟨n, f, .ac es rest⟩ B env.σ env'.σ := by
  have hj : flatJoin ⟨n, f, .ac es rest⟩ B = flatJoin ⟨n, f, .ac [] none⟩ B := rfl
  simp only [lowerF, hj] at h
  obtain ⟨id, hid, n', ⟨w, d⟩, hn', hwd, h₃⟩ := mem_lowerF_nary.1 h
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hn'
  obtain rfl := Option.some.inj hn'
  simp only [runEStepG, EEnv.setView_self, List.mem_map, List.mem_filter, EEnv.setView_σ,
    EEnv.withBinding_σ] at h₃
  obtain ⟨σ', ⟨hd, hacc⟩, rfl⟩ := h₃
  simp only [EEnv.withBinding_σ]
  obtain ⟨v₀, hn₀⟩ := hE.normalP hwd
  have hent : Multiset.entries (ofEntries w) = w := normalize_ac_entries hn₀
  obtain ⟨-, hr, -, -⟩ := hrf
  simp only [RAtom.msetRestVars] at hr
  have hfresh : ∀ r ∈ rest, (joinBind c.G env.σ n id).rest r = none := by
    intro r hr'; exact hr r (Option.mem_toList.2 hr')
  rw [← hent] at hd
  obtain ⟨hext, taken, hnd, hlen, hmem', hcls, hmult, hrest⟩ :=
    decompose_ac_sound' es rest (ofEntries w) _ _ hfresh hd
  have hfr := frame_decomposeAC es rest _ _ _ hd
  have hbound : ∀ x ∈ es.map Prod.fst, ∃ c', σ'.cls x = some c' := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e he
    exact ⟨t, hcls (e, t) ht⟩
  rw [DemandL.acceptsEB_iff] at hacc
  obtain ⟨d', hd', hacc'⟩ := hE.to_full hext hbound hwd hacc
  refine lowerSpecF_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    (by simpa [RAtom.elems] using hbound) ?_
  refine ⟨id, nd, hext.2.1 _ _ (joinBind_node_self _ _ _ _), hmem,
    hext.1 _ _ (joinBind_cls_self _ _ _ _), hop, w, d', hd', ?_, ?_⟩
  · exact matchN_ac_vars.2 ⟨ofEntries w, taken, rfl, hnd, hlen, hmem', hcls, hmult, hrest⟩
  · show DemandL.acceptsE .ac d' (takenOf σ' (es.map Prod.fst))
    exact hacc'

theorem lowerF_complete_ac {E : Enumerator} (hE : E.Spec) {c : FCtx} {env : EEnv} {σ' : Binding} {n : Var} {f : Sym}
    {es : List (Var × Mult)} {rest : Option Var} {B : Finset Var} {r : Nat}
    (hk : c.G.KeysNodup) (hdom : ClsDom env.σ B) (hrf : RAtom.RestFresh ⟨n, f, .ac es rest⟩ env.σ)
    (hext : Extends env.σ σ') (hsat : AtomSatG E c σ' ⟨n, f, .ac es rest⟩) :
    ∃ env₁ ∈ runEG E c (lowerF ⟨n, f, .ac es rest⟩ B r) env, Extends env₁.σ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, w, d, hwd, hm, hacc⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨m, taken, hch, hnd, hlen, hmem', hcl, hmult, hrest⟩ := matchN_ac_vars.1 hm
  simp only at hnode hcls hop
  simp only [ofView, Node.mk.injEq, Children.mset.injEq, true_and] at hch
  subst hch
  obtain ⟨v₀, hn₀⟩ := hE.normal hwd
  have hent : Multiset.entries (ofEntries w) = w := normalize_ac_entries hn₀
  have hjoin : id ∈ candidates c.G env.σ (joinLookups ⟨n, f, .ac [] none⟩ B) :=
    join_lower_complete hdom hext hmem hop hcls (by simp [extraLookups, containsLookups, RAtom.elems])
  have hext₁ : Extends (joinBind c.G env.σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨-, hr, -, -⟩ := hrf
  simp only [RAtom.msetRestVars] at hr
  have hfresh : ∀ r ∈ rest, (joinBind c.G env.σ n id).rest r = none := by
    intro r hr'; exact hr r (Option.mem_toList.2 hr')
  obtain ⟨σ₁, h₁, hext'⟩ :=
    decompose_ac_complete' es rest (ofEntries w) _ _ taken hext₁ hnd hlen hmem' hcl hmult hrest
  obtain ⟨-, taken₁, -, hlen₁, -, hcls₁, -, -⟩ :=
    decompose_ac_sound' es rest (ofEntries w) _ _ hfresh h₁
  have hbound : ∀ x ∈ es.map Prod.fst, ∃ c', σ'.cls x = some c' := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e he
    exact ⟨t, hcl (e, t) ht⟩
  have hb₁ : ∀ x ∈ es.map Prod.fst, ∃ c', σ₁.cls x = some c' := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen₁ e he
    exact ⟨t, hcls₁ (e, t) ht⟩
  have htk : takenOf σ₁ (es.map Prod.fst) = takenOf σ' (es.map Prod.fst) :=
    takenOf_extends hext' _ hb₁
  have hacc₀ : d.acceptsE (c.ctx f .ac).κ (takenOf σ' (es.map Prod.fst)) := hacc
  obtain ⟨d', hd', hacc'⟩ := hE.to_pruned hext₁ hbound hwd hacc₀
  refine ⟨((env.withBinding (joinBind c.G env.σ n id)).setView r (w, d')).withBinding σ₁, ?_, hext'⟩
  have hj : flatJoin ⟨n, f, .ac es rest⟩ B = flatJoin ⟨n, f, .ac [] none⟩ B := rfl
  simp only [lowerF, hj]
  rw [mem_lowerF_nary]
  refine ⟨id, hjoin, nd, (w, d'), nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem, hd', ?_⟩
  simp only [runEStepG, EEnv.setView_self, List.mem_map, List.mem_filter, EEnv.setView_σ,
    EEnv.withBinding_σ]
  refine ⟨σ₁, ⟨by rw [hent] at h₁; exact h₁, ?_⟩, rfl⟩
  rw [DemandL.acceptsEB_iff, htk]
  exact hacc'

/-! ## ACI -/

theorem lowerF_sound_aci {E : Enumerator} (hE : E.Spec) {c : FCtx} {env env' : EEnv} {n : Var} {f : Sym} {es : List Var}
    {rest : Option Var} {B : Finset Var} {r : Nat} (hk : c.G.KeysNodup) (hdom : ClsDom env.σ B)
    (hn : env.σ.node n = none) (hrf : RAtom.RestFresh ⟨n, f, .aci es rest⟩ env.σ)
    (h : env' ∈ runEG E c (lowerF ⟨n, f, .aci es rest⟩ B r) env) :
    LowerSpecF E c ⟨n, f, .aci es rest⟩ B env.σ env'.σ := by
  have hj : flatJoin ⟨n, f, .aci es rest⟩ B = flatJoin ⟨n, f, .ac [] none⟩ B := rfl
  simp only [lowerF, hj] at h
  obtain ⟨id, hid, n', ⟨w, d⟩, hn', hwd, h₃⟩ := mem_lowerF_nary.1 h
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hn'
  obtain rfl := Option.some.inj hn'
  simp only [runEStepG, EEnv.setView_self, List.mem_map, List.mem_filter, EEnv.setView_σ,
    EEnv.withBinding_σ] at h₃
  obtain ⟨σ', ⟨hd, hacc⟩, rfl⟩ := h₃
  simp only [EEnv.withBinding_σ]
  obtain ⟨v₀, hn₀⟩ := hE.normalP hwd
  have hsort := normalize_aci_sort hn₀
  obtain ⟨-, -, hr, -⟩ := hrf
  simp only [RAtom.setRestVars] at hr
  have hfresh : ∀ r ∈ rest, (joinBind c.G env.σ n id).finRest r = none := by
    intro r hr'; exact hr r (Option.mem_toList.2 hr')
  rw [← hsort] at hd
  obtain ⟨hext, taken, hnd, hlen, hmem', hcls, hrest⟩ :=
    decompose_aci_sound' es rest _ _ _ hfresh hd
  have hfr := frame_decomposeACI es rest _ _ _ hd
  have hbound : ∀ x ∈ es, ∃ c', σ'.cls x = some c' := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen x hx
    exact ⟨t, hcls (x, t) ht⟩
  rw [DemandL.acceptsEB_iff] at hacc
  obtain ⟨d', hd', hacc'⟩ := hE.to_full hext hbound hwd hacc
  refine lowerSpecF_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    (by simpa [RAtom.elems] using hbound) ?_
  refine ⟨id, nd, hext.2.1 _ _ (joinBind_node_self _ _ _ _), hmem,
    hext.1 _ _ (joinBind_cls_self _ _ _ _), hop, w, d', hd', ?_, ?_⟩
  · exact matchN_aci_vars.2 ⟨_, taken, rfl, hnd, hlen, hmem', hcls, hrest⟩
  · show DemandL.acceptsE .aci d' (takenOf σ' es)
    exact hacc'

theorem lowerF_complete_aci {E : Enumerator} (hE : E.Spec) {c : FCtx} {env : EEnv} {σ' : Binding} {n : Var} {f : Sym}
    {es : List Var} {rest : Option Var} {B : Finset Var} {r : Nat}
    (hk : c.G.KeysNodup) (hdom : ClsDom env.σ B) (hrf : RAtom.RestFresh ⟨n, f, .aci es rest⟩ env.σ)
    (hext : Extends env.σ σ') (hsat : AtomSatG E c σ' ⟨n, f, .aci es rest⟩) :
    ∃ env₁ ∈ runEG E c (lowerF ⟨n, f, .aci es rest⟩ B r) env, Extends env₁.σ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, w, d, hwd, hm, hacc⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨st, taken, hch, hnd, hlen, hmem', hcl, hrest⟩ := matchN_aci_vars.1 hm
  simp only at hnode hcls hop
  simp only [ofView, Node.mk.injEq, Children.set.injEq, true_and] at hch
  subst hch
  obtain ⟨v₀, hn₀⟩ := hE.normal hwd
  have hsort := normalize_aci_sort hn₀
  have hjoin : id ∈ candidates c.G env.σ (joinLookups ⟨n, f, .ac [] none⟩ B) :=
    join_lower_complete hdom hext hmem hop hcls (by simp [extraLookups, containsLookups, RAtom.elems])
  have hext₁ : Extends (joinBind c.G env.σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨-, -, hr, -⟩ := hrf
  simp only [RAtom.setRestVars] at hr
  have hfresh : ∀ r ∈ rest, (joinBind c.G env.σ n id).finRest r = none := by
    intro r hr'; exact hr r (Option.mem_toList.2 hr')
  obtain ⟨σ₁, h₁, hext'⟩ :=
    decompose_aci_complete' es rest _ _ _ taken hext₁ hnd hlen hmem' hcl hrest
  obtain ⟨-, taken₁, -, hlen₁, -, hcls₁, -⟩ := decompose_aci_sound' es rest _ _ _ hfresh h₁
  have hbound : ∀ x ∈ es, ∃ c', σ'.cls x = some c' := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen x hx
    exact ⟨t, hcl (x, t) ht⟩
  have hb₁ : ∀ x ∈ es, ∃ c', σ₁.cls x = some c' := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen₁ x hx
    exact ⟨t, hcls₁ (x, t) ht⟩
  have htk : takenOf σ₁ es = takenOf σ' es := takenOf_extends hext' _ hb₁
  have hacc₀ : d.acceptsE (c.ctx f .aci).κ (takenOf σ' es) := hacc
  obtain ⟨d', hd', hacc'⟩ := hE.to_pruned hext₁ hbound hwd hacc₀
  refine ⟨((env.withBinding (joinBind c.G env.σ n id)).setView r (w, d')).withBinding σ₁, ?_, hext'⟩
  have hj : flatJoin ⟨n, f, .aci es rest⟩ B = flatJoin ⟨n, f, .ac [] none⟩ B := rfl
  simp only [lowerF, hj]
  rw [mem_lowerF_nary]
  refine ⟨id, hjoin, nd, (w, d'), nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem, hd', ?_⟩
  simp only [runEStepG, EEnv.setView_self, List.mem_map, List.mem_filter, EEnv.setView_σ,
    EEnv.withBinding_σ]
  refine ⟨σ₁, ⟨by rw [hsort] at h₁; exact h₁, ?_⟩, rfl⟩
  rw [DemandL.acceptsEB_iff, htk]
  exact hacc'

/-! ## Assoc -/

theorem lowerF_sound_assoc {E : Enumerator} (hE : E.Spec) {c : FCtx} {env env' : EEnv} {n : Var} {f : Sym}
    {pre suf : Option Var} {fx : List Var} {B : Finset Var} {r : Nat} (hk : c.G.KeysNodup)
    (hdom : ClsDom env.σ B) (hn : env.σ.node n = none)
    (hrf : RAtom.RestFresh ⟨n, f, .assoc pre fx suf⟩ env.σ)
    (h : env' ∈ runEG E c (lowerF ⟨n, f, .assoc pre fx suf⟩ B r) env) :
    LowerSpecF E c ⟨n, f, .assoc pre fx suf⟩ B env.σ env'.σ := by
  have hj : flatJoin ⟨n, f, .assoc pre fx suf⟩ B = flatJoin ⟨n, f, .ac [] none⟩ B := rfl
  simp only [lowerF, hj] at h
  obtain ⟨id, hid, n', ⟨w, d⟩, hn', hwd, h₃⟩ := mem_lowerF_nary.1 h
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hn'
  obtain rfl := Option.some.inj hn'
  simp only [runEStepG, EEnv.setView_self, List.mem_map, List.mem_filter, EEnv.setView_σ,
    EEnv.withBinding_σ] at h₃
  obtain ⟨σ', ⟨hd, hacc⟩, rfl⟩ := h₃
  simp only [EEnv.withBinding_σ]
  obtain ⟨hs, -, -, hnd'⟩ := hrf
  simp only [RAtom.seqRestVars] at hs hnd'
  have hpre₀ : ∀ r, pre = some r → (joinBind c.G env.σ n id).seqRest r = none := by
    intro r hr; subst hr; exact hs r (by simp)
  have hsuf₀ : ∀ r, suf = some r → (joinBind c.G env.σ n id).seqRest r = none := by
    intro r hr; subst hr; exact hs r (by simp)
  have hdist : ∀ r, pre = some r → suf ≠ some r := by
    intro r hr hs'; subst hr; subst hs'; simp at hnd'
  obtain ⟨hext, u, mid, v, hcs, hlen, hpre, hsuf, hcls⟩ :=
    expand_a_sound' pre suf fx _ _ _ hpre₀ hsuf₀ hdist hd
  have hfr := frame_expandA hd
  have hf₂ : List.Forall₂ (fun x c => σ'.cls x = some c) fx mid :=
    List.forall₂_iff_zip.2 ⟨hlen.symm, fun hab => hcls _ hab⟩
  have hbound : ∀ x ∈ fx, ∃ c', σ'.cls x = some c' := by
    intro x hx
    obtain ⟨b, -, hb⟩ := forall₂_exists_right hf₂ x hx
    exact ⟨b, hb⟩
  rw [DemandL.acceptsEB_iff] at hacc
  obtain ⟨d', hd', hacc'⟩ := hE.to_full hext hbound hwd hacc
  refine lowerSpecF_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    (by simpa [RAtom.elems] using hbound) ?_
  refine ⟨id, nd, hext.2.1 _ _ (joinBind_node_self _ _ _ _), hmem,
    hext.1 _ _ (joinBind_cls_self _ _ _ _), hop, w, d', hd', ?_, ?_⟩
  · have hch : ofView .assoc w = .seq (u ++ mid ++ v) := by simp [ofView, hcs]
    rw [hch]
    exact matchN_assoc_vars.2 ⟨u, mid, v, rfl, hpre, hsuf, hf₂⟩
  · show DemandL.acceptsE .assoc d' (takenOf σ' fx)
    exact hacc'

theorem lowerF_complete_assoc {E : Enumerator} (hE : E.Spec) {c : FCtx} {env : EEnv} {σ' : Binding} {n : Var} {f : Sym}
    {pre suf : Option Var} {fx : List Var} {B : Finset Var} {r : Nat}
    (hk : c.G.KeysNodup) (hdom : ClsDom env.σ B)
    (hrf : RAtom.RestFresh ⟨n, f, .assoc pre fx suf⟩ env.σ)
    (hext : Extends env.σ σ') (hsat : AtomSatG E c σ' ⟨n, f, .assoc pre fx suf⟩) :
    ∃ env₁ ∈ runEG E c (lowerF ⟨n, f, .assoc pre fx suf⟩ B r) env, Extends env₁.σ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, w, d, hwd, hm, hacc⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨u, mid, v, hch, hpre, hsuf, hf₂⟩ := matchN_assoc_vars.1 hm
  simp only at hnode hcls hop
  simp only [ofView, Node.mk.injEq, Children.seq.injEq, true_and] at hch
  have hjoin : id ∈ candidates c.G env.σ (joinLookups ⟨n, f, .ac [] none⟩ B) :=
    join_lower_complete hdom hext hmem hop hcls (by simp [extraLookups, containsLookups, RAtom.elems])
  have hext₁ : Extends (joinBind c.G env.σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨hs, -, -, hnd'⟩ := hrf
  simp only [RAtom.seqRestVars] at hs hnd'
  have hpre₀ : ∀ r, pre = some r → (joinBind c.G env.σ n id).seqRest r = none := by
    intro r hr; subst hr; exact hs r (by simp)
  have hsuf₀ : ∀ r, suf = some r → (joinBind c.G env.σ n id).seqRest r = none := by
    intro r hr; subst hr; exact hs r (by simp)
  have hdist : ∀ r, pre = some r → suf ≠ some r := by
    intro r hr hs'; subst hr; subst hs'; simp at hnd'
  obtain ⟨σ₁, h₁, hext'⟩ := expand_a_complete' pre suf fx u mid v _ _ hext₁ hf₂.length_eq.symm
    hpre hsuf (fun ec hec => (List.forall₂_iff_zip.1 hf₂).2 hec)
  obtain ⟨-, u₁, mid₁, v₁, -, hlen₁, -, -, hcls₁⟩ :=
    expand_a_sound' pre suf fx _ _ _ hpre₀ hsuf₀ hdist h₁
  have hbound : ∀ x ∈ fx, ∃ c', σ'.cls x = some c' := by
    intro x hx
    obtain ⟨b, -, hb⟩ := forall₂_exists_right hf₂ x hx
    exact ⟨b, hb⟩
  have hb₁ : ∀ x ∈ fx, ∃ c', σ₁.cls x = some c' := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen₁.symm x hx
    exact ⟨t, hcls₁ (x, t) ht⟩
  have htk : takenOf σ₁ fx = takenOf σ' fx := takenOf_extends hext' _ hb₁
  have hacc₀ : d.acceptsE (c.ctx f .assoc).κ (takenOf σ' fx) := hacc
  obtain ⟨d', hd', hacc'⟩ := hE.to_pruned hext₁ hbound hwd hacc₀
  refine ⟨((env.withBinding (joinBind c.G env.σ n id)).setView r (w, d')).withBinding σ₁, ?_, hext'⟩
  have hj : flatJoin ⟨n, f, .assoc pre fx suf⟩ B = flatJoin ⟨n, f, .ac [] none⟩ B := rfl
  simp only [lowerF, hj]
  rw [mem_lowerF_nary]
  refine ⟨id, hjoin, nd, (w, d'), nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem, hd', ?_⟩
  simp only [runEStepG, EEnv.setView_self, List.mem_map, List.mem_filter, EEnv.setView_σ,
    EEnv.withBinding_σ]
  refine ⟨σ₁, ⟨by rw [hch]; exact h₁, ?_⟩, rfl⟩
  rw [DemandL.acceptsEB_iff, htk]
  exact hacc'

/-! ## Any atom -/

/-- **Soundness of one flattened lowering.** -/
theorem lowerF_sound {E : Enumerator} (hE : E.Spec) {c : FCtx} {sig : Sym → Kind} {env env' : EEnv} {a : RAtom} {B : Finset Var}
    {r : Nat} (hk : c.G.KeysNodup) (hconf : c.G.Conforms sig) (hwk : a.WK sig)
    (hdom : ClsDom env.σ B) (hn : env.σ.node a.node = none) (hrf : a.RestFresh env.σ)
    (h : env' ∈ runEG E c (lowerF a B r) env) : LowerSpecF E c a B env.σ env'.σ := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | assoc pre fx suf => exact lowerF_sound_assoc hE hk hdom hn hrf h
  | ac es rest => exact lowerF_sound_ac hE hk hdom hn hrf h
  | aci es rest => exact lowerF_sound_aci hE hk hdom hn hrf h
  | plain cs =>
      simp only [lowerF] at h
      obtain ⟨σ', h', rfl⟩ := (mem_runE_base _ _ _).1 h
      exact LowerSpec.toF (lower_sound hk hconf hwk hdom hn hrf h') rfl
  | comm x y =>
      simp only [lowerF] at h
      obtain ⟨σ', h', rfl⟩ := (mem_runE_base _ _ _).1 h
      exact LowerSpec.toF (lower_sound hk hconf hwk hdom hn hrf h') rfl

/-- **Completeness of one flattened lowering.** -/
theorem lowerF_complete {E : Enumerator} (hE : E.Spec) {c : FCtx} {env : EEnv} {σ' : Binding} {a : RAtom} {B : Finset Var}
    {r : Nat} (hk : c.G.KeysNodup) (hdom : ClsDom env.σ B) (hrf : a.RestFresh env.σ)
    (hext : Extends env.σ σ') (hsat : AtomSatG E c σ' a) :
    ∃ env₁ ∈ runEG E c (lowerF a B r) env, Extends env₁.σ σ' := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | assoc pre fx suf => exact lowerF_complete_assoc hE hk hdom hrf hext hsat
  | ac es rest => exact lowerF_complete_ac hE hk hdom hrf hext hsat
  | aci es rest => exact lowerF_complete_aci hE hk hdom hrf hext hsat
  | plain cs =>
      obtain ⟨σ₁, h₁, hext₁⟩ := lower_complete hk hdom hext ((atomSatF_of_none rfl).1 hsat)
      exact ⟨env.withBinding σ₁, (mem_runE_base _ _ _).2 ⟨σ₁, h₁, rfl⟩, hext₁⟩
  | comm x y =>
      obtain ⟨σ₁, h₁, hext₁⟩ := lower_complete hk hdom hext ((atomSatF_of_none rfl).1 hsat)
      exact ⟨env.withBinding σ₁, (mem_runE_base _ _ _).2 ⟨σ₁, h₁, rfl⟩, hext₁⟩

/-! ## Monotonicity -/

theorem elems_bound_of_matchN {G : Graph} {a : RAtom} {nd : Node} {σ : Binding}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) (h : MatchN G a.shallow nd σ) :
    ∀ x ∈ a.elems, ∃ c, σ.cls x = some c := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | plain cs => simp [Shape.flatKind] at hκ
  | comm x y => simp [Shape.flatKind] at hκ
  | assoc pre fx suf =>
      simp only [RAtom.shallow] at h
      obtain ⟨u, mid, v, -, -, -, hf₂⟩ := matchN_assoc_vars.1 h
      intro x hx
      obtain ⟨b, -, hb⟩ := forall₂_exists_right hf₂ x (by simpa [RAtom.elems] using hx)
      exact ⟨b, hb⟩
  | ac es rest =>
      simp only [RAtom.shallow] at h
      obtain ⟨m, taken, -, -, hlen, -, hcls, -, -⟩ := matchN_ac_vars.1 h
      intro x hx
      simp only [RAtom.elems, List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e he
      exact ⟨t, hcls (e, t) ht⟩
  | aci es rest =>
      simp only [RAtom.shallow] at h
      obtain ⟨st, taken, -, -, hlen, -, hcls, -⟩ := matchN_aci_vars.1 h
      intro x hx
      obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen x (by simpa [RAtom.elems] using hx)
      exact ⟨t, hcls (x, t) ht⟩

theorem AtomSatG.mono {E : Enumerator} {c : FCtx} {σ σ' : Binding} {a : RAtom} (h : AtomSatG E c σ a)
    (hext : Extends σ σ') : AtomSatG E c σ' a := by
  unfold AtomSatG at h ⊢
  cases hκ : a.shape.flatKind with
  | none => rw [hκ] at h; exact AtomSat.mono h hext
  | some κ =>
      rw [hκ] at h
      obtain ⟨id, nd, hn, hmem, hc, hop, w, d, hwd, hm, hacc⟩ := h
      refine ⟨id, nd, hext.2.1 _ _ hn, hmem, hext.1 _ _ hc, hop, w, d, hwd, hm.mono hext, ?_⟩
      have hb := elems_bound_of_matchN (nd := ⟨a.op, ofView κ w⟩) hκ hm
      rw [← takenOf_extends hext _ hb]
      exact hacc

/-! ## Plans -/

/-- The variables bound after a plan: `B` and every atom's `binds`. -/
def planBound : List RAtom → Finset Var → Finset Var
  | [], B => B
  | a :: as, B => planBound as (B ∪ a.binds)

/-- The hypotheses of the per-atom theorems along a plan: distinct node ids,
nodes conform to the kind signature and every atom is well-kinded, every
atom's node and rest variables are unbound, node variables are distinct and
rest variables are distinct across the query (rest-variable linearity). -/
structure PlanFWF (c : FCtx) (sig : Sym → Kind) (as : List RAtom) (σ : Binding) : Prop where
  keys : c.G.KeysNodup
  conf : c.G.Conforms sig
  wk : ∀ a ∈ as, a.WK sig
  nodeFresh : ∀ a ∈ as, σ.node a.node = none
  nodesNodup : (as.map RAtom.node).Nodup
  restFresh : ∀ a ∈ as, a.RestFresh σ
  restsNodup : (as.flatMap RAtom.restVars).Nodup

theorem PlanFWF.tail {E : Enumerator} {c : FCtx} {sig : Sym → Kind} {a : RAtom} {as : List RAtom} {B : Finset Var}
    {σ σ' : Binding} (hw : PlanFWF c sig (a :: as) σ) (hs : LowerSpecF E c a B σ σ') :
    PlanFWF c sig as σ' := by
  have hnd := hw.nodesNodup
  simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
  have hrd := hw.restsNodup
  simp only [List.flatMap_cons, List.nodup_append] at hrd
  obtain ⟨-, hrd', hdisj⟩ := hrd
  have hnot : ∀ a' ∈ as, ∀ x ∈ a'.restVars, x ∉ a.restVars := by
    intro a' ha' x hx hxa
    exact hdisj x hxa x (List.mem_flatMap.2 ⟨a', ha', hx⟩) rfl
  refine ⟨hw.keys, hw.conf, fun a' h => hw.wk a' (List.mem_cons_of_mem _ h), ?_, hnd.2, ?_, hrd'⟩
  · intro a' ha'
    have hne : a'.node ≠ a.node := fun h => hnd.1 ⟨a', ha', h⟩
    rw [hs.node _ hne]
    exact hw.nodeFresh a' (List.mem_cons_of_mem _ ha')
  · intro a' ha'
    obtain ⟨h1, h2, h3, h4⟩ := hw.restFresh a' (List.mem_cons_of_mem _ ha')
    refine ⟨?_, ?_, ?_, h4⟩
    · intro x hx
      rw [hs.seqRest x (fun h => hnot a' ha' x (by simp [RAtom.restVars, hx])
        (by simp [RAtom.restVars, h]))]
      exact h1 x hx
    · intro x hx
      rw [hs.rest x (fun h => hnot a' ha' x (by simp [RAtom.restVars, hx])
        (by simp [RAtom.restVars, h]))]
      exact h2 x hx
    · intro x hx
      rw [hs.finRest x (fun h => hnot a' ha' x (by simp [RAtom.restVars, hx])
        (by simp [RAtom.restVars, h]))]
      exact h3 x hx

/-- Soundness of a flattened plan, any atom order and any start. -/
theorem planF_sound {E : Enumerator} (hE : E.Spec) {c : FCtx} {sig : Sym → Kind} :
    ∀ (as : List RAtom) (B : Finset Var) (r : Nat) (env env' : EEnv),
      PlanFWF c sig as env.σ → ClsDom env.σ B → env' ∈ runEG E c (planF as B r) env →
      Extends env.σ env'.σ ∧ ClsDom env'.σ (planBound as B) ∧ ∀ a ∈ as, AtomSatG E c env'.σ a
  | [], B, r, env, env', _, hdom, h => by
      simp only [planF, runEG, List.mem_singleton] at h
      subst h
      exact ⟨Extends.refl _, hdom, by simp⟩
  | a :: as, B, r, env, env', hw, hdom, h => by
      simp only [planF] at h
      obtain ⟨env₁, h₁, h₂⟩ := (mem_runE_append _ _ _ _).1 h
      have hs := lowerF_sound hE hw.keys hw.conf (hw.wk a (List.mem_cons_self ..)) hdom
        (hw.nodeFresh a (List.mem_cons_self ..)) (hw.restFresh a (List.mem_cons_self ..)) h₁
      obtain ⟨hext, hdom', hsat⟩ := planF_sound hE as _ _ env₁ env' (hw.tail hs) hs.clsDom h₂
      refine ⟨hs.ext.trans hext, hdom', ?_⟩
      intro a' ha'
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact AtomSatG.mono hs.sat hext
      · exact hsat a' ha'

/-- Completeness of a flattened plan, any atom order and any start. -/
theorem planF_complete {E : Enumerator} (hE : E.Spec) {c : FCtx} {sig : Sym → Kind} :
    ∀ (as : List RAtom) (B : Finset Var) (r : Nat) (env : EEnv) (σ' : Binding),
      PlanFWF c sig as env.σ → ClsDom env.σ B → Extends env.σ σ' →
      (∀ a ∈ as, AtomSatG E c σ' a) →
      ∃ env' ∈ runEG E c (planF as B r) env, Extends env'.σ σ'
  | [], B, r, env, σ', _, _, hext, _ => ⟨env, by simp [planF, runEG], hext⟩
  | a :: as, B, r, env, σ', hw, hdom, hext, hsat => by
      obtain ⟨env₁, h₁, hext₁⟩ := lowerF_complete hE (r := r) hw.keys hdom
        (hw.restFresh a (List.mem_cons_self ..)) hext (hsat a (List.mem_cons_self ..))
      have hs := lowerF_sound hE hw.keys hw.conf (hw.wk a (List.mem_cons_self ..)) hdom
        (hw.nodeFresh a (List.mem_cons_self ..)) (hw.restFresh a (List.mem_cons_self ..)) h₁
      obtain ⟨env', h', hext'⟩ := planF_complete hE as (B ∪ a.binds) (r + regsOf a) env₁ σ'
        (hw.tail hs) hs.clsDom hext₁ (fun a' ha' => hsat a' (List.mem_cons_of_mem _ ha'))
      exact ⟨env', by simp only [planF]; exact (mem_runE_append _ _ _ _).2 ⟨env₁, h₁, h'⟩, hext'⟩

/-! ## The main theorems: from the empty environment -/

/-- The plan-level hypotheses at the empty binding. -/
structure QueryFWF (c : FCtx) (sig : Sym → Kind) (as : List RAtom) : Prop where
  keys : c.G.KeysNodup
  conf : c.G.Conforms sig
  wk : ∀ a ∈ as, a.WK sig
  nodesNodup : (as.map RAtom.node).Nodup
  seqNodup : ∀ a ∈ as, a.seqRestVars.Nodup
  restsNodup : (as.flatMap RAtom.restVars).Nodup

theorem QueryFWF.planFWF {c : FCtx} {sig : Sym → Kind} {as : List RAtom} (h : QueryFWF c sig as) :
    PlanFWF c sig as EEnv.empty.σ :=
  ⟨h.keys, h.conf, h.wk, fun _ _ => rfl, h.nodesNodup,
    fun a ha => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, h.seqNodup a ha⟩, h.restsNodup⟩

theorem clsDom_empty : ClsDom EEnv.empty.σ ∅ := by
  intro x; simp [EEnv.empty, Binding.empty]

/-- Soundness of a flattened plan from the empty environment, for any
enumeration meeting `Enumerator.Spec`. -/
theorem flatten_plan_sound_of_spec {E : Enumerator} (hE : E.Spec) {c : FCtx} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {env' : EEnv}
    (h : env' ∈ runEG E c (planF as ∅ r) EEnv.empty) :
    (∀ a ∈ as, AtomSatG E c env'.σ a) ∧ ClsDom env'.σ (planBound as ∅) := by
  obtain ⟨-, hdom, hsat⟩ := planF_sound hE as ∅ r _ _ hw.planFWF clsDom_empty h
  exact ⟨hsat, hdom⟩

/-- Completeness of a flattened plan from the empty environment, for any
enumeration meeting `Enumerator.Spec`. -/
theorem flatten_plan_complete_of_spec {E : Enumerator} (hE : E.Spec) {c : FCtx}
    {sig : Sym → Kind} {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG E c σ' a) :
    ∃ env' ∈ runEG E c (planF as ∅ r) EEnv.empty, Extends env'.σ σ' := by
  refine planF_complete hE as ∅ r _ σ' hw.planFWF clsDom_empty ?_ hsat
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro x y h <;> simp [EEnv.empty, Binding.empty] at h

/-- **Soundness of a flattened plan with several view registers.** For any
order of the query's atoms, every binding the flattened plan emits from the
empty environment satisfies every atom under `AtomSatF` (each n-ary atom
through a view of its own node accepted by its own demand) and binds
exactly the atoms' class variables. -/
theorem flatten_plan_sound {c : FCtx} {sig : Sym → Kind} {as : List RAtom} (r : Nat)
    (hw : QueryFWF c sig as) {env' : EEnv} (h : env' ∈ runE c (planF as ∅ r) EEnv.empty) :
    (∀ a ∈ as, AtomSatF c env'.σ a) ∧ ClsDom env'.σ (planBound as ∅) :=
  flatten_plan_sound_of_spec Enumerator.base_spec r hw h

/-- **Completeness of a flattened plan with several view registers**
(`flatten_plan_complete`). For any order of the query's atoms, every binding
that satisfies every atom under `AtomSatF` (each n-ary atom matched on any
view of a node of its class, accepted by that view's demand) is emitted by
the flattened plan, up to extension: the emitted binding agrees with it on
every variable the emitted binding binds, which are exactly the atoms'
variables (`flatten_plan_sound`). -/
theorem flatten_plan_complete {c : FCtx} {sig : Sym → Kind} {as : List RAtom} (r : Nat)
    (hw : QueryFWF c sig as) {σ' : Binding} (hsat : ∀ a ∈ as, AtomSatF c σ' a) :
    ∃ env' ∈ runE c (planF as ∅ r) EEnv.empty, Extends env'.σ σ' :=
  flatten_plan_complete_of_spec Enumerator.base_spec r hw hsat

end Semper.EMatch.Flatten
