import SemperProofs.EMatch.Main
import SemperProofs.EMatch.Flatten.Enum
import SemperProofs.EMatch.Flatten.Canon

/-!
# `:flatten`: the interpreter fragment "flatten, then decompose on the view"

`FStep` extends the reference plan steps with `Step::Flatten` and the
view-reading decompositions (`schedule.rs:98-128`); `FEnv` threads the view
register file next to the binding (§5 Q13). `runFStep` is `run_step`
(`ematch.rs:1920-2047`): a `flatten` step enumerates the node's distinct
canonical views and runs the continuation once per view with the register
written; a decomposition with a view register reads the register instead
of the stored children and keeps a complete assignment only if the
register's demand accepts the classes it took (§2.2).

`flatten_ac_sound` / `flatten_ac_complete` (and the `aci`, `assoc`
analogues): the two-step fragment emits exactly the bindings of
`MatchFlat`, built from the existing decomposition lemmas
(`decompose_ac_*`, `decompose_aci_*`, `expand_a_*` of `Main.lean`) and
`views_sound` / `views_complete`.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Steps, environments, the interpreter -/

/-- The binding and the view register file. -/
structure FEnv where
  σ : Binding
  views : Nat → Option (List (C × Nat) × Demand)

/-- The graph, the index's filing predicate and the laws per operator. -/
structure FCtx where
  G : Graph
  filed : NodeId → Bool
  laws : Sym → Laws

/-- The view context of a `Flatten` step for operator `f` and kind `κ`. -/
def FCtx.ctx (c : FCtx) (f : Sym) (κ : FlatKind) : Ctx := ⟨c.G, f, κ, c.filed⟩

/-- Plan steps with the view mechanism (`schedule.rs:98-128`). -/
inductive FStep where
  | base (s : Step)
  | flatten (node : Var) (f : Sym) (κ : FlatKind) (out : Nat)
  | decomposeAC (node : Var) (elems : List (Var × Mult)) (rest : Option Var) (view : Nat)
  | decomposeACI (node : Var) (elems : List Var) (rest : Option Var) (view : Nat)
  | expandA (node : Var) (pre : Option Var) (elems : List Var) (suf : Option Var)
      (view : Nat)

def FEnv.setView (env : FEnv) (r : Nat) (wd : List (C × Nat) × Demand) : FEnv :=
  { env with views := Function.update env.views r (some wd) }

def FEnv.withBinding (env : FEnv) (σ : Binding) : FEnv := { env with σ := σ }

/-- `run_step` with views. A decomposition reading a register never written
emits nothing (`ematch.rs:1980, 2005, 2036`). -/
def runFStep (c : FCtx) : FStep → FEnv → List FEnv
  | .base s, env => (runStep c.G s env.σ).map env.withBinding
  | .flatten v f κ out, env =>
      match env.σ.nodeOf c.G v with
      | some n => (enumerate (c.ctx f κ) (c.laws f) n).map (env.setView out)
      | none => []
  | .decomposeAC _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeAC elems rest w env.σ).filter
            (fun σ' => d.acceptsB (takenOf σ' (elems.map Prod.fst)))).map env.withBinding
      | none => []
  | .decomposeACI _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeACI elems rest (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsB (takenOf σ' elems))).map env.withBinding
      | none => []
  | .expandA _ pre elems suf r, env =>
      match env.views r with
      | some (w, d) =>
          ((expandA pre elems suf (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsB (takenOf σ' elems))).map env.withBinding
      | none => []

/-- Depth-first search over a plan with views. -/
def runF (c : FCtx) : List FStep → FEnv → List FEnv
  | [], env => [env]
  | s :: ss, env => (runFStep c s env).flatMap (runF c ss)

/-! ## Helpers -/

theorem mem_runF_two {c : FCtx} {s₁ s₂ : FStep} {env env' : FEnv} :
    env' ∈ runF c [s₁, s₂] env ↔
      ∃ env₁ ∈ runFStep c s₁ env, env' ∈ runFStep c s₂ env₁ := by
  simp [runF]

theorem mem_flatten_step {c : FCtx} {v : Var} {f : Sym} {κ : FlatKind} {r : Nat}
    {env env₁ : FEnv} {n : Node} (hn : env.σ.nodeOf c.G v = some n) :
    env₁ ∈ runFStep c (.flatten v f κ r) env ↔
      ∃ wd ∈ enumerate (c.ctx f κ) (c.laws f) n, env₁ = env.setView r wd := by
  simp only [runFStep, hn, List.mem_map]
  constructor
  · rintro ⟨wd, h, rfl⟩; exact ⟨wd, h, rfl⟩
  · rintro ⟨wd, h, rfl⟩; exact ⟨wd, h, rfl⟩

@[simp] theorem setView_views_self (env : FEnv) (r : Nat) (wd : List (C × Nat) × Demand) :
    (env.setView r wd).views r = some wd := by
  simp [FEnv.setView]

@[simp] theorem setView_σ (env : FEnv) (r : Nat) (wd : List (C × Nat) × Demand) :
    (env.setView r wd).σ = env.σ := rfl

@[simp] theorem withBinding_σ (env : FEnv) (σ : Binding) :
    (env.withBinding σ).σ = σ := rfl

theorem matchC_var_iff {G : Graph} {x : Var} {c : C} {σ : Binding} :
    MatchC G (.var x) c σ ↔ σ.cls x = some c := by
  constructor
  · intro h
    cases h with
    | var h => exact h
    | app _ _ hhead _ => simp [Pat.head] at hhead
  · exact MatchC.var

theorem takenOf_eq_of_zip {σ : Binding} :
    ∀ (xs : List Var) (cs : List C), cs.length = xs.length →
      (∀ ec ∈ xs.zip cs, σ.cls ec.1 = some ec.2) → takenOf σ xs = cs
  | [], [], _, _ => rfl
  | x :: xs, c :: cs, hlen, h => by
      have ih := takenOf_eq_of_zip xs cs (by simpa using hlen)
        (fun ec hec => h ec (by simp [hec]))
      simp only [takenOf] at ih ⊢
      simp [h (x, c) (by simp), ih]
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

theorem zip_map_fst {es : List (Var × Mult)} {taken : List C} {σ : Binding}
    (h : ∀ et ∈ es.zip taken, σ.cls et.1.1 = some et.2) :
    ∀ ec ∈ (es.map Prod.fst).zip taken, σ.cls ec.1 = some ec.2 := by
  intro ec hec
  rw [List.zip_map_left, List.mem_map] at hec
  obtain ⟨et, het, rfl⟩ := hec
  simpa using h et het

/-- The element patterns of an AC decomposition step: its class variables. -/
def acPats (es : List (Var × Mult)) : List (Pat × Mult) :=
  es.map (fun e => (.var e.1, e.2))

theorem acPats_zip_matchC {G : Graph} {es : List (Var × Mult)} {taken : List C}
    {σ : Binding} :
    (∀ et ∈ (acPats es).zip taken, MatchC G et.1.1 et.2 σ) ↔
      ∀ et ∈ es.zip taken, σ.cls et.1.1 = some et.2 := by
  unfold acPats
  rw [List.zip_map_left]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp [matchC_var_iff]

theorem acPats_zip_multOk {es : List (Var × Mult)} {taken : List C} {σ : Binding}
    {m : Multiset C} :
    (∀ et ∈ (acPats es).zip taken, MultOk σ et.1.2 (m.count et.2)) ↔
      ∀ et ∈ es.zip taken, MultOk σ et.1.2 (m.count et.2) := by
  unfold acPats
  rw [List.zip_map_left]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp

theorem varPats_zip_matchC {G : Graph} {xs : List Var} {taken : List C} {σ : Binding} :
    (∀ pc ∈ (xs.map Pat.var).zip taken, MatchC G pc.1 pc.2 σ) ↔
      ∀ ec ∈ xs.zip taken, σ.cls ec.1 = some ec.2 := by
  rw [List.zip_map_left]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp [matchC_var_iff]

theorem bound_of_zip {σ : Binding} :
    ∀ (xs : List Var) (cs : List C), cs.length = xs.length →
      (∀ ec ∈ xs.zip cs, σ.cls ec.1 = some ec.2) → ∀ x ∈ xs, ∃ c, σ.cls x = some c
  | [], _, _, _ => by simp
  | x :: xs, c :: cs, hlen, h => by
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨c, h (y, c) (by simp)⟩
      · exact bound_of_zip xs cs (by simpa using hlen) (fun ec hec => h ec (by simp [hec])) y hy
  | _ :: _, [], hlen, _ => by simp at hlen

theorem takenOf_extends {σ σ' : Binding} (hext : Binding.Extends σ σ') :
    ∀ (xs : List Var), (∀ x ∈ xs, ∃ c, σ.cls x = some c) → takenOf σ xs = takenOf σ' xs
  | [], _ => rfl
  | x :: xs, hb => by
      obtain ⟨c, hc⟩ := hb x (by simp)
      have ih := takenOf_extends hext xs (fun y hy => hb y (by simp [hy]))
      simp only [takenOf] at ih ⊢
      simp [hc, hext.1 x c hc, ih]

/-- The two `taken` lists of a binding and an extension agree on the item
variables bound by the first. -/
theorem taken_unique {σ σ' : Binding} (hext : Binding.Extends σ σ') {xs : List Var}
    {t t' : List C} (ht : t.length = xs.length) (ht' : t'.length = xs.length)
    (h : ∀ ec ∈ xs.zip t, σ.cls ec.1 = some ec.2)
    (h' : ∀ ec ∈ xs.zip t', σ'.cls ec.1 = some ec.2) : takenOf σ xs = t' := by
  rw [takenOf_extends hext xs (bound_of_zip xs t ht h)]
  exact takenOf_eq_of_zip xs t' ht' h'

/-! ## `MatchV` against `MatchN` -/

theorem MatchV.toMatchN {G : Graph} {P : Pat} {ch : Children} {σ : Binding}
    {taken : List C} {f : Sym} (h : MatchV G P ch σ taken) (hf : P.head = some f) :
    MatchN G P ⟨f, ch⟩ σ := by
  cases h with
  | assoc hlen hpre hsuf hargs =>
      simp only [Pat.head, Option.some.injEq] at hf; subst hf
      exact MatchN.assoc hlen hpre hsuf hargs
  | ac hnd hlen hmem hcls hmult hrest =>
      simp only [Pat.head, Option.some.injEq] at hf; subst hf
      exact MatchN.ac hnd hlen hmem hcls hmult hrest
  | aci hnd hlen hmem hcls hrest =>
      simp only [Pat.head, Option.some.injEq] at hf; subst hf
      exact MatchN.aci hnd hlen hmem hcls hrest

theorem MatchN.toMatchV_assoc {G : Graph} {f : Sym} {pre suf : Option Var} {args : List Pat}
    {ch : Children} {σ : Binding} (h : MatchN G (.assoc f pre args suf) ⟨f, ch⟩ σ) :
    ∃ taken, MatchV G (.assoc f pre args suf) ch σ taken := by
  cases h with
  | assoc hlen hpre hsuf hargs => exact ⟨_, MatchV.assoc hlen hpre hsuf hargs⟩

theorem MatchN.toMatchV_ac {G : Graph} {f : Sym} {elems : List (Pat × Mult)}
    {rest : Option Var} {ch : Children} {σ : Binding}
    (h : MatchN G (.ac f elems rest) ⟨f, ch⟩ σ) :
    ∃ taken, MatchV G (.ac f elems rest) ch σ taken := by
  cases h with
  | ac hnd hlen hmem hcls hmult hrest => exact ⟨_, MatchV.ac hnd hlen hmem hcls hmult hrest⟩

theorem MatchN.toMatchV_aci {G : Graph} {f : Sym} {elems : List Pat}
    {rest : Option Var} {ch : Children} {σ : Binding}
    (h : MatchN G (.aci f elems rest) ⟨f, ch⟩ σ) :
    ∃ taken, MatchV G (.aci f elems rest) ch σ taken := by
  cases h with
  | aci hnd hlen hmem hcls hrest => exact ⟨_, MatchV.aci hnd hlen hmem hcls hrest⟩

/-! ## AC -/

/-- Soundness: every binding the fragment emits for an AC atom is a
`MatchFlat` binding at the node bound to `v`. Hypothesis: the rest
variable is unbound on entry (as for `decompose_ac_sound`). -/
theorem flatten_ac_sound (c : FCtx) (v v' : Var) (f : Sym) (es : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env env' : FEnv) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.rest r = none)
    (h : env' ∈ runF c [.flatten v f .ac r, .decomposeAC v' es rest r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlat (c.ctx f .ac) (c.laws f) (.ac f (acPats es) rest) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runF_two.1 h
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flatten_step hn).1 h₁
  simp only [runFStep, setView_views_self, List.mem_map, List.mem_filter,
    setView_σ] at h₂
  obtain ⟨σ', ⟨hσ', hacc⟩, rfl⟩ := h₂
  have hviews := views_sound hwd
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hviews.1
  have hent : Multiset.entries (ofEntries w) = w := normalize_ac_entries hn₀
  rw [← hent] at hσ'
  obtain ⟨hext, taken, hnd, hlen, hmem, hcls, hmult, hrest⟩ :=
    decompose_ac_sound es rest (ofEntries w) env.σ σ' hfresh hσ'
  have htaken : takenOf σ' (es.map Prod.fst) = taken :=
    takenOf_eq_of_zip _ _ (by simpa using hlen.symm) (zip_map_fst hcls)
  refine ⟨hext, w, hviews.1, taken, ?_, ?_⟩
  · exact MatchV.ac hnd (by simpa [acPats] using hlen) hmem (acPats_zip_matchC.2 hcls)
      (acPats_zip_multOk.2 hmult) hrest
  · rw [htaken, Demand.acceptsB_iff] at hacc
    exact (accepts_iff_altsAccept hwd taken).1 hacc

/-- Completeness: every `MatchFlat` binding for an AC atom is emitted by
the fragment, up to extension. -/
theorem flatten_ac_complete (c : FCtx) (v v' : Var) (f : Sym) (es : List (Var × Mult))
    (rest : Option Var) (r : Nat) (env : FEnv) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.rest r = none)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlat (c.ctx f .ac) (c.laws f) (.ac f (acPats es) rest) n σ') :
    ∃ env'' ∈ runF c [.flatten v f .ac r, .decomposeAC v' es rest r] env,
      Binding.Extends env''.σ σ' := by
  obtain ⟨w, hw, taken, hmv, halts⟩ := hm
  obtain ⟨d, hwd⟩ := mem_enumerate_iff.2 hw
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hw
  have hent : Multiset.entries (ofEntries w) = w := normalize_ac_entries hn₀
  cases hmv with
  | ac hnd hlen hmem hcls hmult hrest =>
    have hcls' := acPats_zip_matchC.1 hcls
    have hmult' := acPats_zip_multOk.1 hmult
    obtain ⟨σ'', hσ'', hext'⟩ := decompose_ac_complete es rest (ofEntries w) env.σ σ' taken
      hext hnd (by simpa [acPats] using hlen) hmem hcls' hmult' hrest
    obtain ⟨-, taken'', -, hlen'', -, hcls'', -, -⟩ :=
      decompose_ac_sound es rest (ofEntries w) env.σ σ'' hfresh hσ''
    rw [hent] at hσ''
    refine ⟨(env.setView r (w, d)).withBinding σ'', ?_, hext'⟩
    rw [mem_runF_two]
    refine ⟨env.setView r (w, d), (mem_flatten_step hn).2 ⟨(w, d), hwd, rfl⟩, ?_⟩
    simp only [runFStep, setView_views_self, List.mem_map, List.mem_filter, setView_σ]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' (es.map Prod.fst) = taken :=
      taken_unique hext' (by simpa using hlen''.symm) (by simpa [acPats] using hlen.symm)
        (zip_map_fst hcls'') (zip_map_fst hcls')
    rw [htaken, Demand.acceptsB_iff]
    exact (accepts_iff_altsAccept hwd taken).2 halts

/-! ## ACI -/

theorem flatten_aci_sound (c : FCtx) (v v' : Var) (f : Sym) (es : List Var)
    (rest : Option Var) (r : Nat) (env env' : FEnv) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.finRest r = none)
    (h : env' ∈ runF c [.flatten v f .aci r, .decomposeACI v' es rest r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlat (c.ctx f .aci) (c.laws f) (.aci f (es.map Pat.var) rest) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runF_two.1 h
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flatten_step hn).1 h₁
  simp only [runFStep, setView_views_self, List.mem_map, List.mem_filter,
    setView_σ] at h₂
  obtain ⟨σ', ⟨hσ', hacc⟩, rfl⟩ := h₂
  have hviews := views_sound hwd
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hviews.1
  have hsort := normalize_aci_sort hn₀
  rw [← hsort] at hσ'
  obtain ⟨hext, taken, hnd, hlen, hmem, hcls, hrest⟩ :=
    decompose_aci_sound es rest _ env.σ σ' hfresh hσ'
  have htaken : takenOf σ' es = taken := takenOf_eq_of_zip _ _ hlen.symm hcls
  refine ⟨hext, w, hviews.1, taken, ?_, ?_⟩
  · exact MatchV.aci hnd (by simpa using hlen) hmem (varPats_zip_matchC.2 hcls) hrest
  · rw [htaken, Demand.acceptsB_iff] at hacc
    exact (accepts_iff_altsAccept hwd taken).1 hacc

theorem flatten_aci_complete (c : FCtx) (v v' : Var) (f : Sym) (es : List Var)
    (rest : Option Var) (r : Nat) (env : FEnv) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n) (hfresh : ∀ r ∈ rest, env.σ.finRest r = none)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlat (c.ctx f .aci) (c.laws f) (.aci f (es.map Pat.var) rest) n σ') :
    ∃ env'' ∈ runF c [.flatten v f .aci r, .decomposeACI v' es rest r] env,
      Binding.Extends env''.σ σ' := by
  obtain ⟨w, hw, taken, hmv, halts⟩ := hm
  obtain ⟨d, hwd⟩ := mem_enumerate_iff.2 hw
  obtain ⟨v₀, ls₀, hv₀, hn₀⟩ := hw
  have hsort := normalize_aci_sort hn₀
  cases hmv with
  | aci hnd hlen hmem hcls hrest =>
    have hcls' := varPats_zip_matchC.1 hcls
    obtain ⟨σ'', hσ'', hext'⟩ := decompose_aci_complete es rest _ env.σ σ' taken
      hext hnd (by simpa using hlen) hmem hcls' hrest
    obtain ⟨-, taken'', -, hlen'', -, hcls'', -⟩ :=
      decompose_aci_sound es rest _ env.σ σ'' hfresh hσ''
    rw [hsort] at hσ''
    refine ⟨(env.setView r (w, d)).withBinding σ'', ?_, hext'⟩
    rw [mem_runF_two]
    refine ⟨env.setView r (w, d), (mem_flatten_step hn).2 ⟨(w, d), hwd, rfl⟩, ?_⟩
    simp only [runFStep, setView_views_self, List.mem_map, List.mem_filter, setView_σ]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' es = taken :=
      taken_unique hext' hlen''.symm (by simpa using hlen.symm) hcls'' hcls'
    rw [htaken, Demand.acceptsB_iff]
    exact (accepts_iff_altsAccept hwd taken).2 halts

/-! ## Assoc -/

theorem flatten_assoc_sound (c : FCtx) (v v' : Var) (f : Sym) (pre suf : Option Var)
    (es : List Var) (r : Nat) (env env' : FEnv) (n : Node)
    (hn : env.σ.nodeOf c.G v = some n)
    (hpre₀ : ∀ r, pre = some r → env.σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → env.σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (h : env' ∈ runF c [.flatten v f .assoc r, .expandA v' pre es suf r] env) :
    Binding.Extends env.σ env'.σ ∧
      MatchFlat (c.ctx f .assoc) (c.laws f) (.assoc f pre (es.map Pat.var) suf) n env'.σ := by
  obtain ⟨env₁, h₁, h₂⟩ := mem_runF_two.1 h
  obtain ⟨⟨w, d⟩, hwd, rfl⟩ := (mem_flatten_step hn).1 h₁
  simp only [runFStep, setView_views_self, List.mem_map, List.mem_filter,
    setView_σ] at h₂
  obtain ⟨σ', ⟨hσ', hacc⟩, rfl⟩ := h₂
  have hviews := views_sound hwd
  obtain ⟨hext, u, mid, v₂, heq, hlen, hpre, hsuf, hcls⟩ :=
    expand_a_sound pre suf es _ env.σ σ' hpre₀ hsuf₀ hdist hσ'
  have htaken : takenOf σ' es = mid := takenOf_eq_of_zip _ _ hlen hcls
  refine ⟨hext, w, hviews.1, mid, ?_, ?_⟩
  · have hch : ofView (c.ctx f .assoc).κ w = .seq (u ++ mid ++ v₂) := by
      simp [ofView, FCtx.ctx, heq]
    rw [hch]
    exact MatchV.assoc (by simpa using hlen.symm) hpre hsuf (varPats_zip_matchC.2 hcls)
  · rw [htaken, Demand.acceptsB_iff] at hacc
    exact (accepts_iff_altsAccept hwd mid).1 hacc

theorem flatten_assoc_complete (c : FCtx) (v v' : Var) (f : Sym) (pre suf : Option Var)
    (es : List Var) (r : Nat) (env : FEnv) (n : Node) (σ' : Binding)
    (hn : env.σ.nodeOf c.G v = some n)
    (hpre₀ : ∀ r, pre = some r → env.σ.seqRest r = none)
    (hsuf₀ : ∀ r, suf = some r → env.σ.seqRest r = none)
    (hdist : ∀ r, pre = some r → suf ≠ some r)
    (hext : Binding.Extends env.σ σ')
    (hm : MatchFlat (c.ctx f .assoc) (c.laws f) (.assoc f pre (es.map Pat.var) suf) n σ') :
    ∃ env'' ∈ runF c [.flatten v f .assoc r, .expandA v' pre es suf r] env,
      Binding.Extends env''.σ σ' := by
  obtain ⟨w, hw, taken, hmv, halts⟩ := hm
  obtain ⟨d, hwd⟩ := mem_enumerate_iff.2 hw
  generalize hch : ofView (c.ctx f .assoc).κ w = ch at hmv
  cases hmv with
  | @assoc _ _ _ _ u _ v₂ _ hlen hpre hsuf hargs =>
    simp only [ofView, FCtx.ctx, Children.seq.injEq] at hch
    have hcls' := varPats_zip_matchC.1 hargs
    obtain ⟨σ'', hσ'', hext'⟩ := expand_a_complete pre suf es u taken v₂ env.σ σ' hext
      (by simpa using hlen.symm) hpre hsuf hcls'
    rw [← hch] at hσ''
    obtain ⟨-, u'', mid'', v₂'', -, hlen'', -, -, hcls''⟩ :=
      expand_a_sound pre suf es _ env.σ σ'' hpre₀ hsuf₀ hdist hσ''
    refine ⟨(env.setView r (w, d)).withBinding σ'', ?_, hext'⟩
    rw [mem_runF_two]
    refine ⟨env.setView r (w, d), (mem_flatten_step hn).2 ⟨(w, d), hwd, rfl⟩, ?_⟩
    simp only [runFStep, setView_views_self, List.mem_map, List.mem_filter, setView_σ]
    refine ⟨σ'', ⟨hσ'', ?_⟩, rfl⟩
    have htaken : takenOf σ'' es = taken :=
      taken_unique hext' hlen'' (by simpa using hlen.symm) hcls'' hcls'
    rw [htaken, Demand.acceptsB_iff]
    exact (accepts_iff_altsAccept hwd taken).2 halts

end Semper.EMatch.Flatten
