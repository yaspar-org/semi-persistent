import SemperProofs.EMatch.Engine.Atoms

/-!
# Lowering one atom (spec-scheduler §2, §3.2)

`lower a B` is the step list the scheduler emits for a scanning atom `a`
under the bound set `B` (`schedule.rs`, `emit_atom` / `try_eager_lower` /
`emit_variadic_join`), as a pure function of `(a, B)`:

* the join `join n ls`: `[byRepr n, byOp f]` when the node variable is
  already bound (the class re-join), else `byOp f` followed by one lookup per
  bound child (`byChildPos` for a plain atom, `byContains` for a variadic
  one);
* then, for a plain atom, the child loop (`extractChild` for an unbound
  child, `checkChildEq` for a bound or repeated one), and for a variadic
  atom its decomposition step.

Deviation from the spec (recorded in `engine-lean-status.md`): a `Comm` atom
emits no `byContains` lookup, because the model's `by_contains` index files
only sequence, multiset and set nodes (`Children.isVariadic`), whereas the
engine also files sorted pairs. The `:flatten` views are not modelled.

The main theorem `lower_sound_complete` characterises `run G (lower a B) σ`
exactly: the emitted bindings are the extensions of `σ` that satisfy the
atom, bind exactly `B ∪ binds a` as classes, and write nothing outside the
atom's node, multiplicity and rest variables.
-/

namespace Semper.EMatch

open Binding (Extends)

/-! ## The lowering -/

/-- `byChildPos i c` for every bound child `c` at position `i`. -/
def childLookups : List Var → Nat → Finset Var → List Lookup
  | [], _, _ => []
  | c :: cs, i, B =>
      (if c ∈ B then [Lookup.byChildPos i c] else []) ++ childLookups cs (i + 1) B

/-- `byContains e` for every bound element `e`. -/
def containsLookups (es : List Var) (B : Finset Var) : List Lookup :=
  es.filterMap (fun e => if e ∈ B then some (Lookup.byContains e) else none)

/-- The bound-variable lookups added to `byOp` when the node is unbound. -/
def extraLookups (a : RAtom) (B : Finset Var) : List Lookup :=
  match a.shape with
  | .plain cs => childLookups cs 0 B
  | .comm _ _ => []
  | _ => containsLookups a.elems B

/-- The lookups of the atom's join (spec §2.3, first three rows). -/
def joinLookups (a : RAtom) (B : Finset Var) : List Lookup :=
  if a.node ∈ B then [.byRepr a.node, .byOp a.op]
  else .byOp a.op :: extraLookups a B

/-- The child loop of a plain atom (`emit_read_children`): a child that is
unbound so far is extracted and becomes bound; a bound one is checked. -/
def childSteps (n : Var) : List Var → Nat → Finset Var → Plan
  | [], _, _ => []
  | c :: cs, i, B =>
      if c ∈ B then .checkChildEq n i c :: childSteps n cs (i + 1) B
      else .extractChild n i c :: childSteps n cs (i + 1) (insert c B)

/-- The steps after the join. -/
def lowerBody (a : RAtom) (B : Finset Var) : Plan :=
  match a.shape with
  | .plain cs => childSteps a.node cs 0 (insert a.node B)
  | .comm x y => [.decomposeComm a.node x y]
  | .assoc pre fx suf => [.expandA a.node pre fx suf]
  | .ac es rest => [.decomposeAC a.node es rest]
  | .aci es rest => [.decomposeACI a.node es rest]

/-- `lower a B` (spec §2.3). -/
def lower (a : RAtom) (B : Finset Var) : Plan :=
  .join a.node (joinLookups a B) :: lowerBody a B

/-! ## The specification of one lowering -/

/-- `ClsDom σ B`: the class map of `σ` is bound exactly on `B`. -/
def ClsDom (σ : Binding) (B : Finset Var) : Prop := ∀ x, x ∈ B ↔ ∃ c, σ.cls x = some c

/-- The rest variables of the atom are unbound (rest-variable linearity,
`R:931-969`) and its prefix and suffix rests are distinct. -/
def RAtom.RestFresh (a : RAtom) (σ : Binding) : Prop :=
  (∀ r ∈ a.seqRestVars, σ.seqRest r = none) ∧ (∀ r ∈ a.msetRestVars, σ.rest r = none) ∧
    (∀ r ∈ a.setRestVars, σ.finRest r = none) ∧ a.seqRestVars.Nodup

/-- The kind of an atom's shape. -/
def Shape.kind : Shape → Kind
  | .plain cs => .plain cs.length
  | .comm _ _ => .comm
  | .assoc _ _ _ => .assoc
  | .ac _ _ => .ac
  | .aci _ _ => .aci

/-- The atom uses the shape of its operator's kind (the resolver's check). -/
def RAtom.WK (sig : Sym → Kind) (a : RAtom) : Prop := sig a.op = a.shape.kind

/-- What `run G (lower a B) σ` emits (spec §3.2, `lower_sound_complete`):
an extension of `σ` satisfying the atom, with classes bound exactly on
`B ∪ binds a`, the node map changed only at the atom's node variable, and
the multiplicity and rest maps changed only at the atom's own variables. -/
structure LowerSpec (G : Graph) (a : RAtom) (B : Finset Var) (σ σ' : Binding) : Prop where
  ext : Extends σ σ'
  clsDom : ClsDom σ' (B ∪ a.binds)
  node : ∀ v, v ≠ a.node → σ'.node v = σ.node v
  mult : ∀ k, k ∉ a.multVars → σ'.mult k = σ.mult k
  rest : ∀ r, r ∉ a.msetRestVars → σ'.rest r = σ.rest r
  seqRest : ∀ r, r ∉ a.seqRestVars → σ'.seqRest r = σ.seqRest r
  finRest : ∀ r, r ∉ a.setRestVars → σ'.finRest r = σ.finRest r
  sat : AtomSat G σ' a

/-! ## Inversion of `MatchN` on shallow patterns -/

theorem matchC_var_iff {G : Graph} {x : Var} {c : C} {σ : Binding} :
    MatchC G (.var x) c σ ↔ σ.cls x = some c := by
  constructor
  · intro h
    cases h with
    | var hx => exact hx
    | app _ _ hh _ => simp [Pat.head] at hh
  · exact MatchC.var

theorem forall₂_cls_of_zip_vars {vs : List Var} {cs : List C} {σ : Binding} {G : Graph}
    (hlen : vs.length = cs.length)
    (h : ∀ pc ∈ (vs.map Pat.var).zip cs, MatchC G pc.1 pc.2 σ) :
    List.Forall₂ (fun v c => σ.cls v = some c) vs cs := by
  rw [List.forall₂_iff_zip]
  refine ⟨hlen, fun hab => ?_⟩
  have := h _ (by rw [List.zip_map_left, List.mem_map]; exact ⟨_, hab, rfl⟩)
  exact matchC_var_iff.1 this

theorem zip_vars_of_forall₂ {vs : List Var} {cs : List C} {σ : Binding} {G : Graph}
    (h : List.Forall₂ (fun v c => σ.cls v = some c) vs cs) :
    ∀ pc ∈ (vs.map Pat.var).zip cs, MatchC G pc.1 pc.2 σ := by
  intro pc hpc
  rw [List.zip_map_left, List.mem_map] at hpc
  obtain ⟨⟨v, c⟩, hvc, rfl⟩ := hpc
  exact MatchC.var ((List.forall₂_iff_zip.1 h).2 hvc)

theorem matchN_plain_vars {G : Graph} {f : Sym} {cs : List Var} {nd : Node} {σ : Binding} :
    MatchN G (.plain f (cs.map .var)) nd σ ↔
      ∃ cs', nd = ⟨f, .tuple cs'⟩ ∧ List.Forall₂ (fun v c => σ.cls v = some c) cs cs' := by
  constructor
  · intro h
    cases h with
    | plain hl hall =>
        rename_i cs'
        exact ⟨cs', rfl, forall₂_cls_of_zip_vars (by simpa using hl) hall⟩
  · rintro ⟨cs', rfl, h⟩
    exact MatchN.plain (by simpa using h.length_eq) (zip_vars_of_forall₂ h)

theorem matchN_comm_vars {G : Graph} {f : Sym} {x y : Var} {nd : Node} {σ : Binding} :
    MatchN G (.comm f (.var x) (.var y)) nd σ ↔
      ∃ a b, nd = ⟨f, .spair a b⟩ ∧
        ((σ.cls x = some a ∧ σ.cls y = some b) ∨ (σ.cls x = some b ∧ σ.cls y = some a)) := by
  constructor
  · intro h
    cases h with
    | comm₁ hp hq => exact ⟨_, _, rfl, Or.inl ⟨matchC_var_iff.1 hp, matchC_var_iff.1 hq⟩⟩
    | comm₂ hp hq => exact ⟨_, _, rfl, Or.inr ⟨matchC_var_iff.1 hp, matchC_var_iff.1 hq⟩⟩
  · rintro ⟨a, b, rfl, h | h⟩
    · exact MatchN.comm₁ (MatchC.var h.1) (MatchC.var h.2)
    · exact MatchN.comm₂ (MatchC.var h.1) (MatchC.var h.2)

theorem matchN_assoc_vars {G : Graph} {f : Sym} {pre suf : Option Var} {fx : List Var}
    {nd : Node} {σ : Binding} :
    MatchN G (.assoc f pre (fx.map .var) suf) nd σ ↔
      ∃ u mid v, nd = ⟨f, .seq (u ++ mid ++ v)⟩ ∧ SeqRestOk σ pre u ∧ SeqRestOk σ suf v ∧
        List.Forall₂ (fun x c => σ.cls x = some c) fx mid := by
  constructor
  · intro h
    cases h with
    | assoc hl hpre hsuf hall =>
        exact ⟨_, _, _, rfl, hpre, hsuf, forall₂_cls_of_zip_vars (by simpa using hl) hall⟩
  · rintro ⟨u, mid, v, rfl, hpre, hsuf, h⟩
    exact MatchN.assoc (by simpa using h.length_eq) hpre hsuf (zip_vars_of_forall₂ h)

theorem mem_zip_map_pair {es : List (Var × Mult)} {taken : List C} {et : (Pat × Mult) × C}
    (h : et ∈ (es.map fun e => (Pat.var e.1, e.2)).zip taken) :
    ∃ e ∈ es.zip taken, et = ((Pat.var e.1.1, e.1.2), e.2) := by
  rw [List.zip_map_left, List.mem_map] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, he, rfl⟩

theorem matchN_ac_vars {G : Graph} {f : Sym} {es : List (Var × Mult)} {rest : Option Var}
    {nd : Node} {σ : Binding} :
    MatchN G (.ac f (es.map fun e => (.var e.1, e.2)) rest) nd σ ↔
      ∃ m taken, nd = ⟨f, .mset m⟩ ∧ taken.Nodup ∧ es.length = taken.length ∧
        (∀ c ∈ taken, c ∈ m) ∧ (∀ et ∈ es.zip taken, σ.cls et.1.1 = some et.2) ∧
        (∀ et ∈ es.zip taken, MultOk σ et.1.2 (m.count et.2)) ∧ MsetRestOk σ rest m taken := by
  constructor
  · intro h
    cases h with
    | ac hnd hl hmem hall hmult hrest =>
        rename_i m taken
        refine ⟨m, taken, rfl, hnd, by simpa using hl, hmem, ?_, ?_, hrest⟩
        · intro et het
          have := hall ((Pat.var et.1.1, et.1.2), et.2)
            (by rw [List.zip_map_left, List.mem_map]; exact ⟨et, het, rfl⟩)
          exact matchC_var_iff.1 this
        · intro et het
          exact hmult ((Pat.var et.1.1, et.1.2), et.2)
            (by rw [List.zip_map_left, List.mem_map]; exact ⟨et, het, rfl⟩)
  · rintro ⟨m, taken, rfl, hnd, hl, hmem, hcls, hmult, hrest⟩
    refine MatchN.ac hnd (by simpa using hl) hmem ?_ ?_ hrest
    · intro et het
      obtain ⟨e, he, rfl⟩ := mem_zip_map_pair het
      exact MatchC.var (hcls e he)
    · intro et het
      obtain ⟨e, he, rfl⟩ := mem_zip_map_pair het
      exact hmult e he

theorem matchN_aci_vars {G : Graph} {f : Sym} {es : List Var} {rest : Option Var}
    {nd : Node} {σ : Binding} :
    MatchN G (.aci f (es.map .var) rest) nd σ ↔
      ∃ s taken, nd = ⟨f, .set s⟩ ∧ taken.Nodup ∧ es.length = taken.length ∧
        (∀ c ∈ taken, c ∈ s) ∧ (∀ et ∈ es.zip taken, σ.cls et.1 = some et.2) ∧
        SetRestOk σ rest s taken := by
  constructor
  · intro h
    cases h with
    | aci hnd hl hmem hall hrest =>
        rename_i s taken
        refine ⟨s, taken, rfl, hnd, by simpa using hl, hmem, ?_, hrest⟩
        intro et het
        have := hall (Pat.var et.1, et.2)
          (by rw [List.zip_map_left, List.mem_map]; exact ⟨et, het, rfl⟩)
        exact matchC_var_iff.1 this
  · rintro ⟨s, taken, rfl, hnd, hl, hmem, hcls, hrest⟩
    refine MatchN.aci hnd (by simpa using hl) hmem ?_ hrest
    intro et het
    rw [List.zip_map_left, List.mem_map] at het
    obtain ⟨e, he, rfl⟩ := het
    exact MatchC.var (hcls e he)

/-! ## The join -/

theorem byOp_mem_joinLookups (a : RAtom) (B : Finset Var) : Lookup.byOp a.op ∈ joinLookups a B := by
  unfold joinLookups; split <;> simp

theorem mem_childLookups : ∀ {cs : List Var} {i : Nat} {B : Finset Var} {l : Lookup},
    l ∈ childLookups cs i B → ∃ j c, cs[j]? = some c ∧ c ∈ B ∧ l = .byChildPos (i + j) c := by
  intro cs
  induction cs with
  | nil => intro i B l h; simp [childLookups] at h
  | cons c cs ih =>
      intro i B l h
      simp only [childLookups, List.mem_append] at h
      rcases h with h | h
      · split at h
        · simp only [List.mem_singleton] at h
          exact ⟨0, c, rfl, by assumption, by simpa using h⟩
        · simp at h
      · obtain ⟨j, c', hj, hB, rfl⟩ := ih h
        exact ⟨j + 1, c', by simpa using hj, hB, by congr 1; omega⟩

theorem mem_containsLookups {es : List Var} {B : Finset Var} {l : Lookup}
    (h : l ∈ containsLookups es B) : ∃ e ∈ es, e ∈ B ∧ l = .byContains e := by
  simp only [containsLookups, List.mem_filterMap] at h
  obtain ⟨e, he, hl⟩ := h
  split at hl
  · exact ⟨e, he, by assumption, (Option.some.inj hl).symm⟩
  · cases hl

theorem joinBind_node (G : Graph) (σ : Binding) (t : Var) (id : NodeId) (v : Var) :
    (joinBind G σ t id).node v = if v = t then some id else σ.node v := by
  split
  · subst ‹v = t›; simp
  · simp [*]

theorem joinBind_cls (G : Graph) (σ : Binding) (t : Var) (id : NodeId) (v : Var) :
    (joinBind G σ t id).cls v = if v = t then some (G.find id) else σ.cls v := by
  split
  · subst ‹v = t›; simp
  · simp [*]

theorem extends_joinBind_of_cls {G : Graph} {σ : Binding} {n : Var} {id : NodeId}
    (hn : σ.node n = none) (hc : σ.cls n = none ∨ σ.cls n = some (G.find id)) :
    Extends σ (joinBind G σ n id) := by
  refine ⟨?_, ?_, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  · intro w c hw
    rw [joinBind_cls]
    split
    · subst ‹w = n›
      rcases hc with hc | hc
      · rw [hc] at hw; cases hw
      · rw [← hc, hw]
    · exact hw
  · intro v i hv
    rw [joinBind_node]
    split
    · subst ‹v = n›; rw [hn] at hv; cases hv
    · exact hv

theorem extends_joinBind_of_bound {G : Graph} {σ σ' : Binding} {n : Var} {id : NodeId}
    (hext : Extends σ σ') (hn : σ'.node n = some id) (hc : σ'.cls n = some (G.find id)) :
    Extends (joinBind G σ n id) σ' := by
  refine ⟨?_, ?_, hext.2.2.1, hext.2.2.2.1, hext.2.2.2.2.1, hext.2.2.2.2.2⟩
  · intro w c hw
    rw [joinBind_cls] at hw
    split at hw
    · subst ‹w = n›; rw [hc]; exact hw
    · exact hext.1 w c hw
  · intro v i hv
    rw [joinBind_node] at hv
    split at hv
    · subst ‹v = n›; rw [hn]; exact hv
    · exact hext.2.1 v i hv

theorem clsDom_joinBind {G : Graph} {σ : Binding} {B : Finset Var} {n : Var} {id : NodeId}
    (hdom : ClsDom σ B) : ClsDom (joinBind G σ n id) (insert n B) := by
  intro x
  rw [joinBind_cls, Finset.mem_insert]
  split
  · subst ‹x = n›; simp
  · rw [hdom x]; simp [*]

/-- The candidates of the atom's join: stored nodes of the atom's operator,
in the class of the node variable when it is bound. -/
theorem join_lower_sound {G : Graph} {σ : Binding} {a : RAtom} {B : Finset Var} {id : NodeId}
    (hdom : ClsDom σ B) (h : id ∈ candidates G σ (joinLookups a B)) :
    ∃ nd, (id, nd) ∈ G.nodes ∧ nd.op = a.op ∧
      (σ.cls a.node = none ∨ σ.cls a.node = some (G.find id)) := by
  rw [join_complete'] at h
  obtain ⟨-, hall⟩ := h
  obtain ⟨nd, hmem, hop⟩ := hall _ (byOp_mem_joinLookups a B)
  refine ⟨nd, hmem, hop, ?_⟩
  by_cases hn : a.node ∈ B
  · right
    have := hall (.byRepr a.node) (by simp [joinLookups, hn])
    exact this.2
  · left
    rcases hc : σ.cls a.node with _ | c
    · rfl
    · exact absurd ((hdom a.node).2 ⟨c, hc⟩) hn

theorem join_lower_complete {G : Graph} {σ σ' : Binding} {a : RAtom} {B : Finset Var}
    {id : NodeId} {nd : Node}
    (hdom : ClsDom σ B) (hext : Extends σ σ') (hmem : (id, nd) ∈ G.nodes) (hop : nd.op = a.op)
    (hcls : σ'.cls a.node = some (G.find id))
    (hextra : ∀ l ∈ extraLookups a B, l.pred G σ id) :
    id ∈ candidates G σ (joinLookups a B) := by
  rw [join_complete']
  refine ⟨⟨nd, hmem⟩, ?_⟩
  intro l hl
  unfold joinLookups at hl
  split at hl
  · rename_i hn
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨c, hc⟩ := (hdom a.node).1 hn
      have := hext.1 _ _ hc
      rw [hcls] at this
      exact ⟨⟨nd, hmem⟩, by rw [hc, this]⟩
    · exact ⟨nd, hmem, hop⟩
  · simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨nd, hmem, hop⟩
    · exact hextra l hl

theorem runStep_join_lower {G : Graph} {σ σ' : Binding} {a : RAtom} {B : Finset Var} :
    σ' ∈ runStep G (.join a.node (joinLookups a B)) σ ↔
      ∃ id ∈ candidates G σ (joinLookups a B), joinBind G σ a.node id = σ' :=
  runStep_join_mem

/-! ## Frames and domains -/

theorem clsDom_of_frame {cs ks rs ss fs : List Var} {σ σ' : Binding} {B : Finset Var}
    (hfr : Frame cs ks rs ss fs σ σ') (hdom : ClsDom σ B)
    (hall : ∀ c ∈ cs, ∃ c', σ'.cls c = some c') : ClsDom σ' (B ∪ cs.toFinset) := by
  intro x
  rw [Finset.mem_union, List.mem_toFinset]
  by_cases hx : x ∈ cs
  · simp [hx, hall x hx]
  · rw [hfr.cls x hx]
    simp [hx, hdom x]

theorem clsDom_congr {σ : Binding} {B B' : Finset Var} (h : ClsDom σ B) (hBB : B = B') :
    ClsDom σ B' := hBB ▸ h

/-! ## The child loop of a plain atom -/

theorem runStep_checkChildEq_mem {G : Graph} {v x : Var} {pos : Nat} {σ σ' : Binding}
    (h : σ' ∈ runStep G (.checkChildEq v pos x) σ) :
    σ' = σ ∧ ∃ n c, σ.nodeOf G v = some n ∧ σ.cls x = some c ∧ n.children.childAt pos = some c := by
  simp only [runStep] at h
  split at h
  · rename_i n c hn hc
    split at h
    · simp only [List.mem_singleton] at h
      exact ⟨h, n, c, hn, hc, by assumption⟩
    · simp at h
  · simp at h

theorem runStep_checkChildEq_complete {G : Graph} {v x : Var} {pos : Nat} {σ : Binding}
    {n : Node} {c : C} (hn : σ.nodeOf G v = some n) (hc : σ.cls x = some c)
    (hch : n.children.childAt pos = some c) :
    σ ∈ runStep G (.checkChildEq v pos x) σ := by
  simp [runStep, hn, hc, hch]

theorem nodeOf_setCls (G : Graph) (σ : Binding) (x : Var) (c : C) (v : Var) :
    (σ.setCls x c).nodeOf G v = σ.nodeOf G v := rfl

/-- Soundness of the child loop: every binding it emits extends the input,
writes only the children's class variables, binds every child, and binds
each child `cs[j]` to the class at position `i + j`. -/
theorem childSteps_sound {G : Graph} {n : Var} {nd : Node} :
    ∀ (cs : List Var) (i : Nat) (B : Finset Var) (σ₁ σ'' : Binding),
    σ₁.nodeOf G n = some nd → σ'' ∈ run G (childSteps n cs i B) σ₁ →
    Extends σ₁ σ'' ∧ Frame cs [] [] [] [] σ₁ σ'' ∧ (∀ c ∈ cs, ∃ c', σ''.cls c = some c') ∧
      ∀ j (hj : j < cs.length), ∃ c', nd.children.childAt (i + j) = some c' ∧
        σ''.cls cs[j] = some c' := by
  intro cs
  induction cs with
  | nil =>
      intro i B σ₁ σ'' _ h
      simp only [childSteps, run] at h
      simp only [List.mem_singleton] at h
      subst h
      exact ⟨Extends.refl _, Frame.refl _ _ _ _ _ _, by simp, by simp⟩
  | cons c cs ih =>
      intro i B σ₁ σ'' hn h
      simp only [childSteps] at h
      split at h
      · rw [mem_run_cons] at h
        obtain ⟨σm, hm, h⟩ := h
        obtain ⟨rfl, n', c', hn', hc, hch⟩ := runStep_checkChildEq_mem hm
        rw [hn] at hn'
        obtain rfl := Option.some.inj hn'
        obtain ⟨hext, hfr, hall, hidx⟩ := ih (i + 1) B σm σ'' hn h
        refine ⟨hext, hfr.mono (List.subset_cons_self _ _) (by simp) (by simp) (by simp) (by simp),
          ?_, ?_⟩
        · intro x hx
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨c', hext.1 _ _ hc⟩
          · exact hall x hx
        · intro j hj
          cases j with
          | zero => exact ⟨c', by simpa using hch, by simpa using hext.1 _ _ hc⟩
          | succ j =>
              obtain ⟨c'', h₁, h₂⟩ := hidx j (by simpa using hj)
              exact ⟨c'', by rw [← h₁]; congr 1; omega, by simpa using h₂⟩
      · rw [mem_run_cons] at h
        obtain ⟨σm, hm, h⟩ := h
        obtain ⟨n', c', hn', hch, hcm, hextm, hfrm⟩ := runStep_extractChild_mem hm
        rw [hn] at hn'
        obtain rfl := Option.some.inj hn'
        have hnm : σm.nodeOf G n = some nd := by
          simp only [Binding.nodeOf] at hn ⊢; rw [hfrm.node]; exact hn
        obtain ⟨hext, hfr, hall, hidx⟩ := ih (i + 1) (insert c B) σm σ'' hnm h
        refine ⟨hextm.trans hext, ?_, ?_, ?_⟩
        · have := hfrm.trans hfr
          simpa using this
        · intro x hx
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨c', hext.1 _ _ hcm⟩
          · exact hall x hx
        · intro j hj
          cases j with
          | zero => exact ⟨c', by simpa using hch, by simpa using hext.1 _ _ hcm⟩
          | succ j =>
              obtain ⟨c'', h₁, h₂⟩ := hidx j (by simpa using hj)
              exact ⟨c'', by rw [← h₁]; congr 1; omega, by simpa using h₂⟩

/-- Completeness of the child loop. -/
theorem childSteps_complete {G : Graph} {n : Var} {nd : Node} {σ' : Binding} :
    ∀ (cs : List Var) (i : Nat) (B : Finset Var) (σ₁ : Binding),
    σ₁.nodeOf G n = some nd → ClsDom σ₁ B → Extends σ₁ σ' →
    (∀ j (hj : j < cs.length), ∃ c', nd.children.childAt (i + j) = some c' ∧
      σ'.cls cs[j] = some c') →
    ∃ σ'' ∈ run G (childSteps n cs i B) σ₁, Extends σ'' σ' := by
  intro cs
  induction cs with
  | nil =>
      intro i B σ₁ _ _ hext _
      exact ⟨σ₁, by simp [childSteps, run], hext⟩
  | cons c cs ih =>
      intro i B σ₁ hn hdom hext hidx
      obtain ⟨c', hch, hc'⟩ := hidx 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at hch hc'
      have hidx' : ∀ j (hj : j < cs.length), ∃ c', nd.children.childAt (i + 1 + j) = some c' ∧
          σ'.cls cs[j] = some c' := by
        intro j hj
        obtain ⟨c'', h₁, h₂⟩ := hidx (j + 1) (by simpa using hj)
        exact ⟨c'', by rw [← h₁]; congr 1; omega, by simpa using h₂⟩
      simp only [childSteps]
      split
      · rename_i hcB
        obtain ⟨c₀, hc₀⟩ := (hdom c).1 hcB
        have := hext.1 _ _ hc₀
        rw [hc'] at this
        obtain rfl := Option.some.inj this
        obtain ⟨σ'', h'', hext''⟩ := ih (i + 1) B σ₁ hn hdom hext hidx'
        exact ⟨σ'', mem_run_cons.2 ⟨σ₁, runStep_checkChildEq_complete hn hc₀ hch, h''⟩, hext''⟩
      · rename_i hcB
        have hnone : σ₁.cls c = none := by
          rcases h : σ₁.cls c with _ | c₀
          · rfl
          · exact absurd ((hdom c).2 ⟨c₀, h⟩) hcB
        have hstep : σ₁.setCls c c' ∈ runStep G (.extractChild n i c) σ₁ := by
          simp [runStep, hn, hch, hnone]
        have hdom' : ClsDom (σ₁.setCls c c') (insert c B) := by
          intro x
          rw [Finset.mem_insert]
          by_cases hx : x = c
          · subst hx; simp
          · rw [setCls_cls_of_ne _ _ _ _ hx, hdom x]; simp [hx]
        have hext' : Extends (σ₁.setCls c c') σ' := by
          refine ⟨?_, hext.2.1, hext.2.2.1, hext.2.2.2.1, hext.2.2.2.2.1, hext.2.2.2.2.2⟩
          intro x cx hx
          by_cases hxc : x = c
          · subst hxc; rw [setCls_cls_self] at hx; rw [← hx]; exact hc'
          · rw [setCls_cls_of_ne _ _ _ _ hxc] at hx; exact hext.1 x cx hx
        obtain ⟨σ'', h'', hext''⟩ := ih (i + 1) (insert c B) (σ₁.setCls c c')
          (by rw [nodeOf_setCls]; exact hn) hdom' hext' hidx'
        exact ⟨σ'', mem_run_cons.2 ⟨_, hstep, h''⟩, hext''⟩

/-! ## Generic helpers -/

theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
    (∀ j (hj : j < l₁.length) (hj' : j < l₂.length), R l₁[j] l₂[j]) → List.Forall₂ R l₁ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ hl _; cases l₂ <;> simp_all
  | cons a l₁ ih =>
      intro l₂ hl h
      cases l₂ with
      | nil => simp at hl
      | cons b l₂ =>
          refine List.Forall₂.cons (h 0 (by simp) (by simp)) (ih (by simpa using hl) ?_)
          intro j hj hj'
          exact h (j + 1) (by simpa using hj) (by simpa using hj')

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    ∀ j (hj : j < l₁.length) (hj' : j < l₂.length), R l₁[j] l₂[j] := by
  intro l₁ l₂ h
  induction h with
  | nil => intro j hj; simp at hj
  | cons hab _ ih =>
      intro j hj hj'
      cases j with
      | zero => simpa using hab
      | succ j => exact ih j (by simpa using hj) (by simpa using hj')

theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro a ha; simp at ha
  | cons hab _ ih =>
      intro a ha
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨_, List.mem_cons_self .., hab⟩
      · obtain ⟨b, hb, hr⟩ := ih a ha
        exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem mem_zip_of_mem_left {α β : Type} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → ∀ a ∈ l₁, ∃ b, (a, b) ∈ l₁.zip l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ a ha; simp at ha
  | cons x l₁ ih =>
      intro l₂ hl a ha
      cases l₂ with
      | nil => simp at hl
      | cons y l₂ =>
          rw [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact ⟨y, by simp⟩
          · obtain ⟨b, hb⟩ := ih (by simpa using hl) a ha
            exact ⟨b, List.mem_cons_of_mem _ hb⟩

theorem Binding.ext' {σ σ' : Binding} (h₁ : ∀ x, σ.cls x = σ'.cls x)
    (h₂ : ∀ x, σ.node x = σ'.node x) (h₃ : ∀ x, σ.mult x = σ'.mult x)
    (h₄ : ∀ x, σ.rest x = σ'.rest x) (h₅ : ∀ x, σ.seqRest x = σ'.seqRest x)
    (h₆ : ∀ x, σ.finRest x = σ'.finRest x) : σ = σ' := by
  obtain ⟨c, n, m, r, s, f⟩ := σ
  obtain ⟨c', n', m', r', s', f'⟩ := σ'
  simp only at h₁ h₂ h₃ h₄ h₅ h₆
  congr <;> funext x <;> first | exact h₁ x | exact h₂ x | exact h₃ x | exact h₄ x | exact h₅ x | exact h₆ x

theorem binds_eq (n : Var) (f : Sym) (sh : Shape) (B : Finset Var) :
    B ∪ (RAtom.binds ⟨n, f, sh⟩) = insert n B ∪ (RAtom.elems ⟨n, f, sh⟩).toFinset := by
  ext x; simp [RAtom.binds]

theorem seqRest_joinBind_none {G : Graph} {σ : Binding} {n : Var} {id : NodeId} {r : Var}
    (h : σ.seqRest r = none) : (joinBind G σ n id).seqRest r = none := h
theorem rest_joinBind_none {G : Graph} {σ : Binding} {n : Var} {id : NodeId} {r : Var}
    (h : σ.rest r = none) : (joinBind G σ n id).rest r = none := h
theorem finRest_joinBind_none {G : Graph} {σ : Binding} {n : Var} {id : NodeId} {r : Var}
    (h : σ.finRest r = none) : (joinBind G σ n id).finRest r = none := h

/-- Frame of a join followed by a body frame: node changed only at `n`. -/
theorem lowerSpec_of_frame {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {sh : Shape}
    {B : Finset Var} {id : NodeId} {nd : Node} {ks rs ss fs : List Var}
    (hdom : ClsDom σ B) (hn : σ.node n = none)
    (hc : σ.cls n = none ∨ σ.cls n = some (G.find id))
    (hfr : Frame (RAtom.elems ⟨n, f, sh⟩) ks rs ss fs (joinBind G σ n id) σ')
    (hks : ∀ k ∈ ks, k ∈ RAtom.multVars ⟨n, f, sh⟩)
    (hrs : ∀ r ∈ rs, r ∈ RAtom.msetRestVars ⟨n, f, sh⟩)
    (hss : ∀ r ∈ ss, r ∈ RAtom.seqRestVars ⟨n, f, sh⟩)
    (hfs : ∀ r ∈ fs, r ∈ RAtom.setRestVars ⟨n, f, sh⟩)
    (hext : Extends (joinBind G σ n id) σ')
    (hall : ∀ c ∈ RAtom.elems ⟨n, f, sh⟩, ∃ c', σ'.cls c = some c')
    (hmem : (id, nd) ∈ G.nodes) (hop : nd.op = f)
    (hm : MatchN G (RAtom.shallow ⟨n, f, sh⟩) nd σ') :
    LowerSpec G ⟨n, f, sh⟩ B σ σ' where
  ext := (extends_joinBind_of_cls hn hc).trans hext
  clsDom := clsDom_congr (clsDom_of_frame hfr (clsDom_joinBind hdom) hall) (binds_eq n f sh B).symm
  node v hv := by rw [hfr.node, joinBind_node_of_ne _ _ _ _ _ hv]
  mult k hk := hfr.mult k (fun h => hk (hks k h))
  rest r hr := hfr.rest r (fun h => hr (hrs r h))
  seqRest r hr := hfr.seqRest r (fun h => hr (hss r h))
  finRest r hr := hfr.finRest r (fun h => hr (hfs r h))
  sat := ⟨id, nd, hext.2.1 _ _ (joinBind_node_self _ _ _ _), hmem,
    hext.1 _ _ (joinBind_cls_self _ _ _ _), hop, hm⟩

/-! ## Soundness per shape -/

theorem lower_sound_plain {G : Graph} {sig : Sym → Kind} {σ σ' : Binding} {n : Var} {f : Sym}
    {cs : List Var} {B : Finset Var}
    (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : sig f = .plain cs.length)
    (hdom : ClsDom σ B) (hn : σ.node n = none)
    (h : σ' ∈ run G (lower ⟨n, f, .plain cs⟩ B) σ) :
    LowerSpec G ⟨n, f, .plain cs⟩ B σ σ' := by
  simp only [lower, lowerBody] at h
  rw [mem_run_cons] at h
  obtain ⟨σ₁, h₁, h⟩ := h
  obtain ⟨id, hid, rfl⟩ := runStep_join_mem.1 h₁
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  have hkind := hconf (id, nd) hmem
  simp only at hkind
  rw [hop, hwk] at hkind
  obtain ⟨cs', hch, hlen⟩ := Children.kind_plain hkind
  have hnd : (joinBind G σ n id).nodeOf G n = some nd :=
    nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem
  obtain ⟨hext, hfr, hall, hidx⟩ := childSteps_sound cs 0 (insert n B) _ σ' hnd h
  have hf₂ : List.Forall₂ (fun v c => σ'.cls v = some c) cs cs' := by
    refine forall₂_of_getElem hlen.symm ?_
    intro j hj hj'
    obtain ⟨c', h₁, h₂⟩ := hidx j hj
    rw [hch] at h₁
    simp only [Children.childAt, Nat.zero_add, List.getElem?_eq_getElem hj'] at h₁
    rw [h₂, h₁]
  refine lowerSpec_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    (by simpa [RAtom.elems] using hall) hmem hop ?_
  obtain ⟨f', ch⟩ := nd
  simp only at hop hch
  subst hop hch
  exact matchN_plain_vars.2 ⟨cs', rfl, hf₂⟩

theorem lower_sound_comm {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {x y : Var}
    {B : Finset Var} (hk : G.KeysNodup) (hdom : ClsDom σ B) (hn : σ.node n = none)
    (h : σ' ∈ run G (lower ⟨n, f, .comm x y⟩ B) σ) :
    LowerSpec G ⟨n, f, .comm x y⟩ B σ σ' := by
  simp only [lower, lowerBody] at h
  rw [mem_run_cons] at h
  obtain ⟨σ₁, h₁, h⟩ := h
  obtain ⟨id, hid, rfl⟩ := runStep_join_mem.1 h₁
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  rw [mem_run_cons] at h
  obtain ⟨σ₂, h₂, h⟩ := h
  simp only [run, List.mem_singleton] at h
  subst h
  obtain ⟨g, a, b, hnd, hd⟩ := runStep_decomposeComm_mem h₂
  rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hnd
  obtain rfl := Option.some.inj hnd
  simp only at hop
  subst hop
  obtain ⟨hext, hab⟩ := decompose_comm_sound' x y a b _ _ hd
  have hfr := frame_decomposeComm hd
  refine lowerSpec_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    ?_ hmem rfl ?_
  · intro c hc'
    simp only [RAtom.elems, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hab with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases hc' with rfl | rfl <;> exact ⟨_, by assumption⟩
  · exact matchN_comm_vars.2 ⟨a, b, rfl, hab⟩

theorem lower_sound_assoc {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {pre suf : Option Var}
    {fx : List Var} {B : Finset Var} (hk : G.KeysNodup) (hdom : ClsDom σ B) (hn : σ.node n = none)
    (hrf : RAtom.RestFresh ⟨n, f, .assoc pre fx suf⟩ σ)
    (h : σ' ∈ run G (lower ⟨n, f, .assoc pre fx suf⟩ B) σ) :
    LowerSpec G ⟨n, f, .assoc pre fx suf⟩ B σ σ' := by
  simp only [lower, lowerBody] at h
  rw [mem_run_cons] at h
  obtain ⟨σ₁, h₁, h⟩ := h
  obtain ⟨id, hid, rfl⟩ := runStep_join_mem.1 h₁
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  rw [mem_run_cons] at h
  obtain ⟨σ₂, h₂, h⟩ := h
  simp only [run, List.mem_singleton] at h
  subst h
  obtain ⟨g, cs, hnd, hd⟩ := runStep_expandA_mem h₂
  rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hnd
  obtain rfl := Option.some.inj hnd
  simp only at hop
  subst hop
  obtain ⟨hs, -, -, hnd'⟩ := hrf
  simp only [RAtom.seqRestVars] at hs hnd'
  have hpre₀ : ∀ r, pre = some r → (joinBind G σ n id).seqRest r = none := by
    intro r hr; subst hr; exact hs r (by simp)
  have hsuf₀ : ∀ r, suf = some r → (joinBind G σ n id).seqRest r = none := by
    intro r hr; subst hr; exact hs r (by simp)
  have hdist : ∀ r, pre = some r → suf ≠ some r := by
    intro r hr hs'; subst hr; subst hs'; simp at hnd'
  obtain ⟨hext, u, mid, v, hcs, hlen, hpre, hsuf, hcls⟩ :=
    expand_a_sound' pre suf fx cs _ _ hpre₀ hsuf₀ hdist hd
  subst hcs
  have hfr := frame_expandA hd
  have hf₂ : List.Forall₂ (fun x c => σ'.cls x = some c) fx mid :=
    List.forall₂_iff_zip.2 ⟨hlen.symm, fun hab => hcls _ hab⟩
  refine lowerSpec_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    ?_ hmem rfl ?_
  · intro c hc'
    obtain ⟨b, -, hb⟩ := forall₂_exists_right hf₂ c (by simpa [RAtom.elems] using hc')
    exact ⟨b, hb⟩
  · exact matchN_assoc_vars.2 ⟨u, mid, v, rfl, hpre, hsuf, hf₂⟩

theorem lower_sound_ac {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {es : List (Var × Mult)}
    {rest : Option Var} {B : Finset Var} (hk : G.KeysNodup) (hdom : ClsDom σ B)
    (hn : σ.node n = none) (hrf : RAtom.RestFresh ⟨n, f, .ac es rest⟩ σ)
    (h : σ' ∈ run G (lower ⟨n, f, .ac es rest⟩ B) σ) :
    LowerSpec G ⟨n, f, .ac es rest⟩ B σ σ' := by
  simp only [lower, lowerBody] at h
  rw [mem_run_cons] at h
  obtain ⟨σ₁, h₁, h⟩ := h
  obtain ⟨id, hid, rfl⟩ := runStep_join_mem.1 h₁
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  rw [mem_run_cons] at h
  obtain ⟨σ₂, h₂, h⟩ := h
  simp only [run, List.mem_singleton] at h
  subst h
  obtain ⟨g, m, hnd, hd⟩ := runStep_decomposeAC_mem h₂
  rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hnd
  obtain rfl := Option.some.inj hnd
  simp only at hop
  subst hop
  obtain ⟨-, hr, -, -⟩ := hrf
  simp only [RAtom.msetRestVars] at hr
  have hfresh : ∀ r ∈ rest, (joinBind G σ n id).rest r = none := by
    intro r hr'; exact hr r (Option.mem_toList.2 hr')
  obtain ⟨hext, taken, hnd', hlen, hmem', hcls, hmult, hrest⟩ :=
    decompose_ac_sound' es rest m _ _ hfresh hd
  have hfr := frame_decomposeAC es rest _ _ _ hd
  refine lowerSpec_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    ?_ hmem rfl ?_
  · intro c hc'
    simp only [RAtom.elems, List.mem_map] at hc'
    obtain ⟨e, he, rfl⟩ := hc'
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e he
    exact ⟨t, hcls (e, t) ht⟩
  · exact matchN_ac_vars.2 ⟨m, taken, rfl, hnd', hlen, hmem', hcls, hmult, hrest⟩

theorem lower_sound_aci {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {es : List Var}
    {rest : Option Var} {B : Finset Var} (hk : G.KeysNodup) (hdom : ClsDom σ B)
    (hn : σ.node n = none) (hrf : RAtom.RestFresh ⟨n, f, .aci es rest⟩ σ)
    (h : σ' ∈ run G (lower ⟨n, f, .aci es rest⟩ B) σ) :
    LowerSpec G ⟨n, f, .aci es rest⟩ B σ σ' := by
  simp only [lower, lowerBody] at h
  rw [mem_run_cons] at h
  obtain ⟨σ₁, h₁, h⟩ := h
  obtain ⟨id, hid, rfl⟩ := runStep_join_mem.1 h₁
  obtain ⟨nd, hmem, hop, hc⟩ := join_lower_sound hdom hid
  simp only at hop
  rw [mem_run_cons] at h
  obtain ⟨σ₂, h₂, h⟩ := h
  simp only [run, List.mem_singleton] at h
  subst h
  obtain ⟨g, st, hnd, hd⟩ := runStep_decomposeACI_mem h₂
  rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hnd
  obtain rfl := Option.some.inj hnd
  simp only at hop
  subst hop
  obtain ⟨-, -, hr, -⟩ := hrf
  simp only [RAtom.setRestVars] at hr
  have hfresh : ∀ r ∈ rest, (joinBind G σ n id).finRest r = none := by
    intro r hr'; exact hr r (Option.mem_toList.2 hr')
  obtain ⟨hext, taken, hnd', hlen, hmem', hcls, hrest⟩ :=
    decompose_aci_sound' es rest st _ _ hfresh hd
  have hfr := frame_decomposeACI es rest _ _ _ hd
  refine lowerSpec_of_frame hdom hn hc (by simpa [RAtom.elems] using hfr) (by simp [RAtom.multVars])
    (by simp [RAtom.msetRestVars]) (by simp [RAtom.seqRestVars]) (by simp [RAtom.setRestVars]) hext
    ?_ hmem rfl ?_
  · intro c hc'
    simp only [RAtom.elems] at hc'
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen c hc'
    exact ⟨t, hcls (c, t) ht⟩
  · exact matchN_aci_vars.2 ⟨st, taken, rfl, hnd', hlen, hmem', hcls, hrest⟩

/-- Soundness of the lowering of any atom. -/
theorem lower_sound {G : Graph} {sig : Sym → Kind} {σ σ' : Binding} {a : RAtom} {B : Finset Var}
    (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : a.WK sig)
    (hdom : ClsDom σ B) (hn : σ.node a.node = none) (hrf : a.RestFresh σ)
    (h : σ' ∈ run G (lower a B) σ) : LowerSpec G a B σ σ' := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | plain cs => exact lower_sound_plain hk hconf hwk hdom hn h
  | comm x y => exact lower_sound_comm hk hdom hn h
  | assoc pre fx suf => exact lower_sound_assoc hk hdom hn hrf h
  | ac es rest => exact lower_sound_ac hk hdom hn hrf h
  | aci es rest => exact lower_sound_aci hk hdom hn hrf h

/-! ## Completeness per shape -/

/-- The `byContains` predicate for a bound element whose class is a child
of the node. -/
theorem contains_pred {G : Graph} {σ σ' : Binding} {B : Finset Var} {id : NodeId} {nd : Node}
    {e : Var} {c : C} (hdom : ClsDom σ B) (hext : Extends σ σ') (hmem : (id, nd) ∈ G.nodes)
    (heB : e ∈ B) (hc : σ'.cls e = some c) (hv : nd.children.isVariadic = true)
    (hcc : nd.children.containsClass c = true) : (Lookup.byContains e).pred G σ id := by
  obtain ⟨c₀, hc₀⟩ := (hdom e).1 heB
  have h' := hext.1 _ _ hc₀
  rw [hc] at h'
  exact ⟨nd, c₀, hmem, hc₀, hv, (Option.some.inj h') ▸ hcc⟩

theorem lower_complete_plain {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {cs : List Var}
    {B : Finset Var} (hk : G.KeysNodup) (hdom : ClsDom σ B) (hext : Extends σ σ')
    (hsat : AtomSat G σ' ⟨n, f, .plain cs⟩) :
    ∃ σ₁ ∈ run G (lower ⟨n, f, .plain cs⟩ B) σ, Extends σ₁ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨cs', rfl, hf₂⟩ := matchN_plain_vars.1 hm
  simp only at hnode hcls hop
  have hlen := hf₂.length_eq
  have hidx : ∀ j (hj : j < cs.length), ∃ c', (Children.tuple cs').childAt (0 + j) = some c' ∧
      σ'.cls cs[j] = some c' := by
    intro j hj
    refine ⟨cs'[j]'(hlen ▸ hj), ?_, forall₂_getElem hf₂ j hj (hlen ▸ hj)⟩
    simp [Children.childAt, List.getElem?_eq_getElem (hlen ▸ hj)]
  have hjoin : id ∈ candidates G σ (joinLookups ⟨n, f, .plain cs⟩ B) := by
    refine join_lower_complete hdom hext hmem rfl hcls ?_
    intro l hl
    simp only [extraLookups] at hl
    obtain ⟨j, c, hj, hcB, rfl⟩ := mem_childLookups hl
    have hjl : j < cs.length := (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨c', hch, hc'⟩ := hidx j hjl
    have hcj : cs[j] = c := by simpa [List.getElem?_eq_getElem hjl] using hj
    rw [hcj] at hc'
    obtain ⟨c₀, hc₀⟩ := (hdom c).1 hcB
    have h' := hext.1 _ _ hc₀
    rw [hc'] at h'
    exact ⟨_, c₀, hmem, hc₀, (Option.some.inj h') ▸ hch⟩
  have hext₁ : Extends (joinBind G σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨σ₁, h₁, hext'⟩ := childSteps_complete (nd := ⟨f, .tuple cs'⟩) cs 0 (insert n B)
    (joinBind G σ n id) (nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem) (clsDom_joinBind hdom)
    hext₁ hidx
  refine ⟨σ₁, ?_, hext'⟩
  simp only [lower, lowerBody]
  exact mem_run_cons.2 ⟨_, runStep_join_mem.2 ⟨id, hjoin, rfl⟩, h₁⟩

theorem lower_complete_comm {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {x y : Var}
    {B : Finset Var} (hk : G.KeysNodup) (hdom : ClsDom σ B) (hext : Extends σ σ')
    (hsat : AtomSat G σ' ⟨n, f, .comm x y⟩) :
    ∃ σ₁ ∈ run G (lower ⟨n, f, .comm x y⟩ B) σ, Extends σ₁ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨a, b, rfl, hab⟩ := matchN_comm_vars.1 hm
  simp only at hnode hcls hop
  have hjoin : id ∈ candidates G σ (joinLookups ⟨n, f, .comm x y⟩ B) :=
    join_lower_complete hdom hext hmem rfl hcls (by simp [extraLookups])
  have hext₁ : Extends (joinBind G σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨σ₁, h₁, hext'⟩ := decompose_comm_complete' x y a b _ _ hext₁ hab
  refine ⟨σ₁, ?_, hext'⟩
  simp only [lower, lowerBody]
  refine mem_run_cons.2 ⟨_, runStep_join_mem.2 ⟨id, hjoin, rfl⟩, mem_run_cons.2 ⟨σ₁, ?_, by simp [run]⟩⟩
  simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
  exact h₁

theorem lower_complete_assoc {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym}
    {pre suf : Option Var} {fx : List Var} {B : Finset Var}
    (hk : G.KeysNodup) (hdom : ClsDom σ B) (hext : Extends σ σ')
    (hsat : AtomSat G σ' ⟨n, f, .assoc pre fx suf⟩) :
    ∃ σ₁ ∈ run G (lower ⟨n, f, .assoc pre fx suf⟩ B) σ, Extends σ₁ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨u, mid, v, rfl, hpre, hsuf, hf₂⟩ := matchN_assoc_vars.1 hm
  simp only at hnode hcls hop
  have hjoin : id ∈ candidates G σ (joinLookups ⟨n, f, .assoc pre fx suf⟩ B) := by
    refine join_lower_complete hdom hext hmem rfl hcls ?_
    intro l hl
    simp only [extraLookups, RAtom.elems] at hl
    obtain ⟨e, he, heB, rfl⟩ := mem_containsLookups hl
    obtain ⟨c, hc, hec⟩ := forall₂_exists_right hf₂ e he
    refine contains_pred hdom hext hmem heB hec (by simp [Children.isVariadic]) ?_
    simp [Children.containsClass, hc]
  have hext₁ : Extends (joinBind G σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨σ₁, h₁, hext'⟩ := expand_a_complete' pre suf fx u mid v _ _ hext₁ hf₂.length_eq.symm hpre hsuf
    (fun ec hec => (List.forall₂_iff_zip.1 hf₂).2 hec)
  refine ⟨σ₁, ?_, hext'⟩
  simp only [lower, lowerBody]
  refine mem_run_cons.2 ⟨_, runStep_join_mem.2 ⟨id, hjoin, rfl⟩, mem_run_cons.2 ⟨σ₁, ?_, by simp [run]⟩⟩
  simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
  exact h₁

theorem lower_complete_ac {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {es : List (Var × Mult)}
    {rest : Option Var} {B : Finset Var}
    (hk : G.KeysNodup) (hdom : ClsDom σ B) (hext : Extends σ σ')
    (hsat : AtomSat G σ' ⟨n, f, .ac es rest⟩) :
    ∃ σ₁ ∈ run G (lower ⟨n, f, .ac es rest⟩ B) σ, Extends σ₁ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨m, taken, rfl, hnd, hlen, hmem', hcl, hmult, hrest⟩ := matchN_ac_vars.1 hm
  simp only at hnode hcls hop
  have hjoin : id ∈ candidates G σ (joinLookups ⟨n, f, .ac es rest⟩ B) := by
    refine join_lower_complete hdom hext hmem rfl hcls ?_
    intro l hl
    simp only [extraLookups, RAtom.elems] at hl
    obtain ⟨e, he, heB, rfl⟩ := mem_containsLookups hl
    rw [List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e' he'
    refine contains_pred hdom hext hmem heB (hcl (e', t) ht) (by simp [Children.isVariadic]) ?_
    simp only [Children.containsClass, decide_eq_true_eq]
    exact hmem' t (List.of_mem_zip ht).2
  have hext₁ : Extends (joinBind G σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨σ₁, h₁, hext'⟩ := decompose_ac_complete' es rest m _ _ taken hext₁ hnd hlen hmem' hcl hmult hrest
  refine ⟨σ₁, ?_, hext'⟩
  simp only [lower, lowerBody]
  refine mem_run_cons.2 ⟨_, runStep_join_mem.2 ⟨id, hjoin, rfl⟩, mem_run_cons.2 ⟨σ₁, ?_, by simp [run]⟩⟩
  simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
  exact h₁

theorem lower_complete_aci {G : Graph} {σ σ' : Binding} {n : Var} {f : Sym} {es : List Var}
    {rest : Option Var} {B : Finset Var}
    (hk : G.KeysNodup) (hdom : ClsDom σ B) (hext : Extends σ σ')
    (hsat : AtomSat G σ' ⟨n, f, .aci es rest⟩) :
    ∃ σ₁ ∈ run G (lower ⟨n, f, .aci es rest⟩ B) σ, Extends σ₁ σ' := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hsat
  simp only [RAtom.shallow] at hm
  obtain ⟨st, taken, rfl, hnd, hlen, hmem', hcl, hrest⟩ := matchN_aci_vars.1 hm
  simp only at hnode hcls hop
  have hjoin : id ∈ candidates G σ (joinLookups ⟨n, f, .aci es rest⟩ B) := by
    refine join_lower_complete hdom hext hmem rfl hcls ?_
    intro l hl
    simp only [extraLookups, RAtom.elems] at hl
    obtain ⟨e, he, heB, rfl⟩ := mem_containsLookups hl
    obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e he
    refine contains_pred hdom hext hmem heB (hcl (e, t) ht) (by simp [Children.isVariadic]) ?_
    simp only [Children.containsClass, decide_eq_true_eq]
    exact hmem' t (List.of_mem_zip ht).2
  have hext₁ : Extends (joinBind G σ n id) σ' := extends_joinBind_of_bound hext hnode hcls
  obtain ⟨σ₁, h₁, hext'⟩ := decompose_aci_complete' es rest st _ _ taken hext₁ hnd hlen hmem' hcl hrest
  refine ⟨σ₁, ?_, hext'⟩
  simp only [lower, lowerBody]
  refine mem_run_cons.2 ⟨_, runStep_join_mem.2 ⟨id, hjoin, rfl⟩, mem_run_cons.2 ⟨σ₁, ?_, by simp [run]⟩⟩
  simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
  exact h₁

/-- Completeness of the lowering of any atom: every extension of `σ` that
satisfies the atom lies above an emitted binding. -/
theorem lower_complete {G : Graph} {σ σ' : Binding} {a : RAtom} {B : Finset Var}
    (hk : G.KeysNodup) (hdom : ClsDom σ B) (hext : Extends σ σ') (hsat : AtomSat G σ' a) :
    ∃ σ₁ ∈ run G (lower a B) σ, Extends σ₁ σ' := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | plain cs => exact lower_complete_plain hk hdom hext hsat
  | comm x y => exact lower_complete_comm hk hdom hext hsat
  | assoc pre fx suf => exact lower_complete_assoc hk hdom hext hsat
  | ac es rest => exact lower_complete_ac hk hdom hext hsat
  | aci es rest => exact lower_complete_aci hk hdom hext hsat

/-! ## Uniqueness and the main theorem -/

/-- A satisfied atom binds all its multiplicity variables. -/
theorem AtomSat.multVars_bound {G : Graph} {σ : Binding} {a : RAtom} (h : AtomSat G σ a) :
    ∀ k ∈ a.multVars, ∃ m, σ.mult k = some m := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | ac es rest =>
      obtain ⟨id, nd, -, -, -, -, hm⟩ := h
      simp only [RAtom.shallow] at hm
      obtain ⟨m, taken, -, -, hlen, -, -, hmult, -⟩ := matchN_ac_vars.1 hm
      intro k hk
      simp only [RAtom.multVars] at hk
      rw [mem_multVars] at hk
      obtain ⟨e, he, hke⟩ := hk
      obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e he
      have := hmult (e, t) ht
      obtain ⟨e₁, μ⟩ := e
      cases μ with
      | exact _ => simp [Mult.vars] at hke
      | var k' lo hi =>
          simp only [Mult.vars, List.mem_singleton] at hke
          subst hke
          exact ⟨_, this.1⟩
  | plain cs => simp [RAtom.multVars]
  | comm x y => simp [RAtom.multVars]
  | assoc pre fx suf => simp [RAtom.multVars]
  | aci es rest => simp [RAtom.multVars]

theorem AtomSat.seqRest_bound {G : Graph} {σ : Binding} {a : RAtom} (h : AtomSat G σ a) :
    ∀ r ∈ a.seqRestVars, ∃ u, σ.seqRest r = some u := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | assoc pre fx suf =>
      obtain ⟨id, nd, -, -, -, -, hm⟩ := h
      simp only [RAtom.shallow] at hm
      obtain ⟨u, mid, v, -, hpre, hsuf, -⟩ := matchN_assoc_vars.1 hm
      intro r hr
      simp only [RAtom.seqRestVars, List.mem_append, Option.mem_toList] at hr
      rcases hr with rfl | rfl
      · exact ⟨u, hpre⟩
      · exact ⟨v, hsuf⟩
  | plain cs => simp [RAtom.seqRestVars]
  | comm x y => simp [RAtom.seqRestVars]
  | ac es rest => simp [RAtom.seqRestVars]
  | aci es rest => simp [RAtom.seqRestVars]

theorem AtomSat.msetRest_bound {G : Graph} {σ : Binding} {a : RAtom} (h : AtomSat G σ a) :
    ∀ r ∈ a.msetRestVars, ∃ m, σ.rest r = some m := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | ac es rest =>
      obtain ⟨id, nd, -, -, -, -, hm⟩ := h
      simp only [RAtom.shallow] at hm
      obtain ⟨m, taken, -, -, -, -, -, -, hrest⟩ := matchN_ac_vars.1 hm
      intro r hr
      simp only [RAtom.msetRestVars, Option.mem_toList] at hr
      subst hr
      exact ⟨_, hrest⟩
  | plain cs => simp [RAtom.msetRestVars]
  | comm x y => simp [RAtom.msetRestVars]
  | assoc pre fx suf => simp [RAtom.msetRestVars]
  | aci es rest => simp [RAtom.msetRestVars]

theorem AtomSat.setRest_bound {G : Graph} {σ : Binding} {a : RAtom} (h : AtomSat G σ a) :
    ∀ r ∈ a.setRestVars, ∃ s, σ.finRest r = some s := by
  obtain ⟨n, f, sh⟩ := a
  cases sh with
  | aci es rest =>
      obtain ⟨id, nd, -, -, -, -, hm⟩ := h
      simp only [RAtom.shallow] at hm
      obtain ⟨st, taken, -, -, -, -, -, hrest⟩ := matchN_aci_vars.1 hm
      intro r hr
      simp only [RAtom.setRestVars, Option.mem_toList] at hr
      subst hr
      exact ⟨_, hrest⟩
  | plain cs => simp [RAtom.setRestVars]
  | comm x y => simp [RAtom.setRestVars]
  | assoc pre fx suf => simp [RAtom.setRestVars]
  | ac es rest => simp [RAtom.setRestVars]

/-- A satisfied atom binds all its element class variables. -/
theorem AtomSat.elems_bound {G : Graph} {σ : Binding} {a : RAtom} (h : AtomSat G σ a) :
    ∀ e ∈ a.elems, ∃ c, σ.cls e = some c := by
  obtain ⟨n, f, sh⟩ := a
  obtain ⟨id, nd, -, -, -, -, hm⟩ := h
  simp only [RAtom.shallow] at hm
  cases sh with
  | plain cs =>
      obtain ⟨cs', -, hf₂⟩ := matchN_plain_vars.1 hm
      intro e he
      obtain ⟨c, -, hc⟩ := forall₂_exists_right hf₂ e he
      exact ⟨c, hc⟩
  | comm x y =>
      obtain ⟨a, b, -, hab⟩ := matchN_comm_vars.1 hm
      intro e he
      simp only [RAtom.elems, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases hab with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases he with rfl | rfl <;> exact ⟨_, by assumption⟩
  | assoc pre fx suf =>
      obtain ⟨u, mid, v, -, -, -, hf₂⟩ := matchN_assoc_vars.1 hm
      intro e he
      obtain ⟨c, -, hc⟩ := forall₂_exists_right hf₂ e he
      exact ⟨c, hc⟩
  | ac es rest =>
      obtain ⟨m, taken, -, -, hlen, -, hcl, -, -⟩ := matchN_ac_vars.1 hm
      intro e he
      simp only [RAtom.elems, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e' he'
      exact ⟨t, hcl (e', t) ht⟩
  | aci es rest =>
      obtain ⟨st, taken, -, -, hlen, -, hcl, -⟩ := matchN_aci_vars.1 hm
      intro e he
      obtain ⟨t, ht⟩ := mem_zip_of_mem_left hlen e he
      exact ⟨t, hcl (e, t) ht⟩

/-- Two bindings meeting the specification, one below the other, are equal. -/
theorem lowerSpec_unique {G : Graph} {a : RAtom} {B : Finset Var} {σ σ₁ σ' : Binding}
    (h₁ : LowerSpec G a B σ σ₁) (h₂ : LowerSpec G a B σ σ') (hext : Extends σ₁ σ') : σ₁ = σ' := by
  refine Binding.ext' ?_ ?_ ?_ ?_ ?_ ?_
  · intro x
    by_cases hx : x ∈ B ∪ a.binds
    · obtain ⟨c, hc⟩ := (h₁.clsDom x).1 hx
      rw [hc, hext.1 x c hc]
    · have e₁ : σ₁.cls x = none := by
        rcases h : σ₁.cls x with _ | c
        · rfl
        · exact absurd ((h₁.clsDom x).2 ⟨c, h⟩) hx
      have e₂ : σ'.cls x = none := by
        rcases h : σ'.cls x with _ | c
        · rfl
        · exact absurd ((h₂.clsDom x).2 ⟨c, h⟩) hx
      rw [e₁, e₂]
  · intro v
    by_cases hv : v = a.node
    · subst hv
      obtain ⟨id, -, hid, -⟩ := h₁.sat
      rw [hid, hext.2.1 _ _ hid]
    · rw [h₁.node v hv, h₂.node v hv]
  · intro k
    by_cases hk : k ∈ a.multVars
    · obtain ⟨m, hm⟩ := h₁.sat.multVars_bound k hk
      rw [hm, hext.2.2.1 _ _ hm]
    · rw [h₁.mult k hk, h₂.mult k hk]
  · intro r
    by_cases hr : r ∈ a.msetRestVars
    · obtain ⟨m, hm⟩ := h₁.sat.msetRest_bound r hr
      rw [hm, hext.2.2.2.1 _ _ hm]
    · rw [h₁.rest r hr, h₂.rest r hr]
  · intro r
    by_cases hr : r ∈ a.seqRestVars
    · obtain ⟨u, hu⟩ := h₁.sat.seqRest_bound r hr
      rw [hu, hext.2.2.2.2.1 _ _ hu]
    · rw [h₁.seqRest r hr, h₂.seqRest r hr]
  · intro r
    by_cases hr : r ∈ a.setRestVars
    · obtain ⟨s, hs⟩ := h₁.sat.setRest_bound r hr
      rw [hs, hext.2.2.2.2.2 _ _ hs]
    · rw [h₁.finRest r hr, h₂.finRest r hr]

/-- Spec §3.2, `lower_sound_complete`: under a bound set `B` that is exactly
the class domain of `σ`, with the atom's node variable unbound and its rest
variables fresh, the lowering emits exactly the bindings that extend `σ`,
satisfy the atom, bind the classes `B ∪ binds a`, and write nothing else.
Hypotheses in engine terms: distinct node ids (`hk`); every stored node has
the children shape of its operator's kind and the atom uses that shape
(`hconf`, `hwk`; only the plain shape needs this: a plain atom's child loop
reads positions of any tuple/sequence node); the atom's node variable has
not been joined before (`hn`, node-variable linearity); its rest variables
are unbound and distinct (`hrf`, rest-variable linearity). -/
theorem lower_sound_complete {G : Graph} {sig : Sym → Kind} (a : RAtom) (B : Finset Var)
    (σ : Binding) (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : a.WK sig)
    (hdom : ClsDom σ B) (hn : σ.node a.node = none) (hrf : a.RestFresh σ) :
    ∀ σ', σ' ∈ run G (lower a B) σ ↔ LowerSpec G a B σ σ' := by
  intro σ'
  constructor
  · exact lower_sound hk hconf hwk hdom hn hrf
  · intro hs
    obtain ⟨σ₁, h₁, hext⟩ := lower_complete hk hdom hs.ext hs.sat
    have := lowerSpec_unique (lower_sound hk hconf hwk hdom hn hrf h₁) hs hext
    subst this
    exact h₁

end Semper.EMatch
