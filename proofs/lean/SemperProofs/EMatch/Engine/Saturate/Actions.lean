import SemperProofs.EMatch.Engine.Matcher

/-!
# Rule actions and fired instances (spec-actions §A-§C)

A rule's head is a list of actions (`apply.rs:164-174`, `CompiledAction`):
`Insert(t)` builds the term `t` under the match (`apply.rs:1289-1292`),
`Union(a, b)` builds both sides and merges their classes
(`apply.rs:1271-1288`), `Subsume(x)` flags the match's node for `x`
(`apply.rs:1300-1304`). The actions of one match run in head order after
the whole query has been matched (`apply.rs:1308-1350`, `saturate.rs:757-764`).

Right-hand-side terms are the pattern type `Pat`: a variable is read from
the binding (`FetchNode`, `apply.rs:713`), an application is built with
`add` from the values of its subterms, a rest variable is spliced
(`apply.rs:927-931`), an element with a multiplicity contributes that count
(`apply.rs:914-926`; a count of `0` omits the element without building it).

`Den G σ t c` says the term is built in `G`: every application has a stored
node whose children are the values of its subterms (canonical classes, the
stored children being `find`-fixed points after `rebuild`) and whose class
is `c`. `Fired G σ rule` says every action's consequence is present in `G`.
The n-ary normal form of `add` (unit drop, degenerate arity, flattening of
nested same-op children, inverse cancellation, `egraph.rs:1047-1110`) is not
modelled: `Den` stores the literal child list (spec-actions §C.1).
-/

namespace Semper.EMatch

/-- A right-hand-side multiplicity: an exact literal, or the count bound to
a multiplicity variable (the bounds of a `Mult.var` are a left-hand-side
constraint and are ignored here). -/
def RMultOk (σ : Binding) : Mult → Nat → Prop
  | .exact k, n => n = k
  | .var k _ _, n => σ.mult k = some n

/-- The spliced multiset rest: the bound multiset, or `0` without a rest. -/
def MsetRestVal (σ : Binding) : Option Var → Multiset C → Prop
  | none, m => m = 0
  | some r, m => σ.rest r = some m

/-- The spliced set rest: the bound set, or `∅` without a rest. -/
def SetRestVal (σ : Binding) : Option Var → Finset C → Prop
  | none, s => s = ∅
  | some r, s => σ.finRest r = some s

/-- The multiset of children of an AC application: each element's class
with its count (`push_count`, `apply.rs:497-523`). -/
def acChildren : List (C × Nat) → Multiset C
  | [] => 0
  | (c, k) :: cks => k • ({c} : Multiset C) + acChildren cks

theorem acChildren_map (f : C → C) : ∀ cks : List (C × Nat),
    (acChildren cks).map f = acChildren (cks.map fun ck => (f ck.1, ck.2))
  | [] => by simp [acChildren]
  | (c, k) :: cks => by
      simp only [acChildren, Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton,
        List.map_cons, acChildren_map f cks]

/-- `Den G σ t c`: the right-hand-side term `t` is built in `G` under the
binding `σ` with value `c` (a representative). -/
inductive Den (G : Graph) (σ : Binding) : Pat → C → Prop
  /-- `FetchNode`: the bound class, canonicalized. -/
  | var {x : Var} {c : C} : σ.cls x = some c → Den G σ (.var x) (G.find c)
  | plain {f : Sym} {args : List Pat} {cs : List C} {id : NodeId} :
      args.length = cs.length → (∀ pc ∈ args.zip cs, Den G σ pc.1 pc.2) →
      (id, ⟨f, .tuple cs⟩) ∈ G.nodes → Den G σ (.plain f args) (G.find id)
  /-- The store sorts the pair: either order of the two values. -/
  | comm {f : Sym} {p q : Pat} {a b : C} {id : NodeId} :
      Den G σ p a → Den G σ q b →
      ((id, ⟨f, .spair a b⟩) ∈ G.nodes ∨ (id, ⟨f, .spair b a⟩) ∈ G.nodes) →
      Den G σ (.comm f p q) (G.find id)
  | assoc {f : Sym} {pre suf : Option Var} {args : List Pat} {cs u v : List C} {id : NodeId} :
      args.length = cs.length → (∀ pc ∈ args.zip cs, Den G σ pc.1 pc.2) →
      SeqRestOk σ pre u → SeqRestOk σ suf v →
      (id, ⟨f, .seq (u.map G.find ++ cs ++ v.map G.find)⟩) ∈ G.nodes →
      Den G σ (.assoc f pre args suf) (G.find id)
  /-- An element of count `0` is omitted without being built
  (`apply.rs:920-925`). -/
  | ac {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var} {cks : List (C × Nat)}
      {m₀ : Multiset C} {id : NodeId} :
      elems.length = cks.length →
      (∀ ek ∈ elems.zip cks, RMultOk σ ek.1.2 ek.2.2) →
      (∀ ek ∈ elems.zip cks, ek.2.2 ≠ 0 → Den G σ ek.1.1 ek.2.1) →
      MsetRestVal σ rest m₀ →
      (id, ⟨f, .mset (acChildren cks + m₀.map G.find)⟩) ∈ G.nodes →
      Den G σ (.ac f elems rest) (G.find id)
  | aci {f : Sym} {elems : List Pat} {rest : Option Var} {cs : List C} {s₀ : Finset C}
      {id : NodeId} :
      elems.length = cs.length → (∀ pc ∈ elems.zip cs, Den G σ pc.1 pc.2) →
      SetRestVal σ rest s₀ →
      (id, ⟨f, .set (cs.toFinset ∪ s₀.image G.find)⟩) ∈ G.nodes →
      Den G σ (.aci f elems rest) (G.find id)

/-- Every value of `Den` is `G.find` of something. -/
theorem Den.exists_find {G : Graph} {σ : Binding} {t : Pat} {c : C} (h : Den G σ t c) :
    ∃ c₀, c = G.find c₀ := by
  cases h <;> exact ⟨_, rfl⟩

/-- Values are representatives when `find` is idempotent. -/
theorem Den.find_eq {G : Graph} (hidem : G.FindIdem) {σ : Binding} {t : Pat} {c : C}
    (h : Den G σ t c) : G.find c = c := by
  obtain ⟨c₀, rfl⟩ := h.exists_find
  exact hidem c₀

/-- A rule action (`CompiledAction`, `apply.rs:164-174`; `Set` is
unimplemented in the engine, `apply.rs:1293-1299`). -/
inductive Action where
  | insert (t : Pat)
  | union (a b : Pat)
  | subsume (x : Var)

/-- A rule: its resolved query atoms, the procedure that matches them (the
static plan or the adaptive scheduler, `Matcher`), and its head actions in
order. `(rewrite L R)` is `[union (var root) R]` plus `subsume root` under
`:subsume` (`apply.rs:377-384`); `(rule body head)` is the head in order
(`apply.rs:431-434`). -/
structure Rule where
  atoms : List QAtom
  matcher : Matcher
  actions : List Action

mutual
/-- Whether a right-hand side contains an n-ary application (`assoc`, `ac`
or `aci`): the terms whose stored node `rebuild` may rewrite non-literally
(unit drop, nilpotent clamp, degenerate arity, `recanonize_node`). A
variable, a plain or a commutative application is kept literally. -/
def Pat.hasNary : Pat → Bool
  | .var _ => false
  | .plain _ args => Pat.hasNaryList args
  | .comm _ p q => p.hasNary || q.hasNary
  | .assoc .. => true
  | .ac .. => true
  | .aci .. => true
def Pat.hasNaryList : List Pat → Bool
  | [] => false
  | p :: ps => p.hasNary || Pat.hasNaryList ps
end

theorem Pat.hasNaryList_eq_false {args : List Pat} :
    Pat.hasNaryList args = false ↔ ∀ p ∈ args, p.hasNary = false := by
  induction args with
  | nil => simp [Pat.hasNaryList]
  | cons p ps ih => simp [Pat.hasNaryList, ih]

/-- Whether an action builds an n-ary term. -/
def Action.hasNary : Action → Bool
  | .insert t => t.hasNary
  | .union a b => a.hasNary || b.hasNary
  | .subsume _ => false

/-- Whether some action of the rule builds an n-ary term: the rules the
semi-naive loop matches in full after a round whose rebuild rewrote a stored
node non-literally (`respelled`, `saturate.rs`). -/
def Rule.buildsNary (rule : Rule) : Bool := rule.actions.any Action.hasNary

/-- The consequence of one action is present in `G` under `σ`. -/
def ActFired (G : Graph) (σ : Binding) : Action → Prop
  | .insert t => ∃ c, Den G σ t c
  -- both values are representatives, so one class is `find` equality
  | .union a b => ∃ c, Den G σ a c ∧ Den G σ b c
  | .subsume _ => True

/-- Every consequence of the instance `(rule, σ)` is present in `G`. -/
def Fired (G : Graph) (σ : Binding) (rule : Rule) : Prop :=
  ∀ act ∈ rule.actions, ActFired G σ act

/-- The union's two sides have the same `find`: the form of `ActFired` for a
union stated with `find`. -/
theorem actFired_union_find {G : Graph} (hidem : G.FindIdem) {σ : Binding} {a b : Pat}
    {c₁ c₂ : C} (ha : Den G σ a c₁) (hb : Den G σ b c₂) (hf : G.find c₁ = G.find c₂) :
    ActFired G σ (.union a b) := by
  refine ⟨c₁, ha, ?_⟩
  have : c₁ = c₂ := by rw [← ha.find_eq hidem, ← hb.find_eq hidem, hf]
  exact this ▸ hb

end Semper.EMatch
