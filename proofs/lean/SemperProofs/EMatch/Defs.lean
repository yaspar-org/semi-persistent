import Mathlib

/-!
# E-matching under maximum-partition semantics: definitions

Formalizes parts (a) and (b) of the proof sketch
`notes-ematch-proof.md`: the abstract e-graph, the pattern language, the
binding, and the declarative matching relation `MatchC` / `MatchN`.

Modelling choices (sketch part (h)):
* e-class ids, node ids, symbols and variables are `Nat`;
* an e-node is a head symbol with children of one kind (tuple, sorted pair,
  sequence, multiset, set);
* the binding is a structure of partial maps (`Var → Option _`);
* `MatchC` / `MatchN` is a mutually inductive `Prop`; the AC clause chooses a
  duplicate-free list `taken` of children (the injection `a`), each element
  takes the whole count of its child, and the rest is the complement.

Not modelled: literals, sequence-filter patterns `(..fs P)`, predicates.
-/

namespace Semper.EMatch

/-- E-class identifier. -/
abbrev C := Nat
/-- Operator symbol. -/
abbrev Sym := Nat
/-- E-node identifier. -/
abbrev NodeId := Nat
/-- Pattern variable (e-class, node, multiplicity or rest variable). -/
abbrev Var := Nat

/-- Children of an e-node, shaped by the kind of its operator
(sketch, table in (a)). The `spair` invariant `a ≤ b` is not enforced by
the type. -/
inductive Children where
  /-- Plain operator of arity `k`: a `k`-tuple of e-classes. -/
  | tuple (cs : List C)
  /-- Commutative operator: a sorted pair. -/
  | spair (a b : C)
  /-- Associative operator: a sequence. -/
  | seq (cs : List C)
  /-- AC operator: a multiset (class with count). -/
  | mset (m : Multiset C)
  /-- ACI operator: a finite set. -/
  | set (s : Finset C)
  deriving DecidableEq

/-- An e-node: a head symbol and its children. -/
structure Node where
  op : Sym
  children : Children
  deriving DecidableEq

/-- An e-graph read through the frozen representative snapshot: a finite list
of identified e-nodes and the representative map `find`. -/
structure Graph where
  nodes : List (NodeId × Node)
  find : NodeId → C

/-- Child class at a position, for tuple, sorted-pair and sequence nodes. -/
def Children.childAt : Children → Nat → Option C
  | .tuple cs, i => cs[i]?
  | .seq cs, i => cs[i]?
  | .spair a _, 0 => some a
  | .spair _ b, 1 => some b
  | .spair _ _, _ => none
  | .mset _, _ => none
  | .set _, _ => none

/-- Whether the node kind is variadic (sequence, multiset or set): the kinds
the `by_contains` index files. -/
def Children.isVariadic : Children → Bool
  | .seq _ => true
  | .mset _ => true
  | .set _ => true
  | _ => false

/-- Membership of a class among the children of a variadic node. -/
def Children.containsClass (ch : Children) (c : C) : Bool :=
  match ch with
  | .seq cs => decide (c ∈ cs)
  | .mset m => decide (c ∈ m)
  | .set s => decide (c ∈ s)
  | _ => false

/-- `members(c, f)`: the identified nodes of class `c` with head `f`. -/
def Graph.members (G : Graph) (c : C) (f : Sym) : List (NodeId × Node) :=
  G.nodes.filter (fun p => G.find p.1 = c ∧ p.2.op = f)

/-- Multiplicity annotation of an AC element pattern. `exact m` is a fixed
count; `var k lo hi` is a multiplicity variable `k` with interval
`[lo, hi]` (`hi = none` is unbounded). `:k` is `var k 1 none`,
`:k >= 2` is `var k 2 none`, an omitted annotation is `exact 1`. -/
inductive Mult where
  | exact (m : Nat)
  | var (k : Var) (lo : Nat) (hi : Option Nat)
  deriving DecidableEq

/-- Patterns (sketch (b)). -/
inductive Pat where
  /-- An e-class variable; may occur several times (non-linear). -/
  | var (x : Var)
  /-- Plain application `f(P_1, ..., P_k)`. -/
  | plain (f : Sym) (args : List Pat)
  /-- Commutative application `f(P_1, P_2)`. -/
  | comm (f : Sym) (p q : Pat)
  /-- Associative application `f[R_pre? ; P_1, ..., P_k ; R_suf?]`. -/
  | assoc (f : Sym) (pre : Option Var) (args : List Pat) (suf : Option Var)
  /-- AC application `f{(P_1 : μ_1), ..., (P_p : μ_p) ; R?}`. -/
  | ac (f : Sym) (elems : List (Pat × Mult)) (rest : Option Var)
  /-- ACI application `f{P_1, ..., P_p ; R?}`. -/
  | aci (f : Sym) (elems : List Pat) (rest : Option Var)

/-- Head symbol of an application pattern; `none` for a variable. -/
def Pat.head : Pat → Option Sym
  | .var _ => none
  | .plain f _ => some f
  | .comm f _ _ => some f
  | .assoc f _ _ _ => some f
  | .ac f _ _ => some f
  | .aci f _ _ => some f

/-- A binding: partial maps from variables to e-classes, node ids,
multiplicities, multiset rests, sequence rests and set rests. -/
structure Binding where
  cls : Var → Option C
  node : Var → Option NodeId
  mult : Var → Option Nat
  rest : Var → Option (Multiset C)
  seqRest : Var → Option (List C)
  finRest : Var → Option (Finset C)

namespace Binding

/-- The empty binding. -/
def empty : Binding :=
  ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => none, fun _ => none,
    fun _ => none⟩

def setCls (σ : Binding) (x : Var) (c : C) : Binding :=
  { σ with cls := Function.update σ.cls x (some c) }

def setNode (σ : Binding) (v : Var) (id : NodeId) : Binding :=
  { σ with node := Function.update σ.node v (some id) }

def setMult (σ : Binding) (k : Var) (m : Nat) : Binding :=
  { σ with mult := Function.update σ.mult k (some m) }

def setRest (σ : Binding) (r : Var) (m : Multiset C) : Binding :=
  { σ with rest := Function.update σ.rest r (some m) }

def setSeqRest (σ : Binding) (r : Var) (u : List C) : Binding :=
  { σ with seqRest := Function.update σ.seqRest r (some u) }

def setSetRest (σ : Binding) (r : Var) (s : Finset C) : Binding :=
  { σ with finRest := Function.update σ.finRest r (some s) }

/-- `Extends σ σ'`: every entry bound in `σ` is bound to the same value in
`σ'`. -/
def Extends (σ σ' : Binding) : Prop :=
  (∀ x c, σ.cls x = some c → σ'.cls x = some c) ∧
  (∀ v id, σ.node v = some id → σ'.node v = some id) ∧
  (∀ k m, σ.mult k = some m → σ'.mult k = some m) ∧
  (∀ r m, σ.rest r = some m → σ'.rest r = some m) ∧
  (∀ r u, σ.seqRest r = some u → σ'.seqRest r = some u) ∧
  (∀ r s, σ.finRest r = some s → σ'.finRest r = some s)

theorem Extends.refl (σ : Binding) : Extends σ σ :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h, fun _ _ h => h⟩

theorem Extends.trans {σ₁ σ₂ σ₃ : Binding} (h₁ : Extends σ₁ σ₂)
    (h₂ : Extends σ₂ σ₃) : Extends σ₁ σ₃ :=
  ⟨fun x c h => h₂.1 x c (h₁.1 x c h),
    fun v id h => h₂.2.1 v id (h₁.2.1 v id h),
    fun k m h => h₂.2.2.1 k m (h₁.2.2.1 k m h),
    fun r m h => h₂.2.2.2.1 r m (h₁.2.2.2.1 r m h),
    fun r u h => h₂.2.2.2.2.1 r u (h₁.2.2.2.2.1 r u h),
    fun r s h => h₂.2.2.2.2.2 r s (h₁.2.2.2.2.2 r s h)⟩

end Binding

/-- `m ⊨ μ` under `σ` (sketch (b), AC clause): an exact annotation fixes the
count; a multiplicity variable is bound to the count and the count lies in
the interval. -/
def MultOk (σ : Binding) : Mult → Nat → Prop
  | .exact k, m => m = k
  | .var k lo hi, m => σ.mult k = some m ∧ lo ≤ m ∧ ∀ h ∈ hi, m ≤ h

/-- A sequence rest variable binds the given side; an absent rest forces the
side empty. -/
def SeqRestOk (σ : Binding) : Option Var → List C → Prop
  | none, u => u = []
  | some r, u => σ.seqRest r = some u

/-- The multiset rest: the children not taken, with their counts; without a
rest every child is taken. -/
def MsetRestOk (σ : Binding) (rest : Option Var) (m : Multiset C)
    (taken : List C) : Prop :=
  match rest with
  | none => ∀ c ∈ m, c ∈ taken
  | some r => σ.rest r = some (m.filter (fun c => c ∉ taken))

/-- The set rest: the children not taken; without a rest every child is
taken. -/
def SetRestOk (σ : Binding) (rest : Option Var) (s : Finset C)
    (taken : List C) : Prop :=
  match rest with
  | none => ∀ c ∈ s, c ∈ taken
  | some r => σ.finRest r = some (s.filter (fun c => c ∉ taken))

mutual
/-- `MatchC G P c σ`: pattern `P` matches at e-class `c` under `σ`. -/
inductive MatchC (G : Graph) : Pat → C → Binding → Prop
  | var {x : Var} {c : C} {σ : Binding} :
      σ.cls x = some c → MatchC G (.var x) c σ
  | app {P : Pat} {c : C} {σ : Binding} {id : NodeId} {n : Node} :
      (id, n) ∈ G.nodes → G.find id = c → P.head = some n.op →
      MatchN G P n σ → MatchC G P c σ
/-- `MatchN G P n σ`: pattern `P` matches the e-node `n` under `σ`
(maximum-partition semantics for AC and ACI). -/
inductive MatchN (G : Graph) : Pat → Node → Binding → Prop
  | plain {f : Sym} {args : List Pat} {cs : List C} {σ : Binding} :
      args.length = cs.length →
      (∀ pc ∈ args.zip cs, MatchC G pc.1 pc.2 σ) →
      MatchN G (.plain f args) ⟨f, .tuple cs⟩ σ
  | comm₁ {f : Sym} {p q : Pat} {a b : C} {σ : Binding} :
      MatchC G p a σ → MatchC G q b σ →
      MatchN G (.comm f p q) ⟨f, .spair a b⟩ σ
  | comm₂ {f : Sym} {p q : Pat} {a b : C} {σ : Binding} :
      MatchC G p b σ → MatchC G q a σ →
      MatchN G (.comm f p q) ⟨f, .spair a b⟩ σ
  | assoc {f : Sym} {pre suf : Option Var} {args : List Pat}
      {u mid v : List C} {σ : Binding} :
      args.length = mid.length →
      SeqRestOk σ pre u → SeqRestOk σ suf v →
      (∀ pc ∈ args.zip mid, MatchC G pc.1 pc.2 σ) →
      MatchN G (.assoc f pre args suf) ⟨f, .seq (u ++ mid ++ v)⟩ σ
  | ac {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var}
      {m : Multiset C} {taken : List C} {σ : Binding} :
      taken.Nodup → elems.length = taken.length →
      (∀ c ∈ taken, c ∈ m) →
      (∀ et ∈ elems.zip taken, MatchC G et.1.1 et.2 σ) →
      (∀ et ∈ elems.zip taken, MultOk σ et.1.2 (m.count et.2)) →
      MsetRestOk σ rest m taken →
      MatchN G (.ac f elems rest) ⟨f, .mset m⟩ σ
  | aci {f : Sym} {elems : List Pat} {rest : Option Var}
      {s : Finset C} {taken : List C} {σ : Binding} :
      taken.Nodup → elems.length = taken.length →
      (∀ c ∈ taken, c ∈ s) →
      (∀ et ∈ elems.zip taken, MatchC G et.1 et.2 σ) →
      SetRestOk σ rest s taken →
      MatchN G (.aci f elems rest) ⟨f, .set s⟩ σ
end

end Semper.EMatch
