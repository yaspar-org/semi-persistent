import SemperProofs.EMatch.Ref

/-!
# `:flatten` views: definitions

The views of an n-ary node under the `:flatten` tag (`spec-flatten.md`
§1), the demand rule (§2), the declarative flattened matching relation
(§4.1) and the reference enumerator (§4.2).

The vocabulary is that of `EMatch/Defs.lean` and `EMatch/Ref.lean`:
`Graph`, `Node`, `Children`, `Pat`, `Binding`, `MatchC`, `MultOk`,
`MsetRestOk`, `SetRestOk`, `SeqRestOk`, `Multiset.entries`, `ofEntries`.

Modelling choices:
* the index's skip predicate (`index.rs:521-538`) is the parameter
  `Ctx.filed`; a node is an `f`-member of `X` iff it is filed, has
  representative `X` and operator `f` (§1.1);
* the opening trees are one inductive relation `OT` over a list of child
  positions; the spec's `ViewOpt`/`ViewKids`/`ViewNode` are its derived
  forms (`ViewOpt`, `ViewNode`, `RawView`), with the spec's constructor
  shapes recovered as lemmas in `Enum.lean`;
* multiplicities are `Nat` (no width), and the three enumeration bounds of
  §3 are not modelled: the reference enumerator is unbounded, and
  `WithinBounds` records the hypothesis under which the engine's
  enumeration is the reference one (§4.4);
* `normalize` is defined concretely per kind (§1.4) with the laws
  (identity class, nilpotent order, resolved inverse map) as parameters;
  the inverse map `inv : C → Option C` is the resolved
  `inverse_class(laws.inverse, ·)` (§5 Q2).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Kinds, children, members (§1.1, §1.2) -/

/-- `FlatKind` (`flatten.rs:59-64`): the folds are `assoc`. -/
inductive FlatKind where
  | assoc
  | ac
  | aci
  deriving DecidableEq, Repr

/-- `kids κ ch`: the `(class, count)` list the walk reads for a node of
kind `κ` (§1.2); a shape mismatch reads no children. -/
def kids : FlatKind → Children → List (C × Nat)
  | .assoc, .seq cs => cs.map (fun c => (c, 1))
  | .ac, .mset m => Multiset.entries m
  | .aci, .set s => (s.sort (· ≤ ·)).map (fun c => (c, 1))
  | _, _ => []

/-- The context of one `Flatten` step: the graph, the operator, the kind
and the index's filing predicate. -/
structure Ctx where
  G : Graph
  f : Sym
  κ : FlatKind
  filed : NodeId → Bool

/-- `(id, m)` is an `f`-member of class `X`: filed, of representative `X`
and operator `f` (§1.1, `flatten.rs:623, 689`). -/
def Ctx.IsMember (ctx : Ctx) (id : NodeId) (m : Node) (X : C) : Prop :=
  (id, m) ∈ ctx.G.nodes ∧ ctx.filed id = true ∧ ctx.G.find id = X ∧ m.op = ctx.f

/-- The `f`-members of `X`, as a list (`by_repr[X] ∩ by_op[f]`). -/
def Ctx.members (ctx : Ctx) (X : C) : List (NodeId × Node) :=
  ctx.G.nodes.filter
    (fun p => decide (ctx.filed p.1 = true ∧ ctx.G.find p.1 = X ∧ p.2.op = ctx.f))

theorem Ctx.mem_members {ctx : Ctx} {X : C} {p : NodeId × Node} :
    p ∈ ctx.members X ↔ ctx.IsMember p.1 p.2 X := by
  simp [Ctx.members, Ctx.IsMember]

/-- The classes of the graph: the path of an opening tree lives in this
finite set. -/
def classesOf (G : Graph) : Finset C :=
  (G.nodes.map (fun p => G.find p.1)).toFinset

/-! ## Opening trees and raw views (§1.3) -/

/-- The leaf groups of an opening instance: when nothing is opened below it
(`ls = []`) the instance is a leaf and its group is the classes directly
under it (`flatten.rs:376-390`, `flatten_differential.rs:204-210`). -/
def leafify (v : List (C × Nat)) (ls : List (List C)) : List (List C) :=
  if ls = [] then [v.map Prod.fst] else ls

/-- `scale k ks`: the children `ks` with every count multiplied by `k`. -/
def scale (k : Nat) (ks : List (C × Nat)) : List (C × Nat) :=
  ks.map (fun e => (e.1, k * e.2))

/-- `OT ctx k P ks v ls`: an opening tree over the child positions `ks`,
reached with inherited multiplicity `k` and path `P`, gives the raw view
`v` with leaf groups `ls` (the spec's `ViewKids`, with `ViewOpt` inlined
as the two constructors `keep` and `opn`). -/
inductive OT (ctx : Ctx) : Nat → Finset C → List (C × Nat) → List (C × Nat) →
    List (List C) → Prop
  | nil {k : Nat} {P : Finset C} : OT ctx k P [] [] []
  /-- Keep the class whole: always an option (`flatten.rs:669-681`). -/
  | keep {k : Nat} {P : Finset C} {X : C} {j : Nat} {rest v₂ : List (C × Nat)}
      {l₂ : List (List C)} :
      OT ctx k P rest v₂ l₂ → OT ctx k P ((X, j) :: rest) ((X, k * j) :: v₂) l₂
  /-- Open `X` through an `f`-member `m`, unless `X` is on the path; the
  member's children inherit the multiplicity `k * j`, and its view is
  spliced in place (`flatten.rs:682-729`). -/
  | opn {k : Nat} {P : Finset C} {X : C} {j : Nat} {rest : List (C × Nat)}
      {id : NodeId} {m : Node} {v₁ v₂ : List (C × Nat)} {l₁ l₂ : List (List C)} :
      X ∉ P → ctx.IsMember id m X →
      OT ctx (k * j) (insert X P) (kids ctx.κ m.children) v₁ l₁ →
      OT ctx k P rest v₂ l₂ →
      OT ctx k P ((X, j) :: rest) (v₁ ++ v₂) (leafify v₁ l₁ ++ l₂)

/-- The spec's `ViewNode`: the view of node `m` reached with multiplicity
`k` and path `P`. -/
def ViewNode (ctx : Ctx) (m : Node) (k : Nat) (P : Finset C) (v : List (C × Nat))
    (ls : List (List C)) : Prop :=
  OT ctx k P (kids ctx.κ m.children) v ls

/-- The spec's `ViewOpt`: the options of one child position of class `X`
with multiplicity `k`. -/
def ViewOpt (ctx : Ctx) (X : C) (k : Nat) (P : Finset C) (v : List (C × Nat))
    (ls : List (List C)) : Prop :=
  (v = [(X, k)] ∧ ls = []) ∨
    (X ∉ P ∧ ∃ id m l₁, ctx.IsMember id m X ∧
      ViewNode ctx m k (insert X P) v l₁ ∧ ls = leafify v l₁)

/-- A raw view of the root node `n`: path empty, multiplicity 1
(`flatten.rs:585-592`). -/
def RawView (ctx : Ctx) (n : Node) (v : List (C × Nat)) (ls : List (List C)) : Prop :=
  ViewNode ctx n 1 ∅ v ls

/-! ## Canonization (§1.4) -/

/-- The laws of one operator, with the inverse already resolved to a map on
classes (`inverse_class(laws.inverse, ·)`, `flatten.rs:519-527`). -/
structure Laws where
  unit : Option C
  nilpotent : Option Nat
  inv : Option (C → Option C)

/-- The laws-free operator. -/
def Laws.free : Laws := ⟨none, none, none⟩

/-- `Normal` (`nary_canon.rs:46-59`), without `Overflow` (counts are `Nat`). -/
inductive Normal where
  | node (w : List (C × Nat))
  | unit
  | single (c : C)
  | empty
  deriving DecidableEq

/-- AC kind step: sort by class and sum equal classes (`nary_canon.rs:105-120`). -/
def coalesce (v : List (C × Nat)) : List (C × Nat) :=
  Multiset.entries (ofEntries v)

/-- ACI kind step: sort, dedup, counts one (`nary_canon.rs:98-104`). -/
def dedupAci (v : List (C × Nat)) : List (C × Nat) :=
  ((v.map Prod.fst).toFinset.sort (· ≤ ·)).map (fun c => (c, 1))

/-- Identity drop (`nary_canon.rs:122-124`). -/
def dropUnit (u : Option C) (v : List (C × Nat)) : List (C × Nat) :=
  match u with
  | none => v
  | some u => v.filter (fun e => e.1 ≠ u)

/-- Nilpotent clamp (`nary_canon.rs:125-132`). -/
def clamp (r : Option Nat) (v : List (C × Nat)) : List (C × Nat) :=
  match r with
  | none => v
  | some r => (v.map (fun e => (e.1, e.2 % r))).filter (fun e => e.2 ≠ 0)

/-- One iteration of `cancel_by` at index `i` (`nary_canon.rs:181-209`). -/
def cancelAt (inv : C → Option C) (l : List (C × Nat)) (i : Nat) : List (C × Nat) :=
  match l[i]? with
  | none => l
  | some (x, xc) =>
      if xc = 0 then l
      else
        match inv x with
        | none => l
        | some y =>
            if y = x then (if 1 < xc then l.set i (x, xc % 2) else l)
            else
              match l.findIdx? (fun e => e.1 = y) with
              | none => l
              | some j =>
                  match l[j]? with
                  | none => l
                  | some (_, yc) =>
                      let t := min xc yc
                      (l.set i (x, xc - t)).set j (y, yc - t)

/-- The first `i` iterations of the cancellation pass. -/
def cancelSteps (inv : C → Option C) (l : List (C × Nat)) : Nat → List (C × Nat)
  | 0 => l
  | i + 1 => cancelAt inv (cancelSteps inv l i) i

/-- Inverse-pair cancellation (`nary_canon.rs:168-214`): the sequential pass
over every index, then the zero entries removed. -/
def cancel (inv : C → Option C) (l : List (C × Nat)) : List (C × Nat) :=
  (cancelSteps inv l l.length).filter (fun e => e.2 ≠ 0)

/-- The normalized child list, before the degenerate-arity classification
(`nary_canon.rs:96-138`). -/
def normalizeList (κ : FlatKind) (laws : Laws) (v : List (C × Nat)) : List (C × Nat) :=
  let v₁ := match κ with
    | .assoc => v
    | .aci => dedupAci v
    | .ac => coalesce v
  let v₂ := dropUnit laws.unit v₁
  match κ with
  | .ac =>
      let v₃ := clamp laws.nilpotent v₂
      match laws.inv with
      | none => v₃
      | some inv => cancel inv v₃
  | _ => v₂

/-- Degenerate arity (`nary_canon.rs:139-144`). -/
def classify (unit : Option C) : List (C × Nat) → Normal
  | [] => if unit.isSome then .unit else .empty
  | [(c, 1)] => .single c
  | w => .node w

/-- `normalize` (`nary_canon.rs:65-145`) over `Nat` counts. -/
def normalize (κ : FlatKind) (laws : Laws) (v : List (C × Nat)) : Normal :=
  classify laws.unit (normalizeList κ laws v)

/-! ## Distinct canonical views and their demand (§1.5) -/

/-- The canonical views of `n`. -/
def Views (ctx : Ctx) (laws : Laws) (n : Node) : Set (List (C × Nat)) :=
  { w | ∃ v ls, RawView ctx n v ls ∧ normalize ctx.κ laws v = .node w }

/-- The opening trees giving the view `w`, each as its leaf groups. -/
def Alts (ctx : Ctx) (laws : Laws) (n : Node) (w : List (C × Nat)) :
    Set (List (List C)) :=
  { ls | ∃ v, RawView ctx n v ls ∧ normalize ctx.κ laws v = .node w }

/-- `Demand` (`flatten.rs:196-200`). -/
structure Demand where
  unconditional : Bool
  alts : List (List (List C))
  deriving DecidableEq

/-- The default demand: a register never written accepts everything
(`flatten.rs:202-209`, `ematch.rs:591-594`). -/
def Demand.default : Demand := ⟨true, []⟩

/-- `Demand.accepts` (`flatten.rs:213-219`): unconditional, or some opening
tree has every leaf group hit by a taken class. -/
def Demand.accepts (d : Demand) (taken : List C) : Prop :=
  d.unconditional = true ∨ ∃ ls ∈ d.alts, ∀ g ∈ ls, ∃ c ∈ g, c ∈ taken

/-- The executable form of `Demand.accepts`. -/
def Demand.acceptsB (d : Demand) (taken : List C) : Bool :=
  d.unconditional || d.alts.any (fun ls => ls.all (fun g => g.any (fun c => decide (c ∈ taken))))

theorem Demand.acceptsB_iff (d : Demand) (taken : List C) :
    d.acceptsB taken = true ↔ d.accepts taken := by
  simp [Demand.acceptsB, Demand.accepts]

/-- The demand rule on the set of opening trees of a view (§2.1): some tree
opens nothing, or some tree has every leaf group hit. -/
def AltsAccept (A : Set (List (List C))) (taken : List C) : Prop :=
  [] ∈ A ∨ ∃ ls ∈ A, ∀ g ∈ ls, ∃ c ∈ g, c ∈ taken

/-! ## The reference enumerator (§4.2) -/

/-- A raw view with its leaf groups. -/
abbrev Raw := List (C × Nat) × List (List C)

/-- The product over the child positions of each position's options
(`flatten_differential.rs:195-227`). -/
def kidsOf (opt : C → Nat → Finset C → List Raw) :
    List (C × Nat) → Nat → Finset C → List Raw
  | [], _, _ => [([], [])]
  | (X, j) :: rest, k, P =>
      (opt X (k * j) P).flatMap (fun r₁ =>
        (kidsOf opt rest k P).map (fun r₂ => (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2)))

/-- The options of one child position: keep, or open through each
`f`-member when the class is not on the path; `fuel` bounds the opening
depth. -/
def rawOpt (ctx : Ctx) : Nat → C → Nat → Finset C → List Raw
  | 0, X, k, _ => [([(X, k)], [])]
  | fuel + 1, X, k, P =>
      ([(X, k)], []) ::
        (if X ∈ P then []
         else (ctx.members X).flatMap (fun p =>
           (kidsOf (rawOpt ctx fuel) (kids ctx.κ p.2.children) k (insert X P)).map
             (fun r => (r.1, leafify r.1 r.2))))

/-- The raw views of node `m` with inherited multiplicity `k` and path `P`. -/
def rawNode (ctx : Ctx) (fuel : Nat) (m : Node) (k : Nat) (P : Finset C) : List Raw :=
  kidsOf (rawOpt ctx fuel) (kids ctx.κ m.children) k P

/-- Enough fuel: the path is a set of classes of the graph and grows by one
per opening. -/
def fuelOf (G : Graph) : Nat := (classesOf G).card

/-- The raw views of the root `n` (path empty, multiplicity 1), canonized;
a raw view whose normal form is not a node is dropped (`flatten.rs:333-334`). -/
def rawRecords (ctx : Ctx) (laws : Laws) (n : Node) : List Raw :=
  (rawNode ctx (fuelOf ctx.G) n 1 ∅).filterMap (fun r =>
    match normalize ctx.κ laws r.1 with
    | .node w => some (w, r.2)
    | _ => none)

/-- The leaf groups of the records giving `w`. -/
def altsOf (recs : List Raw) (w : List (C × Nat)) : List (List (List C)) :=
  (recs.filter (fun r => r.1 = w)).map Prod.snd

/-- `demand_into` (`flatten.rs:286-302`) over a record list. -/
def demandOf (recs : List Raw) (w : List (C × Nat)) : Demand :=
  if [] ∈ altsOf recs w then ⟨true, []⟩ else ⟨false, altsOf recs w⟩

/-- `dedup` (`flatten.rs:402-421`): the distinct views with their demands. -/
def enumerateFrom (recs : List Raw) : List (List (C × Nat) × Demand) :=
  (recs.map Prod.fst).dedup.map (fun w => (w, demandOf recs w))

/-- `flatten::enumerate` as a list function. -/
def enumerate (ctx : Ctx) (laws : Laws) (n : Node) : List (List (C × Nat) × Demand) :=
  enumerateFrom (rawRecords ctx laws n)

/-- Every leaf group holds a takeable class (§2.3). -/
def leavesMeet (T : C → Bool) (ls : List (List C)) : Bool :=
  ls.all (fun g => g.any T)

/-- The enumeration pruned by `takeable` (§2.3): only the trees whose every
leaf group meets `T` are recorded. -/
def enumeratePruned (T : C → Bool) (ctx : Ctx) (laws : Laws) (n : Node) :
    List (List (C × Nat) × Demand) :=
  enumerateFrom ((rawRecords ctx laws n).filter (fun r => leavesMeet T r.2))

/-! ## Bounds (§3, §4.4) -/

/-- Every count of every raw view and every coalesced sum fits the width
`W`: the product skip and the sum drop of §3 are absent. -/
def FitsWidth (W : Nat) (ctx : Ctx) (n : Node) : Prop :=
  ∀ v ls, RawView ctx n v ls → (∀ e ∈ v, e.2 ≤ W) ∧ (∀ e ∈ coalesce v, e.2 ≤ W)

/-- The hypothesis under which the engine's enumeration of `n` is the
reference enumeration: counts fit the width. The three count bounds of §3
(`MAX_VIEWS`, `MAX_WORK`, `MAX_ELEMS`) are not modelled; the engine's
`Err(OVER_BOUND)` makes the node contribute no view at all, and this
development says nothing about such a node. -/
structure WithinBounds (W : Nat) (ctx : Ctx) (n : Node) : Prop where
  fitsWidth : FitsWidth W ctx n

/-! ## Matching on views (§4.1) -/

/-- The children the decomposition sees for a view. -/
def ofView : FlatKind → List (C × Nat) → Children
  | .assoc, w => .seq (w.map Prod.fst)
  | .ac, w => .mset (ofEntries w)
  | .aci, w => .set (w.map Prod.fst).toFinset

/-- `MatchV G P ch σ taken`: the n-ary clauses of `MatchN` with the taken
classes exposed (assoc: the fixed middle; ac, aci: the `taken` list). -/
inductive MatchV (G : Graph) : Pat → Children → Binding → List C → Prop
  | assoc {f : Sym} {pre suf : Option Var} {args : List Pat}
      {u mid v : List C} {σ : Binding} :
      args.length = mid.length →
      SeqRestOk σ pre u → SeqRestOk σ suf v →
      (∀ pc ∈ args.zip mid, MatchC G pc.1 pc.2 σ) →
      MatchV G (.assoc f pre args suf) (.seq (u ++ mid ++ v)) σ mid
  | ac {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var}
      {m : Multiset C} {taken : List C} {σ : Binding} :
      taken.Nodup → elems.length = taken.length →
      (∀ c ∈ taken, c ∈ m) →
      (∀ et ∈ elems.zip taken, MatchC G et.1.1 et.2 σ) →
      (∀ et ∈ elems.zip taken, MultOk σ et.1.2 (m.count et.2)) →
      MsetRestOk σ rest m taken →
      MatchV G (.ac f elems rest) (.mset m) σ taken
  | aci {f : Sym} {elems : List Pat} {rest : Option Var}
      {s : Finset C} {taken : List C} {σ : Binding} :
      taken.Nodup → elems.length = taken.length →
      (∀ c ∈ taken, c ∈ s) →
      (∀ et ∈ elems.zip taken, MatchC G et.1 et.2 σ) →
      SetRestOk σ rest s taken →
      MatchV G (.aci f elems rest) (.set s) σ taken

/-- `MatchFlat`: the n-ary pattern `P` matches node `n` through some
canonical view, with the demand rule on the classes the items take. -/
def MatchFlat (ctx : Ctx) (laws : Laws) (P : Pat) (n : Node) (σ : Binding) : Prop :=
  ∃ w ∈ Views ctx laws n, ∃ taken,
    MatchV ctx.G P (ofView ctx.κ w) σ taken ∧ AltsAccept (Alts ctx laws n w) taken

/-- The classes a list of item variables is bound to. -/
def takenOf (σ : Binding) (xs : List Var) : List C :=
  xs.filterMap σ.cls

end Semper.EMatch.Flatten
