import Conform.Case

/-!
# Multi-round conformance programs: generation

A case is a small e-graph built from nullary constants `C0..Cn` (`union`
lines, some merging two constants so that a class is heavier than another),
zero to two globals bound to constants, two to four rules whose right-hand
sides build terms, and `(run k)` with `k ∈ [2, 5]`.

Operators: `F` plain (arity 1 or 2), `G` `:comm`, `Cat` `:assoc`, `Add`
`:assoc-comm`, `And` `:assoc-comm-idem`, no laws (no unit, no inverse, so
that the normal form of `add` is the literal child list up to the degenerate
arity, spec-actions §C.1). Symbols: the five shapes are `0..4`
(`Conform.Shape.sym`), constant `Ci` is `10 + i`.

Rule bodies are patterns of `Conform.genApp` (the e-matching generator's
pattern grammar: nested applications, AC multiplicities and multiplicity
variables, rests) sharing class variables, plus `(= x g)` with a global
(written as an equality, or inline in the child position) and `(= x y)`.
Heads are `union` and insert actions over right-hand-side terms: variables,
constants, globals, and plain, pair and n-ary applications splicing the
bound rests and multiplicity variables. A `rewrite` is `union (root, R)`,
occasionally with `:subsume`.

Biases (see the task list in `Main.lean`): a constant merge rule into a
heavy class (the survivor is the class the parents store), a global equated
to a child variable whose class a merge rule absorbs, right-hand sides that
rebuild an existing node (an insert hitting the hash-cons after round 1), a
rule consuming the operator another rule's head builds (a term built in
round r matched in round r+1), two rules feeding each other.
-/

namespace Conform.Rounds

open Semper.EMatch Conform

/-- The symbol of constant `Ci`. -/
def constSym (i : Nat) : Sym := 10 + i

/-- Global `gj` is the class variable `90 + j` (bound only through an
equality filter, never by matching). -/
def globVar (j : Nat) : Var := 90 + j
def isGlobVar (v : Var) : Bool := 90 ≤ v ∧ v < 100

/-- The class variable of the root of body pattern `i`, as
`compile P (rootOf i)` names it. -/
def rootOf (i : Nat) : Var := 1000 * (i + 1)

inductive Act where
  | union (a b : Pat)
  | insert (t : Pat)

structure Eq where
  x : Var
  y : Var          -- a class variable or `globVar j`
  inline : Bool    -- a global written in the child position of `x`

structure RRule where
  body : List Pat
  eqs : List Eq
  acts : List Act
  rewrite : Bool
  subsume : Bool

structure RCase where
  seed : Nat
  idx : Nat
  nC : Nat
  arity : Nat
  globals : List Nat
  init : List String
  rules : List RRule
  k : Nat
  tags : List String

/-! ## Printing -/

def opName (f : Sym) : String :=
  if f ≥ 10 then s!"C{f - 10}" else (Shape.ofSym f).name

def ppVar (inl : List (Var × Nat)) (v : Var) : String :=
  match inl.lookup v with
  | some j => s!"g{j}"
  | none => if isGlobVar v then s!"g{v - 90}" else s!"x{v}"

def ppMultBody : Mult → String
  | .exact 1 => ""
  | .exact m => s!":{m}"
  | .var k lo _ => s!":k{k}" ++ (if lo ≥ 2 then s!">={lo}" else "")

def ppMultRhs : Mult → String
  | .exact 1 => ""
  | .exact m => s!":{m}"
  | .var k _ _ => s!":k{k}"

partial def ppP (inl : List (Var × Nat)) (rhs : Bool) : Pat → String
  | .var x => ppVar inl x
  | .plain f [] => s!"({opName f})"
  | .plain f args => s!"({opName f} " ++ " ".intercalate (args.map (ppP inl rhs)) ++ ")"
  | .comm f p q => s!"({opName f} {ppP inl rhs p} {ppP inl rhs q})"
  | .assoc f pre args suf =>
      let pre := match pre with | some r => [s!"..r{r}"] | none => []
      let suf := match suf with | some r => [s!"..r{r}"] | none => []
      s!"({opName f} " ++ " ".intercalate (pre ++ args.map (ppP inl rhs) ++ suf) ++ ")"
  | .ac f elems rest =>
      let rest := match rest with | some r => [s!"..r{r}"] | none => []
      s!"({opName f} " ++ " ".intercalate (elems.map (fun e => ppP inl rhs e.1 ++
        (if rhs then ppMultRhs e.2 else ppMultBody e.2)) ++ rest) ++ ")"
  | .aci f elems rest =>
      let rest := match rest with | some r => [s!"..r{r}"] | none => []
      s!"({opName f} " ++ " ".intercalate (elems.map (ppP inl rhs) ++ rest) ++ ")"

def RRule.inl (r : RRule) : List (Var × Nat) :=
  r.eqs.filterMap fun e => if e.inline then some (e.x, e.y - 90) else none

def ppAct (inl : List (Var × Nat)) : Act → String
  | .union a b => s!"(union {ppP inl true a} {ppP inl true b})"
  | .insert t => ppP inl true t

def RRule.pp (r : RRule) : String :=
  let inl := r.inl
  if r.rewrite then
    match r.body, r.acts with
    | [l], [.union _ rhs] =>
        s!"(rewrite {ppP inl false l} {ppP inl true rhs}" ++ (if r.subsume then " :subsume)" else ")")
    | _, _ => ";; malformed rewrite"
  else
    let used := r.acts.flatMap fun a => match a with
      | .union x y => x.vars ++ y.vars
      | .insert t => t.vars
    let facts := (r.body.zipIdx).map (fun (p, i) =>
        if used.contains (rootOf i) then s!"(= x{rootOf i} {ppP inl false p})" else ppP inl false p) ++
      (r.eqs.filterMap fun e => if e.inline then none else some s!"(= {ppVar [] e.x} {ppVar [] e.y})")
    s!"(rule ({" ".intercalate facts}) ({" ".intercalate (r.acts.map (ppAct inl))}))"

/-! ## Generation -/

def constNode (i : Nat) : String := s!"(C{i})"

/-- An initial node over constants, of a random shape. -/
def genInitNode (nC arity : Nat) (pref : List Nat) : Gen (Shape × String) := do
  let c : Gen Nat := do
    if (← chance 1 2) ∧ !pref.isEmpty then pick pref 0 else nat 0 (nC - 1)
  let sh ← pick Shape.all .plain
  match sh with
  | .plain =>
      let args ← (List.range arity).mapM fun _ => c
      return (sh, "(F " ++ " ".intercalate (args.map constNode) ++ ")")
  | .comm => return (sh, s!"(G {constNode (← c)} {constNode (← c)})")
  | .seq =>
      let n ← nat 2 3
      let args ← (List.range n).mapM fun _ => c
      return (sh, "(Cat " ++ " ".intercalate (args.map constNode) ++ ")")
  | .mset =>
      let n ← nat 1 2
      let args := (← (List.range n).mapM fun _ => c).eraseDups
      let elems ← args.mapM fun a => do
        let m ← if args.length = 1 then nat 2 3 else (do pure (if (← chance 1 4) then 2 else 1))
        pure (constNode a ++ (if m = 1 then "" else s!":{m}"))
      return (sh, "(Add " ++ " ".intercalate elems ++ ")")
  | .set =>
      let n ← nat 2 3
      let args := (← (List.range n).mapM fun _ => c).eraseDups
      let args := if args.length < 2 then (args ++ [(args.headD 0 + 1) % nC]).eraseDups else args
      return (sh, "(And " ++ " ".intercalate (args.map constNode) ++ ")")

/-- The bound variables of a body, by kind. -/
structure Env where
  cls : List Var
  mults : List Var
  acRests : List Var
  aciRests : List Var
  seqRests : List Var
  globals : Nat
  nC : Nat
  arity : Nat

def Env.ofBody (body : List Pat) (nG nC arity : Nat) (extra : List Var) : Env :=
  let vs := (body.flatMap Pat.vars).eraseDups
  { cls := (vs.filter (fun v => v < 90)) ++ extra
    mults := vs.filter (fun v => 100 ≤ v ∧ v < 200)
    acRests := vs.filter (fun v => 200 ≤ v ∧ v < 300)
    aciRests := vs.filter (fun v => 300 ≤ v ∧ v < 400)
    seqRests := vs.filter (fun v => 400 ≤ v ∧ v < 1000)
    globals := nG, nC, arity }

/-- A right-hand-side term. `avoid` is the n-ary shape of the enclosing
application: a same-op n-ary child would be spliced by `add`
(`egraph.rs:1047-1057`), so it is not generated. `want` biases the head. -/
partial def genRhs (env : Env) (fuel : Nat) (avoid : Option Shape) (want : Option Shape) :
    Gen Pat := do
  let r ← nat 1 20
  if want.isNone ∧ (fuel = 0 ∨ r ≤ 8) ∧ !env.cls.isEmpty then
    return .var (← pick env.cls 0)
  if want.isNone ∧ r ≤ 10 then
    if env.globals > 0 ∧ (← chance 1 3) then return .var (globVar (← nat 0 (env.globals - 1)))
    return .plain (constSym (← nat 0 (env.nC - 1))) []
  let shapes := Shape.all.filter (fun s => some s ≠ avoid)
  let sh ← match want with
    | some s => pure s
    | none => pick shapes .plain
  let sub : Gen Pat := genRhs env (fuel - 1) (if sh.kind?.isSome then some sh else none) none
  match sh with
  | .plain => return .plain sh.sym (← (List.range env.arity).mapM fun _ => sub)
  | .comm => return .comm sh.sym (← sub) (← sub)
  | .seq =>
      let rs := env.seqRests
      let pre ← if !rs.isEmpty ∧ (← chance 1 2) then some <$> pick rs 0 else pure none
      let suf ← if !rs.isEmpty ∧ (← chance 1 2) then some <$> pick (rs.filter (some · ≠ pre)) 0 else pure none
      let suf := if suf = some 0 then none else suf
      let n ← if pre.isSome ∨ suf.isSome then nat 1 2 else (do pure (if (← chance 1 5) then 1 else 2))
      return .assoc sh.sym pre (← (List.range n).mapM fun _ => sub) suf
  | .mset =>
      let n ← if (← chance 1 5) then pure 1 else pure 2
      let elems ← (List.range n).mapM fun _ => do
        let p ← sub
        let r ← nat 1 10
        let μ ← if r ≤ 6 then pure (Mult.exact 1) else if r ≤ 8 then pure (Mult.exact 2)
          else if !env.mults.isEmpty then (do pure (Mult.var (← pick env.mults 100) 1 none))
          else pure (Mult.exact 3)
        return (p, μ)
      let rest ← if !env.acRests.isEmpty ∧ (← chance 1 2) then some <$> pick env.acRests 200 else pure none
      return .ac sh.sym elems rest
  | .set =>
      let n ← if (← chance 1 5) then pure 1 else pure 2
      let rest ← if !env.aciRests.isEmpty ∧ (← chance 1 2) then some <$> pick env.aciRests 300 else pure none
      return .aci sh.sym (← (List.range n).mapM fun _ => sub) rest

/-- The head shape of a right-hand side that rebuilds the body's root node
(a hash-cons hit): the same application with its items permuted where the
shape allows it. -/
def rebuildOf : Pat → Option Pat
  | .comm f p q => some (.comm f q p)
  | .aci f elems rest => some (.aci f elems.reverse rest)
  | .ac f elems rest => some (.ac f elems.reverse rest)
  | .plain f args => some (.plain f args)
  | .assoc f pre args suf => some (.assoc f pre args suf)
  | _ => none

/-- The heads (shapes) an action list builds. -/
partial def builtShapes : Pat → List Shape
  | .var _ => []
  | .plain f args => (if f < 10 then [Shape.ofSym f] else []) ++ args.flatMap builtShapes
  | .comm f p q => [Shape.ofSym f] ++ builtShapes p ++ builtShapes q
  | .assoc f _ args _ => [Shape.ofSym f] ++ args.flatMap builtShapes
  | .ac f elems _ => [Shape.ofSym f] ++ elems.flatMap (builtShapes ·.1)
  | .aci f elems _ => [Shape.ofSym f] ++ elems.flatMap builtShapes

def actShapes : Act → List Shape
  | .union a b => builtShapes a ++ builtShapes b
  | .insert t => builtShapes t

/-- The class variables of a body that sit in a child position (all of
them: `genApp` never returns a bare variable at the root). -/
def childVars (body : List Pat) : List Var :=
  ((body.flatMap Pat.vars).filter (· < 90)).eraseDups

partial def renameVar (a b : Var) : Pat → Pat
  | .var x => .var (if x = a then b else x)
  | .plain f args => .plain f (args.map (renameVar a b))
  | .comm f p q => .comm f (renameVar a b p) (renameVar a b q)
  | .assoc f pre args suf => .assoc f pre (args.map (renameVar a b)) suf
  | .ac f elems rest => .ac f (elems.map fun e => (renameVar a b e.1, e.2)) rest
  | .aci f elems rest => .aci f (elems.map (renameVar a b)) rest

/-- A shallow body pattern, likely to match: variables (reused with
probability 1/5), exact multiplicity one or a multiplicity variable, rests
with probability 1/2 (n-ary) or 1/3 (sequence ends), a nested application
of a present shape with probability 1/6 per item. -/
partial def genSimple (arity : Nat) (present : List Shape) (fuel : Nat) (sh : Shape) : PGen Pat := do
  let item : PGen Pat := do
    if fuel > 0 ∧ !present.isEmpty ∧ (← chance 1 6) then
      genSimple arity present (fuel - 1) (← pick present .plain)
    else genVar
  let n : PGen Nat := do if (← chance 1 3) then pure 1 else pure 2
  match sh with
  | .plain => return .plain sh.sym (← (List.range arity).mapM fun _ => item)
  | .comm => return .comm sh.sym (← item) (← item)
  | .seq =>
      let pre ← if (← chance 1 3) then
          some <$> freshRest (·.nextPre) (fun s => { s with nextPre := s.nextPre + 1 }) else pure none
      let args ← (List.range (← n)).mapM fun _ => item
      let suf ← if (← chance 1 3) then
          some <$> freshRest (·.nextSuf) (fun s => { s with nextSuf := s.nextSuf + 1 }) else pure none
      return .assoc sh.sym pre args suf
  | .mset =>
      let elems ← (List.range (← n)).mapM fun _ => do
        let p ← item
        let μ ← if (← chance 1 6) then (do
            let st ← get
            set { st with nextMult := st.nextMult + 1, usedMult := st.usedMult ++ [st.nextMult] }
            pure (Mult.var st.nextMult 1 none)) else pure (Mult.exact 1)
        return (p, μ)
      let rest ← if (← chance 1 2) then
          some <$> freshRest (·.nextAc) (fun s => { s with nextAc := s.nextAc + 1 }) else pure none
      return .ac sh.sym elems rest
  | .set =>
      -- an ACI node holds distinct classes: fresh variables
      let fresh : PGen Pat := do
        let st ← get
        set { st with nextCls := st.nextCls + 1, used := st.used ++ [st.nextCls] }
        return Pat.var st.nextCls
      let elems ← (List.range (← n)).mapM fun _ => do
        if fuel > 0 ∧ !present.isEmpty ∧ (← chance 1 6) then
          genSimple arity present (fuel - 1) (← pick present .plain)
        else fresh
      let rest ← if (← chance 1 2) then
          some <$> freshRest (·.nextAci) (fun s => { s with nextAci := s.nextAci + 1 }) else pure none
      return .aci sh.sym elems rest

def genBody (arity : Nat) (present : List Shape) (root : Shape) (n : Nat) : Gen (List Pat) := do
  let widths : Shape → List Nat := fun _ => [2, 3]
  let mut st : PState := {}
  let mut out : List Pat := []
  for i in List.range n do
    let sh ← if i = 0 then pure root else pick present .plain
    let (p, st') ← if (← chance 1 4) then (genApp 1 arity widths present sh).run st
      else (genSimple arity present 1 sh).run st
    st := st'
    out := out ++ [p]
  -- a second pattern shares a class variable with the first
  match out with
  | [p, q] =>
      let vp := (p.vars.filter (· < 90)).eraseDups
      let vq := (q.vars.filter (· < 90)).eraseDups
      if vp.any (vq.contains ·) ∨ vp.isEmpty ∨ vq.isEmpty then return out
      -- rename the first class variable of `q` to one of `p`
      let a ← pick vq 0
      let b ← pick vp 0
      return [p, renameVar a b q]
  | _ => return out

/-- One rule. `produced` are the shapes earlier heads build (a consumer
rule matches one of them), `heavy` the constant of the heavy class. -/
def genRule (nC arity nG : Nat) (present produced : List Shape) (heavy : Nat) :
    Gen (RRule × List String) := do
  let r ← nat 1 20
  -- a merge rule: a constant rewritten into the heavy class, or a match
  -- whose class variable is unioned with it
  if r ≤ 3 then
    let j ← nat 0 (nC - 1)
    let j := if j = heavy then (j + 1) % nC else j
    if (← chance 1 2) then
      let (a, b) := if (← chance 2 3) then (j, heavy) else (heavy, j)
      return ({ body := [.plain (constSym a) []], eqs := [], rewrite := true, subsume := false,
                acts := [.union (.var (rootOf 0)) (.plain (constSym b) [])] }, ["merge-const"])
    let sh ← pick present .plain
    let body ← genBody arity present sh 1
    let vs := childVars body
    if vs.isEmpty then
      return ({ body, eqs := [], rewrite := false, subsume := false,
                acts := [.union (.var (rootOf 0)) (.plain (constSym heavy) [])] }, ["merge-match"])
    let x ← pick vs 0
    return ({ body, eqs := [], rewrite := false, subsume := false,
              acts := [.union (.var x) (.plain (constSym heavy) [])] }, ["merge-match"])
  -- two rules feeding each other is generated by `genPair`
  let consumer := !produced.isEmpty ∧ (← chance 1 2)
  let root ← if consumer then pick produced .plain else pick present .plain
  let nPat ← if (← chance 1 4) then pure 2 else pure 1
  let body ← genBody arity (present ++ produced).eraseDups root nPat
  let vs := childVars body
  let mut tags : List String := if consumer then ["consumer"] else []
  -- equalities
  let mut eqs : List Eq := []
  if nG > 0 ∧ !vs.isEmpty ∧ (← chance 1 3) then
    let x ← pick vs 0
    let j ← nat 0 (nG - 1)
    let inline ← chance 1 3
    eqs := eqs ++ [⟨x, globVar j, inline⟩]
    tags := tags ++ [if inline then "global-inline" else "global-eq"]
  if vs.length ≥ 2 ∧ (← chance 1 10) then
    let xs ← distinct 2 vs 0
    match xs with
    | [a, b] => eqs := eqs ++ [⟨a, b, false⟩]; tags := tags ++ ["local-eq"]
    | _ => pure ()
  let env := Env.ofBody body nG nC arity []
  let rewrite := nPat = 1 ∧ eqs.all (·.inline) ∧ (← chance 1 2)
  if rewrite then
    let reb := if (← chance 1 6) then rebuildOf (body.headD (.var 0)) else none
    let rhs ← match reb with
      | some p => do tags := tags ++ ["rebuild"]; pure p
      | none => do
          let want ← if (← chance 3 4) then some <$> pick Shape.all .plain else pure none
          genRhs env 2 none want
    let subsume ← chance 1 8
    if subsume then tags := tags ++ ["subsume"]
    return ({ body, eqs, rewrite := true, subsume, acts := [.union (.var (rootOf 0)) rhs] }, tags)
  let nAct ← nat 1 2
  let env ← if (← chance 1 3) then pure (Env.ofBody body nG nC arity [rootOf 0]) else pure env
  let mut acts : List Act := []
  for _ in List.range nAct do
    let a ← nat 1 10
    if a ≤ 4 then
      let t ← genRhs env 2 none (some (← pick Shape.all .plain))
      -- the parser's insert action reads its top-level children without a
      -- multiplicity (`parser.rs:846-866`, `parse_rhs` per child)
      let t := match t with
        | .ac f elems rest => .ac f (elems.map fun e => (e.1, Mult.exact 1)) rest
        | t => t
      acts := acts ++ [.insert t]
    else
      let lhs ← if (← chance 1 2) ∧ !vs.isEmpty then (do pure (Pat.var (← pick vs 0)))
        else if (← chance 1 2) then pure (Pat.var (rootOf 0)) else genRhs env 1 none none
      let rhs ← genRhs env 2 none none
      acts := acts ++ [.union lhs rhs]
  return ({ body, eqs, rewrite := false, subsume := false, acts }, tags)

/-- Two rules feeding each other: the first matches shape `a` and builds
shape `b` over its variables, the second matches `b` and builds `a`; both
heads use only bound classes, so the pair stops after a bounded number of
rounds unless a head nests a new application. -/
def genPair (nC arity nG : Nat) (present : List Shape) : Gen (List RRule) := do
  let a ← pick present .plain
  let b ← pick Shape.all .plain
  let mk (x y : Shape) : Gen RRule := do
    let body ← genBody arity (present ++ [y]).eraseDups x 1
    let env := Env.ofBody body nG nC arity []
    let rhs ← genRhs env 1 none (some y)
    if (← chance 1 2) then
      return { body, eqs := [], rewrite := true, subsume := false, acts := [.union (.var (rootOf 0)) rhs] }
    else
      let rhs := match rhs with
        | .ac f elems rest => .ac f (elems.map fun e => (e.1, Mult.exact 1)) rest
        | t => t
      return { body, eqs := [], rewrite := false, subsume := false, acts := [.insert rhs] }
  return [← mk a b, ← mk b a]

def genK : Gen Nat := do
  let r ← nat 1 8
  return if r = 1 then 2 else if r ≤ 3 then 3 else if r ≤ 5 then 4 else 5

def genCase (seed idx : Nat) : Gen RCase := do
  let nC ← nat 3 6
  let arity ← nat 1 2
  let nG ← nat 0 2
  let globals ← (List.range nG).mapM fun _ => nat 0 (nC - 1)
  let heavy ← nat 0 (nC - 1)
  -- the heavy class: one or two other constants merged into it
  let mut init : List String := []
  let nHeavy ← if nC ≥ 4 then nat 0 1 else pure 0
  for _ in List.range nHeavy do
    let j ← nat 0 (nC - 1)
    if j ≠ heavy ∧ !(globals.contains j) then
      init := init ++ [s!"(union {constNode heavy} {constNode j})"]
  let nN ← nat 2 6
  let mut present : List Shape := []
  for _ in List.range nN do
    let (sh, t) ← genInitNode nC arity (heavy :: globals)
    present := (present ++ [sh]).eraseDups
    -- a node in a constant's class (the heavy one with probability 1/4), or
    -- in a class of its own
    let r ← nat 1 8
    if r ≤ 2 then init := init ++ [s!"(union {constNode heavy} {t})"]
    else if r ≤ 4 then init := init ++ [s!"(union {constNode (← nat 0 (nC - 1))} {t})"]
    else init := init ++ [t]
  let nR ← nat 2 4
  let mut rules : List RRule := []
  let mut produced : List Shape := []
  let mut tags : List String := []
  for i in List.range nR do
    if i + 1 < nR ∧ rules.length + 2 ≤ nR ∧ (← chance 1 4) then
      let pair ← genPair nC arity nG present
      rules := rules ++ pair
      tags := tags ++ ["feeding-pair"]
      produced := (produced ++ (pair.flatMap fun r => r.acts.flatMap actShapes)).eraseDups
      continue
    if rules.length ≥ nR then continue
    let (rule, tg) ← genRule nC arity nG present produced heavy
    rules := rules ++ [rule]
    tags := tags ++ tg
    produced := (produced ++ (rule.acts.flatMap actShapes)).eraseDups
  let k ← genK
  -- the shape of the `EqGlobal` gap (spec-semi-naive-rounds §C.4): a global
  -- `g0` bound to a light constant `a`, a parent storing the heavy class,
  -- a rule equating the parent's child to `g0`, and a rewrite merging `a`
  -- into the heavy class, whose id survives (the parent is not
  -- recanonicalized, only `a`'s node is touched)
  if nC ≥ 4 ∧ (← chance 1 5) then
    let others := (List.range nC).filter (· ≠ heavy)
    let a ← pick others 0
    let j ← pick (others.filter (· ≠ a)) 0
    let globals2 := match globals with | [] => [a] | _ :: gs => a :: gs
    let parent := "(F " ++ " ".intercalate (List.replicate arity (constNode heavy)) ++ ")"
    let init2 := [s!"(union {constNode heavy} {constNode j})", parent] ++ init
    let args := (List.range arity).map Pat.var
    let inline ← chance 1 3
    let act ← if (← chance 1 2) then pure (Act.insert (.comm 1 (.var 0) (.var 0)))
      else pure (Act.union (.plain (constSym (← nat 0 (nC - 1))) []) (.plain (constSym (← nat 0 (nC - 1))) []))
    let gap : RRule := { body := [.plain 0 args], eqs := [⟨0, globVar 0, inline⟩], acts := [act],
                         rewrite := false, subsume := false }
    let merge : RRule := { body := [.plain (constSym a) []], eqs := [], rewrite := true, subsume := false,
                           acts := [.union (.var (rootOf 0)) (.plain (constSym heavy) [])] }
    return { seed, idx, nC, arity, globals := globals2, init := init2, rules := gap :: rules ++ [merge], k,
             tags := (tags ++ ["eq-global-gap"]).eraseDups }
  return { seed, idx, nC, arity, globals, init, rules, k, tags := tags.eraseDups }

def caseOf (seed idx : Nat) : RCase :=
  (genCase seed idx).run' (mkStdGen (seed * 1000003 + idx + 77777))

/-- The program up to the rules (declarations, globals, initial graph, rules). -/
def RCase.prefix (cs : RCase) : List String :=
  ["(sort E)"] ++
  ((List.range cs.nC).map fun i => s!"(function C{i} () E)") ++
  [s!"(function F ({" ".intercalate (List.replicate cs.arity "E")}) E)",
   "(function G (E E) E :comm)",
   "(function Cat (E) E :assoc)",
   "(function Add (E) E :assoc-comm)",
   "(function And (E) E :assoc-comm-idem)"] ++
  ((cs.globals.zipIdx).map fun (c, j) => s!"(let g{j} {constNode c})") ++
  cs.init ++ cs.rules.map RRule.pp

def pad4 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (4 - s.length) ++ s

def fileName (seed idx : Nat) : String := s!"r{seed}_{pad4 idx}.egg"

end Conform.Rounds
