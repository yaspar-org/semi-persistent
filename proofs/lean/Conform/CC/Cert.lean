import Conform.CC.Emit

/-!
# AC-congruence conformance: countermodel certificates

A `check-neq A B` of the certifying generator is backed by a concrete
commutative monoid and a valuation of the summand classes under which every
asserted equation holds, the declared laws hold, and `A`, `B` take different
values (`SemperProofs/CC/Countermodel.lean`, `not_E_of_separates`). The models:

* `zn m` (dimension `d`): `(ℤ/m)^d` under addition, unit `0`, inverse
  negation. An abelian group, so cancellative; nilpotent of order `k` when
  `m ∣ k`. Used for every non-idempotent operator.
* `natv` (dimension `d`): `ℕ^d` under addition (free commutative monoid on `d`
  generators, cancellative). Operators without inverse or nilpotent law.
* `trunc t` (dimension `d`): `{0..t}^d` under saturating addition, a
  commutative monoid (a truncated free one). Non-cancellative operators
  without inverse or nilpotent law.
* `maxn` and `bits`: `({0..t}, max)` and finite sets under union, the
  idempotent operators.

The laws hold for every element by the choice of model (`modelsFor`);
the valuation only has to send the unit to `0`, each inverse pair to a pair
summing to `0`, and satisfy the asserted equations, which the search checks.
The search is a depth-first assignment of the classes in order, pruning on
each equation (and inverse pair) as soon as its classes are assigned.
-/

namespace Conform.CC

inductive MKind where
  | zn (m : Nat)
  | natv
  | trunc (t : Nat)
  | maxn
  | bits
  deriving Repr, BEq, Inhabited

structure Model where
  kind : MKind
  dim : Nat
  /-- Candidate values of one coordinate. -/
  coord : List Nat
  deriving Inhabited

def MKind.comb : MKind → Nat → Nat → Nat
  | .zn m, a, b => (a + b) % m
  | .natv, a, b => a + b
  | .trunc t, a, b => min t (a + b)
  | .maxn, a, b => max a b
  | .bits, a, b => a ||| b

def Model.name (M : Model) : String :=
  match M.kind with
  | .zn m => s!"Z{m}^{M.dim}"
  | .natv => s!"N^{M.dim}"
  | .trunc t => s!"T{t}^{M.dim}"
  | .maxn => s!"max{M.coord.length - 1}^{M.dim}"
  | .bits => s!"sets{M.dim}"

/-- Every vector of dimension `d` over `coord`. -/
def vectors (coord : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | d + 1 => coord.flatMap fun c => (vectors coord d).map (c :: ·)

def Model.values (M : Model) : List (List Nat) := vectors M.coord M.dim

def Model.zero (M : Model) : List Nat := List.replicate M.dim 0

def Model.add (M : Model) (a b : List Nat) : List Nat := (a.zip b).map fun (x, y) => M.kind.comb x y

/-- The value of a monomial; the unit atom `nC` and unassigned atoms are `0`. -/
def Model.eval (M : Model) (asg : Array (List Nat)) (m : List Nat) : List Nat :=
  m.foldl (fun acc a => M.add acc (asg.getD a M.zero)) M.zero

/-- The models whose laws are those of the case's operator. -/
def modelsFor (th : Theory) : List Model :=
  if th.idem then
    [⟨.maxn, 1, [0, 1, 2, 3]⟩, ⟨.bits, 1, [0, 1, 2, 3, 4, 5, 6, 7]⟩, ⟨.maxn, 2, [0, 1, 2]⟩]
  else
    let ms : List Nat := match th.nil with
      | some k => (List.range 13).filter fun m => m ≥ 2 && k % m == 0
      | none => [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    let zns : List Model := ms.map fun m => ⟨.zn m, 1, List.range m⟩
    let zn2 : List Model := (ms.filter (· ≤ 3)).map fun m => ⟨.zn m, 2, List.range m⟩
    let free : List Model :=
      if th.nil.isNone && th.inv.isEmpty then
        [⟨.natv, 1, [0, 1, 2, 3]⟩, ⟨.natv, 2, [0, 1, 2]⟩] ++
        (if th.cancel then [] else [⟨.trunc 2, 2, [0, 1, 2]⟩, ⟨.trunc 1, 3, [0, 1]⟩])
      else []
    free ++ zns ++ zn2

/-- A certificate: the model and a valuation of the classes `0..nC-1`. -/
structure Cert where
  model : Model
  asg : Array (List Nat)
  deriving Inhabited

structure SearchSt where
  budget : Nat
  certs : Array (Option Cert)
  open_ : Nat
  found : Array Cert := #[]

/-- The constraints of a theory as pairs of monomials: asserted equations
and inverse pairs (`{x, y} = ∅`). Each is checked at the depth of its
largest non-unit class. -/
def constraints (th : Theory) (nC : Nat) : Array (List (List Nat × List Nat)) := Id.run do
  let cs := th.eqs ++ th.inv.map fun p => ([p.1, p.2], [])
  let mut out : Array (List (List Nat × List Nat)) := Array.replicate (nC + 1) []
  for c in cs do
    let atoms := (c.1 ++ c.2).filter (· < nC)
    let d := atoms.foldl max 0
    out := out.modify d (c :: ·)
  return out

partial def dfs (M : Model) (vals : List (List Nat)) (cons : Array (List (List Nat × List Nat)))
    (nC : Nat) (pairs : Array (List Nat × List Nat)) (i : Nat) (asg : Array (List Nat)) :
    StateM SearchSt Unit := do
  let st ← get
  if st.budget = 0 || st.open_ = 0 then return
  if i = nC then
    -- a full valuation satisfying every constraint
    let mut certs := st.certs
    let mut open_ := st.open_
    let mut used := false
    for j in [0:pairs.size] do
      if certs[j]!.isNone then
        let (p, q) := pairs[j]!
        if M.eval asg p != M.eval asg q then
          certs := certs.set! j (some ⟨M, asg⟩)
          open_ := open_ - 1
          used := true
    let found := if used && st.found.size < 6 then st.found.push ⟨M, asg⟩ else st.found
    set { st with certs, open_, found, budget := st.budget - 1 }
    return
  for v in vals do
    let st ← get
    if st.budget = 0 || st.open_ = 0 then return
    set { st with budget := st.budget - 1 }
    let asg' := asg.set! i v
    let ok := (cons.getD i []).all fun (l, r) => M.eval asg' l == M.eval asg' r
    if ok then dfs M vals cons nC pairs (i + 1) asg'

/-- Search every model of the theory for valuations separating the pairs. -/
def certify (th : Theory) (nC : Nat) (pairs : Array (List Nat × List Nat)) (budget : Nat) :
    Array (Option Cert) × Array Cert := Id.run do
  let cons := constraints th nC
  -- constraints over the unit alone (e.g. `Neg u = u`) are checked at depth 0
  let mut st : SearchSt := { budget := 0, certs := Array.replicate pairs.size none,
                             open_ := pairs.size }
  for M in modelsFor th do
    if st.open_ = 0 then break
    let start : Array (List Nat) := Array.replicate (nC + 1) M.zero
    let vals := M.values
    let (_, st') := (dfs M vals cons nC pairs 0 start).run { st with budget := budget }
    st := st'
  return (st.certs, st.found)

/-! ## Wider cases -/

/-- A wide case: 3..6 classes, 2..6 random equations of sizes 1..4, random
laws among the combinations the engine accepts. -/
def genWide (seed idx : Nat) : Gen CCase := do
  let nC ← nat 3 6
  let idem ← chance 1 6
  let unit ← chance 1 2
  let mut nil : Option Nat := none
  let mut cancel := false
  let mut acts : List Act := []
  if !idem then
    if unit && (← chance 1 4) then nil := some (← pick [2, 2, 3, 4, 6] 2)
    cancel ← chance 1 4
    if unit && (← chance 2 5) then
      for _ in List.range (← nat 1 2) do
        acts := acts ++ [.neg (← nat 0 (nC - 1)) (← nat 0 nC)]
  for _ in List.range (← nat 2 6) do
    let l ← atoms nC (← nat 1 4)
    let r ← atoms nC (← nat 1 3)
    let l := if unit && (← chance 1 8) then l ++ [nC] else l
    if l.mergeSort != r.mergeSort then acts := acts ++ [.eq l r]
  if (← chance 1 3) then
    let l ← acts.mapM fun x => do return (← nat 0 1000, x)
    acts := (l.mergeSort (fun p q => p.1 ≤ q.1)).map (·.2)
  let na := nC + if unit then 1 else 0
  let bs := [3, 4, 5].filter fun B => univSize na B ≤ 1200
  let B ← pick bs 3
  return { seed, idx, family := "wide", nC, unit, idem, nil, cancel, B, acts }

/-- Case `idx` of the certifying generator: even cases are the families of
`caseOf`, odd ones are wide. -/
def certCaseOf (seed idx : Nat) : CCase :=
  if idx % 2 = 0 then caseOf seed idx
  else
    let h := ((seed * 1000003 + idx) * 2654435761 + 977) % 4294967291
    (genWide seed idx).run' (mkStdGen h)

/-! ## Checks -/

structure CertChecks where
  eqs : List (List Nat × List Nat)
  neqs : List ((List Nat × List Nat) × Cert)
  found : Array Cert
  cand : Nat
  uncert : Nat

def showVal (v : List Nat) : String :=
  match v with
  | [x] => toString x
  | v => "(" ++ ",".intercalate (v.map toString) ++ ")"

def Cert.show (c : Cert) (nC : Nat) : String :=
  c.model.name ++ " " ++ " ".intercalate ((List.range nC).map fun i =>
    s!"C{i}={showVal (c.asg.getD i [])}")

def certChecks (cs : CCase) (maxNeq : Nat) : CertChecks := Id.run do
  let th := cs.theory
  let r := solve th cs.B
  let U := r.univ
  let mut first : Std.HashMap Nat (List Nat) := {}
  let mut eqs : Array (List Nat × List Nat) := #[]
  let mut mins : Array (List Nat) := #[]
  for i in [0:U.mons.size] do
    let m := U.mons[i]!
    if cs.emittable m then
      let k := SemperProofs.CC.Bounded.find r.rep i
      match first[k]? with
      | some m0 => eqs := eqs.push (m0, m)
      | none => first := first.insert k m; mins := mins.push m
  -- candidates: class minima of size <= 2 pairwise, equation sides against them,
  -- minima of size 3 against their neighbours
  let ms := mins.toList
  let small := ms.filter (·.length ≤ 2)
  let mut cand : Array (List Nat × List Nat) := #[]
  for e in th.eqs do
    for q in small do
      if cs.emittable e.1 && !r.same e.1 q then cand := cand.push (e.1, q)
      if cs.emittable e.2 && !r.same e.2 q then cand := cand.push (e.2, q)
  for k in [0:small.length] do
    for l in [k + 1:small.length] do
      cand := cand.push (small.getD k [], small.getD l [])
  let big := ms.filter (·.length == 3)
  for k in [0:big.length] do
    cand := cand.push (big.getD k [], big.getD (k + 1) (small.getD 0 []))
  let cand1 := cand.toList.filter (fun (p, q) => p != q && cs.emittable p && cs.emittable q)
  let cand2 := (cand1.foldl (fun (acc : Array (List Nat × List Nat)) pq =>
    if acc.contains pq || acc.contains (pq.2, pq.1) then acc else acc.push pq) #[]).extract 0 400
  let (certs, found) := certify th cs.nC cand2 400000
  let mut neqs : Array ((List Nat × List Nat) × Cert) := #[]
  let mut unc := 0
  for j in [0:cand2.size] do
    match certs[j]! with
    | some c => if neqs.size < maxNeq then neqs := neqs.push (cand2[j]!, c)
    | none => unc := unc + 1
  return { eqs := eqs.toList, neqs := neqs.toList, found, cand := cand2.size, uncert := unc }

def certFileName (seed idx : Nat) : String := s!"cs{seed}_{pad4 idx}.egg"

/-- The program text. `dump` keeps the `dump-egraph` line the soundness runner
reads (it writes `DUMPFILE` relative to the working directory); a committed
fixture omits it, so running the test suite writes no file into the tree. -/
def certProgram (cs : CCase) (ck : CertChecks) (dump : Bool := true) : String :=
  let header := [
    ";; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.",
    ";; SPDX-License-Identifier: Apache-2.0",
    ";; EXPECT: ok",
    ";; TYPES: machine",
    s!";; semper-conform-cc-cert seed={cs.seed} case={cs.idx} family={cs.family} bound={cs.B} classes={cs.nC}",
    ";; Every check-neq pair is separated by a countermodel of the declared laws and the",
    ";; asserted equations (SemperProofs/CC/Countermodel.lean: not_E_of_separates); its",
    ";; certificate precedes it. check-eq pairs are =_E (bounded oracle).",
    s!";; candidates: {ck.cand}, certified check-neq: {ck.neqs.length}, uncertified: {ck.uncert}, check-eq: {ck.eqs.length}"] ++
    ck.found.toList.map (fun c => s!";; MODEL {c.show cs.nC}")
  "\n".intercalate (header ++ cs.decls ++ ["(set-option :completion eager)"] ++
    cs.acts.map cs.act ++
    (if dump then ["(dump-egraph (C0) :file \"DUMPFILE\")"] else []) ++
    ck.neqs.flatMap (fun ((p, q), c) =>
      [s!";; CERT {c.show cs.nC}", s!"(check-neq {cs.mono p} {cs.mono q})"]) ++
    ck.eqs.map (fun (p, q) => s!"(check-eq {cs.mono p} {cs.mono q})")) ++ "\n"

end Conform.CC
