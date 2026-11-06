import Conform.Flatten.Oracle

/-!
# `:flatten` conformance generator: the `.egg` program of a case

As `Conform.Emit`: model class `c` is the nullary constructor `(Cc)`, the AC
unit `(Zero)`, the ACI unit `(Top)`; the rule tags its matches with `Tag`,
a multiplicity `k` as `(R (End) (End):k)`, a multiset or set rest as
`(R (End) ..r)`, a sequence rest as `(RS (End) ..r)`. The folds are
`SubL` (`:assoc-left`) and `SubR` (`:assoc-right`).
-/

namespace ConformF

open Semper.EMatch Semper.EMatch.Flatten
open Conform (Arg Match tagVars isClsVar isMultVar isSeqRest ppCount ppMult pad4 childClasses)

def cname (cs : FCase) (c : C) : String :=
  if cs.lawsAC.unit = some c then "(Zero)"
  else if cs.aciUnit = some c then "(Top)"
  else s!"(C{c})"

def ppChildren (cs : FCase) : Children → String
  | .tuple l => " ".intercalate (l.map (cname cs))
  | .spair a b => s!"{cname cs a} {cname cs b}"
  | .seq l => " ".intercalate (l.map (cname cs))
  | .mset m => " ".intercalate ((Semper.EMatch.Multiset.entries m).map
      (fun e => ppCount (cname cs e.1) e.2))
  | .set s => " ".intercalate ((s.sort (· ≤ ·)).map (cname cs))

def ppNode (cs : FCase) (n : Node) : String :=
  s!"({(FShape.ofSym n.op).name} {ppChildren cs n.children})"

partial def ppPat : Pat → String
  | .var x => s!"x{x}"
  | .plain f args => s!"({(FShape.ofSym f).name} " ++ " ".intercalate (args.map ppPat) ++ ")"
  | .comm f p q => s!"({(FShape.ofSym f).name} {ppPat p} {ppPat q})"
  | .assoc f pre args suf =>
      let pre := match pre with | some r => [s!"..r{r}"] | none => []
      let suf := match suf with | some r => [s!"..r{r}"] | none => []
      s!"({(FShape.ofSym f).name} " ++ " ".intercalate (pre ++ args.map ppPat ++ suf) ++ ")"
  | .ac f elems rest =>
      let rest := match rest with | some r => [s!"..r{r}"] | none => []
      s!"({(FShape.ofSym f).name} " ++
        " ".intercalate (elems.map (fun e => ppPat e.1 ++ ppMult e.2) ++ rest) ++ ")"
  | .aci f elems rest =>
      let rest := match rest with | some r => [s!"..r{r}"] | none => []
      s!"({(FShape.ofSym f).name} " ++ " ".intercalate (elems.map ppPat ++ rest) ++ ")"

def ppTagVar (v : Var) : String :=
  if isClsVar v then s!"x{v}"
  else if isMultVar v then s!"(R (End) (End):k{v})"
  else if isSeqRest v then s!"(RS (End) ..r{v})"
  else s!"(R (End) ..r{v})"

def ppArg (cs : FCase) : Arg → String
  | .cls c => cname cs c
  | .mult m => s!"(R (End):{m + 1})"
  | .mset e => if e.isEmpty then "(End)" else
      "(R (End) " ++ " ".intercalate (e.map (fun p => ppCount (cname cs p.1) p.2)) ++ ")"
  | .fset l => if l.isEmpty then "(End)" else
      "(R (End) " ++ " ".intercalate (l.map (cname cs)) ++ ")"
  | .seq l => if l.isEmpty then "(End)" else
      "(RS (End) " ++ " ".intercalate (l.map (cname cs)) ++ ")"

def ppTag (cs : FCase) (m : Match) : String :=
  "(Tag " ++ " ".intercalate (m.args.map (ppArg cs)) ++ ")"

def ppLaws (cs : FCase) : String :=
  (match cs.lawsAC.unit with | some _ => " :identity (Zero)" | none => "") ++
  (match cs.lawsAC.nilpotent with | some r => s!" :nilpotent {r}" | none => "") ++
  (if cs.lawsAC.inv.isEmpty then "" else " :inverse Neg")

def fileName (seed idx : Nat) : String := s!"f{seed}_{pad4 idx}.egg"

/-- The features a case covers, for the header and the coverage counts. -/
def features (cs : FCase) : List String :=
  let G := cs.graph
  let ops := patOps cs.pat
  let has (s : FShape) := ops.contains s.sym
  let lawsN := ops.filter (fun f =>
    (f = FShape.mset.sym && cs.lawsAC.present) || (f = FShape.set.sym && cs.aciUnit.isSome))
  let cyclic := cs.nodes.any (fun p => (childClasses p.2.children).contains (G.find p.1))
  let multi := cs.nodes.any (fun p => cs.nodes.any (fun q =>
    p.1 < q.1 && p.2.op = q.2.op && G.find p.1 = G.find q.1))
  let (mx, _) := viewStats G cs.pat
  (if nestedNary cs.pat then ["nested"] else []) ++
  (if has .mset && has .set && lawsN.length ≥ 2 then ["laws2"] else []) ++
  (if cyclic then ["cyclic"] else []) ++
  (if multi then ["multi"] else []) ++
  (if (has .seq || has .foldL || has .foldR) && seqRest cs.pat then ["seqrest"] else []) ++
  (if has .foldL || has .foldR then ["fold"] else []) ++
  (if mx ≥ 100 then ["nearcap"] else [])

/-- The program of a case, with its expected and rejected matches. -/
def program (cs : FCase) (ms : List Match) (rej : List Match) : String :=
  let vars := tagVars cs.pat
  let decls :=
    (cs.classes.map fun c =>
      if cs.lawsAC.unit = some c then "(function Zero () E)"
      else if cs.aciUnit = some c then "(function Top () E)"
      else s!"(function C{c} () E)") ++
    ["(function End () E)"] ++
    (if cs.lawsAC.inv.isEmpty then [] else ["(function Neg (E) E)"]) ++
    [s!"(function F ({" ".intercalate (List.replicate cs.arity "E")}) E)",
     "(function G (E E) E :comm)",
     "(function Cat (E) E :assoc)",
     s!"(function Add (E) E :assoc-comm{ppLaws cs})",
     s!"(function And (E) E :assoc-comm-idem{match cs.aciUnit with | some _ => " :identity (Top)" | none => ""})",
     "(function SubL (E) E :assoc-left)",
     "(function SubR (E) E :assoc-right)",
     "(function R (E) E :assoc-comm)",
     "(function RS (E) E :assoc)",
     s!"(function Tag ({" ".intercalate (List.replicate vars.length "E")}) E)"]
  let invs := cs.lawsAC.inv.map fun p => s!"(union (Neg {cname cs p.1}) {cname cs p.2})"
  let nodes := cs.nodes.map fun p =>
    s!"(union {cname cs (cs.graph.find p.1)} {ppNode cs p.2})"
  let rule := s!"(rewrite {ppPat cs.pat} (Tag {" ".intercalate (vars.map ppTagVar)})" ++
    (if cs.flatten then " :flatten)" else ")")
  let checks := (ms.map fun m => s!"(check-eq {cname cs m.root} {ppTag cs m})").eraseDups
  let neqs := rej.map fun m => s!"(check-neq {cname cs m.root} {ppTag cs m})"
  let (mx, work) := viewStats cs.graph cs.pat
  let header := [
    ";; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.",
    ";; SPDX-License-Identifier: Apache-2.0",
    ";; EXPECT: ok",
    ";; TYPES: machine",
    s!";; semper-conform-flatten seed={cs.seed} case={cs.idx} family={cs.family.name} root={cs.root.name} flatten={cs.flatten} classes={cs.nC} views={mx} work={work}",
    s!";; features: {",".intercalate (features cs)}",
    ";; Generated by the :flatten conformance generator of the Lean e-matching model",
    ";; (proofs/lean/Conform/Flatten); the expected matches are the flattened plan's",
    ";; (SemperProofs/EMatch/Flatten/PlanDefs.lean). Regenerate with",
    s!";;   lake exe semper-conform-flatten {cs.seed} <count> <dir>   (file {fileName cs.seed cs.idx})",
    s!";; expected matches: {ms.length}, rejected candidates: {rej.length}"]
  "\n".intercalate (header ++ ["(sort E)"] ++ decls ++ invs ++ nodes ++ [rule, "(run 1)"] ++
    checks ++ neqs) ++ "\n"

end ConformF
