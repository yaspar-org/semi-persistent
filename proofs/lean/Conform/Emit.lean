import Conform.Oracle

/-!
# Conformance generator: the `.egg` program of a case

Model class `c` is the nullary constructor `(Cc)`, the AC unit is `(Zero)`,
the ACI unit `(Top)`; a node is `(union <class> <node>)`. The rule is a
`rewrite` whose right-hand side is the tagging constructor `Tag` applied to
the bound variables: a class as itself, a multiplicity `k` as
`(R (End) (End):k)`, a multiset or set rest as `(R (End) ..r)`, a sequence
rest as `(RS (End) ..r)`. `R` is a laws-free AC operator and `RS` a
sequence operator; the sentinel `(End)` keeps a rest application non-empty
(a sequence has no unit) and one of one child is that child.
-/

namespace Conform

open Semper.EMatch Semper.EMatch.Flatten

def cname (cs : Case) (c : C) : String :=
  if cs.lawsAC.unit = some c then "(Zero)"
  else if cs.aciUnit = some c then "(Top)"
  else s!"(C{c})"

def ppCount (s : String) (n : Nat) : String :=
  if n = 1 then s else s!"{s}:{n}"

def ppChildren (cs : Case) : Children → String
  | .tuple l => " ".intercalate (l.map (cname cs))
  | .spair a b => s!"{cname cs a} {cname cs b}"
  | .seq l => " ".intercalate (l.map (cname cs))
  | .mset m => " ".intercalate ((Semper.EMatch.Multiset.entries m).map
      (fun e => ppCount (cname cs e.1) e.2))
  | .set s => " ".intercalate ((s.sort (· ≤ ·)).map (cname cs))

def ppNode (cs : Case) (n : Node) : String :=
  s!"({(Shape.ofSym n.op).name} {ppChildren cs n.children})"

def ppMult : Mult → String
  | .exact 1 => ""
  | .exact m => s!":{m}"
  | .var k lo _ => s!":k{k}" ++ (if lo ≥ 2 then s!">={lo}" else "")

partial def ppPat : Pat → String
  | .var x => s!"x{x}"
  | .plain _ args => "(F " ++ " ".intercalate (args.map ppPat) ++ ")"
  | .comm _ p q => s!"(G {ppPat p} {ppPat q})"
  | .assoc _ pre args suf =>
      let pre := match pre with | some r => [s!"..r{r}"] | none => []
      let suf := match suf with | some r => [s!"..r{r}"] | none => []
      "(Cat " ++ " ".intercalate (pre ++ args.map ppPat ++ suf) ++ ")"
  | .ac _ elems rest =>
      let rest := match rest with | some r => [s!"..r{r}"] | none => []
      "(Add " ++ " ".intercalate (elems.map (fun e => ppPat e.1 ++ ppMult e.2) ++ rest) ++ ")"
  | .aci _ elems rest =>
      let rest := match rest with | some r => [s!"..r{r}"] | none => []
      "(And " ++ " ".intercalate (elems.map ppPat ++ rest) ++ ")"

/-- The right-hand side argument of a tag variable. -/
def ppTagVar (v : Var) : String :=
  if isClsVar v then s!"x{v}"
  else if isMultVar v then s!"(R (End) (End):k{v})"
  else if isSeqRest v then s!"(RS (End) ..r{v})"
  else s!"(R (End) ..r{v})"

/-- The ground term of a tag argument. -/
def ppArg (cs : Case) : Arg → String
  | .cls c => cname cs c
  | .mult m => s!"(R (End):{m + 1})"
  | .mset e => if e.isEmpty then "(End)" else
      "(R (End) " ++ " ".intercalate (e.map (fun p => ppCount (cname cs p.1) p.2)) ++ ")"
  | .fset l => if l.isEmpty then "(End)" else
      "(R (End) " ++ " ".intercalate (l.map (cname cs)) ++ ")"
  | .seq l => if l.isEmpty then "(End)" else
      "(RS (End) " ++ " ".intercalate (l.map (cname cs)) ++ ")"

def ppTag (cs : Case) (m : Match) : String :=
  "(Tag " ++ " ".intercalate (m.args.map (ppArg cs)) ++ ")"

def ppLaws (cs : Case) : String :=
  (match cs.lawsAC.unit with | some _ => " :identity (Zero)" | none => "") ++
  (match cs.lawsAC.nilpotent with | some r => s!" :nilpotent {r}" | none => "") ++
  (if cs.lawsAC.inv.isEmpty then "" else " :inverse Neg")

def pad4 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (4 - s.length) ++ s

def fileName (seed idx : Nat) : String := s!"c{seed}_{pad4 idx}.egg"

/-- The program of a case, with its expected and rejected matches. -/
def program (cs : Case) (ms : List Match) (rej : List Match) : String :=
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
  let header := [
    ";; EXPECT: ok",
    ";; TYPES: machine",
    s!";; semper-conform seed={cs.seed} case={cs.idx} root={cs.root.name} flatten={cs.flatten} classes={cs.nC}",
    ";; Generated by the conformance generator of the Lean e-matching model (proofs/lean/Conform);",
    ";; the expected matches are the reference interpreter's. Regenerate with",
    s!";;   lake exe semper-conform {cs.seed} <count> <dir>   (file {fileName cs.seed cs.idx})",
    s!";; expected matches: {ms.length}, rejected candidates: {rej.length}"]
  "\n".intercalate (header ++ ["(sort E)"] ++ decls ++ invs ++ nodes ++ [rule, "(run 1)"] ++
    checks ++ neqs) ++ "\n"

end Conform
