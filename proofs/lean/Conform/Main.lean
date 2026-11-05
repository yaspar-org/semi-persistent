import Conform.Emit

/-!
# `semper-conform`: conformance programs for the Semper engine

    lake exe semper-conform <seed> <count> <outdir>

writes `<outdir>/c<seed>_<idx>.egg` for `idx` in `[0, count)`. Each program
builds a small e-graph, runs one rule tagging its matches, and checks the
match set the Lean reference interpreter computes (`check-eq`) and a sample
of the candidates it rejects (`check-neq`). The same seed gives
byte-identical files.

    lake exe semper-conform <seed> <count> <outdir> --only <idx>

writes that one case.
-/

open Conform

def writeCase (outdir : String) (seed idx : Nat) : IO Unit := do
  let cs := caseOf seed idx
  let ms := expected cs
  let rej := rejected cs ms 4
  let note := if regroupOverBudget cs then
    ";; regrouping past the model's budget (Conform.regroupCap): the expected matches omit the regrouped views\n"
    else ""
  IO.FS.writeFile s!"{outdir}/{fileName seed idx}" (program cs ms rej ++ note)

def main (args : List String) : IO UInt32 := do
  match args with
  | seed :: count :: outdir :: rest =>
      let some seed := seed.toNat? | do IO.eprintln "seed: a natural number"; return 1
      let some count := count.toNat? | do IO.eprintln "count: a natural number"; return 1
      IO.FS.createDirAll outdir
      match rest with
      | ["--only", i] =>
          let some i := i.toNat? | do IO.eprintln "--only: a natural number"; return 1
          writeCase outdir seed i
      | ["--dump", i] =>
          let some i := i.toNat? | do IO.eprintln "--dump: a natural number"; return 1
          let cs := caseOf seed i
          IO.println (program cs [] [])
      | [] =>
          for i in List.range count do
            writeCase outdir seed i
      | _ => IO.eprintln "usage: semper-conform <seed> <count> <outdir> [--only <idx>]"; return 1
      return 0
  | _ =>
      IO.eprintln "usage: semper-conform <seed> <count> <outdir> [--only <idx>]"
      return 1
