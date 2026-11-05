import Conform.CC.Cert

/-!
# `semper-conform-cc-cert`: certified AC-congruence disequality programs

    lake exe semper-conform-cc-cert <seed> <count> <outdir> [--only <idx>]

writes `<outdir>/cs<seed>_<idx>.egg`. Each program asserts equations under
eager completion, dumps the e-graph, and checks `check-neq` only on pairs a
countermodel separates (certificate in the preceding comment), then the
bounded oracle's `check-eq` pairs.
-/

open Conform.CC

def writeCert (outdir : String) (seed idx : Nat) : IO Unit := do
  let cs := certCaseOf seed idx
  IO.FS.writeFile s!"{outdir}/{certFileName seed idx}" (certProgram cs (certChecks cs 40))

def main (args : List String) : IO UInt32 := do
  match args with
  | [seed, count, outdir] =>
    let (some seed, some count) := (seed.toNat?, count.toNat?) | return 1
    IO.FS.createDirAll outdir
    for i in List.range count do writeCert outdir seed i
    return 0
  | [seed, _, outdir, "--only", i] =>
    let (some seed, some i) := (seed.toNat?, i.toNat?) | return 1
    IO.FS.createDirAll outdir
    writeCert outdir seed i
    return 0
  | _ =>
    IO.eprintln "usage: semper-conform-cc-cert <seed> <count> <outdir> [--only <idx>]"
    return 1
