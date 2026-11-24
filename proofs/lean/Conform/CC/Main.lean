import Conform.CC.Emit

/-!
# `semper-conform-cc`: AC-congruence conformance programs

    lake exe semper-conform-cc <seed> <count> <outdir> [--only <idx>]

writes `<outdir>/cc<seed>_<idx>.egg` for `idx` in `[0, count)` (or the one
case `idx`). Each program declares one AC or ACI operator with laws, asserts
inverse nodes and equations between monomials under eager completion, and
checks the bounded oracle's partition: `check-eq` for every identified pair
(sound for `E`), `check-neq` for pairs separated at the bound and at the
bound plus two. Case `idx` of seed `s` has its own generator state; the same
seed gives byte-identical files.
-/

open Conform.CC

def writeCase (outdir : String) (seed idx : Nat) : IO Unit := do
  let cs := caseOf seed idx
  IO.FS.writeFile s!"{outdir}/{fileName seed idx}" (program cs (checksOf cs))

def usage : IO UInt32 := do
  IO.eprintln "usage: semper-conform-cc <seed> <count> <outdir> [--only <idx>]"
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [seed, count, outdir] =>
    let (some seed, some count) := (seed.toNat?, count.toNat?) | usage
    IO.FS.createDirAll outdir
    for i in List.range count do writeCase outdir seed i
    return 0
  | [seed, _, outdir, "--only", i] =>
    let (some seed, some i) := (seed.toNat?, i.toNat?) | usage
    IO.FS.createDirAll outdir
    writeCase outdir seed i
    return 0
  | _ => usage
