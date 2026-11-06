import Conform.Flatten.Emit

/-!
# `semper-conform-flatten`: `:flatten` conformance programs for the Semper engine

    lake exe semper-conform-flatten <seed> <count> <outdir>

writes `<outdir>/f<seed>_<idx>.egg` for `idx` in `[0, count)`; `--only <idx>`
writes one case, `--dump <idx>` prints the program without the oracle. The
same seed gives byte-identical files.
-/

open ConformF

def writeCase (outdir : String) (seed idx : Nat) : IO Unit := do
  let cs := caseOf seed idx
  let ms := expected cs
  let rej := rejected cs ms 4
  IO.FS.writeFile s!"{outdir}/{fileName seed idx}" (program cs ms rej)

def usage : String := "usage: semper-conform-flatten <seed> <count> <outdir> [--only <idx> | --dump <idx>]"

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
          IO.println (program (caseOf seed i) [] [])
      | [] =>
          for i in List.range count do
            writeCase outdir seed i
      | _ => IO.eprintln usage; return 1
      return 0
  | _ => IO.eprintln usage; return 1
