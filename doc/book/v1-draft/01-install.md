# Install and run

This chapter builds the engine from source, runs one program and says where each
part of its output goes, gives the exit status for every outcome, and names the
crates in the workspace.

## Build from source

From a fresh checkout:

```bash
git clone https://github.com/yaspar-org/semi-persistent
cd semi-persistent
cargo build --release
```

The toolchain is pinned in `rust-toolchain.toml` (currently 1.97.1), so
`rustup` selects the right compiler on its own. The Verus proof annotations in
`containers-verus`, `abstract-domains` and `au-verus` erase under plain
`rustc`, so a normal `cargo build` needs no verifier.

This produces the front end at `target/release/semi-persistent`. A debug build
works too and is fast enough for everything in this book except the 100-problem
corpus.

The workspace publishes to crates.io on `v*` tags
(`.github/workflows/publish.yml`); the CLI binary lives in the
`semi-persistent-egraph` package, and `semi-persistent` is a facade crate that
re-exports the library surface.

## Run a program

A program is a text file of S-expression commands, conventionally `.egg`. Pass
one path:

```bash
target/release/semi-persistent egraph/examples/basic.egg
```

```text
ok — 14 nodes
```

That last line goes to standard error. `ok` means every `(check ...)` in the
program passed and nothing failed to parse or sort-check; the count is the
number of e-nodes in the e-graph when the program finished. Query output
(`extract`, `antiunify`, `print-size`) goes to standard output, so the two are
separable:

```bash
target/release/semi-persistent prog.egg > results.txt
```

## Exit status

| outcome | stderr | exit |
| --- | --- | --- |
| every check passed | `ok — N nodes` | 0 |
| a `(check ...)` failed | `error: check failed: terms are not equal` | 1 |
| the program did not parse | `parse error: ...` | 1 |
| a declaration or term did not sort-check | `sort error: ...` | 1 |

A program that only asks questions and asserts nothing will report `ok` no
matter what it printed. The `checkau` command exists so that anti-unification
results can be asserted rather than eyeballed; see
[chapter 5](05-anti-unification.md).

## The rest of the workspace

You do not need any of these to use the engine; the list explains the names you
will see:

| Crate | What it is |
| --- | --- |
| `semi-persistent-egraph` | the engine and the `semi-persistent` binary |
| `semi-persistent-containers-verus` | the container layer the engine is built on, with Verus proofs of the snapshot protocol |
| `semi-persistent-containers` | an independent plain-Rust implementation of the same containers, kept as a differential oracle |
| `semi-persistent-traversals` | arena-based recursion schemes |
| `semi-persistent-abstract-domains` | verified bitvector and interval domains |
| `au-verus` | machine-checked lemmas about the anti-unification objective |
| `semi-persistent` | published facade re-exporting the above |
