# Install and build

## Build from source

```bash
git clone https://github.com/yaspar-org/semi-persistent.git
cd semi-persistent
cargo build --release
```

The workspace requires Rust 1.97.1, pinned in `rust-toolchain.toml`. `rustup`
selects this compiler when Cargo runs in the checkout. A normal build does not
require Verus; the proof annotations compile away under `rustc`.

Cargo writes the command-line program to `target/release/semi-persistent`. Run
its help command to confirm the build:

```bash
./target/release/semi-persistent --help
```

```text
Equality saturation engine

Usage: semi-persistent [OPTIONS] <FILE>
```

### Re-running the Verus proofs

Verus is required only to re-check the proofs in `abstract-domains`,
`containers-verus`, and `au-verus`. All three crates pin the same Verus release
in their `.verus-version` files.

The following installs the pinned release on x86-64 Linux or Apple Silicon
macOS. The release archive includes Verus, `cargo-verus`, and Z3.

```bash
version=$(cat containers-verus/.verus-version)

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) asset=x86-linux ;;
  Darwin-arm64) asset=arm64-macos ;;
  *) echo "Download the matching asset from the Verus release page"; exit 1 ;;
esac

tmp=$(mktemp -d)
curl -fL \
  "https://github.com/verus-lang/verus/releases/download/release%2F${version}/verus-${version}-${asset}.zip" \
  -o "$tmp/verus.zip"
unzip -q "$tmp/verus.zip" -d "$tmp"

verus_home="$HOME/.local/verus-$version"
mkdir -p "$HOME/.local"
mv "$tmp"/verus-* "$verus_home"
export PATH="$verus_home:$PATH"
```

On macOS, allow the downloaded binaries through Gatekeeper:

```bash
bash "$verus_home/macos_allow_gatekeeper.sh"
```

Add the `PATH` export to your shell startup file to retain it in later shells.
Confirm the installation with `verus --version`, then run the proof suites:

```bash
(cd abstract-domains && cargo verus verify)
(cd containers-verus && cargo verus verify)
(cd containers-verus && cargo verus verify --features literal-types)
(cd au-verus && cargo verus verify)
```

## The crates in the workspace

Running Semper does not require working with these crates individually. Cargo
prints their package names during builds, and the corresponding Rust crate
names appear in stack traces. This table maps those names to their source paths.

| Package | Path | Purpose |
| --- | --- | --- |
| `semi-persistent` | `semi-persistent/` | Published facade that re-exports the containers, e-graph, and traversal libraries. |
| `semi-persistent-egraph` | `egraph/` | The Semper engine library and the `semi-persistent` command-line binary. |
| `semi-persistent-containers-verus` | `containers-verus/` | Verus-verified production container layer used by the e-graph. |
| `semi-persistent-containers` | `containers/` | Independent plain-Rust container implementation retained as a reference and performance baseline. |
| `containers-conformance` | `containers-conformance/` | Differential, property, layout, and benchmark harness comparing the two container implementations. |
| `containers-verus-canary` | `containers-verus/canary/` | Compile and smoke tests for the e-graph-shaped uses of the verified container API. |
| `semi-persistent-traversals` | `traversals/` | Typed arenas and stack-safe folds, unfolds, transforms, and zippers. |
| `semi-persistent-traversals-derive` | `traversals/derive/` | Procedural macros that generate traversal arenas and supporting types. |
| `traversals-compile-tests` | `traversals/compile-tests/` | Downstream compile tests for the generated traversal API. |
| `semi-persistent-abstract-domains` | `abstract-domains/` | Verus-verified bitvector abstract domains and their executable mirrors. |
| `semi-persistent-au-verus` | `au-verus/` | Machine-checked lemmas for the positional anti-unification model. |

## Run the test suite

From the workspace root, run:

```bash
cargo test --workspace
```

At the time of writing, Cargo discovers 1,782 tests. The default run executes
1,731 and reports 51 as ignored. On the machine used to prepare this chapter,
the command completed in 6 minutes 2 seconds.

The interpreter's file-based integration fixtures live under
`egraph/tests/egg/`. The harness in `egraph/tests/egg_tests.rs` sends each
registered `.egg` program through the parser, sort checker, and interpreter.
Unless overridden by a fixture directive, it runs the program with both naive
and semi-naive evaluation.

The same harness defines `book_examples`. It scans `doc/book/examples/` for
every file with the `.egg` extension and sends each one through the same
checker. Chapters include those files directly, so every book example is a
test. Adding an example to that directory does not require separate Rust test
registration.

The ignored count includes manual diagnostics and measurements rather than one
unfinished suite. Six entries are child-process cases for hasher configuration;
their non-ignored driver tests already execute them in fresh processes. The
slow ignored groups are:

- the `completion_*` diagnostics and the `ac_vs_rules` comparison;
- the `bench_acgen_*` fixtures in `egg_tests`;
- the AU measurement and stress tests in the `au_*` test binaries; and
- the feature-gated, 100-million-element `compat_vec_stress` tests.

List ignored tests without running them:

```bash
cargo test --workspace -- --ignored --list
```

Run slow tests by naming their harness rather than running every ignored test
together. For example:

```bash
cargo test -p semi-persistent-egraph --release --test egg_tests \
  bench_acgen -- --ignored --nocapture

cargo test -p semi-persistent-egraph --release --test ac_vs_rules \
  -- --ignored --nocapture

cargo test -p semi-persistent-egraph --release --test au_hardness \
  hardness_map -- --ignored --nocapture

cargo test -p semi-persistent-containers-verus --features compat-all \
  --test compat_vec_stress -- --ignored --test-threads 1 --nocapture
```

The repository's reproduction guide gives the commands and expected durations
for the individual AU measurements.
