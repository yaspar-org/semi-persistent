# Install and build

> Chapter contents: the toolchain requirement, the build command, where the binary
> lands, what the workspace crates are, and how to run the test suite.
>
> Carry over: `v1-draft/01-install.md` is accurate. Keep its build steps, its crate
> list and its wording, drop the section openers it still carries in two places.
>
> Verify before writing: the rust-toolchain file or `Cargo.toml` for the minimum
> toolchain, and the crate names and paths in the workspace `Cargo.toml`.

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

> Table of crate name, path, and one line of purpose. State that none of them is
> needed to use the engine and that the list exists to explain the names the reader
> will see in build output and in stack traces.

## Run the test suite

> The `cargo test` invocation, the count of tests it runs and how long it takes,
> and the two suites a reader of this book will care about: the `.egg` file tests
> under `egraph/tests/egg/`, and `book_examples`, which executes every program in
> this book. Say that a book example is a test.
>
> Name the slow suites that are `#[ignore]`d and how to run them, so a reader does
> not conclude the suite is incomplete.
