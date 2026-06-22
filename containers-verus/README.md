# containers-verus: Verified Semi-Persistent Containers

A Verus port of `semi-persistent-containers`, built to be formally verified.

## What we're proving

For every container `C<T, ..., const TRACK: bool>`:

1. **Untracked equivalence (`TRACK = false`).**
   `C` is observationally equivalent to its non-semi-persistent counterpart
   (`std::Vec<T>` for `Vec`, `Map<K,V>` for `Map`, `Set<T>` for `SparseSet` /
   `BPlusTreeSet`, etc.). `mark` and `restore` are statically uncallable.

2. **Tracked correctness (`TRACK = true`).**
   An internal ghost stack `snapshots: Seq<Spec>` records the deep copy of
   `view()` at each `mark()`. After `restore(token)`:
   `view() == snapshots[token.frame_idx]`.

3. **Branch-cut safety.**
   A ghost append-only fork tree records the history of all marks. Token
   validity is `current_path.contains(t.node_id)`. `restore(t)` has
   `requires is_valid(t)`, so tokens for cut subtrees are statically rejected.
   An exec method `is_token_valid(&self, t) -> bool` mirrors the predicate.

## What is trusted

The proofs carry **no `admit`s or `assume`s** — but that means no fact is
injected into a proof, *not* that nothing is trusted. The entire trust boundary
is a small, explicit set of `#[verifier::external_body]` items modeling things
the logic cannot describe: a process-global atomic id counter, an opaque
identity type, and a few spec-free byte-accounting diagnostics. None hides any
algorithmic logic. Every one is enumerated and justified in
[`doc/design/10-trust-boundary.md`](doc/design/10-trust-boundary.md) — read it to
know exactly what the verification does and does not guarantee.

## Architecture

```
Layer 0: tagged.rs / index_like.rs       -- Trait specs (niche, bijection)
Layer 1: diff_store.rs                   -- Capture-protocol contract (trait)
Layer 2: parallel_store.rs / inline_store.rs -- Two impls of DiffStore
Layer 3: frame.rs / container_id.rs / fork_history.rs -- Frame stack, identity, branches
Layer 4: vec.rs                          -- Vec<T,I,S,TRACK> proved over the trait specs
Layer 5: append_only_vec / map / sparse_set / list / circular_list  -- containers over the verified Vec/arena
         bplus (+ bplus_tree / bplus_layout / bplus_search)         -- BPlusTreeSet over its own InlineStore arena
         dense_id / opt / capture_bits                              -- supporting value types
```

All of the Layer-5 containers follow the same diff-store / dynamic-frames pattern
and are verified (see "Verification status" below).

## Verification status

**935 facts verified across 21 modules, 0 errors, 0 `admit`s/`assume`s**
(run `./verify-all.sh` from the package root for the live per-module tally).
The whole container family is verified:

- **`Vec`** (the semi-persistent core): the headline reconstruction theorem at
  arbitrary mark-nesting depth, over both `DiffStore` backends
  (`ParallelStore` / `InlineStore`), plus branch-cut safety and faithful `pop`.
- **`AppendOnlyVec`, `Map` (`SpMap`), `SparseSet`, `ListArena`, `CircularList`** —
  each verified for its core API, including `mark`/`restore`.
- **`BPlusTreeSet`** — fully verified, not a scaffold: `insert` (with split
  propagation and new-root growth) is *total* and carries its full model
  transition; sound in-order traversal and `seek` (the cursor enumerates the
  sorted set, never skipping a present key); the arena provably never overflows
  (so `insert` needs no caller capacity precondition); and `mark`/`restore`.
  Insert-only — production has no `remove`.

Trusted boundary: 6 `#[verifier::external_body]` items, all enumerated in
[`doc/design/10-trust-boundary.md`](doc/design/10-trust-boundary.md). Runtime
property tests (80 across 6 files) exercise the executable code against plain-`std`
oracles. The skeptical, method-by-method coverage accounting vs. the production
crate is [`doc/future/parity-audit-and-plan.md`](doc/future/parity-audit-and-plan.md).

## Prerequisites

- [Verus](https://github.com/verus-lang/verus) pinned in `.verus-version`
- [`cargo-verus`](https://github.com/verus-lang/verus)
- Rust toolchain in `rust-toolchain.toml`

## Running

```bash
# Verify everything via cargo
cargo verus verify

# Per-module driver (mirrors abstract-domains)
./verify-all.sh
```

Excluded from the default `cargo build` and `cargo test --workspace`. Built
separately, exactly like `abstract-domains`.

## Long-term goal

If the verification effort succeeds across the full container set, the
production `containers` crate gets replaced with this verified implementation
in the e-graph engine. That's a long shot but it's the direction.

## License

Apache-2.0.
