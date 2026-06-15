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

## Architecture

```
Layer 0: tagged.rs / index_like.rs       -- Trait specs (niche, bijection)
Layer 1: diff_store.rs                   -- Capture-protocol contract (trait)
Layer 2: parallel_store.rs / inline_store.rs -- Two impls of DiffStore
Layer 3: frame.rs / container_id.rs / fork_history.rs -- Frame stack, identity, branches
Layer 4: vec.rs                          -- Vec<T,I,S,TRACK> proved over the trait specs
```

Other containers (`AppendOnlyVec`, `Map`, `SparseSet`, `BPlusTreeSet`, `ListArena`)
follow the same pattern and are added incrementally.

## Verification status

Skeleton only — no proofs landed yet. See `doc/proof-status.md` (forthcoming) for the running tally.

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
