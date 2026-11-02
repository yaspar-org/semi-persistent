# Changelog

## [Unreleased]

### Added

- `egraph/tests/egg/cbmc/`: 214 programs converted from 107 CBMC e-graph dumps (a
  `base` and a `cong` e-graph per dump, up to 42,120 nodes each), with the converter
  `scripts/cbmc-egg-convert.py`. `cbmc_corpus` in `egg_tests.rs` loads and rebuilds every
  one under naive and semi-naive evaluation.
- `(query fact ... :limit n)` prints a query's matches, each named variable as a term
  extracted from its class, ordered by content colour so the output does not depend on
  class ids.
- `(check ... :count k)`, `:min k` and `:none` count a check's matches, as distinct
  assignments of its named variables.
- `(!= p q)` in checks and rule bodies requires two different e-classes. Literal values
  are compared by the typed guard (`IBig::!=`).
- `SpMap` has a key discipline parameter: `SpMap<K, V, I, TRACK, UNIQUE>`,
  with `SpUniqueMap<K, V, I, TRACK>` as the `UNIQUE = true` alias. Under it
  no key occurs twice in the log — `try_insert` refuses a present key with
  the new `ContainerError::DuplicateKey`, `try_intern` answers with the
  existing entry — and the previous-occurrence column is not kept, so an
  insert is one hash and one log push and a restore's index unwind is a
  bare removal per discarded entry. The default `UNIQUE = false` is the
  published last-write-wins map, unchanged. Every interning table in the
  e-graph (four registries, the literal store, the unit-node and
  inverse-op maps, the seven anti-unification indices) and the hinted
  arena's fingerprint index are `SpUniqueMap`s; a repeated operator, rule
  or axiom name, or a second unit node or inverse for an operator, is now
  refused by the map rather than shadowed.
- `SpMap::try_intern`: interning insert in one hash of the key.
- `SpMap::try_intern_with(key, f)`: interning insert whose value is computed
  only on a miss, still in one hash. The anti-unification action cache and
  or-statistics map build their entries inside it; the action cache used to
  hash a class pair three times per visit (check, insert, read-back).
- `SpMap<…, S>`: the index's hasher is a parameter, any `hasher_spec::ValidHasher`
  (`Default`, and provably valid in vstd's model on an already-shipped axiom).
  `IndexHasher` stays the default; `std::hash::RandomState` is implemented for
  keys from an untrusted source. No new trusted item.
- `VecD`, the runtime-selected three-tier column, is an enum over the three
  static columns (`vec_dyn`), dispatched once per operation, instead of a
  `Vec` over the per-primitive `DynStore`. Same constructors and methods;
  it is no longer the same type as `Vec<T, I, DynStore<T, I>, TRACK>`,
  which still exists. On the three-tier write rows the runtime-selected
  columns were 1.26–2.2× the static ones running the same loops; they are
  now within 1.02–1.19 on writes (one match per operation) and level on
  restores.
- The e-graph node caches' hint slot is the id family's own repr word with
  the family's reserved bit as the spill marker (`HintSlot<L>`), so it is as
  wide as the id: 32 bits for a 31-bit family, 64 for a 63-bit one. It was a
  hardcoded `u32` with a `1 << 31` tag that a 63-bit id would have overflowed
  into the spill index silently in release builds.
- `AppendOnlyVec::try_push` reads the length once for the capacity test, the
  returned index and the append, and the whole append path (`try_push`,
  `push`, `len`, `can_push`, `as_slice`, the group's `Deref`) is inlined
  unconditionally: the append loop a caller runs is a compare, a branch to
  the cold growth call and a store, the same instructions as a bare
  `Vec::push` loop.
- `retained_containers_bench` has `aov/push`, `aov/push_presized`,
  `aov/scan` and `aov/mark_restore` beside the alignment-bound `aov/log`
  composite, and `bench_compare.py` prints a speedup column (reference ÷
  new) next to its ratio.

### Changed

- The AC completion mode is part of the program: `(set-option :completion
  off|eager)` sets graph completion and `(set-option :check-completion on|off)`
  check completion, from that command on; `:complete` and `:no-complete` override
  check completion for one command. `--derive-ac-eqs` and `--lazy-ac-eqs` set the
  starting values, which a program's `set-option` overrides. The test fixtures'
  `;; DERIVE_AC_EQS:` and `;; LAZY_AC_EQS:` directives are replaced by `set-option`
  lines (55 fixtures), and the harness rejects the old directives.

- `prove` is renamed to `check-eq` and `check-neq`: `(prove (= a b))` is
  `(check-eq a b)`, `(prove (!= a b))` is `(check-neq a b)`, and a build-only
  `(prove t)` is the bare term `t`. `check-eq` takes two or more terms and requires
  them all in one class. `prove` is a parse error that names its replacement.
  `scripts/migrate-prove.py` rewrote the repository (3,509 sites); the hash-pinned
  egglog example manifests were refreshed for the rewritten programs.

- `check` has egglog's semantics: `(check fact ...)` is a conjunctive query over the
  e-graph in the language of rule bodies, it builds nothing, and it succeeds when the
  query has a match. A name that is not a global is a variable of that one check. In
  lazy AC mode a check runs completion, and rule rounds when needed, inside the check
  transaction, and reports a budget stop as inconclusive. The previous meaning (build the
  terms, rebuild, compare classes) is `prove`; every check in the repository was rewritten
  to `prove` by `scripts/migrate-check.py`. **Breaking:** a program whose check names a
  term it never built now fails; write `prove` for the old meaning.
- `(run N :until fact ...)` takes a query goal, as egglog's does. The ground goal that
  builds its terms once is `(run N :goal (= a b))`.
- `explain_deep`'s memoization is now recorded in full: the code comment,
  design chapter 15 and a regression test (`deep_proof_diamond_is_linear`)
  state both failure modes the two pair sets prevent, exponential
  re-expansion on diamonds and non-termination when a congruence step's
  original-children pair routes through that same edge, with the termination
  bound that follows.

- `reconstruct_parent_split` (B+ tree) is three proofs instead of one: the
  link splice and the footprint reasoning moved into
  `reconstruct_parent_split_links` and `reconstruct_parent_split_ids`, and the
  `rlimit(70)` bump is gone; every query now verifies at the default limit
  (the single body timed out on the Linux CI runner). Every quantifier whose
  trigger Verus reported as auto-chosen now carries that trigger explicitly
  (containers-verus and au-verus); the verifier prints no trigger notes.

- Version tokens now carry their minting manager, a generation and a depth
  (`GroupToken`; `VecToken` is an alias); every container is a group of one
  with its own token manager, and a token from another container is refused.
- `restore(t)` resets to the checkpoint and keeps its frame open (semantics
  B): the token stays valid and can be restored to again, every token minted
  after it is dead, and the new `pop_scope` / `try_pop_scope` (with
  `ContainerError::NoOpenFrame`) drops the open top frame. The SMT-LIB
  `pop` is `restore_and_pop(t)` / `try_restore_and_pop(t)`: the two fused
  on one pop core, at the legacy restore's cost. The e-graph gains
  `EGraph::pop_scope` and `EGraph::restore_and_pop`; its interpreter's
  `(pop)` is the fused call. The stamp table
  behind token validity is O(1) per mark and per restore, and a restore
  never migrates tier history (the reopened frame is a header push with a
  deferred rollover; the next `mark` applies the tier policy once).
- The e-graph literal store is a verified `SpMap` keyed by canonical keys
  (`LitVal::Key`, `CanonicalKey`): floats intern under `CanonicalF64`,
  rationals under `CanonicalRational`.
- Byte reporters (`heap_bytes`, `tracking_bytes`, `total_bytes`,
  `diff_log_len`) are plain Rust outside the verified perimeter; the
  `HeapBytes` trait is exported for stores, and `DiffStore` no longer has a
  `heap_bytes` method.
- The Trail dedupe takes a verified straight-copy fast path on strictly
  ascending frames.

- The fork-history manager is always provided from the outside:
  `group::ForkHistory<M: Member>` owns one `History` and one typed member.
  Members carry no tokens — their versioning surface is structural
  (`push_frame`, `reset_frame`, `restore_frame`, `pop_frame`, `depth_exec`) —
  and the group answers `mark` (`Option<GroupToken>`),
  `restore`/`restore_and_pop`/`pop_scope` (`bool`), `mint_pushed`, `is_valid`,
  `depth` and `in_lockstep`. Every container in the crate is a `Member`,
  `Pair<A, B>` forwards to two members and nests, and a standalone container
  is a group of one (`ForkHistory::new(Vec::new())`). `Deref`/`DerefMut` keep
  typed access. A member driven behind the group's back drifts and the next
  group operation refuses, changing nothing.
- The e-graph runs its nine synchronized members on one `History` through a
  borrowed forwarding view (`EGraphMembers`): no per-member token stacks, one
  token per scope for the whole e-graph. Store traces land at 0.97–1.00× of
  the previous commit, `empty20k` at 0.79–0.80×, saturation at parity.

- The trusted base is 12 `external_body` items, down from 34: twelve read-only
  diagnostics moved out of the verified perimeter, and ten were proved (the B+
  tree node-layout primitives, the container id's equality, the sparse set's
  value comparison, the precondition guard and the compression-mode heuristic
  with its statistics pass). The B+ tree paths pay Rust's bounds checks again;
  they remain faster than the unverified implementation.

### Fixed

- In lazy AC mode, a `check` whose facts contain `(!= p q)` now waits for the
  completion fixpoint before answering. It stopped at the first match, so
  `(check (!= u t))` could pass where a later merge, after a rule round and AC
  completion, joins `u` and `t`.

### Removed

- Every container's own versioning surface. `Vec`, `AppendOnlyVec`, `SpMap`,
  `SparseSet`, `CircularList`, `ListArena`, `UnionFind`, `BPlusTreeSet`,
  `EClasses` and `HintedArena` no longer have `mark`, `try_mark`, `restore`,
  `try_restore`, `restore_and_pop`, `try_restore_and_pop`, `pop_scope`,
  `try_pop_scope` or `is_valid_token`, and the token types (`MapToken`,
  `SparseSetToken`, `CircularListToken`, `ListArenaToken`, `UnionFindToken`,
  `BPlusToken`, `EClassesToken`) are gone; `VecToken` remains as the alias for
  the group's `GroupToken`. Version a container by putting it in a
  `ForkHistory` group of one. `Vec` and `AppendOnlyVec` also lost the embedded
  `Genealogy`: the branch cut happens in the group's `History`.
- The predecessor dyn group (`sync_group`, with `Box<dyn SyncMember>`
  members) and the `Solo`/`SyncPair` migration wrappers.
- In the e-graph, the wrappers' token layer: `CacheToken`, `PoolCacheToken`,
  `NodeStoreToken`, `RoutingToken`, `LitValStoreToken` and the registry
  tokens. The director pool takes the frame protocol instead.

### Added

- Randomized grouped-history tests at the `ForkHistory` and e-graph levels,
  and a typed-group suite (`tests/typed_group.rs`): a group of one per
  container, a nested `Pair` of three columns under one history driven by a
  randomized lockstep proptest, and the refusal cases.

## [0.3.0] - 2026-08-28

### Added

- Added the Semper book, with executable examples covering the language,
  algebraic canonization, saturation, anti-unification, and policy repair.

### Changed

- Made malformed algebraic declarations and rule right-hand sides fail during
  resolution instead of relying on unchecked representation invariants.
- Clarified that anti-unification optimality is relative to the equalities
  materialized in the selected e-graph completion mode.
- Aligned every workspace package and internal published dependency at
  version `0.3.0`.

### Fixed

- Honored `:assoc-left` and `:assoc-right` flattening directions during both
  source-term construction and rewrite right-hand-side construction.
- Rejected algebraic operators whose argument and result sorts make variadic
  singleton collapse unsound, as well as conflicting associativity tags.
- Added lexically scoped right-hand-side comprehension locals without mutating
  query match shapes or runtime match rows.
- Enforced collection element sorts, fixed right-hand-side arity, and
  literal-producing comprehension filters.
- Rebuilt before every `run :until` observation, including the final
  observation after exhausting the rule-round budget.

## [0.2.0] - 2026-08-25

### Added

- Published `semi-persistent-containers-verus`, the executable
  Verus-verified container layer used by the e-graph.
- Added canonical license, conduct, contribution, and security documents to
  every workspace package, with a CI gate for package metadata and source
  headers.
- Added Exact and Monte Carlo graph search for e-graph anti-unification,
  including explicit cycle policies and rewrite-aware semantic diffing.
- Added native associative, commutative, and idempotent canonization across
  construction, matching, and anti-unification.
- Added plain, eager, and goal-directed lazy AC congruence-closure modes.
- Added deterministic batch proof-path export using an Euler-tour LCA index.

### Changed

- Switched `semi-persistent-egraph` to the verified container implementation;
  the independent Rust implementation remains available as a differential and
  performance reference.
- Reworked AC matching around maximum partitions so its exponential factor is
  in pattern variables and distinct children rather than child multiplicity.
- Made pool-backed variadic recursion-scheme nodes traversable and deduplicated
  by their child sequences.
- Aligned every workspace package and internal published dependency at
  version `0.2.0`.

### Verification

- Added differential, property, layout, and regression coverage between the
  verified and reference container implementations.
- Added Verus proofs for the container protocol and selected
  anti-unification objective and lower-bound lemmas. The exact scope and
  remaining obligations are maintained in [`doc/claims.md`](doc/claims.md).
