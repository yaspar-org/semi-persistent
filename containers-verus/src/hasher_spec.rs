// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `SpMap`'s index hasher: a seed-controlled, deterministic-by-default
//! `BuildHasher`, plus the trusted fact that it builds valid hashers (trust
//! ledger group D — hasher axioms).
//!
//! `SpMap`'s transient key index is `std::collections::HashMap<K, usize, S>`
//! with `S = IndexHasher`. `IndexHasher` hashes with foldhash's `fast` family —
//! the same hash ALGORITHM production gets from `hashbrown 0.17`, whose
//! `DefaultHashBuilder` is a newtype wrapping `foldhash::fast::RandomState`.
//! That closes the SpMap performance gap (SipHash → foldhash) with no
//! algorithmic change.
//!
//! ## Determinism policy
//!
//! Reproducible hashing is a project requirement. `IndexHasher` is therefore
//! seeded from a value the operator controls; absent configuration, the default
//! build falls back to a fixed constant rather than per-process entropy. This
//! pins this hash component, not every source of process- or machine-level
//! nondeterminism.
//!
//! | build | default seed | reproducible across processes? |
//! |---|---|---|
//! | default | configured seed, else [`DEFAULT_SEED`] | yes, when startup configuration is serialized and identical |
//! | `hasher-random-seed` | fresh per-process entropy | no (deliberately) |
//!
//! [`DEFAULT_SEED`] is `0`, and that is not arbitrary: foldhash defines
//! `with_seed(0)` to coincide with its own `FixedState::default()`, so the
//! default build reproduces foldhash's canonical fixed-seed hashes.
//! `tests/hasher_determinism.rs` pins those as golden values.
//!
//! ### Three ways to control the seed
//!
//! 1. **Environment** — set `SP_HASHER_SEED` to a `u64` (decimal, or
//!    `0x`-prefixed hex). Read once, lazily, on first use. This is the "fix it
//!    via config" path for an already-deployed binary: no rebuild, no code
//!    change.
//! 2. **Programmatically** — [`set_default_seed`] during startup, e.g. from a
//!    parsed config file. Takes precedence over the environment. It fails once
//!    the seed has been observed (see "Seal-on-first-use"). Call it during
//!    single-threaded startup; a concurrent first use can make the call return
//!    [`SeedSealed`] after different hashers have observed different seeds.
//! 3. **Per instance** — [`IndexHasher::with_seed`] is a `const fn`; hand it to
//!    a `HashMap` directly when one map wants its own seed.
//!
//! [`effective_seed`] reports the current process default. Logging it and
//! feeding it back reproduces hashing when all default hashers were constructed
//! after one serialized seed choice. It cannot diagnose a caller that ignored
//! a concurrent [`SeedSealed`] error.
//!
//! ### Seal-on-first-use
//!
//! Reproducibility is only auditable if the seed is constant for the process.
//! The first `IndexHasher::default()` therefore *seals* the seed:
//! [`set_default_seed`] then returns [`SeedSealed`] rather than accepting a late
//! update. Callers that must control the seed must set it before constructing
//! any container and treat the error as fatal. The atomics detect, but do not
//! roll back, a setter racing with first use; continuing after that race can
//! leave already-constructed and later hashers with different seeds.
//!
//! ### Why the seed lives in `Default`, not a `with_hasher` constructor
//!
//! `SpMap::new()` reaches its index through `HashMap::default()`. That is the
//! constructor vstd specs *generically* over `S: Default`; vstd does NOT spec
//! `HashMap::with_hasher` (zero occurrences in `std_specs::hash`). Routing the
//! seed through `IndexHasher`'s own `Default` therefore keeps the whole map
//! verified with no added trust, whereas a `with_hasher`-based API would have
//! needed a new trusted `assume_specification` — more TCB for the same knob.
//!
//! ### What the seed does and does NOT affect
//!
//! Worth being precise, because "deterministic hashing" is easy to overclaim.
//! The seed perturbs which BUCKET a key lands in — nothing else. `SpMap`'s
//! observable behaviour is already seed-independent by construction: the
//! append-only log is the source of truth, `iter()` walks that log in insertion
//! order, `rebuild_index` replays the log in insertion order, and the index is
//! never iterated (lookup-only: `get`/`contains_key`/`insert`/`clear`). So
//! fixing the seed changes no output; it makes the internal memory layout and
//! probe sequences reproducible too, which is what makes a hash-order bug or a
//! performance regression bisectable rather than a coin flip.
//!
//! ## Why the axiom is credible
//!
//! `builds_valid_hashers::<S>()` asserts, per vstd's prose (`std_specs::hash`),
//! that for any two hashers `S` builds, feeding both the same write sequence
//! leaves them in matching states with the same `finish()` digest. It does NOT
//! assert collision-freedom or any distribution property — a HashMap's
//! correctness never depends on those.
//!
//! vstd models `std::HashMap<K, V, S>` generically over any `S: BuildHasher`
//! (`insert`/`get`/`contains_key`/`len`/`clear`/`default` are all `S`-generic,
//! gated on `builds_valid_hashers::<S>()`). vstd ships exactly one instance of
//! that predicate as an axiom — `axiom_random_state_builds_valid_hashers`, for
//! std's `RandomState` (`admit()`ed, since the predicate is `uninterp` and no
//! proof can conclude it for ANY hasher). This module supplies the mirror-image
//! fact for `IndexHasher`.
//!
//! `IndexHasher` is the *easier* assumption than vstd's own. It stores its seed
//! by value at construction, so `build_hasher` is a pure function of that seed
//! and every hasher a given instance builds is identically seeded — including
//! under `hasher-random-seed`, where the entropy is drawn once when the seed is
//! chosen, never per `build_hasher` call. In the default build the unconfigured
//! fallback is a compile-time constant; environment or programmatic
//! configuration can replace it. For every constructed `IndexHasher`,
//! determinism given its stored seed and the fed bytes is the trusted fact.
//!
//! Trust ledger: group D (hasher facts), 1 axiom + 2 contract-free external
//! type registrations (`IndexHasher` and foldhash's `FoldHasher`, both needed
//! only so the types can be NAMED in specs). Unlike the `obeys_key_model` key
//! axioms (feature `literal-types`), the hasher fact is UNCONDITIONAL: `SpMap`'s
//! index is core, so it is needed in every build.

use core::hash::BuildHasher;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use vstd::prelude::*;
// `std_specs::hash` is spec-only; vstd gates it behind `cfg(verus_keep_ghost)`
// (set by the Verus driver, not plain cargo). Mirror the gate — the ghost part
// of this module is one axiom + two type registrations.
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::builds_valid_hashers;

/// Environment variable that overrides the default seed.
///
/// Value is a `u64`: decimal, or hex with a `0x`/`0X` prefix. A malformed value
/// panics rather than falling back silently — a typo'd seed that quietly
/// reverted to the default would defeat the point of pinning it.
pub const SEED_ENV_VAR: &str = "SP_HASHER_SEED";

/// The built-in default seed.
///
/// foldhash defines `with_seed(0)` to coincide with `FixedState::default()`, so
/// this makes the default build reproduce foldhash's canonical fixed-seed
/// hashes — the values pinned in `tests/hasher_determinism.rs`.
pub const DEFAULT_SEED: u64 = 0;

/// The process-wide seed handed to `IndexHasher::default()`. [`SEED_INIT`]
/// tracks whether it has been resolved, so no seed value is stolen as a
/// sentinel — all 2^64 are usable.
static DEFAULT_SEED_CELL: AtomicU64 = AtomicU64::new(DEFAULT_SEED);
/// Whether `DEFAULT_SEED_CELL` has been resolved (env read, or seed set).
static SEED_INIT: AtomicBool = AtomicBool::new(false);
/// Whether the default seed has been OBSERVED — i.e. some `IndexHasher` was
/// built from it. Sealing at that point makes "one seed per run" an invariant
/// rather than a hope.
static SEED_SEALED: AtomicBool = AtomicBool::new(false);

/// [`set_default_seed`] was called after the seed had already been used.
///
/// Returned rather than ignored: a mid-run seed change would split the process
/// into two hash regimes, so this is a real error the caller should handle by
/// setting the seed earlier, before constructing any container.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SeedSealed {
    /// The seed that is — and will remain — in force for this process.
    pub in_force: u64,
}

impl core::fmt::Display for SeedSealed {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "hasher seed is already sealed at {:#018x}; set it during startup, \
             before constructing any container",
            self.in_force
        )
    }
}

impl std::error::Error for SeedSealed {}

/// Parse a seed from an environment value: decimal, or `0x`-prefixed hex.
/// Panics on a malformed value — see [`SEED_ENV_VAR`].
fn parse_seed(raw: &str) -> u64 {
    let t = raw.trim();
    let parsed = match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => t.parse::<u64>(),
    };
    parsed.unwrap_or_else(|e| {
        panic!("{SEED_ENV_VAR}={raw:?} is not a valid u64 seed ({e}); expected decimal or 0x-hex")
    })
}

/// Draw a fresh per-process seed. Only reached under `hasher-random-seed`.
///
/// std's `RandomState` is the entropy source already present in every std build
/// (it is what `HashMap::new()` uses), so this needs no extra dependency: hash a
/// constant with it and take the digest as the seed.
#[cfg(feature = "hasher-random-seed")]
fn random_seed() -> u64 {
    std::collections::hash_map::RandomState::new().hash_one(0u64)
}

/// Resolve the default seed on first use: an explicit [`set_default_seed`] wins,
/// else [`SEED_ENV_VAR`], else [`DEFAULT_SEED`] (or fresh entropy under
/// `hasher-random-seed`).
fn resolve_default_seed() -> u64 {
    if !SEED_INIT.load(Ordering::Acquire) {
        #[cfg(not(feature = "hasher-random-seed"))]
        let fallback = DEFAULT_SEED;
        #[cfg(feature = "hasher-random-seed")]
        let fallback = random_seed();

        let seed = match std::env::var(SEED_ENV_VAR) {
            Ok(raw) => parse_seed(&raw),
            Err(_) => fallback,
        };
        // A concurrent resolver may win this race; either way exactly one value
        // is published, and `SEED_INIT` never returns to false, so the seed
        // observed from here on is stable.
        if !SEED_INIT.swap(true, Ordering::AcqRel) {
            DEFAULT_SEED_CELL.store(seed, Ordering::Release);
        }
    }
    DEFAULT_SEED_CELL.load(Ordering::Acquire)
}

/// Pin the process-wide default seed, e.g. from a parsed config file.
///
/// Call during startup, before constructing any container. Takes precedence over
/// [`SEED_ENV_VAR`].
///
/// # Errors
///
/// [`SeedSealed`] if the seed has already been observed — see
/// "Seal-on-first-use" in the module docs. With serialized startup, an error
/// means the seed is unchanged. If this call races with first use, it may have
/// published `seed` before detecting the race; the caller must treat the error
/// as fatal because an earlier hasher may hold the previous value.
pub fn set_default_seed(seed: u64) -> Result<(), SeedSealed> {
    let sealed = || SeedSealed {
        in_force: DEFAULT_SEED_CELL.load(Ordering::Acquire),
    };
    if SEED_SEALED.load(Ordering::Acquire) {
        return Err(sealed());
    }
    DEFAULT_SEED_CELL.store(seed, Ordering::Release);
    SEED_INIT.store(true, Ordering::Release);
    // Re-check: a hasher built concurrently with this call could have sealed the
    // seed just after the first check, having read either value. Reporting the
    // race is the honest outcome; swallowing it would let two hash regimes
    // coexist behind an `Ok`.
    if SEED_SEALED.load(Ordering::Acquire) {
        return Err(sealed());
    }
    Ok(())
}

/// The seed `IndexHasher::default()` will use, resolving it if needed.
///
/// Log this to make a run reproducible: feeding the value back via
/// [`SEED_ENV_VAR`] or [`set_default_seed`] reproduces the same hashing — the
/// point of the whole policy under `hasher-random-seed` in particular.
///
/// Reading the seed does NOT seal it; only building a hasher does.
pub fn effective_seed() -> u64 {
    resolve_default_seed()
}

/// Whether the default seed has been observed and is therefore now immutable.
pub fn seed_is_sealed() -> bool {
    SEED_SEALED.load(Ordering::Acquire)
}

/// `SpMap`'s index `BuildHasher`: foldhash `fast` with an explicit seed.
///
/// 8 bytes — the same size as `foldhash::fast::RandomState` and hashbrown's
/// `DefaultHashBuilder`, so seed control costs nothing in memory parity.
/// (foldhash's own `SeedableRandomState`, which defers fixed-vs-random to
/// runtime, is 16 bytes; carrying just the seed gets the same flexibility at
/// half the width.)
///
/// `Default` uses the process seed (see the module docs); [`Self::with_seed`]
/// pins one per instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IndexHasher {
    seed: u64,
}

impl IndexHasher {
    /// An `IndexHasher` with an explicit seed, independent of process config.
    ///
    /// `const`, so it can seed a `static`. Seed [`DEFAULT_SEED`] reproduces
    /// `foldhash::fast::FixedState::default()`.
    #[inline(always)]
    pub const fn with_seed(seed: u64) -> Self {
        Self { seed }
    }

    /// This instance's seed — what to record to reproduce its hashing.
    #[inline(always)]
    pub const fn seed(&self) -> u64 {
        self.seed
    }
}

impl core::default::Default for IndexHasher {
    /// Seeds from process config, and SEALS that seed (module docs:
    /// "Seal-on-first-use").
    #[inline]
    fn default() -> Self {
        let seed = resolve_default_seed();
        SEED_SEALED.store(true, Ordering::Release);
        Self::with_seed(seed)
    }
}

impl BuildHasher for IndexHasher {
    type Hasher = foldhash::fast::FoldHasher<'static>;

    /// Delegates to foldhash, so the hash FUNCTION is exactly the one production
    /// uses via hashbrown. `FixedState::with_seed` is a const XOR, so this is
    /// the same work `FixedState::build_hasher` does — no added indirection.
    #[inline(always)]
    fn build_hasher(&self) -> Self::Hasher {
        foldhash::fast::FixedState::with_seed(self.seed).build_hasher()
    }
}

verus! {

// Register the hasher types as opaque external types so they can be NAMED in
// specs. No semantics assumed here (`external_body`); the fact follows below.
// `IndexHasher` is ours, but is registered the same way: its internals are
// irrelevant to the model, which observes only `builds_valid_hashers`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)] // registration marker; the wrapped field is never read
pub struct ExIndexHasher(crate::hasher_spec::IndexHasher);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)] // registration marker; the wrapped field is never read
pub struct ExFoldHasher<'a>(foldhash::fast::FoldHasher<'a>);

/// `IndexHasher` builds valid hashers. Mirrors vstd's shipped
/// `axiom_random_state_builds_valid_hashers` for std's `RandomState`, and is the
/// weaker assumption: the seed is stored by value at construction, so
/// `build_hasher` is a pure function of it and every hasher one instance builds
/// is identically seeded. Trust ledger: group D (hasher facts).
pub broadcast axiom fn axiom_index_hasher_builds_valid_hashers()
    ensures
        #[trigger] builds_valid_hashers::<IndexHasher>(),
;

} // verus!
