// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Reproducibility guarantees for `SpMap`'s index hasher.
//!
//! Project requirement: the same inputs must produce the same run, byte for
//! byte, across processes and machines. `IndexHasher` therefore carries an
//! explicit seed whose default is a fixed constant, controllable via
//! `SP_HASHER_SEED`, `set_default_seed`, or `IndexHasher::with_seed`.
//!
//! Three distinct claims get pinned here, and they are NOT the same:
//!
//!   1. **Observable determinism** — `SpMap`'s public behaviour never depends on
//!      the seed at all, in any configuration. The log is the source of truth,
//!      `iter()` walks it in insertion order, `rebuild_index` replays it in
//!      insertion order, and the index is lookup-only (never iterated).
//!   2. **Hash-level determinism** — with the default seed, hashes are equal to
//!      pinned GOLDEN VALUES, so bucket placement and probe sequences reproduce
//!      across processes and machines too. That is what makes a hash-order bug
//!      or a perf regression bisectable instead of a coin flip. Self-consistency
//!      within one process would prove nothing here (a randomly seeded hasher
//!      also satisfies it), hence absolute values.
//!   3. **Seed control** — `with_seed` actually changes the hashing, distinct
//!      seeds disagree, and equal seeds agree.
//!
//! Note on the process-global seed: `set_default_seed` and `SP_HASHER_SEED`
//! govern one process-wide cell and seal on first use, so they cannot be
//! exercised from cargo's shared-process test harness without ordering races
//! against every other test. The per-instance path (`with_seed`) is what is
//! asserted here; the global path is covered by `tests/hasher_seed_config.rs`,
//! which runs one scenario per process.

use std::hash::{BuildHasher, Hash};

use semi_persistent_containers_verus::hasher_spec::{DEFAULT_SEED, IndexHasher};
use semi_persistent_containers_verus::{ShrinkPolicy, SpMap};

/// Hash one value with an explicitly seeded builder.
fn hash_seeded<T: Hash>(seed: u64, v: &T) -> u64 {
    IndexHasher::with_seed(seed).hash_one(v)
}

// ---------------------------------------------------------------------------
// 1. Hash-level determinism: golden values
// ---------------------------------------------------------------------------

/// Absolute hash outputs for the default seed, recorded from foldhash 0.2.0.
///
/// `DEFAULT_SEED` is 0, and foldhash defines `with_seed(0)` to coincide with
/// `FixedState::default()` — so these are also foldhash's canonical fixed-seed
/// hashes, which makes them checkable against the upstream crate directly.
///
/// If this test fails, the effective hashing changed: a foldhash upgrade, a
/// different `DEFAULT_SEED`, or a change to `build_hasher`. That is not
/// automatically wrong, but it breaks byte-for-byte reproducibility against
/// every prior run, so update these constants only deliberately and record the
/// change (see `src/hasher_spec.rs`).
#[test]
fn default_seed_hashes_are_pinned_to_golden_values() {
    const GOLDEN_U64: [(u64, u64); 5] = [
        (0, 0x5fdf_1327_d2d8_911f),
        (1, 0x9f63_3a9f_ad5c_2231),
        (2, 0xdd78_bfb7_41d1_30a4),
        (42, 0xed5b_5072_6db8_abda),
        (u64::MAX, 0x5fdf_4a97_c2d3_115f),
    ];
    for (k, expected) in GOLDEN_U64 {
        let got = hash_seeded(DEFAULT_SEED, &k);
        assert_eq!(
            got, expected,
            "hash of u64 {k} moved: got 0x{got:016x}, expected 0x{expected:016x} \
             — the default seed or hash algorithm changed"
        );
    }

    // Byte-fed keys travel a different foldhash path than fixed-width ints, so
    // pin both.
    const GOLDEN_STR: [(&str, u64); 3] = [
        ("", 0x36ce_5d2e_6332_2a37),
        ("a", 0xec1c_48cf_e246_8b3c),
        ("hello world", 0xe756_593d_261a_9738),
    ];
    for (s, expected) in GOLDEN_STR {
        let got = hash_seeded(DEFAULT_SEED, &s.to_string());
        assert_eq!(
            got, expected,
            "hash of {s:?} moved: got 0x{got:016x}, expected 0x{expected:016x} \
             — the default seed or hash algorithm changed"
        );
    }
}

/// The documented tie between `DEFAULT_SEED` and foldhash's own fixed state.
/// `hasher_spec` claims seed 0 reproduces `FixedState::default()`; assert it
/// against the upstream type rather than trusting the comment.
#[test]
fn default_seed_matches_foldhash_fixed_state() {
    for i in 0u64..256 {
        let ours = hash_seeded(DEFAULT_SEED, &i);
        let theirs = foldhash::fast::FixedState::default().hash_one(i);
        assert_eq!(
            ours, theirs,
            "DEFAULT_SEED no longer coincides with foldhash's FixedState::default() at {i}"
        );
    }
}

/// `IndexHasher` must stay pointer-width-cheap: seed control is only free if it
/// is the same 8 bytes hashbrown's `DefaultHashBuilder` is. (foldhash's
/// `SeedableRandomState` is 16 — this guards against drifting onto it.)
#[test]
fn index_hasher_is_eight_bytes() {
    assert_eq!(
        std::mem::size_of::<IndexHasher>(),
        8,
        "IndexHasher grew past 8 bytes — memory parity with production's \
         hashbrown DefaultHashBuilder is lost"
    );
}

// ---------------------------------------------------------------------------
// 2. Seed control
// ---------------------------------------------------------------------------

/// Equal seeds hash identically; distinct seeds (mostly) do not. The second
/// half is what proves the seed is actually wired into the hash rather than
/// being a decorative field.
#[test]
fn seed_controls_hashing() {
    for i in 0u64..128 {
        assert_eq!(
            hash_seeded(7, &i),
            hash_seeded(7, &i),
            "same seed disagreed with itself at {i}"
        );
    }

    // A seed change must perturb essentially every key. Not asserting ALL
    // differ: two seeds colliding on one key is legitimate hash behaviour, so
    // require an overwhelming majority instead of a property foldhash never
    // promised.
    let differing = (0u64..256)
        .filter(|i| hash_seeded(DEFAULT_SEED, i) != hash_seeded(0xdead_beef, i))
        .count();
    assert!(
        differing > 250,
        "changing the seed perturbed only {differing}/256 hashes — the seed is \
         not reaching the hash function"
    );

    assert_eq!(IndexHasher::with_seed(99).seed(), 99, "seed() misreports");
}

/// `with_seed` is `const`, so a seed can be pinned in a `static`/`const`
/// context. Compile-time check as much as a runtime one.
#[test]
fn with_seed_is_const() {
    const PINNED: IndexHasher = IndexHasher::with_seed(0x1234_5678_9abc_def0);
    assert_eq!(PINNED.seed(), 0x1234_5678_9abc_def0);
}

// ---------------------------------------------------------------------------
// 3. Observable determinism (holds for ANY seed)
// ---------------------------------------------------------------------------

/// `iter()` yields insertion order, independent of hashing. Two maps built the
/// same way must agree exactly — including on shadowed (overwritten) entries,
/// which linger in the log by design.
#[test]
fn iteration_order_is_insertion_order() {
    let build = || {
        let mut m: SpMap<u64, u64, true> = SpMap::new();
        for i in 0..64u64 {
            m.insert(i * 7 % 13, i);
        }
        m.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>()
    };
    let a = build();
    let b = build();
    assert_eq!(a, b, "iteration order differed between identical maps");

    // And it really is insertion order, not hash order: reconstruct expected.
    let expected: Vec<(u64, u64)> = (0..64u64).map(|i| (i * 7 % 13, i)).collect();
    assert_eq!(a, expected, "iter() did not yield insertion order");
}

/// The headline reproducibility property: identical operation sequences produce
/// identical observable state, including across mark/restore (which rebuilds the
/// index from scratch — the one place hashing could leak into behaviour).
#[test]
fn identical_op_sequences_produce_identical_state() {
    let run = || {
        let mut m: SpMap<String, u64, true> = SpMap::new();
        for i in 0..50u64 {
            m.insert(format!("key{}", i % 20), i);
        }
        let tok = m.mark(ShrinkPolicy::Never);
        for i in 50..100u64 {
            m.insert(format!("key{}", i % 30), i);
        }
        let after_writes: Vec<(String, u64)> = m.iter().map(|(k, v)| (k.clone(), *v)).collect();
        m.restore(tok);
        // Post-restore the index has been fully rebuilt.
        let after_restore: Vec<(String, u64)> = m.iter().map(|(k, v)| (k.clone(), *v)).collect();
        let probes: Vec<Option<u64>> = (0..30)
            .map(|i| m.get_by_key(&format!("key{i}")).copied())
            .collect();
        (after_writes, after_restore, probes)
    };
    assert_eq!(run(), run(), "identical op sequences diverged");
}

/// Lookups must agree with the log after a rebuild, for every key — the
/// invariant that makes the index a pure accelerator rather than state.
#[test]
fn lookups_agree_with_log_after_restore() {
    let mut m: SpMap<u64, u64, true> = SpMap::new();
    for i in 0..100u64 {
        m.insert(i % 40, i);
    }
    let tok = m.mark(ShrinkPolicy::Never);
    for i in 100..200u64 {
        m.insert(i % 60, i);
    }
    m.restore(tok);

    // Last-write-wins over the surviving log, computed independently.
    let mut expected = std::collections::BTreeMap::new();
    for (k, v) in m.iter() {
        expected.insert(*k, *v);
    }
    assert!(!expected.is_empty(), "test degenerated to an empty map");
    for (k, v) in &expected {
        assert_eq!(
            m.get_by_key(k).copied(),
            Some(*v),
            "index disagreed with log for key {k}"
        );
    }
    for absent in 200..210u64 {
        assert_eq!(m.get_by_key(&absent), None, "phantom key {absent}");
    }
}
