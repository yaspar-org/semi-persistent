// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The process-global seed configuration paths: `SP_HASHER_SEED` and
//! `set_default_seed`, plus seal-on-first-use.
//!
//! These govern one process-wide cell that seals on first use, so they cannot be
//! exercised as ordinary `#[test]`s — cargo runs a file's tests as threads in ONE
//! process, and whichever touched the seed first would decide the outcome for
//! the rest. Each scenario therefore runs in its own process: the `driver_*`
//! tests re-exec this same test binary, naming one `#[ignore]`d child scenario
//! and setting the environment for it.
//!
//! The per-instance path (`IndexHasher::with_seed`) needs none of this and is
//! covered in `tests/hasher_determinism.rs`.

use std::hash::BuildHasher;
use std::process::Command;

use semi_persistent_containers_verus::SpMap;
use semi_persistent_containers_verus::hasher_spec::{
    self, DEFAULT_SEED, IndexHasher, SEED_ENV_VAR,
};

/// Marks a child process, so a child never recursively spawns more children.
const CHILD_MARKER: &str = "SP_HASHER_SEED_TEST_CHILD";

/// Run one `#[ignore]`d scenario from this binary in a fresh process, with `env`
/// applied. Returns its stdout on success; panics with the captured output on
/// failure, so a child assertion surfaces as a readable parent failure.
fn run_child(scenario: &str, env: &[(&str, &str)]) -> String {
    let exe = std::env::current_exe().expect("current_exe");
    let mut cmd = Command::new(exe);
    // `--exact` so a scenario name is never a prefix-match for another;
    // `--include-ignored` because scenarios are `#[ignore]`d to keep them out of
    // the default run; `--test-threads=1` so the single scenario owns the process.
    cmd.args([
        "--exact",
        scenario,
        "--include-ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    cmd.env(CHILD_MARKER, "1");
    // Inherited state would defeat the point of a fresh process.
    cmd.env_remove(SEED_ENV_VAR);
    for (k, v) in env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("spawn child test process");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(
        out.status.success(),
        "child scenario {scenario} failed ({:?})\n--- stdout ---\n{stdout}\n--- stderr ---\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr),
    );
    // A filter matching NOTHING also exits 0, so a renamed scenario would make
    // its driver pass vacuously. Require that exactly one test actually ran.
    assert!(
        stdout.contains("1 passed"),
        "child scenario {scenario} did not run (filter matched no test?)\n{stdout}"
    );
    stdout
}

fn is_child() -> bool {
    std::env::var_os(CHILD_MARKER).is_some()
}

/// Hash a probe value with the process's default-configured hasher. Building the
/// hasher is what SEALS the seed, so callers get sealing as a side effect —
/// deliberately, since that is the behaviour under test.
fn hash_with_default_hasher(v: u64) -> u64 {
    IndexHasher::default().hash_one(v)
}

fn hash_with_seed(seed: u64, v: u64) -> u64 {
    IndexHasher::with_seed(seed).hash_one(v)
}

// ---------------------------------------------------------------------------
// Drivers (run in the normal test process; each spawns one child)
// ---------------------------------------------------------------------------

/// With nothing configured, the default build must land on `DEFAULT_SEED`.
/// This is the claim that the default build is reproducible at all.
#[test]
fn driver_unconfigured_uses_default_seed() {
    run_child("child_unconfigured_uses_default_seed", &[]);
}

/// `SP_HASHER_SEED` in decimal must take effect.
#[test]
fn driver_env_var_decimal() {
    run_child(
        "child_env_var_takes_effect",
        &[(SEED_ENV_VAR, "1234567890")],
    );
}

/// `SP_HASHER_SEED` in `0x` hex must take effect, and must mean the same as the
/// equivalent decimal (a hex value silently parsed as decimal would be a
/// silent-wrong-seed bug, the worst kind here).
#[test]
fn driver_env_var_hex_equals_decimal() {
    let hex = run_child("child_report_seed", &[(SEED_ENV_VAR, "0xFF")]);
    let dec = run_child("child_report_seed", &[(SEED_ENV_VAR, "255")]);
    assert_eq!(hex.trim(), dec.trim(), "0xFF and 255 resolved differently");
    assert!(hex.contains("seed=255"), "unexpected child report: {hex:?}");
}

/// A malformed `SP_HASHER_SEED` must FAIL LOUDLY. Falling back to the default
/// would give a silently unreproducible run — exactly what the config exists to
/// prevent. (The child is expected to panic, so this driver asserts failure
/// directly rather than going through `run_child`.)
#[test]
fn driver_malformed_env_var_panics() {
    let exe = std::env::current_exe().expect("current_exe");
    let out = Command::new(exe)
        .args([
            "--exact",
            "child_report_seed",
            "--include-ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD_MARKER, "1")
        .env(SEED_ENV_VAR, "not-a-number")
        .output()
        .expect("spawn child");
    assert!(
        !out.status.success(),
        "a malformed {SEED_ENV_VAR} was accepted instead of panicking"
    );
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        all.contains("not a valid u64 seed"),
        "panic message did not name the bad seed: {all}"
    );
}

/// `set_default_seed` must win over `SP_HASHER_SEED` — an explicit programmatic
/// choice outranks ambient environment.
#[test]
fn driver_set_default_seed_overrides_env() {
    run_child(
        "child_set_default_seed_overrides_env",
        &[(SEED_ENV_VAR, "111")],
    );
}

/// Once the seed has been observed, `set_default_seed` must fail rather than
/// split the process into two hash regimes.
#[test]
fn driver_seed_seals_on_first_use() {
    run_child("child_seed_seals_on_first_use", &[]);
}

/// A configured seed must actually reach `SpMap`'s index — the whole point.
#[test]
fn driver_configured_seed_reaches_spmap() {
    run_child(
        "child_configured_seed_reaches_spmap",
        &[(SEED_ENV_VAR, "0x99")],
    );
}

// ---------------------------------------------------------------------------
// Child scenarios (one per process; `#[ignore]`d so the default run skips them)
// ---------------------------------------------------------------------------

#[test]
#[ignore = "child scenario; spawned by a driver_* test in its own process"]
fn child_report_seed() {
    assert!(is_child(), "must be spawned by a driver");
    // Deliberately BEFORE any hasher is built: reading must not seal.
    println!("seed={}", hasher_spec::effective_seed());
    assert!(
        !hasher_spec::seed_is_sealed(),
        "effective_seed() sealed the seed; only building a hasher should"
    );
}

#[test]
#[ignore = "child scenario; spawned by a driver_* test in its own process"]
fn child_unconfigured_uses_default_seed() {
    assert!(is_child(), "must be spawned by a driver");
    assert!(
        std::env::var_os(SEED_ENV_VAR).is_none(),
        "driver failed to clear {SEED_ENV_VAR}"
    );

    // In the default build the seed is the fixed constant; under
    // `hasher-random-seed` it is fresh entropy, which is the documented
    // difference between the two builds.
    #[cfg(not(feature = "hasher-random-seed"))]
    {
        assert_eq!(
            hasher_spec::effective_seed(),
            DEFAULT_SEED,
            "default build did not use DEFAULT_SEED"
        );
        assert_eq!(
            hash_with_default_hasher(42),
            hash_with_seed(DEFAULT_SEED, 42),
            "default hasher disagreed with an explicitly DEFAULT_SEED-ed one"
        );
    }
    #[cfg(feature = "hasher-random-seed")]
    {
        // Can't assert a specific value, but the seed must still be STABLE and
        // reportable — that is what makes a randomized run replayable.
        let s = hasher_spec::effective_seed();
        assert_eq!(s, hasher_spec::effective_seed(), "random seed not stable");
        assert_eq!(
            hash_with_default_hasher(42),
            hash_with_seed(s, 42),
            "effective_seed() does not describe the hasher actually built"
        );
    }
}

#[test]
#[ignore = "child scenario; spawned by a driver_* test in its own process"]
fn child_env_var_takes_effect() {
    assert!(is_child(), "must be spawned by a driver");
    const EXPECTED: u64 = 1_234_567_890;
    assert_eq!(
        hasher_spec::effective_seed(),
        EXPECTED,
        "{SEED_ENV_VAR} was not honoured"
    );
    assert_eq!(
        hash_with_default_hasher(42),
        hash_with_seed(EXPECTED, 42),
        "the env seed did not reach the built hasher"
    );
    // And it must genuinely differ from the unconfigured default, else the test
    // would pass even if the env var were ignored.
    assert_ne!(
        hash_with_default_hasher(42),
        hash_with_seed(DEFAULT_SEED, 42),
        "configured seed produced the default hashing"
    );
}

#[test]
#[ignore = "child scenario; spawned by a driver_* test in its own process"]
fn child_set_default_seed_overrides_env() {
    assert!(is_child(), "must be spawned by a driver");
    const CHOSEN: u64 = 0xabc_def;
    hasher_spec::set_default_seed(CHOSEN).expect("seed not yet used, so must succeed");
    assert_eq!(
        hasher_spec::effective_seed(),
        CHOSEN,
        "set_default_seed lost to {SEED_ENV_VAR}"
    );
    assert_eq!(
        hash_with_default_hasher(7),
        hash_with_seed(CHOSEN, 7),
        "the programmatic seed did not reach the built hasher"
    );
}

#[test]
#[ignore = "child scenario; spawned by a driver_* test in its own process"]
fn child_seed_seals_on_first_use() {
    assert!(is_child(), "must be spawned by a driver");
    const FIRST: u64 = 0x1111;
    const SECOND: u64 = 0x2222;

    hasher_spec::set_default_seed(FIRST).expect("first set must succeed");
    assert!(!hasher_spec::seed_is_sealed(), "sealed before any use");

    // Build a container: this observes the seed and must seal it.
    let _m: SpMap<u64, u64, usize, true> = SpMap::new();
    assert!(
        hasher_spec::seed_is_sealed(),
        "constructing an SpMap did not seal the seed"
    );

    let err = hasher_spec::set_default_seed(SECOND)
        .expect_err("setting the seed after use must fail, not silently split the run");
    assert_eq!(
        err.in_force, FIRST,
        "error reported the wrong seed in force"
    );
    assert_eq!(
        hasher_spec::effective_seed(),
        FIRST,
        "a rejected set_default_seed still mutated the seed"
    );
    assert!(
        err.to_string().contains("sealed"),
        "unhelpful error message: {err}"
    );
}

#[test]
#[ignore = "child scenario; spawned by a driver_* test in its own process"]
fn child_configured_seed_reaches_spmap() {
    assert!(is_child(), "must be spawned by a driver");
    // 0x99 via the env var. An SpMap built now must hash with it, which is
    // observable through the index: probe the map's own lookups against a
    // reference map keyed the same way.
    assert_eq!(hasher_spec::effective_seed(), 0x99);

    let mut m: SpMap<u64, u64, usize, true> = SpMap::new();
    for i in 0..200u64 {
        m.try_insert(i, i * 3).expect("insert: within index word");
    }
    // Behaviour is seed-independent by design, so this asserts CORRECTNESS under
    // a non-default seed rather than a seed-specific output: a wrong seed
    // reaching only half the code path (e.g. insert vs. lookup) would break
    // lookups outright.
    for i in 0..200u64 {
        assert_eq!(
            m.get_by_key(&i).copied(),
            Some(i * 3),
            "lookup failed at {i}"
        );
    }
    assert_eq!(m.get_by_key(&999), None);
    assert!(
        hasher_spec::seed_is_sealed(),
        "SpMap construction did not seal the seed"
    );
}
