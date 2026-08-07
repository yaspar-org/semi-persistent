// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ported production stress tests: the 100M-element traces from
//! `containers/tests/vec_proptest.rs` (mod stress).
//!
//! Permanently `#[ignore]`d for per-PR CI (migration plan Phase 1.1): run in
//! the nightly/stress CI job via `cargo test --features compat-all -- --ignored
//! --test-threads 1`.
use semi_persistent_containers_verus::{IndexLike, ShrinkPolicy, Tagged, VecI};

semi_persistent_containers_verus::define_id31! {
    pub struct TestId / StoredTestId, "t";
}

// `T: Default` added vs production's helper: verus `restore` requires it
// (the resize-regrow filler — production restore has the same bound on the
// method; its helper only compiled because the bound was deferred).
fn run_stress<T: Tagged + Clone + Default, I: IndexLike + Tagged>(
    n: u32,
    sprinkle: u32,
    frames: u32,
    make_val: fn(u32) -> T,
    get_raw: fn(T) -> u32,
) {
    let mut v: VecI<T, I, true> = VecI::new();
    let zero = make_val(0);
    for _ in 0..n {
        v.push(zero);
    }

    fn xorshift(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    let mut tokens = Vec::new();
    for frame in 1..=frames {
        tokens.push(v.mark(ShrinkPolicy::Never));
        let mut rng = 0xDEAD_BEEF_0000_0000u64 | frame as u64;
        for _ in 0..sprinkle {
            let idx = I::try_from_usize((xorshift(&mut rng) % n as u64) as usize).unwrap();
            v.set(idx, make_val(frame));
        }
    }

    for frame in (1..=frames).rev() {
        let tok = tokens.pop().unwrap();
        v.restore(tok);
        let mut rng = 0xDEAD_BEEF_0000_0000u64 | frame as u64;
        for _ in 0..sprinkle {
            let idx = I::try_from_usize((xorshift(&mut rng) % n as u64) as usize).unwrap();
            let val = get_raw(v.get(idx));
            assert!(val < frame, "frame {frame}: v[?] = {val}");
        }
    }
}

#[test]
#[ignore = "100M-element stress: nightly/stress CI only"]
fn vec_100m_u32_u32() {
    let t = std::time::Instant::now();
    run_stress::<u32, u32>(100_000_000, 100_000, 10, |v| v, |v| v);
    eprintln!("VecI<u32, u32>: {:?}", t.elapsed());
}

#[test]
#[ignore = "100M-element stress: nightly/stress CI only"]
fn vec_100m_dense_id() {
    let t = std::time::Instant::now();
    run_stress::<TestId, u32>(100_000_000, 100_000, 10, TestId::new, |v| v.raw());
    eprintln!("VecI<TestId, u32>: {:?}", t.elapsed());
}
