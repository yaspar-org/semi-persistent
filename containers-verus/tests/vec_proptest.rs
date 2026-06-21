// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime property tests for the semi-persistent `Vec` family (`Vec` +
//! `AppendOnlyVec`).
//!
//! Verus proves these correct; `cargo test` erases the `requires`/`ensures`/
//! `proof` and runs the *executable* bodies, so these tests confirm the
//! compiled code actually runs and matches a plain-`std` oracle. The headline
//! property is semi-persistence: `mark()` then mutate then `restore(token)`
//! rolls the view back to the snapshot taken at the mark — exercised here
//! against a stack of oracle snapshots.

use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;
use semi_persistent_containers_verus::parallel_store::ParallelStore;
use semi_persistent_containers_verus::vec::{ShrinkPolicy, Vec as SpVec};

// Untracked instantiation over the ParallelStore backend (the tracked path is
// exercised by `rollback_stress::<true>`).
type VecU = SpVec<u32, u32, ParallelStore<u32, u32>, false>;

// Reproducible pseudo-random stream (no rand dep; fixed seed = debuggable).
struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 17
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() as usize) % n
    }
}

// --------------------------------------------------------------------------
// Vec: push/pop/set/get/len vs a std::Vec oracle, interleaved with mark/restore.
// --------------------------------------------------------------------------

fn read_back(v: &VecU) -> Vec<u32> {
    let n = v.len() as usize;
    (0..n).map(|i| v.get(i as u32)).collect()
}

#[test]
fn vec_ops_match_oracle() {
    for seed in 0..16u64 {
        let mut v = VecU::new();
        let mut oracle: Vec<u32> = Vec::new();
        let mut rng = Lcg::new(seed ^ 0xA11CE);

        for step in 0..2000 {
            // Bias toward push so the vector grows; sprinkle pop/set.
            match rng.below(10) {
                0..=5 => {
                    let val = rng.next() as u32;
                    v.push(val);
                    oracle.push(val);
                }
                6..=7 => {
                    let got = v.pop();
                    let want = oracle.pop();
                    assert_eq!(got, want, "seed={seed} step={step}: pop mismatch");
                }
                _ => {
                    if !oracle.is_empty() {
                        let i = rng.below(oracle.len());
                        let val = rng.next() as u32;
                        v.set(i as u32, val);
                        oracle[i] = val;
                    }
                }
            }
            assert_eq!(
                v.len() as usize,
                oracle.len(),
                "seed={seed} step={step}: len mismatch"
            );
            assert_eq!(v.is_empty(), oracle.is_empty());
        }
        assert_eq!(read_back(&v), oracle, "seed={seed}: final contents mismatch");
    }
    println!("vec_ops_match_oracle: OK");
}

// --------------------------------------------------------------------------
// Semi-persistence: a stack of marks; mutate freely; restore in LIFO order and
// confirm each restore reproduces the oracle snapshot captured at that mark.
// This is the property the whole crate exists for, run on the untracked and
// the tracked backend (the observational guarantee is identical — task #41).
// --------------------------------------------------------------------------

#[test]
fn vec_mark_restore_untracked() {
    rollback_stress::<false>(0xBEEF);
}

#[test]
fn vec_mark_restore_tracked() {
    rollback_stress::<true>(0xCAFE);
}

fn rollback_stress<const TRACK: bool>(seed: u64) {
    // Generic over TRACK so we exercise both the diff-log and the
    // snapshot-copy reconstruction paths through the same script.
    let mut v = SpVec::<u32, u32, ParallelStore<u32, u32>, TRACK>::new();
    let mut oracle: Vec<u32> = Vec::new();
    let mut rng = Lcg::new(seed);

    // (token, snapshot-of-oracle-at-mark) pairs, LIFO.
    let mut frames: Vec<(_, Vec<u32>)> = Vec::new();

    for _ in 0..40 {
        // Grow a bit.
        for _ in 0..rng.below(8) {
            let val = rng.next() as u32;
            v.push(val);
            oracle.push(val);
        }
        // Mark: snapshot the oracle alongside the token.
        let token = v.mark(ShrinkPolicy::Never);
        frames.push((token, oracle.clone()));

        // Mutate past the mark (push/pop/set), so restore has real work to undo.
        for _ in 0..rng.below(12) {
            match rng.below(3) {
                0 => {
                    let val = rng.next() as u32;
                    v.push(val);
                    oracle.push(val);
                }
                1 => {
                    v.pop();
                    oracle.pop();
                }
                _ => {
                    if !oracle.is_empty() {
                        let i = rng.below(oracle.len());
                        let val = rng.next() as u32;
                        v.set(i as u32, val);
                        oracle[i] = val;
                    }
                }
            }
        }

        // Occasionally unwind some frames and verify each rollback.
        if rng.below(2) == 0 {
            while let Some((tok, snap)) = frames.pop() {
                v.restore(tok);
                oracle = snap.clone();
                let got: Vec<u32> = (0..v.len() as usize).map(|i| v.get(i as u32)).collect();
                assert_eq!(
                    got, snap,
                    "TRACK={TRACK}: restore did not reproduce the marked snapshot"
                );
                if rng.below(2) == 0 {
                    break; // leave some frames for a later unwind
                }
            }
        }
    }

    // Final full unwind.
    while let Some((tok, snap)) = frames.pop() {
        v.restore(tok);
        let got: Vec<u32> = (0..v.len() as usize).map(|i| v.get(i as u32)).collect();
        assert_eq!(got, snap, "TRACK={TRACK}: final unwind mismatch");
    }
    println!("rollback_stress<TRACK={TRACK}>: OK");
}

// --------------------------------------------------------------------------
// AppendOnlyVec: push (returns a stable index) / get / len, plus mark/restore.
// Oracle: a plain Vec, push-only; restore truncates back to the marked length.
// --------------------------------------------------------------------------

#[test]
fn append_only_vec_ops_and_rollback() {
    for seed in 0..12u64 {
        let mut a = AppendOnlyVec::<u64, false>::new();
        let mut oracle: Vec<u64> = Vec::new();
        let mut rng = Lcg::new(seed ^ 0x5151);
        let mut frames: Vec<(_, Vec<u64>)> = Vec::new();

        for _ in 0..300 {
            match rng.below(10) {
                0 => {
                    let token = a.mark(ShrinkPolicy::Never);
                    frames.push((token, oracle.clone()));
                }
                1 if !frames.is_empty() => {
                    let (tok, snap) = frames.pop().unwrap();
                    a.restore(tok);
                    oracle = snap;
                }
                _ => {
                    let val = rng.next();
                    let idx = a.push(val);
                    assert_eq!(idx, oracle.len(), "seed={seed}: push index mismatch");
                    oracle.push(val);
                }
            }
            // length and a random read agree with the oracle.
            assert_eq!(a.len(), oracle.len(), "seed={seed}: len mismatch");
            if !oracle.is_empty() {
                let i = rng.below(oracle.len());
                assert_eq!(*a.get(i), oracle[i], "seed={seed}: get({i}) mismatch");
            }
        }
        println!("append_only_vec seed={seed}: OK ({} entries)", oracle.len());
    }
}
