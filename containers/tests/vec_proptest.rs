// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proptest::prelude::*;
use semi_persistent_containers::{DenseId, IdFactory};
use semi_persistent_containers::{ShrinkPolicy, VecToken};

semi_persistent_containers::define_id31! {
    pub struct TestId / StoredTestId, "t";
}

#[derive(Clone, Debug)]
enum Op {
    Push(u32),
    Set(usize, u32),
    Get(usize),
    Pop,
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        40 => any::<u32>().prop_map(Op::Push),
        30 => (any::<usize>(), any::<u32>()).prop_map(|(i, v)| Op::Set(i, v)),
        20 => any::<usize>().prop_map(Op::Get),
        10 => Just(Op::Pop),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn run_ops(ops: Vec<Op>, mut v: semi_persistent_containers::VecI<u32, u32, true>) {
    let mut oracle: Vec<u32> = Vec::new();
    let mut snapshots: Vec<(VecToken, Vec<u32>)> = Vec::new();

    for op in ops {
        match op {
            Op::Push(val) => {
                v.push(val);
                oracle.push(val);
            }
            Op::Set(idx, val) => {
                if oracle.is_empty() {
                    continue;
                }
                let idx = idx % oracle.len();
                v.set(idx as u32, val);
                oracle[idx] = val;
            }
            Op::Get(idx) => {
                if oracle.is_empty() {
                    continue;
                }
                let idx = idx % oracle.len();
                assert_eq!(v.get(idx as u32), oracle[idx], "get mismatch at {idx}");
            }
            Op::Pop => {
                let got = v.pop();
                let expected = oracle.pop();
                assert_eq!(got, expected, "pop mismatch");
            }
            Op::Mark => {
                if snapshots.len() >= 20 {
                    continue;
                }
                let token = v.mark(ShrinkPolicy::Never);
                snapshots.push((token, oracle.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap) = snapshots[idx].clone();
                v.restore(token);
                oracle = snap;
                snapshots.truncate(idx);
            }
        }
    }

    // Final consistency check.
    let len = oracle.len();
    assert_eq!(v.len(), len as u32, "final len mismatch");
    for (i, expected) in oracle.iter().enumerate() {
        assert_eq!(v.get(i as u32), *expected, "final mismatch at {i}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn vec_inline_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops(ops, semi_persistent_containers::VecI::<u32, u32, true>::new());
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn vec_parallel_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        let v = semi_persistent_containers::VecP::<u32, u32, true>::new();
        let mut oracle: Vec<u32> = Vec::new();
        let mut snapshots: Vec<(VecToken, Vec<u32>)> = Vec::new();
        let mut v = v;

        for op in ops {
            match op {
                Op::Push(val) => {
                    v.push(val);
                    oracle.push(val);
                }
                Op::Set(idx, val) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    v.set(idx as u32, val);
                    oracle[idx] = val;
                }
                Op::Get(idx) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    assert_eq!(v.get(idx as u32), oracle[idx]);
                }
                Op::Pop => {
                    assert_eq!(v.pop(), oracle.pop());
                }
                Op::Mark => {
                    if snapshots.len() >= 20 { continue; }
                    let token = v.mark(ShrinkPolicy::Never);
                    snapshots.push((token, oracle.clone()));
                }
                Op::Restore(idx) => {
                    if snapshots.is_empty() { continue; }
                    let idx = idx % snapshots.len();
                    let (token, snap) = snapshots[idx].clone();
                    v.restore(token);
                    oracle = snap;
                    snapshots.truncate(idx);
                }
            }
        }

        let len = oracle.len();
        assert_eq!(v.len(), len as u32);
        for (i, expected) in oracle.iter().enumerate() {
            assert_eq!(v.get(i as u32), *expected);
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn vec_dense_id_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        // VecI storing TestId values, indexed by u32 (TestId::Index)
        let mut v = semi_persistent_containers::VecI::<TestId, u32, true>::new();
        let mut oracle: Vec<TestId> = Vec::new();
        let mut snapshots: Vec<(VecToken, Vec<TestId>)> = Vec::new();
        let mut factory = IdFactory::<TestId>::new();

        for op in ops {
            match op {
                Op::Push(_) => {
                    if let Some(id) = factory.try_alloc() {
                        v.push(id);
                        oracle.push(id);
                    }
                }
                Op::Set(idx, raw) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    let val = TestId::from_usize(raw as usize % factory.count().max(1));
                    v.set(idx as u32, val);
                    oracle[idx] = val;
                }
                Op::Get(idx) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    assert_eq!(v.get(idx as u32), oracle[idx]);
                }
                Op::Pop => {
                    assert_eq!(v.pop(), oracle.pop());
                }
                Op::Mark => {
                    if snapshots.len() >= 20 { continue; }
                    let token = v.mark(ShrinkPolicy::Never);
                    snapshots.push((token, oracle.clone()));
                }
                Op::Restore(idx) => {
                    if snapshots.is_empty() { continue; }
                    let idx = idx % snapshots.len();
                    let (token, snap) = snapshots[idx].clone();
                    v.restore(token);
                    oracle = snap;
                    snapshots.truncate(idx);
                }
            }
        }

        let len = oracle.len();
        assert_eq!(v.len(), len as u32);
        for (i, expected) in oracle.iter().enumerate() {
            assert_eq!(v.get(i as u32), *expected);
        }
    }
}

#[cfg(test)]
mod stress {
    use super::TestId;
    use semi_persistent_containers::{ShrinkPolicy, VecI};

    fn run_stress<
        T: semi_persistent_containers::Tagged + Clone + Default,
        I: semi_persistent_containers::IndexLike + semi_persistent_containers::Tagged,
    >(
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
    fn vec_100m_u32_u32() {
        let t = std::time::Instant::now();
        run_stress::<u32, u32>(100_000_000, 100_000, 10, |v| v, |v| v);
        eprintln!("VecI<u32, u32>: {:?}", t.elapsed());
    }

    #[test]
    fn vec_100m_dense_id() {
        let t = std::time::Instant::now();
        run_stress::<TestId, u32>(100_000_000, 100_000, 10, TestId::new, |v| v.raw());
        eprintln!("VecI<TestId, u32>: {:?}", t.elapsed());
    }
}
