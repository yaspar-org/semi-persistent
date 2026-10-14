// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive oracle for the real executable Congruence<u8>.
use semi_persistent_abstract_domains::congruence::Congruence;
use std::collections::HashMap;

type C = Congruence<u8>;

fn check_wf(c: &C) {
    let (m, r) = c.parts();
    assert!(m == 0 || (r < m && u16::from(r) + u16::from(m) <= 255));
    assert!(c.contains(r));
}

// Enumerate the raw progression using widened arithmetic, independently of
// the implementation's remainder-based membership check.
fn oracle(m: u8, r: u8) -> [u64; 4] {
    let mut bits = [0; 4];
    let mut x = if m == 0 {
        u16::from(r)
    } else {
        u16::from(r % m)
    };
    loop {
        bits[usize::from(x / 64)] |= 1u64 << (x % 64);
        if m == 0 {
            break;
        }
        x += u16::from(m);
        if x > 255 {
            break;
        }
    }
    bits
}

#[test]
fn constants_and_top() {
    let top = C::top();
    check_wf(&top);
    assert_eq!(top.parts(), (1, 0));
    for r in 0..=u8::MAX {
        let c = C::constant(r);
        check_wf(&c);
        assert_eq!(c.parts(), (0, r));
        for x in 0..=u8::MAX {
            assert_eq!(c.contains(x), x == r);
            assert!(top.contains(x));
        }
    }
}

#[test]
fn exhaustive_raw_inputs_membership_normalization_and_canonicity() {
    let mut representatives = HashMap::new();
    for m in 0..=u8::MAX {
        for r in 0..=u8::MAX {
            let c = C::new(m, r);
            check_wf(&c);
            let expected = oracle(m, r);
            let normalized = c.normalize();
            assert_eq!(normalized.parts(), c.parts());
            let reconstructed = C::new(c.parts().0, c.parts().1);
            assert_eq!(reconstructed.parts(), c.parts());
            let mut actual = [0u64; 4];
            for x in 0..=u8::MAX {
                let has = c.contains(x);
                assert_eq!(
                    has,
                    expected[usize::from(x / 64)] & (1u64 << (x % 64)) != 0,
                    "m={m}, r={r}, x={x}"
                );
                assert_eq!(normalized.contains(x), has);
                if has {
                    actual[usize::from(x / 64)] |= 1u64 << (x % 64);
                }
            }
            // Every canonical representation is reached by its own raw pair.
            // Identical sets must always yield identical canonical pairs.
            if let Some(previous) = representatives.insert(actual, c.parts()) {
                assert_eq!(previous, c.parts(), "duplicate gamma for m={m}, r={r}");
            }
        }
    }
    // 256 singletons + sum(min(m, 256-m), m=1..255) progressions.
    assert_eq!(representatives.len(), 16_640);
}

#[test]
fn finite_width_singleton_and_second_member_boundary() {
    assert_eq!(C::new(201, 200).parts(), C::constant(200).parts());
    assert_eq!(C::new(128, 127).parts(), (128, 127));
    assert!(C::new(128, 127).contains(255));
    assert_eq!(C::new(129, 127).parts(), (0, 127));
    assert_eq!(C::new(255, 0).parts(), (255, 0));
    assert!(C::new(255, 0).contains(255));
    assert_eq!(C::new(255, 255).parts(), (255, 0));
    assert_eq!(C::new(4, 5).parts(), (4, 1));
    assert_eq!(C::new(1, 255).parts(), C::top().parts());
}

#[test]
fn generic_widths_and_legacy_aliases() {
    macro_rules! check {
        ($word:ty, $legacy:ty) => {{
            let c = Congruence::<$word>::new(<$word>::MAX, <$word>::MAX - 1);
            assert_eq!(c.parts(), (0, <$word>::MAX - 1));
            let c: $legacy = Congruence::<$word>::new(<$word>::MAX, 0);
            assert!(c.contains(0));
            assert!(c.contains(<$word>::MAX));
            assert!(!c.contains(1));
        }};
    }
    use semi_persistent_abstract_domains::domains::{d8, d16, d32, d64};
    check!(u8, d8::Congruence);
    check!(u16, d16::Congruence);
    check!(u32, d32::Congruence);
    check!(u64, d64::Congruence);
}
