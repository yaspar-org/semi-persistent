// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the u8 Anum against brute-force concretization. The
//! Verus proofs cover all widths; these tests run the executable code
//! (contracts are erased at runtime).
use semi_persistent_abstract_domains::domains::d8::{ExecAnum, ExecTnum};

fn has(a: &ExecAnum, c: u8) -> bool {
    c >= a.base && (c - a.base) & !a.span == 0
}

fn members(a: &ExecAnum) -> Vec<u8> {
    (0..=255u8).filter(|&c| has(a, c)).collect()
}

#[test]
fn ones_mask_is_the_least_all_ones_at_or_above() {
    for n in 0..=255u8 {
        let want = if n == 0 {
            0
        } else {
            u8::MAX >> n.leading_zeros()
        };
        assert_eq!(ExecAnum::ones_mask(n), want, "ones_mask({n})");
    }
}

#[test]
fn div_const_contains_every_quotient() {
    for base in 0..=255u8 {
        for span in 0..=255u8 {
            let a = ExecAnum { base, span };
            let ms = members(&a);
            for d in [1u8, 2, 3, 7, 16, 255] {
                let q = a.div_const(d);
                for &c in &ms {
                    assert!(has(&q, c / d), "{base}+{span} / {d} misses {c}");
                }
            }
        }
    }
}

#[test]
fn add_contains_every_sum() {
    // A deterministic sample of operand pairs; every member pair is checked.
    let mut s: u32 = 0x9e37_79b9;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        s
    };
    for _ in 0..20_000 {
        let r = next();
        let a = ExecAnum {
            base: r as u8,
            span: (r >> 8) as u8 & (r >> 24) as u8,
        };
        let b = ExecAnum {
            base: (r >> 16) as u8,
            span: (r >> 4) as u8 & (r >> 12) as u8,
        };
        let sum = a.add(&b);
        for x in members(&a) {
            for y in members(&b) {
                assert!(has(&sum, x.wrapping_add(y)), "{x} + {y}");
            }
        }
    }
}

#[test]
fn from_etn_keeps_every_member() {
    for mask in 0..=255u8 {
        for val in (0..=255u8).filter(|v| v & mask == 0) {
            let t = ExecTnum { val, mask };
            let a = ExecAnum::from_etn(&t);
            for c in (0..=255u8).filter(|&c| c & !mask == val) {
                assert!(has(&a, c), "from_etn({val}, {mask}) misses {c}");
            }
        }
    }
}

/// to_etn must carry the base into the span: Anum(1, 1) is {1, 2}, which the
/// former `(base & !span, span)` encoding gave as {0, 1}.
#[test]
fn to_etn_keeps_every_member() {
    let tn_has = |t: &ExecTnum, c: u8| c & !t.mask == t.val;
    for base in 0..=255u8 {
        for span in 0..=255u8 {
            let a = ExecAnum { base, span };
            let t = a.to_etn();
            assert_eq!(t.val & t.mask, 0);
            for c in members(&a) {
                assert!(tn_has(&t, c), "to_etn({base}, {span}) misses {c}");
            }
        }
    }
}

#[test]
fn sub_contains_every_difference() {
    // A deterministic sample of operand pairs; every member pair is checked.
    let mut s: u32 = 0x2545_f491;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        s
    };
    for _ in 0..20_000 {
        let r = next();
        let a = ExecAnum {
            base: r as u8,
            span: (r >> 8) as u8 & (r >> 24) as u8,
        };
        let b = ExecAnum {
            base: (r >> 16) as u8 & 0x3f,
            span: (r >> 4) as u8 & (r >> 12) as u8 & 0x1f,
        };
        let diff = a.sub(&b);
        for x in members(&a) {
            for y in members(&b) {
                assert!(has(&diff, x.wrapping_sub(y)), "{x} - {y}");
            }
        }
    }
}
