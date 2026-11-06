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

/// A deterministic sample of operand pairs, spans thinned so member lists stay short.
fn sample_pairs(seed: u32, n: usize) -> Vec<(ExecAnum, ExecAnum)> {
    let mut s = seed;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        s
    };
    (0..n)
        .map(|_| {
            let (r, q) = (next(), next());
            let a = ExecAnum {
                base: r as u8,
                span: (r >> 8) as u8 & (r >> 24) as u8,
            };
            let b = ExecAnum {
                base: q as u8,
                span: (q >> 8) as u8 & (q >> 24) as u8,
            };
            (a, b)
        })
        .collect()
}

#[test]
fn neg_contains_every_negation() {
    for base in 0..=255u8 {
        for span in 0..=255u8 {
            let a = ExecAnum { base, span };
            let n = a.neg();
            for c in members(&a) {
                assert!(has(&n, c.wrapping_neg()), "-({base}+{span}) misses -{c}");
            }
        }
    }
    let one = ExecAnum::constant(1).neg();
    assert_eq!((one.base, one.span), (255, 0));
}

#[test]
fn not_and_shifts_contain_every_result() {
    for base in 0..=255u8 {
        for span in 0..=255u8 {
            let a = ExecAnum { base, span };
            let ms = members(&a);
            let n = a.bw_not();
            for &c in &ms {
                assert!(has(&n, !c), "!({base}+{span}) misses !{c}");
            }
            for k in [0u32, 1, 3, 7] {
                let (l, r) = (a.lshi(k), a.rshi(k));
                for &c in &ms {
                    assert!(has(&l, c << k), "({base}+{span}) << {k} misses {c}");
                    assert!(has(&r, c >> k), "({base}+{span}) >> {k} misses {c}");
                }
            }
        }
    }
}

#[test]
fn join_and_meet_contain_their_members() {
    for (a, b) in sample_pairs(0x1b87_3593, 20_000) {
        let (j, m) = (a.join(&b), a.meet(&b));
        let mb = members(&b);
        for x in members(&a) {
            assert!(has(&j, x), "join misses {x}");
            if mb.contains(&x) {
                assert!(has(&m, x), "meet misses {x}");
            }
        }
        for &y in &mb {
            assert!(has(&j, y), "join misses {y}");
        }
        let same = a.join(&a);
        assert_eq!((same.base, same.span), (a.base, a.span));
    }
}

#[test]
fn bitwise_and_mul_contain_every_result() {
    for (a, b) in sample_pairs(0x85eb_ca6b, 5_000) {
        let (and, or, xor, mul) = (a.bw_and(&b), a.bw_or(&b), a.bw_xor(&b), a.mul(&b));
        let mb = members(&b);
        for x in members(&a) {
            for &y in &mb {
                assert!(has(&and, x & y), "{x} & {y}");
                assert!(has(&or, x | y), "{x} | {y}");
                assert!(has(&xor, x ^ y), "{x} ^ {y}");
                assert!(has(&mul, x.wrapping_mul(y)), "{x} * {y}");
            }
        }
    }
}

#[test]
fn mul_precise_contains_every_product_and_is_no_looser() {
    let check = |a: ExecAnum, b: ExecAnum| {
        let (mul, precise) = (a.mul(&b), a.mul_precise(&b));
        let mb = members(&b);
        for x in members(&a) {
            for &y in &mb {
                assert!(has(&precise, x.wrapping_mul(y)), "{x} * {y}");
            }
        }
        assert!(
            members(&precise).len() <= members(&mul).len(),
            "({}, {}) * ({}, {})",
            a.base,
            a.span,
            b.base,
            b.span
        );
    };
    for (a, b) in sample_pairs(0x2545_f491, 5_000) {
        check(a, b);
    }
    // Bases and spans below 16, where mul is often top and the Tnum is tighter.
    for b1 in 0..16u8 {
        for s1 in 0..16u8 {
            for b2 in (0..16u8).step_by(3) {
                for s2 in (0..16u8).step_by(3) {
                    check(
                        ExecAnum { base: b1, span: s1 },
                        ExecAnum { base: b2, span: s2 },
                    );
                }
            }
        }
    }
}
