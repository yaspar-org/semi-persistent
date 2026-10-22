// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the u8 Tnum `neg` and `sub` against brute-force
//! concretization.
use semi_persistent_abstract_domains::domains::d8::ExecTnum;

fn has(t: &ExecTnum, c: u8) -> bool {
    c & !t.mask == t.val
}

fn all_tnums() -> Vec<ExecTnum> {
    let mut out = Vec::new();
    for mask in 0..=255u8 {
        for val in 0..=255u8 {
            if val & mask == 0 {
                out.push(ExecTnum { val, mask });
            }
        }
    }
    out
}

fn members(t: &ExecTnum) -> Vec<u8> {
    (0..=255u8).filter(|&c| has(t, c)).collect()
}

#[test]
fn neg_contains_every_negation() {
    for t in all_tnums() {
        let r = t.neg();
        assert_eq!(r.val & r.mask, 0);
        for c in members(&t) {
            assert!(has(&r, c.wrapping_neg()), "neg misses -{c}");
        }
    }
}

#[test]
fn sub_contains_every_difference() {
    let tnums = all_tnums();
    // Every Tnum on the left against a stride of Tnums on the right.
    for a in &tnums {
        let ma = members(a);
        for b in tnums.iter().step_by(97) {
            let r = a.sub(b);
            assert_eq!(r.val & r.mask, 0);
            for &x in &ma {
                for y in members(b) {
                    assert!(has(&r, x.wrapping_sub(y)), "{x} - {y}");
                }
            }
        }
    }
}

#[test]
fn mul_contains_every_product() {
    let tnums = all_tnums();
    for a in tnums.iter().step_by(7) {
        let ma = members(a);
        for b in tnums.iter().step_by(11) {
            let r = a.mul(b);
            assert_eq!(r.val & r.mask, 0);
            for &x in &ma {
                for y in members(b) {
                    assert!(has(&r, x.wrapping_mul(y)), "{x} * {y}");
                }
            }
        }
    }
}
