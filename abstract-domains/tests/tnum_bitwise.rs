// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the u8 Tnum `bw_not` and `bw_and_not` against brute-force
//! concretization, and against their former encodings through `bw_xor` and
//! `bw_and`.
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

fn same(a: &ExecTnum, b: &ExecTnum) -> bool {
    a.val == b.val && a.mask == b.mask
}

#[test]
fn bw_not_contains_every_complement_and_matches_xor_with_ones() {
    let ones = ExecTnum::constant(u8::MAX);
    for t in all_tnums() {
        let r = t.bw_not();
        assert!(same(&r, &t.bw_xor(&ones)));
        for c in (0..=255u8).filter(|&c| has(&t, c)) {
            assert!(has(&r, !c), "bw_not misses !{c}");
        }
    }
}

#[test]
fn bw_and_not_matches_and_with_not() {
    let tnums = all_tnums();
    for a in &tnums {
        for b in &tnums {
            assert!(same(&a.bw_and_not(b), &a.bw_and(&b.bw_not())));
        }
    }
}

#[test]
fn bw_and_not_contains_every_member_pair() {
    let tnums = all_tnums();
    // Every Tnum on the left against a stride of Tnums on the right.
    for a in &tnums {
        let ma: Vec<u8> = (0..=255u8).filter(|&c| has(a, c)).collect();
        for b in tnums.iter().step_by(97) {
            let r = a.bw_and_not(b);
            for &x in &ma {
                for y in (0..=255u8).filter(|&c| has(b, c)) {
                    assert!(has(&r, x & !y), "{x} & !{y}");
                }
            }
        }
    }
}
