// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the u8 Tnum shifts against brute-force concretization.
//! The Verus proofs cover all widths; these tests run the executable code
//! (contracts are erased at runtime) on every u8 Tnum and every shift amount.
use semi_persistent_abstract_domains::domains::d8::ExecTnum;

fn has(t: &ExecTnum, c: u8) -> bool {
    c & !t.mask == t.val
}

/// Every well-formed u8 Tnum: each bit is 0, 1 or unknown.
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

#[test]
fn rshi_and_lshi_contain_every_shifted_member() {
    let tnums = all_tnums();
    assert_eq!(tnums.len(), 6561);
    for t in &tnums {
        let members: Vec<u8> = (0..=255u8).filter(|&c| has(t, c)).collect();
        for k in 0..8u32 {
            let r = t.rshi(k);
            let l = t.lshi(k);
            assert_eq!(r.val & r.mask, 0);
            assert_eq!(l.val & l.mask, 0);
            for &c in &members {
                assert!(has(&r, c >> k), "rshi {k} misses {c}");
                assert!(has(&l, c << k), "lshi {k} misses {c}");
            }
        }
    }
}

#[test]
fn shifts_by_one_agree_with_rsh_and_lsh() {
    for t in all_tnums() {
        let (r, r1) = (t.rshi(1), t.rsh());
        let (l, l1) = (t.lshi(1), t.lsh());
        assert_eq!((r.val, r.mask), (r1.val, r1.mask));
        assert_eq!((l.val, l.mask), (l1.val, l1.mask));
    }
}
