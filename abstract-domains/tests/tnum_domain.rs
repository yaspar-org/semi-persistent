// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of `ExecTnum` as a `Domain`, `Canonical` and `Refine`
//! domain, against brute-force concretization at u8: every well-formed Tnum
//! for the single-value checks, and sampled pairs for the binary ones.
use semi_persistent_abstract_domains::domains::d8::ExecTnum;
use semi_persistent_abstract_domains::facts::Facts;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::reduce::{Product, REDUCE_FUEL, Refine};
use std::collections::HashMap;

/// A set of u8 values as a 256-bit mask.
type Set = [u128; 2];

fn has(t: &ExecTnum, x: u8) -> bool {
    x & !t.mask == t.val
}

fn set(t: &ExecTnum) -> Set {
    let mut s = [0u128; 2];
    for x in 0..=255u8 {
        if has(t, x) {
            s[(x >> 7) as usize] |= 1 << (x & 127);
        }
    }
    s
}

fn bot_set(b: &BotOr<ExecTnum>) -> Set {
    match b {
        BotOr::Bot => [0, 0],
        BotOr::Val(t) => set(t),
    }
}

fn subset(a: Set, b: Set) -> bool {
    a[0] & !b[0] == 0 && a[1] & !b[1] == 0
}

fn and(a: Set, b: Set) -> Set {
    [a[0] & b[0], a[1] & b[1]]
}

/// The best Tnum of a nonempty set: known where every member agrees.
fn alpha(s: Set) -> ExecTnum {
    let (mut all, mut any) = (0xffu8, 0u8);
    for x in 0..=255u8 {
        if s[(x >> 7) as usize] >> (x & 127) & 1 == 1 {
            all &= x;
            any |= x;
        }
    }
    ExecTnum {
        val: all,
        mask: any ^ all,
    }
}

/// Every well-formed u8 Tnum: val and mask disjoint.
fn all_tnums() -> Vec<ExecTnum> {
    let mut out = Vec::new();
    for val in 0..=255u8 {
        for mask in 0..=255u8 {
            if val & mask == 0 {
                out.push(ExecTnum { val, mask });
            }
        }
    }
    out
}

fn samples() -> Vec<ExecTnum> {
    all_tnums().into_iter().step_by(13).collect()
}

#[test]
fn every_tnum_is_nonempty_canonical_and_exports_its_bounds() {
    let all = all_tnums();
    assert_eq!(all.len(), 6561);
    let mut seen: HashMap<Set, (u8, u8)> = HashMap::new();
    for t in &all {
        let s = set(t);
        assert!(s != [0, 0], "empty Tnum ({}, {})", t.val, t.mask);
        if let Some(prev) = seen.insert(s, (t.val, t.mask)) {
            panic!("({}, {}) and {:?} denote the same set", t.val, t.mask, prev);
        }
        let BotOr::Val(f) = t.to_channel() else {
            panic!("a Tnum exports facts")
        };
        let (lo, hi) = f.interval().bounds();
        assert_eq!(
            (lo, hi),
            (t.val, t.val | t.mask),
            "bounds of ({}, {})",
            t.val,
            t.mask
        );
        assert!((0..=255u8).all(|x| !has(t, x) || (lo <= x && x <= hi)));
    }
}

#[test]
fn sampled_pairs_leq_join_meet_widen_against_sets() {
    let s = samples();
    let mut bots = 0usize;
    for a in &s {
        let sa = set(a);
        for b in &s {
            let sb = set(b);
            assert_eq!(
                Domain::leq(a, b),
                subset(sa, sb),
                "leq ({}, {}) ({}, {})",
                a.val,
                a.mask,
                b.val,
                b.mask
            );

            let j = Domain::join(a, b);
            let union = [sa[0] | sb[0], sa[1] | sb[1]];
            let best = alpha(union);
            assert_eq!(
                (j.val, j.mask),
                (best.val, best.mask),
                "join is the best Tnum of the union"
            );
            let w = Domain::widen(a, b);
            assert_eq!((w.val, w.mask), (j.val, j.mask));

            let m = a.meet(b);
            assert_eq!(
                bot_set(&m),
                and(sa, sb),
                "meet ({}, {}) ({}, {})",
                a.val,
                a.mask,
                b.val,
                b.mask
            );
            if let BotOr::Bot = m {
                bots += 1;
            }
        }
    }
    assert!(bots > 0, "the samples include conflicting pairs");
}

#[test]
fn refine_keeps_exactly_the_members_in_the_interval_hull() {
    let pts: Vec<u8> = (0..=255u16)
        .step_by(17)
        .map(|v| v as u8)
        .chain([1, 254, 255])
        .collect();
    for t in samples() {
        for &lo in &pts {
            for &hi in &pts {
                if lo > hi {
                    continue;
                }
                let f = Facts::from_interval(Interval::new(lo, hi).unwrap());
                let r = t.refine(&f);
                let sr = bot_set(&r);
                for x in 0..=255u8 {
                    let in_r = sr[(x >> 7) as usize] >> (x & 127) & 1 == 1;
                    if has(&t, x) && lo <= x && x <= hi {
                        assert!(
                            in_r,
                            "refine dropped {x} from ({}, {}) by [{lo}, {hi}]",
                            t.val, t.mask
                        );
                    }
                    if in_r {
                        assert!(has(&t, x), "refine added {x} to ({}, {})", t.val, t.mask);
                    }
                }
            }
        }
    }
}

#[test]
fn product_with_interval_reduces_both_ways() {
    // {129, 131, 133, 135} and [0, 130]: the Tnum raises the interval to
    // [129, 130], whose common prefix 1000_00 leaves {129, 131} in the Tnum.
    let p = Product {
        a: Interval::new(0u8, 130).unwrap(),
        b: ExecTnum {
            val: 0b1000_0001,
            mask: 0b0000_0110,
        },
    };
    let BotOr::Val(r) = p.reduce(REDUCE_FUEL) else {
        panic!("129 is a common member")
    };
    assert_eq!(r.a.bounds(), (129, 130));
    assert_eq!((r.b.val, r.b.mask), (129, 2));

    // {2, 3} and [4, 9]: no common member.
    let q = Product {
        a: Interval::new(4u8, 9).unwrap(),
        b: ExecTnum { val: 2, mask: 1 },
    };
    assert!(matches!(q.reduce(REDUCE_FUEL), BotOr::Bot));
}
