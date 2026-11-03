// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the `Facts` congruence field and the grid step of
//! `normalize` (src/facts.rs) against concrete u8 sets, and boundary cases at
//! u128.
use semi_persistent_abstract_domains::congruence::Congruence;
use semi_persistent_abstract_domains::facts::Facts;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::reduce::{Channel, Refine};
use std::collections::HashMap;

type F8 = Facts<u8>;
type Set8 = [bool; 256];
/// A record's fields: interval bounds and congruence `(modulus, residue)`.
type Repr = ((u8, u8), (u8, u8));

fn bot<D>(b: BotOr<D>) -> Option<D> {
    match b {
        BotOr::Bot => None,
        BotOr::Val(d) => Some(d),
    }
}

fn has(f: &F8, x: u8) -> bool {
    let (lo, hi) = f.interval().bounds();
    lo <= x && x <= hi && f.congruence().contains(x)
}

fn set_of(f: &F8) -> Set8 {
    std::array::from_fn(|z| has(f, z as u8))
}

fn repr(f: &F8) -> Repr {
    (f.interval().bounds(), f.congruence().parts())
}

/// Bounds near the ends of the range, around small moduli and the sign bit.
const PTS: [u8; 17] = [
    0, 1, 2, 3, 7, 8, 9, 10, 11, 100, 127, 128, 129, 250, 253, 254, 255,
];

fn intervals() -> Vec<Interval<u8>> {
    let mut out = Vec::new();
    for &a in &PTS {
        for &b in &PTS {
            if a <= b {
                out.push(Interval::new(a, b).unwrap());
            }
        }
    }
    out
}

/// Constants at the bounds above, every class with modulus up to 20, and a
/// few large moduli where the class has two or three members.
fn congruences() -> Vec<Congruence<u8>> {
    let mut out: Vec<_> = PTS.iter().map(|&v| Congruence::constant(v)).collect();
    for m in (1..=20u8).chain([100, 127, 128, 200, 255]) {
        for r in 0..m {
            out.push(Congruence::new(m, r));
        }
    }
    out
}

/// `from_parts` is exact, and its result is reduced: the bounds are the least
/// and greatest members, a single member is a constant congruence, and equal
/// sets get equal records.
#[test]
fn from_parts_is_exact_and_canonical() {
    let mut seen: HashMap<Set8, Repr> = HashMap::new();
    let (us, cs) = (intervals(), congruences());
    let mut nonempty = 0;
    for u in &us {
        for c in &cs {
            let (lo, hi) = u.bounds();
            let want: Set8 = std::array::from_fn(|z| {
                let x = z as u8;
                lo <= x && x <= hi && c.contains(x)
            });
            match bot(Facts::from_parts(u.dup(), c.dup())) {
                None => assert!(want.iter().all(|&w| !w), "{:?} {:?}", u.bounds(), c.parts()),
                Some(f) => {
                    assert_eq!(set_of(&f), want, "{:?} {:?}", u.bounds(), c.parts());
                    let (flo, fhi) = f.interval().bounds();
                    assert!(want[flo as usize] && want[fhi as usize]);
                    assert!(want[..flo as usize].iter().all(|&w| !w));
                    assert!(want[fhi as usize + 1..].iter().all(|&w| !w));
                    if flo == fhi {
                        assert_eq!(f.congruence().parts(), (0, flo));
                    }
                    let r = repr(&f);
                    assert_eq!(*seen.entry(want).or_insert(r), r, "two records for one set");
                    // A normalized record is a fixpoint of `normalize`.
                    let g = bot(f.normalize()).expect("nonempty");
                    assert_eq!(repr(&g), r);
                    nonempty += 1;
                }
            }
        }
    }
    assert_eq!(us.len(), 153);
    assert!(nonempty > 0 && seen.len() > 1);
}

/// The worked examples of doc/reduced-product.md, and the empty grid
/// intersection from the #129 review.
#[test]
fn grid_step_examples() {
    let f = |lo, hi, m, r| {
        bot(Facts::from_parts(
            Interval::new(lo, hi).unwrap(),
            Congruence::new(m, r),
        ))
    };
    // [3, 10] and 4Z+3: 10 rounds down to 7.
    assert_eq!(f(3u8, 10, 4, 3).map(|f| repr(&f)), Some(((3, 7), (4, 3))));
    // [10, 11] and 4Z+1: 10 rounds up to 13, 11 down to 9, so empty.
    assert!(f(10u8, 11, 4, 1).is_none());
    // [8, 9] and 4Z+3: no member of 4Z+3 lies in [8, 9].
    assert!(f(8u8, 9, 4, 3).is_none());
    // [5, 9] and 4Z+3: one member left, so the congruence becomes constant.
    assert_eq!(f(5u8, 9, 4, 3).map(|f| repr(&f)), Some(((7, 7), (0, 7))));
    // A constant congruence collapses the interval to it.
    assert_eq!(
        f(0u8, 255, 0, 42).map(|f| repr(&f)),
        Some(((42, 42), (0, 42)))
    );
    // A singleton interval makes the congruence constant on its own.
    let s = Facts::from_interval(Interval::constant(9u8));
    assert_eq!(repr(&s), ((9, 9), (0, 9)));
}

/// Records over every class with modulus up to 6 and a few bounds: meet and
/// refine are exact, join and widen cover both operands, and `leq` is sound.
#[test]
fn lattice_operations_against_sets() {
    let pts = [0u8, 3, 4, 9, 128, 255];
    let mut recs: Vec<F8> = Vec::new();
    for &a in &pts {
        for &b in &pts {
            if a > b {
                continue;
            }
            for m in 0..=6u8 {
                for r in 0..m.max(1) {
                    let c = if m == 0 {
                        Congruence::constant(a)
                    } else {
                        Congruence::new(m, r)
                    };
                    if let Some(f) = bot(Facts::from_parts(Interval::new(a, b).unwrap(), c)) {
                        recs.push(f);
                    }
                }
            }
        }
    }
    for a in &recs {
        let sa = set_of(a);
        for b in &recs {
            let sb = set_of(b);
            let want: Set8 = std::array::from_fn(|z| sa[z] && sb[z]);
            for r in [bot(a.meet_exact(b)), bot(a.meet(b)), bot(a.refine(b))] {
                match r {
                    None => assert!(want.iter().all(|&w| !w)),
                    Some(m) => assert_eq!(set_of(&m), want),
                }
            }
            for j in [a.join(b), a.widen(b)] {
                let sj = set_of(&j);
                assert!((0..256).all(|z| !(sa[z] || sb[z]) || sj[z]));
            }
            if a.leq(b) {
                assert!((0..256).all(|z| !sa[z] || sb[z]));
            }
        }
    }
}

#[test]
fn grid_step_at_u128_boundaries() {
    const MAX: u128 = u128::MAX;
    let f = |lo, hi, m, r| {
        bot(Facts::from_parts(
            Interval::new(lo, hi).unwrap(),
            Congruence::new(m, r),
        ))
        .map(|f| (f.interval().bounds(), f.congruence().parts()))
    };
    // MAX is odd: the even members of [MAX - 3, MAX] are MAX - 3 and MAX - 1.
    assert_eq!(f(MAX - 3, MAX, 2, 0), Some(((MAX - 3, MAX - 1), (2, 0))));
    assert_eq!(f(MAX - 3, MAX, 2, 1), Some(((MAX - 2, MAX), (2, 1))));
    // Rounding up past MAX means empty.
    assert_eq!(f(MAX, MAX, 2, 0), None);
    assert_eq!(f(MAX - 1, MAX, 4, 1), None);
    // Rounding down below 0 means empty.
    assert_eq!(f(0, 2, 8, 5), None);
    // Modulus 2^127, residue 3: members 3 and 2^127 + 3.
    let half = 1u128 << 127;
    assert_eq!(f(0, MAX, half, 3), Some(((3, half + 3), (half, 3))));
    assert_eq!(
        f(4, MAX, half, 3),
        Some(((half + 3, half + 3), (0, half + 3)))
    );
    // Top congruence leaves the interval unchanged.
    assert_eq!(f(5, MAX, 1, 0), Some(((5, MAX), (1, 0))));
    let t = Facts::<u128>::top();
    assert_eq!(t.interval().bounds(), (0, MAX));
    assert!(t.congruence().is_top());
}
