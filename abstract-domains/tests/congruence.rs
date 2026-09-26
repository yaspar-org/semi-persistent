// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

macro_rules! core_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::domains::$domain::Congruence;
            let max = <$uint>::MAX;
            let top = Congruence::top();
            for x in [0, 1, max] {
                let singleton = Congruence::constant(x);
                assert!(singleton.contains(x));
                assert!(!singleton.contains(x.wrapping_add(1)));
                assert!(singleton.refines(&top));
                assert!(!top.refines(&singleton));
            }
            let even = Congruence { modulus: 2, residue: 0 };
            let odd = Congruence { modulus: 2, residue: 1 };
            let four = Congruence { modulus: 4, residue: 0 };
            assert!(four.refines(&even));
            assert!(!even.refines(&four));
            assert!(!even.refines(&odd));
            assert!(even.refines(&even));

            let finite_singleton = Congruence { modulus: max, residue: 1 };
            assert!(finite_singleton.refines(&Congruence::constant(1)));
            assert!(Congruence::constant(1).refines(&finite_singleton));
            assert!(finite_singleton.refines(&odd));
            let two_values = Congruence { modulus: max, residue: 0 };
            assert!(!two_values.refines(&Congruence::constant(0)));
            assert!(!two_values.refines(&even));

            for m in [0, 1, 2, max] {
                for r in [0, 1, max] {
                    let normalized = Congruence { modulus: m, residue: r }.normalize();
                    assert_eq!(normalized.modulus, m);
                    assert_eq!(normalized.residue, if m == 0 { r } else { r % m });
                    let twice = normalized.normalize();
                    assert_eq!((twice.modulus, twice.residue), (normalized.modulus, normalized.residue));
                    for x in [0, 1, 2, max - 1, max] {
                        assert_eq!(normalized.contains(x), if m == 0 { x == r } else { x % m == r % m });
                    }
                }
            }
        }
    };
}

core_cases!(core_u8, d8, u8);
core_cases!(core_u16, d16, u16);
core_cases!(core_u32, d32, u32);
core_cases!(core_u64, d64, u64);

#[test]
fn refinement_matches_finite_u8_sets() {
    use semi_persistent_abstract_domains::domains::d8::Congruence;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = Congruence { modulus: m, residue: r }.normalize();
            let values: Vec<bool> = (0..=u8::MAX).map(|x| {
                if m == 0 { x == r } else { x % m == r % m }
            }).collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let subset = av.iter().zip(bv).all(|(x, y)| !x || *y);
            assert_eq!(a.refines(b), subset,
                "({}, {}) refines ({}, {})", a.modulus, a.residue, b.modulus, b.residue);
        }
    }
}

macro_rules! meet_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::domains::$domain::Congruence;
            let a = Congruence { modulus: 6, residue: 1 };
            let b = Congruence { modulus: 4, residue: 3 };
            let merged = a.meet(&b).expect("compatible constraints");
            assert_eq!((merged.modulus, merged.residue), (12, 7));
            assert!(a.meet(&Congruence { modulus: 4, residue: 2 }).is_none());
            for (left, right) in [(a, Congruence::top()), (Congruence::top(), a), (a, a)] {
                let result = left.meet(&right).unwrap();
                assert_eq!((result.modulus, result.residue), (a.modulus, a.residue));
            }
            for x in [0, 7] {
                let singleton = Congruence::constant(x);
                for result in [a.meet(&singleton), singleton.meet(&a)] {
                    if x == 7 {
                        let r = result.unwrap();
                        assert_eq!((r.modulus, r.residue), (0, x));
                    } else {
                        assert!(result.is_none());
                    }
                }
                assert!(singleton.meet(&singleton).unwrap().contains(x));
                assert!(singleton.meet(&Congruence::constant(x + 1)).is_none());
            }
            let max = <$uint>::MAX;
            for x in [0, 1, max] {
                let left = Congruence { modulus: max, residue: x % max };
                let right = Congruence { modulus: max - 1, residue: x % (max - 1) };
                for result in [left.meet(&right), right.meet(&left)] {
                    let r = result.expect("unique representable solution");
                    assert_eq!((r.modulus, r.residue), (0, x));
                }
            }
            let left = Congruence { modulus: max, residue: max - 1 };
            let right = Congruence { modulus: max - 1, residue: max - 2 };
            assert!(left.meet(&right).is_none());
            assert!(right.meet(&left).is_none());
        }
    };
}

meet_cases!(meet_u8, d8, u8);
meet_cases!(meet_u16, d16, u16);
meet_cases!(meet_u32, d32, u32);
meet_cases!(meet_u64, d64, u64);

#[test]
fn meet_matches_finite_u8_sets() {
    use semi_persistent_abstract_domains::domains::d8::Congruence;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = Congruence { modulus: m, residue: r }.normalize();
            let values: Vec<bool> = (0..=u8::MAX).map(|x| {
                if m == 0 { x == r } else { x % m == r % m }
            }).collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let result = a.meet(b);
            if let Some(r) = result {
                assert!(r.modulus == 0 || r.residue < r.modulus);
            }
            let mut nonempty = false;
            for x in 0..=u8::MAX {
                let expected = av[x as usize] && bv[x as usize];
                nonempty |= expected;
                assert_eq!(result.as_ref().is_some_and(|r| r.contains(x)), expected,
                    "({}, {}) meet ({}, {}) at {x}", a.modulus, a.residue, b.modulus, b.residue);
            }
            assert_eq!(result.is_some(), nonempty);
        }
    }
}

macro_rules! join_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::domains::$domain::Congruence;
            let a = Congruence { modulus: 4, residue: 1 };
            let b = Congruence { modulus: 6, residue: 3 };
            for (left, right) in [(a, b), (b, a)] {
                let r = left.join(&right);
                assert_eq!((r.modulus, r.residue), (2, 1));
            }
            let same = a.join(&a);
            assert_eq!((same.modulus, same.residue), (4, 1));
            for (left, right) in [(a, Congruence::top()), (Congruence::top(), a)] {
                let r = left.join(&right);
                assert_eq!((r.modulus, r.residue), (1, 0));
            }
            let one = Congruence::constant(1);
            let five = Congruence::constant(5);
            let r = one.join(&five);
            assert_eq!((r.modulus, r.residue), (4, 1));
            assert_eq!(one.join(&one).modulus, 0);
            let r = a.join(&five);
            assert_eq!((r.modulus, r.residue), (4, 1));
            let r = a.join(&Congruence::constant(2));
            assert_eq!((r.modulus, r.residue), (1, 0));

            let max = <$uint>::MAX;
            let finite_one = Congruence { modulus: max, residue: 1 };
            let r = finite_one.join(&five);
            assert_eq!((r.modulus, r.residue), (4, 1));
            let r = finite_one.join(&one);
            assert_eq!((r.modulus, r.residue), (0, 1));
            let r = Congruence::constant(0).join(&Congruence::constant(max));
            assert_eq!((r.modulus, r.residue), (max, 0));
            let r = Congruence::constant(max - 1).join(&Congruence::constant(max));
            assert_eq!((r.modulus, r.residue), (1, 0));
        }
    };
}

join_cases!(join_u8, d8, u8);
join_cases!(join_u16, d16, u16);
join_cases!(join_u32, d32, u32);
join_cases!(join_u64, d64, u64);

#[test]
fn join_covers_finite_u8_sets() {
    use semi_persistent_abstract_domains::domains::d8::Congruence;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = Congruence { modulus: m, residue: r }.normalize();
            let values: Vec<bool> = (0..=u8::MAX).map(|x| {
                if m == 0 { x == r } else { x % m == r % m }
            }).collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let result = a.join(b);
            assert!(result.modulus == 0 || result.residue < result.modulus);
            let reverse = b.join(a);
            assert_eq!((result.modulus, result.residue), (reverse.modulus, reverse.residue));
            for x in 0..=u8::MAX {
                if av[x as usize] || bv[x as usize] {
                    assert!(result.contains(x),
                        "({}, {}) join ({}, {}) misses {x}", a.modulus, a.residue, b.modulus, b.residue);
                }
            }
            for (upper, _) in &classes {
                if a.refines(upper) && b.refines(upper) {
                    assert!(result.refines(upper));
                }
            }
        }
    }
}

macro_rules! add_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::domains::$domain::Congruence;
            let max = <$uint>::MAX;
            for (x, y) in [(0, 0), (1, 2), (max, 1), (max, max)] {
                let r = Congruence::constant(x).add(&Congruence::constant(y));
                assert_eq!((r.modulus, r.residue), (0, x.wrapping_add(y)));
            }
            let finite_one = Congruence { modulus: max, residue: 1 };
            let r = finite_one.add(&Congruence::constant(max));
            assert_eq!((r.modulus, r.residue), (0, 0));
            let odd = Congruence { modulus: 2, residue: 1 };
            let r = odd.add(&odd);
            assert_eq!((r.modulus, r.residue), (2, 0));
            let four = Congruence { modulus: 4, residue: 3 };
            let r = four.add(&Congruence::constant(2));
            assert_eq!((r.modulus, r.residue), (4, 1));
            for (a, b) in [(odd, Congruence::top()), (Congruence::top(), odd)] {
                let r = a.add(&b);
                assert_eq!((r.modulus, r.residue), (1, 0));
            }
            let multiples_of_three = Congruence { modulus: 3, residue: 0 };
            let r = multiples_of_three.add(&multiples_of_three);
            assert_eq!((r.modulus, r.residue), (1, 0));
            assert!(r.contains(max.wrapping_add(3)));
        }
    };
}

add_cases!(add_u8, d8, u8);
add_cases!(add_u16, d16, u16);
add_cases!(add_u32, d32, u32);
add_cases!(add_u64, d64, u64);

#[test]
fn addition_covers_finite_u8_sums() {
    use semi_persistent_abstract_domains::domains::d8::Congruence;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = Congruence { modulus: m, residue: r }.normalize();
            let values: Vec<u8> = (0..=u8::MAX).filter(|x| {
                if m == 0 { *x == r } else { x % m == r % m }
            }).collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let result = a.add(b);
            assert!(result.modulus == 0 || result.residue < result.modulus);
            let reverse = b.add(a);
            assert_eq!((result.modulus, result.residue), (reverse.modulus, reverse.residue));
            for &x in av {
                for &y in bv {
                    assert!(result.contains(x.wrapping_add(y)),
                        "({}, {}) + ({}, {}) misses {x} + {y}", a.modulus, a.residue, b.modulus, b.residue);
                }
            }
        }
    }
}
