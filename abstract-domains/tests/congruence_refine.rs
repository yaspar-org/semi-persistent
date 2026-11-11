// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_abstract_domains::congruence::Congruence;
use semi_persistent_abstract_domains::facts::Facts;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::reduce::{Product, Refine};
use semi_persistent_abstract_domains::semantics::Unsigned;
use semi_persistent_abstract_domains::transfer::Arith;

fn val<T>(r: BotOr<T>) -> T {
    match r {
        BotOr::Val(v) => v,
        BotOr::Bot => panic!("expected nonempty"),
    }
}

fn has(f: &Facts<u8>, x: u8) -> bool {
    let (lo, hi) = f.interval().bounds();
    lo <= x && x <= hi && f.congruence().contains(x)
}

fn facts(lo: u8, hi: u8) -> Facts<u8> {
    Facts::from_interval(Interval::new(lo, hi).unwrap())
}

#[test]
fn hulls_constants_and_top() {
    for m in 0..=255u8 {
        for r in 0..=255u8 {
            let c = Congruence::new(m, r);
            let exported = val(c.to_channel());
            assert!(exported.congruence().same(&c));
            let (lo, hi) = exported.interval().bounds();
            for x in 0..=255u8 {
                assert_eq!(has(&exported, x), c.contains(x));
            }
            let members: Vec<_> = (0..=255u8).filter(|&x| c.contains(x)).collect();
            assert_eq!((lo, hi), (members[0], *members.last().unwrap()));
        }
    }
    assert_eq!(
        val(Congruence::<u8>::top().to_channel())
            .interval()
            .bounds(),
        (0, 255)
    );
}

#[test]
fn refinement_and_reduction_preserve_intersections() {
    let points = [0, 1, 3, 7, 10, 11, 127, 128, 254, 255];
    for m in [0, 1, 2, 3, 4, 17, 128, 255] {
        for r in points {
            let c = Congruence::new(m, r);
            for lo in points {
                for hi in points.into_iter().filter(|&hi| lo <= hi) {
                    let f = facts(lo, hi);
                    let refined = c.refine(&f);
                    for fuel in [0, 1, 3] {
                        let reduced = Product { a: c, b: f.dup() }.reduce(fuel);
                        for x in 0..=255u8 {
                            let expected = c.contains(x) && lo <= x && x <= hi;
                            let retained = match &refined {
                                BotOr::Bot => false,
                                BotOr::Val(v) => v.contains(x),
                            };
                            assert!(!expected || retained);
                            assert!(!retained || c.contains(x));
                            let actual = match &reduced {
                                BotOr::Bot => false,
                                BotOr::Val(p) => p.a.contains(x) && has(&p.b, x),
                            };
                            assert_eq!(actual, expected);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn singleton_and_bottom_feedback() {
    let c = Congruence::new(4u8, 3);
    assert_eq!(val(c.refine(&facts(7, 7))).as_constant(), Some(7));
    assert!(matches!(c.refine(&facts(6, 6)), BotOr::Bot));
    assert!(matches!(c.refine(&facts(0, 2)), BotOr::Bot));
    assert!(val(c.refine(&Facts::top())).same(&c));
    assert!(matches!(c.refine(&facts(8, 9)), BotOr::Bot));
    assert_eq!(val(c.refine(&facts(5, 9))).as_constant(), Some(7));
}

#[test]
fn product_arithmetic_sound_through_channel() {
    type P = Product<Congruence<u8>, Facts<u8>>;
    let a = P {
        a: Congruence::new(4, 3),
        b: facts(0, 255),
    };
    let b = P {
        a: Congruence::constant(1),
        b: facts(1, 1),
    };
    let outputs = [
        <P as Arith<Unsigned<u8>>>::add(&a, &b),
        <P as Arith<Unsigned<u8>>>::sub(&a, &b),
        <P as Arith<Unsigned<u8>>>::neg(&a),
    ];
    for (op, output) in outputs.into_iter().enumerate() {
        let reduced = val(output.reduce(3));
        let exported = val(reduced.to_channel());
        for x in (0..=255u8).filter(|&x| a.a.contains(x)) {
            let y = match op {
                0 => x.wrapping_add(1),
                1 => x.wrapping_sub(1),
                _ => x.wrapping_neg(),
            };
            assert!(reduced.a.contains(y) && has(&reduced.b, y) && has(&exported, y));
        }
    }
}

#[test]
fn u128_full_width_channel_and_refinement() {
    let c = Congruence::new(4u128, 3);
    assert_eq!(val(c.to_channel()).interval().bounds(), (3, u128::MAX));
    let f = Facts::from_interval(Interval::constant(u128::MAX));
    assert_eq!(val(c.refine(&f)).as_constant(), Some(u128::MAX));
    let p = val(Product { a: c, b: f }.reduce(3));
    assert_eq!(p.a.as_constant(), Some(u128::MAX));
    let f = Facts::from_interval(Interval::constant(u128::MAX - 1));
    assert!(matches!(c.refine(&f), BotOr::Bot));
    let c = Congruence::constant(1u128 << 127);
    assert_eq!(
        val(c.to_channel()).interval().bounds(),
        (1u128 << 127, 1u128 << 127)
    );
}

#[test]
fn snapped_bounds_and_reduction_fuel() {
    for fuel in [0, 1, 3] {
        let p = val(Product {
            a: Congruence::new(4u8, 3),
            b: facts(3, 10),
        }
        .reduce(fuel));
        assert_eq!(
            p.b.interval().bounds(),
            if fuel == 0 { (3, 10) } else { (3, 7) }
        );
        if fuel > 0 {
            assert!(p.b.congruence().same(&p.a));
        }
        let empty = Product {
            a: Congruence::new(4u8, 3),
            b: facts(8, 9),
        }
        .reduce(fuel);
        assert_eq!(matches!(empty, BotOr::Bot), fuel > 0);
    }
}

#[test]
fn incoming_congruence_and_nested_products() {
    let c = Congruence::new(4u8, 3);
    let incoming = val(Facts::from_parts(Interval::top(), Congruence::new(6, 5)));
    let merged = val(c.refine(&incoming));
    assert!(merged.same(&Congruence::new(12, 11)));
    for x in 0..=255u8 {
        assert_eq!(merged.contains(x), c.contains(x) && has(&incoming, x));
    }
    let incompatible = val(Facts::from_parts(Interval::top(), Congruence::new(2, 0)));
    assert!(matches!(c.refine(&incompatible), BotOr::Bot));

    for fuel in [1, 3] {
        let pair = val(Product {
            a: c,
            b: incoming.congruence(),
        }
        .reduce(fuel));
        assert!(pair.a.same(&merged) && pair.b.same(&merged));
        assert!(matches!(
            Product {
                a: c,
                b: incompatible.congruence()
            }
            .reduce(fuel),
            BotOr::Bot
        ));
        let nested = val(Product {
            a: Product {
                a: c,
                b: incoming.congruence(),
            },
            b: facts(8, 24),
        }
        .reduce(fuel));
        assert_eq!(nested.b.interval().bounds(), (11, 23));
        for x in 0..=255u8 {
            assert_eq!(
                nested.a.a.contains(x) && nested.a.b.contains(x) && has(&nested.b, x),
                c.contains(x) && has(&incoming, x) && (8..=24).contains(&x)
            );
        }
        assert!(matches!(
            Product {
                a: Product {
                    a: c,
                    b: incoming.congruence()
                },
                b: facts(12, 22),
            }
            .reduce(fuel),
            BotOr::Bot
        ));
    }
}

/// Every u8 interval for representative grids, including top and a constant.
/// The oracle enumerates actual words rather than reproducing grid rounding.
#[test]
fn every_u8_interval_against_concrete_members() {
    for c in [
        Congruence::top(),
        Congruence::constant(127u8),
        Congruence::new(4, 3),
        Congruence::new(17, 5),
    ] {
        for lo in 0..=255u8 {
            for hi in lo..=255u8 {
                let expected: Vec<_> = (lo..=hi).filter(|&x| c.contains(x)).collect();
                let f = facts(lo, hi);
                let refined = c.refine(&f);
                let reduced = Product { a: c, b: f }.reduce(1);
                assert_eq!(matches!(refined, BotOr::Bot), expected.is_empty());
                assert_eq!(matches!(reduced, BotOr::Bot), expected.is_empty());
                if let BotOr::Val(r) = refined {
                    if expected.len() == 1 {
                        assert_eq!(r.as_constant(), Some(expected[0]));
                    }
                    for x in 0..=255u8 {
                        assert!(!r.contains(x) || c.contains(x));
                        assert_eq!(
                            r.contains(x) && lo <= x && x <= hi,
                            expected.binary_search(&x).is_ok()
                        );
                    }
                }
                if let BotOr::Val(p) = reduced {
                    assert_eq!(
                        p.b.interval().bounds(),
                        (expected[0], *expected.last().unwrap())
                    );
                    for x in 0..=255u8 {
                        assert_eq!(
                            p.a.contains(x) && has(&p.b, x),
                            expected.binary_search(&x).is_ok()
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn u128_grid_conflicts_and_snapping() {
    let max = u128::MAX;
    let c = Congruence::new(4u128, 1);
    let interval = |lo, hi| Facts::from_interval(Interval::new(lo, hi).unwrap());
    assert!(val(c.to_channel()).congruence().same(&c));
    assert!(matches!(c.refine(&interval(max - 1, max)), BotOr::Bot));
    assert_eq!(
        val(c.refine(&interval(max - 3, max))).as_constant(),
        Some(max - 2)
    );
    let p = val(Product {
        a: c,
        b: interval(max - 7, max),
    }
    .reduce(1));
    assert_eq!(p.b.interval().bounds(), (max - 6, max - 2));
    let c = Congruence::new(1u128 << 127, 3);
    assert_eq!(
        val(c.refine(&interval(4, max))).as_constant(),
        Some((1u128 << 127) + 3)
    );
    assert!(matches!(c.refine(&interval(0, 2)), BotOr::Bot));
    let incompatible = val(Facts::from_parts(
        Interval::top(),
        Congruence::new(2u128, 0),
    ));
    assert!(matches!(c.refine(&incompatible), BotOr::Bot));
}
