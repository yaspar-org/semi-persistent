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

fn facts(lo: u8, hi: u8) -> Facts<u8> {
    Facts::from_interval(Interval::new(lo, hi).unwrap())
}

#[test]
fn hulls_constants_and_top() {
    for m in 0..=255u8 {
        for r in 0..=255u8 {
            let c = Congruence::new(m, r);
            let (lo, hi) = val(c.to_channel()).interval().bounds();
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
                                BotOr::Val(p) => {
                                    let (l, h) = p.b.interval().bounds();
                                    p.a.contains(x) && l <= x && x <= h
                                }
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
    // General grid emptiness remains the responsibility of normalization.
    assert!(val(c.refine(&facts(8, 9))).same(&c));
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
        let (lo, hi) = val(reduced.to_channel()).interval().bounds();
        for x in (0..=255u8).filter(|&x| a.a.contains(x)) {
            let y = match op {
                0 => x.wrapping_add(1),
                1 => x.wrapping_sub(1),
                _ => x.wrapping_neg(),
            };
            assert!(reduced.a.contains(y) && lo <= y && y <= hi);
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
