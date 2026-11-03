// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Facts arithmetic checked against concrete wrapping machine-word operations.
use semi_persistent_abstract_domains::congruence::Congruence;
use semi_persistent_abstract_domains::facts::Facts;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::reduce::Channel;
use semi_persistent_abstract_domains::semantics::Unsigned;
use semi_persistent_abstract_domains::transfer::Arith;
use semi_persistent_abstract_domains::word::Word;
use std::fmt::Debug;

fn val<T>(r: BotOr<T>) -> T {
    match r {
        BotOr::Val(v) => v,
        BotOr::Bot => panic!("expected nonempty facts"),
    }
}

fn facts(lo: u8, hi: u8, m: u8, r: u8) -> Facts<u8> {
    val(Facts::from_parts(
        Interval::new(lo, hi).unwrap(),
        Congruence::new(m, r),
    ))
}

fn constant<W: Word>(x: W) -> Facts<W> {
    Facts::from_interval(Interval::constant(x))
}

fn has<W: Word>(f: &Facts<W>, x: W) -> bool {
    let (lo, hi) = f.interval().bounds();
    lo.le(x) && x.le(hi) && f.congruence().contains(x)
}

fn normalized<W: Word + Debug + PartialEq>(f: &Facts<W>) {
    let n = val(f.normalize());
    assert_eq!(n.interval().bounds(), f.interval().bounds());
    assert_eq!(n.congruence().parts(), f.congruence().parts());
    let (lo, hi) = f.interval().bounds();
    assert!(f.congruence().contains(lo) && f.congruence().contains(hi));
    if lo == hi {
        assert_eq!(f.congruence().as_constant(), Some(lo));
    }
}

fn check_constant<W: Word + Debug + PartialEq>(f: &Facts<W>, expected: W) {
    assert_eq!(f.interval().bounds(), (expected, expected));
    assert_eq!(f.congruence().as_constant(), Some(expected));
    normalized(f);
}

#[test]
fn exhaustive_u8_constants() {
    for x in 0..=255u8 {
        let a = constant(x);
        check_constant(&a.neg(), x.wrapping_neg());
        for y in 0..=255u8 {
            let b = constant(y);
            check_constant(&a.add(&b), x.wrapping_add(y));
            check_constant(&a.sub(&b), x.wrapping_sub(y));
        }
    }
}

#[test]
fn nonconstant_parity_and_grid_normalization() {
    let odd = facts(0, 255, 4, 3);
    let one = constant(1u8);
    let sum = odd.add(&one);
    // Mixed wrapping makes the interval Top; the congruence snaps its upper bound.
    assert_eq!(sum.interval().bounds(), (0, 252));
    assert_eq!(sum.congruence().parts(), (4, 0));
    let difference = odd.sub(&one);
    assert_eq!(difference.interval().bounds(), (2, 254));
    assert_eq!(difference.congruence().parts(), (4, 2));
    let negative = odd.neg();
    assert_eq!(negative.interval().bounds(), (1, 253));
    assert_eq!(negative.congruence().parts(), (4, 1));
    for f in [&sum, &difference, &negative] {
        normalized(f);
    }
    let even = facts(0, 255, 2, 0);
    let odd = facts(0, 255, 2, 1);
    assert_eq!(even.add(&odd).congruence().parts(), (2, 1));
    assert_eq!(odd.sub(&odd).congruence().parts(), (2, 0));
    assert_eq!(even.neg().congruence().parts(), (2, 0));
}

#[test]
fn non_power_of_two_wrap_segments() {
    let multiples = facts(0, 255, 6, 0);
    let nonzero = facts(0, 255, 6, 5);
    let cases = [
        // No wrap: all multiples of six are at most 252.
        (multiples.add(&constant(1)), (6, 1)),
        (nonzero.sub(&constant(1)), (6, 4)),
        // Uniform wrap: even the least sum is 5 + 251 = 256.
        (nonzero.add(&constant(251)), (6, 0)),
        (constant(0).sub(&nonzero), (6, 5)),
        (nonzero.neg(), (6, 5)),
        // Mixed wrap reduces the stride using the machine modulus.
        (multiples.add(&constant(5)), (2, 1)),
        (multiples.sub(&constant(1)), (2, 1)),
        (multiples.neg(), (2, 0)),
        // Odd stride and mixed wrapping can require Top.
        (facts(0, 255, 3, 0).add(&constant(1)), (1, 0)),
    ];
    for (result, expected) in cases {
        assert_eq!(result.congruence().parts(), expected);
        normalized(&result);
    }
}

/// Sampled reduced records; every concrete operand pair is enumerated.
#[test]
fn sampled_facts_exhaustive_concrete_operands() {
    let records = [
        Facts::top(),
        constant(0),
        constant(1),
        constant(251),
        constant(255),
        facts(0, 255, 2, 0),
        facts(0, 255, 2, 1),
        facts(0, 255, 3, 0),
        facts(0, 255, 4, 3),
        facts(0, 255, 6, 0),
        facts(0, 255, 6, 5),
        facts(0, 255, 17, 3),
        facts(0, 255, 200, 1),
        facts(3, 30, 4, 1),
        facts(120, 140, 3, 2),
        facts(240, 255, 6, 5),
    ];
    for a in &records {
        let xs: Vec<_> = (0..=255u8).filter(|&x| has(a, x)).collect();
        let neg = <Facts<u8> as Arith<Unsigned<u8>>>::neg(a);
        normalized(&neg);
        for &x in &xs {
            assert!(has(&neg, x.wrapping_neg()));
        }
        for b in &records {
            let ys: Vec<_> = (0..=255u8).filter(|&y| has(b, y)).collect();
            let sum = <Facts<u8> as Arith<Unsigned<u8>>>::add(a, b);
            let difference = <Facts<u8> as Arith<Unsigned<u8>>>::sub(a, b);
            normalized(&sum);
            normalized(&difference);
            for &x in &xs {
                for &y in &ys {
                    assert!(has(&sum, x.wrapping_add(y)), "add {x} {y}");
                    assert!(has(&difference, x.wrapping_sub(y)), "sub {x} {y}");
                }
            }
        }
    }
}

#[test]
fn u128_overflow_underflow_and_nonconstant_grids() {
    let max = u128::MAX;
    let points = [0, 1, 2, (1u128 << 127) - 1, 1u128 << 127, max - 1, max];
    for x in points {
        let a = constant(x);
        check_constant(&a.neg(), x.wrapping_neg());
        for y in points {
            let b = constant(y);
            check_constant(&a.add(&b), x.wrapping_add(y));
            check_constant(&a.sub(&b), x.wrapping_sub(y));
        }
    }
    let odd = val(Facts::from_parts(
        Interval::top(),
        Congruence::new(4u128, 3),
    ));
    let sum = odd.add(&constant(1));
    assert_eq!(sum.interval().bounds(), (0, max - 3));
    assert_eq!(sum.congruence().parts(), (4, 0));
    let low = val(Facts::from_parts(
        Interval::new(1u128, 9).unwrap(),
        Congruence::new(4, 1),
    ));
    let high = val(Facts::from_parts(
        Interval::new(max - 8, max).unwrap(),
        Congruence::new(4, 3),
    ));
    for a in [&low, &high] {
        let neg = a.neg();
        normalized(&neg);
        let (lo, hi) = a.interval().bounds();
        for x in lo..=hi {
            if !has(a, x) {
                continue;
            }
            assert!(has(&neg, x.wrapping_neg()));
            for b in [&low, &high] {
                let sum = a.add(b);
                let difference = a.sub(b);
                normalized(&sum);
                normalized(&difference);
                let (blo, bhi) = b.interval().bounds();
                for y in blo..=bhi {
                    if has(b, y) {
                        assert!(has(&sum, x.wrapping_add(y)));
                        assert!(has(&difference, x.wrapping_sub(y)));
                    }
                }
            }
        }
    }
    normalized(&sum);
}
