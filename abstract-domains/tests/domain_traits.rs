// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the reference domains against brute-force concretization.
//! The Verus proofs cover all widths; these tests exercise the executable code
//! (contracts are erased at runtime) exhaustively over sampled u8 intervals.
use semi_persistent_abstract_domains::ibig::IBig;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::interval_z::{Hi, IntervalZ, Lo};
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::semantics::{Euclid, Trunc, Unsigned};
use semi_persistent_abstract_domains::transfer::{Arith, DivRem, DivZero, Mul};
use semi_persistent_abstract_domains::word::Word;

type I8 = Interval<u8>;
type U = Unsigned<u8>;

fn iv(lo: u8, hi: u8) -> I8 {
    Interval::new(lo, hi).expect("lo <= hi")
}

fn has(i: &I8, x: u8) -> bool {
    let (lo, hi) = i.bounds();
    lo <= x && x <= hi
}

fn bot_has(b: &BotOr<I8>, x: u8) -> bool {
    match b {
        BotOr::Bot => false,
        BotOr::Val(i) => has(i, x),
    }
}

/// Intervals with bounds on a coarse grid plus the extremes.
fn samples() -> Vec<I8> {
    let pts: Vec<u8> = (0..=255u16)
        .step_by(51)
        .map(|v| v as u8)
        .chain([1, 2, 254, 255])
        .collect();
    let mut out = Vec::new();
    for &a in &pts {
        for &b in &pts {
            if a <= b {
                out.push(iv(a, b));
            }
        }
    }
    out
}

#[test]
fn interval_lattice_and_canonicity() {
    let s = samples();
    for a in &s {
        for b in &s {
            let j = a.join(b);
            let w = a.widen(b);
            let m = a.meet(b);
            for x in 0..=255u8 {
                let in_a = has(a, x);
                let in_b = has(b, x);
                if in_a || in_b {
                    assert!(has(&j, x) && has(&w, x));
                }
                if in_a && in_b {
                    assert!(bot_has(&m, x));
                }
                if a.leq(b) && in_a {
                    assert!(in_b);
                }
            }
            if matches!(m, BotOr::Bot) {
                assert!((0..=255u8).all(|x| !(has(a, x) && has(b, x))));
            }
            // Canonical: equal concretizations are equal bounds.
            if (0..=255u8).all(|x| has(a, x) == has(b, x)) {
                assert_eq!(a.bounds(), b.bounds());
            }
        }
    }
}

#[test]
fn interval_unsigned_transfers() {
    let s = samples();
    for a in &s {
        let n = <I8 as Arith<U>>::neg(a);
        for x in 0..=255u8 {
            if has(a, x) {
                assert!(has(&n, x.wrapping_neg()));
            }
        }
        for b in &s {
            let add = <I8 as Arith<U>>::add(a, b);
            let sub = <I8 as Arith<U>>::sub(a, b);
            let (q, qf) = <I8 as DivRem<U>>::div(a, b);
            let (r, rf) = <I8 as DivRem<U>>::rem(a, b);
            let mul = <I8 as Mul<U>>::mul(a, b);
            let (blo, bhi) = b.bounds();
            let expect_flag = |f: &DivZero| match f {
                DivZero::Never => assert!(blo > 0),
                DivZero::Maybe => assert!(blo == 0 && bhi > 0),
                DivZero::Always => assert!(bhi == 0),
            };
            expect_flag(&qf);
            expect_flag(&rf);
            for x in (0..=255u8).filter(|&x| has(a, x)) {
                for y in (0..=255u8).filter(|&y| has(b, y)) {
                    assert!(has(&add, x.wrapping_add(y)));
                    assert!(has(&sub, x.wrapping_sub(y)));
                    assert!(has(&mul, x.wrapping_mul(y)));
                    if let (Some(qv), Some(rv)) = (x.checked_div(y), x.checked_rem(y)) {
                        assert!(bot_has(&q, qv));
                        assert!(bot_has(&r, rv));
                    }
                }
            }
        }
    }
}

#[test]
fn interval_precision_cases() {
    // every sum wraps once: [200,210] + [100,110] = [44,64]
    assert_eq!(
        <I8 as Arith<U>>::add(&iv(200, 210), &iv(100, 110)).bounds(),
        (44, 64)
    );
    // every difference wraps once: [1,2] - [10,20] = [237,248]
    assert_eq!(
        <I8 as Arith<U>>::sub(&iv(1, 2), &iv(10, 20)).bounds(),
        (237, 248)
    );
    // singleton remainder is exact, and hi < d.lo is the identity
    let one = |b: &BotOr<I8>| match b {
        BotOr::Val(i) => i.bounds(),
        BotOr::Bot => panic!("bot"),
    };
    assert_eq!(one(&<I8 as DivRem<U>>::rem(&iv(1, 1), &iv(2, 2)).0), (1, 1));
    assert_eq!(
        one(&<I8 as DivRem<U>>::rem(&iv(27, 45), &iv(50, 60)).0),
        (27, 45)
    );
    assert_eq!(
        <I8 as Mul<U>>::mul(&iv(3, 5), &iv(10, 20)).bounds(),
        (30, 100)
    );
}

/// A small deterministic generator (high bits only; see the LCG note in the
/// containers tests).
fn next(s: &mut u128) -> u128 {
    *s = s
        .wrapping_mul(0x2545_f491_4f6c_dd1d_2545_f491_4f6c_dd1d)
        .wrapping_add(1_442_695_040_888_963_407);
    s.rotate_left(64)
}

#[test]
fn word_primitives_match_native() {
    for x in 0..=255u8 {
        assert_eq!(<u8 as Word>::trailing_zeros(x), x.trailing_zeros());
        for y in 0..=255u8 {
            assert_eq!(<u8 as Word>::wrapping_add(x, y), x.wrapping_add(y));
            assert_eq!(<u8 as Word>::wrapping_sub(x, y), x.wrapping_sub(y));
            assert_eq!(<u8 as Word>::checked_mul(x, y), x.checked_mul(y));
        }
    }
    let mut s = 7u128;
    for _ in 0..20_000 {
        let (a, b, m) = (next(&mut s), next(&mut s), next(&mut s));
        let sh = (next(&mut s) % 128) as u32;
        assert_eq!(
            <u128 as Word>::trailing_zeros(a >> sh),
            (a >> sh).trailing_zeros()
        );
        assert_eq!(
            <u64 as Word>::trailing_zeros(a as u64),
            (a as u64).trailing_zeros()
        );
        let (a64, b64, m64) = (a as u64, b as u64, (m as u64) | 1);
        let want64 = ((a64 as u128 * b64 as u128) % m64 as u128) as u64;
        assert_eq!(<u64 as Word>::mulmod(a64, b64, m64), want64);
        for m in [m | 1, (m >> 70) | 1] {
            let want = (num_bigint::BigUint::from(a) * num_bigint::BigUint::from(b))
                % num_bigint::BigUint::from(m);
            assert_eq!(
                num_bigint::BigUint::from(<u128 as Word>::mulmod(a, b, m)),
                want
            );
        }
    }
    assert_eq!(<u128 as Word>::trailing_zeros(0), 128);
    assert_eq!(<u128 as Word>::half(), 1u128 << 127);
}

#[test]
fn interval_u128_instance() {
    let a = Interval::<u128>::new(u128::MAX - 10, u128::MAX).unwrap();
    let b = Interval::<u128>::new(20, 30).unwrap();
    let s = <Interval<u128> as Arith<Unsigned<u128>>>::add(&a, &b);
    assert_eq!(s.bounds(), (9, 29));
    let m = <Interval<u128> as Mul<Unsigned<u128>>>::mul(&b, &b);
    assert_eq!(m.bounds(), (400, 900));
    assert!(a.join(&b).leq(&Interval::<u128>::top()));
}

fn z(v: i64) -> IBig {
    IBig::from_i64(v)
}

fn zi(lo: Option<i64>, hi: Option<i64>) -> IntervalZ {
    let lo = lo.map_or(Lo::NegInf, |v| Lo::Fin(z(v)));
    let hi = hi.map_or(Hi::PosInf, |v| Hi::Fin(z(v)));
    IntervalZ::new(lo, hi).expect("lo <= hi")
}

fn zhas(i: &IntervalZ, x: i64) -> bool {
    let c = IntervalZ::constant(z(x));
    c.leq(i)
}

#[test]
fn interval_z_lattice_and_arith() {
    let bounds: Vec<Option<i64>> = vec![None, Some(-7), Some(-1), Some(0), Some(3), Some(9)];
    let mut s = Vec::new();
    for &lo in &bounds {
        for &hi in &bounds {
            let ok = match (lo, hi) {
                (Some(a), Some(b)) => a <= b,
                _ => true,
            };
            if ok {
                s.push(zi(lo, hi));
            }
        }
    }
    let probe: Vec<i64> = (-20..=20).collect();
    for a in &s {
        for b in &s {
            let j = a.join(b);
            let m = a.meet(b);
            let add = <IntervalZ as Arith<Euclid>>::add(a, b);
            let sub = <IntervalZ as Arith<Euclid>>::sub(a, b);
            let (qe, fe) = <IntervalZ as DivRem<Euclid>>::div(a, b);
            let (re, _) = <IntervalZ as DivRem<Euclid>>::rem(a, b);
            let (qt, ft) = <IntervalZ as DivRem<Trunc>>::div(a, b);
            let (rt, _) = <IntervalZ as DivRem<Trunc>>::rem(a, b);
            match fe {
                DivZero::Always => assert!(matches!(qe, BotOr::Bot)),
                DivZero::Never => assert!(!zhas(b, 0)),
                DivZero::Maybe => assert!(zhas(b, 0)),
            }
            match ft {
                DivZero::Always => assert!(matches!(qt, BotOr::Bot)),
                DivZero::Never => assert!(!zhas(b, 0)),
                DivZero::Maybe => assert!(zhas(b, 0)),
            }
            for &x in &probe {
                let (in_a, in_b) = (zhas(a, x), zhas(b, x));
                if in_a || in_b {
                    assert!(zhas(&j, x));
                }
                if in_a && in_b {
                    assert!(matches!(&m, BotOr::Val(v) if zhas(v, x)));
                }
                for &y in &probe {
                    if in_a && zhas(b, y) {
                        assert!(zhas(&add, x + y) && zhas(&sub, x - y));
                        let prod = <IntervalZ as Mul<Euclid>>::mul(a, b);
                        assert!(zhas(&prod, x * y));
                        if y != 0 {
                            assert!(matches!(&qe, BotOr::Val(v) if zhas(v, x.div_euclid(y))));
                            assert!(matches!(&re, BotOr::Val(v) if zhas(v, x.rem_euclid(y))));
                            assert!(matches!(&qt, BotOr::Val(v) if zhas(v, x / y)));
                            assert!(matches!(&rt, BotOr::Val(v) if zhas(v, x % y)));
                        }
                    }
                }
            }
        }
    }
}
