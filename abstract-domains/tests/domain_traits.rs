// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the reference domains against brute-force concretization.
//! The Verus proofs cover all widths; these tests exercise the executable code
//! (contracts are erased at runtime) exhaustively over sampled u8 intervals.
use semi_persistent_abstract_domains::ibig::IBig;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::interval_z::{Hi, IntervalZ, Lo};
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::semantics::{Euclid, Unsigned};
use semi_persistent_abstract_domains::strided::StridedInterval;
use semi_persistent_abstract_domains::transfer::{Arith, DivRem, DivZero, Mul};
use semi_persistent_abstract_domains::word::Word;

type I8 = Interval<u8>;
type U = Unsigned<u8>;
type SI8 = StridedInterval<u8>;

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
            let (q, f) = <IntervalZ as DivRem<Euclid>>::div(a, b);
            match f {
                DivZero::Always => assert!(matches!(q, BotOr::Bot)),
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
                    }
                }
            }
        }
    }
}

fn si(stride: u8, lo: u8, hi: u8) -> SI8 {
    SI8::new(stride, lo, hi).expect("lo <= hi")
}

fn has_si(s: &SI8, x: u8) -> bool {
    s.contains(x)
}

fn bot_has_si(b: &BotOr<SI8>, x: u8) -> bool {
    match b {
        BotOr::Bot => false,
        BotOr::Val(v) => has_si(v, x),
    }
}

/// `lo`/`hi` on a coarse grid plus the extremes, crossed with a handful of
/// strides -- including 0 and non-dividing strides, so `new` has to
/// exercise its own canonicalization (e.g. `si(5, 7, 7)` collapsing to the
/// same value as `si(0, 7, 7)`) rather than only ever seeing pre-canonical
/// input.
fn strided_samples() -> Vec<SI8> {
    let pts: Vec<u8> = (0..=255u16)
        .step_by(51)
        .map(|v| v as u8)
        .chain([1, 2, 254, 255])
        .collect();
    let strides = [0u8, 1, 2, 3, 5];
    let mut out = Vec::new();
    for &lo in &pts {
        for &hi in &pts {
            if lo <= hi {
                for &s in &strides {
                    out.push(si(s, lo, hi));
                }
            }
        }
    }
    out
}

#[test]
fn strided_interval_lattice_and_canonicity() {
    let s = strided_samples();
    for a in &s {
        for b in &s {
            let j = a.join(b);
            let w = a.widen(b);
            let m = a.meet(b);
            for x in 0..=255u8 {
                let in_a = has_si(a, x);
                let in_b = has_si(b, x);
                if in_a || in_b {
                    assert!(has_si(&j, x) && has_si(&w, x));
                }
                if in_a && in_b {
                    assert!(bot_has_si(&m, x));
                }
                if a.leq(b) && in_a {
                    assert!(in_b);
                }
            }
            if matches!(m, BotOr::Bot) {
                assert!((0..=255u8).all(|x| !(has_si(a, x) && has_si(b, x))));
            }
            // Canonical: equal concretizations are equal (stride, lo, hi).
            if (0..=255u8).all(|x| has_si(a, x) == has_si(b, x)) {
                assert_eq!(a.bounds(), b.bounds());
            }
        }
    }
}

/// The review's exact example: (0,7,7), (2,7,7) and (5,7,7) all denote
/// {7}. Canonical wf means they are now literally the same value, not
/// just equal under some separate normalize() step.
#[test]
fn strided_canonical_form_is_unique() {
    let a = si(0, 7, 7);
    let b = si(2, 7, 7);
    let c = si(5, 7, 7);
    assert_eq!(a.bounds(), b.bounds());
    assert_eq!(b.bounds(), c.bounds());
}

/// Same stride, compatible residue: join widens the bounds to the least
/// upper bound the domain can represent -- not necessarily the exact
/// union. This example happens to be exact (11 = 8 + 3, no gap between the
/// operands), but see `strided_join_same_residue_is_not_always_exact`
/// below for one that isn't.
#[test]
fn strided_join_same_residue_is_the_least_upper_bound() {
    let a = si(3, 2, 8); // {2, 5, 8}
    let b = si(3, 11, 14); // {11, 14}, 11 == 2 (mod 3)
    assert_eq!(a.join(&b).bounds(), (3, 2, 14));
}

#[test]
fn strided_join_same_residue_is_not_always_exact() {
    let a = si(3, 2, 8);
    let b = si(3, 14, 17);
    let j = a.join(&b);
    assert!(j.contains(11));
    assert!(!a.contains(11) && !b.contains(11));
}

/// Two distinct singletons: the two-point set is exactly representable as
/// a stride equal to the gap between them.
#[test]
fn strided_join_two_singletons_is_exact() {
    let a = si(0, 4, 4);
    let b = si(0, 10, 10);
    assert_eq!(a.join(&b).bounds(), (6, 4, 10));
}

/// When one stride divides the other and both `lo`s sit on its grid, join
/// keeps that stride: `{4} ⊔ (2,0,10)` is `(2,0,10)`, not `(1,0,10)`.
#[test]
fn strided_join_keeps_a_dividing_stride() {
    assert_eq!(si(0, 4, 4).join(&si(2, 0, 10)).bounds(), (2, 0, 10));
    assert_eq!(si(2, 0, 10).join(&si(0, 4, 4)).bounds(), (2, 0, 10));
    assert_eq!(si(6, 0, 12).join(&si(3, 3, 9)).bounds(), (3, 0, 12));
}

/// Neither stride divides the other: the tight stride is
/// `gcd(3, 5, 0) = 1` here anyway, but in general it needs `gcd` from
/// #112. Join falls back to stride 1 and keeps the bounds.
#[test]
fn strided_join_incompatible_strides_keeps_bounds() {
    let a = si(3, 0, 9);
    let b = si(5, 0, 20);
    let j = a.join(&b);
    let (stride, lo, hi) = j.bounds();
    assert_eq!((stride, lo, hi), (1, 0, 20));
}

fn bot_bounds_si(b: &BotOr<SI8>) -> Option<(u8, u8, u8)> {
    match b {
        BotOr::Bot => None,
        BotOr::Val(v) => Some(v.bounds()),
    }
}

/// Top's stride 1 divides every stride, so meeting with Top clips `x` to
/// its own bounds: the identity.
#[test]
fn strided_meet_with_top_is_identity() {
    for x in &strided_samples() {
        assert_eq!(bot_bounds_si(&SI8::top().meet(x)), Some(x.bounds()));
        assert_eq!(bot_bounds_si(&x.meet(&SI8::top())), Some(x.bounds()));
    }
}

#[test]
fn strided_meet_is_commutative() {
    let s = strided_samples();
    for a in &s {
        for b in &s {
            assert_eq!(bot_bounds_si(&a.meet(b)), bot_bounds_si(&b.meet(a)));
        }
    }
}

/// Meet is the exact intersection for every pair, `Bot` exactly when it
/// is empty: the CRT class of the two residues, clipped to the common bounds.
#[test]
fn strided_meet_is_exact() {
    let s = strided_samples();
    for a in &s {
        for b in &s {
            let m = a.meet(b);
            for x in 0..=255u8 {
                assert_eq!(bot_has_si(&m, x), has_si(a, x) && has_si(b, x));
            }
        }
    }
}

/// Neither of 4 and 6 divides the other: CRT merges `0 mod 4` and
/// `2 mod 6` into `8 mod 12`, and `0 mod 4` with `3 mod 6` has no solution.
#[test]
fn strided_meet_non_dividing_strides_uses_crt() {
    let a = si(4, 0, 40);
    assert_eq!(bot_bounds_si(&a.meet(&si(6, 2, 32))), Some((12, 8, 32)));
    assert_eq!(bot_bounds_si(&a.meet(&si(6, 3, 33))), None);
    // a single common point.
    assert_eq!(
        bot_bounds_si(&si(4, 0, 12).meet(&si(6, 2, 14))),
        Some((0, 8, 8))
    );
}

/// `i = 0; while i < 200 { i += 4 }`: widening keeps stride 4 by jumping
/// the unstable upper bound to the last grid point (252), and one
/// decreasing iteration through the exact guard meet gives `(4, 0, 200)`.
/// Widening straight to Top would end at `(1, 0, 203)`.
#[test]
fn strided_widen_keeps_the_stride() {
    let entry = si(0, 0, 0);
    let guard = si(1, 0, 199);
    let body = |x: &SI8| -> SI8 {
        let BotOr::Val(v) = x.meet(&guard) else {
            panic!("loop head meets the guard")
        };
        let (s, lo, hi) = v.bounds();
        entry.join(&si(s, lo + 4, hi + 4))
    };
    let mut x = entry.join(&entry);
    loop {
        let next = body(&x);
        if next.leq(&x) {
            break;
        }
        x = x.widen(&next);
    }
    assert_eq!(x.bounds(), (4, 0, 252));
    assert_eq!(body(&x).bounds(), (4, 0, 200));
}

#[test]
fn strided_widen_jumps_to_last_grid_point() {
    let a = si(3, 10, 16);
    // lower bound unstable: 10 - 3k down to 1; upper bound stable.
    assert_eq!(a.widen(&si(3, 4, 16)).bounds(), (3, 1, 16));
    // upper bound unstable: last point of 10 + 3k below 255 is 253.
    assert_eq!(a.widen(&si(3, 10, 19)).bounds(), (3, 10, 253));
}

/// `leq` is complete: it answers exactly the brute-force subset question.
#[test]
fn strided_leq_is_complete() {
    let s = strided_samples();
    for a in &s {
        for b in &s {
            let subset = (0..=255u8).all(|x| !has_si(a, x) || has_si(b, x));
            assert_eq!(a.leq(b), subset);
        }
    }
}

#[test]
fn strided_constant_and_new_contract() {
    assert_eq!(SI8::constant(7).bounds(), (0, 7, 7));
    // stride 0 denotes {lo}, whatever hi is.
    assert_eq!(si(0, 7, 20).bounds(), (0, 7, 7));
}

/// `clip` and `widen` build some results directly instead of through `new`;
/// rebuilding each result through `new` must give the same value.
#[test]
fn strided_meet_and_widen_results_are_canonical() {
    let s = strided_samples();
    let canon = |v: &SI8| {
        let (st, lo, hi) = v.bounds();
        assert_eq!(si(st, lo, hi).bounds(), v.bounds());
    };
    for a in &s {
        for b in &s {
            if let BotOr::Val(m) = a.meet(b) {
                canon(&m);
            }
            canon(&a.widen(b));
        }
    }
}

fn si_points(a: &SI8) -> Vec<u8> {
    (0..=255u8).filter(|&x| has_si(a, x)).collect()
}

/// Every concrete sum, difference and negation lands in the abstract
/// result. Exact (the result is exactly the set of concrete results) when
/// the operands share a grid (equal strides, or a singleton) and no result
/// wraps or every result wraps; `neg` is exact whenever 0 is not in the set.
/// Bounds near 0, the middle and 255 (so sums and differences wrap all
/// ways), with sets capped at 32 points to keep the pair loop fast; Top is
/// added back explicitly.
fn strided_arith_samples() -> Vec<SI8> {
    let pts = [0u8, 1, 2, 7, 100, 128, 250, 254, 255];
    let strides = [0u8, 1, 2, 3, 4, 6, 64];
    let mut out = vec![SI8::top()];
    for &lo in &pts {
        for &hi in &pts {
            for &st in &strides {
                if lo <= hi {
                    let v = si(st, lo, hi);
                    if si_points(&v).len() <= 32 && !out.iter().any(|o| o.bounds() == v.bounds()) {
                        out.push(v);
                    }
                }
            }
        }
    }
    out
}

#[test]
fn strided_unsigned_arith() {
    let s = strided_arith_samples();
    for a in &s {
        let pa = si_points(a);
        let n = <SI8 as Arith<U>>::neg(a);
        let negs: Vec<u8> = pa.iter().map(|&x| x.wrapping_neg()).collect();
        assert!(negs.iter().all(|&v| has_si(&n, v)));
        if !has_si(a, 0) {
            assert_eq!(si_points(&n).len(), negs.len());
        }
        for b in &s {
            let pb = si_points(b);
            let (sa, _, _) = a.bounds();
            let (sb, _, _) = b.bounds();
            let same_grid = sa == sb || sa == 0 || sb == 0;
            for (r, f) in [
                (
                    <SI8 as Arith<U>>::add(a, b),
                    u8::wrapping_add as fn(u8, u8) -> u8,
                ),
                (<SI8 as Arith<U>>::sub(a, b), u8::wrapping_sub),
            ] {
                let mut results = std::collections::BTreeSet::new();
                let mut wraps = std::collections::BTreeSet::new();
                for &x in &pa {
                    for &y in &pb {
                        let v = f(x, y);
                        assert!(has_si(&r, v));
                        results.insert(v);
                        let wide = if f(1, 1) == 2 {
                            x as i32 + y as i32
                        } else {
                            x as i32 - y as i32
                        };
                        wraps.insert(!(0..=255).contains(&wide));
                    }
                }
                if same_grid && wraps.len() == 1 {
                    assert_eq!(si_points(&r).len(), results.len());
                }
            }
        }
    }
}

#[test]
fn strided_unsigned_arith_examples() {
    let add = <SI8 as Arith<U>>::add;
    let sub = <SI8 as Arith<U>>::sub;
    let neg = <SI8 as Arith<U>>::neg;
    // no wrap: shift both bounds, keep the stride.
    assert_eq!(add(&si(4, 0, 8), &si(0, 3, 3)).bounds(), (4, 3, 11));
    // every sum wraps: both bounds come back down by 256.
    assert_eq!(
        add(&si(4, 200, 208), &si(0, 100, 100)).bounds(),
        (4, 44, 52)
    );
    // some sums wrap: Top.
    assert_eq!(add(&si(4, 0, 252), &si(0, 8, 8)).bounds(), (1, 0, 255));
    // every difference is negative: both bounds go up by 256.
    assert_eq!(sub(&si(0, 1, 1), &si(2, 3, 7)).bounds(), (2, 250, 254));
    // neg reverses the grid; {0} stays {0}.
    assert_eq!(neg(&si(3, 1, 7)).bounds(), (3, 249, 255));
    assert_eq!(neg(&si(0, 0, 0)).bounds(), (0, 0, 0));
    // 0 maps to 0, the rest to 256 - x: {0} joined with (4, 248, 252).
    assert_eq!(neg(&si(4, 0, 8)).bounds(), (4, 0, 252));
}
