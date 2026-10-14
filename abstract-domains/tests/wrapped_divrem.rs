// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_abstract_domains::{
    lattice::{BotOr, Domain},
    semantics::{Signed, Unsigned},
    transfer::{DivRem, DivZero},
    wrapped::Wrapped,
};
fn contains(r: &BotOr<Wrapped<u8>>, x: u8) -> bool {
    match r {
        BotOr::Bot => false,
        BotOr::Val(w) => w.contains(x),
    }
}
fn flag(r: &DivZero) -> u8 {
    match r {
        DivZero::Never => 0,
        DivZero::Maybe => 1,
        DivZero::Always => 2,
    }
}
fn values(lo: u8, hi: u8) -> Vec<u8> {
    (0..=255)
        .filter(|&x| {
            if lo <= hi {
                lo <= x && x <= hi
            } else {
                x >= lo || x <= hi
            }
        })
        .collect()
}
#[test]
fn exhaustive_u8_singleton_division_and_zero_flags() {
    for x in 0..=255u8 {
        for y in 0..=255u8 {
            let a = Wrapped::constant(x);
            let b = Wrapped::constant(y);
            let uq = <Wrapped<u8> as DivRem<Unsigned<u8>>>::div(&a, &b);
            let ur = <Wrapped<u8> as DivRem<Unsigned<u8>>>::rem(&a, &b);
            let sq = <Wrapped<u8> as DivRem<Signed<u8>>>::div(&a, &b);
            let sr = <Wrapped<u8> as DivRem<Signed<u8>>>::rem(&a, &b);
            for r in [&uq, &ur, &sq, &sr] {
                assert_eq!(flag(&r.1), if y == 0 { 2 } else { 0 });
                assert_eq!(r.0.is_bot(), y == 0);
            }
            if let Some(quotient) = x.checked_div(y) {
                // Quotient is exact on singleton inputs. Reference Interval's
                // remainder can conservatively include smaller magnitudes.
                assert!(matches!(uq.0,BotOr::Val(w) if w==Wrapped::constant(quotient)));
                assert!(
                    matches!(sq.0,BotOr::Val(w) if w==Wrapped::constant((x as i8).wrapping_div(y as i8) as u8))
                );
                assert!(contains(&ur.0, x % y));
                assert!(contains(&sr.0, (x as i8).wrapping_rem(y as i8) as u8));
            }
        }
    }
}
#[test]
fn sampled_u8_arcs_all_concrete_dividends_and_divisors() {
    let endpoints = [0, 1, 2, 126, 127, 128, 254, 255];
    let mut cases = vec![(Wrapped::<u8>::top(), (0..=255).collect::<Vec<u8>>())];
    for lo in endpoints {
        for hi in endpoints {
            cases.push((Wrapped::new(lo, hi), values(lo, hi)));
        }
    }
    for (a, xs) in &cases {
        for (b, ys) in &cases {
            let uq = <Wrapped<u8> as DivRem<Unsigned<u8>>>::div(a, b);
            let ur = <Wrapped<u8> as DivRem<Unsigned<u8>>>::rem(a, b);
            let sq = <Wrapped<u8> as DivRem<Signed<u8>>>::div(a, b);
            let sr = <Wrapped<u8> as DivRem<Signed<u8>>>::rem(a, b);
            let expected = if ys == &[0] {
                2
            } else if ys.contains(&0) {
                1
            } else {
                0
            };
            for r in [&uq, &ur, &sq, &sr] {
                assert_eq!(flag(&r.1), expected);
                assert_eq!(r.0.is_bot(), expected == 2);
            }
            let mut eq = [false; 256];
            let mut er = [false; 256];
            let mut esq = [false; 256];
            let mut esr = [false; 256];
            for &x in xs {
                for &y in ys {
                    if let Some(quotient) = x.checked_div(y) {
                        eq[quotient as usize] = true;
                        er[(x % y) as usize] = true;
                        esq[(x as i8).wrapping_div(y as i8) as u8 as usize] = true;
                        esr[(x as i8).wrapping_rem(y as i8) as u8 as usize] = true;
                    }
                }
            }
            for x in 0..=255u8 {
                assert!(!eq[x as usize] || contains(&uq.0, x));
                assert!(!er[x as usize] || contains(&ur.0, x));
                assert!(!esq[x as usize] || contains(&sq.0, x));
                assert!(!esr[x as usize] || contains(&sr.0, x));
            }
        }
    }
}
macro_rules! boundary {
    ($name:ident,$w:ty)=>{#[test] fn $name(){
        type D=Wrapped<$w>;
        let max=<$w>::MAX;let min=max/2+1;
        let r=<D as DivRem<Signed<$w>>>::div(&D::constant(min),&D::constant(max));
        assert_eq!(flag(&r.1),0);assert!(matches!(r.0,BotOr::Val(w) if w==D::constant(min)));
        let r=<D as DivRem<Signed<$w>>>::rem(&D::constant(min),&D::constant(max));
        assert!(matches!(r.0,BotOr::Val(w) if w.contains(0)));
        let r=<D as DivRem<Unsigned<$w>>>::div(&D::top(),&D::constant(0));
        assert!(r.0.is_bot());assert_eq!(flag(&r.1),2);
        let r=<D as DivRem<Signed<$w>>>::div(&D::new(max-9,max),&D::new(1,2));
        assert!(matches!(r.0,BotOr::Val(w) if w.contains(max)&&w.contains(max-9)&&!w.contains(1)));
        let r=<D as DivRem<Unsigned<$w>>>::div(&D::constant(12),&D::new(max,1));
        assert_eq!(flag(&r.1),1);assert!(matches!(r.0,BotOr::Val(w) if w.contains(0)&&w.contains(12)));
    }};
}
boundary!(u8_boundary, u8);
boundary!(u16_boundary, u16);
boundary!(u32_boundary, u32);
boundary!(u64_boundary, u64);
