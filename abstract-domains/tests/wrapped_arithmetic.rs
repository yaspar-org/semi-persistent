// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_abstract_domains::{
    lattice::Domain,
    semantics::{Signed, Unsigned},
    transfer::Arith,
    wrapped::Wrapped,
};

fn concrete(lo: u8, hi: u8) -> Vec<u8> {
    (0..=255u8)
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
fn exhaustive_u8_arc_negation_is_exact() {
    for lo in 0..=255u8 {
        for hi in 0..=255u8 {
            let a = Wrapped::new(lo, hi);
            let r = <Wrapped<u8> as Arith<Unsigned<u8>>>::neg(&a);
            let signed = <Wrapped<u8> as Arith<Signed<u8>>>::neg(&a);
            assert!(r == signed);
            let mut expected = [false; 256];
            for x in concrete(lo, hi) {
                expected[x.wrapping_neg() as usize] = true;
            }
            for x in 0..=255u8 {
                assert_eq!(
                    r.contains(x),
                    expected[x as usize],
                    "neg [{lo},{hi}] at {x}"
                );
            }
        }
    }
}

#[test]
fn exhaustive_u8_singleton_add_sub() {
    for x in 0..=255u8 {
        for y in 0..=255u8 {
            let a = Wrapped::constant(x);
            let b = Wrapped::constant(y);
            let add = <Wrapped<u8> as Arith<Unsigned<u8>>>::add(&a, &b);
            let sub = <Wrapped<u8> as Arith<Unsigned<u8>>>::sub(&a, &b);
            assert!(add == Wrapped::constant(x.wrapping_add(y)));
            assert!(sub == Wrapped::constant(x.wrapping_sub(y)));
            assert!(
                <Wrapped<u8> as Arith<Signed<u8>>>::add(&a, &b)
                    == Wrapped::constant((x as i8).wrapping_add(y as i8) as u8)
            );
            assert!(
                <Wrapped<u8> as Arith<Signed<u8>>>::sub(&a, &b)
                    == Wrapped::constant((x as i8).wrapping_sub(y as i8) as u8)
            );
        }
    }
}

#[test]
fn sampled_u8_arithmetic_against_exact_concrete_sets() {
    // 64 arcs plus Top: sample abstract inputs; exhaust all concrete pairs
    // within each input. This is not all pairs of the 65,281 canonical arcs.
    let endpoints = [0, 1, 2, 126, 127, 128, 254, 255];
    let mut cases = vec![(Wrapped::<u8>::top(), (0..=255u8).collect::<Vec<_>>())];
    for lo in endpoints {
        for hi in endpoints {
            cases.push((Wrapped::new(lo, hi), concrete(lo, hi)));
        }
    }
    for (a, xs) in &cases {
        for (b, ys) in &cases {
            let add = <Wrapped<u8> as Arith<Unsigned<u8>>>::add(a, b);
            let sub = <Wrapped<u8> as Arith<Unsigned<u8>>>::sub(a, b);
            assert!(add == <Wrapped<u8> as Arith<Signed<u8>>>::add(a, b));
            assert!(sub == <Wrapped<u8> as Arith<Signed<u8>>>::sub(a, b));
            let mut sums = [false; 256];
            let mut differences = [false; 256];
            for &x in xs {
                for &y in ys {
                    sums[x.wrapping_add(y) as usize] = true;
                    differences[x.wrapping_sub(y) as usize] = true;
                }
            }
            for x in 0..=255u8 {
                assert_eq!(add.contains(x), sums[x as usize]);
                assert_eq!(sub.contains(x), differences[x as usize]);
            }
        }
    }
}

macro_rules! boundaries {
    ($test:ident, $w:ty) => {
        #[test]
        fn $test() {
            type D = Wrapped<$w>;
            let max = <$w>::MAX;
            let one = D::constant(1);
            let a = D::new(max - 1, max);
            assert!(<D as Arith<Unsigned<$w>>>::add(&a, &one) == D::new(max, 0));
            assert!(<D as Arith<Signed<$w>>>::neg(&a) == D::new(1, 2));
            assert!(<D as Arith<Unsigned<$w>>>::sub(&D::new(0, 1), &one) == D::new(max, 0));
            let half = max / 2 + 1;
            assert!(<D as Arith<Signed<$w>>>::neg(&D::constant(half)) == D::constant(half));
            assert!(
                <D as Arith<Signed<$w>>>::add(&D::constant(half - 1), &one) == D::constant(half)
            );
            assert!(<D as Arith<Unsigned<$w>>>::add(&D::new(0, half), &D::new(0, half)).is_top());
        }
    };
}
boundaries!(u8_boundaries, u8);
boundaries!(u16_boundaries, u16);
boundaries!(u32_boundaries, u32);
boundaries!(u64_boundaries, u64);
