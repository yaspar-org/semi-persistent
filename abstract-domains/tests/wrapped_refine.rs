// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks for Wrapped's participation in the shared reduced-product
//! protocol.  They use exhaustive u8 concretization, so a failed assertion
//! provides a concrete bit pattern witness.

use semi_persistent_abstract_domains::{
    facts::Facts,
    interval::Interval,
    lattice::{BotOr, Domain},
    reduce::{Product, Refine},
    wrapped::Wrapped,
};

type W8 = Wrapped<u8>;
type F8 = Facts<u8>;
type P8 = Product<W8, Interval<u8>>;

fn interval(lo: u8, hi: u8) -> Interval<u8> {
    Interval::new(lo, hi).expect("ordered u8 endpoints")
}

fn facts_contains(facts: &F8, x: u8) -> bool {
    let (lo, hi) = facts.interval().bounds();
    lo <= x && x <= hi
}

fn unwrap_value<D>(value: BotOr<D>) -> D {
    match value {
        BotOr::Val(value) => value,
        BotOr::Bot => panic!("a non-bottom domain value must export facts"),
    }
}

/// A non-wrapping arc can express its unsigned bounds exactly.  A wrapping arc
/// is the disjunction `[lo, MAX] U [0, hi]`, which the current unsigned-bound
/// fact channel cannot express, so it deliberately exports Top instead.
#[test]
fn wrapped_exports_sound_facts_for_every_u8_arc() {
    let mut cases = 0usize;
    for lo in 0..=u8::MAX {
        for hi in 0..=u8::MAX {
            let wrapped = W8::new(lo, hi);
            let facts = unwrap_value(wrapped.to_channel());

            for x in 0..=u8::MAX {
                assert!(
                    !wrapped.contains(x) || facts_contains(&facts, x),
                    "facts dropped {x} from Wrapped({lo}, {hi})"
                );
                if lo <= hi && lo.wrapping_sub(hi) != 1 {
                    assert_eq!(facts_contains(&facts, x), wrapped.contains(x));
                }
            }
            if lo > hi {
                assert!(
                    (0..=u8::MAX).all(|x| facts_contains(&facts, x)),
                    "wrapping arcs must conservatively export Top"
                );
            }
            cases += 1;
        }
    }
    assert_eq!(cases, 65_536);
}

/// Wrapped refinement meets the arc with the interval fact. It must keep every
/// jointly possible value, add none, and be stable under repeated reduction.
#[test]
fn wrapped_refinement_is_sound_and_stable() {
    let facts = [
        F8::from_interval(interval(0, 0)),
        F8::from_interval(interval(0, 10)),
        F8::from_interval(interval(10, 60)),
        F8::from_interval(interval(127, 128)),
        F8::from_interval(interval(250, 255)),
        <F8 as Domain>::top(),
    ];

    let endpoints = [0u8, 1, 10, 127, 128, 200, 250, 255];
    for &lo in &endpoints {
        for &hi in &endpoints {
            let wrapped = W8::new(lo, hi);
            for f in &facts {
                match wrapped.refine(f) {
                    BotOr::Bot => assert!(
                        (0..=u8::MAX).all(|x| !(wrapped.contains(x) && facts_contains(f, x)))
                    ),
                    BotOr::Val(refined) => {
                        let refined_twice = unwrap_value(refined.refine(f));
                        for x in 0..=u8::MAX {
                            assert!(
                                !(wrapped.contains(x) && facts_contains(f, x))
                                    || refined.contains(x),
                                "refinement lost joint value {x}"
                            );
                            assert!(
                                !refined.contains(x) || wrapped.contains(x),
                                "refinement added value {x}"
                            );
                            assert_eq!(
                                refined_twice.contains(x),
                                refined.contains(x),
                                "a second refinement changed membership of {x}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// Reduction through a shared channel preserves the product's exact concrete
/// meaning, including a Wrapped value that crosses the zero boundary.
#[test]
fn wrapped_interval_product_reduction_preserves_concretization() {
    let products = [
        P8 {
            a: W8::new(10, 30),
            b: interval(20, 40),
        },
        P8 {
            a: W8::new(250, 10),
            b: interval(0, 20),
        },
        P8 {
            a: W8::new(250, 10),
            b: interval(100, 200),
        },
    ];

    for product in products {
        let expected: Vec<bool> = (0..=u8::MAX)
            .map(|x| {
                product.a.contains(x) && {
                    let (lo, hi) = product.b.bounds();
                    lo <= x && x <= hi
                }
            })
            .collect();
        match product.reduce(3) {
            BotOr::Bot => assert!(expected.iter().all(|value| !value)),
            BotOr::Val(reduced) => {
                for x in 0..=u8::MAX {
                    let (lo, hi) = reduced.b.bounds();
                    assert_eq!(
                        reduced.a.contains(x) && lo <= x && x <= hi,
                        expected[x as usize]
                    );
                }
            }
        }
    }
}

#[test]
fn split_refinement_never_grows_and_product_converges() {
    let original = W8::new(250, 10);
    let split_fact = F8::from_interval(interval(1, 254));
    let refined = unwrap_value(original.refine(&split_fact));
    assert!(refined == original);
    for a in [W8::new(250, 5), W8::new(0, 5)] {
        let p = P8 {
            a,
            b: interval(0, 10),
        };
        let r = unwrap_value(p.reduce(2));
        assert!(r.a == W8::new(0, 5));
        assert_eq!(r.b.bounds(), (0, 5));
    }
}
