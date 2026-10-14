// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive oracle for the real executable Congruence<u8>.
use semi_persistent_abstract_domains::congruence::Congruence;
use semi_persistent_abstract_domains::lattice::Domain;
use semi_persistent_abstract_domains::semantics::Unsigned;
use semi_persistent_abstract_domains::transfer::Arith;
use std::collections::HashMap;

type C = Congruence<u8>;

fn check_wf(c: &C) {
    let (m, r) = c.parts();
    assert!(m == 0 || (r < m && u16::from(r) + u16::from(m) <= 255));
    assert!(c.contains(r));
}

// Enumerate the raw progression using widened arithmetic, independently of
// the implementation's remainder-based membership check.
fn oracle(m: u8, r: u8) -> [u64; 4] {
    let mut bits = [0; 4];
    let mut x = if m == 0 {
        u16::from(r)
    } else {
        u16::from(r % m)
    };
    loop {
        bits[usize::from(x / 64)] |= 1u64 << (x % 64);
        if m == 0 {
            break;
        }
        x += u16::from(m);
        if x > 255 {
            break;
        }
    }
    bits
}

#[test]
fn constants_and_top() {
    let top = C::top();
    check_wf(&top);
    assert_eq!(top.parts(), (1, 0));
    for r in 0..=u8::MAX {
        let c = C::constant(r);
        check_wf(&c);
        assert_eq!(c.parts(), (0, r));
        for x in 0..=u8::MAX {
            assert_eq!(c.contains(x), x == r);
            assert!(top.contains(x));
        }
    }
}

#[test]
fn exhaustive_raw_inputs_membership_normalization_and_canonicity() {
    let mut representatives = HashMap::new();
    for m in 0..=u8::MAX {
        for r in 0..=u8::MAX {
            let c = C::new(m, r);
            check_wf(&c);
            let expected = oracle(m, r);
            let copied = c;
            assert!(copied.same(&c));
            let reconstructed = C::new(c.parts().0, c.parts().1);
            assert_eq!(reconstructed.parts(), c.parts());
            let mut actual = [0u64; 4];
            for x in 0..=u8::MAX {
                let has = c.contains(x);
                assert_eq!(
                    has,
                    expected[usize::from(x / 64)] & (1u64 << (x % 64)) != 0,
                    "m={m}, r={r}, x={x}"
                );
                if has {
                    actual[usize::from(x / 64)] |= 1u64 << (x % 64);
                }
            }
            let cardinality: u32 = actual.iter().map(|bits| bits.count_ones()).sum();
            assert_eq!(c.is_top(), cardinality == 256);
            assert_eq!(c.as_constant().is_some(), cardinality == 1);
            if let Some(value) = c.as_constant() {
                assert!(c.contains(value));
            }
            assert!(c.same(&reconstructed));
            assert_eq!(c.same(&C::top()), actual == [u64::MAX; 4]);
            assert_eq!(c.same(&C::constant(r)), actual == oracle(0, r));
            assert_eq!(c.same(&C::new(3, r)), actual == oracle(3, r));
            // Every canonical representation is reached by its own raw pair.
            // Identical sets must always yield identical canonical pairs.
            if let Some(previous) = representatives.insert(actual, c.parts()) {
                assert_eq!(previous, c.parts(), "duplicate gamma for m={m}, r={r}");
            }
        }
    }
    // 256 singletons + sum(min(m, 256-m), m=1..255) progressions.
    assert_eq!(representatives.len(), 16_640);
}

#[test]
fn finite_width_singleton_and_second_member_boundary() {
    assert_eq!(C::new(201, 200).parts(), C::constant(200).parts());
    assert_eq!(C::new(128, 127).parts(), (128, 127));
    assert!(C::new(128, 127).contains(255));
    assert_eq!(C::new(129, 127).parts(), (0, 127));
    assert_eq!(C::new(255, 0).parts(), (255, 0));
    assert!(C::new(255, 0).contains(255));
    assert_eq!(C::new(255, 255).parts(), (255, 0));
    assert_eq!(C::new(4, 5).parts(), (4, 1));
    assert_eq!(C::new(1, 255).parts(), C::top().parts());
}

#[test]
fn generic_widths_and_width_aliases() {
    macro_rules! check {
        ($word:ty, $alias:ty) => {{
            let c = Congruence::<$word>::new(<$word>::MAX, <$word>::MAX - 1);
            assert_eq!(c.parts(), (0, <$word>::MAX - 1));
            let c: $alias = Congruence::<$word>::new(<$word>::MAX, 0);
            assert!(c.contains(0));
            assert!(c.contains(<$word>::MAX));
            assert!(!c.contains(1));
        }};
    }
    use semi_persistent_abstract_domains::domains::{d8, d16, d32, d64};
    check!(u8, d8::Congruence);
    check!(u16, d16::Congruence);
    check!(u32, d32::Congruence);
    check!(u64, d64::Congruence);
}

macro_rules! core_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::congruence::Congruence;
            type C = Congruence<$uint>;
            let max = <$uint>::MAX;
            let top = C::top();
            for x in [0, 1, max] {
                let singleton = C::constant(x);
                assert!(singleton.contains(x));
                assert!(!singleton.contains(x.wrapping_add(1)));
                assert!(singleton.refines(&top));
                assert!(!top.refines(&singleton));
            }
            let even = C::new(2, 0);
            let odd = C::new(2, 1);
            let four = C::new(4, 0);
            assert!(four.refines(&even));
            assert!(!even.refines(&four));
            assert!(!even.refines(&odd));
            assert!(even.refines(&even));

            let finite_singleton = C::new(max, 1);
            assert!(finite_singleton.refines(&C::constant(1)));
            assert!(C::constant(1).refines(&finite_singleton));
            assert!(finite_singleton.refines(&odd));
            let two_values = C::new(max, 0);
            assert!(!two_values.refines(&C::constant(0)));
            assert!(!two_values.refines(&even));

            for m in [0, 1, 2, max] {
                for r in [0, 1, max] {
                    let normalized = C::new(m, r);
                    let nr = if m == 0 { r } else { r % m };
                    let nm = if m != 0 && m > max - nr { 0 } else { m };
                    assert_eq!(normalized.parts(), (nm, nr));
                    let twice = C::new(nm, nr);
                    assert_eq!(twice.parts(), normalized.parts());
                    for x in [0, 1, 2, max - 1, max] {
                        assert_eq!(
                            normalized.contains(x),
                            if m == 0 { x == r } else { x % m == r % m }
                        );
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
    use semi_persistent_abstract_domains::congruence::Congruence;
    type C = Congruence<u8>;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = C::new(m, r);
            let values: Vec<bool> = (0..=u8::MAX)
                .map(|x| if m == 0 { x == r } else { x % m == r % m })
                .collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let subset = av.iter().zip(bv).all(|(x, y)| !x || *y);
            assert_eq!(
                a.refines(b),
                subset,
                "({}, {}) refines ({}, {})",
                a.parts().0,
                a.parts().1,
                b.parts().0,
                b.parts().1
            );
        }
    }
}

use semi_persistent_abstract_domains::lattice::BotOr;

fn meet_value<W>(result: BotOr<Congruence<W>>) -> Congruence<W> {
    match result {
        BotOr::Val(value) => value,
        BotOr::Bot => panic!("expected nonempty intersection"),
    }
}

macro_rules! meet_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::congruence::Congruence;
            type C = Congruence<$uint>;
            let a = C::new(6, 1);
            let b = C::new(4, 3);
            let merged = meet_value(a.meet(&b));
            assert_eq!(merged.parts(), (12, 7));
            assert!(matches!(a.meet(&C::new(4, 2)), BotOr::Bot));
            let top = C::top();
            for (left, right) in [(&a, &top), (&top, &a), (&a, &a)] {
                let result = meet_value(left.meet(right));
                assert_eq!(result.parts(), a.parts());
            }
            for x in [0, 7] {
                let singleton = C::constant(x);
                for result in [a.meet(&singleton), singleton.meet(&a)] {
                    if x == 7 {
                        let r = meet_value(result);
                        assert_eq!(r.parts(), (0, x));
                    } else {
                        assert!(matches!(result, BotOr::Bot));
                    }
                }
                assert!(meet_value(singleton.meet(&singleton)).contains(x));
                assert!(matches!(singleton.meet(&C::constant(x + 1)), BotOr::Bot));
            }
            let max = <$uint>::MAX;
            for x in [0, 1, max] {
                let left = C::new(max, x % max);
                let right = C::new(max - 1, x % (max - 1));
                for result in [left.meet(&right), right.meet(&left)] {
                    let r = meet_value(result);
                    assert_eq!(r.parts(), (0, x));
                }
            }
            let left = C::new(max, max - 1);
            let right = C::new(max - 1, max - 2);
            assert!(matches!(left.meet(&right), BotOr::Bot));
            assert!(matches!(right.meet(&left), BotOr::Bot));
        }
    };
}

meet_cases!(meet_u8, d8, u8);
meet_cases!(meet_u16, d16, u16);
meet_cases!(meet_u32, d32, u32);
meet_cases!(meet_u64, d64, u64);

#[test]
fn meet_matches_finite_u8_sets() {
    use semi_persistent_abstract_domains::congruence::Congruence;
    type C = Congruence<u8>;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = C::new(m, r);
            let values: Vec<bool> = (0..=u8::MAX)
                .map(|x| if m == 0 { x == r } else { x % m == r % m })
                .collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let result = a.meet(b);
            if let BotOr::Val(r) = &result {
                let (m, r) = r.parts();
                assert!(m == 0 || (r < m && u16::from(r) + u16::from(m) <= 255));
            }
            let mut nonempty = false;
            for x in 0..=u8::MAX {
                let expected = av[x as usize] && bv[x as usize];
                nonempty |= expected;
                assert_eq!(
                    matches!(&result, BotOr::Val(r) if r.contains(x)),
                    expected,
                    "({}, {}) meet ({}, {}) at {x}",
                    a.parts().0,
                    a.parts().1,
                    b.parts().0,
                    b.parts().1
                );
            }
            assert_eq!(matches!(result, BotOr::Val(_)), nonempty);
        }
    }
}

macro_rules! join_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::congruence::Congruence;
            type C = Congruence<$uint>;
            let a = C::new(4, 1);
            let b = C::new(6, 3);
            for (left, right) in [(&a, &b), (&b, &a)] {
                let r = left.join(right);
                assert_eq!(r.parts(), (2, 1));
            }
            let same = a.join(&a);
            assert_eq!(same.parts(), (4, 1));
            let top = C::top();
            for (left, right) in [(&a, &top), (&top, &a)] {
                let r = left.join(right);
                assert_eq!(r.parts(), (1, 0));
            }
            let one = C::constant(1);
            let five = C::constant(5);
            let r = one.join(&five);
            assert_eq!(r.parts(), (4, 1));
            assert_eq!(one.join(&one).parts().0, 0);
            let r = a.join(&five);
            assert_eq!(r.parts(), (4, 1));
            let r = a.join(&C::constant(2));
            assert_eq!(r.parts(), (1, 0));

            let max = <$uint>::MAX;
            let finite_one = C::new(max, 1);
            let r = finite_one.join(&five);
            assert_eq!(r.parts(), (4, 1));
            let r = finite_one.join(&one);
            assert_eq!(r.parts(), (0, 1));
            let r = C::constant(0).join(&C::constant(max));
            assert_eq!(r.parts(), (max, 0));
            let r = C::constant(max - 1).join(&C::constant(max));
            assert_eq!(r.parts(), (1, 0));
        }
    };
}

join_cases!(join_u8, d8, u8);
join_cases!(join_u16, d16, u16);
join_cases!(join_u32, d32, u32);
join_cases!(join_u64, d64, u64);

#[test]
fn join_covers_finite_u8_sets() {
    use semi_persistent_abstract_domains::congruence::Congruence;
    type C = Congruence<u8>;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = C::new(m, r);
            let values: Vec<bool> = (0..=u8::MAX)
                .map(|x| if m == 0 { x == r } else { x % m == r % m })
                .collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let result = a.join(b);
            let (m, r) = result.parts();
            assert!(m == 0 || (r < m && u16::from(r) + u16::from(m) <= 255));
            let reverse = b.join(a);
            assert_eq!(result.parts(), reverse.parts());
            for x in 0..=u8::MAX {
                if av[x as usize] || bv[x as usize] {
                    assert!(
                        result.contains(x),
                        "({}, {}) join ({}, {}) misses {x}",
                        a.parts().0,
                        a.parts().1,
                        b.parts().0,
                        b.parts().1
                    );
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
            use semi_persistent_abstract_domains::congruence::Congruence;
            type C = Congruence<$uint>;
            let max = <$uint>::MAX;
            for (x, y) in [(0, 0), (1, 2), (max, 1), (max, max)] {
                let r = C::constant(x).add(&C::constant(y));
                assert_eq!(r.parts(), (0, x.wrapping_add(y)));
            }
            let finite_one = C::new(max, 1);
            let r = finite_one.add(&C::constant(max));
            assert_eq!(r.parts(), (0, 0));
            let odd = C::new(2, 1);
            let r = odd.add(&odd);
            assert_eq!(r.parts(), (2, 0));
            let four = C::new(4, 3);
            let r = four.add(&C::constant(2));
            assert_eq!(r.parts(), (4, 1));
            let top = C::top();
            for (a, b) in [(&odd, &top), (&top, &odd)] {
                let r = a.add(b);
                assert_eq!(r.parts(), (1, 0));
            }
            let multiples_of_three = C::new(3, 0);
            let r = multiples_of_three.add(&multiples_of_three);
            assert_eq!(r.parts(), (1, 0));
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
    use semi_persistent_abstract_domains::congruence::Congruence;
    type C = Congruence<u8>;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = C::new(m, r);
            let values: Vec<u8> = (0..=u8::MAX)
                .filter(|x| if m == 0 { *x == r } else { x % m == r % m })
                .collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let result = a.add(b);
            let (m, r) = result.parts();
            assert!(m == 0 || (r < m && u16::from(r) + u16::from(m) <= 255));
            let reverse = b.add(a);
            assert_eq!(result.parts(), reverse.parts());
            for &x in av {
                for &y in bv {
                    assert!(
                        result.contains(x.wrapping_add(y)),
                        "({}, {}) + ({}, {}) misses {x} + {y}",
                        a.parts().0,
                        a.parts().1,
                        b.parts().0,
                        b.parts().1
                    );
                }
            }
        }
    }
}

macro_rules! trait_cases {
    ($name:ident, $word:ty) => {
        #[test]
        fn $name() {
            type C = Congruence<$word>;
            let max = <$word>::MAX;
            let stride = max / 2 + 2; // odd, with exactly two represented members
            let a = C::new(stride, 0);
            let one = C::constant(1);
            let top = <C as Domain>::top();
            assert!(Domain::leq(&a, &top));
            assert!(!Domain::leq(&top, &a));
            assert_eq!(Domain::dup(&a).parts(), a.parts());
            assert_eq!(Domain::join(&a, &a).parts(), a.parts());
            assert_eq!(Domain::widen(&a, &one).parts(), a.join(&one).parts());
            assert!(matches!(Domain::meet(&a, &one), BotOr::Bot));
            assert_eq!(meet_value(Domain::meet(&a, &top)).parts(), a.parts());

            // Keeping the odd stride is strictly more precise than gcd(stride, 2^N).
            let precise = <C as Arith<Unsigned<$word>>>::add(&a, &one);
            assert_eq!(precise.parts(), (stride, 1));
            let edge = C::constant(max - stride);
            assert_eq!(
                <C as Arith<Unsigned<$word>>>::add(&a, &edge).parts(),
                (stride, max - stride)
            );
            let wraps = C::constant(max - stride + 1);
            assert_eq!(
                <C as Arith<Unsigned<$word>>>::add(&a, &wraps).parts(),
                (1, 0)
            );
            let odd = C::new(2, 1);
            assert_eq!(<C as Arith<Unsigned<$word>>>::neg(&odd).parts(), (2, 1));
            assert_eq!(
                <C as Arith<Unsigned<$word>>>::sub(&odd, &odd).parts(),
                (2, 0)
            );
            for x in [0, 1, max / 2, max - 1, max] {
                let x_class = C::constant(x);
                assert_eq!(
                    <C as Arith<Unsigned<$word>>>::neg(&x_class).parts(),
                    (0, x.wrapping_neg())
                );
                for y in [0, 1, max] {
                    assert_eq!(
                        <C as Arith<Unsigned<$word>>>::sub(&x_class, &C::constant(y)).parts(),
                        (0, x.wrapping_sub(y))
                    );
                }
            }
            let bottom: BotOr<C> = BotOr::Bot;
            let value = BotOr::Val(a);
            assert!(bottom.leq(&value));
            assert!(!value.leq(&bottom));
            assert!(value.meet(&bottom).is_bot());
            assert_eq!(meet_value(bottom.join(&value)).parts(), (stride, 0));
            assert_eq!(meet_value(bottom.widen(&value)).parts(), (stride, 0));
        }
    };
}

trait_cases!(traits_u8, u8);
trait_cases!(traits_u16, u16);
trait_cases!(traits_u32, u32);
trait_cases!(traits_u64, u64);

// Enumerate each canonical nonempty set once, without computing any GCD/CRT.
fn canonical_classes() -> Vec<(C, [u64; 4])> {
    let mut classes = Vec::new();
    for r in 0..=u8::MAX {
        classes.push((C::constant(r), oracle(0, r)));
    }
    for m in 1..=u8::MAX {
        for r in 0..m.min((256u16 - u16::from(m)) as u8) {
            classes.push((C::new(m, r), oracle(m, r)));
        }
    }
    assert_eq!(classes.len(), 16_640);
    classes
}

fn bit_subset(a: &[u64; 4], b: &[u64; 4]) -> bool {
    (0..4).all(|i| a[i] & !b[i] == 0)
}

fn members(bits: &[u64; 4]) -> impl Iterator<Item = u8> + '_ {
    (0..=u8::MAX).filter(|x| bits[usize::from(x / 64)] & (1u64 << (x % 64)) != 0)
}

#[test]
fn every_canonical_u8_class_maximum_negation_and_addition_boundaries() {
    for (a, bits) in canonical_classes() {
        let values: Vec<_> = members(&bits).collect();
        let last = *values.last().unwrap();
        assert_eq!(a.max_member(), last);
        let negative = <C as Arith<Unsigned<u8>>>::neg(&a);
        check_wf(&negative);
        for &x in &values {
            assert!(
                negative.contains(x.wrapping_neg()),
                "neg {:?}: {x}",
                a.parts()
            );
        }
        // Every class: zero shift, largest non-wrapping shift, first wrapping
        // shift (where it exists), and MAX. Check every represented operand.
        for y in [0, 255 - last, (255 - last).saturating_add(1), 255] {
            let b = C::constant(y);
            let sum = <C as Arith<Unsigned<u8>>>::add(&a, &b);
            check_wf(&sum);
            if y <= 255 - last {
                let (m, r) = a.parts();
                let expected = C::new(m, r + y);
                assert_eq!(
                    sum.parts(),
                    expected.parts(),
                    "no-wrap {:?} + {y}",
                    a.parts()
                );
            }
            for &x in &values {
                assert!(
                    sum.contains(x.wrapping_add(y)),
                    "{:?} + {y}: {x}",
                    a.parts()
                );
            }
        }
    }
}

#[test]
fn exhaustive_u8_constant_arithmetic() {
    for x in 0..=u8::MAX {
        for y in 0..=u8::MAX {
            let a = C::constant(x);
            let b = C::constant(y);
            assert_eq!(
                <C as Arith<Unsigned<u8>>>::add(&a, &b).parts(),
                (0, x.wrapping_add(y))
            );
            assert_eq!(
                <C as Arith<Unsigned<u8>>>::sub(&a, &b).parts(),
                (0, x.wrapping_sub(y))
            );
        }
    }
}

#[test]
fn trait_operations_against_finite_sets_and_all_canonical_upper_bounds() {
    let all = canonical_classes();
    let mut inputs = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            inputs.push((C::new(m, r), oracle(m, r)));
        }
    }
    // Precompute containing sets by concrete bitset inclusion, independently
    // of refines/join. Intersect these lists to check *every* possible upper
    // bound of each input pair without a cubic membership scan.
    let uppers: Vec<Vec<usize>> = inputs
        .iter()
        .map(|(_, bits)| {
            all.iter()
                .enumerate()
                .filter_map(|(i, (_, upper))| bit_subset(bits, upper).then_some(i))
                .collect()
        })
        .collect();
    for (i, (a, av)) in inputs.iter().enumerate() {
        let xs: Vec<_> = members(av).collect();
        for (b, bv) in &inputs {
            assert_eq!(Domain::leq(a, b), bit_subset(av, bv));
            let join = Domain::join(a, b);
            let joined = oracle(join.parts().0, join.parts().1);
            check_wf(&join);
            assert!(bit_subset(av, &joined) && bit_subset(bv, &joined));
            for &k in &uppers[i] {
                if bit_subset(bv, &all[k].1) {
                    assert!(
                        bit_subset(&joined, &all[k].1),
                        "LUB {:?}, {:?}",
                        a.parts(),
                        b.parts()
                    );
                }
            }
            assert_eq!(Domain::widen(a, b).parts(), join.parts());
            let meet = Domain::meet(a, b);
            let intersection = std::array::from_fn(|k| av[k] & bv[k]);
            match meet {
                BotOr::Bot => assert_eq!(intersection, [0; 4]),
                BotOr::Val(c) => {
                    check_wf(&c);
                    assert_eq!(oracle(c.parts().0, c.parts().1), intersection);
                }
            }
            let sum = <C as Arith<Unsigned<u8>>>::add(a, b);
            let difference = <C as Arith<Unsigned<u8>>>::sub(a, b);
            check_wf(&sum);
            check_wf(&difference);
            let ys: Vec<_> = members(bv).collect();
            for &x in &xs {
                for &y in &ys {
                    assert!(sum.contains(x.wrapping_add(y)));
                    assert!(
                        difference.contains(x.wrapping_sub(y)),
                        "{:?} - {:?}: {x} - {y}",
                        a.parts(),
                        b.parts()
                    );
                }
            }
        }
    }
}

core_cases!(core_u128, d128, u128);
meet_cases!(meet_u128, d128, u128);
join_cases!(join_u128, d128, u128);
add_cases!(add_u128, d128, u128);
trait_cases!(traits_u128, u128);

#[test]
fn wrapping_precision_regressions() {
    // Every nonzero member wraps in the same direction under negation.
    assert_eq!(C::new(3, 1).neg().parts(), (3, 0));
    assert_eq!(C::new(5, 3).neg().parts(), (5, 3));
    assert_eq!(C::new(3, 1).sub(&C::constant(1)).parts(), (3, 0));
    assert_eq!(C::constant(0).sub(&C::new(3, 1)).parts(), (3, 0));
    assert_eq!(C::new(3, 1).add(&C::constant(255)).parts(), (3, 0));
    assert_eq!(C::new(5, 3).add(&C::constant(255)).parts(), (5, 2));
    // Zero itself must not be mistaken for a wrapping negative input.
    assert_eq!(C::constant(0).neg().parts(), (0, 0));
    assert_eq!(C::new(3, 0).neg().parts(), (1, 0));
    assert_eq!(C::new(3, 0).add(&C::constant(1)).parts(), (1, 0));
}

fn concrete_hull(values: impl IntoIterator<Item = u8>) -> (u8, u8) {
    let mut values = values.into_iter();
    let first = values.next().unwrap();
    let mut stride = 0;
    for x in values {
        let mut delta = x.abs_diff(first);
        while delta != 0 {
            (stride, delta) = (delta, stride % delta);
        }
    }
    (stride, if stride == 0 { first } else { first % stride })
}

#[test]
fn exhaustive_u8_nonzero_negation_precision() {
    for (a, bits) in canonical_classes() {
        if !a.contains(0) {
            assert_eq!(
                a.neg().parts(),
                concrete_hull(members(&bits).map(u8::wrapping_neg)),
                "neg {:?}",
                a.parts()
            );
        }
    }
}

#[test]
fn exhaustive_u8_classes_with_every_constant_arithmetic() {
    // All 16,640 canonical u8 classes x all 256 constants, in both subtraction
    // orders. This covers every concrete member, not just endpoints.
    for (a, bits) in canonical_classes() {
        let values: Vec<_> = members(&bits).collect();
        let first = values[0];
        let last = *values.last().unwrap();
        for y in 0..=u8::MAX {
            let b = C::constant(y);
            let sum = a.add(&b);
            let difference = a.sub(&b);
            let reverse = b.sub(&a);
            check_wf(&sum);
            check_wf(&difference);
            check_wf(&reverse);
            assert_eq!(sum.parts(), b.add(&a).parts());
            for &x in &values {
                assert!(
                    sum.contains(x.wrapping_add(y)),
                    "{:?} + {y}: {x}",
                    a.parts()
                );
                assert!(
                    difference.contains(x.wrapping_sub(y)),
                    "{:?} - {y}: {x}",
                    a.parts()
                );
                assert!(
                    reverse.contains(y.wrapping_sub(x)),
                    "{y} - {:?}: {x}",
                    a.parts()
                );
            }
            // When the concrete range stays on one side of the boundary,
            // compare precision against an independent best-class oracle.
            if last.checked_add(y).is_some() || first.checked_add(y).is_none() {
                assert_eq!(
                    sum.parts(),
                    concrete_hull(values.iter().map(|x| x.wrapping_add(y)))
                );
            }
            if first >= y || last < y {
                assert_eq!(
                    difference.parts(),
                    concrete_hull(values.iter().map(|x| x.wrapping_sub(y)))
                );
            }
            if y >= last || y < first {
                assert_eq!(
                    reverse.parts(),
                    concrete_hull(values.iter().map(|x| y.wrapping_sub(*x)))
                );
            }
        }
    }
}

#[test]
fn u128_arithmetic_boundaries_and_precision() {
    type C128 = Congruence<u128>;
    let max = u128::MAX;
    let half = 1u128 << 127;
    for x in [0, 1, 255, 1u128 << 64, half - 1, half, max - 1, max] {
        let a = C128::constant(x);
        assert_eq!(
            <C128 as Arith<Unsigned<u128>>>::neg(&a).parts(),
            (0, x.wrapping_neg())
        );
        for y in [0, 1, 1u128 << 64, half, max] {
            let b = C128::constant(y);
            assert_eq!(
                <C128 as Arith<Unsigned<u128>>>::add(&a, &b).parts(),
                (0, x.wrapping_add(y))
            );
            assert_eq!(
                <C128 as Arith<Unsigned<u128>>>::sub(&a, &b).parts(),
                (0, x.wrapping_sub(y))
            );
        }
    }
    assert_eq!(C128::new(3, 1).neg().parts(), (3, 0));
    assert_eq!(C128::new(3, 1).add(&C128::constant(max)).parts(), (3, 0));
    assert_eq!(C128::new(3, 1).sub(&C128::constant(1)).parts(), (3, 0));
    assert_eq!(C128::new(half, 0).max_member(), half);
    assert_eq!(
        C128::new(half, 0).add(&C128::new(half, 0)).parts(),
        (half, 0)
    );
    assert_eq!(
        C128::new(half, 0).sub(&C128::new(half, 0)).parts(),
        (half, 0)
    );
    assert_eq!(C128::new(half, 0).neg().parts(), (half, 0));
}
