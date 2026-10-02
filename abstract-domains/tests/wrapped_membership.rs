// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_abstract_domains::{
    lattice::{BotOr, Domain},
    wrapped::Wrapped,
};
#[allow(dead_code)]
#[path = "support/wrapped_oracle.rs"]
mod wrapped_oracle;
use wrapped_oracle::{Oracle, Repr};

#[test]
fn exhaustive_u8_membership_and_canonical_constructors() {
    let oracle = Oracle::new(8).unwrap();
    let mut seen = std::collections::HashMap::<[u64; 4], Wrapped<u8>>::new();
    for lo in 0..=255u8 {
        for hi in 0..=255u8 {
            let w = Wrapped::new(lo, hi);
            let expected = oracle
                .values(Repr::Arc {
                    lo: lo as u32,
                    hi: hi as u32,
                })
                .unwrap();
            let mut bits = [0u64; 4];
            for x in 0..=255u8 {
                assert_eq!(w.contains(x), expected.contains(x as u32));
                // Signed and unsigned interpretations use the same carrier bits.
                assert_eq!(w.contains((x as i8) as u8), expected.contains(x as u32));
                if expected.contains(x as u32) {
                    bits[x as usize / 64] |= 1 << (x % 64);
                }
            }
            assert_eq!(w.is_top(), hi.wrapping_add(1) == lo);
            if w.is_top() {
                assert!(w == Wrapped::<u8>::top());
            }
            if let Some(previous) = seen.get(&bits) {
                assert!(*previous == w);
            } else {
                seen.insert(bits, w);
            }
        }
    }
    assert_eq!(seen.len(), 256 * 255 + 1);
}

#[test]
fn sampled_u8_domain_operations_against_sets() {
    let ps = [
        0u8, 1, 2, 3, 7, 8, 14, 15, 16, 127, 128, 129, 252, 253, 254, 255,
    ];
    let mut cases = vec![Wrapped::<u8>::top()];
    for lo in ps {
        for hi in ps {
            cases.push(Wrapped::new(lo, hi));
        }
    }
    for a in &cases {
        for b in &cases {
            let j = a.join(b);
            let m = a.meet(b);
            let w = a.widen(b);
            let mut intersect = false;
            let mut subset = true;
            for x in 0..=255u8 {
                let aa = a.contains(x);
                let bb = b.contains(x);
                subset &= !aa || bb;
                intersect |= aa && bb;
                if aa || bb {
                    assert!(j.contains(x));
                    assert!(w.contains(x));
                }
                if aa && bb {
                    assert!(matches!(&m,BotOr::Val(v) if v.contains(x)));
                }
            }
            assert_eq!(a.leq(b), subset);
            assert_eq!(matches!(m, BotOr::Bot), !intersect);
            let minimum_cover = |intersection: bool| {
                let present = |x: u8| {
                    if intersection {
                        a.contains(x) && b.contains(x)
                    } else {
                        a.contains(x) || b.contains(x)
                    }
                };
                if !(0..=255u8).any(present) {
                    return 0;
                }
                let mut gap = 0;
                let mut longest = 0;
                for n in 0..512 {
                    if present(n as u8) {
                        gap = 0;
                    } else {
                        gap += 1;
                        longest = longest.max(gap);
                    }
                }
                256 - longest
            };
            assert_eq!(
                (0..=255u8).filter(|&x| j.contains(x)).count(),
                minimum_cover(false)
            );
            let meet_size = match &m {
                BotOr::Bot => 0,
                BotOr::Val(v) => (0..=255u8).filter(|&x| v.contains(x)).count(),
            };
            assert_eq!(meet_size, minimum_cover(true));
            assert!(j == b.join(a));
            match (m, b.meet(a)) {
                (BotOr::Bot, BotOr::Bot) => {}
                (BotOr::Val(x), BotOr::Val(y)) => assert!(x == y),
                _ => panic!("asymmetric meet"),
            }
            if b.leq(a) {
                assert!(w == *a);
            } else {
                let n = (0..=255u8).filter(|&x| a.contains(x)).count();
                let nw = (0..=255u8).filter(|&x| w.contains(x)).count();
                assert!(nw >= (2 * n).min(256));
            }
        }
    }
}
#[test]
fn shared_bottom_lifts_and_split_meet() {
    let a = Wrapped::<u8>::new(250, 6);
    let b = Wrapped::<u8>::new(4, 252);
    let m = a.meet(&b);
    for x in [4, 5, 6, 250, 251, 252] {
        assert!(matches!(&m,BotOr::Val(w) if w.contains(x)));
    }
    let bot = BotOr::<Wrapped<u8>>::Bot;
    let v = BotOr::Val(a);
    assert!(bot.leq(&v));
    assert!(bot.meet(&v).is_bot());
    assert!(matches!(bot.join(&v),BotOr::Val(w) if w==Wrapped::new(250,6)));
}
macro_rules! boundaries {
    ($name:ident,$ty:ty) => {
        #[test]
        fn $name() {
            let p = [
                0,
                1,
                <$ty>::MAX / 2,
                <$ty>::MAX / 2 + 1,
                <$ty>::MAX - 1,
                <$ty>::MAX,
            ];
            for lo in p {
                for hi in p {
                    let w = Wrapped::<$ty>::new(lo, hi);
                    for x in p {
                        assert_eq!(w.contains(x), x.wrapping_sub(lo) <= hi.wrapping_sub(lo));
                    }
                    assert_eq!(w.is_top(), hi.wrapping_add(1) == lo);
                }
            }
            for x in p {
                let w = Wrapped::<$ty>::constant(x);
                for y in p {
                    assert_eq!(w.contains(y), x == y);
                }
            }
        }
    };
}
boundaries!(u8_boundaries, u8);
boundaries!(u16_boundaries, u16);
boundaries!(u32_boundaries, u32);
boundaries!(u64_boundaries, u64);
