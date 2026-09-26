// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Production membership/normalization through AbstractValue. The helpers below
//! lift operations in the test harness only; no production lifted API is claimed.
#[allow(dead_code)]
#[path = "support/wrapped_oracle.rs"]
mod wrapped_oracle;
#[allow(dead_code)]
#[path = "support/wrapped_u32_cases.rs"]
mod wrapped_u32_cases;
use semi_persistent_abstract_domains::domains::{AbstractValue, Wrapped};
use wrapped_oracle::{Oracle, Repr};

macro_rules! harness {
    ($module:ident, $ty:ty, $bits:ty) => {
        mod $module {
            use super::*;
            type Value = AbstractValue<Wrapped<$ty>>;
            fn arc(lo: $ty, hi: $ty) -> Value {
                AbstractValue::NonBot(Wrapped::Arc { lo, hi })
            }
            #[allow(dead_code)] // Only u8/i8 exhaustive and u32 reference adapters use this.
            pub(super) fn from_repr(r: Repr) -> Value {
                match r {
                    Repr::Empty => AbstractValue::Bot,
                    Repr::Full => AbstractValue::NonBot(Wrapped::Top),
                    Repr::Arc { lo, hi } => arc(lo as $bits as $ty, hi as $bits as $ty),
                }
            }
            pub(super) fn contains(v: Value, x: $ty) -> bool {
                match v {
                    AbstractValue::Bot => false,
                    AbstractValue::NonBot(w) => w.contains(x),
                }
            }
            fn normalize(v: Value) -> Value {
                match v {
                    AbstractValue::Bot => AbstractValue::Bot,
                    AbstractValue::NonBot(w) => AbstractValue::NonBot(w.normalize()),
                }
            }
            #[allow(dead_code)] // Run only for genuine eight-bit implementations.
            pub(super) fn exhaustive() {
                let oracle = Oracle::new(8).unwrap();
                for r in oracle.raw_representations() {
                    let expected = oracle.values(r).unwrap();
                    let v = from_repr(r);
                    let n = normalize(v);
                    assert!(n == from_repr(oracle.normalize(r).unwrap()), "{r:?}");
                    assert!(normalize(n) == n);
                    for x in 0..256 {
                        let concrete = x as $bits as $ty;
                        assert_eq!(contains(v, concrete), expected.contains(x), "{r:?}, {x}");
                        assert_eq!(
                            contains(n, concrete),
                            expected.contains(x),
                            "normalized {r:?}, {x}"
                        );
                    }
                }
            }
            #[test]
            #[allow(clippy::clone_on_copy)]
            fn boundaries_and_wrapper() {
                let points: [$ty; 7] = [
                    <$ty>::MIN,
                    <$ty>::MIN.wrapping_add(1),
                    0,
                    1,
                    <$ty>::MAX.wrapping_sub(1),
                    <$ty>::MAX,
                    (1 as $bits).rotate_right(1) as $ty,
                ];
                let bot = AbstractValue::<Wrapped<$ty>>::Bot;
                let top = AbstractValue::NonBot(Wrapped::<$ty>::Top);
                assert!(normalize(bot) == bot);
                assert!(normalize(top) == top);
                assert!(bot.clone() == bot && top.clone() == top);
                for x in points {
                    assert!(!contains(bot, x));
                    assert!(contains(top, x));
                }
                for lo in points {
                    assert!(normalize(arc(lo, lo.wrapping_sub(1))) == top);
                    assert!(normalize(arc(lo, lo)) == arc(lo, lo));
                    for hi in points {
                        let value = arc(lo, hi);
                        assert!(value.clone() == value);
                        if let AbstractValue::NonBot(w) = value {
                            assert!(w.clone() == w);
                        }
                        let n = normalize(value);
                        let distance = (hi as $bits).wrapping_sub(lo as $bits);
                        assert!(n == if distance == <$bits>::MAX { top } else { value });
                        assert!(normalize(n) == n);
                        let mut probes = points.to_vec();
                        probes.extend([
                            lo.wrapping_sub(1),
                            lo.wrapping_add(1),
                            hi.wrapping_sub(1),
                            hi.wrapping_add(1),
                        ]);
                        for x in probes {
                            let expected = (x as $bits).wrapping_sub(lo as $bits) <= distance;
                            assert_eq!(contains(value, x), expected, "lo={lo},hi={hi},x={x}");
                            assert_eq!(
                                contains(n, x),
                                expected,
                                "normalized lo={lo},hi={hi},x={x}"
                            );
                        }
                    }
                }
            }
        }
    };
}
harness!(unsigned8, u8, u8);
harness!(signed8, i8, u8);
harness!(unsigned16, u16, u16);
harness!(signed16, i16, u16);
harness!(unsigned32, u32, u32);
harness!(signed32, i32, u32);
harness!(unsigned64, u64, u64);
harness!(signed64, i64, u64);
harness!(unsigned128, u128, u128);
harness!(signed128, i128, u128);

#[test]
fn exhaustive_u8() {
    unsigned8::exhaustive();
}
#[test]
fn exhaustive_i8() {
    signed8::exhaustive();
}
#[test]
fn production_u32_reference_cases() {
    wrapped_u32_cases::check_membership(|r, x| unsigned32::contains(unsigned32::from_repr(r), x))
        .unwrap();
}
