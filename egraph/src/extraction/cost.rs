// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The cost type, and the width a build holds its values to.
//!
//! Arithmetic on [`Cost`] is exact: a result outside `i64` is held as an
//! arbitrary-precision integer, so no operation wraps, saturates, or panics. The width
//! is a property of the build ([`CostWidth`], `--cost-bits 32|64|big`): every value of
//! an order-encoded integer and every interpreted cost must lie in it, and one that
//! does not is a reported error naming the operation that produced it. Under
//! [`CostWidth::Big`] every value lies in it. A solver back end has its own range
//! (u64 weights for the totalizer, 32-bit integers for clingo), checked where a value
//! leaves for it.
//!
//! A value outside `i64` is interned in a process-wide, append-only table, so `Cost`
//! stays `Copy`, as the engine's big multiplicity does (`doc/goal-counted-multiplicities.md`,
//! decision 6). Interning makes equal values equal handles, so `Eq` and `Hash` are
//! derived; `Ord` compares values. An entry is never removed: the memory is that of the
//! distinct values beyond `i64` a process creates, which under the 32- and 64-bit
//! widths are only the values reported as errors.

use num_bigint::BigInt;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};

/// An exact integer cost. Inline in `i64`; interned beyond it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Cost(Repr);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Repr {
    Small(i64),
    /// Index into [`table`]; the value is outside `i64`, so the form is canonical.
    Big(u32),
}

#[derive(Default)]
struct Table {
    values: Vec<BigInt>,
    index: HashMap<BigInt, u32>,
}

fn table() -> &'static RwLock<Table> {
    static T: OnceLock<RwLock<Table>> = OnceLock::new();
    T.get_or_init(Default::default)
}

impl Cost {
    pub const ZERO: Cost = Cost(Repr::Small(0));
    pub const ONE: Cost = Cost(Repr::Small(1));

    pub const fn new(v: i64) -> Cost {
        Cost(Repr::Small(v))
    }

    /// `v`, inline when it fits `i64`.
    pub fn from_big(v: BigInt) -> Cost {
        if let Ok(s) = i64::try_from(&v) {
            return Cost(Repr::Small(s));
        }
        if let Some(&i) = table().read().unwrap().index.get(&v) {
            return Cost(Repr::Big(i));
        }
        let mut t = table().write().unwrap();
        if let Some(&i) = t.index.get(&v) {
            return Cost(Repr::Big(i));
        }
        // 2^32 distinct values beyond i64 exhaust memory first.
        let i = u32::try_from(t.values.len()).expect("fewer than 2^32 interned costs");
        t.values.push(v.clone());
        t.index.insert(v, i);
        Cost(Repr::Big(i))
    }

    pub fn to_big(self) -> BigInt {
        match self.0 {
            Repr::Small(v) => BigInt::from(v),
            Repr::Big(i) => table().read().unwrap().values[i as usize].clone(),
        }
    }

    pub fn to_i64(self) -> Option<i64> {
        match self.0 {
            Repr::Small(v) => Some(v),
            Repr::Big(_) => None,
        }
    }

    pub fn to_u64(self) -> Option<u64> {
        match self.0 {
            Repr::Small(v) => u64::try_from(v).ok(),
            Repr::Big(_) => u64::try_from(&self.to_big()).ok(),
        }
    }

    pub fn is_negative(self) -> bool {
        match self.0 {
            Repr::Small(v) => v < 0,
            Repr::Big(_) => self.to_big().sign() == num_bigint::Sign::Minus,
        }
    }

    pub fn abs(self) -> Cost {
        if self.is_negative() { -self } else { self }
    }

    /// Bits of the absolute value: 0 for 0.
    pub fn bits(self) -> u64 {
        match self.0 {
            Repr::Small(v) => 64 - u64::from(v.unsigned_abs().leading_zeros()),
            Repr::Big(_) => self.to_big().bits(),
        }
    }

    /// `self / o`, truncated toward zero, or `None` when `o` is 0.
    pub fn checked_div(self, o: Cost) -> Option<Cost> {
        if o == Cost::ZERO {
            return None;
        }
        // The i64 form fails only on MIN / -1, whose result is exact in the big form.
        let small = self
            .to_i64()
            .zip(o.to_i64())
            .and_then(|(a, b)| a.checked_div(b));
        Some(small.map_or_else(|| Cost::from_big(self.to_big() / o.to_big()), Cost::new))
    }

    /// `self % o`, with the sign of `self`, or `None` when `o` is 0.
    pub fn checked_rem(self, o: Cost) -> Option<Cost> {
        if o == Cost::ZERO {
            return None;
        }
        // The i64 form fails only on MIN % -1, whose result is exact in the big form.
        let small = self
            .to_i64()
            .zip(o.to_i64())
            .and_then(|(a, b)| a.checked_rem(b));
        Some(small.map_or_else(|| Cost::from_big(self.to_big() % o.to_big()), Cost::new))
    }

    /// A decimal integer, with an optional sign.
    pub fn parse(s: &str) -> Option<Cost> {
        s.parse::<BigInt>().ok().map(Cost::from_big)
    }

    fn big_op(self, o: Cost, f: impl Fn(BigInt, BigInt) -> BigInt) -> Cost {
        Cost::from_big(f(self.to_big(), o.to_big()))
    }
}

impl Default for Cost {
    fn default() -> Self {
        Cost::ZERO
    }
}

macro_rules! from_int {
    ($($t:ty),*) => {$(
        impl From<$t> for Cost {
            fn from(v: $t) -> Cost {
                match i64::try_from(v) {
                    Ok(s) => Cost(Repr::Small(s)),
                    Err(_) => Cost::from_big(BigInt::from(v)),
                }
            }
        }
    )*};
}
from_int!(i8, i16, i32, i64, u8, u16, u32, u64, usize, i128, u128);

impl TryFrom<Cost> for i64 {
    type Error = String;
    fn try_from(c: Cost) -> Result<i64, String> {
        c.to_i64().ok_or_else(|| format!("{c} is outside i64"))
    }
}

impl TryFrom<Cost> for u64 {
    type Error = String;
    fn try_from(c: Cost) -> Result<u64, String> {
        c.to_u64().ok_or_else(|| format!("{c} is outside u64"))
    }
}

impl From<BigInt> for Cost {
    fn from(v: BigInt) -> Cost {
        Cost::from_big(v)
    }
}

impl std::ops::Add for Cost {
    type Output = Cost;
    fn add(self, o: Cost) -> Cost {
        if let (Repr::Small(a), Repr::Small(b)) = (self.0, o.0)
            && let Some(r) = a.checked_add(b)
        {
            return Cost(Repr::Small(r));
        }
        self.big_op(o, |a, b| a + b)
    }
}

impl std::ops::Sub for Cost {
    type Output = Cost;
    fn sub(self, o: Cost) -> Cost {
        if let (Repr::Small(a), Repr::Small(b)) = (self.0, o.0)
            && let Some(r) = a.checked_sub(b)
        {
            return Cost(Repr::Small(r));
        }
        self.big_op(o, |a, b| a - b)
    }
}

impl std::ops::Mul for Cost {
    type Output = Cost;
    fn mul(self, o: Cost) -> Cost {
        if let (Repr::Small(a), Repr::Small(b)) = (self.0, o.0)
            && let Some(r) = a.checked_mul(b)
        {
            return Cost(Repr::Small(r));
        }
        self.big_op(o, |a, b| a * b)
    }
}

impl std::ops::Neg for Cost {
    type Output = Cost;
    fn neg(self) -> Cost {
        if let Repr::Small(a) = self.0
            && let Some(r) = a.checked_neg()
        {
            return Cost(Repr::Small(r));
        }
        Cost::from_big(-self.to_big())
    }
}

impl std::ops::AddAssign for Cost {
    fn add_assign(&mut self, o: Cost) {
        *self = *self + o;
    }
}

impl std::ops::SubAssign for Cost {
    fn sub_assign(&mut self, o: Cost) {
        *self = *self - o;
    }
}

impl std::iter::Sum for Cost {
    fn sum<I: Iterator<Item = Cost>>(it: I) -> Cost {
        it.fold(Cost::ZERO, |a, b| a + b)
    }
}

impl Ord for Cost {
    fn cmp(&self, o: &Cost) -> Ordering {
        match (self.0, o.0) {
            (Repr::Small(a), Repr::Small(b)) => a.cmp(&b),
            // A big value lies outside i64, so its sign orders it against any small one.
            (Repr::Small(_), Repr::Big(_)) => {
                if o.is_negative() {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
            (Repr::Big(_), Repr::Small(_)) => o.cmp(self).reverse(),
            (Repr::Big(i), Repr::Big(j)) if i == j => Ordering::Equal,
            (Repr::Big(_), Repr::Big(_)) => self.to_big().cmp(&o.to_big()),
        }
    }
}

impl PartialOrd for Cost {
    fn partial_cmp(&self, o: &Cost) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl PartialEq<i64> for Cost {
    fn eq(&self, o: &i64) -> bool {
        self.0 == Repr::Small(*o)
    }
}

impl PartialOrd<i64> for Cost {
    fn partial_cmp(&self, o: &i64) -> Option<Ordering> {
        Some(self.cmp(&Cost::new(*o)))
    }
}

impl std::fmt::Display for Cost {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Repr::Small(v) => write!(f, "{v}"),
            Repr::Big(_) => write!(f, "{}", self.to_big()),
        }
    }
}

impl std::fmt::Debug for Cost {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

/// The range a build's values must lie in: `--cost-bits 32|64|big`, signed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum CostWidth {
    W32,
    W64,
    /// No cap (the default): costs are limited only by the solver they are exported to.
    #[default]
    Big,
}

impl CostWidth {
    /// `32`, `64`, or `big`.
    pub fn parse(s: &str) -> Option<CostWidth> {
        match s {
            "32" => Some(CostWidth::W32),
            "64" => Some(CostWidth::W64),
            "big" => Some(CostWidth::Big),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            CostWidth::W32 => "32-bit",
            CostWidth::W64 => "64-bit",
            CostWidth::Big => "unbounded",
        }
    }

    pub fn contains(self, v: Cost) -> bool {
        match self {
            CostWidth::W32 => v.to_i64().is_some_and(|x| i32::try_from(x).is_ok()),
            CostWidth::W64 => v.to_i64().is_some(),
            CostWidth::Big => true,
        }
    }

    /// `v`, or an error naming `what` when it is outside the width.
    pub fn check(self, what: &str, v: Cost) -> Result<Cost, String> {
        if self.contains(v) {
            Ok(v)
        } else {
            Err(format!(
                "{what}: the value {v} is outside the {} cost range (--cost-bits)",
                self.name()
            ))
        }
    }
}

/// The exact weight of the windowed totalizer: no cap, every sum exact.
impl crate::extraction::totalizer::Weight for Cost {
    fn zero() -> Self {
        Cost::ZERO
    }
    fn checked_add(&self, o: &Self) -> Option<Self> {
        Some(*self + *o)
    }
    fn sub(&self, o: &Self) -> Self {
        *self - *o
    }
    fn max_cap() -> Option<Self> {
        None
    }
}
