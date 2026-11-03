// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The engine-facing names for abstract-domain carriers and fields.
//!
//! This module is deliberately the only place where the e-graph's textual
//! names are translated into abstract-domain identifiers.  The lookup tables
//! are ordinary Rust: they are checked exhaustively by runtime tests, while
//! the value and transfer layer added below them is verified in Verus.

use crate::bool4::Bool4;
use crate::facts::Facts;
use crate::facts_z::FactsZ;
use crate::ibig::IBig;
use crate::interval::Interval;
use crate::interval_z::{Hi, IntervalZ, Lo};
use crate::lattice::{BotOr, Domain};
use crate::semantics::{Euclid, Unsigned};
use crate::transfer::{Arith, DivRem, Mul};
use crate::word::Word;

/// Native bit-vector widths supported by `Word`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Width {
    W8,
    W16,
    W32,
    W64,
    W128,
}

impl Width {
    /// Width in bits.
    pub const fn bits(self) -> u32 {
        match self {
            Self::W8 => 8,
            Self::W16 => 16,
            Self::W32 => 32,
            Self::W64 => 64,
            Self::W128 => 128,
        }
    }
}

/// A concrete carrier understood by the registry.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Carrier {
    Bool,
    Int,
    BitVec(Width),
    /// A syntactically valid bit-vector width for which no native `Word`
    /// instance exists yet.  Its analysis value is always top.
    TopOnly {
        bits: u32,
    },
}

/// Returns a native carrier when `bits` has a `Word` implementation; all
/// other positive widths are represented as a top-only carrier.
pub const fn carrier_of_bitvec(bits: u32) -> Option<Carrier> {
    match bits {
        0 => None,
        8 => Some(Carrier::BitVec(Width::W8)),
        16 => Some(Carrier::BitVec(Width::W16)),
        32 => Some(Carrier::BitVec(Width::W32)),
        64 => Some(Carrier::BitVec(Width::W64)),
        128 => Some(Carrier::BitVec(Width::W128)),
        _ => Some(Carrier::TopOnly { bits }),
    }
}

/// A per-sort mask over the fields of its fact record.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
pub struct DomainSet(u8);

impl DomainSet {
    pub const EMPTY: Self = Self(0);

    pub const fn empty() -> Self {
        Self::EMPTY
    }

    pub const fn from_bit(bit: u8) -> Self {
        Self(1 << bit)
    }

    pub const fn contains(self, bit: u8) -> bool {
        self.0 & (1 << bit) != 0
    }

    pub const fn insert(self, bit: u8) -> Self {
        Self(self.0 | (1 << bit))
    }

    pub const fn bits(self) -> u8 {
        self.0
    }
}

/// Why a domain name cannot be selected for a carrier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NameError {
    Unknown,
    WrongCarrier(Carrier),
}

/// Resolves every domain name in the project plan, including planned fields.
/// The bit is stable even when the corresponding field is not implemented.
pub fn domain_bit(carrier: Carrier, name: &str) -> Result<u8, NameError> {
    match carrier {
        Carrier::Int => match name {
            "interval" => Ok(0),
            "congruence" => Ok(1),
            "nonzero" => Ok(2),
            "ubounds" | "sbounds" | "bits" | "bool" => Err(NameError::WrongCarrier(carrier)),
            _ => Err(NameError::Unknown),
        },
        Carrier::BitVec(_) => match name {
            "ubounds" => Ok(0),
            "sbounds" => Ok(1),
            "congruence" => Ok(2),
            "bits" => Ok(3),
            "interval" | "nonzero" | "bool" => Err(NameError::WrongCarrier(carrier)),
            _ => Err(NameError::Unknown),
        },
        Carrier::Bool => match name {
            "bool" => Ok(0),
            "interval" | "congruence" | "nonzero" | "ubounds" | "sbounds" | "bits" => {
                Err(NameError::WrongCarrier(carrier))
            }
            _ => Err(NameError::Unknown),
        },
        Carrier::TopOnly { .. } => match name {
            "ubounds" | "sbounds" | "congruence" | "bits" => Ok(match name {
                "ubounds" => 0,
                "sbounds" => 1,
                "congruence" => 2,
                _ => 3,
            }),
            "interval" | "nonzero" | "bool" => Err(NameError::WrongCarrier(carrier)),
            _ => Err(NameError::Unknown),
        },
    }
}

/// Whether the backing field for a resolved bit exists today.
pub const fn domain_available(carrier: Carrier, bit: u8) -> bool {
    match carrier {
        Carrier::Bool => bit == 0,
        Carrier::Int => bit == 0,
        Carrier::BitVec(_) => bit == 0,
        Carrier::TopOnly { .. } => false,
    }
}

/// The enabled domains for a sort when no `:domains` annotation is present.
pub const fn default_domains(carrier: Carrier) -> DomainSet {
    match carrier {
        Carrier::Bool | Carrier::Int | Carrier::BitVec(_) => DomainSet::from_bit(0),
        Carrier::TopOnly { .. } => DomainSet::EMPTY,
    }
}

/// An in-memory registry value.
///
/// This is intentionally an ergonomic Rust enum rather than the compact
/// class-storage representation. `encode` and `decode` will be the only
/// boundary that exposes its fixed-size byte representation to the e-graph
/// storage layer.
pub enum Value {
    Bool(Bool4),
    Int(FactsZ),
    Bv8(Facts<u8>),
    Bv16(Facts<u16>),
    Bv32(Facts<u32>),
    Bv64(Facts<u64>),
    Bv128(Facts<u128>),
    /// The unique value for a top-only carrier.
    Top,
}

/// A registry operation either finds a contradictory set of facts or returns
/// one non-bottom value. It is the dynamic-carrier counterpart of
/// `BotOr<D>`; `Value` itself cannot implement `Domain` because its concrete
/// type depends on the carrier.
pub enum RegistryResult {
    Bot,
    Val(Value),
}

/// The operands retained by a backward transfer. `arity` identifies the
/// meaningful prefix of `values`; unused positions contain a top value and
/// keep the engine-facing representation fixed-size.
pub struct BackwardResult {
    pub values: [Value; 3],
    pub arity: usize,
}

/// A concrete singleton reported to the e-graph for a derived merge.
pub enum Const {
    Bool(bool),
    Int(IBig),
    Bv(u128),
}

/// Number of bytes in the class-layer entry for one carrier.
///
/// The current records contain only their available interval field: two
/// native words for a bit-vector and two `i64` bounds for integers.
pub const fn entry_size(carrier: Carrier) -> usize {
    match carrier {
        Carrier::Bool => 1,
        Carrier::Int => 16,
        Carrier::BitVec(width) => (width.bits() / 4) as usize,
        Carrier::TopOnly { .. } => 0,
    }
}

/// The least precise non-bottom analysis value for a carrier.
pub fn top(carrier: Carrier) -> Value {
    match carrier {
        Carrier::Bool => Value::Bool(<Bool4 as Domain>::top()),
        Carrier::Int => Value::Int(<FactsZ as Domain>::top()),
        Carrier::BitVec(Width::W8) => Value::Bv8(<Facts<u8> as Domain>::top()),
        Carrier::BitVec(Width::W16) => Value::Bv16(<Facts<u16> as Domain>::top()),
        Carrier::BitVec(Width::W32) => Value::Bv32(<Facts<u32> as Domain>::top()),
        Carrier::BitVec(Width::W64) => Value::Bv64(<Facts<u64> as Domain>::top()),
        Carrier::BitVec(Width::W128) => Value::Bv128(<Facts<u128> as Domain>::top()),
        Carrier::TopOnly { .. } => Value::Top,
    }
}

fn bool_to_byte(value: &Bool4) -> u8 {
    match value {
        Bool4::False => 0,
        Bool4::True => 1,
        Bool4::Top => 2,
    }
}

fn byte_to_bool(byte: u8) -> Bool4 {
    match byte {
        0 => Bool4::False,
        1 => Bool4::True,
        _ => Bool4::Top,
    }
}

fn put_i64(out: &mut [u8], offset: usize, value: i64) {
    out[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

fn get_i64(bytes: &[u8], offset: usize) -> i64 {
    i64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

fn encode_lo(lo: Lo) -> i64 {
    match lo {
        Lo::NegInf => i64::MIN,
        // i64::MIN is reserved for -infinity. Rounding it outward preserves
        // every concrete value represented by the source interval.
        Lo::Fin(value) => value.to_i64().unwrap_or(i64::MIN),
    }
}

fn encode_hi(hi: Hi) -> i64 {
    match hi {
        Hi::PosInf => i64::MAX,
        // i64::MAX is reserved for +infinity.
        Hi::Fin(value) => value.to_i64().unwrap_or(i64::MAX),
    }
}

fn decode_lo(value: i64) -> Lo {
    if value == i64::MIN {
        Lo::NegInf
    } else {
        Lo::Fin(IBig::from_i64(value))
    }
}

fn decode_hi(value: i64) -> Hi {
    if value == i64::MAX {
        Hi::PosInf
    } else {
        Hi::Fin(IBig::from_i64(value))
    }
}

fn encode_int(value: &FactsZ, out: &mut [u8]) {
    let interval = value.interval();
    let (lo, hi) = interval.bounds();
    put_i64(out, 0, encode_lo(lo));
    put_i64(out, 8, encode_hi(hi));
}

fn decode_int(bytes: &[u8]) -> FactsZ {
    let interval = IntervalZ::new(decode_lo(get_i64(bytes, 0)), decode_hi(get_i64(bytes, 8)))
        .unwrap_or_else(IntervalZ::top);
    FactsZ::from_interval(interval)
}

/// Encodes a value into the fixed-size representation owned by the e-class
/// storage layer. Invalid value/carrier combinations are programmer errors at
/// the typed registry boundary.
pub fn encode(carrier: Carrier, value: &Value, out: &mut [u8]) {
    assert_eq!(out.len(), entry_size(carrier));
    match (carrier, value) {
        (Carrier::Bool, Value::Bool(value)) => out[0] = bool_to_byte(value),
        (Carrier::Int, Value::Int(value)) => encode_int(value, out),
        (Carrier::BitVec(Width::W8), Value::Bv8(value)) => {
            let (lo, hi) = value.interval().bounds();
            out.copy_from_slice(&[lo, hi]);
        }
        (Carrier::BitVec(Width::W16), Value::Bv16(value)) => {
            let (lo, hi) = value.interval().bounds();
            out[..2].copy_from_slice(&lo.to_le_bytes());
            out[2..].copy_from_slice(&hi.to_le_bytes());
        }
        (Carrier::BitVec(Width::W32), Value::Bv32(value)) => {
            let (lo, hi) = value.interval().bounds();
            out[..4].copy_from_slice(&lo.to_le_bytes());
            out[4..].copy_from_slice(&hi.to_le_bytes());
        }
        (Carrier::BitVec(Width::W64), Value::Bv64(value)) => {
            let (lo, hi) = value.interval().bounds();
            out[..8].copy_from_slice(&lo.to_le_bytes());
            out[8..].copy_from_slice(&hi.to_le_bytes());
        }
        (Carrier::BitVec(Width::W128), Value::Bv128(value)) => {
            let (lo, hi) = value.interval().bounds();
            out[..16].copy_from_slice(&lo.to_le_bytes());
            out[16..].copy_from_slice(&hi.to_le_bytes());
        }
        (Carrier::TopOnly { .. }, Value::Top) => {}
        _ => panic!("registry value does not match its carrier"),
    }
}

fn facts_from_bounds<W: crate::word::Word>(lo: W, hi: W) -> Facts<W> {
    let interval = Interval::new(lo, hi).unwrap_or_else(Interval::top);
    Facts::from_interval(interval)
}

/// Decodes an entry previously created by `encode`. Malformed byte intervals
/// are safely widened to top rather than becoming an invalid domain value.
pub fn decode(carrier: Carrier, bytes: &[u8]) -> Value {
    assert_eq!(bytes.len(), entry_size(carrier));
    match carrier {
        Carrier::Bool => Value::Bool(byte_to_bool(bytes[0])),
        Carrier::Int => Value::Int(decode_int(bytes)),
        Carrier::BitVec(Width::W8) => Value::Bv8(facts_from_bounds(bytes[0], bytes[1])),
        Carrier::BitVec(Width::W16) => Value::Bv16(facts_from_bounds(
            u16::from_le_bytes(bytes[..2].try_into().unwrap()),
            u16::from_le_bytes(bytes[2..].try_into().unwrap()),
        )),
        Carrier::BitVec(Width::W32) => Value::Bv32(facts_from_bounds(
            u32::from_le_bytes(bytes[..4].try_into().unwrap()),
            u32::from_le_bytes(bytes[4..].try_into().unwrap()),
        )),
        Carrier::BitVec(Width::W64) => Value::Bv64(facts_from_bounds(
            u64::from_le_bytes(bytes[..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..].try_into().unwrap()),
        )),
        Carrier::BitVec(Width::W128) => Value::Bv128(facts_from_bounds(
            u128::from_le_bytes(bytes[..16].try_into().unwrap()),
            u128::from_le_bytes(bytes[16..].try_into().unwrap()),
        )),
        Carrier::TopOnly { .. } => Value::Top,
    }
}

fn duplicate(value: &Value) -> Value {
    match value {
        Value::Bool(value) => Value::Bool(value.dup()),
        Value::Int(value) => Value::Int(value.dup()),
        Value::Bv8(value) => Value::Bv8(value.dup()),
        Value::Bv16(value) => Value::Bv16(value.dup()),
        Value::Bv32(value) => Value::Bv32(value.dup()),
        Value::Bv64(value) => Value::Bv64(value.dup()),
        Value::Bv128(value) => Value::Bv128(value.dup()),
        Value::Top => Value::Top,
    }
}

fn field_enabled(mask: DomainSet) -> bool {
    mask.contains(0)
}

/// Meets two entries. With the currently available one-field records, an
/// empty mask means no analysis and therefore produces top; otherwise this
/// delegates to the verified `Domain::meet` implementation for the carrier.
pub fn meet(carrier: Carrier, mask: DomainSet, left: &Value, right: &Value) -> RegistryResult {
    if !field_enabled(mask) {
        return RegistryResult::Val(top(carrier));
    }
    macro_rules! meet_value {
        ($a:expr, $b:expr, $variant:ident) => {
            match $a.meet($b) {
                BotOr::Bot => RegistryResult::Bot,
                BotOr::Val(value) => RegistryResult::Val(Value::$variant(value)),
            }
        };
    }
    match (carrier, left, right) {
        (Carrier::Bool, Value::Bool(a), Value::Bool(b)) => meet_value!(a, b, Bool),
        (Carrier::Int, Value::Int(a), Value::Int(b)) => meet_value!(a, b, Int),
        (Carrier::BitVec(Width::W8), Value::Bv8(a), Value::Bv8(b)) => meet_value!(a, b, Bv8),
        (Carrier::BitVec(Width::W16), Value::Bv16(a), Value::Bv16(b)) => {
            meet_value!(a, b, Bv16)
        }
        (Carrier::BitVec(Width::W32), Value::Bv32(a), Value::Bv32(b)) => {
            meet_value!(a, b, Bv32)
        }
        (Carrier::BitVec(Width::W64), Value::Bv64(a), Value::Bv64(b)) => {
            meet_value!(a, b, Bv64)
        }
        (Carrier::BitVec(Width::W128), Value::Bv128(a), Value::Bv128(b)) => {
            meet_value!(a, b, Bv128)
        }
        (Carrier::TopOnly { .. }, Value::Top, Value::Top) => RegistryResult::Val(Value::Top),
        _ => panic!("registry value does not match its carrier"),
    }
}

/// Reduces an entry under the supplied domain mask. The current records have
/// exactly one available field, so their verified normalization is the
/// identity. Keeping this function here makes the transition to multi-field
/// reductions local when Congruence and Sign facts become available.
pub fn reduce(carrier: Carrier, mask: DomainSet, value: &Value) -> RegistryResult {
    if !field_enabled(mask) {
        return RegistryResult::Val(top(carrier));
    }
    match (carrier, value) {
        (Carrier::Bool, Value::Bool(_))
        | (Carrier::Int, Value::Int(_))
        | (Carrier::BitVec(Width::W8), Value::Bv8(_))
        | (Carrier::BitVec(Width::W16), Value::Bv16(_))
        | (Carrier::BitVec(Width::W32), Value::Bv32(_))
        | (Carrier::BitVec(Width::W64), Value::Bv64(_))
        | (Carrier::BitVec(Width::W128), Value::Bv128(_))
        | (Carrier::TopOnly { .. }, Value::Top) => RegistryResult::Val(duplicate(value)),
        _ => panic!("registry value does not match its carrier"),
    }
}

/// Returns a constant only when the currently enabled available field proves
/// that the value is a singleton.
pub fn as_constant(carrier: Carrier, mask: DomainSet, value: &Value) -> Option<Const> {
    if !field_enabled(mask) {
        return None;
    }
    match (carrier, value) {
        (Carrier::Bool, Value::Bool(Bool4::False)) => Some(Const::Bool(false)),
        (Carrier::Bool, Value::Bool(Bool4::True)) => Some(Const::Bool(true)),
        (Carrier::Int, Value::Int(facts)) => match facts.interval().bounds() {
            (Lo::Fin(lo), Hi::Fin(hi)) if lo.le(&hi) && hi.le(&lo) => Some(Const::Int(lo)),
            _ => None,
        },
        (Carrier::BitVec(Width::W8), Value::Bv8(facts)) => singleton_u8(facts),
        (Carrier::BitVec(Width::W16), Value::Bv16(facts)) => singleton_u16(facts),
        (Carrier::BitVec(Width::W32), Value::Bv32(facts)) => singleton_u32(facts),
        (Carrier::BitVec(Width::W64), Value::Bv64(facts)) => singleton_u64(facts),
        (Carrier::BitVec(Width::W128), Value::Bv128(facts)) => singleton_u128(facts),
        _ => None,
    }
}

macro_rules! singleton {
    ($name:ident, $word:ty) => {
        fn $name(facts: &Facts<$word>) -> Option<Const> {
            let (lo, hi) = facts.interval().bounds();
            (lo == hi).then_some(Const::Bv(lo as u128))
        }
    };
}

singleton!(singleton_u8, u8);
singleton!(singleton_u16, u16);
singleton!(singleton_u32, u32);
singleton!(singleton_u64, u64);
singleton!(singleton_u128, u128);

fn value_carrier(value: &Value) -> Carrier {
    match value {
        Value::Bool(_) => Carrier::Bool,
        Value::Int(_) => Carrier::Int,
        Value::Bv8(_) => Carrier::BitVec(Width::W8),
        Value::Bv16(_) => Carrier::BitVec(Width::W16),
        Value::Bv32(_) => Carrier::BitVec(Width::W32),
        Value::Bv64(_) => Carrier::BitVec(Width::W64),
        Value::Bv128(_) => Carrier::BitVec(Width::W128),
        Value::Top => Carrier::TopOnly { bits: 0 },
    }
}

fn result_carrier(op: Op, args: &[Value]) -> Carrier {
    match op {
        Op::Lt
        | Op::Le
        | Op::Gt
        | Op::Ge
        | Op::Eq
        | Op::Distinct
        | Op::Not
        | Op::And
        | Op::Or
        | Op::Xor
        | Op::Implies
        | Op::BvUlt
        | Op::BvUle
        | Op::BvUgt
        | Op::BvUge
        | Op::BvSlt
        | Op::BvSle
        | Op::BvSgt
        | Op::BvSge => Carrier::Bool,
        Op::Ite if args.len() >= 2 => value_carrier(&args[1]),
        _ if !args.is_empty() => value_carrier(&args[0]),
        _ => Carrier::TopOnly { bits: 0 },
    }
}

/// Executes every currently available forward transfer. Operators whose
/// backing transfer has not landed yet deliberately return `Top`; this is a
/// sound result and makes the registry usable while the domain matrix grows.
pub fn forward(op: Op, mask: DomainSet, args: &[Value]) -> Value {
    let carrier = result_carrier(op, args);
    if !field_enabled(mask) {
        return top(carrier);
    }

    macro_rules! binary_arith {
        ($a:expr, $b:expr, $variant:ident, $semantics:ty, $method:ident) => {
            Value::$variant(<Facts<_> as Arith<$semantics>>::$method($a, $b))
        };
    }
    macro_rules! unary_arith {
        ($a:expr, $variant:ident, $semantics:ty) => {
            Value::$variant(<Facts<_> as Arith<$semantics>>::neg($a))
        };
    }
    macro_rules! binary_mul {
        ($a:expr, $b:expr, $variant:ident, $semantics:ty) => {
            Value::$variant(<Facts<_> as Mul<$semantics>>::mul($a, $b))
        };
    }

    match (op, args) {
        (Op::Not, [Value::Bool(a)]) => Value::Bool(a.not()),
        (Op::And, [Value::Bool(a), Value::Bool(b)]) => Value::Bool(a.and(b)),
        (Op::Or, [Value::Bool(a), Value::Bool(b)]) => Value::Bool(a.or(b)),
        (Op::Xor, [Value::Bool(a), Value::Bool(b)]) => Value::Bool(a.not().eq(b)),
        (Op::Implies, [Value::Bool(a), Value::Bool(b)]) => Value::Bool(a.not().or(b)),
        (Op::Eq, [Value::Bool(a), Value::Bool(b)]) => Value::Bool(a.eq(b)),
        (Op::Ite, [Value::Bool(c), then_value, else_value]) => {
            if c.is_true() {
                duplicate(then_value)
            } else if c.is_false() {
                duplicate(else_value)
            } else {
                join_same_carrier(carrier, then_value, else_value)
            }
        }
        (Op::Add, [Value::Int(a), Value::Int(b)]) => {
            Value::Int(<FactsZ as Arith<Euclid>>::add(a, b))
        }
        (Op::Sub, [Value::Int(a), Value::Int(b)]) => {
            Value::Int(<FactsZ as Arith<Euclid>>::sub(a, b))
        }
        (Op::Neg, [Value::Int(a)]) => Value::Int(<FactsZ as Arith<Euclid>>::neg(a)),
        (Op::BvAdd, [Value::Bv8(a), Value::Bv8(b)]) => binary_arith!(a, b, Bv8, Unsigned<u8>, add),
        (Op::BvAdd, [Value::Bv16(a), Value::Bv16(b)]) => {
            binary_arith!(a, b, Bv16, Unsigned<u16>, add)
        }
        (Op::BvAdd, [Value::Bv32(a), Value::Bv32(b)]) => {
            binary_arith!(a, b, Bv32, Unsigned<u32>, add)
        }
        (Op::BvAdd, [Value::Bv64(a), Value::Bv64(b)]) => {
            binary_arith!(a, b, Bv64, Unsigned<u64>, add)
        }
        (Op::BvAdd, [Value::Bv128(a), Value::Bv128(b)]) => {
            binary_arith!(a, b, Bv128, Unsigned<u128>, add)
        }
        (Op::BvSub, [Value::Bv8(a), Value::Bv8(b)]) => binary_arith!(a, b, Bv8, Unsigned<u8>, sub),
        (Op::BvSub, [Value::Bv16(a), Value::Bv16(b)]) => {
            binary_arith!(a, b, Bv16, Unsigned<u16>, sub)
        }
        (Op::BvSub, [Value::Bv32(a), Value::Bv32(b)]) => {
            binary_arith!(a, b, Bv32, Unsigned<u32>, sub)
        }
        (Op::BvSub, [Value::Bv64(a), Value::Bv64(b)]) => {
            binary_arith!(a, b, Bv64, Unsigned<u64>, sub)
        }
        (Op::BvSub, [Value::Bv128(a), Value::Bv128(b)]) => {
            binary_arith!(a, b, Bv128, Unsigned<u128>, sub)
        }
        (Op::BvNeg, [Value::Bv8(a)]) => unary_arith!(a, Bv8, Unsigned<u8>),
        (Op::BvNeg, [Value::Bv16(a)]) => unary_arith!(a, Bv16, Unsigned<u16>),
        (Op::BvNeg, [Value::Bv32(a)]) => unary_arith!(a, Bv32, Unsigned<u32>),
        (Op::BvNeg, [Value::Bv64(a)]) => unary_arith!(a, Bv64, Unsigned<u64>),
        (Op::BvNeg, [Value::Bv128(a)]) => unary_arith!(a, Bv128, Unsigned<u128>),
        (Op::BvMul, [Value::Bv8(a), Value::Bv8(b)]) => binary_mul!(a, b, Bv8, Unsigned<u8>),
        (Op::BvMul, [Value::Bv16(a), Value::Bv16(b)]) => binary_mul!(a, b, Bv16, Unsigned<u16>),
        (Op::BvMul, [Value::Bv32(a), Value::Bv32(b)]) => binary_mul!(a, b, Bv32, Unsigned<u32>),
        (Op::BvMul, [Value::Bv64(a), Value::Bv64(b)]) => binary_mul!(a, b, Bv64, Unsigned<u64>),
        (Op::BvMul, [Value::Bv128(a), Value::Bv128(b)]) => binary_mul!(a, b, Bv128, Unsigned<u128>),
        (Op::BvUdiv, [Value::Bv8(a), Value::Bv8(b)]) => Value::Bv8(unsigned_div(a, b)),
        (Op::BvUdiv, [Value::Bv16(a), Value::Bv16(b)]) => Value::Bv16(unsigned_div(a, b)),
        (Op::BvUdiv, [Value::Bv32(a), Value::Bv32(b)]) => Value::Bv32(unsigned_div(a, b)),
        (Op::BvUdiv, [Value::Bv64(a), Value::Bv64(b)]) => Value::Bv64(unsigned_div(a, b)),
        (Op::BvUdiv, [Value::Bv128(a), Value::Bv128(b)]) => Value::Bv128(unsigned_div(a, b)),
        (Op::BvUrem, [Value::Bv8(a), Value::Bv8(b)]) => Value::Bv8(unsigned_rem(a, b)),
        (Op::BvUrem, [Value::Bv16(a), Value::Bv16(b)]) => Value::Bv16(unsigned_rem(a, b)),
        (Op::BvUrem, [Value::Bv32(a), Value::Bv32(b)]) => Value::Bv32(unsigned_rem(a, b)),
        (Op::BvUrem, [Value::Bv64(a), Value::Bv64(b)]) => Value::Bv64(unsigned_rem(a, b)),
        (Op::BvUrem, [Value::Bv128(a), Value::Bv128(b)]) => Value::Bv128(unsigned_rem(a, b)),
        _ => top(carrier),
    }
}

/// Applies a backward transfer from a result fact to its operands.
///
/// The first registry slice deliberately preserves the operands for transfers
/// that have no domain-specific backward implementation yet. This is sound:
/// every satisfying concrete tuple remains represented and no operand grows.
/// It gives the saturation engine one stable API now; comparison and `ite`
/// refinements can replace the corresponding cases as they land.
pub fn backward(_op: Op, mask: DomainSet, _result: &Value, args: &[Value]) -> BackwardResult {
    assert!(
        args.len() <= 3,
        "registry operators have arity at most three"
    );
    let mut values = [Value::Top, Value::Top, Value::Top];
    for (index, argument) in args.iter().enumerate() {
        values[index] = if field_enabled(mask) {
            duplicate(argument)
        } else {
            top(value_carrier(argument))
        };
    }
    BackwardResult {
        values,
        arity: args.len(),
    }
}

fn join_same_carrier(carrier: Carrier, left: &Value, right: &Value) -> Value {
    match (carrier, left, right) {
        (Carrier::Bool, Value::Bool(a), Value::Bool(b)) => Value::Bool(a.join(b)),
        (Carrier::Int, Value::Int(a), Value::Int(b)) => Value::Int(a.join(b)),
        (Carrier::BitVec(Width::W8), Value::Bv8(a), Value::Bv8(b)) => Value::Bv8(a.join(b)),
        (Carrier::BitVec(Width::W16), Value::Bv16(a), Value::Bv16(b)) => Value::Bv16(a.join(b)),
        (Carrier::BitVec(Width::W32), Value::Bv32(a), Value::Bv32(b)) => Value::Bv32(a.join(b)),
        (Carrier::BitVec(Width::W64), Value::Bv64(a), Value::Bv64(b)) => Value::Bv64(a.join(b)),
        (Carrier::BitVec(Width::W128), Value::Bv128(a), Value::Bv128(b)) => Value::Bv128(a.join(b)),
        (Carrier::TopOnly { .. }, Value::Top, Value::Top) => Value::Top,
        _ => panic!("ite branches have different carriers"),
    }
}

/// Adds the SMT-LIB `bvudiv x 0 = all-ones` case to the verified transfer
/// over nonzero divisors.  `DivRem` deliberately leaves zero divisors out of
/// its contract, so the registry is the one layer that makes this total.
fn unsigned_div<W: Word>(dividend: &Facts<W>, divisor: &Facts<W>) -> Facts<W> {
    let (nonzero, _) = <Facts<W> as DivRem<Unsigned<W>>>::div(dividend, divisor);
    let zero_case = Facts::from_interval(Interval::constant(W::max()));
    if <Facts<W> as DivRem<Unsigned<W>>>::contains_zero(divisor) {
        match nonzero {
            BotOr::Bot => zero_case,
            BotOr::Val(value) => value.join(&zero_case),
        }
    } else {
        match nonzero {
            BotOr::Val(value) => value,
            // A well-formed nonzero divisor cannot produce Bot.  Top keeps
            // this dispatcher total if a future domain weakens that result.
            BotOr::Bot => <Facts<W> as Domain>::top(),
        }
    }
}

/// Adds the SMT-LIB `bvurem x 0 = x` case to the verified transfer over
/// nonzero divisors.
fn unsigned_rem<W: Word>(dividend: &Facts<W>, divisor: &Facts<W>) -> Facts<W> {
    let (nonzero, _) = <Facts<W> as DivRem<Unsigned<W>>>::rem(dividend, divisor);
    if <Facts<W> as DivRem<Unsigned<W>>>::contains_zero(divisor) {
        match nonzero {
            BotOr::Bot => dividend.dup(),
            BotOr::Val(value) => value.join(dividend),
        }
    } else {
        match nonzero {
            BotOr::Val(value) => value,
            BotOr::Bot => <Facts<W> as Domain>::top(),
        }
    }
}

/// An SMT-LIB operator accepted by the first registry implementation.
///
/// The enum keeps the textual parser out of the verified transfer layer.  A
/// future transfer implementation can therefore dispatch on this closed set
/// without repeating string comparisons.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Op {
    Add,
    Sub,
    Neg,
    Mul,
    Div,
    Mod,
    Abs,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Distinct,
    Ite,
    Not,
    And,
    Or,
    Xor,
    Implies,
    BvAdd,
    BvSub,
    BvNeg,
    BvMul,
    BvUdiv,
    BvUrem,
    BvSdiv,
    BvSrem,
    BvSmod,
    BvAnd,
    BvOr,
    BvXor,
    BvNot,
    BvShl,
    BvLshr,
    BvAshr,
    BvUlt,
    BvUle,
    BvUgt,
    BvUge,
    BvSlt,
    BvSle,
    BvSgt,
    BvSge,
    Extract,
    Concat,
    ZeroExtend,
    SignExtend,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OpError {
    Unknown,
    Signature,
}

fn same(a: Carrier, b: Carrier) -> bool {
    match (a, b) {
        (Carrier::Bool, Carrier::Bool) | (Carrier::Int, Carrier::Int) => true,
        (Carrier::BitVec(x), Carrier::BitVec(y)) => x == y,
        (Carrier::TopOnly { bits: x }, Carrier::TopOnly { bits: y }) => x == y,
        _ => false,
    }
}

const fn is_bv(c: Carrier) -> bool {
    matches!(c, Carrier::BitVec(_) | Carrier::TopOnly { .. })
}

const fn carrier_bits(c: Carrier) -> Option<u32> {
    match c {
        Carrier::BitVec(width) => Some(width.bits()),
        Carrier::TopOnly { bits } => Some(bits),
        Carrier::Bool | Carrier::Int => None,
    }
}

fn binary_same(args: &[Carrier]) -> Result<Carrier, OpError> {
    if args.len() == 2 && same(args[0], args[1]) {
        Ok(args[0])
    } else {
        Err(OpError::Signature)
    }
}

/// Resolves an SMT-LIB spelling and checks its carrier signature.
///
/// The function intentionally resolves operators whose transfer is still a
/// top-producing stub.  Syntax validation must not depend on whether an
/// optional abstract-domain field has landed yet.
pub fn op(name: &str, args: &[Carrier]) -> Result<(Op, Carrier), OpError> {
    use Carrier::{Bool, Int};
    match name {
        "not" => {
            return if args == [Bool] {
                Ok((Op::Not, Bool))
            } else {
                Err(OpError::Signature)
            };
        }
        "abs" => {
            return if args == [Int] {
                Ok((Op::Abs, Int))
            } else {
                Err(OpError::Signature)
            };
        }
        "bvneg" => {
            return if args.len() == 1 && is_bv(args[0]) {
                Ok((Op::BvNeg, args[0]))
            } else {
                Err(OpError::Signature)
            };
        }
        "bvnot" => {
            return if args.len() == 1 && is_bv(args[0]) {
                Ok((Op::BvNot, args[0]))
            } else {
                Err(OpError::Signature)
            };
        }
        "extract" => {
            return if args.len() == 1 && is_bv(args[0]) {
                Ok((Op::Extract, args[0]))
            } else {
                Err(OpError::Signature)
            };
        }
        "zero_extend" => {
            return if args.len() == 1 && is_bv(args[0]) {
                Ok((Op::ZeroExtend, args[0]))
            } else {
                Err(OpError::Signature)
            };
        }
        "sign_extend" => {
            return if args.len() == 1 && is_bv(args[0]) {
                Ok((Op::SignExtend, args[0]))
            } else {
                Err(OpError::Signature)
            };
        }
        "ite" => {
            return if args.len() == 3 && args[0] == Bool && same(args[1], args[2]) {
                Ok((Op::Ite, args[1]))
            } else {
                Err(OpError::Signature)
            };
        }
        "concat" if args.len() == 2 && is_bv(args[0]) && is_bv(args[1]) => {
            let bits = carrier_bits(args[0]).unwrap() + carrier_bits(args[1]).unwrap();
            return Ok((Op::Concat, carrier_of_bitvec(bits).unwrap()));
        }
        "-" if args == [Int] => return Ok((Op::Neg, Int)),
        _ => {}
    }
    let binary = match binary_same(args) {
        Ok(carrier) => carrier,
        Err(_) => {
            return match name {
                "+" | "-" | "*" | "div" | "mod" | "<" | "<=" | ">" | ">=" | "and" | "or"
                | "xor" | "=>" | "=" | "distinct" | "bvadd" | "bvsub" | "bvmul" | "bvudiv"
                | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" | "bvand" | "bvor" | "bvxor"
                | "bvshl" | "bvlshr" | "bvashr" | "bvult" | "bvule" | "bvugt" | "bvuge"
                | "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "concat" => Err(OpError::Signature),
                _ => Err(OpError::Unknown),
            };
        }
    };
    let int_binary = |operator| {
        if binary == Int {
            Ok((operator, Int))
        } else {
            Err(OpError::Signature)
        }
    };
    let bool_binary = |operator| {
        if binary == Bool {
            Ok((operator, Bool))
        } else {
            Err(OpError::Signature)
        }
    };
    let bv_binary = |operator| {
        if is_bv(binary) {
            Ok((operator, binary))
        } else {
            Err(OpError::Signature)
        }
    };

    match name {
        "+" => int_binary(Op::Add),
        "*" => int_binary(Op::Mul),
        "div" => int_binary(Op::Div),
        "mod" => int_binary(Op::Mod),
        "<" => int_binary(Op::Lt).map(|(o, _)| (o, Bool)),
        "<=" => int_binary(Op::Le).map(|(o, _)| (o, Bool)),
        ">" => int_binary(Op::Gt).map(|(o, _)| (o, Bool)),
        ">=" => int_binary(Op::Ge).map(|(o, _)| (o, Bool)),
        "and" => bool_binary(Op::And),
        "or" => bool_binary(Op::Or),
        "xor" => bool_binary(Op::Xor),
        "=>" => bool_binary(Op::Implies),
        "=" => {
            if args.len() == 2 && same(args[0], args[1]) {
                Ok((Op::Eq, Bool))
            } else {
                Err(OpError::Signature)
            }
        }
        "distinct" => {
            if args.len() == 2 && same(args[0], args[1]) {
                Ok((Op::Distinct, Bool))
            } else {
                Err(OpError::Signature)
            }
        }
        "-" => int_binary(Op::Sub),
        "bvadd" => bv_binary(Op::BvAdd),
        "bvsub" => bv_binary(Op::BvSub),
        "bvmul" => bv_binary(Op::BvMul),
        "bvudiv" => bv_binary(Op::BvUdiv),
        "bvurem" => bv_binary(Op::BvUrem),
        "bvsdiv" => bv_binary(Op::BvSdiv),
        "bvsrem" => bv_binary(Op::BvSrem),
        "bvsmod" => bv_binary(Op::BvSmod),
        "bvand" => bv_binary(Op::BvAnd),
        "bvor" => bv_binary(Op::BvOr),
        "bvxor" => bv_binary(Op::BvXor),
        "bvshl" => bv_binary(Op::BvShl),
        "bvlshr" => bv_binary(Op::BvLshr),
        "bvashr" => bv_binary(Op::BvAshr),
        "bvult" => bv_binary(Op::BvUlt).map(|(o, _)| (o, Bool)),
        "bvule" => bv_binary(Op::BvUle).map(|(o, _)| (o, Bool)),
        "bvugt" => bv_binary(Op::BvUgt).map(|(o, _)| (o, Bool)),
        "bvuge" => bv_binary(Op::BvUge).map(|(o, _)| (o, Bool)),
        "bvslt" => bv_binary(Op::BvSlt).map(|(o, _)| (o, Bool)),
        "bvsle" => bv_binary(Op::BvSle).map(|(o, _)| (o, Bool)),
        "bvsgt" => bv_binary(Op::BvSgt).map(|(o, _)| (o, Bool)),
        "bvsge" => bv_binary(Op::BvSge).map(|(o, _)| (o, Bool)),
        _ => Err(OpError::Unknown),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn carrier_table_covers_native_and_top_only_widths() {
        assert_eq!(carrier_of_bitvec(8), Some(Carrier::BitVec(Width::W8)));
        assert_eq!(carrier_of_bitvec(128), Some(Carrier::BitVec(Width::W128)));
        assert_eq!(carrier_of_bitvec(7), Some(Carrier::TopOnly { bits: 7 }));
        assert_eq!(carrier_of_bitvec(0), None);
    }

    #[test]
    fn domain_names_have_stable_bits_and_availability() {
        let bv = Carrier::BitVec(Width::W32);
        assert_eq!(domain_bit(bv, "ubounds"), Ok(0));
        assert_eq!(domain_bit(bv, "bits"), Ok(3));
        assert!(!domain_available(bv, 3));
        assert_eq!(
            domain_bit(Carrier::Int, "ubounds"),
            Err(NameError::WrongCarrier(Carrier::Int))
        );
        assert_eq!(
            domain_bit(Carrier::Bool, "octagon"),
            Err(NameError::Unknown)
        );
    }

    #[test]
    fn operators_resolve_only_with_a_valid_signature() {
        let bv = Carrier::BitVec(Width::W8);
        assert_eq!(op("bvadd", &[bv, bv]), Ok((Op::BvAdd, bv)));
        assert_eq!(op("bvult", &[bv, bv]), Ok((Op::BvUlt, Carrier::Bool)));
        assert_eq!(
            op("concat", &[bv, bv]),
            Ok((Op::Concat, Carrier::BitVec(Width::W16)))
        );
        assert_eq!(
            op("+", &[Carrier::Int, Carrier::Int]),
            Ok((Op::Add, Carrier::Int))
        );
        assert_eq!(
            op("bvadd", &[Carrier::Int, Carrier::Int]),
            Err(OpError::Signature)
        );
        assert_eq!(op("unknown", &[bv]), Err(OpError::Unknown));
    }

    #[test]
    fn entry_table_uses_fixed_carrier_sizes() {
        assert_eq!(entry_size(Carrier::Bool), 1);
        assert_eq!(entry_size(Carrier::Int), 16);
        assert_eq!(entry_size(Carrier::BitVec(Width::W8)), 2);
        assert_eq!(entry_size(Carrier::BitVec(Width::W128)), 32);
        assert_eq!(entry_size(Carrier::TopOnly { bits: 7 }), 0);
        assert!(matches!(top(Carrier::TopOnly { bits: 7 }), Value::Top));
    }

    #[test]
    fn bool_and_u8_entries_round_trip() {
        let mut bool_entry = [0_u8; 1];
        encode(Carrier::Bool, &Value::Bool(Bool4::True), &mut bool_entry);
        assert!(matches!(
            decode(Carrier::Bool, &bool_entry),
            Value::Bool(Bool4::True)
        ));

        let carrier = Carrier::BitVec(Width::W8);
        let source = facts_from_bounds(10_u8, 42_u8);
        let mut entry = [0_u8; 2];
        encode(carrier, &Value::Bv8(source), &mut entry);
        assert_eq!(entry, [10, 42]);
        match decode(carrier, &entry) {
            Value::Bv8(value) => assert_eq!(value.interval().bounds(), (10, 42)),
            _ => panic!("u8 registry entry decoded to the wrong carrier"),
        }
    }

    #[test]
    fn lattice_and_forward_dispatch_use_available_fields() {
        let carrier = Carrier::BitVec(Width::W8);
        let mask = DomainSet::from_bit(0);
        let left = decode(carrier, &[1, 1]);
        let right = decode(carrier, &[2, 2]);
        match forward(Op::BvAdd, mask, &[left, right]) {
            Value::Bv8(value) => assert_eq!(value.interval().bounds(), (3, 3)),
            _ => panic!("bvadd did not retain its native carrier"),
        }

        let disjoint_left = decode(carrier, &[0, 1]);
        let disjoint_right = decode(carrier, &[2, 3]);
        assert!(matches!(
            meet(carrier, mask, &disjoint_left, &disjoint_right),
            RegistryResult::Bot
        ));

        let bool_value = forward(
            Op::Ite,
            mask,
            &[
                Value::Bool(Bool4::True),
                Value::Bool(Bool4::False),
                Value::Bool(Bool4::True),
            ],
        );
        assert!(matches!(bool_value, Value::Bool(Bool4::False)));
    }

    #[test]
    fn singleton_detection_requires_a_singleton_interval() {
        let carrier = Carrier::BitVec(Width::W8);
        let mask = DomainSet::from_bit(0);
        assert!(matches!(
            as_constant(carrier, mask, &decode(carrier, &[7, 7])),
            Some(Const::Bv(7))
        ));
        assert!(as_constant(carrier, mask, &decode(carrier, &[7, 8])).is_none());
        assert!(as_constant(carrier, DomainSet::empty(), &decode(carrier, &[7, 7])).is_none());
    }

    #[test]
    fn disabled_masks_and_backward_stubs_are_safe() {
        let carrier = Carrier::BitVec(Width::W8);
        let original = decode(carrier, &[7, 7]);
        assert!(matches!(
            reduce(carrier, DomainSet::empty(), &original),
            RegistryResult::Val(Value::Bv8(value)) if value.interval().bounds() == (0, u8::MAX)
        ));

        let argument = decode(carrier, &[7, 7]);
        let refined = backward(Op::BvAdd, DomainSet::from_bit(0), &original, &[argument]);
        assert_eq!(refined.arity, 1);
        match &refined.values[0] {
            Value::Bv8(value) => assert_eq!(value.interval().bounds(), (7, 7)),
            _ => panic!("backward transfer changed the argument carrier"),
        }
    }
}
