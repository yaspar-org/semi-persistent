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
use crate::reduce::{Channel, meet_normalize};
use crate::semantics::{Euclid, Unsigned};
use crate::transfer::{Arith, DivRem, Mul};
use crate::word::Word;
use vstd::prelude::*;

verus! {
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
    pub fn bits(self) -> (bits: u32) {
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

// A per-sort mask over the fields of its fact record.
verus! {
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
pub struct DomainSet(u8);

impl DomainSet {
    pub fn empty() -> Self {
        Self(0)
    }

    pub fn from_bit(bit: u8) -> Self {
        if bit < 8 {
            Self(1u8 << bit)
        } else {
            Self::empty()
        }
    }

    pub fn contains(self, bit: u8) -> bool {
        bit < 8 && self.0 & (1u8 << bit) != 0
    }

    pub fn insert(self, bit: u8) -> Self {
        if bit < 8 {
            Self(self.0 | (1u8 << bit))
        } else {
            self
        }
    }

    pub fn bits(self) -> u8 {
        self.0
    }
}

/// The mask of each input sort and of the result sort for one transfer.  A
/// comparison or `ite` crosses sort boundaries, so one global mask is not a
/// meaningful contract for those operators.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TransferMasks {
    pub args: [DomainSet; 3],
    pub result: DomainSet,
}

impl TransferMasks {
    /// Use one mask for a same-sort transfer.
    pub fn uniform(mask: DomainSet) -> Self {
        Self {
            args: [mask, mask, mask],
            result: mask,
        }
    }
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
pub fn default_domains(carrier: Carrier) -> DomainSet {
    match carrier {
        Carrier::Bool | Carrier::Int | Carrier::BitVec(_) => DomainSet::from_bit(0),
        Carrier::TopOnly { .. } => DomainSet::empty(),
    }
}

// An in-memory registry value. This is intentionally an ergonomic Rust enum
// rather than the compact class-storage representation. `encode` and `decode`
// are the only boundary that exposes its fixed-size byte representation to the
// e-graph storage layer.
verus! {
pub enum Value {
    Bool(Bool4),
    Int(FactsZ),
    Bv8(Facts<u8>),
    Bv16(Facts<u16>),
    Bv32(Facts<u32>),
    Bv64(Facts<u64>),
    Bv128(Facts<u128>),
    /// The unique value for a bit-vector carrier without a native `Word`
    /// implementation.  Retaining the width is essential: two top-only
    /// carriers have the same abstract value but different SMT-LIB sorts.
    TopOnly { bits: u32 },
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
pub enum BackwardResult {
    /// No concrete operand tuple can produce the requested result.
    Bot,
    /// The retained operands. `arity` identifies the meaningful prefix;
    /// unused entries are top values.
    Val { values: [Value; 3], arity: usize },
}

/// A concrete singleton reported to the e-graph for a derived merge.
pub enum ConstValue {
    Bool(bool),
    Int(IBig),
    Bv(u128),
}

/// A concrete singleton together with the only carrier at which it may be
/// interpreted.  This prevents, for example, a `#xff` from being read as an
/// Int or as a BitVec(16) constant.
pub struct Const {
    pub carrier: Carrier,
    pub value: ConstValue,
}

/// Why a concrete value cannot be materialized at a requested carrier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstError {
    CarrierMismatch,
    OutOfRange,
}

impl Value {
    /// Every dynamic value carries the invariant of its statically selected
    /// domain.  Dynamic dispatch functions require this predicate before they
    /// call a verified domain operation.
    pub open spec fn wf(&self) -> bool {
        match self {
            Value::Bool(value) => value.wf(),
            Value::Int(value) => value.wf(),
            Value::Bv8(value) => value.wf(),
            Value::Bv16(value) => value.wf(),
            Value::Bv32(value) => value.wf(),
            Value::Bv64(value) => value.wf(),
            Value::Bv128(value) => value.wf(),
            Value::TopOnly { .. } => true,
        }
    }

    pub open spec fn carrier(&self) -> Carrier {
        match self {
            Value::Bool(_) => Carrier::Bool,
            Value::Int(_) => Carrier::Int,
            Value::Bv8(_) => Carrier::BitVec(Width::W8),
            Value::Bv16(_) => Carrier::BitVec(Width::W16),
            Value::Bv32(_) => Carrier::BitVec(Width::W32),
            Value::Bv64(_) => Carrier::BitVec(Width::W64),
            Value::Bv128(_) => Carrier::BitVec(Width::W128),
            Value::TopOnly { bits } => Carrier::TopOnly { bits: *bits },
        }
    }

    pub open spec fn gamma_bool(&self, concrete: bool) -> bool {
        match self { Value::Bool(value) => value.gamma(concrete), _ => false }
    }

    pub open spec fn gamma_int(&self, concrete: int) -> bool {
        match self { Value::Int(value) => value.gamma(concrete), _ => false }
    }

    pub open spec fn gamma_u8(&self, concrete: u8) -> bool {
        match self { Value::Bv8(value) => value.gamma(concrete), _ => false }
    }

    pub open spec fn gamma_u16(&self, concrete: u16) -> bool {
        match self { Value::Bv16(value) => value.gamma(concrete), _ => false }
    }

    pub open spec fn gamma_u32(&self, concrete: u32) -> bool {
        match self { Value::Bv32(value) => value.gamma(concrete), _ => false }
    }

    pub open spec fn gamma_u64(&self, concrete: u64) -> bool {
        match self { Value::Bv64(value) => value.gamma(concrete), _ => false }
    }

    pub open spec fn gamma_u128(&self, concrete: u128) -> bool {
        match self { Value::Bv128(value) => value.gamma(concrete), _ => false }
    }
}

/// Dynamic counterparts of the `Domain` contracts.  A registry value has one
/// concrete sort, so each branch is a normal `gamma` assertion for its native
/// domain rather than an untyped encoding of concrete values.
pub open spec fn covers_both(carrier: Carrier, result: &Value, left: &Value, right: &Value) -> bool {
    match carrier {
        Carrier::Bool => forall|x: bool| #[trigger] result.gamma_bool(x) <== left.gamma_bool(x) || right.gamma_bool(x),
        Carrier::Int => forall|x: int| #[trigger] result.gamma_int(x) <== left.gamma_int(x) || right.gamma_int(x),
        Carrier::BitVec(Width::W8) => forall|x: u8| #[trigger] result.gamma_u8(x) <== left.gamma_u8(x) || right.gamma_u8(x),
        Carrier::BitVec(Width::W16) => forall|x: u16| #[trigger] result.gamma_u16(x) <== left.gamma_u16(x) || right.gamma_u16(x),
        Carrier::BitVec(Width::W32) => forall|x: u32| #[trigger] result.gamma_u32(x) <== left.gamma_u32(x) || right.gamma_u32(x),
        Carrier::BitVec(Width::W64) => forall|x: u64| #[trigger] result.gamma_u64(x) <== left.gamma_u64(x) || right.gamma_u64(x),
        Carrier::BitVec(Width::W128) => forall|x: u128| #[trigger] result.gamma_u128(x) <== left.gamma_u128(x) || right.gamma_u128(x),
        Carrier::TopOnly { .. } => true,
    }
}

pub open spec fn covers_intersection(carrier: Carrier, result: &Value, left: &Value, right: &Value) -> bool {
    match carrier {
        Carrier::Bool => forall|x: bool| #[trigger] left.gamma_bool(x) && right.gamma_bool(x) ==> result.gamma_bool(x),
        Carrier::Int => forall|x: int| #[trigger] left.gamma_int(x) && right.gamma_int(x) ==> result.gamma_int(x),
        Carrier::BitVec(Width::W8) => forall|x: u8| #[trigger] left.gamma_u8(x) && right.gamma_u8(x) ==> result.gamma_u8(x),
        Carrier::BitVec(Width::W16) => forall|x: u16| #[trigger] left.gamma_u16(x) && right.gamma_u16(x) ==> result.gamma_u16(x),
        Carrier::BitVec(Width::W32) => forall|x: u32| #[trigger] left.gamma_u32(x) && right.gamma_u32(x) ==> result.gamma_u32(x),
        Carrier::BitVec(Width::W64) => forall|x: u64| #[trigger] left.gamma_u64(x) && right.gamma_u64(x) ==> result.gamma_u64(x),
        Carrier::BitVec(Width::W128) => forall|x: u128| #[trigger] left.gamma_u128(x) && right.gamma_u128(x) ==> result.gamma_u128(x),
        Carrier::TopOnly { .. } => true,
    }
}

pub open spec fn intersection_empty(carrier: Carrier, left: &Value, right: &Value) -> bool {
    match carrier {
        Carrier::Bool => forall|x: bool| #[trigger] left.gamma_bool(x) ==> !right.gamma_bool(x),
        Carrier::Int => forall|x: int| #[trigger] left.gamma_int(x) ==> !right.gamma_int(x),
        Carrier::BitVec(Width::W8) => forall|x: u8| #[trigger] left.gamma_u8(x) ==> !right.gamma_u8(x),
        Carrier::BitVec(Width::W16) => forall|x: u16| #[trigger] left.gamma_u16(x) ==> !right.gamma_u16(x),
        Carrier::BitVec(Width::W32) => forall|x: u32| #[trigger] left.gamma_u32(x) ==> !right.gamma_u32(x),
        Carrier::BitVec(Width::W64) => forall|x: u64| #[trigger] left.gamma_u64(x) ==> !right.gamma_u64(x),
        Carrier::BitVec(Width::W128) => forall|x: u128| #[trigger] left.gamma_u128(x) ==> !right.gamma_u128(x),
        Carrier::TopOnly { .. } => false,
    }
}

pub open spec fn is_top_value(carrier: Carrier, value: &Value) -> bool {
    match carrier {
        Carrier::Bool => forall|x: bool| #[trigger] value.gamma_bool(x),
        Carrier::Int => forall|x: int| #[trigger] value.gamma_int(x),
        Carrier::BitVec(Width::W8) => forall|x: u8| #[trigger] value.gamma_u8(x),
        Carrier::BitVec(Width::W16) => forall|x: u16| #[trigger] value.gamma_u16(x),
        Carrier::BitVec(Width::W32) => forall|x: u32| #[trigger] value.gamma_u32(x),
        Carrier::BitVec(Width::W64) => forall|x: u64| #[trigger] value.gamma_u64(x),
        Carrier::BitVec(Width::W128) => forall|x: u128| #[trigger] value.gamma_u128(x),
        Carrier::TopOnly { .. } => true,
    }
}

pub open spec fn same_gamma(carrier: Carrier, left: &Value, right: &Value) -> bool {
    covers_intersection(carrier, right, left, left)
        && covers_intersection(carrier, left, right, right)
}

/// An SMT-LIB operator accepted by the registry.  Operators whose backing
/// transfer has not landed still have a signature and a sound top fallback.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Op {
    Add, Sub, Neg, Mul, Div, Mod, Abs,
    Lt, Le, Gt, Ge, Eq, Distinct, Ite,
    Not, And, Or, Xor, Implies,
    BvAdd, BvSub, BvNeg, BvMul, BvUdiv, BvUrem, BvSdiv, BvSrem, BvSmod,
    BvAnd, BvOr, BvXor, BvNot, BvShl, BvLshr, BvAshr,
    BvUlt, BvUle, BvUgt, BvUge, BvSlt, BvSle, BvSgt, BvSge,
    Extract,
    Concat { result: Carrier },
    ZeroExtend,
    SignExtend,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OpError {
    Unknown,
    Signature,
}
}

// Materializes a carrier-tagged concrete value as a canonical registry value.
// The tag check is part of the API rather than an assertion so an e-graph
// cannot accidentally read a literal at a different sort.
verus! {
pub fn constant(carrier: Carrier, constant: &Const) -> Result<Value, ConstError> {
    if carrier != constant.carrier {
        return Err(ConstError::CarrierMismatch);
    }
    match (carrier, &constant.value) {
        (Carrier::Bool, ConstValue::Bool(value)) => Ok(Value::Bool(Bool4::constant(*value))),
        (Carrier::Int, ConstValue::Int(value)) => Ok(Value::Int(FactsZ::from_interval(
            IntervalZ::constant(value.dup()),
        ))),
        (Carrier::BitVec(Width::W8), ConstValue::Bv(value)) => u8::try_from(*value)
            .map(|value| Value::Bv8(Facts::from_interval(Interval::constant(value))))
            .map_err(|_| ConstError::OutOfRange),
        (Carrier::BitVec(Width::W16), ConstValue::Bv(value)) => u16::try_from(*value)
            .map(|value| Value::Bv16(Facts::from_interval(Interval::constant(value))))
            .map_err(|_| ConstError::OutOfRange),
        (Carrier::BitVec(Width::W32), ConstValue::Bv(value)) => u32::try_from(*value)
            .map(|value| Value::Bv32(Facts::from_interval(Interval::constant(value))))
            .map_err(|_| ConstError::OutOfRange),
        (Carrier::BitVec(Width::W64), ConstValue::Bv(value)) => u64::try_from(*value)
            .map(|value| Value::Bv64(Facts::from_interval(Interval::constant(value))))
            .map_err(|_| ConstError::OutOfRange),
        (Carrier::BitVec(Width::W128), ConstValue::Bv(value)) => {
            Ok(Value::Bv128(Facts::from_interval(Interval::constant(*value))))
        }
        _ => Err(ConstError::CarrierMismatch),
    }
}

/// Number of bytes in the class-layer entry for one carrier.
///
/// The current records contain only their available interval field: two
/// native words for a bit-vector and two `i64` bounds for integers.
pub fn entry_size(carrier: Carrier) -> usize {
    match carrier {
        Carrier::Bool => 1,
        Carrier::Int => 16,
        Carrier::BitVec(width) => (width.bits() / 4) as usize,
        Carrier::TopOnly { .. } => 0,
    }
}

/// The least precise non-bottom analysis value for a carrier.
pub fn top(carrier: Carrier) -> (value: Value)
    ensures value.wf(), value.carrier() == carrier, is_top_value(carrier, &value),
{
    match carrier {
        Carrier::Bool => Value::Bool(<Bool4 as Domain>::top()),
        Carrier::Int => Value::Int(<FactsZ as Domain>::top()),
        Carrier::BitVec(Width::W8) => Value::Bv8(<Facts<u8> as Domain>::top()),
        Carrier::BitVec(Width::W16) => Value::Bv16(<Facts<u16> as Domain>::top()),
        Carrier::BitVec(Width::W32) => Value::Bv32(<Facts<u32> as Domain>::top()),
        Carrier::BitVec(Width::W64) => Value::Bv64(<Facts<u64> as Domain>::top()),
        Carrier::BitVec(Width::W128) => Value::Bv128(<Facts<u128> as Domain>::top()),
        Carrier::TopOnly { bits } => Value::TopOnly { bits },
    }
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
        (Carrier::TopOnly { bits }, Value::TopOnly { bits: value_bits }) if bits == *value_bits => {
        }
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
        Carrier::TopOnly { bits } => Value::TopOnly { bits },
    }
}

verus! {
fn duplicate(value: &Value) -> (result: Value)
    requires value.wf(),
    ensures result.wf(),
{
    match value {
        Value::Bool(value) => Value::Bool(value.dup()),
        Value::Int(value) => Value::Int(value.dup()),
        Value::Bv8(value) => Value::Bv8(value.dup()),
        Value::Bv16(value) => Value::Bv16(value.dup()),
        Value::Bv32(value) => Value::Bv32(value.dup()),
        Value::Bv64(value) => Value::Bv64(value.dup()),
        Value::Bv128(value) => Value::Bv128(value.dup()),
        Value::TopOnly { bits } => Value::TopOnly { bits: *bits },
    }
}

fn field_enabled(mask: DomainSet) -> bool {
    mask.contains(0)
}

/// Meets two entries and normalizes the surviving record. An empty mask means
/// no analysis and therefore produces top.  For every available field this
/// delegates to the verified exact meet, then to the field's verified
/// normalization; future fields extend the same dispatch rather than adding a
/// second reduction route.
pub fn meet(carrier: Carrier, mask: DomainSet, left: &Value, right: &Value) -> (result: RegistryResult)
    requires left.wf(), right.wf(),
    ensures match result {
        RegistryResult::Bot => intersection_empty(carrier, left, right),
        RegistryResult::Val(value) => value.wf() && value.carrier() == carrier && covers_intersection(carrier, &value, left, right),
    },
{
    if !field_enabled(mask) {
        return RegistryResult::Val(top(carrier));
    }
    match (carrier, left, right) {
        (Carrier::Bool, Value::Bool(a), Value::Bool(b)) => {
            let intersection = meet_normalize(a, b);
            match intersection {
            BotOr::Bot => {
                proof {
                    assert forall|x: bool| #[trigger] left.gamma_bool(x) implies !right.gamma_bool(x) by {
                        assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                    }
                }
                RegistryResult::Bot
            }
            BotOr::Val(value) => {
                proof {
                    assert forall|x: bool| #[trigger] left.gamma_bool(x) && right.gamma_bool(x)
                        implies Value::Bool(value).gamma_bool(x) by {
                        assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                    }
                }
                RegistryResult::Val(Value::Bool(value))
            }
            }
        }
        (Carrier::Int, Value::Int(a), Value::Int(b)) => {
            let intersection = meet_normalize(a, b);
            match intersection {
                BotOr::Bot => {
                    proof {
                        assert forall|x: int| #[trigger] left.gamma_int(x) implies !right.gamma_int(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Bot
                }
                BotOr::Val(value) => {
                    proof {
                        assert forall|x: int| #[trigger] left.gamma_int(x) && right.gamma_int(x)
                            implies Value::Int(value).gamma_int(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Val(Value::Int(value))
                }
            }
        }
        (Carrier::BitVec(Width::W8), Value::Bv8(a), Value::Bv8(b)) => {
            let intersection = meet_normalize(a, b);
            match intersection {
                BotOr::Bot => {
                    proof {
                        assert forall|x: u8| #[trigger] left.gamma_u8(x) implies !right.gamma_u8(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Bot
                }
                BotOr::Val(value) => {
                    proof {
                        assert forall|x: u8| #[trigger] left.gamma_u8(x) && right.gamma_u8(x)
                            implies Value::Bv8(value).gamma_u8(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Val(Value::Bv8(value))
                }
            }
        }
        (Carrier::BitVec(Width::W16), Value::Bv16(a), Value::Bv16(b)) => {
            let intersection = meet_normalize(a, b);
            match intersection {
                BotOr::Bot => {
                    proof {
                        assert forall|x: u16| #[trigger] left.gamma_u16(x) implies !right.gamma_u16(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Bot
                }
                BotOr::Val(value) => {
                    proof {
                        assert forall|x: u16| #[trigger] left.gamma_u16(x) && right.gamma_u16(x)
                            implies Value::Bv16(value).gamma_u16(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Val(Value::Bv16(value))
                }
            }
        }
        (Carrier::BitVec(Width::W32), Value::Bv32(a), Value::Bv32(b)) => {
            let intersection = meet_normalize(a, b);
            match intersection {
                BotOr::Bot => {
                    proof {
                        assert forall|x: u32| #[trigger] left.gamma_u32(x) implies !right.gamma_u32(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Bot
                }
                BotOr::Val(value) => {
                    proof {
                        assert forall|x: u32| #[trigger] left.gamma_u32(x) && right.gamma_u32(x)
                            implies Value::Bv32(value).gamma_u32(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Val(Value::Bv32(value))
                }
            }
        }
        (Carrier::BitVec(Width::W64), Value::Bv64(a), Value::Bv64(b)) => {
            let intersection = meet_normalize(a, b);
            match intersection {
                BotOr::Bot => {
                    proof {
                        assert forall|x: u64| #[trigger] left.gamma_u64(x) implies !right.gamma_u64(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Bot
                }
                BotOr::Val(value) => {
                    proof {
                        assert forall|x: u64| #[trigger] left.gamma_u64(x) && right.gamma_u64(x)
                            implies Value::Bv64(value).gamma_u64(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Val(Value::Bv64(value))
                }
            }
        }
        (Carrier::BitVec(Width::W128), Value::Bv128(a), Value::Bv128(b)) => {
            let intersection = meet_normalize(a, b);
            match intersection {
                BotOr::Bot => {
                    proof {
                        assert forall|x: u128| #[trigger] left.gamma_u128(x) implies !right.gamma_u128(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Bot
                }
                BotOr::Val(value) => {
                    proof {
                        assert forall|x: u128| #[trigger] left.gamma_u128(x) && right.gamma_u128(x)
                            implies Value::Bv128(value).gamma_u128(x) by {
                            assert(intersection.gamma(x) == (a.gamma(x) && b.gamma(x)));
                        }
                    }
                    RegistryResult::Val(Value::Bv128(value))
                }
            }
        }
        (
            Carrier::TopOnly { bits },
            Value::TopOnly { bits: left_bits },
            Value::TopOnly { bits: right_bits },
        ) if bits == *left_bits && bits == *right_bits => RegistryResult::Val(Value::TopOnly { bits }),
        // The carrier is chosen by the surface parser.  A malformed caller
        // cannot manufacture a typed conflict, so use a safe top fallback at
        // the advertised carrier rather than panicking inside saturation.
        _ => RegistryResult::Val(top(carrier)),
    }
}

/// Joins two entries at one carrier.  A disabled record has no enabled field,
/// so its least upper bound is top.  `ite` and forward stubs use this public
/// operation rather than reimplementing a carrier switch.
pub fn join(carrier: Carrier, mask: DomainSet, left: &Value, right: &Value) -> (result: Value)
    requires left.wf(), right.wf(),
    ensures result.wf(), result.carrier() == carrier, covers_both(carrier, &result, left, right),
{
    if !field_enabled(mask) {
        return top(carrier);
    }
    join_same_carrier(carrier, left, right)
}

/// Reduces an entry under the supplied domain mask. The current records have
/// exactly one available field today. It nevertheless invokes its verified
/// normalization, which is the single place future multi-field reduction will
/// be reached from the engine-facing registry.
pub fn reduce(carrier: Carrier, mask: DomainSet, value: &Value) -> (result: RegistryResult)
    requires value.wf(),
    ensures match result {
        RegistryResult::Bot => true,
        RegistryResult::Val(reduced) => reduced.wf() && reduced.carrier() == carrier,
    },
{
    if !field_enabled(mask) {
        return RegistryResult::Val(top(carrier));
    }
    macro_rules! normalize_value {
        ($value:expr, $variant:ident) => {
            match $value.normalize() {
                BotOr::Bot => RegistryResult::Bot,
                BotOr::Val(value) => RegistryResult::Val(Value::$variant(value)),
            }
        };
    }
    match (carrier, value) {
        (Carrier::Bool, Value::Bool(value)) => normalize_value!(value, Bool),
        (Carrier::Int, Value::Int(value)) => normalize_value!(value, Int),
        (Carrier::BitVec(Width::W8), Value::Bv8(value)) => normalize_value!(value, Bv8),
        (Carrier::BitVec(Width::W16), Value::Bv16(value)) => normalize_value!(value, Bv16),
        (Carrier::BitVec(Width::W32), Value::Bv32(value)) => normalize_value!(value, Bv32),
        (Carrier::BitVec(Width::W64), Value::Bv64(value)) => normalize_value!(value, Bv64),
        (Carrier::BitVec(Width::W128), Value::Bv128(value)) => normalize_value!(value, Bv128),
        (Carrier::TopOnly { bits }, Value::TopOnly { bits: value_bits }) if bits == *value_bits => {
            RegistryResult::Val(Value::TopOnly { bits })
        }
        _ => RegistryResult::Val(top(carrier)),
    }
}

/// Returns a constant only when the currently enabled available field proves
/// that the value is a singleton.
pub fn as_constant(carrier: Carrier, mask: DomainSet, value: &Value) -> Option<Const>
    requires value.wf(),
{
    if !field_enabled(mask) {
        return None;
    }
    match (carrier, value) {
        (Carrier::Bool, Value::Bool(Bool4::False)) => Some(Const {
            carrier,
            value: ConstValue::Bool(false),
        }),
        (Carrier::Bool, Value::Bool(Bool4::True)) => Some(Const {
            carrier,
            value: ConstValue::Bool(true),
        }),
        (Carrier::Int, Value::Int(facts)) => match facts.interval().bounds() {
            (Lo::Fin(lo), Hi::Fin(hi)) if lo.le(&hi) && hi.le(&lo) => Some(Const {
                carrier,
                value: ConstValue::Int(lo),
            }),
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

fn singleton_u8(facts: &Facts<u8>) -> Option<Const>
    requires facts.wf(),
{
    let (lo, hi) = facts.interval().bounds();
    if lo == hi {
        Some(Const { carrier: Carrier::BitVec(Width::W8), value: ConstValue::Bv(lo as u128) })
    } else { None }
}

fn singleton_u16(facts: &Facts<u16>) -> Option<Const>
    requires facts.wf(),
{
    let (lo, hi) = facts.interval().bounds();
    if lo == hi {
        Some(Const { carrier: Carrier::BitVec(Width::W16), value: ConstValue::Bv(lo as u128) })
    } else { None }
}

fn singleton_u32(facts: &Facts<u32>) -> Option<Const>
    requires facts.wf(),
{
    let (lo, hi) = facts.interval().bounds();
    if lo == hi {
        Some(Const { carrier: Carrier::BitVec(Width::W32), value: ConstValue::Bv(lo as u128) })
    } else { None }
}

fn singleton_u64(facts: &Facts<u64>) -> Option<Const>
    requires facts.wf(),
{
    let (lo, hi) = facts.interval().bounds();
    if lo == hi {
        Some(Const { carrier: Carrier::BitVec(Width::W64), value: ConstValue::Bv(lo as u128) })
    } else { None }
}

fn singleton_u128(facts: &Facts<u128>) -> Option<Const>
    requires facts.wf(),
{
    let (lo, hi) = facts.interval().bounds();
    if lo == hi {
        Some(Const { carrier: Carrier::BitVec(Width::W128), value: ConstValue::Bv(lo) })
    } else { None }
}

fn value_carrier(value: &Value) -> (carrier: Carrier)
    ensures carrier == value.carrier(),
{
    match value {
        Value::Bool(_) => Carrier::Bool,
        Value::Int(_) => Carrier::Int,
        Value::Bv8(_) => Carrier::BitVec(Width::W8),
        Value::Bv16(_) => Carrier::BitVec(Width::W16),
        Value::Bv32(_) => Carrier::BitVec(Width::W32),
        Value::Bv64(_) => Carrier::BitVec(Width::W64),
        Value::Bv128(_) => Carrier::BitVec(Width::W128),
        Value::TopOnly { bits } => Carrier::TopOnly { bits: *bits },
    }
}

fn result_carrier(op: Op, args: &[Value]) -> Carrier {
    match op {
        Op::Concat { result } => result,
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
fn unary_arg(args: &[Value]) -> (result: Option<&Value>)
    requires args.len() > 0 ==> args[0].wf(),
    ensures match result { Some(value) => value.wf(), None => true },
{
    if args.len() == 1 {
        Some(&args[0])
    } else {
        None
    }
}

fn binary_args(args: &[Value]) -> (result: Option<(&Value, &Value)>)
    requires
        args.len() > 0 ==> args[0].wf(),
        args.len() > 1 ==> args[1].wf(),
    ensures match result { Some((left, right)) => left.wf() && right.wf(), None => true },
{
    if args.len() == 2 {
        Some((&args[0], &args[1]))
    } else {
        None
    }
}

fn ternary_args(args: &[Value]) -> (result: Option<(&Value, &Value, &Value)>)
    requires
        args.len() > 0 ==> args[0].wf(),
        args.len() > 1 ==> args[1].wf(),
        args.len() > 2 ==> args[2].wf(),
    ensures match result { Some((first, second, third)) => first.wf() && second.wf() && third.wf(), None => true },
{
    if args.len() == 3 {
        Some((&args[0], &args[1], &args[2]))
    } else {
        None
    }
}

fn input_masks_enabled(masks: TransferMasks, args: &[Value]) -> bool {
    match args.len() {
        0 => true,
        1 => field_enabled(masks.args[0]),
        2 => field_enabled(masks.args[0]) && field_enabled(masks.args[1]),
        3 => {
            field_enabled(masks.args[0])
                && field_enabled(masks.args[1])
                && field_enabled(masks.args[2])
        }
        _ => false,
    }
}

pub fn forward(op: Op, masks: TransferMasks, args: &[Value]) -> Value
    requires
        args.len() <= 3,
        args.len() > 0 ==> args[0].wf(),
        args.len() > 1 ==> args[1].wf(),
        args.len() > 2 ==> args[2].wf(),
{
    let carrier = result_carrier(op, args);
    if !field_enabled(masks.result) {
        return top(carrier);
    }
    if !input_masks_enabled(masks, args) {
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

    match (op, unary_arg(args), binary_args(args), ternary_args(args)) {
        (Op::Not, Some(Value::Bool(a)), _, _) => Value::Bool(a.not()),
        (Op::And, _, Some((Value::Bool(a), Value::Bool(b))), _) => Value::Bool(a.and(b)),
        (Op::Or, _, Some((Value::Bool(a), Value::Bool(b))), _) => Value::Bool(a.or(b)),
        (Op::Xor, _, Some((Value::Bool(a), Value::Bool(b))), _) => Value::Bool(a.not().eq(b)),
        (Op::Implies, _, Some((Value::Bool(a), Value::Bool(b))), _) => Value::Bool(a.not().or(b)),
        (Op::Eq, _, Some((Value::Bool(a), Value::Bool(b))), _) => Value::Bool(a.eq(b)),
        (Op::Ite, _, _, Some((Value::Bool(c), then_value, else_value))) => {
            let branch_carrier = value_carrier(then_value);
            if c.is_true() {
                duplicate(then_value)
            } else if c.is_false() {
                duplicate(else_value)
            } else if same(branch_carrier, value_carrier(else_value)) {
                join(branch_carrier, masks.result, then_value, else_value)
            } else {
                top(carrier)
            }
        }
        (Op::Add, _, Some((Value::Int(a), Value::Int(b))), _) => {
            Value::Int(<FactsZ as Arith<Euclid>>::add(a, b))
        }
        (Op::Sub, _, Some((Value::Int(a), Value::Int(b))), _) => {
            Value::Int(<FactsZ as Arith<Euclid>>::sub(a, b))
        }
        (Op::Neg, Some(Value::Int(a)), _, _) => Value::Int(<FactsZ as Arith<Euclid>>::neg(a)),
        (Op::Div, _, Some((Value::Int(a), Value::Int(b))), _) => int_div(a, b),
        (Op::Mod, _, Some((Value::Int(a), Value::Int(b))), _) => int_rem(a, b),
        (Op::BvAdd, _, Some((Value::Bv8(a), Value::Bv8(b))), _) => binary_arith!(a, b, Bv8, Unsigned<u8>, add),
        (Op::BvAdd, _, Some((Value::Bv16(a), Value::Bv16(b))), _) => {
            binary_arith!(a, b, Bv16, Unsigned<u16>, add)
        }
        (Op::BvAdd, _, Some((Value::Bv32(a), Value::Bv32(b))), _) => {
            binary_arith!(a, b, Bv32, Unsigned<u32>, add)
        }
        (Op::BvAdd, _, Some((Value::Bv64(a), Value::Bv64(b))), _) => {
            binary_arith!(a, b, Bv64, Unsigned<u64>, add)
        }
        (Op::BvAdd, _, Some((Value::Bv128(a), Value::Bv128(b))), _) => {
            binary_arith!(a, b, Bv128, Unsigned<u128>, add)
        }
        (Op::BvSub, _, Some((Value::Bv8(a), Value::Bv8(b))), _) => binary_arith!(a, b, Bv8, Unsigned<u8>, sub),
        (Op::BvSub, _, Some((Value::Bv16(a), Value::Bv16(b))), _) => {
            binary_arith!(a, b, Bv16, Unsigned<u16>, sub)
        }
        (Op::BvSub, _, Some((Value::Bv32(a), Value::Bv32(b))), _) => {
            binary_arith!(a, b, Bv32, Unsigned<u32>, sub)
        }
        (Op::BvSub, _, Some((Value::Bv64(a), Value::Bv64(b))), _) => {
            binary_arith!(a, b, Bv64, Unsigned<u64>, sub)
        }
        (Op::BvSub, _, Some((Value::Bv128(a), Value::Bv128(b))), _) => {
            binary_arith!(a, b, Bv128, Unsigned<u128>, sub)
        }
        (Op::BvNeg, Some(Value::Bv8(a)), _, _) => unary_arith!(a, Bv8, Unsigned<u8>),
        (Op::BvNeg, Some(Value::Bv16(a)), _, _) => unary_arith!(a, Bv16, Unsigned<u16>),
        (Op::BvNeg, Some(Value::Bv32(a)), _, _) => unary_arith!(a, Bv32, Unsigned<u32>),
        (Op::BvNeg, Some(Value::Bv64(a)), _, _) => unary_arith!(a, Bv64, Unsigned<u64>),
        (Op::BvNeg, Some(Value::Bv128(a)), _, _) => unary_arith!(a, Bv128, Unsigned<u128>),
        (Op::BvMul, _, Some((Value::Bv8(a), Value::Bv8(b))), _) => binary_mul!(a, b, Bv8, Unsigned<u8>),
        (Op::BvMul, _, Some((Value::Bv16(a), Value::Bv16(b))), _) => binary_mul!(a, b, Bv16, Unsigned<u16>),
        (Op::BvMul, _, Some((Value::Bv32(a), Value::Bv32(b))), _) => binary_mul!(a, b, Bv32, Unsigned<u32>),
        (Op::BvMul, _, Some((Value::Bv64(a), Value::Bv64(b))), _) => binary_mul!(a, b, Bv64, Unsigned<u64>),
        (Op::BvMul, _, Some((Value::Bv128(a), Value::Bv128(b))), _) => binary_mul!(a, b, Bv128, Unsigned<u128>),
        (Op::BvUdiv, _, Some((Value::Bv8(a), Value::Bv8(b))), _) => Value::Bv8(unsigned_div(a, b)),
        (Op::BvUdiv, _, Some((Value::Bv16(a), Value::Bv16(b))), _) => Value::Bv16(unsigned_div(a, b)),
        (Op::BvUdiv, _, Some((Value::Bv32(a), Value::Bv32(b))), _) => Value::Bv32(unsigned_div(a, b)),
        (Op::BvUdiv, _, Some((Value::Bv64(a), Value::Bv64(b))), _) => Value::Bv64(unsigned_div(a, b)),
        (Op::BvUdiv, _, Some((Value::Bv128(a), Value::Bv128(b))), _) => Value::Bv128(unsigned_div(a, b)),
        (Op::BvUrem, _, Some((Value::Bv8(a), Value::Bv8(b))), _) => Value::Bv8(unsigned_rem(a, b)),
        (Op::BvUrem, _, Some((Value::Bv16(a), Value::Bv16(b))), _) => Value::Bv16(unsigned_rem(a, b)),
        (Op::BvUrem, _, Some((Value::Bv32(a), Value::Bv32(b))), _) => Value::Bv32(unsigned_rem(a, b)),
        (Op::BvUrem, _, Some((Value::Bv64(a), Value::Bv64(b))), _) => Value::Bv64(unsigned_rem(a, b)),
        (Op::BvUrem, _, Some((Value::Bv128(a), Value::Bv128(b))), _) => Value::Bv128(unsigned_rem(a, b)),
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
pub fn backward(op: Op, masks: TransferMasks, result: &Value, args: &[Value]) -> BackwardResult
    requires
        args.len() <= 3,
        result.wf(),
        args.len() > 0 ==> args[0].wf(),
        args.len() > 1 ==> args[1].wf(),
        args.len() > 2 ==> args[2].wf(),
{
    if op == Op::Ite && args.len() == 3 {
        return backward_ite(masks, result, args);
    }
    backward_identity(masks, args)
}

/// Preserve each operand for a missing backward transfer.  This is sound: it
/// never grows a record and therefore keeps every satisfying concrete tuple.
fn backward_identity(masks: TransferMasks, args: &[Value]) -> BackwardResult
    requires
        args.len() <= 3,
        args.len() > 0 ==> args[0].wf(),
        args.len() > 1 ==> args[1].wf(),
        args.len() > 2 ==> args[2].wf(),
{
    let mut values = [top(Carrier::TopOnly { bits: 0 }), top(Carrier::TopOnly { bits: 0 }), top(Carrier::TopOnly { bits: 0 })];
    if !args.is_empty() {
        values[0] = if field_enabled(masks.args[0]) {
            duplicate(&args[0])
        } else {
            top(value_carrier(&args[0]))
        };
    }
    if args.len() > 1 {
        values[1] = if field_enabled(masks.args[1]) {
            duplicate(&args[1])
        } else {
            top(value_carrier(&args[1]))
        };
    }
    if args.len() > 2 {
        values[2] = if field_enabled(masks.args[2]) {
            duplicate(&args[2])
        } else {
            top(value_carrier(&args[2]))
        };
    }
    BackwardResult::Val {
        values,
        arity: args.len(),
    }
}

/// The backward `ite` rule from eclass-analysis §6.  It intersects each
/// branch with the requested result, removes an impossible branch from the
/// condition, and reports bottom when neither branch can produce the result.
fn backward_ite(masks: TransferMasks, result: &Value, args: &[Value]) -> BackwardResult
    requires
        args.len() == 3,
        result.wf(),
        args[0].wf(),
        args[1].wf(),
        args[2].wf(),
{
    if !field_enabled(masks.result)
        || !field_enabled(masks.args[0])
        || !field_enabled(masks.args[1])
        || !field_enabled(masks.args[2])
    {
        return backward_identity(masks, args);
    }
    let (condition, then_value, else_value) = (&args[0], &args[1], &args[2]);
    let Value::Bool(condition) = condition else {
        return backward_identity(masks, args);
    };
    let carrier = value_carrier(then_value);
    if !same(carrier, value_carrier(else_value)) || !same(carrier, value_carrier(result)) {
        return backward_identity(masks, args);
    }

    let true_condition = meet(
        Carrier::Bool,
        masks.args[0],
        &Value::Bool(condition.dup()),
        &Value::Bool(Bool4::True),
    );
    let false_condition = meet(
        Carrier::Bool,
        masks.args[0],
        &Value::Bool(condition.dup()),
        &Value::Bool(Bool4::False),
    );
    let then_meet = meet(carrier, masks.result, then_value, result);
    let else_meet = meet(carrier, masks.result, else_value, result);

    let true_live = matches!(true_condition, RegistryResult::Val(_))
        && matches!(then_meet, RegistryResult::Val(_));
    let false_live = matches!(false_condition, RegistryResult::Val(_))
        && matches!(else_meet, RegistryResult::Val(_));
    if !true_live && !false_live {
        return BackwardResult::Bot;
    }

    let refined_condition = match (true_live, false_live) {
        (true, true) => duplicate(&args[0]),
        (true, false) => Value::Bool(Bool4::True),
        (false, true) => Value::Bool(Bool4::False),
        (false, false) => unreachable!(),
    };
    let refined_then = if true_live {
        match then_meet {
            RegistryResult::Val(value) => value,
            RegistryResult::Bot => unreachable!(),
        }
    } else {
        duplicate(then_value)
    };
    let refined_else = if false_live {
        match else_meet {
            RegistryResult::Val(value) => value,
            RegistryResult::Bot => unreachable!(),
        }
    } else {
        duplicate(else_value)
    };
    BackwardResult::Val {
        values: [refined_condition, refined_then, refined_else],
        arity: 3,
    }
}

/// A decided `ite` condition selects the zero-based branch index in an
/// e-node's argument list: 1 for the then branch and 2 for the else branch.
pub fn decided_branch(op: Op, condition: &Value) -> Option<usize> {
    match (op, condition) {
        (Op::Ite, Value::Bool(value)) if value.is_true() => Some(1),
        (Op::Ite, Value::Bool(value)) if value.is_false() => Some(2),
        _ => None,
    }
}

fn join_same_carrier(carrier: Carrier, left: &Value, right: &Value) -> (result: Value)
    requires left.wf(), right.wf(),
    ensures result.wf(), result.carrier() == carrier, covers_both(carrier, &result, left, right),
{
    match (carrier, left, right) {
        (Carrier::Bool, Value::Bool(a), Value::Bool(b)) => Value::Bool(a.join(b)),
        (Carrier::Int, Value::Int(a), Value::Int(b)) => Value::Int(a.join(b)),
        (Carrier::BitVec(Width::W8), Value::Bv8(a), Value::Bv8(b)) => Value::Bv8(a.join(b)),
        (Carrier::BitVec(Width::W16), Value::Bv16(a), Value::Bv16(b)) => Value::Bv16(a.join(b)),
        (Carrier::BitVec(Width::W32), Value::Bv32(a), Value::Bv32(b)) => Value::Bv32(a.join(b)),
        (Carrier::BitVec(Width::W64), Value::Bv64(a), Value::Bv64(b)) => Value::Bv64(a.join(b)),
        (Carrier::BitVec(Width::W128), Value::Bv128(a), Value::Bv128(b)) => Value::Bv128(a.join(b)),
        (
            Carrier::TopOnly { bits },
            Value::TopOnly { bits: left_bits },
            Value::TopOnly { bits: right_bits },
        ) if bits == *left_bits && bits == *right_bits => Value::TopOnly { bits },
        _ => top(carrier),
    }
}

/// Adds the SMT-LIB `bvudiv x 0 = all-ones` case to the verified transfer
/// over nonzero divisors.  `DivRem` deliberately leaves zero divisors out of
/// its contract, so the registry is the one layer that makes this total.
fn unsigned_div<W: Word>(dividend: &Facts<W>, divisor: &Facts<W>) -> Facts<W>
    requires dividend.wf(), divisor.wf(),
{
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
fn unsigned_rem<W: Word>(dividend: &Facts<W>, divisor: &Facts<W>) -> Facts<W>
    requires dividend.wf(), divisor.wf(),
{
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

/// SMT-LIB leaves Int division by zero unspecified.  The verified `DivRem`
/// result covers nonzero divisors; joining top when zero is possible is the
/// sound registry interpretation of the unspecified case.
fn int_div(dividend: &FactsZ, divisor: &FactsZ) -> Value
    requires dividend.wf(), divisor.wf(),
{
    let (nonzero, _) = <FactsZ as DivRem<Euclid>>::div(dividend, divisor);
    if <FactsZ as DivRem<Euclid>>::contains_zero(divisor) {
        Value::Int(<FactsZ as Domain>::top())
    } else {
        match nonzero {
            BotOr::Val(value) => Value::Int(value),
            BotOr::Bot => Value::Int(<FactsZ as Domain>::top()),
        }
    }
}

/// See [`int_div`].
fn int_rem(dividend: &FactsZ, divisor: &FactsZ) -> Value
    requires dividend.wf(), divisor.wf(),
{
    let (nonzero, _) = <FactsZ as DivRem<Euclid>>::rem(dividend, divisor);
    if <FactsZ as DivRem<Euclid>>::contains_zero(divisor) {
        Value::Int(<FactsZ as Domain>::top())
    } else {
        match nonzero {
            BotOr::Val(value) => Value::Int(value),
            BotOr::Bot => Value::Int(<FactsZ as Domain>::top()),
        }
    }
}

fn same(a: Carrier, b: Carrier) -> bool {
    match (a, b) {
        (Carrier::Bool, Carrier::Bool) | (Carrier::Int, Carrier::Int) => true,
        (Carrier::BitVec(x), Carrier::BitVec(y)) => x == y,
        (Carrier::TopOnly { bits: x }, Carrier::TopOnly { bits: y }) => x == y,
        _ => false,
    }
}
}

fn is_bv(c: Carrier) -> bool {
    matches!(c, Carrier::BitVec(_) | Carrier::TopOnly { .. })
}

fn carrier_bits(c: Carrier) -> Option<u32> {
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
        // These operators require source-level indices (`i`, `j`, or `K`) to
        // determine their output width. `op` deliberately rejects them until
        // the surface interface carries those indices; accepting them here
        // would construct a value at the wrong carrier.
        "extract" | "zero_extend" | "sign_extend" => return Err(OpError::Signature),
        "ite" => {
            return if args.len() == 3 && args[0] == Bool && same(args[1], args[2]) {
                Ok((Op::Ite, args[1]))
            } else {
                Err(OpError::Signature)
            };
        }
        "concat" if args.len() == 2 && is_bv(args[0]) && is_bv(args[1]) => {
            let Some(bits) = carrier_bits(args[0])
                .unwrap()
                .checked_add(carrier_bits(args[1]).unwrap())
            else {
                return Err(OpError::Signature);
            };
            let Some(result) = carrier_of_bitvec(bits) else {
                return Err(OpError::Signature);
            };
            return Ok((Op::Concat { result }, result));
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
            Ok((
                Op::Concat {
                    result: Carrier::BitVec(Width::W16),
                },
                Carrier::BitVec(Width::W16),
            ))
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
        assert!(matches!(
            top(Carrier::TopOnly { bits: 7 }),
            Value::TopOnly { bits: 7 }
        ));
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
        match forward(Op::BvAdd, TransferMasks::uniform(mask), &[left, right]) {
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
            TransferMasks::uniform(mask),
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
            Some(Const {
                carrier: Carrier::BitVec(Width::W8),
                value: ConstValue::Bv(7),
            })
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
        let refined = backward(
            Op::BvAdd,
            TransferMasks::uniform(DomainSet::from_bit(0)),
            &original,
            &[argument],
        );
        match refined {
            BackwardResult::Val { values, arity } => {
                assert_eq!(arity, 1);
                match &values[0] {
                    Value::Bv8(value) => assert_eq!(value.interval().bounds(), (7, 7)),
                    _ => panic!("backward transfer changed the argument carrier"),
                }
            }
            BackwardResult::Bot => panic!("a fallback transfer cannot create bottom"),
        }
    }
}
