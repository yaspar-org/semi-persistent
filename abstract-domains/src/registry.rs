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
use crate::lattice::Domain;

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
}
