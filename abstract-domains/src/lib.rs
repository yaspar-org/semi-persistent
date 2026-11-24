// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! semi-persistent-abstract-domains: Verified abstract domains for bitvector analysis.
//!
//! Provides Tnums (tristate numbers), Anums (additive tristate numbers),
//! Unums (horizontally composable additive tristate numbers),
//! and Intervals, formally verified in Verus.
//!
//! Architecture:
//! - Layer 1: bools (Bit) + nats — infinite bitstrings on nat
//! - Layer 2: tbit (TBit) + tnum (Tnum) + anum (Anum) + unum (Unum) + div — abstract domains with soundness proofs
//! - Layer 3: chopped (ChoppedTnum, ChoppedAnum, ChoppedUnum) — bounded-width simulation
//! - Layer 4: exec_tnum, exec_anum, exec_unum (ExecTnum<W>, ExecAnum<W>,
//!   ExecUnum<W>, generic over bitword::BitWord): executable implementations,
//!   proved once for every width. domains names them, with Interval<W>, at
//!   u8/u16/u32/u64.
//! - Shared interface: lattice (Domain, BotOr), word (Word), semantics
//!   (Semantics), transfer (Arith, DivRem, DivZero); reference domains
//!   interval (Interval<W>) and interval_z (IntervalZ over ibig::IBig).
//!   See doc/domain-traits.md.
//! - Reduced products: reduce (Channel, Refine, Product), the fact records
//!   facts (Facts<W>, transfers in facts_ops) and facts_z (FactsZ), and bool4
//!   (Bool4). See doc/reduced-product.md.

pub mod anum;
pub mod arithmetic;
pub mod bitword;
pub mod bool4;
pub mod bools;
pub mod chopped;
pub mod congruence;
pub mod congruence_laws;
pub mod div;
pub mod domains;
pub mod exec_anum;
pub mod exec_tnum;
pub mod exec_unum;
pub mod facts;
pub mod facts_ops;
pub mod facts_z;
pub mod ibig;
pub mod interval;
pub mod interval_z;
pub mod lattice;
pub mod nats;
pub mod pair_mul;
pub mod reduce;
pub mod semantics;
pub mod sign;
pub mod strided;
pub mod tbit;
pub mod tnum;
pub mod transfer;
pub mod unum;
pub mod word;
pub mod wrapped;
