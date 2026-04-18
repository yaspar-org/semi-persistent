// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! semi-persistent-abstract-domains: Verified abstract domains for bitvector analysis.
//!
//! Provides Tnums (tristate numbers), Anums (additive tristate numbers),
//! Unums (horizontally composable additive tristate numbers),
//! Intervals, and their reduced product ReducedProduct — formally verified in Verus.
//!
//! Architecture:
//! - Layer 1: bools (Bit) + nats — infinite bitstrings on nat
//! - Layer 2: tbit (TBit) + tnum (Tnum) + anum (Anum) + unum (Unum) + div — abstract domains with soundness proofs
//! - Layer 3: reg (TnumReg, UnumReg) — bounded register simulation
//! - Layer 4: exec_tnum + domains (ExecTnum, ExecAnum, ExecUnum, Interval, ReducedProduct) — executable u8/u16/u32/u64/u128 implementations

pub mod anum;
pub mod bools;
pub mod chopped;
pub mod demo;
pub mod div;
pub mod domains;
pub mod exec_tnum;
pub mod nats;
pub mod tbit;
pub mod tnum;
pub mod unum;
