// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Machine-checked lemmas for a positional anti-unification model.
//!
//! The solver lives in `egraph`, which is outside the Verus toolchain, so
//! nothing there carries a proof obligation. This crate holds the part of the
//! argument that can be checked mechanically: the properties of the objective
//! and of the recurrence, stated over an abstract model rather than over the
//! implementation.
//!
//! What that does and does not buy. The crate proves objective-order and
//! representation lemmas, plus a lower-bound theorem for any function
//! satisfying two recurrence inequalities. It does not define the intended
//! least recurrence solution, prove that solution is attained, state
//! `D* = OPT`, or refine the production AC/ACI solver to this positional model.
//! `egraph/tests/au_oracle.rs` provides finite implementation evidence. See
//! `doc/claims.md` for the exact claim and the proof roadmap.

pub mod completeness;
pub mod objective;
pub mod recurrence;
pub mod terms;
