// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Companion SAT/SMT layer for the semi-persistent e-graph.
//!
//! The e-graph crate is a saturation engine with no notion of Boolean
//! search; this crate adds one, following the architecture of Z3's legacy
//! `smt` core: a SAT engine owns assignments, decisions, and clause
//! learning, and the e-graph serves as the theory backend for equality
//! reasoning. The workspace's semi-persistent `mark`/`restore` protocol
//! replaces the hand-written trail machinery such solvers normally carry —
//! one restore token rewinds merges, node creation, and proof edges
//! together, and restoring to an ancestor token is non-chronological
//! backjumping in a single call.
//!
//! Layer 0 ([`euf`]) is the ground theory interface: equality atoms,
//! assertion, congruence-aware consistency checking, and conflict
//! explanation in terms of asserted literals. The CDCL driver builds on it
//! in a later layer.

pub mod euf;

pub use euf::{AtomId, AtomId64, CheckResult, Euf, Euf31, Euf63, EufConfig, EufToken, Lit};
