// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Solver-agnostic extraction from e-graphs, with a ladder of encodings and
//! programmable cost functions.
//!
//! A cost function is ordinary Rust (or a script in Roto, [`script`]) that reads the
//! variables a rung exposes, builds order-encoded integers with the operators of [`oint`],
//! adds constraints, and states an objective. This module lowers all of it to CNF for its
//! internal incremental solver or to OPB for a third-party one, writes an answer-set
//! program or a MiniZinc model for criteria in those languages, breaks cycles for all of
//! them, and reports the cost of the extracted term by interpreting the cost expression
//! rather than by reading the solver's objective.
//!
//! Costs are exact ([`cost::Cost`]), and every number written for a solver is checked
//! against that solver's own range first (`tests/data/solver_width/README.md`).
//!
//! It was four crates until 2026-10-06 (`extract-api`, `extract-script`, `mltl-cost`, and
//! `pb-verus`), in a second repository, reached through a `cost-models` feature. The user
//! asked for one crate and for cost models in the default build, so the modules moved here
//! and the feature is gone.
//!
//! # What the clause encoders guarantee
//!
//! [`totalizer`] emits one direction only: negating an emitted indicator bounds a weighted
//! sum. Over the assignment model of [`cnf`], writing `a` for an assignment and `ws` for
//! the weighted literals:
//!
//! ```text
//! cnf(a, emitted)  /\  !a.lit(indicator_at_least(t))  ==>  weighted_sum(a, ws) < t
//! ```
//!
//! That property is **not machine-checked**. It is established by exhaustive differential
//! testing (`tests/pb_exhaustive.rs`, `tests/pb_windowed.rs`): every assignment over the
//! input literals of small instances, the emitted clause set solved by enumeration, and the
//! implication checked against a directly computed sum. The Verus `spec fn`s that stated it
//! were dropped with the crate's `vstd` dependency; they return when the property is
//! verified rather than tested (user, 2026-10-06).
//!
//! The converse does not hold, deliberately: an indicator may be true while the sum is
//! below its threshold, because only the forward clause family is emitted. [`totalizer`]
//! records why.
//!
//! See `doc/extraction/api.md#part-1-the-api` in the `ltl-eqsat` repository, and §11.2
//! of the design notes (`egraph/doc/design/11-extraction.md`).

pub mod asp;
pub mod cnf;
pub mod cost;
pub mod dpw;
pub mod graph;
pub mod lp;
pub mod mltl_cost;
pub mod mzn;
pub mod oint;
pub mod pb;
pub mod rung;
pub mod script;
pub mod seq;
pub mod solve;
pub mod target;
pub mod totalizer;

pub use cnf::Lit;
pub use cost::{Cost, CostWidth};
