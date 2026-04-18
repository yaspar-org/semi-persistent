// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Surface AST — uniform syntax before resolve-time dispatch.
//!
//! `(op child1 child2 ..rest)` looks the same regardless of operator kind.
//! The lowering pass inspects `OpKind` to produce the strongly-typed `Pattern`.

use crate::ast::{Action, Command, MultSpec, RhsTerm, Span};

/// A child in a surface pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SurfacePatChild {
    /// Single element pattern.
    Elem(SurfacePattern),
    /// Element with multiplicity: `x:2`, `x:k`, `x:k>=2`.
    ElemMult(SurfacePattern, MultSpec),
}

/// Uniform pattern — `(op children...)` with optional `..rest` and `:mult`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SurfacePattern {
    /// Bare identifier = pattern variable.
    Var(String, Span),
    /// Literal constant.
    Lit(String, Span),
    /// `(op [..pre] child1 child2 ... [..suf])`.
    App {
        op: String,
        prefix: Option<(String, Span)>,
        children: Vec<SurfacePatChild>,
        suffix: Option<(String, Span)>,
        span: Span,
    },
}

impl SurfacePattern {
    pub fn span(&self) -> Span {
        match self {
            SurfacePattern::Var(_, s) | SurfacePattern::Lit(_, s) => *s,
            SurfacePattern::App { span, .. } => *span,
        }
    }
}

/// Surface command — pattern-bearing commands use `SurfacePattern`,
/// everything else passes through as `Command`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SurfaceCommand {
    Rewrite {
        lhs: SurfacePattern,
        rhs: RhsTerm,
        when: Vec<SurfacePattern>,
        subsume: bool,
    },
    Rule {
        body: Vec<SurfacePattern>,
        head: Vec<Action>,
    },
    Pass(Command),
}
