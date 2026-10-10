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
    /// `..name` between children: a bare sequence of a sequence pattern
    /// (`doc/sequence-patterns.md`). A `..name` right after the operator or right
    /// before `)` is the `prefix` or `suffix` rest instead, as before.
    Seq(String, Span),
    /// `(..name[:mult] base [:except other])`: a filtered sequence, with an optional
    /// multiplicity annotation (AC).
    Filter {
        name: String,
        mult: Option<MultSpec>,
        base: Box<SurfacePattern>,
        except: Option<(String, Span)>,
        span: Span,
    },
}

impl SurfacePatChild {
    /// Whether this child is a sequence-pattern construct, which only sequence
    /// rules accept.
    pub fn is_sequence(&self) -> bool {
        matches!(
            self,
            SurfacePatChild::Seq(..) | SurfacePatChild::Filter { .. }
        )
    }
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
        /// `:flatten`: the rule matches its n-ary operators on the flattened form.
        flatten: bool,
        /// `:ruleset name`, or `None` for the default ruleset.
        ruleset: Option<String>,
    },
    Rule {
        body: Vec<SurfacePattern>,
        head: Vec<Action>,
        /// `:flatten`, as for `Rewrite`.
        flatten: bool,
        /// `:ruleset name`, or `None` for the default ruleset.
        ruleset: Option<String>,
    },
    /// A rewrite whose left-hand side has a collection pattern `(each name pat)`;
    /// see [`crate::collection`].
    CollectionRewrite(crate::collection::SurfaceRule),
    Pass(Command),
}
