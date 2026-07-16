// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! AST types for the Semper surface language.
//!
//! All names are strings at this stage; resolution to OpId/SortId/VarId
//! happens in a later pass.

macro_rules! typed_var_id {
    ($(#[doc = $doc:expr] pub struct $name:ident;)*) => {$(
        #[doc = $doc]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u16);
        impl $name {
            pub const fn new(x: u16) -> Self { Self(x) }
            pub const fn idx(self) -> usize { self.0 as usize }
        }
    )*};
}

typed_var_id! {
    #[doc = "E-node variable (single G binding) — raw flatten namespace."]
    pub struct VarId;
    #[doc = "Sequence rest variable (A nodes, &[G] slice into pool)."]
    pub struct SeqVarId;
    #[doc = "Set rest variable (ACI nodes, &[G] slice into pool)."]
    pub struct SetVarId;
    #[doc = "Multiset rest variable (AC nodes, &[(G,u32)] slice into pool)."]
    pub struct MsetVarId;
    #[doc = "Multiplicity variable (single u32 binding)."]
    pub struct MultVarId;
    #[doc = "Literal value variable (single LitValId binding from OpKind::Lit nodes)."]
    pub struct LitValVarId;
    #[doc = "Global variable (let-bound, resolved at match time from global bindings)."]
    pub struct GlobalVarId;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

/// Byte-offset range `[start, end)` into the original source string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Span {
    /// No source location available.
    #[default]
    Dummy,
    /// Byte offsets `[start, end)` into the original source string.
    Range { start: u32, end: u32 },
}

impl Span {
    pub const fn new(start: u32, end: u32) -> Self {
        Self::Range { start, end }
    }
}

/// Multiplicity constraint on an AC element.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultSpec {
    Exact(u64),
    Var {
        name: String,
        constraint: Option<(CmpOp, u64)>,
    },
}

// ---------------------------------------------------------------------------
// Patterns (LHS of rules) — bare ident = variable, (op ...) = application
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    /// Bare identifier = pattern variable.
    Var(String, Span),
    /// Literal constant (integer, rational, bool).
    Lit(String, Span),
    /// `(op p1 p2 ...)` — plain/C application (including nullary `(op)`).
    Plain {
        op: String,
        children: Vec<Pattern>,
        span: Span,
    },
    /// `(op [p1 p2 ...])` — A exact.
    AExact {
        op: String,
        children: Vec<Pattern>,
        span: Span,
    },
    /// `(op [..pre p1 ...])` — A with prefix rest.
    APrefix {
        op: String,
        rest: String,
        fixed: Vec<Pattern>,
        span: Span,
    },
    /// `(op [p1 ... ..suf])` — A with suffix rest.
    ASuffix {
        op: String,
        fixed: Vec<Pattern>,
        rest: String,
        span: Span,
    },
    /// `(op [..pre p1 ... ..suf])` — A with both rests.
    ABoth {
        op: String,
        pre: String,
        fixed: Vec<Pattern>,
        suf: String,
        span: Span,
    },
    /// `(op {e1:m1 e2:m2 ...})` — AC exact.
    ACExact {
        op: String,
        elems: Vec<(Pattern, MultSpec)>,
        span: Span,
    },
    /// `(op {e1:m1 ... ..rest})` — AC subset.
    ACSub {
        op: String,
        elems: Vec<(Pattern, MultSpec)>,
        rest: String,
        span: Span,
    },
    /// `(op {e1 e2 ...})` — ACI exact.
    ACIExact {
        op: String,
        elems: Vec<Pattern>,
        span: Span,
    },
    /// `(op {e1 ... ..rest})` — ACI subset.
    ACISub {
        op: String,
        elems: Vec<Pattern>,
        rest: String,
        span: Span,
    },
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Var(_, s) | Pattern::Lit(_, s) => *s,
            Pattern::Plain { span, .. }
            | Pattern::AExact { span, .. }
            | Pattern::APrefix { span, .. }
            | Pattern::ASuffix { span, .. }
            | Pattern::ABoth { span, .. }
            | Pattern::ACExact { span, .. }
            | Pattern::ACSub { span, .. }
            | Pattern::ACIExact { span, .. }
            | Pattern::ACISub { span, .. } => *span,
        }
    }
}

// ---------------------------------------------------------------------------
// Terms (ground — no variables, plain S-expr, canonized post-parse)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Lit(String, Span),
    App {
        op: String,
        children: Vec<Term>,
        span: Span,
    },
}

impl Term {
    pub fn span(&self) -> Span {
        match self {
            Term::Lit(_, s) => *s,
            Term::App { span, .. } => *span,
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Lit(s, _) => write!(f, "{s}"),
            Term::App { op, children, .. } => {
                write!(f, "({op}")?;
                for c in children {
                    write!(f, " {c}")?;
                }
                write!(f, ")")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// RHS terms (rewrite right-hand side — variables + rest splicing)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RhsTerm {
    Var(String, Span),
    Lit(String, Span),
    App {
        op: String,
        children: Vec<RhsChild>,
        span: Span,
    },
}

impl RhsTerm {
    pub fn span(&self) -> Span {
        match self {
            RhsTerm::Var(_, s) | RhsTerm::Lit(_, s) => *s,
            RhsTerm::App { span, .. } => *span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RhsChild {
    Term(RhsTerm),
    /// `..name` — splice rest variable contents.
    Splice(String, Span),
    /// `..{body for v in source [if guard]}` — set comprehension.
    SetComp {
        body: Box<RhsTerm>,
        var: String,
        source: String,
        filter: Option<Box<RhsTerm>>,
        span: Span,
    },
    /// `..{body:mult for v:k in source [if guard]}` — multiset comprehension.
    MsetComp {
        body: Box<RhsTerm>,
        mult: MultExpr,
        var: String,
        mult_var: String,
        source: String,
        filter: Option<Box<RhsTerm>>,
        span: Span,
    },
    /// `..[body for v in source [if guard]]` — sequence comprehension.
    SeqComp {
        body: Box<RhsTerm>,
        var: String,
        source: String,
        filter: Option<Box<RhsTerm>>,
        span: Span,
    },
}

/// Multiplicity expression in RHS multiset comprehension.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultExpr {
    Lit(u64),
    Var(String),
}

// ---------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------

/// A single composable algebraic-property tag on a function declaration. Tags combine freely
/// at the surface (`:assoc :comm :idempotent`); the sortcheck resolver maps a tag *set* to a
/// concrete `OpKind` and validates the combination (see `doc/design/ac-algebraic-properties.md`
/// Facet A). The old pre-combined `:assoc-comm` / `:assoc-comm-idem` are accepted as aliases
/// that the parser expands into these basic tags.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgTag {
    Comm,
    Assoc,
    AssocLeft,
    AssocRight,
    /// `x∘x = x` (idempotent, set representation, dedup).
    Idempotent,
    /// `x∘x = e` (nilpotent); optional order `n` (default 2). Requires `Identity`.
    Nilpotent(Option<u8>),
    /// Identity/unit element `e` (`x∘e = x`), given as a ground surface term (`:identity 0`,
    /// `:identity (zero)`). Parsed here, sort-checked and stored deferred at registration.
    Identity(Term),
    /// Cancellativity (`x∘z = y∘z ⟹ x = y`); an equation-level inference, no element.
    Cancellative,
    /// Group inverse: names the unary inverse op (`:inverse neg`). Requires `Identity`.
    Inverse(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    Sort(String),
    Function {
        name: String,
        arg_sorts: Vec<String>,
        ret_sort: String,
        tags: Vec<AlgTag>,
    },
    Datatype {
        name: String,
        variants: Vec<(String, Vec<String>, Vec<AlgTag>)>,
    },
    Rewrite {
        lhs: Pattern,
        rhs: RhsTerm,
        when: Vec<Pattern>,
        subsume: bool,
    },
    Rule {
        body: Vec<Pattern>,
        head: Vec<Action>,
    },
    Let(String, Term),
    Union(Term, Term),
    Insert(Term),
    Run(u64),
    Check(Term),
    CheckEq(Term, Term),
    CheckNeq(Term, Term),
    Extract(Term),
    AntiUnify {
        left: Term,
        right: Term,
        playouts: u64,
        algorithm: String,
    },
    CheckAu {
        left: Term,
        right: Term,
        max_size: u32,
        playouts: u64,
        algorithm: String,
    },
    Push(bool), // true = shrink on mark
    Pop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Action {
    Union(RhsTerm, RhsTerm),
    Insert(RhsTerm),
    Set {
        func: String,
        args: Vec<RhsTerm>,
        value: RhsTerm,
    },
}
