// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! AST types for the Semper surface language.
//!
//! All names are strings at this stage; resolution to OpId/SortId/VarId
//! happens in a later pass.

use crate::registry::OpMeta;

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
    #[doc = "Sequence rest variable (A nodes, `&[G]` slice into pool)."]
    pub struct SeqVarId;
    #[doc = "Set rest variable (ACI nodes, `&[G]` slice into pool)."]
    pub struct SetVarId;
    #[doc = "Multiset rest variable (AC nodes, &[(G,u32)] slice into pool)."]
    pub struct MsetVarId;
    #[doc = "Multiplicity variable (single u32 binding)."]
    pub struct MultVarId;
    #[doc = "RHS-local e-node variable introduced by a comprehension."]
    pub struct RhsLocalVarId;
    #[doc = "RHS-local multiplicity variable introduced by a comprehension."]
    pub struct RhsLocalMultVarId;
    #[doc = "Literal value variable (single LitValId binding from OpKind::Lit nodes)."]
    pub struct LitValVarId;
    #[doc = "Literal-valued sequence variable: a sequence pattern's literal column, one value per element (`doc/sequence-patterns.md`, Typing)."]
    pub struct LitSeqVarId;
    #[doc = "RHS-local literal value introduced by a comprehension over a literal column or a primitive's rows."]
    pub struct RhsLocalLitVarId;
}

/// Global variable (let-bound, resolved at match time from global bindings). A u32,
/// unlike the per-rule variable ids above: globals accumulate over a whole program, and a
/// benchmark can bind more than 65,536 of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GlobalVarId(pub u32);
impl GlobalVarId {
    pub const fn new(x: u32) -> Self {
        Self(x)
    }
    pub const fn idx(self) -> usize {
        self.0 as usize
    }
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

    /// 1-based `(line, column)` of this span's start in `src`, or `None` for
    /// [`Span::Dummy`] or an offset past the end of `src`.
    ///
    /// Byte offsets are what the parser records and what a `Display` on an error type can
    /// print without holding the source; a line and column are what a person reading a
    /// terminal can act on. Diagnostics therefore keep the offset and convert here, at the
    /// one place that has the source text: [`render_in`](Self::render_in), called from the
    /// binary's top-level error reporting.
    ///
    /// The column counts UTF-8 *characters*, not bytes, so a line with multi-byte text still
    /// reports a column a reader can count to. Cost is one scan of the prefix, which is
    /// irrelevant on a path that runs once, as the program is about to exit.
    pub fn line_col(&self, src: &str) -> Option<(usize, usize)> {
        let Span::Range { start, .. } = *self else {
            return None;
        };
        let start = start as usize;
        if start > src.len() {
            return None;
        }
        let prefix = &src[..start];
        let line = prefix.matches('\n').count() + 1;
        let col = prefix
            .rfind('\n')
            .map_or(prefix, |nl| &prefix[nl + 1..])
            .chars()
            .count()
            + 1;
        Some((line, col))
    }

    /// `"line L column C"` for a resolvable span, else `None`.
    ///
    /// Returning `Option` rather than an empty string keeps the caller in charge of how a
    /// missing location reads in its own message, instead of leaving a dangling " at ".
    pub fn render_in(&self, src: &str) -> Option<String> {
        self.line_col(src)
            .map(|(l, c)| format!("line {l} column {c}"))
    }
}

#[cfg(test)]
mod span_tests {
    use super::Span;

    #[test]
    fn line_col_is_one_based_on_the_first_line() {
        let src = "(sort E)\n(constructor a () E)\n";
        assert_eq!(Span::new(0, 4).line_col(src), Some((1, 1)));
        assert_eq!(Span::new(6, 7).line_col(src), Some((1, 7)));
    }

    #[test]
    fn line_col_counts_newlines_and_restarts_the_column() {
        let src = "(sort E)\n(constructor a () E)\n";
        // Offset 9 is the '(' that opens line 2.
        assert_eq!(Span::new(9, 20).line_col(src), Some((2, 1)));
        assert_eq!(Span::new(21, 22).line_col(src), Some((2, 13)));
    }

    #[test]
    fn column_counts_characters_not_bytes() {
        // 'é' is two bytes, so a byte-based column would report 4 rather than 3.
        let src = "aé b";
        assert_eq!(Span::new(3, 4).line_col(src), Some((1, 3)));
    }

    #[test]
    fn dummy_and_out_of_range_do_not_resolve() {
        let src = "(sort E)";
        assert_eq!(Span::Dummy.line_col(src), None);
        assert_eq!(Span::Dummy.render_in(src), None);
        assert_eq!(Span::new(999, 1000).line_col(src), None);
    }

    #[test]
    fn offset_at_end_of_source_resolves() {
        // A span pointing just past the last byte is the EOF position, not an error.
        let src = "(sort E)";
        assert_eq!(Span::new(8, 8).line_col(src), Some((1, 9)));
    }

    #[test]
    fn render_in_is_human_readable() {
        let src = "a\nbb\nccc";
        assert_eq!(
            Span::new(5, 6).render_in(src).as_deref(),
            Some("line 3 column 1")
        );
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
    /// `term:count` as a child of a variadic application: the child with its
    /// multiplicity, at least 1, of any size (the configuration narrows it when the term
    /// is built). An AC operator stores it as one counted child.
    Counted {
        term: Box<Term>,
        count: num_bigint::BigUint,
        span: Span,
    },
}

impl Term {
    pub fn span(&self) -> Span {
        match self {
            Term::Lit(_, s) => *s,
            Term::App { span, .. } | Term::Counted { span, .. } => *span,
        }
    }

    /// How many entries of the written term are `sub`, compared by text: a child written
    /// `x:k` is one occurrence. This is the count of e-class references in the term, the
    /// number of times the class is named. See [`Self::weighted_occurrences`] for the
    /// count with multiplicities.
    pub fn occurrences(&self, sub: &Term) -> u64 {
        let want = sub.to_string();
        let mut n = 0u64;
        let mut stack: Vec<&Term> = vec![self];
        while let Some(t) = stack.pop() {
            let inner = match t {
                Term::Counted { term, .. } => term.as_ref(),
                _ => t,
            };
            if inner.to_string() == want {
                n = n.saturating_add(1);
            }
            if let Term::App { children, .. } = inner {
                stack.extend(children.iter());
            }
        }
        n
    }

    /// How many copies of `sub` the term denotes, compared by text: each occurrence
    /// weighted by the product of the multiplicities on its path from the root, so the
    /// child of `x:k` counts k times. This is the occurrence count of the term with every
    /// multiset written out, computed without writing it out. Saturates at `u128::MAX`.
    pub fn weighted_occurrences(&self, sub: &Term) -> u128 {
        let want = sub.to_string();
        let mut n = 0u128;
        let mut stack: Vec<(&Term, u128)> = vec![(self, 1)];
        while let Some((t, w)) = stack.pop() {
            let (inner, w) = match t {
                Term::Counted { term, count, .. } => {
                    let k = u128::try_from(count).unwrap_or(u128::MAX);
                    (term.as_ref(), w.saturating_mul(k))
                }
                _ => (t, w),
            };
            if inner.to_string() == want {
                n = n.saturating_add(w);
            }
            if let Term::App { children, .. } = inner {
                stack.extend(children.iter().map(|c| (c, w)));
            }
        }
        n
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
            Term::Counted { term, count, .. } => write!(f, "{term}:{count}"),
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
    /// `term:mult` under a variadic op — the term contributed `mult` times.
    /// Multiplicity 0 omits the term (the k−1 = 0 case of a multiplicity variant).
    TermMult {
        term: RhsTerm,
        mult: MultExpr,
        span: Span,
    },
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
    /// A comprehension of a sequence rule whose binder is a tuple or whose source is
    /// an expression: `..{ body[:mult] for (q a b) in (union-by p l u) }`, or
    /// `..[ … ]` for an ordered result (`doc/sequence-patterns.md`, Typing and
    /// "Multiplicities and `zip`").
    RowComp {
        body: Box<RhsTerm>,
        mult: Option<MultExpr>,
        binders: Vec<(String, BinderMult)>,
        source: Box<RhsTerm>,
        filter: Option<Box<RhsTerm>>,
        ordered: bool,
        span: Span,
    },
}

/// A tuple binder's multiplicity: `x` (none), `x:k` (bound), `x:_` (dropped).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinderMult {
    None,
    Var(String),
    Drop,
}

/// Multiplicity expression in RHS multiset comprehension.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultExpr {
    Lit(u64),
    Var(String),
    /// `(u64::- k 1)` — checked u64 arithmetic over multiplicity variables
    /// and literals. The op vocabulary mirrors the u64 primitive ops; the
    /// resolver interval-checks the expression against the LHS multiplicity
    /// constraints so an underflow or division by zero is a compile error,
    /// not a runtime one.
    Prim {
        op: String,
        args: Vec<MultExpr>,
    },
}

// ---------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------

/// A single composable algebraic-property tag on a function declaration. Tags combine freely
/// at the surface (`:assoc :comm :idempotent`); the sortcheck resolver maps a tag *set* to a
/// concrete `OpKind` and validates the combination (see `doc/design/05-algebraic-operators.md` §5.3
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

/// The `:until` goal of a `(run …)`: two ground terms and the relation that has to hold
/// between their classes for the run to stop. `equal` distinguishes `(= a b)` from `(!= a b)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunGoal {
    pub left: Term,
    pub right: Term,
    pub equal: bool,
}

/// One `(datatype …)` variant: a constructor declaration whose return sort is the datatype.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub tags: Vec<AlgTag>,
    /// Always has `is_constructor: true` — a datatype variant is a constructor by
    /// construction — plus whatever `:cost` / `:unextractable` the variant declared.
    pub meta: OpMeta,
}

/// Where a cost model comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CostSource {
    /// A Roto script, by path.
    Script(String),
    /// A cost registered in Rust, by name.
    Rust(String),
    /// Criteria in ASP, by path: appended to the ASP dump of the e-graph.
    Asp(String),
    /// Criteria in MiniZinc, by path: appended to the MiniZinc dump of the e-graph.
    MiniZinc(String),
}

/// Which solver an `(extract … :cost …)` uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverSpec {
    /// The internal incremental CNF descent.
    Internal,
    /// The internal descent with the objective bounded by rustsat's dynamic
    /// polynomial watchdog instead of the totalizer.
    Dpw,
    /// RoundingSat, found as `$ROUNDINGSAT`, `~/.local/bin/roundingsat`, or on the
    /// `PATH`.
    RoundingSat,
    /// No solving: Semper's additive-greedy term, scored by the cost model.
    Greedy,
    /// A pseudo-Boolean competition solver: the program and its arguments; the OPB
    /// file's path is appended.
    Opb(Vec<String>),
    /// A MiniZinc solver by name (`cp-sat`, `chuffed`, ...), with further `minizinc`
    /// arguments.
    MiniZinc(Vec<String>),
    /// An answer-set solver with clingo's JSON output: the program and its
    /// arguments; the program's path is appended.
    Asp(Vec<String>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    Sort(String),
    /// `(function …)` and `(constructor …)`: the same declaration, distinguished only by
    /// `meta.is_constructor`. Both register an operator with identical congruence and
    /// matching behavior; a constructor additionally carries the extraction semantics
    /// (`FLAG_CONSTRUCTOR` on its nodes, `:cost`, `:unextractable`).
    Function {
        name: String,
        arg_sorts: Vec<String>,
        ret_sort: String,
        tags: Vec<AlgTag>,
        meta: OpMeta,
    },
    Datatype {
        name: String,
        variants: Vec<Variant>,
    },
    /// `(ruleset name)` — declares a ruleset. Rules tagged `:ruleset name` join it, and
    /// `(run name N)` runs exactly those rules.
    Ruleset(String),
    Let(String, Term),
    Union(Term, Term),
    Insert(Term),
    /// `(run [ruleset] N [:until (= a b) | :until (!= a b)])`.
    Run {
        /// The ruleset to run, or `None` for the default one (rules with no `:ruleset` tag).
        ruleset: Option<String>,
        /// Iteration budget.
        limit: u64,
        /// Goal that stops the run early once it holds.
        until: Option<RunGoal>,
    },
    /// `(print-size)` — per-operator node counts and the total — or `(print-size Op)`, the
    /// count for one operator.
    PrintSize(Option<String>),
    /// `(print-stats)` — the last run's counters on stdout — or `(print-stats :file "p.json")`,
    /// the same numbers as JSON in a file.
    PrintStats(Option<String>),
    Check(Term),
    CheckEq(Term, Term),
    CheckNeq(Term, Term),
    Extract(Term),
    /// `(cost-model NAME :script "file.roto")` or `(cost-model NAME :rust "id")`.
    CostModel {
        name: String,
        source: CostSource,
        span: Span,
    },
    /// `(extract t :cost NAME [:rung R] [:budget CLAUSES] [:solver internal |
    /// (opb "cmd" "arg"…)] [:file "term.json"])`: extraction under a named cost
    /// model. A rung whose estimated size exceeds the budget steps down the ladder.
    ExtractWith {
        term: Term,
        cost: String,
        rung: String,
        budget: Option<u64>,
        solver: SolverSpec,
        file: Option<String>,
        /// `:proof "dir"`: keep a VeriPB-checkable proof of the final solver call.
        proof: Option<String>,
        /// `:band lo hi [:count n]`: up to `n` (default 10) distinct terms whose cost
        /// lies in `[lo, hi]`, instead of the optimum.
        band: Option<(u64, u64, u64)>,
        span: Span,
    },
    /// `(dump-egraph t :file "p.json")` — write the whole e-graph, with `t`'s class
    /// marked as the root, as JSON for an external extractor to read.
    DumpEGraph {
        root: Term,
        file: String,
    },
    AntiUnify {
        left: Term,
        right: Term,
        playouts: u64,
        algorithm: String,
        cycle_mode: String,
    },
    CheckAu {
        left: Term,
        right: Term,
        max_size: u32,
        playouts: u64,
        algorithm: String,
        cycle_mode: String,
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
