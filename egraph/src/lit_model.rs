// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Literal value model — defines the value representation, literal sorts,
//! and primitive operations available for computation in rules.
//!
//! Clients implement `LitModel` to plug their literal value type into the
//! e-graph, parser, and rewriting engine.

use std::fmt;

use crate::literal::LitVal;

/// Descriptor for a literal sort (e.g. "Int" backed by `IBig`).
pub struct LitSortDesc<V> {
    /// Name in surface syntax: "Int", "Bool", "Rational", etc.
    pub name: &'static str,
    /// Parse a surface-syntax token into a value of this sort.
    pub parse: fn(&str) -> Option<V>,
}

impl<V> Clone for LitSortDesc<V> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<V> Copy for LitSortDesc<V> {}

/// Descriptor for a primitive operation on literal values.
pub struct LitOpDesc<V> {
    /// Name in surface syntax: "+", "*", "not", "<", etc.
    pub name: &'static str,
    /// Argument literal sort names.
    pub arg_sorts: &'static [&'static str],
    /// Return literal sort name.
    pub ret_sort: &'static str,
    /// Evaluate the operation on concrete values.
    ///
    /// `None` means the operation is *partial* and these arguments are outside
    /// its domain: an integer division by zero, a checked-arithmetic overflow,
    /// an exponent too large for the primitive's exponent type. The engine
    /// turns that into an [`EvalError`] and stops the run; see there for why
    /// this is a `None` rather than a panic.
    ///
    /// It is not the channel for a sort mismatch. Argument sorts are settled by
    /// sortcheck against `arg_sorts` before a rule is installed, so an
    /// implementation may treat an unexpected variant as unreachable.
    pub eval: fn(&[&V]) -> Option<V>,
}

impl<V> Clone for LitOpDesc<V> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<V> Copy for LitOpDesc<V> {}

/// Where in a rule a partial operation was applied outside its domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvalSite {
    /// A primitive application in a right-hand side.
    Rhs,
    /// A predicate guard on a left-hand side.
    Guard,
    /// A multiplicity expression on a right-hand side.
    Multiplicity,
}

impl fmt::Display for EvalSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            EvalSite::Rhs => "the right-hand side",
            EvalSite::Guard => "a guard",
            EvalSite::Multiplicity => "a multiplicity expression",
        })
    }
}

/// A partial operation applied outside its domain while a rule ran.
///
/// This is a *program* error, not an engine invariant violation. The rule is
/// well sorted and the match is real; the arguments only became available when
/// the rule fired, and on these particular ones the operation has no value. So
/// there is nothing for the engine to repair and no term it could sensibly
/// build, and the honest response is to stop and say which operation on which
/// operands failed.
///
/// It is reported rather than panicked for the same reason: a panic aborts the
/// process and leaves the caller unable to tell a bad `.egg` program from a bug
/// in the engine. An [`EvalError`] travels out through `apply` and `saturate`
/// to the interpreter, which prints it and exits nonzero.
///
/// Sort mismatches are deliberately *not* represented here — see
/// [`LitOpDesc::eval`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalError {
    /// Surface name of the operation, e.g. `"i64::/"` or `"u64::-"`.
    pub op: &'static str,
    /// The operands it was applied to, already formatted: the error outlives
    /// the borrowed values, and the value type is only `Display` here.
    pub args: Vec<String>,
    /// Which part of the rule was under evaluation.
    pub site: EvalSite,
    /// The rule's name, filled in at the boundary that knows it. The
    /// evaluators see only the operation, so they leave this `None`.
    pub rule: Option<String>,
    /// Source span of the rule that was applying, filled in with the name. Byte offsets,
    /// because that is what the parser records and what this type can hold without borrowing
    /// the program text; [`render`](Self::render) turns them into a line and column.
    pub span: crate::ast::Span,
}

impl EvalError {
    /// Record a fault at `site`, formatting the operands for the diagnostic.
    pub fn new<V: fmt::Display>(op: &'static str, args: &[&V], site: EvalSite) -> Self {
        Self {
            op,
            args: args.iter().map(|a| a.to_string()).collect(),
            site,
            rule: None,
            span: crate::ast::Span::Dummy,
        }
    }

    /// Attribute the fault to a rule. Keeps an existing attribution, so the
    /// innermost frame that knows a name wins.
    pub fn in_rule(mut self, name: &str) -> Self {
        if self.rule.is_none() {
            self.rule = Some(name.to_owned());
        }
        self
    }

    /// Attach the applying rule's source span. Keeps an existing span, matching
    /// [`in_rule`](Self::in_rule): the innermost frame that knows a location wins.
    pub fn at(mut self, span: crate::ast::Span) -> Self {
        if matches!(self.span, crate::ast::Span::Dummy) {
            self.span = span;
        }
        self
    }

    /// The message with the rule's **line and column**, which `Display` cannot report because
    /// it does not have the program text. Falls back to `Display` when the span is unresolvable
    /// (a rule built through the API rather than parsed), so a caller can always use this.
    pub fn render(&self, src: &str) -> String {
        match self.span.render_in(src) {
            Some(at) => match &self.rule {
                Some(rule) => format!(
                    "rule '{rule}' at {at}: {} in {} is undefined on ({})",
                    self.op,
                    self.site,
                    self.args.join(", ")
                ),
                None => format!(
                    "at {at}: {} in {} is undefined on ({})",
                    self.op,
                    self.site,
                    self.args.join(", ")
                ),
            },
            None => self.to_string(),
        }
    }
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(rule) = &self.rule {
            write!(f, "rule '{rule}': ")?;
        }
        write!(
            f,
            "{} in {} is undefined on ({})",
            self.op,
            self.site,
            self.args.join(", ")
        )
    }
}

impl std::error::Error for EvalError {}

/// Client-defined literal value model.
///
/// Bundles the value representation, literal sorts, primitive operations,
/// and sort classification. The e-graph, parser, and execution engine are
/// parameterized over this trait.
pub trait LitModel: 'static {
    /// The concrete literal value type (typically an enum).
    type Value: LitVal;

    /// Available literal sorts.
    fn sorts(&self) -> &[LitSortDesc<Self::Value>];

    /// Available primitive operations on literal values.
    fn ops(&self) -> &[LitOpDesc<Self::Value>];

    /// Which literal sort does this value belong to?
    fn sort_of(val: &Self::Value) -> &'static str;

    /// Try to parse a token as a literal of a specific sort.
    fn parse_as(&self, sort_name: &str, token: &str) -> Option<Self::Value> {
        self.sorts()
            .iter()
            .find(|s| s.name == sort_name)
            .and_then(|s| (s.parse)(token))
    }

    /// Try to parse a token as a literal of any sort.
    /// Returns `(sort_name, value)` on success.
    fn parse_any(&self, token: &str) -> Option<(&'static str, Self::Value)> {
        for sort in self.sorts() {
            if let Some(v) = (sort.parse)(token) {
                return Some((sort.name, v));
            }
        }
        None
    }

    /// Look up a primitive op by name.
    fn find_op(&self, name: &str) -> Option<&LitOpDesc<Self::Value>> {
        self.ops().iter().find(|op| op.name == name)
    }

    /// Is this identifier a literal sort name?
    fn is_lit_sort(&self, name: &str) -> bool {
        self.sorts().iter().any(|s| s.name == name)
    }

    /// Is this literal value truthy? Used for comprehension filter guards.
    fn is_truthy(val: &Self::Value) -> bool;
}
