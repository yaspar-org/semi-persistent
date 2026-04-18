// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Literal value model — defines the value representation, literal sorts,
//! and primitive operations available for computation in rules.
//!
//! Clients implement `LitModel` to plug their literal value type into the
//! e-graph, parser, and rewriting engine.

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
    pub eval: fn(&[&V]) -> V,
}

impl<V> Clone for LitOpDesc<V> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<V> Copy for LitOpDesc<V> {}

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
