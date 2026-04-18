// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Literal value interning.

use std::fmt;
use std::hash::Hash;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use crate::containers::DenseId;

/// Marker trait for literal value types.
pub trait LitVal: Clone + Eq + Hash + fmt::Debug + fmt::Display {}

/// Opaque token for [`LitValStore::mark`] / [`LitValStore::restore`].
#[derive(Clone, Copy, Debug)]
pub struct LitValStoreToken(crate::containers::MapToken);

/// Append-only intern table for literals, backed by `Map`.
#[derive(Debug)]
pub struct LitValStore<L: LitVal, V: DenseId, const TRACK: bool> {
    map: crate::containers::Map<L, (), TRACK>,
    _phantom: core::marker::PhantomData<V>,
}

impl<L: LitVal, V: DenseId, const TRACK: bool> Default for LitValStore<L, V, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: LitVal, V: DenseId, const TRACK: bool> LitValStore<L, V, TRACK> {
    pub fn new() -> Self {
        Self {
            map: crate::containers::Map::new(),
            _phantom: core::marker::PhantomData,
        }
    }

    pub fn intern(&mut self, value: L) -> V {
        if let Some(id) = self.map.id_of(&value) {
            return V::from_usize(id);
        }
        let id = self.map.insert(value, ());
        V::from_usize(id)
    }

    pub fn get(&self, id: V) -> &L {
        self.map.key(id.to_usize())
    }

    /// Try to look up a value without interning it.
    pub fn try_lookup(&self, value: &L) -> Option<V> {
        self.map.id_of(value).map(V::from_usize)
    }

    pub fn len(&self) -> usize {
        self.map.log_len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn mark(&mut self, shrink: crate::containers::ShrinkPolicy) -> LitValStoreToken {
        LitValStoreToken(self.map.mark(shrink))
    }

    pub fn restore(&mut self, token: LitValStoreToken) {
        self.map.restore(token.0);
    }
}

/// Sort-dispatched literal parser.
pub struct LitValParser<L, S: DenseId = crate::id::SortId> {
    parsers: Vec<(S, Box<dyn Fn(&str) -> Option<L>>)>,
}

impl<L, S: DenseId> Default for LitValParser<L, S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L, S: DenseId> LitValParser<L, S> {
    pub fn new() -> Self {
        Self {
            parsers: Vec::new(),
        }
    }

    pub fn register(&mut self, sort: S, f: impl Fn(&str) -> Option<L> + 'static) {
        self.parsers.push((sort, Box::new(f)));
    }

    pub fn parse(&self, s: &str, sort: S) -> Option<L> {
        self.parsers
            .iter()
            .find(|(sid, _)| *sid == sort)
            .and_then(|(_, f)| f(s))
    }
}

impl<L> fmt::Debug for LitValParser<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LitValParser")
            .field("num_parsers", &self.parsers.len())
            .finish()
    }
}

/// Literal values for QF_NIRA (quantifier-free nonlinear integer/real arithmetic).
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum NiraLitVal {
    Bool(bool),
    Int(BigInt),
    Rat(BigRational),
}

impl LitVal for NiraLitVal {}

impl fmt::Debug for NiraLitVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NiraLitVal::Bool(b) => write!(f, "{b}"),
            NiraLitVal::Int(n) => write!(f, "{n}"),
            NiraLitVal::Rat(r) => write!(f, "{r}"),
        }
    }
}

impl fmt::Display for NiraLitVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

// ---------------------------------------------------------------------------
// NiraModel — LitModel implementation for NiraLitVal
// ---------------------------------------------------------------------------

use crate::lit_model::{LitModel, LitOpDesc, LitSortDesc};

pub struct NiraModel;

const NIRA_SORTS: &[LitSortDesc<NiraLitVal>] = &[
    LitSortDesc {
        name: "IBig",
        parse: parse_int,
    },
    LitSortDesc {
        name: "RBig",
        parse: parse_rat,
    },
    LitSortDesc {
        name: "bool",
        parse: parse_bool,
    },
];

fn parse_int(s: &str) -> Option<NiraLitVal> {
    s.parse::<BigInt>().ok().map(NiraLitVal::Int)
}

fn parse_rat(s: &str) -> Option<NiraLitVal> {
    if let Some((n, d)) = s.split_once('/') {
        let num = n.parse::<BigInt>().ok()?;
        let den = d.parse::<BigInt>().ok()?;
        if den.is_zero() {
            return None;
        }
        Some(NiraLitVal::Rat(BigRational::new(num, den)))
    } else {
        None
    }
}

fn parse_bool(s: &str) -> Option<NiraLitVal> {
    match s {
        "true" => Some(NiraLitVal::Bool(true)),
        "false" => Some(NiraLitVal::Bool(false)),
        _ => None,
    }
}

macro_rules! nira_int_binop {
    ($name:expr, $op:tt) => {
        LitOpDesc { name: $name, arg_sorts: &["IBig", "IBig"], ret_sort: "IBig",
            eval: |args| match (args[0], args[1]) {
                (NiraLitVal::Int(a), NiraLitVal::Int(b)) => NiraLitVal::Int(a $op b),
                _ => panic!("type error"),
            },
        }
    };
}

macro_rules! nira_rat_binop {
    ($name:expr, $op:tt) => {
        LitOpDesc { name: $name, arg_sorts: &["RBig", "RBig"], ret_sort: "RBig",
            eval: |args| match (args[0], args[1]) {
                (NiraLitVal::Rat(a), NiraLitVal::Rat(b)) => NiraLitVal::Rat(a $op b),
                _ => panic!("type error"),
            },
        }
    };
}

const NIRA_OPS: &[LitOpDesc<NiraLitVal>] = &[
    nira_int_binop!("+", +),
    nira_int_binop!("-", -),
    nira_int_binop!("*", *),
    nira_rat_binop!("r+", +),
    nira_rat_binop!("r-", -),
    nira_rat_binop!("r*", *),
    nira_rat_binop!("r/", /),
    LitOpDesc {
        name: "<",
        arg_sorts: &["IBig", "IBig"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Int(a), NiraLitVal::Int(b)) => NiraLitVal::Bool(a < b),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "<=",
        arg_sorts: &["IBig", "IBig"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Int(a), NiraLitVal::Int(b)) => NiraLitVal::Bool(a <= b),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "!=",
        arg_sorts: &["IBig", "IBig"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Int(a), NiraLitVal::Int(b)) => NiraLitVal::Bool(a != b),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "and",
        arg_sorts: &["bool", "bool"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Bool(a), NiraLitVal::Bool(b)) => NiraLitVal::Bool(*a && *b),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "or",
        arg_sorts: &["bool", "bool"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Bool(a), NiraLitVal::Bool(b)) => NiraLitVal::Bool(*a || *b),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "not",
        arg_sorts: &["bool"],
        ret_sort: "bool",
        eval: |args| match args[0] {
            NiraLitVal::Bool(a) => NiraLitVal::Bool(!a),
            _ => panic!("type error"),
        },
    },
];

impl LitModel for NiraModel {
    type Value = NiraLitVal;
    fn sorts(&self) -> &[LitSortDesc<NiraLitVal>] {
        NIRA_SORTS
    }
    fn ops(&self) -> &[LitOpDesc<NiraLitVal>] {
        NIRA_OPS
    }
    fn sort_of(val: &NiraLitVal) -> &'static str {
        match val {
            NiraLitVal::Int(_) => "IBig",
            NiraLitVal::Rat(_) => "RBig",
            NiraLitVal::Bool(_) => "bool",
        }
    }
    fn is_truthy(val: &NiraLitVal) -> bool {
        matches!(val, NiraLitVal::Bool(true))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::SortId;
    use crate::nodes::LitValId;

    type LS = LitValStore<NiraLitVal, LitValId, false>;
    #[test]
    fn intern_dedup() {
        let mut store: LS = LitValStore::new();
        let a = store.intern(NiraLitVal::Int(BigInt::from(42)));
        let b = store.intern(NiraLitVal::Int(BigInt::from(42)));
        assert_eq!(a, b);
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn intern_distinct() {
        let mut store: LS = LitValStore::new();
        let a = store.intern(NiraLitVal::Int(BigInt::from(1)));
        let b = store.intern(NiraLitVal::Int(BigInt::from(2)));
        assert_ne!(a, b);
    }

    #[test]
    fn get_roundtrip() {
        let mut store: LS = LitValStore::new();
        let id = store.intern(NiraLitVal::Bool(false));
        assert_eq!(store.get(id), &NiraLitVal::Bool(false));
    }

    #[test]
    fn all_variants() {
        let mut store: LS = LitValStore::new();
        let b = store.intern(NiraLitVal::Bool(true));
        let i = store.intern(NiraLitVal::Int(BigInt::from(99)));
        let r = store.intern(NiraLitVal::Rat(BigRational::new(
            BigInt::from(314),
            BigInt::from(100),
        )));
        assert_ne!(b, i);
        assert_ne!(i, r);
        assert_eq!(store.len(), 3);
    }

    #[test]
    fn parser_dispatch() {
        let int = SortId::new(0);
        let bool_ = SortId::new(1);

        let mut lp = LitValParser::new();
        lp.register(int, |s| s.parse::<BigInt>().ok().map(NiraLitVal::Int));
        lp.register(bool_, |s| match s {
            "true" => Some(NiraLitVal::Bool(true)),
            "false" => Some(NiraLitVal::Bool(false)),
            _ => None,
        });

        assert_eq!(lp.parse("42", int), Some(NiraLitVal::Int(BigInt::from(42))));
        assert_eq!(lp.parse("true", bool_), Some(NiraLitVal::Bool(true)));
    }

    #[test]
    fn parser_unknown_sort() {
        let lp = LitValParser::<NiraLitVal>::new();
        assert_eq!(lp.parse("42", SortId::new(99)), None);
    }

    #[test]
    fn nira_model_parse_and_eval() {
        let m = NiraModel;
        // Parse
        let (sort, v) = m.parse_any("42").unwrap();
        assert_eq!(sort, "IBig");
        assert_eq!(v, NiraLitVal::Int(BigInt::from(42)));

        let (sort, v) = m.parse_any("true").unwrap();
        assert_eq!(sort, "bool");
        assert_eq!(v, NiraLitVal::Bool(true));

        let (sort, _v) = m.parse_any("3/4").unwrap();
        assert_eq!(sort, "RBig");

        assert!(m.parse_any("nonsense").is_none());

        // Eval
        let plus = m.find_op("+").unwrap();
        let a = NiraLitVal::Int(BigInt::from(3));
        let b = NiraLitVal::Int(BigInt::from(7));
        let result = (plus.eval)(&[&a, &b]);
        assert_eq!(result, NiraLitVal::Int(BigInt::from(10)));

        let lt = m.find_op("<").unwrap();
        let result = (lt.eval)(&[&a, &b]);
        assert_eq!(result, NiraLitVal::Bool(true));

        let not = m.find_op("not").unwrap();
        let t = NiraLitVal::Bool(true);
        assert_eq!((not.eval)(&[&t]), NiraLitVal::Bool(false));
    }

    #[test]
    fn nira_model_sort_of() {
        assert_eq!(
            NiraModel::sort_of(&NiraLitVal::Int(BigInt::from(0))),
            "IBig"
        );
        assert_eq!(NiraModel::sort_of(&NiraLitVal::Bool(false)), "bool");
    }
}
