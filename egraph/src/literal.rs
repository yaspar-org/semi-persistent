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
///
/// Carries the log length at the mark alongside the container's own token:
/// restore reads it to find the suffix of values interned since, which is
/// exactly the set of lookup entries it has to drop. The length is not a
/// second branch-history encoding: branch validity lives entirely in the
/// `VecToken`, which restore asserts valid before touching the index, and
/// the length only tells it which suffix values to read from the log while
/// they are still live (after the log restore they are gone).
#[derive(Clone, Copy, Debug)]
pub struct LitValStoreToken(crate::containers::VecToken, usize);

/// Append-only intern table for literals.
///
/// The log is the source of truth and a hash index accelerates lookup, which is
/// what [`crate::containers::SpMap`] provides, but that map rebuilds its index
/// from the surviving log on every restore, cloning every live key. Interning is
/// append-only (a value is pushed once, never overwritten and never mutated),
/// so restore instead deletes the entries for the log suffix it truncates, which
/// costs one hash removal per value interned since the mark rather than one key
/// clone per value in the table. `restore` keeps the rebuild as a fallback on the
/// same terms as the node caches: see `crate::caches::REBUILD_RATIO`.
pub struct LitValStore<L: LitVal, V: DenseId, const TRACK: bool> {
    /// Positions in this log ARE literal-value ids, so the log's index word is `V`'s.
    log: crate::containers::AppendOnlyVec<L, V::Index, TRACK>,
    index: hashbrown::HashMap<L, V::Index>,
}

impl<L: LitVal, V: DenseId, const TRACK: bool> Default for LitValStore<L, V, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: LitVal, V: DenseId, const TRACK: bool> fmt::Debug for LitValStore<L, V, TRACK> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LitValStore")
            .field("len", &self.len())
            .finish()
    }
}

impl<L: LitVal, V: DenseId, const TRACK: bool> LitValStore<L, V, TRACK> {
    pub fn new() -> Self {
        Self {
            log: crate::containers::AppendOnlyVec::new(),
            index: hashbrown::HashMap::new(),
        }
    }

    pub fn intern(&mut self, value: L) -> V {
        if let Some(&id) = self.index.get(&value) {
            return crate::id::id_at_index::<V>(id);
        }
        let id = self
            .log
            .try_push(value.clone())
            .expect("literal interner exhausted the id index word");
        self.index.insert(value, id);
        crate::id::id_at_index::<V>(id)
    }

    pub fn get(&self, id: V) -> &L {
        self.log.get(id.to_index())
    }

    /// Try to look up a value without interning it.
    pub fn try_lookup(&self, value: &L) -> Option<V> {
        self.index
            .get(value)
            .map(|&i| crate::id::id_at_index::<V>(i))
    }

    pub fn len(&self) -> usize {
        use crate::containers::IndexLike;
        self.log.len().as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.log.is_empty()
    }

    pub fn mark(&mut self, shrink: crate::containers::ShrinkPolicy) -> LitValStoreToken {
        LitValStoreToken(
            self.log
                .try_mark(shrink)
                .expect("literal mark: depth bounded by the saturation driver"),
            self.len(),
        )
    }

    pub fn restore(&mut self, token: LitValStoreToken) {
        use crate::containers::IndexLike;
        // Validate the log token BEFORE touching the index: the removals
        // below are not undoable, so an invalid token must refuse while the
        // store is still consistent (index and log in step).
        assert!(
            self.log.is_valid_token(&token.0),
            "literal restore: token is not restorable"
        );
        let saved_len = token.1;
        let live_len = self.len();
        let incremental = crate::caches::restore_incrementally(live_len - saved_len, 0, saved_len);

        if incremental {
            for i in saved_len..live_len {
                let idx = <V::Index as IndexLike>::try_from_usize(i)
                    .expect("log position: below a length the log already holds");
                self.index.remove(self.log.get(idx));
            }
        }

        self.log
            .try_restore(token.0)
            .expect("literal restore: token minted by this container's own mark");

        if !incremental {
            self.index.clear();
            for (i, value) in self.log.iter().enumerate() {
                let idx = <V::Index as IndexLike>::try_from_usize(i)
                    .expect("log position: below a length the log already holds");
                self.index.insert(value.clone(), idx);
            }
        }
        debug_assert_eq!(
            self.index.len(),
            self.len(),
            "restore left the literal index out of step with the log"
        );
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
                (NiraLitVal::Int(a), NiraLitVal::Int(b)) => Some(NiraLitVal::Int(a $op b)),
                _ => panic!("type error"),
            },
        }
    };
}

macro_rules! nira_rat_binop {
    ($name:expr, $op:tt) => {
        LitOpDesc { name: $name, arg_sorts: &["RBig", "RBig"], ret_sort: "RBig",
            eval: |args| match (args[0], args[1]) {
                (NiraLitVal::Rat(a), NiraLitVal::Rat(b)) => Some(NiraLitVal::Rat(a $op b)),
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
    // Not `nira_rat_binop!`: rational division is the one partial operation in
    // this model, and dividing by zero has no value rather than a value the
    // engine could build.
    LitOpDesc {
        name: "r/",
        arg_sorts: &["RBig", "RBig"],
        ret_sort: "RBig",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Rat(a), NiraLitVal::Rat(b)) => {
                if b.is_zero() {
                    return None;
                }
                Some(NiraLitVal::Rat(a / b))
            }
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "<",
        arg_sorts: &["IBig", "IBig"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Int(a), NiraLitVal::Int(b)) => Some(NiraLitVal::Bool(a < b)),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "<=",
        arg_sorts: &["IBig", "IBig"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Int(a), NiraLitVal::Int(b)) => Some(NiraLitVal::Bool(a <= b)),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "!=",
        arg_sorts: &["IBig", "IBig"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Int(a), NiraLitVal::Int(b)) => Some(NiraLitVal::Bool(a != b)),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "and",
        arg_sorts: &["bool", "bool"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Bool(a), NiraLitVal::Bool(b)) => Some(NiraLitVal::Bool(*a && *b)),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "or",
        arg_sorts: &["bool", "bool"],
        ret_sort: "bool",
        eval: |args| match (args[0], args[1]) {
            (NiraLitVal::Bool(a), NiraLitVal::Bool(b)) => Some(NiraLitVal::Bool(*a || *b)),
            _ => panic!("type error"),
        },
    },
    LitOpDesc {
        name: "not",
        arg_sorts: &["bool"],
        ret_sort: "bool",
        eval: |args| match args[0] {
            NiraLitVal::Bool(a) => Some(NiraLitVal::Bool(!a)),
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
        assert_eq!(result, Some(NiraLitVal::Int(BigInt::from(10))));

        let lt = m.find_op("<").unwrap();
        let result = (lt.eval)(&[&a, &b]);
        assert_eq!(result, Some(NiraLitVal::Bool(true)));

        let not = m.find_op("not").unwrap();
        let t = NiraLitVal::Bool(true);
        assert_eq!((not.eval)(&[&t]), Some(NiraLitVal::Bool(false)));
    }

    /// The one partial operation in this model: `r/` has no value at a zero
    /// divisor, and says so instead of panicking inside `BigRational`.
    #[test]
    fn nira_rational_division_by_zero_is_undefined() {
        let m = NiraModel;
        let div = m.find_op("r/").unwrap();
        let one = NiraLitVal::Rat(BigRational::from_integer(BigInt::from(1)));
        let zero = NiraLitVal::Rat(BigRational::from_integer(BigInt::from(0)));
        assert_eq!((div.eval)(&[&one, &zero]), None);
        assert_eq!(
            (div.eval)(&[&one, &one]),
            Some(NiraLitVal::Rat(BigRational::from_integer(BigInt::from(1))))
        );
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
