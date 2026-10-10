// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Cost functions written in Roto, for the extraction of [`crate::extraction`].
//!
//! A script defines `fn cost(g: Graph)`. It runs once, while the problem is built,
//! and never sees a solution. What it reads falls in two groups, with distinct
//! types:
//!
//! - facts of the e-graph (`Graph`, `Class`, `Node`, `Child`, `Use`, `Kind`), known
//!   before solving, with ordinary values (`String`, `u64`, `bool`, lists) that the
//!   script may branch on;
//! - solver values: a `Bool` is one literal (or a conjunction of literals), and
//!   `Exact`, `Over`, and `Under` are order-encoded integers, a finite set of values
//!   with one literal per threshold. A script combines them and charges under them;
//!   it cannot branch on them.
//!
//! The polarity rules are checked when the script is compiled: `Over.minus` accepts
//! only an `Under`, and nothing subtracts an `Over`. Solving, cycle breaking, and the
//! interpreted cost are the library's, exactly as for a cost written in Rust. See
//! `doc/extraction/api.md#part-4-the-roto-binding`.

use crate::extraction::graph::{Assoc, Graph as EGraph, Kind as EKind, Term};
use crate::extraction::oint::{
    Build, Detached, Exact as PExact, OInt, Over as POver, Under as PUnder,
};
use crate::extraction::pb::Pb as EPb;
use crate::extraction::rung::{Levels, Orders, Rung, Selection, Splits};
use crate::extraction::solve::{Outcome, Prepared, Solver, built, interpret, solve_prepared};
use crate::extraction::target::Cmp;
use crate::extraction::{Cost, CostWidth, Lit};
use roto::{List, NoCtx, RotoString, Runtime, TypedFunc, Val, library};
use std::sync::{Arc, Mutex};

pub use crate::extraction::rung::RungKind;

type ClassId = usize;
type NodeId = usize;

struct Ctx {
    graph: Arc<EGraph>,
    rung: Box<dyn Rung>,
    prepared: Prepared,
    rec: Detached,
    /// Operations the build refused, in order: the extraction fails with them.
    errors: Vec<String>,
}

impl Ctx {
    /// Run `f` with a builder over the context's target and recorded state.
    fn build<T>(&mut self, f: impl FnOnce(&mut Build, &dyn Rung) -> T) -> T {
        let rec = std::mem::take(&mut self.rec);
        let mut b = Build::from_parts(self.prepared.target(), rec);
        let out = f(&mut b, &*self.rung);
        self.rec = b.detach();
        out
    }
}

/// The shared build state every script value refers to.
#[derive(Clone)]
struct Ex(Arc<Mutex<Ctx>>);

impl PartialEq for Ex {
    fn eq(&self, o: &Self) -> bool {
        Arc::ptr_eq(&self.0, &o.0)
    }
}

impl Ex {
    fn with<T>(&self, f: impl FnOnce(&mut Ctx) -> T) -> T {
        f(&mut self.0.lock().unwrap())
    }
    fn build<T>(&self, f: impl FnOnce(&mut Build, &dyn Rung) -> T) -> T {
        self.with(|c| c.build(f))
    }
    fn graph(&self) -> Arc<EGraph> {
        self.with(|c| c.graph.clone())
    }
}

// --- the e-graph ---------------------------------------------------------------

/// The e-graph and the build: the argument of `cost`.
#[derive(Clone, PartialEq)]
pub struct Graph(Ex);
/// An e-class reachable from the root.
#[derive(Clone, PartialEq)]
pub struct Class(Ex, ClassId);
/// An e-node that is a candidate of a reachable class.
#[derive(Clone, PartialEq)]
pub struct Node(Ex, NodeId);
/// A child of a node: for a multiset or set node, one distinct operand with its
/// multiplicity; otherwise one position.
#[derive(Clone, PartialEq)]
pub struct Child {
    ex: Ex,
    node: NodeId,
    class: ClassId,
    index: usize,
    multiplicity: u64,
}
/// A node that has a class as a child, seen from that class.
#[derive(Clone, PartialEq)]
pub struct Use(Ex, NodeId, ClassId);
/// Another operand of a parent, under the literals that make it a sibling.
#[derive(Clone, PartialEq)]
pub struct Sibling(Bool, ClassId);
/// An operand under an internal node, under the literals that put it there.
#[derive(Clone, PartialEq)]
pub struct Member(Bool, ClassId);
/// An internal node that the rendering of a flat node may contain.
#[derive(Clone, PartialEq)]
pub struct Inner(Ex, NodeId, usize);
/// The algebraic kind of a node's operator.
#[derive(Clone, Copy, PartialEq)]
pub struct Kind(EKind);

// --- solver values ---------------------------------------------------------------

/// A condition on the solution: the conjunction of its literals, true when empty.
/// `and` concatenates; any other combination defines a new literal. Exact: each
/// literal is true exactly when what it stands for holds.
#[derive(Clone, PartialEq)]
pub struct Bool(Ex, Vec<Lit>);
/// A condition that may be true when what it stands for does not hold: a threshold
/// of an over-estimate. It may be charged under, not required.
#[derive(Clone, PartialEq)]
pub struct BoolOver(Ex, Vec<Lit>);
/// A condition that may be false when what it stands for holds: a threshold of an
/// under-estimate. It may be required, not charged under.
#[derive(Clone, PartialEq)]
pub struct BoolUnder(Ex, Vec<Lit>);

/// The conjunction of `lits` as one literal, defined by clauses when there are two
/// or more.
fn conj(ex: &Ex, lits: &[Lit]) -> Lit {
    match lits {
        [] => Lit::True,
        [l] => *l,
        [first, rest @ ..] => ex.build(|b, _| rest.iter().fold(*first, |acc, &l| b.and(acc, l))),
    }
}

impl Bool {
    /// The conjunction as one literal, defined by clauses when it has two or more.
    fn lit(&self) -> Lit {
        conj(&self.0, &self.1)
    }
}

macro_rules! int_type {
    ($name:ident, $p:ty, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone)]
        pub struct $name(Ex, OInt<$p>);
        impl PartialEq for $name {
            fn eq(&self, o: &Self) -> bool {
                self.0 == o.0
                    && self.1.values() == o.1.values()
                    && self.1.thresholds().eq(o.1.thresholds())
            }
        }
    };
}
int_type!(
    Exact,
    PExact,
    "An order-encoded integer whose encoded value is its value."
);
int_type!(
    Over,
    POver,
    "An order-encoded integer whose encoded value is at least its value."
);
int_type!(
    Under,
    PUnder,
    "An order-encoded integer whose encoded value is at most its value."
);

macro_rules! pb_type {
    ($name:ident, $p:ty, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone)]
        pub struct $name(Ex, crate::extraction::pb::Pb<$p>);
        impl PartialEq for $name {
            fn eq(&self, _: &Self) -> bool {
                false
            }
        }
    };
}
pb_type!(
    Pb,
    PExact,
    "A pseudo-Boolean term whose encoded value is its value."
);
pb_type!(
    PbOver,
    POver,
    "A pseudo-Boolean term whose encoded value is at least its value."
);
pb_type!(
    PbUnder,
    PUnder,
    "A pseudo-Boolean term whose encoded value is at most its value."
);

impl Ex {
    fn fail(&self, e: String) {
        self.with(|c| c.errors.push(e));
    }
}

/// An over-estimate that counts under a condition, for a maximum or a minimum.
#[derive(Clone, PartialEq)]
pub struct OverPart(Bool, Over);
/// An under-estimate that counts under a condition.
#[derive(Clone, PartialEq)]
pub struct UnderPart(Bool, Under);

/// A value per node, 0 where unset: the offsets of a recursive attribute.
#[derive(Clone)]
pub struct NodeValues(Ex, Arc<Mutex<Vec<Cost>>>);
impl PartialEq for NodeValues {
    fn eq(&self, o: &Self) -> bool {
        Arc::ptr_eq(&self.1, &o.1)
    }
}

/// An exact signed integer, built from an `i64`, from a decimal string, or read from the
/// e-graph. A fact known before solving: a script may compute with it and branch on it.
/// Roto's own `+`, `-`, and `*` on `i64` wrap and its `/` by zero aborts; these do not.
#[derive(Clone)]
pub struct IBig(Ex, Cost);
/// An exact unsigned integer: a multiplicity, a weight, a factor. A result below zero is
/// a build error.
#[derive(Clone)]
pub struct UBig(Ex, Cost);
impl PartialEq for IBig {
    fn eq(&self, o: &Self) -> bool {
        self.1 == o.1
    }
}
impl PartialEq for UBig {
    fn eq(&self, o: &Self) -> bool {
        self.1 == o.1
    }
}

fn ibig(ex: &Ex, v: Cost) -> Val<IBig> {
    Val(IBig(ex.clone(), v))
}

/// `v` as a `UBig`, or 0 with an error naming `op` when it is negative.
fn ubig(ex: &Ex, op: &str, v: Cost) -> Val<UBig> {
    if v.is_negative() {
        ex.fail(format!("{op}: the result {v} is negative, outside UBig"));
        return Val(UBig(ex.clone(), Cost::ZERO));
    }
    Val(UBig(ex.clone(), v))
}

/// `a / b` or `a % b`, or 0 with an error when `b` is 0.
fn divide(ex: &Ex, op: &str, r: Option<Cost>) -> Cost {
    r.unwrap_or_else(|| {
        ex.fail(format!("{op}: division by zero"));
        Cost::ZERO
    })
}

/// A decimal integer, or 0 with an error.
fn parse_big(ex: &Ex, op: &str, s: &RotoString) -> Cost {
    let t = s.to_string();
    Cost::parse(t.trim()).unwrap_or_else(|| {
        ex.fail(format!("{op}: '{t}' is not a decimal integer"));
        Cost::ZERO
    })
}

/// A recursive attribute: an over-estimated integer per reachable class.
#[derive(Clone)]
pub struct AttrOver(Ex, Arc<Vec<Option<OInt<POver>>>>);
/// A recursive attribute: an under-estimated integer per reachable class.
#[derive(Clone)]
pub struct AttrUnder(Ex, Arc<Vec<Option<OInt<PUnder>>>>);
impl PartialEq for AttrOver {
    fn eq(&self, o: &Self) -> bool {
        Arc::ptr_eq(&self.1, &o.1)
    }
}
impl PartialEq for AttrUnder {
    fn eq(&self, o: &Self) -> bool {
        Arc::ptr_eq(&self.1, &o.1)
    }
}

fn list<T: roto::Value + Clone>(v: Vec<T>) -> List<T>
where
    T::Transformed: PartialEq,
{
    List::from(v)
}

fn to_vec<T: roto::Value + Clone>(l: &List<T>) -> Vec<T>
where
    T::Transformed: PartialEq,
{
    (0..l.len()).filter_map(|i| l.get(i)).collect()
}

fn class_of(ex: &Ex, c: ClassId) -> Val<Class> {
    Val(Class(ex.clone(), c))
}

impl Child {
    fn of(ex: &Ex, g: &EGraph, n: NodeId) -> Vec<Val<Child>> {
        let node = &g.nodes[n];
        if node.flat() {
            (0..g.operands(n).len())
                .map(|i| {
                    Val(Child {
                        ex: ex.clone(),
                        node: n,
                        class: g.operands(n)[i],
                        index: i,
                        multiplicity: g.multiplicity(n, i),
                    })
                })
                .collect()
        } else {
            node.children
                .iter()
                .enumerate()
                .map(|(i, &c)| {
                    Val(Child {
                        ex: ex.clone(),
                        node: n,
                        class: c,
                        index: i,
                        multiplicity: 1,
                    })
                })
                .collect()
        }
    }
}

fn over_parts(p: &List<Val<OverPart>>) -> Vec<(Vec<Lit>, OInt<POver>)> {
    to_vec(p)
        .into_iter()
        .map(|Val(OverPart(b, x))| (b.1, x.1))
        .collect()
}

fn under_parts(p: &List<Val<UnderPart>>) -> Vec<(Vec<Lit>, OInt<PUnder>)> {
    to_vec(p)
        .into_iter()
        .map(|Val(UnderPart(b, x))| (b.1, x.1))
        .collect()
}

fn cardinality(ex: &Ex, bs: &List<Val<Bool>>, cmp: Cmp, k: Cost) {
    let lits: Vec<Lit> = to_vec(bs).iter().map(|b| b.0.lit()).collect();
    let terms: Vec<(i64, Lit)> = lits.into_iter().map(|l| (1, l)).collect();
    ex.build(|b, _| b.pb(&terms, cmp, k));
}

/// An integer's values as Roto's `i64`: one outside it (under `--cost-bits big`) is an
/// error, and the list then stops before it.
fn values_i64(ex: &Ex, values: &[Cost]) -> List<i64> {
    let mut out = Vec::with_capacity(values.len());
    for &v in values {
        match v.to_i64() {
            Some(x) => out.push(x),
            None => {
                ex.fail(format!("values: the value {v} is outside a script's i64"));
                break;
            }
        }
    }
    list(out)
}

fn lib() -> roto::Library {
    library! {
        #[clone] type Graph = Val<Graph>;
        #[clone] type Class = Val<Class>;
        #[clone] type Node = Val<Node>;
        #[clone] type Child = Val<Child>;
        #[clone] type Use = Val<Use>;
        #[clone] type Sibling = Val<Sibling>;
        #[clone] type Member = Val<Member>;
        #[clone] type Inner = Val<Inner>;
        #[copy] type Kind = Val<Kind>;
        #[clone] type Bool = Val<Bool>;
        #[clone] type BoolOver = Val<BoolOver>;
        #[clone] type BoolUnder = Val<BoolUnder>;
        #[clone] type Exact = Val<Exact>;
        #[clone] type Pb = Val<Pb>;
        #[clone] type PbOver = Val<PbOver>;
        #[clone] type PbUnder = Val<PbUnder>;
        #[clone] type Over = Val<Over>;
        #[clone] type Under = Val<Under>;
        #[clone] type OverPart = Val<OverPart>;
        #[clone] type UnderPart = Val<UnderPart>;
        #[clone] type NodeValues = Val<NodeValues>;
        #[clone] type AttrOver = Val<AttrOver>;
        #[clone] type AttrUnder = Val<AttrUnder>;
        #[clone] type IBig = Val<IBig>;
        #[clone] type UBig = Val<UBig>;

        impl Val<Graph> {
            /// The classes reachable from the root, ascending.
            fn classes(g: Val<Graph>) -> List<Val<Class>> {
                let ex = g.0 .0.clone();
                let cs = ex.with(|c| c.rung.selection().reachable.clone());
                list(cs.into_iter().map(|c| class_of(&ex, c)).collect())
            }
            /// The root class.
            fn root(g: Val<Graph>) -> Val<Class> {
                let ex = g.0 .0.clone();
                let r = ex.graph().root;
                class_of(&ex, r)
            }
            /// Every candidate of every reachable class.
            fn nodes(g: Val<Graph>) -> List<Val<Node>> {
                let ex = g.0 .0.clone();
                let ns = ex.with(|c| c.rung.selection().reachable.iter().flat_map(|&k| c.graph.candidates(k).collect::<Vec<_>>()).collect::<Vec<_>>());
                list(ns.into_iter().map(|n| Val(Node(ex.clone(), n))).collect())
            }
            /// The rung the problem is built on: `selection`, `levels`, `splits`, `binary`, or `orders`.
            fn rung(g: Val<Graph>) -> RotoString { g.0 .0.with(|c| RotoString::from(c.rung.name())) }

            /// A condition that always (`true`) or never (`false`) holds.
            fn bool(g: Val<Graph>, v: bool) -> Val<Bool> { Val(Bool(g.0 .0.clone(), vec![if v { Lit::True } else { Lit::False }])) }
            /// All of `bs`: true when empty.
            fn all(g: Val<Graph>, bs: List<Val<Bool>>) -> Val<Bool> {
                Val(Bool(g.0 .0.clone(), to_vec(&bs).into_iter().flat_map(|b| b.0 .1).collect()))
            }
            /// Any of `bs`: false when empty.
            fn any(g: Val<Graph>, bs: List<Val<Bool>>) -> Val<Bool> {
                let ex = g.0 .0.clone();
                let lits: Vec<Lit> = to_vec(&bs).iter().map(|b| b.0.lit()).collect();
                let l = ex.build(|b, _| lits.iter().fold(Lit::False, |acc, &l| if acc == Lit::False { l } else { b.or(acc, l) }));
                Val(Bool(ex, vec![l]))
            }

            /// The integer `v`.
            fn constant(g: Val<Graph>, v: i64) -> Val<Exact> { let ex = g.0 .0.clone(); let o = ex.build(|b, _| b.constant(v)); Val(Exact(ex, o)) }
            /// The largest part that holds, 0 when none does.
            fn max_over(g: Val<Graph>, parts: List<Val<OverPart>>) -> Val<Over> {
                let ex = g.0 .0.clone(); let p = over_parts(&parts); let v = ex.build(|b, _| b.max_of(&p)); Val(Over(ex, v))
            }
            /// The smallest part that holds, 0 when none does.
            fn min_under(g: Val<Graph>, parts: List<Val<UnderPart>>) -> Val<Under> {
                let ex = g.0 .0.clone(); let p = under_parts(&parts); let v = ex.build(|b, _| b.min_of(&p)); Val(Under(ex, v))
            }
            /// The largest part that holds, as an under-estimate.
            fn max_under(g: Val<Graph>, parts: List<Val<UnderPart>>) -> Val<Under> {
                let ex = g.0 .0.clone(); let p = under_parts(&parts); let v = ex.build(|b, _| b.max_of_down(&p)); Val(Under(ex, v))
            }
            /// The smallest part that holds, as an over-estimate.
            fn min_over(g: Val<Graph>, parts: List<Val<OverPart>>) -> Val<Over> {
                let ex = g.0 .0.clone(); let p = over_parts(&parts); let v = ex.build(|b, _| b.min_of_up(&p)); Val(Over(ex, v))
            }
            /// The sum of `xs`.
            fn sum(g: Val<Graph>, xs: List<Val<Over>>) -> Val<Over> {
                let ex = g.0 .0.clone(); let v: Vec<OInt<POver>> = to_vec(&xs).into_iter().map(|x| x.0 .1).collect();
                let s = ex.build(|b, _| b.sum(&v)); Val(Over(ex, s))
            }
            /// `x` when `c` holds, `y` otherwise.
            fn ite(g: Val<Graph>, c: Val<Bool>, x: Val<Over>, y: Val<Over>) -> Val<Over> {
                let ex = g.0 .0.clone(); let l = c.0.lit(); let v = ex.build(|b, _| b.ite(l, &x.0 .1, &y.0 .1)); Val(Over(ex, v))
            }

            /// A value per node, all 0.
            fn node_values(g: Val<Graph>) -> Val<NodeValues> { let n = g.0 .0.graph().nodes.len(); Val(NodeValues(g.0 .0.clone(), Arc::new(Mutex::new(vec![Cost::ZERO; n])))) }
            /// Per class: the chosen node's offset plus the largest attribute among its
            /// operands (its offset alone for a leaf). Over-estimated.
            fn attribute_max(g: Val<Graph>, offsets: Val<NodeValues>) -> Val<AttrOver> {
                let ex = g.0 .0.clone(); let off = offsets.0 .1.lock().unwrap().clone();
                let v = ex.build(|b, r| b.rec_max_by_id(r, &|n| off[n])); Val(AttrOver(ex, Arc::new(v)))
            }
            /// `attribute_max`, under-estimated.
            fn attribute_max_under(g: Val<Graph>, offsets: Val<NodeValues>) -> Val<AttrUnder> {
                let ex = g.0 .0.clone(); let off = offsets.0 .1.lock().unwrap().clone();
                let v = ex.build(|b, r| b.rec_max_down_by_id(r, &|n| off[n])); Val(AttrUnder(ex, Arc::new(v)))
            }
            /// Per class: the chosen node's offset plus the smallest attribute among its
            /// operands. Under-estimated.
            fn attribute_min(g: Val<Graph>, offsets: Val<NodeValues>) -> Val<AttrUnder> {
                let ex = g.0 .0.clone(); let off = offsets.0 .1.lock().unwrap().clone();
                let v = ex.build(|b, r| b.rec_min_by_id(r, &|n| off[n])); Val(AttrUnder(ex, Arc::new(v)))
            }
            /// `attribute_min`, over-estimated.
            fn attribute_min_over(g: Val<Graph>, offsets: Val<NodeValues>) -> Val<AttrOver> {
                let ex = g.0 .0.clone(); let off = offsets.0 .1.lock().unwrap().clone();
                let v = ex.build(|b, r| b.rec_min_up_by_id(r, &|n| off[n])); Val(AttrOver(ex, Arc::new(v)))
            }

            /// At most `k` of `bs` hold.
            fn at_most(g: Val<Graph>, bs: List<Val<Bool>>, k: u64) { cardinality(&g.0 .0, &bs, Cmp::Le, Cost::from(k)) }
            /// At least `k` of `bs` hold.
            fn at_least(g: Val<Graph>, bs: List<Val<Bool>>, k: u64) { cardinality(&g.0 .0, &bs, Cmp::Ge, Cost::from(k)) }
            /// `at_most` with an exact count.
            fn at_most_big(g: Val<Graph>, bs: List<Val<Bool>>, k: Val<UBig>) { cardinality(&g.0 .0, &bs, Cmp::Le, k.0 .1) }
            /// `at_least` with an exact count.
            fn at_least_big(g: Val<Graph>, bs: List<Val<Bool>>, k: Val<UBig>) { cardinality(&g.0 .0, &bs, Cmp::Ge, k.0 .1) }

            /// The exact integer `v`.
            fn ibig(g: Val<Graph>, v: i64) -> Val<IBig> { ibig(&g.0 .0, Cost::from(v)) }
            /// The exact integer written in `s`, in decimal, with an optional sign: how a
            /// script states a constant past `i64`. A malformed string is an error.
            fn ibig_str(g: Val<Graph>, s: RotoString) -> Val<IBig> { let ex = g.0 .0.clone(); let v = parse_big(&ex, "ibig_str", &s); ibig(&ex, v) }
            /// The exact unsigned integer `v`.
            fn ubig(g: Val<Graph>, v: u64) -> Val<UBig> { ubig(&g.0 .0, "ubig", Cost::from(v)) }
            /// The exact unsigned integer written in `s`; a negative or malformed string is an error.
            fn ubig_str(g: Val<Graph>, s: RotoString) -> Val<UBig> { let ex = g.0 .0.clone(); let v = parse_big(&ex, "ubig_str", &s); ubig(&ex, "ubig_str", v) }
            /// The exact constant `v`.
            fn constant_big(g: Val<Graph>, v: Val<IBig>) -> Val<Exact> { let ex = g.0 .0.clone(); let o = ex.build(|b, _| b.constant(v.0 .1)); Val(Exact(ex, o)) }
            /// A free integer over exact breakpoints.
            fn int_big(g: Val<Graph>, breakpoints: List<Val<IBig>>) -> Val<Exact> {
                let ex = g.0 .0.clone(); let v: Vec<Cost> = to_vec(&breakpoints).into_iter().map(|b| b.0 .1).collect();
                let x = ex.build(|b, _| b.int(&v)); Val(Exact(ex, x))
            }
            /// The exact constant term `c`.
            fn pb_const_big(g: Val<Graph>, c: Val<IBig>) -> Val<Pb> { Val(Pb(g.0 .0.clone(), EPb::constant(c.0 .1))) }
            /// Add the exact `w` to the cost.
            fn charge_const_big(g: Val<Graph>, w: Val<IBig>) { g.0 .0.build(|b, _| b.cost_base(w.0 .1)) }

            /// A free integer over `breakpoints`, chosen by the solver.
            fn int(g: Val<Graph>, breakpoints: List<i64>) -> Val<Exact> {
                let ex = g.0 .0.clone(); let v = to_vec(&breakpoints);
                let x = ex.build(|b, _| b.int(&v)); Val(Exact(ex, x))
            }
            /// A free integer over `scale · breakpoints`.
            fn int_scaled(g: Val<Graph>, breakpoints: List<i64>, scale: u64) -> Val<Exact> {
                let ex = g.0 .0.clone(); let v: Vec<Cost> = to_vec(&breakpoints).into_iter().map(|b| Cost::from(b) * Cost::from(scale)).collect();
                let x = ex.build(|b, _| b.int(&v)); Val(Exact(ex, x))
            }
            /// The number of `bs` that hold.
            fn count(g: Val<Graph>, bs: List<Val<Bool>>) -> Val<Pb> {
                let ex = g.0 .0.clone();
                let t = to_vec(&bs).iter().fold(EPb::constant(0), |t, b| t.plus(&EPb::lit(b.0.lit(), 1)));
                Val(Pb(ex, t))
            }
            /// The constant term `c`.
            fn pb_const(g: Val<Graph>, c: i64) -> Val<Pb> { Val(Pb(g.0 .0.clone(), EPb::constant(c))) }
            /// A free integer over `0, 1, ..., n`.
            fn unary(g: Val<Graph>, n: u64) -> Val<Exact> {
                let ex = g.0 .0.clone();
                // One literal per value: past `MAX_UNARY` they would not fit in memory.
                let n = if n > crate::extraction::oint::MAX_UNARY { ex.fail(format!("unary: {n} values exceed {}", crate::extraction::oint::MAX_UNARY)); 0 } else { n };
                let v: Vec<u64> = (0..=n).collect();
                let x = ex.build(|b, _| b.int(&v)); Val(Exact(ex, x))
            }
            /// Add `w` to the cost.
            fn charge_const(g: Val<Graph>, w: i64) { g.0 .0.build(|b, _| b.cost_base(w)) }

        }

        impl Val<Class> {
            /// The class's candidates: its members less the subsumed ones.
            fn nodes(c: Val<Class>) -> List<Val<Node>> {
                let ex = c.0 .0.clone(); let ns: Vec<NodeId> = ex.graph().candidates(c.0 .1).collect();
                list(ns.into_iter().map(|n| Val(Node(ex.clone(), n))).collect())
            }
            /// The nodes that have this class as a child, once each.
            fn parents(c: Val<Class>) -> List<Val<Use>> {
                let ex = c.0 .0.clone(); let ps = ex.with(|x| x.rung.selection().parents(c.0 .1).to_vec());
                list(ps.into_iter().map(|p| Val(Use(ex.clone(), p, c.0 .1))).collect())
            }
            /// The class is in the term.
            fn chosen(c: Val<Class>) -> Val<Bool> { let ex = c.0 .0.clone(); let l = ex.with(|x| x.rung.selection().class(c.0 .1)); Val(Bool(ex, vec![l])) }
            fn id(c: Val<Class>) -> u64 { c.0 .1 as u64 }
            fn is_root(c: Val<Class>) -> bool { c.0 .0.graph().root == c.0 .1 }
        }

        impl Val<Node> {
            fn op(n: Val<Node>) -> RotoString { RotoString::from(n.0 .0.graph().nodes[n.0 .1].op.as_str()) }
            /// The operator is `op`.
            fn is(n: Val<Node>, op: RotoString) -> bool { n.0 .0.graph().nodes[n.0 .1].op == op.to_string() }
            fn kind(n: Val<Node>) -> Val<Kind> { Val(Kind(n.0 .0.graph().nodes[n.0 .1].kind)) }
            /// Positional children; for a multiset or set node, its distinct operands.
            fn children(n: Val<Node>) -> List<Val<Child>> { let ex = n.0 .0.clone(); let g = ex.graph(); list(Child::of(&ex, &g, n.0 .1)) }
            fn class(n: Val<Node>) -> Val<Class> { class_of(&n.0 .0, n.0 .0.graph().nodes[n.0 .1].class) }
            /// The integer payload, in order: the bounds of an interval, for example.
            /// A value past `i64` is an error; `nums` reads it exactly.
            fn ints(n: Val<Node>) -> List<i64> { let ex = n.0 .0.clone(); let v = ex.graph().nodes[n.0 .1].ints.clone(); values_i64(&ex, &v) }
            /// Integer `j` of the payload, or `None` past the end. A value past `i64` is an
            /// error, and `None`; `num` reads it exactly.
            fn int(n: Val<Node>, j: u64) -> Option<i64> {
                let ex = n.0 .0.clone(); let v = ex.graph().nodes[n.0 .1].ints.get(j as usize).copied()?;
                v.to_i64().or_else(|| { ex.fail(format!("int: the payload integer {v} is outside a script's i64; read it with num")); None })
            }
            /// Integer `j` of the payload, clamped below at 0, or `None` past the end. A value
            /// past `u64` is an error, and `None`.
            fn nat(n: Val<Node>, j: u64) -> Option<u64> {
                let ex = n.0 .0.clone(); let v = ex.graph().nodes[n.0 .1].ints.get(j as usize).copied()?.max(Cost::ZERO);
                v.to_u64().or_else(|| { ex.fail(format!("nat: the payload integer {v} is outside a script's u64; read it with num")); None })
            }
            /// The integer payload, exact: an `IBig` literal past `i64` included.
            fn nums(n: Val<Node>) -> List<Val<IBig>> { let ex = n.0 .0.clone(); let v = ex.graph().nodes[n.0 .1].ints.clone(); list(v.into_iter().map(|x| ibig(&ex, x)).collect()) }
            /// Integer `j` of the payload, exact, or `None` past the end.
            fn num(n: Val<Node>, j: u64) -> Option<Val<IBig>> { let ex = n.0 .0.clone(); let v = ex.graph().nodes[n.0 .1].ints.get(j as usize).copied()?; Some(ibig(&ex, v)) }
            /// The string payload, in order: the name of an atom, for example.
            fn strings(n: Val<Node>) -> List<RotoString> { list(n.0 .0.graph().nodes[n.0 .1].strings.iter().map(|s| RotoString::from(s.as_str())).collect()) }
            fn id(n: Val<Node>) -> u64 { n.0 .1 as u64 }
            /// The node's class is in the term and takes this node.
            fn chosen(n: Val<Node>) -> Val<Bool> { let ex = n.0 .0.clone(); let l = ex.with(|x| x.rung.selection().node(n.0 .1)); Val(Bool(ex, vec![l])) }
            /// The internal nodes the rendering of this flat node may contain. Empty for
            /// a node that is not flat, and at the selection rung.
            fn inner_nodes(n: Val<Node>) -> List<Val<Inner>> {
                let ex = n.0 .0.clone(); let k = ex.with(|x| x.rung.inner_nodes(n.0 .1).len());
                list((0..k).map(|i| Val(Inner(ex.clone(), n.0 .1, i))).collect())
            }
        }

        impl Val<Child> {
            fn class(k: Val<Child>) -> Val<Class> { class_of(&k.0.ex, k.0.class) }
            /// How often the operand occurs: 1 except under a multiset.
            fn multiplicity(k: Val<Child>) -> u64 { k.0.multiplicity }
            /// The multiplicity, exact: to compute with without Roto's wrapping `u64`.
            fn count(k: Val<Child>) -> Val<UBig> { ubig(&k.0.ex, "count", Cost::from(k.0.multiplicity)) }
            /// The position among the node's children (among its distinct operands for a
            /// flat node).
            fn index(k: Val<Child>) -> u64 { k.0.index as u64 }
            /// The operand's depth in the flat node's tree, from 1, where the rung makes
            /// the tree a decision.
            fn depth(k: Val<Child>) -> Option<Val<Exact>> {
                let ex = k.0.ex.clone();
                let d = ex.build(|b, r| r.nesting().and_then(|t| t.depth(b, k.0.node, k.0.class)));
                d.map(|d| Val(Exact(ex, d)))
            }
            /// The operand's position within its block at depth `d`, at the orders rung, for
            /// `d` from 1 (the node itself) to the tree's depth; `None` for any other `d`.
            fn position(k: Val<Child>, d: u64) -> Option<Val<Exact>> {
                let ex = k.0.ex.clone();
                let p = ex.build(|b, r| r.ordering().and_then(|t| t.position(b, k.0.node, k.0.class, d as usize)));
                p.map(|p| Val(Exact(ex, p)))
            }
        }

        impl Val<Use> {
            fn parent(u: Val<Use>) -> Val<Node> { Val(Node(u.0 .0.clone(), u.0 .1)) }
            /// The positions at which the class occurs among the parent's children.
            fn positions(u: Val<Use>) -> List<u64> {
                let g = u.0 .0.graph();
                list(g.nodes[u.0 .1].children.iter().enumerate().filter(|&(_, &k)| k == u.0 .2).map(|(i, _)| i as u64).collect())
            }
            /// The parent's other operands, each under the literals that make it a
            /// sibling: the parent chosen and, where the rung renders a tree, in the
            /// same block.
            fn siblings(u: Val<Use>) -> List<Val<Sibling>> {
                let ex = u.0 .0.clone(); let s = ex.with(|x| x.rung.siblings(u.0 .1, u.0 .2));
                list(s.into_iter().map(|(gs, c)| Val(Sibling(Bool(ex.clone(), gs), c))).collect())
            }
        }

        impl Val<Sibling> {
            fn class(s: Val<Sibling>) -> Val<Class> { class_of(&s.0 .0 .0, s.0 .1) }
            fn present(s: Val<Sibling>) -> Val<Bool> { Val(s.0 .0.clone()) }
        }

        impl Val<Member> {
            fn class(m: Val<Member>) -> Val<Class> { class_of(&m.0 .0 .0, m.0 .1) }
            fn present(m: Val<Member>) -> Val<Bool> { Val(m.0 .0.clone()) }
        }

        impl Val<Inner> {
            /// The flat node is chosen and its tree contains this internal node.
            fn exists(t: Val<Inner>) -> Val<Bool> { let ex = t.0 .0.clone(); let l = ex.with(|x| x.rung.inner_nodes(t.0 .1)[t.0 .2].exists); Val(Bool(ex, vec![l])) }
            /// The operands that may lie under this node.
            fn members(t: Val<Inner>) -> List<Val<Member>> {
                let ex = t.0 .0.clone(); let m = ex.with(|x| x.rung.inner_nodes(t.0 .1)[t.0 .2].members.clone());
                list(m.into_iter().map(|(gs, c)| Val(Member(Bool(ex.clone(), gs), c))).collect())
            }
            /// The operands that may be its siblings.
            fn siblings(t: Val<Inner>) -> List<Val<Sibling>> {
                let ex = t.0 .0.clone(); let s = ex.with(|x| x.rung.inner_nodes(t.0 .1)[t.0 .2].siblings.clone());
                list(s.into_iter().map(|(gs, c)| Val(Sibling(Bool(ex.clone(), gs), c))).collect())
            }
            fn index(t: Val<Inner>) -> u64 { t.0 .2 as u64 }
            fn node(t: Val<Inner>) -> Val<Node> { Val(Node(t.0 .0.clone(), t.0 .1)) }
        }

        impl Val<Kind> {
            /// `plain`, `comm`, `seq`, `seq-left`, `seq-right`, `mset`, or `set`.
            fn name(k: Val<Kind>) -> RotoString {
                RotoString::from(match k.0 .0 {
                    EKind::Plain => "plain",
                    EKind::Comm => "comm",
                    EKind::Seq(Assoc::Both) => "seq",
                    EKind::Seq(Assoc::Left) => "seq-left",
                    EKind::Seq(Assoc::Right) => "seq-right",
                    EKind::MSet => "mset",
                    EKind::Set => "set",
                })
            }
            fn is_plain(k: Val<Kind>) -> bool { k.0 .0 == EKind::Plain }
            fn is_comm(k: Val<Kind>) -> bool { k.0 .0 == EKind::Comm }
            fn is_seq(k: Val<Kind>) -> bool { matches!(k.0 .0, EKind::Seq(_)) }
            fn is_mset(k: Val<Kind>) -> bool { k.0 .0 == EKind::MSet }
            fn is_set(k: Val<Kind>) -> bool { k.0 .0 == EKind::Set }
            /// A multiset or set node, whose tree the rung may choose.
            fn is_flat(k: Val<Kind>) -> bool { k.0 .0.flat() }
            /// A node whose bracketing the rung may choose: a multiset or set node, or
            /// an associative sequence (`:assoc`).
            fn is_bracketed(k: Val<Kind>) -> bool { k.0 .0.bracketed() }
        }

        impl Val<Bool> {
            /// Both hold. Adds no variable.
            fn and(a: Val<Bool>, b: Val<Bool>) -> Val<Bool> { let mut v = a.0 .1.clone(); v.extend(b.0 .1.iter().copied()); Val(Bool(a.0 .0.clone(), v)) }
            fn or(a: Val<Bool>, b: Val<Bool>) -> Val<Bool> { let (x, y) = (a.0.lit(), b.0.lit()); let ex = a.0 .0.clone(); let l = ex.build(|bb, _| bb.or(x, y)); Val(Bool(ex, vec![l])) }
            fn not(a: Val<Bool>) -> Val<Bool> { let l = a.0.lit(); Val(Bool(a.0 .0.clone(), vec![l.not()])) }
            fn implies(a: Val<Bool>, b: Val<Bool>) -> Val<Bool> { let (x, y) = (a.0.lit(), b.0.lit()); let ex = a.0 .0.clone(); let l = ex.build(|bb, _| bb.or(x.not(), y)); Val(Bool(ex, vec![l])) }
            /// The same condition, where one that may be spuriously true is expected.
            fn over(a: Val<Bool>) -> Val<BoolOver> { Val(BoolOver(a.0 .0.clone(), a.0 .1.clone())) }
            /// The same condition, where one that may be spuriously false is expected.
            fn under(a: Val<Bool>) -> Val<BoolUnder> { Val(BoolUnder(a.0 .0.clone(), a.0 .1.clone())) }
            /// `k` where the condition holds, 0 elsewhere.
            fn times(a: Val<Bool>, k: u64) -> Val<Pb> { let l = a.0.lit(); Val(Pb(a.0 .0.clone(), EPb::lit(l, k))) }
            /// The condition holds in every solution.
            fn require(a: Val<Bool>) { let ex = a.0 .0.clone(); let l = a.0.lit(); ex.build(|b, _| b.require(l)) }
            /// Add `w` to the cost where the condition holds.
            fn charge_if(a: Val<Bool>, w: u64) { let ex = a.0 .0.clone(); let l = a.0.lit(); ex.build(|b, _| b.cost_if(l, w)) }
            /// `times` with an exact factor.
            fn times_big(a: Val<Bool>, k: Val<UBig>) -> Val<Pb> { let l = a.0.lit(); Val(Pb(a.0 .0.clone(), EPb::lit(l, k.0 .1))) }
            /// `charge_if` with an exact weight.
            fn charge_if_big(a: Val<Bool>, w: Val<UBig>) { let ex = a.0 .0.clone(); let l = a.0.lit(); ex.build(|b, _| b.cost_if(l, w.0 .1)) }
        }

        impl Val<BoolOver> {
            fn and(a: Val<BoolOver>, b: Val<BoolOver>) -> Val<BoolOver> { let mut v = a.0 .1.clone(); v.extend(b.0 .1.iter().copied()); Val(BoolOver(a.0 .0.clone(), v)) }
            fn or(a: Val<BoolOver>, b: Val<BoolOver>) -> Val<BoolOver> { let ex = a.0 .0.clone(); let (x, y) = (conj(&ex, &a.0 .1), conj(&ex, &b.0 .1)); let l = ex.build(|bb, _| bb.or(x, y)); Val(BoolOver(ex, vec![l])) }
            /// The negation may be spuriously false: an under-estimated condition.
            fn not(a: Val<BoolOver>) -> Val<BoolUnder> { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); Val(BoolUnder(ex, vec![l.not()])) }
            fn times(a: Val<BoolOver>, k: u64) -> Val<PbOver> { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); Val(PbOver(ex, EPb::lit(l, k))) }
            /// Add `w` to the cost where the condition holds; a spurious truth only overcharges.
            fn charge_if(a: Val<BoolOver>, w: u64) { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); ex.build(|b, _| b.cost_if(l, w)) }
            fn times_big(a: Val<BoolOver>, k: Val<UBig>) -> Val<PbOver> { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); Val(PbOver(ex, EPb::lit(l, k.0 .1))) }
            fn charge_if_big(a: Val<BoolOver>, w: Val<UBig>) { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); ex.build(|b, _| b.cost_if(l, w.0 .1)) }
        }

        impl Val<BoolUnder> {
            fn and(a: Val<BoolUnder>, b: Val<BoolUnder>) -> Val<BoolUnder> { let mut v = a.0 .1.clone(); v.extend(b.0 .1.iter().copied()); Val(BoolUnder(a.0 .0.clone(), v)) }
            fn or(a: Val<BoolUnder>, b: Val<BoolUnder>) -> Val<BoolUnder> { let ex = a.0 .0.clone(); let (x, y) = (conj(&ex, &a.0 .1), conj(&ex, &b.0 .1)); let l = ex.build(|bb, _| bb.or(x, y)); Val(BoolUnder(ex, vec![l])) }
            /// The negation may be spuriously true: an over-estimated condition.
            fn not(a: Val<BoolUnder>) -> Val<BoolOver> { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); Val(BoolOver(ex, vec![l.not()])) }
            fn times(a: Val<BoolUnder>, k: u64) -> Val<PbUnder> { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); Val(PbUnder(ex, EPb::lit(l, k))) }
            fn times_big(a: Val<BoolUnder>, k: Val<UBig>) -> Val<PbUnder> { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); Val(PbUnder(ex, EPb::lit(l, k.0 .1))) }
            /// The condition holds in every solution; a spurious falsity only restricts the solver.
            fn require(a: Val<BoolUnder>) { let ex = a.0 .0.clone(); let l = conj(&ex, &a.0 .1); ex.build(|b, _| b.require(l)) }
        }

        impl Val<Exact> {
            fn over(x: Val<Exact>) -> Val<Over> { Val(Over(x.0 .0.clone(), x.0 .1.clone().over())) }
            fn under(x: Val<Exact>) -> Val<Under> { Val(Under(x.0 .0.clone(), x.0 .1.clone().under())) }
            /// The values the integer can take, ascending.
            fn values(x: Val<Exact>) -> List<i64> { values_i64(&x.0 .0, x.0 .1.values()) }
            /// The literal "at least `v`".
            fn at_least(x: Val<Exact>, v: i64) -> Val<Bool> { Val(Bool(x.0 .0.clone(), vec![x.0 .1.at_least(v)])) }
            /// The literal "at most `v`".
            fn at_most(x: Val<Exact>, v: i64) -> Val<Bool> { Val(Bool(x.0 .0.clone(), vec![x.0 .1.at_most(v)])) }
            fn plus_const(x: Val<Exact>, k: i64) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.shift(&x.0 .1, k)); Val(Exact(ex, v)) }
            /// `c · x`, for `c >= 1`.
            fn scale(x: Val<Exact>, c: u64) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.scale(&x.0 .1, c.max(1))); Val(Exact(ex, v)) }
            /// `max(x, lo)`.
            fn clamp(x: Val<Exact>, lo: i64) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.clamp(&x.0 .1, lo)); Val(Exact(ex, v)) }
            /// The values the integer can take, exact.
            fn values_big(x: Val<Exact>) -> List<Val<IBig>> { let ex = x.0 .0.clone(); list(x.0 .1.values().iter().map(|&v| ibig(&ex, v)).collect()) }
            fn at_least_big(x: Val<Exact>, v: Val<IBig>) -> Val<Bool> { Val(Bool(x.0 .0.clone(), vec![x.0 .1.at_least(v.0 .1)])) }
            fn at_most_big(x: Val<Exact>, v: Val<IBig>) -> Val<Bool> { Val(Bool(x.0 .0.clone(), vec![x.0 .1.at_most(v.0 .1)])) }
            fn plus_const_big(x: Val<Exact>, k: Val<IBig>) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.shift(&x.0 .1, k.0 .1)); Val(Exact(ex, v)) }
            /// `c · x` for an exact `c >= 1`.
            fn scale_big(x: Val<Exact>, c: Val<UBig>) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.scale(&x.0 .1, c.0 .1)); Val(Exact(ex, v)) }
            fn clamp_big(x: Val<Exact>, lo: Val<IBig>) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.clamp(&x.0 .1, lo.0 .1)); Val(Exact(ex, v)) }
            fn plus(x: Val<Exact>, y: Val<Exact>) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.plus(&x.0 .1, &y.0 .1)); Val(Exact(ex, v)) }
            fn minus(x: Val<Exact>, y: Val<Exact>) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.minus(&x.0 .1, &y.0 .1)); Val(Exact(ex, v)) }
            fn neg(x: Val<Exact>) -> Val<Exact> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.neg(&x.0 .1)); Val(Exact(ex, v)) }
            /// The integer as a term.
            fn linear(x: Val<Exact>) -> Val<Pb> { Val(Pb(x.0 .0.clone(), EPb::of(&x.0 .1))) }
            /// Add the value to the cost.
            fn charge(x: Val<Exact>) { let ex = x.0 .0.clone(); ex.build(|b, _| b.cost(&x.0 .1)) }
        }

        impl Val<Over> {
            /// `self - u`, which is `self + (-u)`: an over-estimate less an under-estimate.
            /// Not clamped: `max(self - u, 0)` is `self.minus(u).clamp(0)`.
            fn minus(o: Val<Over>, u: Val<Under>) -> Val<Over> { let ex = o.0 .0.clone(); let v = ex.build(|b, _| b.minus(&o.0 .1, &u.0 .1)); Val(Over(ex, v)) }
            fn plus(o: Val<Over>, p: Val<Over>) -> Val<Over> { let ex = o.0 .0.clone(); let v = ex.build(|b, _| b.plus(&o.0 .1, &p.0 .1)); Val(Over(ex, v)) }
            /// `-self`: an under-estimate.
            fn neg(o: Val<Over>) -> Val<Under> { let ex = o.0 .0.clone(); let v = ex.build(|b, _| b.neg(&o.0 .1)); Val(Under(ex, v)) }
            fn plus_const(o: Val<Over>, k: i64) -> Val<Over> { let ex = o.0 .0.clone(); let v = ex.build(|b, _| b.shift(&o.0 .1, k)); Val(Over(ex, v)) }
            /// This value, counted where `c` holds: a part of a maximum or minimum.
            fn when(o: Val<Over>, c: Val<Bool>) -> Val<OverPart> { Val(OverPart(c.0.clone(), o.0.clone())) }
            fn values(x: Val<Over>) -> List<i64> { values_i64(&x.0 .0, x.0 .1.values()) }
            /// "At least `v`"; may hold when the value is below `v`.
            fn at_least(x: Val<Over>, v: i64) -> Val<BoolOver> { Val(BoolOver(x.0 .0.clone(), vec![x.0 .1.at_least(v)])) }
            /// "At most `v`"; may fail when the value is at most `v`.
            fn at_most(x: Val<Over>, v: i64) -> Val<BoolUnder> { Val(BoolUnder(x.0 .0.clone(), vec![x.0 .1.at_most(v)])) }
            fn scale(x: Val<Over>, c: u64) -> Val<Over> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.scale(&x.0 .1, c.max(1))); Val(Over(ex, v)) }
            fn clamp(x: Val<Over>, lo: i64) -> Val<Over> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.clamp(&x.0 .1, lo)); Val(Over(ex, v)) }
            /// The values the integer can take, exact.
            fn values_big(x: Val<Over>) -> List<Val<IBig>> { let ex = x.0 .0.clone(); list(x.0 .1.values().iter().map(|&v| ibig(&ex, v)).collect()) }
            fn at_least_big(x: Val<Over>, v: Val<IBig>) -> Val<BoolOver> { Val(BoolOver(x.0 .0.clone(), vec![x.0 .1.at_least(v.0 .1)])) }
            fn at_most_big(x: Val<Over>, v: Val<IBig>) -> Val<BoolUnder> { Val(BoolUnder(x.0 .0.clone(), vec![x.0 .1.at_most(v.0 .1)])) }
            fn plus_const_big(x: Val<Over>, k: Val<IBig>) -> Val<Over> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.shift(&x.0 .1, k.0 .1)); Val(Over(ex, v)) }
            /// `c · x` for an exact `c >= 1`.
            fn scale_big(x: Val<Over>, c: Val<UBig>) -> Val<Over> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.scale(&x.0 .1, c.0 .1)); Val(Over(ex, v)) }
            fn clamp_big(x: Val<Over>, lo: Val<IBig>) -> Val<Over> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.clamp(&x.0 .1, lo.0 .1)); Val(Over(ex, v)) }
            fn linear(x: Val<Over>) -> Val<PbOver> { Val(PbOver(x.0 .0.clone(), EPb::of(&x.0 .1))) }
            /// Add the value to the cost: an over-estimate never understates it.
            fn charge(x: Val<Over>) { let ex = x.0 .0.clone(); ex.build(|b, _| b.cost(&x.0 .1)) }
        }

        impl Val<Under> {
            fn plus_const(u: Val<Under>, k: i64) -> Val<Under> { let ex = u.0 .0.clone(); let v = ex.build(|b, _| b.shift(&u.0 .1, k)); Val(Under(ex, v)) }
            /// This value, counted where `c` holds.
            fn when(u: Val<Under>, c: Val<Bool>) -> Val<UnderPart> { Val(UnderPart(c.0.clone(), u.0.clone())) }
            fn values(x: Val<Under>) -> List<i64> { values_i64(&x.0 .0, x.0 .1.values()) }
            /// "At least `v`"; may fail when the value is at least `v`.
            fn at_least(x: Val<Under>, v: i64) -> Val<BoolUnder> { Val(BoolUnder(x.0 .0.clone(), vec![x.0 .1.at_least(v)])) }
            /// "At most `v`"; may hold when the value is above `v`.
            fn at_most(x: Val<Under>, v: i64) -> Val<BoolOver> { Val(BoolOver(x.0 .0.clone(), vec![x.0 .1.at_most(v)])) }
            fn plus(x: Val<Under>, y: Val<Under>) -> Val<Under> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.plus(&x.0 .1, &y.0 .1)); Val(Under(ex, v)) }
            /// `self - o`: an under-estimate less an over-estimate.
            fn minus(x: Val<Under>, o: Val<Over>) -> Val<Under> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.minus(&x.0 .1, &o.0 .1)); Val(Under(ex, v)) }
            /// `-self`: an over-estimate.
            fn neg(x: Val<Under>) -> Val<Over> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.neg(&x.0 .1)); Val(Over(ex, v)) }
            fn linear(x: Val<Under>) -> Val<PbUnder> { Val(PbUnder(x.0 .0.clone(), EPb::of(&x.0 .1))) }
            fn scale(x: Val<Under>, c: u64) -> Val<Under> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.scale(&x.0 .1, c.max(1))); Val(Under(ex, v)) }
            fn clamp(x: Val<Under>, lo: i64) -> Val<Under> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.clamp(&x.0 .1, lo)); Val(Under(ex, v)) }
            /// The values the integer can take, exact.
            fn values_big(x: Val<Under>) -> List<Val<IBig>> { let ex = x.0 .0.clone(); list(x.0 .1.values().iter().map(|&v| ibig(&ex, v)).collect()) }
            fn at_least_big(x: Val<Under>, v: Val<IBig>) -> Val<BoolUnder> { Val(BoolUnder(x.0 .0.clone(), vec![x.0 .1.at_least(v.0 .1)])) }
            fn at_most_big(x: Val<Under>, v: Val<IBig>) -> Val<BoolOver> { Val(BoolOver(x.0 .0.clone(), vec![x.0 .1.at_most(v.0 .1)])) }
            fn plus_const_big(x: Val<Under>, k: Val<IBig>) -> Val<Under> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.shift(&x.0 .1, k.0 .1)); Val(Under(ex, v)) }
            /// `c · x` for an exact `c >= 1`.
            fn scale_big(x: Val<Under>, c: Val<UBig>) -> Val<Under> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.scale(&x.0 .1, c.0 .1)); Val(Under(ex, v)) }
            fn clamp_big(x: Val<Under>, lo: Val<IBig>) -> Val<Under> { let ex = x.0 .0.clone(); let v = ex.build(|b, _| b.clamp(&x.0 .1, lo.0 .1)); Val(Under(ex, v)) }
        }


        impl Val<Pb> {
            fn plus(t: Val<Pb>, u: Val<Pb>) -> Val<Pb> { Val(Pb(t.0 .0.clone(), t.0 .1.plus(&u.0 .1))) }
            /// `t - u`: `u` has the opposite polarity.
            fn minus(t: Val<Pb>, u: Val<Pb>) -> Val<Pb> { Val(Pb(t.0 .0.clone(), t.0 .1.minus(&u.0 .1))) }
            fn neg(t: Val<Pb>) -> Val<Pb> { Val(Pb(t.0 .0.clone(), t.0 .1.neg())) }
            fn times(t: Val<Pb>, c: u64) -> Val<Pb> { Val(Pb(t.0 .0.clone(), t.0 .1.times(c))) }
            fn plus_const(t: Val<Pb>, k: i64) -> Val<Pb> { Val(Pb(t.0 .0.clone(), t.0 .1.plus_const(k))) }
            fn times_big(t: Val<Pb>, c: Val<UBig>) -> Val<Pb> { Val(Pb(t.0 .0.clone(), t.0 .1.times(c.0 .1))) }
            fn plus_const_big(t: Val<Pb>, k: Val<IBig>) -> Val<Pb> { Val(Pb(t.0 .0.clone(), t.0 .1.plus_const(k.0 .1))) }
            /// `t >= k`, exact.
            fn at_least_big(t: Val<Pb>, k: Val<IBig>) -> Val<Bool> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k.0 .1)); Val(Bool(ex, vec![l])) }
            /// `t <= k`, exact.
            fn at_most_big(t: Val<Pb>, k: Val<IBig>) -> Val<Bool> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k.0 .1 + Cost::ONE)); Val(Bool(ex, vec![l.not()])) }
            /// The term as an order-encoded integer of the same polarity.
            fn sorted(t: Val<Pb>) -> Val<Exact> {
                let ex = t.0 .0.clone();
                let r = ex.build(|b, _| b.sorted(&t.0 .1));
                match r {
                    Ok(x) => Val(Exact(ex, x)),
                    Err(e) => { ex.fail(e); let z = ex.build(|b, _| b.constant(0)); Val(Exact(ex, z.clone())) }
                }
            }
            /// `t >= k`.
            fn at_least(t: Val<Pb>, k: i64) -> Val<Bool> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k)); Val(Bool(ex, vec![l])) }
            /// `t <= k`.
            fn at_most(t: Val<Pb>, k: i64) -> Val<Bool> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, Cost::from(k) + Cost::ONE)); Val(Bool(ex, vec![l.not()])) }
            /// Add the term to the cost.
            fn charge(t: Val<Pb>) { let ex = t.0 .0.clone(); if let Err(e) = ex.build(|b, _| b.charge_pb(&t.0 .1)) { ex.fail(e); } }
            fn over(t: Val<Pb>) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.clone().over())) }
            fn under(t: Val<Pb>) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.clone().under())) }
        }

        impl Val<PbOver> {
            fn plus(t: Val<PbOver>, u: Val<PbOver>) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.plus(&u.0 .1))) }
            /// `t - u`: `u` has the opposite polarity.
            fn minus(t: Val<PbOver>, u: Val<PbUnder>) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.minus(&u.0 .1))) }
            fn neg(t: Val<PbOver>) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.neg())) }
            fn times(t: Val<PbOver>, c: u64) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.times(c))) }
            fn plus_const(t: Val<PbOver>, k: i64) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.plus_const(k))) }
            fn times_big(t: Val<PbOver>, c: Val<UBig>) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.times(c.0 .1))) }
            fn plus_const_big(t: Val<PbOver>, k: Val<IBig>) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.plus_const(k.0 .1))) }
            /// `t >= k`, exact.
            fn at_least_big(t: Val<PbOver>, k: Val<IBig>) -> Val<BoolOver> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k.0 .1)); Val(BoolOver(ex, vec![l])) }
            /// `t <= k`, exact.
            fn at_most_big(t: Val<PbOver>, k: Val<IBig>) -> Val<BoolUnder> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k.0 .1 + Cost::ONE)); Val(BoolUnder(ex, vec![l.not()])) }
            /// The term as an order-encoded integer of the same polarity.
            fn sorted(t: Val<PbOver>) -> Val<Over> {
                let ex = t.0 .0.clone();
                let r = ex.build(|b, _| b.sorted(&t.0 .1));
                match r {
                    Ok(x) => Val(Over(ex, x)),
                    Err(e) => { ex.fail(e); let z = ex.build(|b, _| b.constant(0)); Val(Over(ex, z.over())) }
                }
            }
            /// `t >= k`.
            fn at_least(t: Val<PbOver>, k: i64) -> Val<BoolOver> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k)); Val(BoolOver(ex, vec![l])) }
            /// `t <= k`.
            fn at_most(t: Val<PbOver>, k: i64) -> Val<BoolUnder> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, Cost::from(k) + Cost::ONE)); Val(BoolUnder(ex, vec![l.not()])) }
            /// Add the term to the cost.
            fn charge(t: Val<PbOver>) { let ex = t.0 .0.clone(); if let Err(e) = ex.build(|b, _| b.charge_pb(&t.0 .1)) { ex.fail(e); } }
        }

        impl Val<PbUnder> {
            fn plus(t: Val<PbUnder>, u: Val<PbUnder>) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.plus(&u.0 .1))) }
            /// `t - u`: `u` has the opposite polarity.
            fn minus(t: Val<PbUnder>, u: Val<PbOver>) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.minus(&u.0 .1))) }
            fn neg(t: Val<PbUnder>) -> Val<PbOver> { Val(PbOver(t.0 .0.clone(), t.0 .1.neg())) }
            fn times(t: Val<PbUnder>, c: u64) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.times(c))) }
            fn plus_const(t: Val<PbUnder>, k: i64) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.plus_const(k))) }
            fn times_big(t: Val<PbUnder>, c: Val<UBig>) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.times(c.0 .1))) }
            fn plus_const_big(t: Val<PbUnder>, k: Val<IBig>) -> Val<PbUnder> { Val(PbUnder(t.0 .0.clone(), t.0 .1.plus_const(k.0 .1))) }
            /// `t >= k`, exact.
            fn at_least_big(t: Val<PbUnder>, k: Val<IBig>) -> Val<BoolUnder> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k.0 .1)); Val(BoolUnder(ex, vec![l])) }
            /// `t <= k`, exact.
            fn at_most_big(t: Val<PbUnder>, k: Val<IBig>) -> Val<BoolOver> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k.0 .1 + Cost::ONE)); Val(BoolOver(ex, vec![l.not()])) }
            /// The term as an order-encoded integer of the same polarity.
            fn sorted(t: Val<PbUnder>) -> Val<Under> {
                let ex = t.0 .0.clone();
                let r = ex.build(|b, _| b.sorted(&t.0 .1));
                match r {
                    Ok(x) => Val(Under(ex, x)),
                    Err(e) => { ex.fail(e); let z = ex.build(|b, _| b.constant(0)); Val(Under(ex, z.under())) }
                }
            }
            /// `t >= k`.
            fn at_least(t: Val<PbUnder>, k: i64) -> Val<BoolUnder> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, k)); Val(BoolUnder(ex, vec![l])) }
            /// `t <= k`.
            fn at_most(t: Val<PbUnder>, k: i64) -> Val<BoolOver> { let ex = t.0 .0.clone(); let l = ex.build(|b, _| b.pb_at_least(&t.0 .1, Cost::from(k) + Cost::ONE)); Val(BoolOver(ex, vec![l.not()])) }
        }

        impl Val<NodeValues> {
            fn set(m: Val<NodeValues>, n: Val<Node>, v: u64) { m.0 .1.lock().unwrap()[n.0 .1] = Cost::from(v); }
            /// A value past `u64` is an error, and 0; `get_big` reads it exactly.
            fn get(m: Val<NodeValues>, n: Val<Node>) -> u64 {
                let v = m.0 .1.lock().unwrap()[n.0 .1];
                v.to_u64().unwrap_or_else(|| { m.0 .0.fail(format!("get: the value {v} is outside a script's u64; read it with get_big")); 0 })
            }
            fn set_big(m: Val<NodeValues>, n: Val<Node>, v: Val<UBig>) { m.0 .1.lock().unwrap()[n.0 .1] = v.0 .1; }
            fn get_big(m: Val<NodeValues>, n: Val<Node>) -> Val<UBig> { let v = m.0 .1.lock().unwrap()[n.0 .1]; Val(UBig(m.0 .0.clone(), v)) }
        }

        impl Val<AttrOver> {
            /// The attribute of `c`.
            fn of(a: Val<AttrOver>, c: Val<Class>) -> Val<Over> {
                let ex = a.0 .0.clone();
                let v = match &a.0 .1[c.0 .1] { Some(v) => v.clone(), None => ex.build(|b, _| b.constant(0)).over() };
                Val(Over(ex, v))
            }
        }

        impl Val<IBig> {
            fn plus(a: Val<IBig>, b: Val<IBig>) -> Val<IBig> { ibig(&a.0 .0, a.0 .1 + b.0 .1) }
            fn minus(a: Val<IBig>, b: Val<IBig>) -> Val<IBig> { ibig(&a.0 .0, a.0 .1 - b.0 .1) }
            fn times(a: Val<IBig>, b: Val<IBig>) -> Val<IBig> { ibig(&a.0 .0, a.0 .1 * b.0 .1) }
            fn neg(a: Val<IBig>) -> Val<IBig> { ibig(&a.0 .0, -a.0 .1) }
            /// Truncated toward zero; division by zero is an error, and 0.
            fn div(a: Val<IBig>, b: Val<IBig>) -> Val<IBig> { let ex = a.0 .0.clone(); let v = divide(&ex, "div", a.0 .1.checked_div(b.0 .1)); ibig(&ex, v) }
            /// With the sign of `a`; by zero is an error, and 0.
            fn rem(a: Val<IBig>, b: Val<IBig>) -> Val<IBig> { let ex = a.0 .0.clone(); let v = divide(&ex, "rem", a.0 .1.checked_rem(b.0 .1)); ibig(&ex, v) }
            fn max(a: Val<IBig>, b: Val<IBig>) -> Val<IBig> { ibig(&a.0 .0, a.0 .1.max(b.0 .1)) }
            fn min(a: Val<IBig>, b: Val<IBig>) -> Val<IBig> { ibig(&a.0 .0, a.0 .1.min(b.0 .1)) }
            fn abs(a: Val<IBig>) -> Val<UBig> { ubig(&a.0 .0, "abs", a.0 .1.abs()) }
            fn lt(a: Val<IBig>, b: Val<IBig>) -> bool { a.0 .1 < b.0 .1 }
            fn le(a: Val<IBig>, b: Val<IBig>) -> bool { a.0 .1 <= b.0 .1 }
            fn gt(a: Val<IBig>, b: Val<IBig>) -> bool { a.0 .1 > b.0 .1 }
            fn ge(a: Val<IBig>, b: Val<IBig>) -> bool { a.0 .1 >= b.0 .1 }
            fn eq(a: Val<IBig>, b: Val<IBig>) -> bool { a.0 .1 == b.0 .1 }
            /// The value as a `UBig`; a negative value is an error, and 0.
            fn to_ubig(a: Val<IBig>) -> Val<UBig> { ubig(&a.0 .0, "to_ubig", a.0 .1) }
            /// The value as an `i64`, or `None` past it.
            fn to_i64(a: Val<IBig>) -> Option<i64> { a.0 .1.to_i64() }
            fn to_string(a: Val<IBig>) -> RotoString { RotoString::from(a.0 .1.to_string().as_str()) }
        }

        impl Val<UBig> {
            fn plus(a: Val<UBig>, b: Val<UBig>) -> Val<UBig> { ubig(&a.0 .0, "plus", a.0 .1 + b.0 .1) }
            /// A result below zero is an error, and 0.
            fn minus(a: Val<UBig>, b: Val<UBig>) -> Val<UBig> { ubig(&a.0 .0, "minus", a.0 .1 - b.0 .1) }
            fn times(a: Val<UBig>, b: Val<UBig>) -> Val<UBig> { ubig(&a.0 .0, "times", a.0 .1 * b.0 .1) }
            /// Division by zero is an error, and 0.
            fn div(a: Val<UBig>, b: Val<UBig>) -> Val<UBig> { let ex = a.0 .0.clone(); let v = divide(&ex, "div", a.0 .1.checked_div(b.0 .1)); ubig(&ex, "div", v) }
            fn rem(a: Val<UBig>, b: Val<UBig>) -> Val<UBig> { let ex = a.0 .0.clone(); let v = divide(&ex, "rem", a.0 .1.checked_rem(b.0 .1)); ubig(&ex, "rem", v) }
            fn max(a: Val<UBig>, b: Val<UBig>) -> Val<UBig> { ubig(&a.0 .0, "max", a.0 .1.max(b.0 .1)) }
            fn min(a: Val<UBig>, b: Val<UBig>) -> Val<UBig> { ubig(&a.0 .0, "min", a.0 .1.min(b.0 .1)) }
            fn lt(a: Val<UBig>, b: Val<UBig>) -> bool { a.0 .1 < b.0 .1 }
            fn le(a: Val<UBig>, b: Val<UBig>) -> bool { a.0 .1 <= b.0 .1 }
            fn gt(a: Val<UBig>, b: Val<UBig>) -> bool { a.0 .1 > b.0 .1 }
            fn ge(a: Val<UBig>, b: Val<UBig>) -> bool { a.0 .1 >= b.0 .1 }
            fn eq(a: Val<UBig>, b: Val<UBig>) -> bool { a.0 .1 == b.0 .1 }
            fn to_ibig(a: Val<UBig>) -> Val<IBig> { ibig(&a.0 .0, a.0 .1) }
            /// The value as a `u64`, or `None` past it.
            fn to_u64(a: Val<UBig>) -> Option<u64> { a.0 .1.to_u64() }
            fn to_string(a: Val<UBig>) -> RotoString { RotoString::from(a.0 .1.to_string().as_str()) }
        }

        impl Val<AttrUnder> {
            /// The attribute of `c`.
            fn of(a: Val<AttrUnder>, c: Val<Class>) -> Val<Under> {
                let ex = a.0 .0.clone();
                let v = match &a.0 .1[c.0 .1] { Some(v) => v.clone(), None => ex.build(|b, _| b.constant(0)).under() };
                Val(Under(ex, v))
            }
        }
    }
}

/// Refuse a cost script that uses Roto's own arithmetic operators.
///
/// Roto's `+`, `-`, and `*` on `i64` and `u64` wrap without an error, and its `/` and `%`
/// by zero abort the process. A cost computed through them can be silently wrong, so a
/// script may not use them, nor their compound forms (`+=`, `-=`, `*=`, `/=`, `%=`) or
/// `--`. Its arithmetic goes through the exact methods of `IBig`, `UBig`, and the encoded
/// integers (`plus`, `minus`, `times`, `div`, `rem`, `neg`). A `-` directly before a digit,
/// where an operand starts, is a negative literal and is allowed; so are the arrows `->`
/// and `=>`.
///
/// The scan is lexical, since Roto's parser is not public: it skips `//` comments, string
/// literals, and character literals. An f-string is scanned whole, so an operator in its
/// text is refused too. Returns `Err("line:column: …")` for the first operator found.
pub fn reject_native_arithmetic(src: &str) -> Result<(), String> {
    let chars: Vec<char> = src.chars().collect();
    let (mut i, mut line, mut col) = (0usize, 1usize, 1usize);
    // The last significant character and the identifier or keyword that ended there, to
    // tell a negative literal (`(-3`, `= -3`, `return -3`) from a binary minus (`k - 3`).
    let (mut last, mut last_word) = (None::<char>, String::new());
    let refuse = |line: usize, col: usize, op: &str| {
        Err(format!(
            "{line}:{col}: `{op}` is Roto's own arithmetic, which wraps on overflow or aborts \
             on division by zero; cost scripts must compute with the exact methods \
             (`plus`, `minus`, `times`, `div`, `rem`, `neg`) of IBig, UBig, and the encoded \
             integers"
        ))
    };
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        let step = |n: usize, i: &mut usize, col: &mut usize| {
            *i += n;
            *col += n;
        };
        match c {
            '\n' => {
                i += 1;
                line += 1;
                col = 1;
                continue;
            }
            c if c.is_whitespace() => {
                step(1, &mut i, &mut col);
                continue;
            }
            '/' if next == Some('/') => {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
                continue;
            }
            '"' if last_word != "f" || last != Some('f') => {
                // A string literal: skip to the unescaped closing quote.
                step(1, &mut i, &mut col);
                while i < chars.len() && chars[i] != '"' {
                    if chars[i] == '\\' {
                        step(1, &mut i, &mut col);
                    }
                    if i < chars.len() && chars[i] == '\n' {
                        line += 1;
                        col = 0;
                    }
                    step(1, &mut i, &mut col);
                }
                step(1, &mut i, &mut col);
                (last, last_word) = (Some('"'), String::new());
                continue;
            }
            '\'' => {
                // A character literal: `'x'` or `'\x'`.
                let len = match (next, chars.get(i + 2), chars.get(i + 3)) {
                    (Some('\\'), _, Some('\'')) => 4,
                    (Some(_), Some('\''), _) => 3,
                    _ => 1,
                };
                step(len, &mut i, &mut col);
                (last, last_word) = (Some('\''), String::new());
                continue;
            }
            '-' | '=' if next == Some('>') => {
                step(2, &mut i, &mut col);
                (last, last_word) = (Some('>'), String::new());
                continue;
            }
            '+' | '*' | '/' | '%' => {
                let op = if next == Some('=') {
                    format!("{c}=")
                } else {
                    c.to_string()
                };
                return refuse(line, col, &op);
            }
            '-' => {
                let operand_starts = match last {
                    None => true,
                    Some(p) if p.is_alphanumeric() || p == '_' => last_word == "return",
                    Some(p) => !matches!(p, ')' | ']' | '}' | '"' | '\''),
                };
                if next.is_some_and(|d| d.is_ascii_digit()) && operand_starts {
                    step(1, &mut i, &mut col);
                    (last, last_word) = (Some('-'), String::new());
                    continue;
                }
                let op = match next {
                    Some('=') => "-=",
                    Some('-') => "--",
                    _ => "-",
                };
                return refuse(line, col, op);
            }
            c if c.is_alphanumeric() || c == '_' => {
                let mut word = String::new();
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    word.push(chars[i]);
                    step(1, &mut i, &mut col);
                }
                last = word.chars().last();
                last_word = word;
                continue;
            }
            _ => {
                step(1, &mut i, &mut col);
                (last, last_word) = (Some(c), String::new());
            }
        }
    }
    Ok(())
}

/// [`reject_native_arithmetic`] over a script file, or every `.roto` file under a script
/// directory, naming the file in the error.
fn reject_native_arithmetic_in(path: &std::path::Path) -> Result<(), String> {
    let mut stack = vec![path.to_path_buf()];
    while let Some(p) = stack.pop() {
        if p.is_dir() {
            let entries = std::fs::read_dir(&p).map_err(|e| format!("{}: {e}", p.display()))?;
            for e in entries.flatten() {
                stack.push(e.path());
            }
        } else if p == path || p.extension().is_some_and(|x| x == "roto") {
            // An unreadable file is left to Roto, which reports it in its own words.
            if let Ok(src) = std::fs::read_to_string(&p) {
                reject_native_arithmetic(&src).map_err(|e| format!("{}:{e}", p.display()))?;
            }
        }
    }
    Ok(())
}

/// A compiled cost script.
pub struct Script {
    // Holds the compiled module alive; compiling once matters because Cranelift
    // takes far longer than one small build.
    cost: TypedFunc<NoCtx, fn(Val<Graph>)>,
}

impl Script {
    /// Compile `path` against the binding. A type error, including a polarity
    /// error, is reported here, before anything is built.
    pub fn compile(path: &str) -> Result<Script, String> {
        reject_native_arithmetic_in(std::path::Path::new(path))?;
        let rt = Runtime::from_lib(lib()).map_err(|e| format!("{e:?}"))?;
        let mut compiled = rt.compile(path).map_err(|e| e.to_string())?;
        let cost = compiled
            .get_function::<fn(Val<Graph>)>("cost")
            .map_err(|e| e.to_string())?;
        Ok(Script { cost })
    }

    /// Build the problem at `rung` with this script's cost, its values in `width`, and
    /// solve it.
    pub fn extract(
        &self,
        graph: Arc<EGraph>,
        rung: RungKind,
        solver: &Solver,
        width: CostWidth,
    ) -> Result<Outcome, String> {
        let (r, rec, prepared) =
            self.run(rung_on(&graph, rung, Prepared::for_solver(solver), width))?;
        solve_prepared(&graph, &*r, &rec, prepared, solver)
    }

    /// The cost this script gives `term` at `rung`, with no solving. The term need
    /// not come from this script. Fails when the build refuses an operation or the
    /// cost is outside `width`.
    pub fn try_cost_of(
        &self,
        graph: Arc<EGraph>,
        rung: RungKind,
        term: &Term,
        width: CostWidth,
    ) -> Result<Cost, String> {
        let (r, rec, _) = self.run(rung_on(
            &graph,
            rung,
            Prepared::Cnf(Default::default()),
            width,
        ))?;
        interpret(&rec, &*r, term, &|_| false)
    }

    /// [`Self::try_cost_of`] at the default width, for a script known to build.
    pub fn cost_of(&self, graph: Arc<EGraph>, rung: RungKind, term: &Term) -> Cost {
        self.try_cost_of(graph, rung, term, CostWidth::default())
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Run the script on a rung already built, adding its cost.
    fn run(
        &self,
        (rung, rec, prepared): (Box<dyn Rung>, Detached, Prepared),
    ) -> Result<(Box<dyn Rung>, Detached, Prepared), String> {
        let graph = rung.selection().graph.clone();
        let ctx = Arc::new(Mutex::new(Ctx {
            graph,
            rung,
            prepared,
            rec,
            errors: Vec::new(),
        }));
        self.cost.call(Val(Graph(Ex(ctx.clone()))));
        let ctx = Arc::try_unwrap(ctx)
            .ok()
            .expect("the script keeps no handle")
            .into_inner()
            .unwrap();
        let errors: Vec<String> = ctx
            .errors
            .iter()
            .chain(ctx.rec.errors.iter())
            .cloned()
            .collect();
        if !errors.is_empty() {
            return Err(format!(
                "the cost script's build failed: {}",
                errors.join("; ")
            ));
        }
        Ok((ctx.rung, ctx.rec, ctx.prepared))
    }
}

/// A cost function written in Rust, over any rung.
pub type NativeCost = fn(&dyn Rung, &mut Build);

/// A named cost, as `(cost-model NAME :script PATH)` or `(cost-model NAME :rust ID)`
/// declares it.
pub enum CostModel {
    Script(Script),
    Native(NativeCost),
    /// Criteria in ASP, appended to the ASP dump of the e-graph (`crate::extraction::lp`):
    /// solved by clingo only.
    Lp(String),
    /// Criteria in MiniZinc, appended to the MiniZinc dump of the e-graph
    /// (`crate::extraction::mzn`): solved through `minizinc` only.
    Mzn(String),
}

fn mzn_outcome(o: crate::extraction::mzn::MznOutcome) -> Outcome {
    // The solver's bound, when it reports one, is the one solver value kept.
    Outcome {
        term: o.term,
        cost: o.cost.map(Cost::from),
        status: o.status,
        warnings: Vec::new(),
        stats: Default::default(),
        solver_costs: o.bound.into_iter().collect(),
        certificate: None,
    }
}

const MZN_SOLVER: &str =
    "a MiniZinc cost model is solved through minizinc: :solver (minizinc \"cp-sat\")";
const NOT_MZN: &str =
    "a MiniZinc solver takes a MiniZinc cost model, (cost-model NAME :minizinc \"f.mzn\")";

/// An ASP extraction as an outcome: the reported cost is the criteria's most
/// important value on the term, and all of them are the solver costs.
fn lp_outcome(o: crate::extraction::lp::LpOutcome) -> Outcome {
    Outcome {
        cost: o
            .term
            .as_ref()
            .map(|_| Cost::from(o.costs.first().copied().unwrap_or(0))),
        term: o.term,
        status: o.status,
        warnings: Vec::new(),
        stats: Default::default(),
        solver_costs: o.costs,
        certificate: None,
    }
}

const LP_SOLVER: &str = "an ASP cost model is solved by clingo: :solver (asp \"clingo\")";

/// `out`, when its cost lies in `width`: the check a solver's own cost (ASP or
/// MiniZinc criteria) gets, as an interpreted cost gets it from the build.
fn within(out: Outcome, width: CostWidth) -> Result<Outcome, String> {
    if let Some(c) = out.cost {
        width.check("the cost", c)?;
    }
    Ok(out)
}

impl CostModel {
    /// Build at `rung` with the model's cost, its values in `width`, and solve.
    pub fn extract(
        &self,
        graph: Arc<EGraph>,
        rung: RungKind,
        solver: &Solver,
        width: CostWidth,
    ) -> Result<Outcome, String> {
        match self {
            CostModel::Lp(criteria) => match solver {
                Solver::Asp(cmd) => within(
                    lp_outcome(crate::extraction::lp::extract(&graph, rung, criteria, cmd)?),
                    width,
                ),
                _ => Err(LP_SOLVER.into()),
            },
            CostModel::Mzn(criteria) => match solver {
                Solver::MiniZinc(cmd) => within(
                    mzn_outcome(crate::extraction::mzn::extract(
                        &graph, rung, criteria, cmd,
                    )?),
                    width,
                ),
                _ => Err(MZN_SOLVER.into()),
            },
            _ if matches!(solver, Solver::MiniZinc(_)) => Err(NOT_MZN.into()),
            CostModel::Script(s) => s.extract(graph, rung, solver, width),
            CostModel::Native(f) => {
                let (r, rec, prepared) = native(
                    *f,
                    rung_on(&graph, rung, Prepared::for_solver(solver), width),
                );
                solve_prepared(&graph, &*r, &rec, prepared, solver)
            }
        }
    }

    /// Distinct terms with cost in `band`, on the internal CNF solver.
    pub fn band(
        &self,
        graph: Arc<EGraph>,
        rung: RungKind,
        band: crate::extraction::solve::Band,
        width: CostWidth,
    ) -> Result<Vec<(Cost, Term)>, String> {
        let (r, rec, prepared) = match self {
            CostModel::Lp(_) => {
                return Err(":band runs on the internal solver, not on an ASP cost model".into());
            }
            CostModel::Mzn(_) => {
                return Err(
                    ":band runs on the internal solver, not on a MiniZinc cost model".into(),
                );
            }
            CostModel::Script(s) => s.run(rung_on(
                &graph,
                rung,
                Prepared::Cnf(Default::default()),
                width,
            ))?,
            CostModel::Native(f) => native(
                *f,
                rung_on(&graph, rung, Prepared::Cnf(Default::default()), width),
            ),
        };
        let Prepared::Cnf(cnf) = prepared else {
            unreachable!("built on a CNF target")
        };
        Ok(crate::extraction::solve::band_prepared(&graph, &*r, &rec, cnf, band, 100_000)?.0)
    }

    /// The cost this model gives `term` at `rung`, with no solving, in `width`.
    pub fn try_cost_of(
        &self,
        graph: Arc<EGraph>,
        rung: RungKind,
        term: &Term,
        width: CostWidth,
    ) -> Result<Cost, String> {
        let cost = match self {
            CostModel::Mzn(criteria) => {
                let cp = crate::extraction::solve::OpbCommand::new("minizinc")
                    .arg("--solver")
                    .arg("cp-sat");
                Cost::from(crate::extraction::mzn::cost_of(
                    &graph, rung, criteria, term, &cp,
                )?)
            }
            CostModel::Lp(criteria) => {
                let clingo = crate::extraction::solve::OpbCommand::new("clingo");
                Cost::from(
                    crate::extraction::lp::cost_of(&graph, rung, criteria, term, &clingo)?
                        .first()
                        .copied()
                        .unwrap_or(0),
                )
            }
            CostModel::Script(s) => return s.try_cost_of(graph, rung, term, width),
            CostModel::Native(f) => {
                let (r, rec, _) = native(
                    *f,
                    rung_on(&graph, rung, Prepared::Cnf(Default::default()), width),
                );
                built(&rec)?;
                return interpret(&rec, &*r, term, &|_| false);
            }
        };
        width.check("the cost", cost)
    }

    /// [`Self::try_cost_of`] at the default width, for a model known to build.
    pub fn cost_of(&self, graph: Arc<EGraph>, rung: RungKind, term: &Term) -> Cost {
        self.try_cost_of(graph, rung, term, CostWidth::default())
            .unwrap_or_else(|e| panic!("{e}"))
    }
}

fn native(
    f: NativeCost,
    (r, rec, mut prepared): (Box<dyn Rung>, Detached, Prepared),
) -> (Box<dyn Rung>, Detached, Prepared) {
    let rec = {
        let mut b = Build::from_parts(prepared.target(), rec);
        f(&*r, &mut b);
        b.detach()
    };
    (r, rec, prepared)
}

/// Build `rung` on `graph` into `prepared`, the values in `width`.
fn rung_on(
    graph: &Arc<EGraph>,
    rung: RungKind,
    mut prepared: Prepared,
    width: CostWidth,
) -> (Box<dyn Rung>, Detached, Prepared) {
    let (r, rec) = {
        let mut b = Build::with_width(prepared.target(), width);
        let sel = Selection::build(graph.clone(), &mut b);
        let r: Box<dyn Rung> = match rung {
            RungKind::Selection => Box::new(sel),
            RungKind::Levels => Box::new(Levels::build(sel, &mut b)),
            RungKind::Splits => Box::new(Splits::build(sel, &mut b, false)),
            RungKind::Binary => Box::new(Splits::build(sel, &mut b, true)),
            RungKind::Orders => Box::new(Orders::build(sel, &mut b)),
        };
        (r, b.detach())
    };
    (r, rec, prepared)
}
