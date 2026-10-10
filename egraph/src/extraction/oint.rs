// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Order-encoded integers and the operators over them.
//!
//! An [`OInt`] is an integer over a sorted set of values `v₀ < v₁ < …`, represented
//! by one literal per value, `ge[j] ⇔ x ≥ vⱼ`, with the chain `ge[j+1] → ge[j]`
//! emitted when it is created. `v₀` is always the least value the integer can take,
//! so `ge[0]` is the constant true.
//!
//! # Polarity
//!
//! The type parameter records the direction in which the encoding may be wrong:
//!
//! | polarity | in every model | forced |
//! | --- | --- | --- |
//! | [`Exact`] | encoded = true value | both directions |
//! | [`Over`] | encoded ≥ true value | upward only |
//! | [`Under`] | encoded ≤ true value | downward only |
//!
//! and in each case some model attains the true value exactly. One direction costs
//! about half the clauses of both, and it is enough when the value is only ever
//! minimized (`Over`) or only ever subtracted (`Under`). The operators take the
//! polarities that keep their result sound and no others, so subtracting an `Over`
//! does not type-check. [`OInt::assume`] is the escape, and it records a warning.
//!
//! # Interpretation
//!
//! Every integer is also a node of an expression graph kept by the [`Build`]. The
//! graph is evaluated on a decoded term by [`Build::eval`], which gives the true
//! value whatever the encoding's slack. That value, not the solver's objective, is
//! the cost the library reports.

use crate::extraction::Lit;
use crate::extraction::cost::{Cost, CostWidth};
use crate::extraction::target::{Cmp, Target};
use std::collections::BTreeMap;
use std::marker::PhantomData;

/// Encoded equals true.
#[derive(Clone, Copy, Debug)]
pub struct Exact;
/// Encoded at least true.
#[derive(Clone, Copy, Debug)]
pub struct Over;
/// Encoded at most true.
#[derive(Clone, Copy, Debug)]
pub struct Under;

pub trait Polarity: Copy + std::fmt::Debug + 'static {
    const NAME: &'static str;
    /// Whether the encoding must force the value up (never below the truth).
    const UP: bool;
    /// Whether the encoding must force the value down (never above the truth).
    const DOWN: bool;
    /// The polarity of the negation.
    type Flip: Polarity;
}
impl Polarity for Exact {
    const NAME: &'static str = "Exact";
    const UP: bool = true;
    const DOWN: bool = true;
    type Flip = Exact;
}
impl Polarity for Over {
    const NAME: &'static str = "Over";
    const UP: bool = true;
    const DOWN: bool = false;
    type Flip = Under;
}
impl Polarity for Under {
    const NAME: &'static str = "Under";
    const UP: bool = false;
    const DOWN: bool = true;
    type Flip = Over;
}

/// Polarities whose encoded value is never below the true one.
pub trait Up: Polarity {}
impl Up for Exact {}
impl Up for Over {}
/// Polarities whose encoded value is never above the true one.
pub trait Down: Polarity {}
impl Down for Exact {}
impl Down for Under {}

/// Index of a node of the expression graph.
pub type ExprId = usize;

/// An order-encoded integer. Cheap to clone: the literals are shared by value.
#[derive(Clone, Debug)]
pub struct OInt<P: Polarity> {
    pub(crate) id: ExprId,
    values: Vec<Cost>,
    ge: Vec<Lit>,
    _p: PhantomData<P>,
}

impl OInt<Exact> {
    /// An exact integer is on both sides of its value, so it widens to either
    /// polarity with no warning.
    pub fn over(self) -> OInt<Over> {
        OInt {
            id: self.id,
            values: self.values,
            ge: self.ge,
            _p: PhantomData,
        }
    }

    pub fn under(self) -> OInt<Under> {
        OInt {
            id: self.id,
            values: self.values,
            ge: self.ge,
            _p: PhantomData,
        }
    }
}

impl<P: Polarity> OInt<P> {
    /// The values the integer can take, ascending.
    pub fn values(&self) -> &[Cost] {
        &self.values
    }

    /// The literal for "at least `v`", rounding `v` up to the next value the
    /// integer can take. Above the largest value it is the constant false.
    ///
    /// For an `Over` integer the literal may be true when the value is below `v`;
    /// for an `Under` one it may be false when the value is at least `v`.
    pub fn at_least(&self, v: impl Into<Cost>) -> Lit {
        let v = v.into();
        let j = self.values.partition_point(|&x| x < v);
        self.ge.get(j).copied().unwrap_or(Lit::False)
    }

    /// The literal for "at most `v`": the negation of "at least `v + 1`", which is
    /// exact, so at the largest value of any width it is the constant true.
    pub fn at_most(&self, v: impl Into<Cost>) -> Lit {
        self.at_least(v.into() + Cost::ONE).not()
    }

    /// The same integer, read with another polarity. Recorded as a warning: the
    /// caller takes responsibility for the direction the encoding may be wrong in.
    pub fn assume<Q: Polarity>(&self, b: &mut Build) -> OInt<Q> {
        b.warn(Warning::PolarityEscape {
            from: P::NAME,
            to: Q::NAME,
        });
        OInt {
            id: self.id,
            values: self.values.clone(),
            ge: self.ge.clone(),
            _p: PhantomData,
        }
    }

    /// The unit expansion: bit `t` (from 0) is `[x >= v0 + t + 1]`, a gap between
    /// breakpoints repeating the literal of the next one. `Err` when the span exceeds
    /// [`MAX_UNARY`], whose literals would not fit in memory.
    pub fn unary(&self) -> Result<Vec<Lit>, String> {
        let (v0, top) = (self.values[0], self.values[self.values.len() - 1]);
        let span = (top - v0)
            .to_u64()
            .filter(|&n| n <= MAX_UNARY)
            .ok_or_else(|| {
                format!(
                    "the unit expansion of an integer spanning {} values exceeds {MAX_UNARY}",
                    top - v0
                )
            })?;
        Ok((1..=span)
            .map(|t| self.at_least(v0 + Cost::from(t)))
            .collect())
    }

    /// Threshold literals with their values, for a cost function that writes its
    /// own constraints.
    pub fn thresholds(&self) -> impl Iterator<Item = (Cost, Lit)> + '_ {
        self.values.iter().copied().zip(self.ge.iter().copied())
    }

    /// The value as weighted literals: `v₀ + Σ (vⱼ − vⱼ₋₁)·ge[j]`, every weight positive.
    pub fn linear(&self) -> (Cost, Vec<(Cost, Lit)>) {
        let mut terms = Vec::new();
        for j in 1..self.values.len() {
            terms.push((self.values[j] - self.values[j - 1], self.ge[j]));
        }
        (self.values.first().copied().unwrap_or(Cost::ZERO), terms)
    }
}

/// Something questionable the build did anyway.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Warning {
    /// An integer has more values than the size threshold.
    LargeDomain { values: usize, threshold: usize },
    /// [`Build::saturate`] truncated values above its bound.
    DomainCapped { bound: Cost, dropped: usize },
    /// [`OInt::assume`] reinterpreted a polarity.
    PolarityEscape {
        from: &'static str,
        to: &'static str,
    },
}

/// A node of the expression graph, evaluated by [`Build::eval`].
#[derive(Clone, Debug)]
pub(crate) enum Expr {
    Const(Cost),
    /// Read from the model: the encoding is exact.
    Read {
        values: Vec<Cost>,
        ge: Vec<Lit>,
    },
    Shift(ExprId, Cost),
    Max(Vec<(Vec<Lit>, ExprId)>),
    Min(Vec<(Vec<Lit>, ExprId)>),
    ClampSub(ExprId, ExprId),
    Sum(Vec<ExprId>),
    Ite(Lit, ExprId, ExprId),
    Saturate(ExprId, Cost),
    /// `c · x`.
    Scale(ExprId, Cost),
    /// `max(x, lo)`.
    Clamp(ExprId, Cost),
    /// `-x`.
    Neg(ExprId),
    /// The value of a pseudo-Boolean term, as [`Build::sorted`] makes it.
    Pb(crate::extraction::pb::PbRec),
    /// Filled in by the rung's recursive attributes.
    External(usize),
}

impl Expr {
    /// The operation, for an error message.
    fn name(&self) -> &'static str {
        match self {
            Expr::Const(_) => "constant",
            Expr::Read { .. } => "int",
            Expr::Shift(..) => "plus_const",
            Expr::Max(_) => "max",
            Expr::Min(_) => "min",
            Expr::ClampSub(..) => "clamp_sub",
            Expr::Sum(_) => "plus",
            Expr::Ite(..) => "ite",
            Expr::Saturate(..) => "saturate",
            Expr::Scale(..) => "scale",
            Expr::Clamp(..) => "clamp",
            Expr::Neg(_) => "neg",
            Expr::Pb(_) => "sorted",
            Expr::External(_) => "attribute",
        }
    }
}

/// How [`Build::plus_by`] adds two order-encoded integers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SumMethod {
    /// Whichever [`SumMethod::choose`] estimates smaller.
    Auto,
    /// One clause per pair of breakpoints: `|Da|·|Db|` per direction, and a result over
    /// exactly the sums that can occur.
    Pairwise,
    /// Batcher's merge over the unit expansions: about `1.5·n·log2 n` clauses per
    /// direction for `n = Va + Vb` unit bits, and a result over every value in range.
    Network,
}

impl SumMethod {
    /// The estimated clause counts per direction, pairwise and network.
    pub fn estimates(a: &[Cost], b: &[Cost]) -> (u64, u64) {
        // Saturating: an estimate past u64 is over every budget either way.
        let pairwise = (a.len() as u64).saturating_mul(b.len() as u64);
        if a.is_empty() || b.is_empty() {
            // An attribute has no values on a class reachable only through a cycle;
            // the pairwise encoding of such a sum is empty.
            return (pairwise, u64::MAX);
        }
        let span = (a[a.len() - 1] - a[0]) + (b[b.len() - 1] - b[0]);
        let n = span.to_u64().unwrap_or(u64::MAX).max(1);
        let network = n.saturating_mul(3 * (64 - n.leading_zeros() as u64) / 2);
        (pairwise, network)
    }

    /// The network when its estimate is at most half the pairwise one, so small or
    /// sparse operands keep the pairwise encoding.
    pub fn choose(a: &[Cost], b: &[Cost]) -> SumMethod {
        let (pairwise, network) = Self::estimates(a, b);
        if network.saturating_mul(2) <= pairwise {
            SumMethod::Network
        } else {
            SumMethod::Pairwise
        }
    }

    fn resolve(self, a: &[Cost], b: &[Cost]) -> SumMethod {
        match self {
            SumMethod::Auto => Self::choose(a, b),
            m => m,
        }
    }
}

/// Values above which an integer triggers [`Warning::LargeDomain`]. A warning only:
/// no value is dropped.
pub const LARGE_DOMAIN: usize = 4096;

/// Unit bits above which [`OInt::unary`] refuses: 2^24 literals, and the merge over them
/// about 36 times as many clauses, is past what the 8 GB limit the benchmarks run under
/// allows. The sum and difference that use it fall back to the pairwise encoding.
pub const MAX_UNARY: u64 = 1 << 24;

/// A Boolean defined by the builder, for interpretation.
#[derive(Clone, Debug)]
pub(crate) enum BoolDef {
    And(Lit, Lit),
}

/// A recursive per-class attribute, for interpretation.
#[derive(Clone, Debug)]
pub(crate) struct RecDef {
    pub(crate) max: bool,
    /// Offset per node, exact.
    pub(crate) offset: Vec<Cost>,
    /// External slot per class.
    pub(crate) slot: Vec<Option<usize>>,
}

/// What a build recorded for interpretation, detached from its target once the
/// build is done, so the solve loop can own the target and still interpret.
#[derive(Clone, Debug, Default)]
pub struct Detached {
    /// The range every integer value and the interpreted cost must lie in.
    pub width: CostWidth,
    /// The most values a recursive attribute may take on one class; reaching it is a
    /// build error. `None`, the default, is no limit.
    pub attribute_cap: Option<usize>,
    pub(crate) exprs: Vec<Expr>,
    pub warnings: Vec<Warning>,
    pub(crate) bool_defs: BTreeMap<u32, BoolDef>,
    /// Objective as recorded: charged integers, gated constants, and the base.
    pub(crate) charged: Vec<ExprId>,
    pub(crate) charged_if: Vec<(Lit, Cost)>,
    pub(crate) charged_base: Cost,
    pub(crate) charged_pb: Vec<crate::extraction::pb::PbRec>,
    pub(crate) recs: Vec<RecDef>,
    pub(crate) slots: usize,
    /// Operations the build could not perform, such as an overflowing sum. An
    /// extraction whose build has any fails with them.
    pub errors: Vec<String>,
}

/// The builder a cost function writes into.
pub struct Build<'t> {
    pub(crate) target: &'t mut dyn Target,
    pub(crate) rec: Detached,
}

impl<'t> std::ops::Deref for Build<'t> {
    type Target = Detached;
    fn deref(&self) -> &Detached {
        &self.rec
    }
}

fn sorted(mut v: Vec<Cost>) -> Vec<Cost> {
    v.sort_unstable();
    v.dedup();
    v
}

/// Literal value in a model; constants are themselves.
pub fn lit_value(model: &dyn Fn(u32) -> bool, l: Lit) -> bool {
    match l {
        Lit::True => true,
        Lit::False => false,
        Lit::Var { var, sign } => model(var) == sign,
    }
}

impl<'t> Build<'t> {
    pub fn new(target: &'t mut dyn Target) -> Self {
        Build {
            target,
            rec: Detached::default(),
        }
    }

    /// A build whose values must lie in `width`.
    pub fn with_width(target: &'t mut dyn Target, width: CostWidth) -> Self {
        Build {
            target,
            rec: Detached {
                width,
                ..Default::default()
            },
        }
    }

    /// Limit a recursive attribute to `cap` values per class (see
    /// [`Detached::attribute_cap`]).
    pub fn set_attribute_cap(&mut self, cap: Option<usize>) {
        self.rec.attribute_cap = cap;
    }

    /// End the build, keeping what interpretation needs.
    pub fn detach(self) -> Detached {
        self.rec
    }

    /// Resume a build over `target` with previously recorded state, as a scripting
    /// binding does between calls.
    pub fn from_parts(target: &'t mut dyn Target, rec: Detached) -> Self {
        Build { target, rec }
    }

    pub fn target(&mut self) -> &mut dyn Target {
        &mut *self.target
    }

    /// The target as CNF, when it is one: for tests and for the internal solver.
    pub fn cnf(&self) -> Option<&crate::extraction::target::CnfTarget> {
        self.target.as_any().downcast_ref()
    }

    /// Record an operation the build could not perform. The first 20 distinct
    /// errors are kept: an operation in a loop would otherwise repeat one per pass.
    pub fn fail(&mut self, e: String) {
        if self.rec.errors.len() < 20 && !self.rec.errors.contains(&e) {
            self.rec.errors.push(e);
        }
    }

    /// Report `r`'s error, if any.
    pub(crate) fn report(&mut self, r: Result<(), String>) {
        if let Err(e) = r {
            self.fail(e);
        }
    }

    pub(crate) fn warn(&mut self, w: Warning) {
        if !self.rec.warnings.contains(&w) {
            self.rec.warnings.push(w);
        }
    }

    fn push(&mut self, e: Expr) -> ExprId {
        self.rec.exprs.push(e);
        self.rec.exprs.len() - 1
    }

    pub(crate) fn thermometer_pub(&mut self, values: &[Cost]) -> Vec<Lit> {
        self.thermometer(values)
    }

    /// Allocate thresholds over `values`: `ge[0]` true, the rest fresh, chained.
    fn thermometer(&mut self, values: &[Cost]) -> Vec<Lit> {
        if values.len() > LARGE_DOMAIN {
            self.warn(Warning::LargeDomain {
                values: values.len(),
                threshold: LARGE_DOMAIN,
            });
        }
        let mut ge = vec![Lit::True];
        for _ in 1..values.len() {
            ge.push(self.target.fresh());
        }
        for j in 2..ge.len() {
            self.target.clause(&[ge[j].not(), ge[j - 1]]);
        }
        ge
    }

    /// The integer over `values` (ascending, not empty), its range checked against the
    /// build's width: an out-of-range value is an error naming the operation.
    fn make<P: Polarity>(&mut self, values: Vec<Cost>, ge: Vec<Lit>, e: Expr) -> OInt<P> {
        let w = self.rec.width;
        // Ascending, so the ends decide.
        for v in [values.first(), values.last()].into_iter().flatten() {
            if !w.contains(*v) {
                let op = e.name();
                self.fail(w.check(op, *v).unwrap_err());
            }
        }
        let id = self.push(e);
        OInt {
            id,
            values,
            ge,
            _p: PhantomData,
        }
    }

    /// [`Self::make`] for the modules that build integers of their own.
    pub(crate) fn make_pub<P: Polarity>(
        &mut self,
        values: Vec<Cost>,
        ge: Vec<Lit>,
        e: Expr,
    ) -> OInt<P> {
        self.make(values, ge, e)
    }

    /// A constant.
    pub fn constant(&mut self, v: impl Into<Cost>) -> OInt<Exact> {
        let v = v.into();
        self.make(vec![v], vec![Lit::True], Expr::Const(v))
    }

    /// A free integer over `values`, a decision variable of the search. No values is
    /// an error, and the integer is then the constant 0.
    pub fn int<V: Into<Cost> + Copy>(&mut self, values: &[V]) -> OInt<Exact> {
        let values = sorted(values.iter().map(|&v| v.into()).collect());
        if values.is_empty() {
            self.fail("int: an integer needs at least one value".into());
            return self.constant(0);
        }
        let ge = self.thermometer(&values);
        self.make(values.clone(), ge.clone(), Expr::Read { values, ge })
    }

    /// An integer given by existing threshold literals, which must encode it
    /// exactly: `ge[j] ⇔ x ≥ values[j]`. How a rung exposes its variables.
    pub fn from_thresholds<V: Into<Cost>>(&mut self, values: Vec<V>, ge: Vec<Lit>) -> OInt<Exact> {
        assert_eq!(values.len(), ge.len());
        let values: Vec<Cost> = values.into_iter().map(Into::into).collect();
        self.make(values.clone(), ge.clone(), Expr::Read { values, ge })
    }

    /// An integer whose value the rung computes, such as a recursive attribute.
    pub(crate) fn external<P: Polarity>(
        &mut self,
        values: Vec<Cost>,
        ge: Vec<Lit>,
        slot: usize,
    ) -> OInt<P> {
        self.make(values, ge, Expr::External(slot))
    }

    /// `x + c`. Free: the same literals under shifted values.
    pub fn shift<P: Polarity>(&mut self, x: &OInt<P>, c: impl Into<Cost>) -> OInt<P> {
        let c = c.into();
        let values = x.values.iter().map(|&v| v + c).collect();
        self.make(values, x.ge.clone(), Expr::Shift(x.id, c))
    }

    /// `c · x` for `c >= 1`. Free: the same literals under scaled values. A factor below
    /// 1 is an error, and the result is then `x`.
    pub fn scale<P: Polarity>(&mut self, x: &OInt<P>, c: impl Into<Cost>) -> OInt<P> {
        let c = c.into();
        if c < 1 {
            self.fail(format!("scale: the factor {c} is not at least 1"));
            return self.make(x.values.clone(), x.ge.clone(), Expr::Scale(x.id, Cost::ONE));
        }
        let values = x.values.iter().map(|&v| v * c).collect();
        self.make(values, x.ge.clone(), Expr::Scale(x.id, c))
    }

    /// `max(x, lo)`. Free: the breakpoints at or below `lo` become `lo`, whose
    /// threshold holds always, and the others keep their literals.
    pub fn clamp<P: Polarity>(&mut self, x: &OInt<P>, lo: impl Into<Cost>) -> OInt<P> {
        let lo = lo.into();
        let keep = x.values.partition_point(|&v| v <= lo);
        let mut values = vec![lo];
        let mut ge = vec![Lit::True];
        values.extend_from_slice(&x.values[keep..]);
        ge.extend_from_slice(&x.ge[keep..]);
        self.make(values, ge, Expr::Clamp(x.id, lo))
    }

    /// `-x`. Free: the breakpoints negated and reversed, and `[-x >= -v(j)]` is
    /// `not [x >= v(j+1)]`. An over-estimate negated is an under-estimate.
    pub fn neg<P: Polarity>(&mut self, x: &OInt<P>) -> OInt<P::Flip> {
        let n = x.values.len();
        let values: Vec<Cost> = (0..n).map(|j| -x.values[n - 1 - j]).collect();
        let ge: Vec<Lit> = (0..n)
            .map(|j| if j == 0 { Lit::True } else { x.ge[n - j].not() })
            .collect();
        self.make(values, ge, Expr::Neg(x.id))
    }

    /// `a + b`, with the directions `P` needs: upward for an over-estimate, downward
    /// for an under-estimate, both for an exact sum. The method is chosen by
    /// [`SumMethod::choose`].
    pub fn plus<P: Polarity>(&mut self, a: &OInt<P>, b: &OInt<P>) -> OInt<P> {
        self.plus_by(a, b, SumMethod::Auto)
    }

    /// `a + b` by the given method.
    pub fn plus_by<P: Polarity>(&mut self, a: &OInt<P>, b: &OInt<P>, method: SumMethod) -> OInt<P> {
        let units = match method.resolve(a.values(), b.values()) {
            // A span past `MAX_UNARY` takes the pairwise encoding, which is exact too.
            SumMethod::Network => a.unary().and_then(|ua| Ok((ua, b.unary()?))).ok(),
            _ => None,
        };
        let (values, ge) = match units {
            Some((ua, ub)) => {
                let c = self.merge(&ua, &ub, P::UP, P::DOWN);
                let v0 = a.values[0] + b.values[0];
                let values: Vec<Cost> = (0..=c.len()).map(|t| v0 + Cost::from(t)).collect();
                let mut ge = vec![Lit::True];
                ge.extend(c);
                (values, ge)
            }
            None => self.sum_blocks(
                vec![
                    (a.values.clone(), a.ge.clone()),
                    (b.values.clone(), b.ge.clone()),
                ],
                P::UP,
                P::DOWN,
            ),
        };
        self.make(values, ge, Expr::Sum(vec![a.id, b.id]))
    }

    /// Batcher's odd-even merge of two sorted bit vectors (`x[t]` is "at least `t +
    /// 1`"), one comparator per pair it compares: `max = x or y`, `min = x and y`,
    /// with the upward clauses (inputs force outputs) where `up` and the downward ones
    /// where `down`. The outputs are chained so they read as an order encoding.
    pub(crate) fn merge(&mut self, x: &[Lit], y: &[Lit], up: bool, down: bool) -> Vec<Lit> {
        let out = self.merge_rec(x, y, up, down);
        for t in 1..out.len() {
            self.target.clause(&[out[t].not(), out[t - 1]]);
        }
        out
    }

    fn merge_rec(&mut self, x: &[Lit], y: &[Lit], up: bool, down: bool) -> Vec<Lit> {
        if x.is_empty() {
            return y.to_vec();
        }
        if y.is_empty() {
            return x.to_vec();
        }
        if x.len() == 1 && y.len() == 1 {
            let (hi, lo) = self.comparator(x[0], y[0], up, down);
            return vec![hi, lo];
        }
        let evens = |v: &[Lit]| v.iter().step_by(2).copied().collect::<Vec<_>>();
        let odds = |v: &[Lit]| v.iter().skip(1).step_by(2).copied().collect::<Vec<_>>();
        let v = self.merge_rec(&evens(x), &evens(y), up, down);
        let w = self.merge_rec(&odds(x), &odds(y), up, down);
        let mut z = vec![v[0]];
        let mut i = 0;
        while i < w.len() || i + 1 < v.len() {
            match (w.get(i), v.get(i + 1)) {
                (Some(&a), Some(&b)) => {
                    let (hi, lo) = self.comparator(a, b, up, down);
                    z.push(hi);
                    z.push(lo);
                }
                (Some(&a), None) => z.push(a),
                (None, Some(&b)) => z.push(b),
                (None, None) => unreachable!(),
            }
            i += 1;
        }
        z
    }

    fn comparator(&mut self, a: Lit, b: Lit, up: bool, down: bool) -> (Lit, Lit) {
        let hi = self.target.fresh();
        let lo = self.target.fresh();
        if up {
            self.target.clause(&[a.not(), hi]);
            self.target.clause(&[b.not(), hi]);
            self.target.clause(&[a.not(), b.not(), lo]);
        }
        if down {
            self.target.clause(&[hi.not(), a, b]);
            self.target.clause(&[lo.not(), a]);
            self.target.clause(&[lo.not(), b]);
        }
        (hi, lo)
    }

    /// `a - b`, which is `a + (-b)`: `b` has the flipped polarity, so only an
    /// under-estimate is subtracted from an over-estimate. Not clamped: `max(a - b,
    /// 0)` is `clamp(minus(a, b), 0)`.
    pub fn minus<P: Polarity>(&mut self, a: &OInt<P>, b: &OInt<P::Flip>) -> OInt<P>
    where
        P::Flip: Polarity<Flip = P>,
    {
        let nb = self.neg(b);
        self.plus(a, &nb)
    }

    /// The maximum over the parts whose gates all hold, or 0 when none does.
    /// Gates must be exact literals.
    pub fn max_of<P: Up>(&mut self, parts: &[(Vec<Lit>, OInt<P>)]) -> OInt<Over> {
        let values = sorted(
            std::iter::once(Cost::ZERO)
                .chain(parts.iter().flat_map(|(_, x)| x.values.iter().copied()))
                .collect(),
        );
        let ge = self.thermometer(&values);
        let out: OInt<Over> = OInt {
            id: 0,
            values: values.clone(),
            ge,
            _p: PhantomData,
        };
        for (gates, x) in parts {
            for (v, l) in x.thresholds() {
                let mut cl: Vec<Lit> = gates.iter().map(|g| g.not()).collect();
                cl.push(l.not());
                cl.push(out.at_least(v));
                self.target.clause(&cl);
            }
        }
        let e = Expr::Max(parts.iter().map(|(g, x)| (g.clone(), x.id)).collect());
        self.make(out.values, out.ge, e)
    }

    /// The maximum, forced in both directions.
    pub fn max_of_exact(&mut self, parts: &[(Vec<Lit>, OInt<Exact>)]) -> OInt<Exact> {
        let up = self.max_of(parts);
        for (j, &v) in up.values.iter().enumerate().skip(1) {
            // At least `v` only if some active part is.
            let mut cl = vec![up.ge[j].not()];
            for (gates, x) in parts {
                let a = self.target.fresh();
                for &g in gates {
                    self.target.clause(&[a.not(), g]);
                }
                self.target.clause(&[a.not(), x.at_least(v)]);
                cl.push(a);
            }
            self.target.clause(&cl);
        }
        OInt {
            id: up.id,
            values: up.values,
            ge: up.ge,
            _p: PhantomData,
        }
    }

    /// The minimum over the parts whose gates all hold, or 0 when none does.
    pub fn min_of<P: Down>(&mut self, parts: &[(Vec<Lit>, OInt<P>)]) -> OInt<Under> {
        let values = sorted(
            std::iter::once(Cost::ZERO)
                .chain(parts.iter().flat_map(|(_, x)| x.values.iter().copied()))
                .collect(),
        );
        let ge = self.thermometer(&values);
        // Some active part, needed for the empty case: no active part means 0.
        let mut actives = Vec::new();
        for (gates, _) in parts {
            let a = self.target.fresh();
            for &g in gates {
                self.target.clause(&[a.not(), g]);
            }
            actives.push(a);
        }
        for j in 1..values.len() {
            let v = values[j];
            let mut any = vec![ge[j].not()];
            any.extend(actives.iter().copied());
            self.target.clause(&any);
            for (gates, x) in parts {
                // An active part below `v` keeps the minimum below `v`.
                let mut cl: Vec<Lit> = gates.iter().map(|g| g.not()).collect();
                cl.push(ge[j].not());
                cl.push(x.at_least(v));
                self.target.clause(&cl);
            }
        }
        let e = Expr::Min(parts.iter().map(|(g, x)| (g.clone(), x.id)).collect());
        self.make(values, ge, e)
    }

    /// The minimum, forced in both directions.
    ///
    /// Upward: the minimum is at least `v` when some part is active and every
    /// active part is at least `v`. As a clause: at least `v`, or no part active, or
    /// some active part below `v`. The two escape literals are pinned to what they
    /// claim, so neither can be set true to dodge the clause.
    pub fn min_of_exact(&mut self, parts: &[(Vec<Lit>, OInt<Exact>)]) -> OInt<Exact> {
        let down = self.min_of(parts);
        let none = self.target.fresh();
        for (gates, _) in parts {
            let mut cl = vec![none.not()];
            cl.extend(gates.iter().map(|g| g.not()));
            self.target.clause(&cl);
        }
        for (j, &v) in down.values.iter().enumerate().skip(1) {
            let mut cl = vec![down.ge[j], none];
            for (gates, x) in parts {
                let below = self.target.fresh();
                for &g in gates {
                    self.target.clause(&[below.not(), g]);
                }
                self.target.clause(&[below.not(), x.at_least(v).not()]);
                cl.push(below);
            }
            self.target.clause(&cl);
        }
        OInt {
            id: down.id,
            values: down.values,
            ge: down.ge,
            _p: PhantomData,
        }
    }

    /// The maximum over the parts whose gates all hold, or 0 when none does,
    /// forced downward: under-estimated when the parts are. The dual of
    /// [`Self::max_of`], which forces upward and needs over-estimates.
    pub fn max_of_down<P: Down>(&mut self, parts: &[(Vec<Lit>, OInt<P>)]) -> OInt<Under> {
        let values = sorted(
            std::iter::once(Cost::ZERO)
                .chain(parts.iter().flat_map(|(_, x)| x.values.iter().copied()))
                .collect(),
        );
        let ge = self.thermometer(&values);
        for (j, &v) in values.iter().enumerate().skip(1) {
            // At least `v` only if some active part is.
            let mut cl = vec![ge[j].not()];
            for (gates, x) in parts {
                let a = self.target.fresh();
                for &g in gates {
                    self.target.clause(&[a.not(), g]);
                }
                self.target.clause(&[a.not(), x.at_least(v)]);
                cl.push(a);
            }
            self.target.clause(&cl);
        }
        let e = Expr::Max(parts.iter().map(|(g, x)| (g.clone(), x.id)).collect());
        self.make(values, ge, e)
    }

    /// The minimum over the parts whose gates all hold, or 0 when none does,
    /// forced upward: over-estimated when the parts are. The dual of
    /// [`Self::min_of`].
    pub fn min_of_up<P: Up>(&mut self, parts: &[(Vec<Lit>, OInt<P>)]) -> OInt<Over> {
        let values = sorted(
            std::iter::once(Cost::ZERO)
                .chain(parts.iter().flat_map(|(_, x)| x.values.iter().copied()))
                .collect(),
        );
        let ge = self.thermometer(&values);
        // `none` holds only when no part is active: pinned so it cannot be set to
        // escape the clauses below.
        let none = self.target.fresh();
        for (gates, _) in parts {
            let mut cl = vec![none.not()];
            cl.extend(gates.iter().map(|g| g.not()));
            self.target.clause(&cl);
        }
        for (j, &v) in values.iter().enumerate().skip(1) {
            // Some part active and every active part at least `v` force at least `v`.
            let mut cl = vec![ge[j], none];
            for (gates, x) in parts {
                let below = self.target.fresh();
                for &g in gates {
                    self.target.clause(&[below.not(), g]);
                }
                self.target.clause(&[below.not(), x.at_least(v).not()]);
                cl.push(below);
            }
            self.target.clause(&cl);
        }
        let e = Expr::Min(parts.iter().map(|(g, x)| (g.clone(), x.id)).collect());
        self.make(values, ge, e)
    }

    /// `max(a − b, 0)`: over-estimated when `a` is and `b` is under-estimated.
    /// Pairwise over the breakpoints, or, where [`SumMethod::choose`] prefers it, a
    /// merge of `a`'s unit bits with the complements of `b`'s: those count
    /// `top(b) - b`, so the merged count is `a - b + top(b) - v0(a)`.
    pub fn clamp_sub<A: Up, B: Down>(&mut self, a: &OInt<A>, b: &OInt<B>) -> OInt<Over> {
        self.clamp_sub_by(a, b, SumMethod::Auto)
    }

    /// [`Self::clamp_sub`] by the given method.
    pub fn clamp_sub_by<A: Up, B: Down>(
        &mut self,
        a: &OInt<A>,
        b: &OInt<B>,
        method: SumMethod,
    ) -> OInt<Over> {
        let units = match method.resolve(a.values(), b.values()) {
            // A span past `MAX_UNARY` takes the pairwise encoding, which is exact too.
            SumMethod::Network => a.unary().and_then(|ua| Ok((ua, b.unary()?))).ok(),
            _ => None,
        };
        if let Some((ua, ub)) = units {
            let nb: Vec<Lit> = ub.iter().rev().map(|l| l.not()).collect();
            let c = self.merge(&ua, &nb, true, false);
            // The merged count is `m = (a - v0(a)) + (top(b) - b)`, so `a - b = m + s` with
            // `s = v0(a) - top(b)`, and `d >= k` iff `m >= k - s`. `d` is at least
            // `max(s, 0)`, whose threshold holds always, and each value above it to
            // `max(top(a) - v0(b), 0) = len(c) + s` is one merged bit.
            let s = a.values[0] - *b.values.last().unwrap();
            let start = s.max(Cost::ZERO);
            let mut values = vec![start];
            let mut ge = vec![Lit::True];
            let first = (start - s).to_u64().expect("start >= s") as usize;
            for (i, &l) in c.iter().enumerate().skip(first) {
                values.push(s + Cost::from(i + 1));
                ge.push(l);
            }
            return self.make(values, ge, Expr::ClampSub(a.id, b.id));
        }
        let values = sorted(
            std::iter::once(Cost::ZERO)
                .chain(
                    a.values
                        .iter()
                        .flat_map(|&av| b.values.iter().map(move |&bv| (av - bv).max(Cost::ZERO))),
                )
                .collect(),
        );
        let ge = self.thermometer(&values);
        let out: OInt<Over> = OInt {
            id: 0,
            values: values.clone(),
            ge,
            _p: PhantomData,
        };
        for (aj, &av) in a.values.iter().enumerate() {
            for (bj, &bv) in b.values.iter().enumerate() {
                if av <= bv {
                    continue;
                }
                // a ≥ av and b ≤ bv force at least av − bv.
                let mut cl = vec![a.ge[aj].not(), out.at_least(av - bv)];
                if let Some(&above) = b.ge.get(bj + 1) {
                    cl.push(above);
                }
                self.target.clause(&cl);
            }
        }
        let e = Expr::ClampSub(a.id, b.id);
        self.make(out.values, out.ge, e)
    }

    /// The sum of over-estimated integers, over-estimated.
    pub fn sum<P: Up>(&mut self, xs: &[OInt<P>]) -> OInt<Over> {
        let mut acc: OInt<Over> = {
            let c = self.constant(0);
            OInt {
                id: c.id,
                values: c.values,
                ge: c.ge,
                _p: PhantomData,
            }
        };
        for x in xs {
            let values = sorted(
                acc.values
                    .iter()
                    .flat_map(|&p| x.values.iter().map(move |&q| p + q))
                    .collect(),
            );
            let ge = self.thermometer(&values);
            let out: OInt<Over> = OInt {
                id: 0,
                values: values.clone(),
                ge,
                _p: PhantomData,
            };
            for (pj, &p) in acc.values.iter().enumerate() {
                for (qj, &q) in x.values.iter().enumerate() {
                    self.target
                        .clause(&[acc.ge[pj].not(), x.ge[qj].not(), out.at_least(p + q)]);
                }
            }
            let e = Expr::Sum(vec![acc.id, x.id]);
            acc = self.make(out.values, out.ge, e);
        }
        acc
    }

    /// `x` when `b`, else `y`, over-estimated. `b` must be an exact literal.
    pub fn ite<P: Up>(&mut self, b: Lit, x: &OInt<P>, y: &OInt<P>) -> OInt<Over> {
        let values = sorted(x.values.iter().chain(y.values.iter()).copied().collect());
        let ge = self.thermometer(&values);
        let out: OInt<Over> = OInt {
            id: 0,
            values: values.clone(),
            ge,
            _p: PhantomData,
        };
        for (v, l) in x.thresholds() {
            self.target.clause(&[b.not(), l.not(), out.at_least(v)]);
        }
        for (v, l) in y.thresholds() {
            self.target.clause(&[b, l.not(), out.at_least(v)]);
        }
        let e = Expr::Ite(b, x.id, y.id);
        self.make(out.values, out.ge, e)
    }

    /// `x` when `b`, else 0.
    pub fn when<P: Up>(&mut self, b: Lit, x: &OInt<P>) -> OInt<Over> {
        self.max_of(&[(vec![b], x.clone())])
    }

    /// `min(x, bound)`: the value set is truncated at `bound`, and a warning records
    /// it when anything was dropped. Sound for the saturated quantity, which is a
    /// different function from `x`.
    pub fn saturate<P: Polarity>(&mut self, x: &OInt<P>, bound: impl Into<Cost>) -> OInt<P> {
        let bound = bound.into();
        let dropped = x.values.iter().filter(|&&v| v > bound).count();
        if dropped > 0 {
            self.warn(Warning::DomainCapped { bound, dropped });
        }
        let keep = x.values.partition_point(|&v| v <= bound);
        let (mut values, mut ge) = (x.values[..keep].to_vec(), x.ge[..keep].to_vec());
        if dropped > 0 && values.last() != Some(&bound) {
            values.push(bound);
            ge.push(x.ge[keep]);
        }
        self.make(values, ge, Expr::Saturate(x.id, bound))
    }

    /// Require a literal.
    pub fn require(&mut self, l: Lit) {
        self.target.clause(&[l]);
    }

    /// A pseudo-Boolean constraint, lowered by the target. A coefficient the target
    /// cannot represent is a build error.
    pub fn pb<V: Into<Cost> + Copy>(&mut self, terms: &[(V, Lit)], cmp: Cmp, k: impl Into<Cost>) {
        let terms: Vec<(Cost, Lit)> = terms.iter().map(|&(a, l)| (a.into(), l)).collect();
        let r = self.target.pb(&terms, cmp, k.into());
        self.report(r);
    }

    /// `a ∧ b`, defined exactly.
    pub fn and(&mut self, a: Lit, b: Lit) -> Lit {
        let x = self.target.fresh();
        self.target.clause(&[x.not(), a]);
        self.target.clause(&[x.not(), b]);
        self.target.clause(&[a.not(), b.not(), x]);
        if let Lit::Var { var, .. } = x {
            self.rec.bool_defs.insert(var, BoolDef::And(a, b));
        }
        x
    }

    /// `a ∨ b`, defined exactly.
    pub fn or(&mut self, a: Lit, b: Lit) -> Lit {
        self.and(a.not(), b.not()).not()
    }

    /// Charge `x` to the objective. Over-estimated or exact only, so the objective
    /// is never understated.
    pub fn cost<P: Up>(&mut self, x: &OInt<P>) {
        self.rec.charged.push(x.id);
        let (base, terms) = x.linear();
        self.target.objective_base(base);
        let start = self.cnf().map(|c| c.objective.len());
        for (w, l) in terms {
            let r = self.target.objective(w, l);
            self.report(r);
        }
        if let Some(start) = start
            && let Some(c) = self
                .target
                .as_any_mut()
                .downcast_mut::<crate::extraction::target::CnfTarget>()
        {
            let end = c.objective.len();
            if end > start + 1 {
                c.blocks.push(start..end);
            }
        }
    }

    /// Charge `w >= 0` when `l` holds. A negative weight is an error: charge its
    /// negation's complement, or a `Pb` term, instead.
    pub fn cost_if(&mut self, l: Lit, w: impl Into<Cost>) {
        let w = w.into();
        if w.is_negative() {
            self.fail(format!("charge_if: the weight {w} is negative"));
            return;
        }
        self.rec.charged_if.push((l, w));
        let r = self.target.objective(w, l);
        self.report(r);
    }

    /// Charge `w` unconditionally.
    pub fn cost_base(&mut self, w: impl Into<Cost>) {
        let w = w.into();
        self.rec.charged_base += w;
        self.target.objective_base(w);
    }
}

impl Detached {
    /// The value of a literal: a definition of this builder, or the model.
    pub fn lit(&self, model: &dyn Fn(u32) -> bool, l: Lit) -> bool {
        match l {
            Lit::True => true,
            Lit::False => false,
            Lit::Var { var, sign } => {
                let v = match self.bool_defs.get(&var) {
                    Some(BoolDef::And(a, b)) => self.lit(model, *a) && self.lit(model, *b),
                    None => model(var),
                };
                v == sign
            }
        }
    }

    /// The recorded objective under a model and external values: what the term
    /// costs, whatever the encoding's slack. Computed exactly; `Err` when the cost is
    /// outside the build's width.
    pub fn objective_value(
        &self,
        model: &dyn Fn(u32) -> bool,
        external: &dyn Fn(usize) -> Cost,
    ) -> Result<Cost, String> {
        let mut memo = BTreeMap::new();
        let mut total = self.charged_base;
        for &id in &self.charged {
            total += self.eval_id(id, model, external, &mut memo);
        }
        for &(l, w) in &self.charged_if {
            if self.lit(model, l) {
                total += w;
            }
        }
        for t in &self.charged_pb {
            total += self.pb_value(t, model, external, &mut memo);
        }
        self.width.check("the cost", total)
    }

    fn pb_value(
        &self,
        t: &crate::extraction::pb::PbRec,
        model: &dyn Fn(u32) -> bool,
        external: &dyn Fn(usize) -> Cost,
        memo: &mut BTreeMap<ExprId, Cost>,
    ) -> Cost {
        let mut v = t.c;
        for &(k, l) in &t.lits {
            if self.lit(model, l) {
                v += k;
            }
        }
        for &(m, id) in &t.ints {
            v += m * self.eval_id(id, model, external, memo);
        }
        v
    }

    /// The true value of `x` under a model, with external slots given, computed
    /// exactly.
    pub fn eval<P: Polarity>(
        &self,
        x: &OInt<P>,
        model: &dyn Fn(u32) -> bool,
        external: &dyn Fn(usize) -> Cost,
    ) -> Cost {
        let mut memo = BTreeMap::new();
        self.eval_id(x.id, model, external, &mut memo)
    }

    pub(crate) fn eval_id(
        &self,
        id: ExprId,
        model: &dyn Fn(u32) -> bool,
        external: &dyn Fn(usize) -> Cost,
        memo: &mut BTreeMap<ExprId, Cost>,
    ) -> Cost {
        if let Some(&v) = memo.get(&id) {
            return v;
        }
        let active = |g: &Vec<Lit>| g.iter().all(|&l| self.lit(model, l));
        let v = match &self.exprs[id] {
            Expr::Const(c) => *c,
            Expr::Read { values, ge } => {
                let j = (0..ge.len())
                    .rev()
                    .find(|&j| self.lit(model, ge[j]))
                    .unwrap_or(0);
                values[j]
            }
            Expr::Shift(e, c) => self.eval_id(*e, model, external, memo) + *c,
            Expr::Max(parts) => parts
                .iter()
                .filter(|(g, _)| active(g))
                .map(|(_, e)| self.eval_id(*e, model, external, memo))
                .max()
                .unwrap_or(Cost::ZERO),
            Expr::Min(parts) => parts
                .iter()
                .filter(|(g, _)| active(g))
                .map(|(_, e)| self.eval_id(*e, model, external, memo))
                .min()
                .unwrap_or(Cost::ZERO),
            Expr::ClampSub(a, b) => {
                let (a, b) = (
                    self.eval_id(*a, model, external, memo),
                    self.eval_id(*b, model, external, memo),
                );
                (a - b).max(Cost::ZERO)
            }
            Expr::Sum(xs) => xs
                .iter()
                .map(|e| self.eval_id(*e, model, external, memo))
                .sum(),
            Expr::Ite(b, x, y) => {
                if self.lit(model, *b) {
                    self.eval_id(*x, model, external, memo)
                } else {
                    self.eval_id(*y, model, external, memo)
                }
            }
            Expr::Saturate(e, bound) => self.eval_id(*e, model, external, memo).min(*bound),
            Expr::Scale(e, c) => self.eval_id(*e, model, external, memo) * *c,
            Expr::Clamp(e, lo) => self.eval_id(*e, model, external, memo).max(*lo),
            Expr::Neg(e) => -self.eval_id(*e, model, external, memo),
            Expr::Pb(t) => self.pb_value(t, model, external, memo),
            Expr::External(slot) => external(*slot),
        };
        memo.insert(id, v);
        v
    }
}

/// The encoded value of `x` under a model: the largest value whose threshold holds.
pub fn encoded<P: Polarity>(x: &OInt<P>, model: &dyn Fn(u32) -> bool) -> Cost {
    let j = (0..x.ge.len())
        .rev()
        .find(|&j| lit_value(model, x.ge[j]))
        .unwrap_or(0);
    x.values[j]
}
