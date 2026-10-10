// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Pseudo-Boolean terms: `c + k1·l1 + ... + kn·ln + m1·x1 + ... + mp·xp` over
//! literals `li` and order-encoded integers `xj`, with signed coefficients.
//!
//! Adding, subtracting, negating, and scaling a term emit nothing. A term is written
//! to a target only when it is charged, compared, or sorted into an integer. An
//! integer part is kept as a reference, not as its threshold literals, so the
//! interpreted value reads the integer's true value on the term rather than its
//! thresholds in the model, which carry the encoding's slack.
//!
//! The polarity is the term's: `Pb<Over>` never has an encoded value below its
//! true value. Negation exchanges `Over` and `Under` (`Polarity::Flip`), so
//! `t.minus(u)` takes a `u` of the flipped polarity, and subtracting an
//! over-estimate from an over-estimate does not type-check.

use crate::extraction::Lit;
use crate::extraction::cost::Cost;
use crate::extraction::oint::{Build, Exact, Expr, ExprId, OInt, Over, Polarity, Under};
use std::marker::PhantomData;

/// An integer as a term part: its expression and its breakpoints.
#[derive(Clone, Debug)]
pub(crate) struct IntRef {
    pub(crate) id: ExprId,
    pub(crate) values: Vec<Cost>,
    pub(crate) ge: Vec<Lit>,
}

/// A term as the interpreter evaluates it.
#[derive(Clone, Debug)]
pub(crate) struct PbRec {
    pub(crate) c: Cost,
    pub(crate) lits: Vec<(Cost, Lit)>,
    pub(crate) ints: Vec<(Cost, ExprId)>,
}

/// A pseudo-Boolean term of polarity `P`.
#[derive(Clone, Debug)]
pub struct Pb<P: Polarity> {
    c: Cost,
    lits: Vec<(Cost, Lit)>,
    ints: Vec<(Cost, IntRef)>,
    _p: PhantomData<P>,
}

impl<P: Polarity> Pb<P> {
    /// The constant `c`. A term's arithmetic is exact; the width applies where the
    /// term becomes an integer ([`Build::sorted`]) or a cost.
    pub fn constant(c: impl Into<Cost>) -> Self {
        Pb {
            c: c.into(),
            lits: Vec::new(),
            ints: Vec::new(),
            _p: PhantomData,
        }
    }

    /// `k·l`, where `l` is a literal of polarity `P`: exactly its truth, or one that
    /// may be spuriously true (`Over`) or spuriously false (`Under`).
    pub fn lit(l: Lit, k: impl Into<Cost>) -> Self {
        Pb {
            c: Cost::ZERO,
            lits: vec![(k.into(), l)],
            ints: Vec::new(),
            _p: PhantomData,
        }
    }

    /// `x` as a term of the same polarity.
    pub fn of(x: &OInt<P>) -> Self {
        let r = IntRef {
            id: x.id,
            values: x.values().to_vec(),
            ge: x.thresholds().map(|(_, l)| l).collect(),
        };
        Pb {
            c: Cost::ZERO,
            lits: Vec::new(),
            ints: vec![(Cost::ONE, r)],
            _p: PhantomData,
        }
    }

    pub fn plus(&self, o: &Pb<P>) -> Pb<P> {
        let mut t = self.clone();
        t.c += o.c;
        t.lits.extend(o.lits.iter().copied());
        t.ints.extend(o.ints.iter().cloned());
        t
    }

    /// `-self`: an over-estimate negated is an under-estimate.
    pub fn neg(&self) -> Pb<P::Flip> {
        Pb {
            c: -self.c,
            lits: self.lits.iter().map(|&(k, l)| (-k, l)).collect(),
            ints: self.ints.iter().map(|(m, r)| (-*m, r.clone())).collect(),
            _p: PhantomData,
        }
    }

    /// `self - o`, which is `self + (-o)`: `o` has the flipped polarity.
    pub fn minus(&self, o: &Pb<P::Flip>) -> Pb<P>
    where
        P::Flip: Polarity<Flip = P>,
    {
        self.plus(&o.neg())
    }

    /// `c·self` for `c >= 0`. A negative `c` would flip the polarity, so it is the
    /// caller's to rule out (the Roto binding takes only unsigned factors).
    pub fn times(&self, c: impl Into<Cost>) -> Pb<P> {
        let c = c.into();
        debug_assert!(!c.is_negative(), "a Pb factor is at least 0");
        Pb {
            c: self.c * c,
            lits: self.lits.iter().map(|&(k, l)| (k * c, l)).collect(),
            ints: self.ints.iter().map(|(m, r)| (*m * c, r.clone())).collect(),
            _p: PhantomData,
        }
    }

    pub fn plus_const(&self, k: impl Into<Cost>) -> Pb<P> {
        let mut t = self.clone();
        t.c += k.into();
        t
    }

    /// The least and greatest values the term can take, each literal and each
    /// integer taken independently.
    pub fn bounds(&self) -> (Cost, Cost) {
        let (mut lo, mut hi) = (self.c, self.c);
        for &(k, _) in &self.lits {
            if k < 0 {
                lo += k;
            } else {
                hi += k;
            }
        }
        for (m, r) in &self.ints {
            let (a, b) = (
                *r.values.first().unwrap() * *m,
                *r.values.last().unwrap() * *m,
            );
            lo += a.min(b);
            hi += a.max(b);
        }
        (lo, hi)
    }

    /// The term as `base + sum w·l` with every `w > 0`: a negative `k·l` is written
    /// `k + (-k)·not l`, and an integer part as its thresholds. `base` is the least
    /// value of [`Self::bounds`].
    pub(crate) fn normalized(&self) -> (Cost, Vec<(Cost, Lit)>) {
        let mut base = self.c;
        let mut out = Vec::new();
        let mut add = |k: Cost, l: Lit, base: &mut Cost| {
            if k > 0 {
                out.push((k, l));
            } else if k < 0 {
                *base += k;
                out.push((-k, l.not()));
            }
        };
        for &(k, l) in &self.lits {
            add(k, l, &mut base);
        }
        for (m, r) in &self.ints {
            base += *m * r.values[0];
            for j in 1..r.values.len() {
                add(*m * (r.values[j] - r.values[j - 1]), r.ge[j], &mut base);
            }
        }
        (
            base,
            out.into_iter().filter(|&(_, l)| l != Lit::False).collect(),
        )
    }

    /// The parts as sorted blocks, `base` aside: each literal a block `{0, w}`, each
    /// integer its own breakpoints less its least (reversed and complemented where its
    /// coefficient is negative), for [`Build::sorted`].
    fn blocks(&self) -> (Cost, Vec<(Vec<Cost>, Vec<Lit>)>) {
        let mut base = self.c;
        let mut out = Vec::new();
        for &(k, l) in &self.lits {
            if k > 0 {
                out.push((vec![Cost::ZERO, k], vec![Lit::True, l]));
            } else if k < 0 {
                base += k;
                out.push((vec![Cost::ZERO, -k], vec![Lit::True, l.not()]));
            }
        }
        for &(m, ref r) in &self.ints {
            let n = r.values.len();
            if m > 0 {
                base += m * r.values[0];
                out.push((
                    r.values.iter().map(|&v| m * (v - r.values[0])).collect(),
                    r.ge.clone(),
                ));
            } else if m < 0 {
                // m·x = m·top + (-m)·(top - x), and `top - x >= top - v(j)` is
                // `not [x >= v(j+1)]`.
                let m = -m;
                let top = r.values[n - 1];
                base -= m * top;
                let values: Vec<Cost> = (0..n).map(|j| m * (top - r.values[n - 1 - j])).collect();
                let ge: Vec<Lit> = (0..n)
                    .map(|j| if j == 0 { Lit::True } else { r.ge[n - j].not() })
                    .collect();
                out.push((values, ge));
            }
        }
        (base, out)
    }

    pub(crate) fn rec(&self) -> PbRec {
        PbRec {
            c: self.c,
            lits: self.lits.clone(),
            ints: self.ints.iter().map(|(m, r)| (*m, r.id)).collect(),
        }
    }
}

impl Pb<Exact> {
    pub fn over(self) -> Pb<Over> {
        Pb {
            c: self.c,
            lits: self.lits,
            ints: self.ints,
            _p: PhantomData,
        }
    }
    pub fn under(self) -> Pb<Under> {
        Pb {
            c: self.c,
            lits: self.lits,
            ints: self.ints,
            _p: PhantomData,
        }
    }
}

impl<'t> Build<'t> {
    /// Add `t` to the objective. Negative weights are normalized into the base,
    /// which is then `t`'s least value, possibly negative.
    pub fn charge_pb<P: crate::extraction::oint::Up>(&mut self, t: &Pb<P>) -> Result<(), String> {
        let (base, terms) = t.normalized();
        debug_assert_eq!(base, t.bounds().0);
        self.target.objective_base(base);
        for (w, l) in terms {
            self.target.objective(w, l)?;
        }
        self.rec.charged_pb.push(t.rec());
        Ok(())
    }

    /// A literal for `t >= k`. `P::UP` makes it hold whenever the encoded term reaches
    /// `k` (so it may be spuriously true for an over-estimate); `P::DOWN` makes it
    /// hold only when the encoded term reaches `k`; an exact term gets both.
    pub fn pb_at_least<P: Polarity>(&mut self, t: &Pb<P>, k: impl Into<Cost>) -> Lit {
        let (base, terms) = t.normalized();
        let kk = k.into() - base;
        let smax: Cost = terms.iter().map(|&(w, _)| w).sum();
        if kk <= 0 {
            return Lit::True;
        }
        if kk > smax {
            return Lit::False;
        }
        let l = self.target.fresh();
        let mut sum: Vec<(Cost, Lit)> = terms;
        if P::DOWN {
            // l -> S >= kk, as S + kk·not l >= kk.
            sum.push((kk, l.not()));
            let r = self.target.pb(&sum, crate::extraction::target::Cmp::Ge, kk);
            self.report(r);
            sum.pop();
        }
        if P::UP {
            // S >= kk -> l, as S - (smax - kk + 1)·l <= kk - 1.
            sum.push((-(smax - kk + Cost::ONE), l));
            let r = self
                .target
                .pb(&sum, crate::extraction::target::Cmp::Le, kk - Cost::ONE);
            self.report(r);
        }
        l
    }

    /// `t` as an order-encoded integer of the same polarity: a balanced pairwise sum
    /// of its parts as sorted blocks, each integer part one block, with the upward
    /// clauses for an over-estimate, the downward ones for an under-estimate, and both
    /// for an exact term.
    pub fn sorted<P: Polarity>(&mut self, t: &Pb<P>) -> Result<OInt<P>, String> {
        let (base, blocks) = t.blocks();
        let (values, ge) = if blocks.is_empty() {
            (vec![Cost::ZERO], vec![Lit::True])
        } else {
            self.sum_blocks(blocks, P::UP, P::DOWN)
        };
        let values = values.into_iter().map(|v| v + base).collect();
        Ok(self.make_pub(values, ge, Expr::Pb(t.rec())))
    }

    /// The pairwise sum of sorted blocks, as a balanced tree.
    pub(crate) fn sum_blocks(
        &mut self,
        mut blocks: Vec<(Vec<Cost>, Vec<Lit>)>,
        up: bool,
        down: bool,
    ) -> (Vec<Cost>, Vec<Lit>) {
        while blocks.len() > 1 {
            let mut next = Vec::with_capacity(blocks.len().div_ceil(2));
            let mut it = blocks.into_iter();
            while let Some(a) = it.next() {
                match it.next() {
                    Some(b) => next.push(self.sum2(&a, &b, up, down)),
                    None => next.push(a),
                }
            }
            blocks = next;
        }
        blocks.pop().unwrap()
    }

    fn sum2(
        &mut self,
        a: &(Vec<Cost>, Vec<Lit>),
        b: &(Vec<Cost>, Vec<Lit>),
        up: bool,
        down: bool,
    ) -> (Vec<Cost>, Vec<Lit>) {
        let mut values: Vec<Cost> = Vec::with_capacity(a.0.len() * b.0.len());
        for &p in &a.0 {
            for &q in &b.0 {
                values.push(p + q);
            }
        }
        values.sort_unstable();
        values.dedup();
        let ge = self.thermometer_pub(&values);
        let at = |v: Cost| -> Lit {
            let j = values.partition_point(|&x| x < v);
            ge.get(j).copied().unwrap_or(Lit::False)
        };
        for (i, &p) in a.0.iter().enumerate() {
            for (j, &q) in b.0.iter().enumerate() {
                if up {
                    // [a >= p] and [b >= q] -> [s >= p + q].
                    self.target.clause(&[a.1[i].not(), b.1[j].not(), at(p + q)]);
                }
                if down {
                    // a < next(p) and b < next(q) -> s <= p + q.
                    let mut cl = vec![at(p + q + Cost::ONE).not()];
                    if let Some(&l) = a.1.get(i + 1) {
                        cl.push(l);
                    }
                    if let Some(&l) = b.1.get(j + 1) {
                        cl.push(l);
                    }
                    self.target.clause(&cl);
                }
            }
        }
        (values, ge)
    }
}
