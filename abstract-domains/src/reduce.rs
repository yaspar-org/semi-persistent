// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Reduction through a shared channel of facts, after Verasco's communication
//! channels (Jourdan et al., POPL 2015, §7).
//!
//! Domains do not reduce against each other pairwise. Each domain writes what
//! it knows into a fact record (`Channel`), the records are met exactly and
//! normalized, and each domain refines itself by the result (`Refine`).
//! `Product<A, B>` runs these rounds; `reduce` proves that a round changes the
//! representation and never the concretization. See doc/reduced-product.md.
// Proof-only bindings are erased outside Verus.
#![allow(unused_variables)]
use crate::bool4::*;
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::*;
use vstd::prelude::*;

verus! {

/// Reduction rounds that `Product` runs after a meet or a transfer. Fuel bounds
/// the work; it affects precision, never soundness.
pub const REDUCE_FUEL: u8 = 3;

/// A fact record: the record that domains write to and refine from.
///
/// A record is a product of fields. `pre_wf` says each field is well formed;
/// `wf` adds that the fields are mutually reduced, which `normalize` establishes.
/// Because `wf` is canonical, `==` on normalized records is set equality.
pub trait Channel: Canonical {
    /// Each field is well formed; the fields need not agree with each other.
    spec fn pre_wf(&self) -> bool;

    proof fn lemma_wf_pre(&self)
        requires
            self.wf(),
        ensures
            self.pre_wf(),
    ;

    /// Field-wise intersection, exact in both directions. The result is
    /// `pre_wf`; `normalize` makes it `wf`.
    fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>)
        requires
            self.wf(),
            o.wf(),
        ensures
            match r {
                BotOr::Bot => forall|c: Self::C| #[trigger] self.gamma(c) ==> !o.gamma(c),
                BotOr::Val(m) => m.pre_wf() && forall|c: Self::C| #[trigger]
                    m.gamma(c) == (self.gamma(c) && o.gamma(c)),
            },
    ;

    /// Propagates information between fields without changing the meaning:
    /// `Bot` only when the record denotes the empty set.
    fn normalize(&self) -> (r: BotOr<Self>)
        requires
            self.pre_wf(),
        ensures
            r.wf(),
            forall|c: Self::C| #[trigger] r.gamma(c) == self.gamma(c),
    ;
}

/// A domain that writes its facts to channel `F` and refines itself from it.
pub trait Refine: Domain {
    type F: Channel<C = Self::C>;

    /// Facts implied by `self`; `Bot` only when `self` is empty. A product
    /// returns `Bot` when its components contradict each other, which is how an
    /// outer round learns that a nested product is empty.
    fn to_channel(&self) -> (f: BotOr<Self::F>)
        requires
            self.wf(),
        ensures
            f.wf(),
            forall|x: Self::C| self.gamma(x) ==> #[trigger] f.gamma(x),
    ;

    /// `self` strengthened by `f`: keeps every value of `self` that `f` accepts,
    /// adds none.
    fn refine(&self, f: &Self::F) -> (r: BotOr<Self>)
        requires
            self.wf(),
            f.wf(),
        ensures
            r.wf(),
            forall|x: Self::C| self.gamma(x) && f.gamma(x) ==> #[trigger] r.gamma(x),
            forall|x: Self::C| #[trigger] r.gamma(x) ==> self.gamma(x),
    ;
}

/// Exact meet followed by normalization: the reduced intersection of two records.
pub fn meet_normalize<F: Channel>(f: &F, g: &F) -> (r: BotOr<F>)
    requires
        f.wf(),
        g.wf(),
    ensures
        r.wf(),
        forall|c: F::C| #[trigger] r.gamma(c) == (f.gamma(c) && g.gamma(c)),
{
    match f.meet_exact(g) {
        BotOr::Bot => BotOr::Bot,
        BotOr::Val(m) => m.normalize(),
    }
}

/// `meet_normalize` lifted to records that may be `Bot`.
pub fn meet_channels<F: Channel>(f: BotOr<F>, g: BotOr<F>) -> (r: BotOr<F>)
    requires
        f.wf(),
        g.wf(),
    ensures
        r.wf(),
        forall|c: F::C| #[trigger] r.gamma(c) == (f.gamma(c) && g.gamma(c)),
{
    match (f, g) {
        (BotOr::Val(f1), BotOr::Val(g1)) => meet_normalize(&f1, &g1),
        _ => BotOr::Bot,
    }
}

/// `γ = γ(a) ∩ γ(b)`. The components share channel `A::F`.
///
/// A product is `Domain` and `Refine`, so products nest, but not `Canonical`:
/// when the channel cannot express what a component knows, the components can
/// be jointly empty or carry redundant information that no round removes.
pub struct Product<A, B> {
    pub a: A,
    pub b: B,
}

impl<A, B> Product<A, B> where A: Refine, B: Refine<C = A::C, F = A::F> {
    /// One reduction round: `f = normalize(a.to_channel() ⊓ b.to_channel())`, then each
    /// component refines by `f`.
    pub fn reduce_once(&self) -> (r: BotOr<Self>)
        requires
            self.wf(),
        ensures
            r.wf(),
            forall|c: A::C| #[trigger] r.gamma(c) == self.gamma(c),
    {
        let ea = self.a.to_channel();
        let eb = self.b.to_channel();
        let m = meet_channels(ea, eb);
        let f = match m {
            BotOr::Bot => {
                proof {
                    assert forall|c: A::C| #[trigger] self.gamma(c) implies false by {
                        assert(ea.gamma(c) && eb.gamma(c));
                        assert(m.gamma(c));
                    }
                }
                return BotOr::Bot;
            },
            BotOr::Val(f) => f,
        };
        proof {
            assert forall|c: A::C| #[trigger] self.gamma(c) implies f.gamma(c) by {
                assert(ea.gamma(c) && eb.gamma(c));
                assert(m.gamma(c));
            }
        }
        let a2 = self.a.refine(&f);
        let b2 = self.b.refine(&f);
        match (a2, b2) {
            (BotOr::Val(a2), BotOr::Val(b2)) => {
                let r = Product { a: a2, b: b2 };
                proof {
                    assert forall|c: A::C| #[trigger] r.gamma(c) == self.gamma(c) by {
                        if self.gamma(c) {
                            assert(f.gamma(c));
                            assert(BotOr::<A>::Val(a2).gamma(c));
                            assert(BotOr::<B>::Val(b2).gamma(c));
                        }
                        if r.gamma(c) {
                            assert(BotOr::<A>::Val(a2).gamma(c));
                            assert(BotOr::<B>::Val(b2).gamma(c));
                        }
                    }
                }
                BotOr::Val(r)
            },
            (a2, b2) => {
                proof {
                    assert forall|c: A::C| #[trigger] self.gamma(c) implies false by {
                        assert(f.gamma(c));
                        assert(a2.gamma(c) && b2.gamma(c));
                    }
                }
                BotOr::Bot
            },
        }
    }

    /// Up to `fuel` rounds, stopping early when a round leaves both components'
    /// concretizations unchanged. The theorem is the contract: for every fuel,
    /// reduction preserves the concretization exactly, and `Bot` means empty.
    pub fn reduce(&self, fuel: u8) -> (r: BotOr<Self>)
        requires
            self.wf(),
        ensures
            r.wf(),
            forall|c: A::C| #[trigger] r.gamma(c) == self.gamma(c),
        decreases fuel,
    {
        if fuel == 0 {
            return BotOr::Val(self.dup());
        }
        match self.reduce_once() {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(p) => {
                if self.a.leq(&p.a) && self.b.leq(&p.b) {
                    BotOr::Val(p)
                } else {
                    let r = p.reduce(fuel - 1);
                    proof {
                        assert forall|c: A::C| #[trigger] r.gamma(c) == self.gamma(c) by {
                            assert(r.gamma(c) == p.gamma(c));
                            assert(BotOr::<Self>::Val(p).gamma(c) == self.gamma(c));
                        }
                    }
                    r
                }
            },
        }
    }

    /// Meet followed by `fuel` reduction rounds: the e-class merge.
    pub fn meet_reduce(&self, o: &Self, fuel: u8) -> (r: BotOr<Self>)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: A::C| #[trigger] r.gamma(c) <== self.gamma(c) && o.gamma(c),
    {
        match self.meet(o) {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(m) => {
                let r = m.reduce(fuel);
                proof {
                    assert forall|c: A::C| self.gamma(c) && o.gamma(c) implies #[trigger] r.gamma(
                        c,
                    ) by {
                        assert(BotOr::<Self>::Val(m).gamma(c));
                    }
                }
                r
            },
        }
    }

}

impl<A, B> Domain for Product<A, B> where A: Refine, B: Refine<C = A::C, F = A::F> {
    type C = A::C;

    open spec fn wf(&self) -> bool {
        self.a.wf() && self.b.wf()
    }

    open spec fn gamma(&self, c: A::C) -> bool {
        self.a.gamma(c) && self.b.gamma(c)
    }

    fn dup(&self) -> (r: Self) {
        Product { a: self.a.dup(), b: self.b.dup() }
    }

    fn top() -> (r: Self) {
        Product { a: A::top(), b: B::top() }
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        self.a.leq(&o.a) && self.b.leq(&o.b)
    }

    fn join(&self, o: &Self) -> (r: Self) {
        Product { a: self.a.join(&o.a), b: self.b.join(&o.b) }
    }

    /// Componentwise meet, unreduced. Calling `reduce` here would make this
    /// impl depend on a function whose contract mentions it (a Verus cycle);
    /// `meet_reduce` is the reduced version.
    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        match (self.a.meet(&o.a), self.b.meet(&o.b)) {
            (BotOr::Val(a), BotOr::Val(b)) => {
                let r = Product { a, b };
                proof {
                    assert forall|c: A::C| self.gamma(c) && o.gamma(c) implies #[trigger] r.gamma(
                        c,
                    ) by {
                        assert(BotOr::<A>::Val(a).gamma(c));
                        assert(BotOr::<B>::Val(b).gamma(c));
                    }
                }
                BotOr::Val(r)
            },
            (ma, mb) => {
                proof {
                    assert forall|c: A::C| #[trigger] self.gamma(c) implies !o.gamma(c) by {
                        if o.gamma(c) {
                            assert(ma.gamma(c) && mb.gamma(c));
                        }
                    }
                }
                BotOr::Bot
            },
        }
    }

    /// Componentwise widening, without reduction: reducing a widened value can
    /// undo the widening and break stabilization.
    fn widen(&self, o: &Self) -> (r: Self) {
        Product { a: self.a.widen(&o.a), b: self.b.widen(&o.b) }
    }
}

impl<A, B> Refine for Product<A, B> where A: Refine, B: Refine<C = A::C, F = A::F> {
    type F = A::F;

    /// The reduced meet of the components' records; `Bot` when they contradict.
    fn to_channel(&self) -> (f: BotOr<A::F>) {
        let ea = self.a.to_channel();
        let eb = self.b.to_channel();
        let f = meet_channels(ea, eb);
        proof {
            assert forall|x: A::C| self.gamma(x) implies #[trigger] f.gamma(x) by {
                assert(ea.gamma(x) && eb.gamma(x));
            }
        }
        f
    }

    /// Componentwise. The caller's record already contains this product's own
    /// record (an outer round meets every leaf's record before refining), so
    /// recomputing it here would only repeat work.
    fn refine(&self, f: &A::F) -> (r: BotOr<Self>) {
        match (self.a.refine(f), self.b.refine(f)) {
            (BotOr::Val(a), BotOr::Val(b)) => {
                let r = Product { a, b };
                proof {
                    assert forall|x: A::C| self.gamma(x) && f.gamma(x) implies #[trigger] r.gamma(
                        x,
                    ) by {
                        assert(BotOr::<A>::Val(a).gamma(x));
                        assert(BotOr::<B>::Val(b).gamma(x));
                    }
                    assert forall|x: A::C| #[trigger] r.gamma(x) implies self.gamma(x) by {
                        assert(BotOr::<A>::Val(a).gamma(x));
                        assert(BotOr::<B>::Val(b).gamma(x));
                    }
                }
                BotOr::Val(r)
            },
            (ra, rb) => {
                proof {
                    assert forall|x: A::C| #[trigger] self.gamma(x) && f.gamma(x) implies false by {
                        assert(ra.gamma(x) && rb.gamma(x));
                    }
                }
                BotOr::Bot
            },
        }
    }
}

impl<S, A, B> Arith<S> for Product<A, B> where
    S: Semantics,
    A: Arith<S> + Refine,
    B: Arith<S> + Refine<C = A::C, F = A::F>,
 {
    /// Componentwise; the caller reduces once at the root.
    fn add(&self, o: &Self) -> (r: Self) {
        Product { a: self.a.add(&o.a), b: self.b.add(&o.b) }
    }

    /// Componentwise; the caller reduces once at the root.
    fn sub(&self, o: &Self) -> (r: Self) {
        Product { a: self.a.sub(&o.a), b: self.b.sub(&o.b) }
    }

    /// Componentwise; the caller reduces once at the root.
    fn neg(&self) -> (r: Self) {
        Product { a: self.a.neg(), b: self.b.neg() }
    }
}

impl<S, A, B> Mul<S> for Product<A, B> where
    S: Semantics,
    A: Mul<S> + Refine,
    B: Mul<S> + Refine<C = A::C, F = A::F>,
 {
    /// Componentwise; the caller reduces once at the root.
    fn mul(&self, o: &Self) -> (r: Self) {
        Product { a: self.a.mul(&o.a), b: self.b.mul(&o.b) }
    }
}

/// Combines the components' division-by-zero flags. A component that proves
/// the divisor excludes 0 (`Never`) or is `{0}` (`Always`) proves it for the
/// product; if one says `Never` and the other `Always`, the divisor is empty
/// and `Always` is sound.
fn combine_div<S, A, B>(qa: BotOr<A>, fa: DivZero, qb: BotOr<B>, fb: DivZero) -> (r: (
    BotOr<Product<A, B>>,
    DivZero,
)) where
    S: Semantics,
    A: DivRem<S> + Refine,
    B: DivRem<S> + Refine<C = A::C, F = A::F>,

    requires
        qa.wf(),
        qb.wf(),
        (qa is Bot) <==> (fa is Always),
        (qb is Bot) <==> (fb is Always),
    ensures
        r.0.wf(),
        forall|c: A::C| qa.gamma(c) && qb.gamma(c) ==> #[trigger] r.0.gamma(c),
        r.1 is Never ==> (fa is Never || fb is Never),
        r.1 is Always ==> (fa is Always || fb is Always),
        (r.0 is Bot) <==> (r.1 is Always),
{
    match (qa, qb) {
        (BotOr::Val(a), BotOr::Val(b)) => {
            let r = Product { a, b };
            let flag = match (fa, fb) {
                (DivZero::Never, _) | (_, DivZero::Never) => DivZero::Never,
                _ => DivZero::Maybe,
            };
            proof {
                assert forall|c: A::C| qa.gamma(c) && qb.gamma(c) implies #[trigger] BotOr::<
                    Product<A, B>,
                >::Val(r).gamma(c) by {
                    assert(r.gamma(c));
                }
            }
            (BotOr::Val(r), flag)
        },
        _ => (BotOr::Bot, DivZero::Always),
    }
}

impl<S, A, B> DivRem<S> for Product<A, B> where
    S: Semantics,
    A: DivRem<S> + Refine,
    B: DivRem<S> + Refine<C = A::C, F = A::F>,
 {
    fn contains_zero(&self) -> (b: bool) {
        self.a.contains_zero() && self.b.contains_zero()
    }

    /// Componentwise, then reduced; flags combined by `combine_div`.
    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (qa, fa) = self.a.div(&d.a);
        let (qb, fb) = self.b.div(&d.b);
        let r = combine_div::<S, A, B>(qa, fa, qb, fb);
        proof {
            assert forall|x: S::V, y: S::V|
                self.gamma(x) && d.gamma(y) && !S::is_zero(y) implies #[trigger] r.0.gamma(
                S::div(x, y),
            ) by {
                assert(qa.gamma(S::div(x, y)) && qb.gamma(S::div(x, y)));
            }
            if r.1 is Always {
                assert forall|y: S::V| #[trigger] d.gamma(y) implies S::is_zero(y) by {
                    assert(d.a.gamma(y) && d.b.gamma(y));
                }
            }
        }
        r
    }

    /// Componentwise, then reduced; flags combined by `combine_div`.
    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (qa, fa) = self.a.rem(&d.a);
        let (qb, fb) = self.b.rem(&d.b);
        let r = combine_div::<S, A, B>(qa, fa, qb, fb);
        proof {
            assert forall|x: S::V, y: S::V|
                self.gamma(x) && d.gamma(y) && !S::is_zero(y) implies #[trigger] r.0.gamma(
                S::rem(x, y),
            ) by {
                assert(qa.gamma(S::rem(x, y)) && qb.gamma(S::rem(x, y)));
            }
            if r.1 is Always {
                assert forall|y: S::V| #[trigger] d.gamma(y) implies S::is_zero(y) by {
                    assert(d.a.gamma(y) && d.b.gamma(y));
                }
            }
        }
        r
    }
}

/// The meet of two components' answers; `Top` when they disagree, which
/// happens only when the operands are empty.
fn meet_answer(ra: Bool4, rb: Bool4) -> (r: Bool4)
    ensures
        forall|z: bool| ra.gamma(z) && rb.gamma(z) ==> #[trigger] r.gamma(z),
{
    match ra.meet(&rb) {
        BotOr::Val(m) => {
            proof {
                assert forall|z: bool| ra.gamma(z) && rb.gamma(z) implies #[trigger] m.gamma(z) by {
                    assert(BotOr::<Bool4>::Val(m).gamma(z));
                }
            }
            m
        },
        BotOr::Bot => Bool4::Top,
    }
}

/// Pairs two refined components; the caller reduces once at the root.
fn pair_reduce<A, B>(x: BotOr<A>, y: BotOr<B>) -> (r: BotOr<Product<A, B>>) where
    A: Refine,
    B: Refine<C = A::C, F = A::F>,

    requires
        x.wf(),
        y.wf(),
    ensures
        r.wf(),
        forall|c: A::C| #[trigger] r.gamma(c) == (x.gamma(c) && y.gamma(c)),
{
    match (x, y) {
        (BotOr::Val(a), BotOr::Val(b)) => {
            let r = BotOr::Val(Product { a, b });
            proof {
                assert forall|c: A::C| #[trigger] r.gamma(c) == (x.gamma(c) && y.gamma(c)) by {
                    assert(BotOr::<A>::Val(a).gamma(c) == a.gamma(c));
                    assert(BotOr::<B>::Val(b).gamma(c) == b.gamma(c));
                }
            }
            r
        },
        _ => BotOr::Bot,
    }
}

impl<S, A, B> Compare<S> for Product<A, B> where
    S: Semantics,
    A: Compare<S> + Refine,
    B: Compare<S> + Refine<C = A::C, F = A::F>,
 {
    /// Componentwise; the answers are met.
    fn lt(&self, o: &Self) -> (r: Bool4) {
        let ra = self.a.lt(&o.a);
        let rb = self.b.lt(&o.b);
        let r = meet_answer(ra, rb);
        proof {
            assert forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) implies r.gamma(S::lt(x, y)) by {
                assert(ra.gamma(S::lt(x, y)) && rb.gamma(S::lt(x, y)));
            }
        }
        r
    }

    /// Componentwise; the answers are met.
    fn le(&self, o: &Self) -> (r: Bool4) {
        let ra = self.a.le(&o.a);
        let rb = self.b.le(&o.b);
        let r = meet_answer(ra, rb);
        proof {
            assert forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) implies r.gamma(S::le(x, y)) by {
                assert(ra.gamma(S::le(x, y)) && rb.gamma(S::le(x, y)));
            }
        }
        r
    }

    /// Componentwise; the answers are met.
    fn eq(&self, o: &Self) -> (r: Bool4) {
        let ra = self.a.eq(&o.a);
        let rb = self.b.eq(&o.b);
        let r = meet_answer(ra, rb);
        proof {
            assert forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) implies r.gamma(x == y) by {
                assert(ra.gamma(x == y) && rb.gamma(x == y));
            }
        }
        r
    }

    /// Componentwise, then each side reduced.
    fn assume_lt(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        let (a0, a1) = self.a.assume_lt(&o.a, t);
        let (b0, b1) = self.b.assume_lt(&o.b, t);
        let r = (pair_reduce(a0, b0), pair_reduce(a1, b1));
        proof {
            assert forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) && S::lt(x, y) == t implies r.0.gamma(x) && r.1.gamma(y) by {
                assert(self.a.gamma(x) && o.a.gamma(y));
                assert(self.b.gamma(x) && o.b.gamma(y));
                assert(a0.gamma(x) && a1.gamma(y) && b0.gamma(x) && b1.gamma(y));
            }
            assert forall|x: S::V| #[trigger] r.0.gamma(x) implies self.gamma(x) by {
                assert(a0.gamma(x) && b0.gamma(x));
            }
            assert forall|y: S::V| #[trigger] r.1.gamma(y) implies o.gamma(y) by {
                assert(a1.gamma(y) && b1.gamma(y));
            }
        }
        r
    }

    /// Componentwise, then each side reduced.
    fn assume_le(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        let (a0, a1) = self.a.assume_le(&o.a, t);
        let (b0, b1) = self.b.assume_le(&o.b, t);
        let r = (pair_reduce(a0, b0), pair_reduce(a1, b1));
        proof {
            assert forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) && S::le(x, y) == t implies r.0.gamma(x) && r.1.gamma(y) by {
                assert(self.a.gamma(x) && o.a.gamma(y));
                assert(self.b.gamma(x) && o.b.gamma(y));
                assert(a0.gamma(x) && a1.gamma(y) && b0.gamma(x) && b1.gamma(y));
            }
            assert forall|x: S::V| #[trigger] r.0.gamma(x) implies self.gamma(x) by {
                assert(a0.gamma(x) && b0.gamma(x));
            }
            assert forall|y: S::V| #[trigger] r.1.gamma(y) implies o.gamma(y) by {
                assert(a1.gamma(y) && b1.gamma(y));
            }
        }
        r
    }

    /// Componentwise, then each side reduced.
    fn assume_eq(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        let (a0, a1) = self.a.assume_eq(&o.a, t);
        let (b0, b1) = self.b.assume_eq(&o.b, t);
        let r = (pair_reduce(a0, b0), pair_reduce(a1, b1));
        proof {
            assert forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) && (x == y) == t implies r.0.gamma(x) && r.1.gamma(y) by {
                assert(self.a.gamma(x) && o.a.gamma(y));
                assert(self.b.gamma(x) && o.b.gamma(y));
                assert(a0.gamma(x) && a1.gamma(y) && b0.gamma(x) && b1.gamma(y));
            }
            assert forall|x: S::V| #[trigger] r.0.gamma(x) implies self.gamma(x) by {
                assert(a0.gamma(x) && b0.gamma(x));
            }
            assert forall|y: S::V| #[trigger] r.1.gamma(y) implies o.gamma(y) by {
                assert(a1.gamma(y) && b1.gamma(y));
            }
        }
        r
    }
}

} // verus!

/// The type of an n-ary product, nested to the right:
/// `product_type![A, B, C]` is `Product<A, Product<B, C>>`. Nesting needs no
/// proof beyond `Product<A, B>`'s, because a product is itself `Refine`.
#[macro_export]
macro_rules! product_type {
    ($a:ty, $b:ty $(,)?) => { $crate::reduce::Product<$a, $b> };
    ($a:ty, $($rest:ty),+ $(,)?) => {
        $crate::reduce::Product<$a, $crate::product_type!($($rest),+)>
    };
}

/// A value of `product_type!` with the same components:
/// `product!(a, b, c)` is `Product { a, b: Product { a: b, b: c } }`.
#[macro_export]
macro_rules! product {
    ($a:expr, $b:expr $(,)?) => { $crate::reduce::Product { a: $a, b: $b } };
    ($a:expr, $($rest:expr),+ $(,)?) => {
        $crate::reduce::Product { a: $a, b: $crate::product!($($rest),+) }
    };
}

/// A pattern that names each component of a `product_type!` value:
/// `let product_pat!(x, y, z) = p;` binds the three leaves.
#[macro_export]
macro_rules! product_pat {
    ($a:pat, $b:pat $(,)?) => { $crate::reduce::Product { a: $a, b: $b } };
    ($a:pat, $($rest:pat),+ $(,)?) => {
        $crate::reduce::Product { a: $a, b: $crate::product_pat!($($rest),+) }
    };
}
