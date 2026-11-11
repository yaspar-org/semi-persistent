// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Facts<W>`: the channel of BitVec(W) e-classes.
//!
//! A record of fields, one per kind of fact, with `γ` the intersection of the
//! fields' concretizations. `normalize` propagates information between fields
//! (the reduction); `wf` adds to the field-wise invariant `pre_wf` the
//! condition that the fields are mutually reduced, which keeps `Facts`
//! canonical.
//!
//! **Adding a field** (doc/reduced-product.md, "Adding a field"): add it to the
//! struct, to `pre_wf`, `gamma`, `dup`, `top` (as top), `leq`, `join`, `widen`
//! and `meet_exact` (field-wise), extend `reduced` and `normalize`, and set it
//! to top in every constructor (or to what `reduced` forces, as `c` is a
//! constant when `u` is a single value). A top field adds no constraint to
//! `γ`, so every existing `to_channel` stays sound and every existing `refine`
//! stays valid.
//!
//! Fields:
//! - `u`, unsigned bounds (src/interval.rs);
//! - `c`, a congruence `x ≡ r mod m` (src/congruence.rs). The grid step of
//!   `normalize` rounds the bounds of `u` onto the grid of `c` (src/grid.rs)
//!   and makes `c` a constant when one value remains.
//!
//! Planned fields (doc/reduced-product.md, planned work):
//! - `s`, signed bounds (src/sbounds.rs);
//! - `bits`, known bits, a Tnum over `Word` (src/tnum_w.rs).
// Proof-only bindings are erased outside Verus.
#![allow(unused_variables)]
use crate::congruence::*;
use crate::grid::*;
use crate::interval::*;
use crate::lattice::*;
use crate::reduce::*;
use crate::word::*;
// Proof-only lemmas, erased outside Verus.
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// `x` lies in both fields.
pub open spec fn in_fields<W: Word>(u: Interval<W>, c: Congruence<W>, x: W) -> bool {
    u.gamma(x) && c.gamma(x)
}

/// The interval and the congruence are reduced against each other: both
/// bounds lie on the grid, and a single value is a constant congruence.
pub open spec fn grid_reduced<W: Word>(u: Interval<W>, c: Congruence<W>) -> bool {
    c.gamma(u.lo()) && c.gamma(u.hi()) && (u.lo() == u.hi() ==> c.modulus().view() == 0)
}

/// Membership in a well-formed congruence is the grid predicate of src/grid.rs.
proof fn lemma_gamma_on_grid<W: Word>(c: Congruence<W>, x: W)
    requires
        c.wf(),
    ensures
        c.gamma(x) == on_grid(x.view() as int, c.residue().view() as int, c.modulus().view() as int),
        grid_wf(c.residue(), c.modulus()),
{
    W::lemma_view_injective(x, c.residue());
}

/// Two points of the same grid are at least one step apart.
proof fn lemma_grid_gap(a: int, b: int, r: int, m: int)
    requires
        m > 0,
        a % m == r,
        b % m == r,
        a < b,
    ensures
        a + m <= b,
{
    lemma_fundamental_div_mod(a, m);
    lemma_fundamental_div_mod(b, m);
    let qa = a / m;
    let qb = b / m;
    assert(qa < qb) by (nonlinear_arith)
        requires
            a == m * qa + r,
            b == m * qb + r,
            a < b,
            m > 0,
    ;
    assert(m * qa + m <= m * qb) by (nonlinear_arith)
        requires
            qa + 1 <= qb,
            m > 0,
    ;
}

/// The congruence for a record that knows only `u`: top, or the constant
/// when `u` is a single value.
fn congruence_of<W: Word>(u: &Interval<W>) -> (c: Congruence<W>)
    requires
        u.wf(),
    ensures
        c.wf(),
        grid_reduced(*u, c),
        forall|x: W| u.gamma(x) ==> #[trigger] c.gamma(x),
{
    let (lo, hi) = u.bounds();
    if lo.eq(hi) {
        let c = Congruence::constant(lo);
        proof {
            assert forall|x: W| u.gamma(x) implies #[trigger] c.gamma(x) by {
                W::lemma_view_injective(x, lo);
            }
        }
        c
    } else {
        Congruence::top()
    }
}

/// The grid step of `normalize`: rounds the bounds of `u` onto the grid of
/// `c`, and makes `c` the constant when one value remains. `None` only when
/// the fields share no value.
fn grid_step<W: Word>(u: &Interval<W>, c: &Congruence<W>) -> (r: Option<
    (Interval<W>, Congruence<W>),
>)
    requires
        u.wf(),
        c.wf(),
    ensures
        match r {
            Some((u2, c2)) => u2.wf() && c2.wf() && grid_reduced(u2, c2) && forall|x: W| #[trigger]
                in_fields(u2, c2, x) == in_fields(*u, *c, x),
            None => forall|x: W| #[trigger] in_fields(*u, *c, x) ==> false,
        },
{
    let (lo, hi) = u.bounds();
    let (m, res) = c.parts();
    proof {
        lemma_gamma_on_grid(*c, lo);
    }
    let lo2 = match round_up(lo, res, m) {
        Some(y) => y,
        None => {
            proof {
                assert forall|x: W| #[trigger] in_fields(*u, *c, x) implies false by {
                    lemma_gamma_on_grid(*c, x);
                }
            }
            return None;
        },
    };
    let hi2 = match round_down(hi, res, m) {
        Some(y) => y,
        None => {
            proof {
                assert forall|x: W| #[trigger] in_fields(*u, *c, x) implies false by {
                    lemma_gamma_on_grid(*c, x);
                }
            }
            return None;
        },
    };
    proof {
        lemma_gamma_on_grid(*c, lo2);
        lemma_gamma_on_grid(*c, hi2);
        // Rounding keeps every common value: it lies on the grid inside `u`.
        assert forall|x: W| #[trigger] in_fields(*u, *c, x) implies lo2.view() <= x.view()
            <= hi2.view() by {
            lemma_gamma_on_grid(*c, x);
        }
    }
    if hi2.lt(lo2) {
        return None;
    }
    if lo2.eq(hi2) {
        let u2 = Interval::constant(lo2);
        let c2 = Congruence::constant(lo2);
        proof {
            assert(u2.gamma(lo2));
            assert forall|x: W| #[trigger] in_fields(u2, c2, x) == in_fields(*u, *c, x) by {
                W::lemma_view_injective(x, lo2);
            }
            assert forall|x: W| u2.gamma(x) implies x == lo2 by {
                W::lemma_view_injective(x, lo2);
            }
            assert(u2.gamma(u2.lo()) && u2.gamma(u2.hi()));
            assert(u2.lo() == lo2 && u2.hi() == lo2);
        }
        Some((u2, c2))
    } else {
        let u2 = Interval::new(lo2, hi2).expect("lo2 <= hi2");
        Some((u2, c.dup()))
    }
}

pub struct Facts<W> {
    /// Unsigned bounds.
    u: Interval<W>,
    /// Congruence.
    c: Congruence<W>,
}

impl<W: Word> Facts<W> {
    pub closed spec fn u(&self) -> Interval<W> {
        self.u
    }

    pub closed spec fn c(&self) -> Congruence<W> {
        self.c
    }

    /// The fields agree: no field can be tightened from the others. The
    /// planned normalize steps extend it.
    pub open spec fn reduced(&self) -> bool {
        grid_reduced(self.u(), self.c())
    }

    /// The record that knows only `u`.
    pub fn from_interval(u: Interval<W>) -> (r: Self)
        requires
            u.wf(),
        ensures
            r.wf(),
            r.u() == u,
            forall|x: W| #[trigger] r.gamma(x) == u.gamma(x),
    {
        let c = congruence_of(&u);
        Facts { u, c }
    }

    /// The reduced record of the facts `u` and `c`; `Bot` when they share no
    /// value.
    pub fn from_parts(u: Interval<W>, c: Congruence<W>) -> (r: BotOr<Self>)
        requires
            u.wf(),
            c.wf(),
        ensures
            r.wf(),
            forall|x: W| #[trigger] r.gamma(x) == (u.gamma(x) && c.gamma(x)),
    {
        let r = match grid_step(&u, &c) {
            Some((u2, c2)) => BotOr::Val(Facts { u: u2, c: c2 }),
            None => BotOr::Bot,
        };
        proof {
            assert forall|x: W| #[trigger] r.gamma(x) == (u.gamma(x) && c.gamma(x)) by {
                assert(in_fields(u, c, x) == (u.gamma(x) && c.gamma(x)));
            }
        }
        r
    }

    pub fn interval(&self) -> (r: Interval<W>)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.u(),
            forall|x: W| self.gamma(x) ==> #[trigger] r.gamma(x),
    {
        self.u.dup()
    }

    pub fn congruence(&self) -> (r: Congruence<W>)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.c(),
            forall|x: W| self.gamma(x) ==> #[trigger] r.gamma(x),
    {
        self.c.dup()
    }
}

impl<W: Word> Domain for Facts<W> {
    type C = W;

    open spec fn wf(&self) -> bool {
        self.pre_wf() && self.reduced()
    }

    open spec fn gamma(&self, c: W) -> bool {
        in_fields(self.u(), self.c(), c)
    }

    fn dup(&self) -> (r: Self) {
        Facts { u: self.u.dup(), c: self.c.dup() }
    }

    fn top() -> (r: Self) {
        let u = Interval::top();
        let c = congruence_of(&u);
        Facts { u, c }
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        let b = self.u.leq(&o.u) && self.c.leq(&o.c);
        proof {
            assert forall|x: W| #[trigger] self.gamma(x) && b implies o.gamma(x) by {
                assert(self.u.gamma(x));
                assert(<Congruence<W> as Domain>::gamma(&self.c, x));
            }
        }
        b
    }

    /// Field-wise join, then the grid step, which re-establishes `reduced`
    /// without a separate proof that the field-wise join keeps it.
    fn join(&self, o: &Self) -> (r: Self) {
        let u = self.u.join(&o.u);
        let c = self.c.join(&o.c);
        proof {
            assert forall|x: W| self.gamma(x) || o.gamma(x) implies #[trigger] in_fields(u, c, x) by {
                assert(self.c.has(x) || o.c.has(x));
            }
            assert(self.gamma(self.u.lo()));
        }
        match grid_step(&u, &c) {
            Some((u2, c2)) => Facts { u: u2, c: c2 },
            None => {
                proof {
                    assert(in_fields(u, c, self.u.lo()));
                }
                Facts { u, c }
            },
        }
    }

    /// `meet_exact` then `normalize`, inlined field by field: calling them from
    /// here would make this impl depend on functions whose contracts mention it.
    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        let mu = self.u.meet_exact(&o.u);
        let mc = self.c.meet(&o.c);
        match (mu, mc) {
            (BotOr::Val(u), BotOr::Val(c)) => {
                let s = grid_step(&u, &c);
                match s {
                    Some((u2, c2)) => {
                        let r = Facts { u: u2, c: c2 };
                        proof {
                            assert forall|x: W| self.gamma(x) && o.gamma(x) implies #[trigger] r.gamma(
                                x,
                            ) by {
                                assert(mu.gamma(x) && c.has(x));
                                assert(in_fields(u, c, x));
                            }
                        }
                        BotOr::Val(r)
                    },
                    None => {
                        proof {
                            assert forall|x: W| #[trigger] self.gamma(x) implies !o.gamma(x) by {
                                if o.gamma(x) {
                                    assert(mu.gamma(x));
                                    assert(u.gamma(x));
                                    assert(c.has(x));
                                    assert(in_fields(u, c, x));
                                    assert(false);
                                }
                            }
                        }
                        BotOr::Bot
                    },
                }
            },
            _ => {
                proof {
                    assert forall|x: W| #[trigger] self.gamma(x) implies !o.gamma(x) by {
                        assert(mu.gamma(x) == (self.u.gamma(x) && o.u.gamma(x)));
                        if let BotOr::Val(c) = mc {
                            assert(c.has(x) == (self.c.has(x) && o.c.has(x)));
                        } else {
                            assert(self.c.has(x) ==> !o.c.has(x));
                        }
                    }
                }
                BotOr::Bot
            },
        }
    }

    /// Field-wise widening, then the grid step: a bound that jumps to the end
    /// of the range rounds back onto the grid.
    fn widen(&self, o: &Self) -> (r: Self) {
        let u = self.u.widen(&o.u);
        let c = self.c.widen(&o.c);
        proof {
            assert forall|x: W| self.gamma(x) || o.gamma(x) implies #[trigger] in_fields(u, c, x) by {
                assert(<Congruence<W> as Domain>::gamma(&self.c, x) || <Congruence<W> as Domain>::gamma(
                    &o.c,
                    x,
                ));
                assert(<Congruence<W> as Domain>::gamma(&c, x));
            }
            assert(self.gamma(self.u.lo()));
        }
        match grid_step(&u, &c) {
            Some((u2, c2)) => Facts { u: u2, c: c2 },
            None => {
                proof {
                    assert(in_fields(u, c, self.u.lo()));
                }
                Facts { u, c }
            },
        }
    }
}

impl<W: Word> Canonical for Facts<W> {
    proof fn lemma_nonempty(&self) {
        assert(self.gamma(self.u.lo()));
    }

    /// Equal sets have the same least and greatest members, which are the
    /// bounds. Past one value, the grid's step is the gap to the second member.
    proof fn lemma_canonical(a: &Self, b: &Self) {
        let (lo, hi) = (a.u.lo(), a.u.hi());
        assert(a.gamma(lo) && a.gamma(hi) && b.gamma(b.u.lo()) && b.gamma(b.u.hi()));
        assert(b.gamma(lo) && b.gamma(hi) && a.gamma(b.u.lo()) && a.gamma(b.u.hi()));
        W::lemma_view_injective(lo, b.u.lo());
        W::lemma_view_injective(hi, b.u.hi());
        assert forall|c: W| #![trigger a.u.gamma(c)] a.u.gamma(c) == b.u.gamma(c) by {}
        Interval::lemma_canonical(&a.u, &b.u);
        if lo != hi {
            a.c.lemma_residue_member();
            b.c.lemma_residue_member();
            let (ma, mb) = (a.c.modulus().view() as int, b.c.modulus().view() as int);
            let l = lo.view() as int;
            W::lemma_view_injective(lo, hi);
            assert(a.c.modulus().view() > 0 && b.c.modulus().view() > 0);
            // Each grid's second member above `lo` lies in both sets.
            lemma_gamma_on_grid(a.c, lo);
            lemma_gamma_on_grid(a.c, hi);
            lemma_gamma_on_grid(b.c, lo);
            lemma_gamma_on_grid(b.c, hi);
            lemma_grid_gap(l, hi.view() as int, a.c.residue().view() as int, ma);
            lemma_grid_gap(l, hi.view() as int, b.c.residue().view() as int, mb);
            hi.lemma_view_bounded();
            let sa = W::from_int(l + ma);
            let sb = W::from_int(l + mb);
            W::lemma_from_int(l + ma);
            W::lemma_from_int(l + mb);
            lemma_small_mod((l + ma) as nat, W::modulus());
            lemma_small_mod((l + mb) as nat, W::modulus());
            lemma_mod_add_multiples_vanish(l, ma);
            lemma_mod_add_multiples_vanish(l, mb);
            lemma_gamma_on_grid(a.c, sa);
            lemma_gamma_on_grid(b.c, sb);
            assert(a.gamma(sa) && b.gamma(sb));
            assert(b.gamma(sa) && a.gamma(sb));
            lemma_gamma_on_grid(b.c, sa);
            lemma_gamma_on_grid(a.c, sb);
            lemma_grid_gap(l, l + ma, b.c.residue().view() as int, mb);
            lemma_grid_gap(l, l + mb, a.c.residue().view() as int, ma);
            assert forall|x: W| #![trigger a.c.gamma(x)] a.c.gamma(x) == b.c.gamma(x) by {}
            Congruence::lemma_canonical(&a.c, &b.c);
        } else {
            assert forall|x: W| #![trigger a.c.gamma(x)] a.c.gamma(x) == b.c.gamma(x) by {
                W::lemma_view_injective(x, lo);
            }
            Congruence::lemma_canonical(&a.c, &b.c);
        }
    }
}

impl<W: Word> Channel for Facts<W> {
    open spec fn pre_wf(&self) -> bool {
        self.u().wf() && self.c().wf()
    }

    proof fn lemma_wf_pre(&self) {
    }

    fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>) {
        let mu = self.u.meet_exact(&o.u);
        let mc = self.c.meet(&o.c);
        match (mu, mc) {
            (BotOr::Val(u), BotOr::Val(c)) => {
                let r = Facts { u, c };
                proof {
                    assert forall|x: W| #[trigger] r.gamma(x) == (self.gamma(x) && o.gamma(x)) by {
                        assert(mu.gamma(x) == (self.u.gamma(x) && o.u.gamma(x)));
                        assert(c.has(x) == (self.c.has(x) && o.c.has(x)));
                    }
                }
                BotOr::Val(r)
            },
            _ => {
                proof {
                    assert forall|x: W| #[trigger] self.gamma(x) implies !o.gamma(x) by {
                        assert(mu.gamma(x) == (self.u.gamma(x) && o.u.gamma(x)));
                        if let BotOr::Val(c) = mc {
                            assert(c.has(x) == (self.c.has(x) && o.c.has(x)));
                        } else {
                            assert(self.c.has(x) ==> !o.c.has(x));
                        }
                    }
                }
                BotOr::Bot
            },
        }
    }

    /// The grid step (doc/reduced-product.md): `u` and `c` snap to each
    /// other. The planned work adds unsigned and signed bounds tightening each
    /// other, and later known bits against bounds and congruence against low
    /// bits.
    fn normalize(&self) -> (r: BotOr<Self>) {
        let r = match grid_step(&self.u, &self.c) {
            Some((u, c)) => BotOr::Val(Facts { u, c }),
            None => BotOr::Bot,
        };
        proof {
            assert forall|x: W| #[trigger] r.gamma(x) == self.gamma(x) by {
                assert(in_fields(self.u, self.c, x) == self.gamma(x));
            }
        }
        r
    }
}

/// Every channel implements `Refine` for itself: `to_channel` is the identity,
/// `refine` is the reduced meet.
impl<W: Word> Refine for Facts<W> {
    type F = Facts<W>;

    fn to_channel(&self) -> (f: BotOr<Facts<W>>) {
        BotOr::Val(self.dup())
    }

    fn refine(&self, f: &Facts<W>) -> (r: BotOr<Self>) {
        meet_normalize(self, f)
    }
}

/// An unsigned interval writes itself into the `u` field and refines by it.
impl<W: Word> Refine for Interval<W> {
    type F = Facts<W>;

    fn to_channel(&self) -> (f: BotOr<Facts<W>>) {
        BotOr::Val(Facts::from_interval(self.dup()))
    }

    fn refine(&self, f: &Facts<W>) -> (r: BotOr<Self>) {
        let u = f.interval();
        let r = self.meet_exact(&u);
        proof {
            assert forall|x: W| self.gamma(x) && f.gamma(x) implies #[trigger] r.gamma(x) by {
                assert(u.gamma(x));
            }
        }
        r
    }
}

} // verus!
