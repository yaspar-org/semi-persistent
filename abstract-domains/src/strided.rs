// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Strided intervals over machine words, generic over the width.
//!
//! Port onto the shared traits (`doc/domain-traits.md`) of the domain
//! previously stamped per-width inside `domains.rs`. Canonical this time:
//! `stride == 0 <==> lo == hi`, and when `stride > 0`, `hi` sits exactly on
//! the stride grid (`(hi - lo) % stride == 0`), so `{7}` has exactly one
//! encoding and `lemma_canonical` is provable. `word::Word` has no generic
//! multiplication, so canonicalizing (snapping `hi` down to the grid) uses
//! `checked_sub` + `urem` instead of the div/mul reasoning the old
//! `normalize()` needed.
#![allow(unused_imports, unused_variables)]
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::*;
use crate::word::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

/// `{lo, lo+stride, lo+2*stride, ..., hi}` in the unsigned reading.
/// `stride == 0` is reserved for singletons (`lo == hi`).
pub struct StridedInterval<W> {
    stride: W,
    lo: W,
    hi: W,
}

/// `from_int` is the identity on in-range integers (same helper as interval.rs).
proof fn lemma_from_small<W: Word>(i: int)
    requires
        0 <= i < W::modulus() as int,
    ensures
        W::from_int(i).view() == i,
{
    W::lemma_from_int(i);
    lemma_small_mod(i as nat, W::modulus());
}

impl<W: Word> StridedInterval<W> {
    pub closed spec fn stride(&self) -> W {
        self.stride
    }

    pub closed spec fn lo(&self) -> W {
        self.lo
    }

    pub closed spec fn hi(&self) -> W {
        self.hi
    }

    pub fn bounds(&self) -> (r: (W, W, W))
        ensures
            r.0 == self.stride(),
            r.1 == self.lo(),
            r.2 == self.hi(),
    {
        (self.stride, self.lo, self.hi)
    }

    pub fn contains(&self, x: W) -> (b: bool)
        ensures
            b == self.gamma(x),
    {
        proof {
            W::lemma_view_bounded(x);
        }
        if !(self.lo.le(x) && x.le(self.hi)) {
            false
        } else if self.stride.eq(W::zero()) {
            true
        } else {
            let diff = x.checked_sub(self.lo).expect("lo <= x");
            proof {
                assert(diff.view() == x.view() - self.lo.view());
            }
            diff.urem(self.stride).eq(W::zero())
        }
    }

    /// Public smart constructor for `{lo + k*stride | k >= 0} ∩ [lo, hi]`:
    /// snaps `hi` down to the last point on the stride grid, and collapses
    /// to the singleton form when only one point remains. With `stride ==
    /// 0` that set is `{lo}` whatever `hi` is. `None` when `lo > hi`,
    /// matching `Interval::new`.
    pub fn new(stride: W, lo: W, hi: W) -> (r: Option<Self>)
        ensures
            match r {
                Some(v) => v.wf() && lo.view() <= hi.view() && forall|x: W| #[trigger]
                    v.gamma(x) <==> if stride.view() == 0 {
                        x.view() == lo.view()
                    } else {
                        lo.view() <= x.view() && x.view() <= hi.view() && (x.view() as int
                            - lo.view() as int) % (stride.view() as int) == 0
                    },
                None => lo.view() > hi.view(),
            },
    {
        if !lo.le(hi) {
            return None;
        }
        Some(Self::mk(stride, lo, hi))
    }

    pub fn constant(c: W) -> (r: Self)
        ensures
            r.wf(),
            forall|x: W| #[trigger] r.gamma(x) <==> x == c,
    {
        let r = StridedInterval { stride: W::zero(), lo: c, hi: c };
        proof {
            assert forall|x: W| #[trigger] r.gamma(x) <==> x == c by {
                W::lemma_view_injective(x, c);
            }
        }
        r
    }

    /// `stride == 0` always means singleton(lo) -- `hi` is ignored in that
    /// case, matching `wf`'s `stride == 0 <==> lo == hi` (a caller passing
    /// `stride == 0` with `lo != hi` is asking for a singleton with a
    /// nonsense upper bound, not for the wide range `[lo, hi]`).
    fn mk(stride: W, lo: W, hi: W) -> (r: Self)
        requires
            lo.view() <= hi.view(),
        ensures
            r.wf(),
            forall|x: W| #[trigger] r.gamma(x) <==> if stride.view() == 0 {
                x.view() == lo.view()
            } else {
                lo.view() <= x.view() && x.view() <= hi.view() && (x.view() as int - lo.view()
                    as int) % (stride.view() as int) == 0
            },
    {
        if stride.eq(W::zero()) || lo.eq(hi) {
            let r = StridedInterval { stride: W::zero(), lo, hi: lo };
            proof {
                if stride.view() > 0 {
                    lemma_mod_multiples_basic(0, stride.view() as int);
                }
            }
            r
        } else {
            let diff = hi.checked_sub(lo).expect("lo <= hi");
            proof {
                assert(diff.view() == hi.view() - lo.view());
            }
            let rem = diff.urem(stride);
            proof {
                assert(rem.view() == diff.view() % stride.view());
                lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                lemma_mul_left_inequality(
                    stride.view() as int,
                    0,
                    diff.view() as int / (stride.view() as int),
                );
                assert(rem.view() as int <= diff.view() as int);
            }
            let canon_hi = hi.checked_sub(rem).expect("rem <= diff <= hi - lo");
            proof {
                assert(canon_hi.view() == hi.view() - rem.view());
                assert(canon_hi.view() as int - lo.view() as int == diff.view() as int
                    - rem.view() as int);
                lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                // diff == stride * (diff/stride) + rem, so canon_hi - lo == stride*(diff/stride)
            }
            if canon_hi.eq(lo) {
                let r = StridedInterval { stride: W::zero(), lo, hi: lo };
                proof {
                    assert forall|x: W| #[trigger] r.gamma(x) <==> (lo.view() <= x.view()
                        && x.view() <= hi.view() && (stride.view() == 0 || (x.view() as int
                        - lo.view() as int) % (stride.view() as int) == 0)) by {
                        if x.view() == lo.view() {
                            lemma_mod_multiples_basic(0, stride.view() as int);
                        } else if lo.view() <= x.view() && x.view() <= hi.view() {
                            // x - lo is a nonzero multiple of stride but canon_hi == lo means
                            // the only multiple of stride in [lo, hi] is 0.
                            if (x.view() as int - lo.view() as int) % (stride.view() as int)
                                == 0 {
                                let k = (x.view() as int - lo.view() as int)
                                    / (stride.view() as int);
                                lemma_fundamental_div_mod(
                                    x.view() as int - lo.view() as int,
                                    stride.view() as int,
                                );
                                if k > 0 {
                                    lemma_mul_inequality(1, k, stride.view() as int);
                                    assert(stride.view() as int * 1 <= stride.view() as int
                                        * k);
                                    assert(x.view() as int - lo.view() as int >= stride.view()
                                        as int);
                                    assert(x.view() as int >= lo.view() as int + stride.view()
                                        as int);
                                    assert(canon_hi.view() as int == lo.view() as int);
                                    assert(x.view() as int <= hi.view() as int);
                                    // and canon_hi == hi - rem == lo, i.e. diff == rem, so
                                    // stride does not fit a second time inside [lo,hi].
                                    assert(diff.view() as int == rem.view() as int);
                                    assert(x.view() as int - lo.view() as int
                                        <= diff.view() as int);
                                    assert(false) by {
                                        lemma_mul_inequality(
                                            stride.view() as int,
                                            x.view() as int - lo.view() as int,
                                            1,
                                        );
                                    };
                                }
                            }
                        }
                    }
                };
                r
            } else {
                let r = StridedInterval { stride, lo, hi: canon_hi };
                proof {
                    let q = diff.view() as int / (stride.view() as int);
                    lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                    assert(canon_hi.view() as int - lo.view() as int == stride.view() as int
                        * q);
                    lemma_mul_left_inequality(stride.view() as int, 0, q);
                    assert(canon_hi.view() as int >= lo.view() as int);
                    lemma_mod_multiples_basic(q, stride.view() as int);
                    lemma_mul_is_commutative(stride.view() as int, q);
                    assert((canon_hi.view() as int - lo.view() as int) % (stride.view() as int)
                        == 0);
                }
                proof {
                    assert forall|x: W| #[trigger] r.gamma(x) <==> (lo.view() <= x.view()
                        && x.view() <= hi.view() && (stride.view() == 0 || (x.view() as int
                        - lo.view() as int) % (stride.view() as int) == 0)) by {
                        if lo.view() <= x.view() && x.view() <= canon_hi.view() && (x.view()
                            as int - lo.view() as int) % (stride.view() as int) == 0 {
                            assert(x.view() as int <= hi.view() as int);
                        }
                        if lo.view() <= x.view() && x.view() <= hi.view() && (x.view() as int
                            - lo.view() as int) % (stride.view() as int) == 0 {
                            let k = (x.view() as int - lo.view() as int)
                                / (stride.view() as int);
                            let q = diff.view() as int / (stride.view() as int);
                            lemma_fundamental_div_mod(
                                x.view() as int - lo.view() as int,
                                stride.view() as int,
                            );
                            lemma_fundamental_div_mod(diff.view() as int, stride.view() as int);
                            lemma_div_is_ordered(
                                x.view() as int - lo.view() as int,
                                diff.view() as int,
                                stride.view() as int,
                            );
                            lemma_mul_left_inequality(stride.view() as int, k, q);
                            assert(x.view() as int - lo.view() as int <= canon_hi.view() as int
                                - lo.view() as int);
                        }
                    };
                }
                r
            }
        }
    }

    /// If a positive `d` is an exact multiple of a positive `s`, `s <= d`.
    proof fn lemma_divisor_le(d: int, s: int)
        requires
            d > 0,
            s > 0,
            d % s == 0,
        ensures
            s <= d,
    {
        let k = d / s;
        lemma_fundamental_div_mod(d, s);
        assert(d == s * k);
        if k == 0 {
            assert(s * 0 == 0);
            assert(d == 0);
        }
        assert(k >= 1);
        lemma_mul_left_inequality(s, 1, k);
    }

    /// Used twice (with `x`/`y` swapped) inside `lemma_canonical` to pin
    /// down the stride once `lo`/`hi` already agree: `x`'s second grid
    /// point (`x.lo + x.stride`) must be a grid point of `y` too, which
    /// forces `y.stride` to divide `x.stride`.
    proof fn lemma_stride_le(x: &Self, y: &Self)
        requires
            x.wf(),
            y.wf(),
            x.lo() == y.lo(),
            x.hi() == y.hi(),
            x.lo().view() < x.hi().view(),
            forall|c: W| #![trigger x.gamma(c)] x.gamma(c) == y.gamma(c),
        ensures
            y.stride().view() <= x.stride().view(),
    {
        let d = x.hi.view() as int - x.lo.view() as int;
        Self::lemma_divisor_le(d, x.stride.view() as int);
        let p_int = x.lo.view() as int + x.stride.view() as int;
        x.hi.lemma_view_bounded();
        lemma_from_small::<W>(p_int);
        let p = W::from_int(p_int);
        lemma_mod_self_0(x.stride.view() as int);
        assert(x.gamma(p));
        assert(y.gamma(p));
        assert((p.view() as int - y.lo.view() as int) % (y.stride.view() as int) == 0);
        Self::lemma_divisor_le(x.stride.view() as int, y.stride.view() as int);
    }

    // ---- general-purpose modular arithmetic building blocks -------------

    proof fn lemma_mod_zero_sum(a: int, b: int, m: int)
        requires
            m > 0,
            a % m == 0,
            b % m == 0,
        ensures
            (a + b) % m == 0,
    {
        lemma_mod_adds(a, b, m);
    }

    proof fn lemma_mod_zero_neg(a: int, m: int)
        requires
            m > 0,
            a % m == 0,
        ensures
            (-a) % m == 0,
    {
        lemma_fundamental_div_mod(a, m);
        let k = a / m;
        assert(a == m * k);
        lemma_mul_unary_negation(m, k);
        assert(-a == m * (-k));
        lemma_mod_multiples_basic(-k, m);
        lemma_mul_is_commutative(m, -k);
    }

    proof fn lemma_mod_zero_diff(a: int, b: int, m: int)
        requires
            m > 0,
            a % m == 0,
            b % m == 0,
        ensures
            (a - b) % m == 0,
    {
        Self::lemma_mod_zero_neg(b, m);
        Self::lemma_mod_zero_sum(a, -b, m);
        assert(a - b == a + (-b));
    }

    /// Divisibility is transitive: `y | x` and `z | y` implies `z | x`.
    proof fn lemma_mod_zero_transitive(x: int, y: int, z: int)
        requires
            y > 0,
            z > 0,
            x % y == 0,
            y % z == 0,
        ensures
            x % z == 0,
    {
        lemma_fundamental_div_mod(x, y);
        lemma_fundamental_div_mod(y, z);
        let p = x / y;
        let q = y / z;
        assert(x == y * p);
        assert(y == z * q);
        assert(x == (z * q) * p);
        lemma_mul_is_associative(z, q, p);
        assert(x == z * (q * p));
        lemma_mod_multiples_basic(q * p, z);
        lemma_mul_is_commutative(z, q * p);
    }

    /// `self_` and `o` share a nonzero stride and agree on residue class
    /// (`self_.lo - o.lo` is a multiple of that stride): a point on one's
    /// grid is on the other's grid too. Says nothing about bounds.
    proof fn lemma_same_grid(self_: &Self, o: &Self, c: W)
        requires
            self_.stride().view() == o.stride().view(),
            self_.stride().view() > 0,
            (self_.lo().view() as int - o.lo().view() as int) % (self_.stride().view() as int)
                == 0,
            (c.view() as int - self_.lo().view() as int) % (self_.stride().view() as int) == 0,
        ensures
            (c.view() as int - o.lo().view() as int) % (self_.stride().view() as int) == 0,
    {
        Self::lemma_mod_zero_sum(
            c.view() as int - self_.lo().view() as int,
            self_.lo().view() as int - o.lo().view() as int,
            self_.stride().view() as int,
        );
        assert(c.view() as int - o.lo().view() as int == (c.view() as int - self_.lo().view()
            as int) + (self_.lo().view() as int - o.lo().view() as int));
    }

    // ---- operation-specific lemmas ---------------------------------------

    /// Bridges the native `abs_diff` (computed by an exec `if self.lo <=
    /// o.lo`) to the signed difference used in spec-level residue checks.
    proof fn lemma_abs_diff_residue(self_lo: W, o_lo: W, abs_diff: W, stride: W)
        requires
            stride.view() > 0,
            abs_diff.view() == if self_lo.view() <= o_lo.view() {
                o_lo.view() - self_lo.view()
            } else {
                self_lo.view() - o_lo.view()
            },
        ensures
            (self_lo.view() as int - o_lo.view() as int) % (stride.view() as int) == 0
                <==> abs_diff.view() as int % (stride.view() as int) == 0,
    {
        if self_lo.view() <= o_lo.view() {
            assert(self_lo.view() as int - o_lo.view() as int == -(abs_diff.view() as int));
            if abs_diff.view() as int % (stride.view() as int) == 0 {
                Self::lemma_mod_zero_neg(abs_diff.view() as int, stride.view() as int);
            }
            if (self_lo.view() as int - o_lo.view() as int) % (stride.view() as int) == 0 {
                Self::lemma_mod_zero_neg(
                    self_lo.view() as int - o_lo.view() as int,
                    stride.view() as int,
                );
            }
        }
    }

    proof fn lemma_leq_sound(self_: &Self, o: &Self, offset: W)
        requires
            self_.wf(),
            o.wf(),
            self_.lo().view() < self_.hi().view(),
            o.lo().view() <= self_.lo().view(),
            self_.hi().view() <= o.hi().view(),
            o.stride().view() > 0,
            self_.stride().view() as int % (o.stride().view() as int) == 0,
            offset.view() == self_.lo().view() - o.lo().view(),
            offset.view() as int % (o.stride().view() as int) == 0,
        ensures
            forall|c: W| #[trigger] self_.gamma(c) ==> o.gamma(c),
    {
        assert forall|c: W| #[trigger] self_.gamma(c) implies o.gamma(c) by {
            if self_.lo.view() <= c.view() && c.view() <= self_.hi.view() && (c.view() as int
                - self_.lo.view() as int) % (self_.stride.view() as int) == 0 {
                Self::lemma_mod_zero_transitive(
                    c.view() as int - self_.lo.view() as int,
                    self_.stride.view() as int,
                    o.stride.view() as int,
                );
                Self::lemma_mod_zero_sum(
                    c.view() as int - self_.lo.view() as int,
                    offset.view() as int,
                    o.stride.view() as int,
                );
                assert(c.view() as int - o.lo.view() as int == (c.view() as int - self_.lo.view()
                    as int) + offset.view() as int);
            }
        };
    }

    /// Converse of `lemma_leq_sound`: if every point of a non-singleton
    /// `self_` is in `o`, then `o.stride` divides `self_.stride`. Witness:
    /// `self_.lo` and `self_.lo + self_.stride` are both on `o`'s grid.
    proof fn lemma_leq_complete(self_: &Self, o: &Self)
        requires
            self_.wf(),
            o.wf(),
            self_.lo().view() < self_.hi().view(),
            o.stride().view() > 0,
            forall|c: W| #[trigger] self_.gamma(c) ==> o.gamma(c),
        ensures
            self_.stride().view() as int % (o.stride().view() as int) == 0,
    {
        self_.lemma_contains_bounds();
        assert(o.gamma(self_.lo));
        let d = self_.hi.view() as int - self_.lo.view() as int;
        Self::lemma_divisor_le(d, self_.stride.view() as int);
        let p_int = self_.lo.view() as int + self_.stride.view() as int;
        self_.hi.lemma_view_bounded();
        lemma_from_small::<W>(p_int);
        let p = W::from_int(p_int);
        lemma_mod_self_0(self_.stride.view() as int);
        assert(self_.gamma(p));
        assert(o.gamma(p));
        Self::lemma_mod_zero_diff(
            p.view() as int - o.lo.view() as int,
            self_.lo.view() as int - o.lo.view() as int,
            o.stride.view() as int,
        );
        assert(self_.stride.view() as int == (p.view() as int - o.lo.view() as int) - (
        self_.lo.view() as int - o.lo.view() as int));
    }

    /// A point of `x` is on any grid `g` that divides `x.stride` and that
    /// `x.lo` sits on (anchored at `base`).
    proof fn lemma_on_grid(x: &Self, base: int, g: int, c: W)
        requires
            x.wf(),
            g > 0,
            x.stride().view() as int % g == 0,
            (x.lo().view() as int - base) % g == 0,
            x.gamma(c),
        ensures
            (c.view() as int - base) % g == 0,
    {
        if x.stride.view() == 0 {
            assert(c.view() == x.lo.view());
        } else {
            Self::lemma_mod_zero_transitive(
                c.view() as int - x.lo.view() as int,
                x.stride.view() as int,
                g,
            );
            Self::lemma_mod_zero_sum(
                c.view() as int - x.lo.view() as int,
                x.lo.view() as int - base,
                g,
            );
            assert(c.view() as int - base == (c.view() as int - x.lo.view() as int) + (
            x.lo.view() as int - base));
        }
    }

    /// `r` spans `[min lo, max hi]` on a grid `g` that divides both strides
    /// and the distance between the two `lo`s, so it contains both operands.
    proof fn lemma_join_on_grid(self_: &Self, o: &Self, g: int, abs_diff: W, r: &Self)
        requires
            self_.wf(),
            o.wf(),
            g > 0,
            self_.stride().view() as int % g == 0,
            o.stride().view() as int % g == 0,
            abs_diff.view() == if self_.lo().view() <= o.lo().view() {
                o.lo().view() - self_.lo().view()
            } else {
                self_.lo().view() - o.lo().view()
            },
            abs_diff.view() as int % g == 0,
            r.stride().view() == g,
            r.lo().view() == if self_.lo().view() <= o.lo().view() {
                self_.lo().view()
            } else {
                o.lo().view()
            },
            r.hi().view() == if self_.hi().view() <= o.hi().view() {
                o.hi().view()
            } else {
                self_.hi().view()
            },
            r.lo().view() < r.hi().view(),
        ensures
            r.wf(),
            forall|c: W| #[trigger] self_.gamma(c) ==> r.gamma(c),
            forall|c: W| #[trigger] o.gamma(c) ==> r.gamma(c),
    {
        let base = r.lo().view() as int;
        // Both `lo`s are on the grid anchored at `base`: one of them is
        // `base`, the other is `abs_diff` above it.
        lemma_mod_multiples_basic(0, g);
        assert((self_.lo.view() as int - base) % g == 0);
        assert((o.lo.view() as int - base) % g == 0);
        assert forall|c: W| #[trigger] self_.gamma(c) implies r.gamma(c) by {
            Self::lemma_on_grid(self_, base, g, c);
        };
        assert forall|c: W| #[trigger] o.gamma(c) implies r.gamma(c) by {
            Self::lemma_on_grid(o, base, g, c);
        };
        self_.lemma_contains_bounds();
        o.lemma_contains_bounds();
        assert(r.gamma(self_.hi) && r.gamma(o.hi));
    }

    proof fn lemma_join_two_points(self_: &Self, o: &Self, r: &Self)
        requires
            self_.wf(),
            o.wf(),
            self_.lo().view() == self_.hi().view(),
            o.lo().view() == o.hi().view(),
            self_.lo().view() != o.lo().view(),
            r.lo().view() == if self_.lo().view() <= o.lo().view() {
                self_.lo().view()
            } else {
                o.lo().view()
            },
            r.hi().view() == if self_.lo().view() <= o.lo().view() {
                o.lo().view()
            } else {
                self_.lo().view()
            },
            r.stride().view() == r.hi().view() - r.lo().view(),
        ensures
            r.wf(),
            forall|c: W| #[trigger] self_.gamma(c) ==> r.gamma(c),
            forall|c: W| #[trigger] o.gamma(c) ==> r.gamma(c),
    {
        lemma_mod_self_0(r.stride().view() as int);
        lemma_mod_multiples_basic(0, r.stride().view() as int);
        assert forall|c: W| #[trigger] self_.gamma(c) implies r.gamma(c) by {}
        assert forall|c: W| #[trigger] o.gamma(c) implies r.gamma(c) by {}
    }

    proof fn lemma_meet_same_stride(self_: &Self, o: &Self, abs_diff: W, r: &Self)
        requires
            self_.wf(),
            o.wf(),
            self_.stride().view() == o.stride().view(),
            self_.stride().view() > 0,
            Self::residues_match(self_, o, abs_diff),
            r.lo().view() == if self_.lo().view() <= o.lo().view() {
                o.lo().view()
            } else {
                self_.lo().view()
            },
            r.hi().view() == if self_.hi().view() <= o.hi().view() {
                self_.hi().view()
            } else {
                o.hi().view()
            },
            r.lo().view() <= r.hi().view(),
            r.stride().view() == if r.lo().view() == r.hi().view() {
                0
            } else {
                self_.stride().view()
            },
        ensures
            r.wf(),
            forall|c: W| #[trigger] r.gamma(c) <== self_.gamma(c) && o.gamma(c),
    {
        Self::lemma_abs_diff_residue(self_.lo, o.lo, abs_diff, self_.stride);
        Self::lemma_mod_zero_neg(
            self_.lo().view() as int - o.lo().view() as int,
            self_.stride().view() as int,
        );
        if r.lo().view() == r.hi().view() {
            // Collapsed to a single point: gamma(r) is just x == r.lo(),
            // which self_.gamma(c) && o.gamma(c) already pins c to (their
            // bounds squeeze to the same point r.lo == r.hi).
            assert forall|c: W| self_.gamma(c) && o.gamma(c) implies #[trigger] r.gamma(c) by {}
            return ;
        }
        // r.lo is max(self_.lo, o.lo) and r.hi is min(self_.hi, o.hi): if c
        // is in both gammas, the bound check is automatic, and the residue
        // check is whichever of the two conjuncts matches r.lo directly --
        // no grid transfer needed, unlike join.
        assert forall|c: W| self_.gamma(c) && o.gamma(c) implies #[trigger] r.gamma(c) by {}
        // r.wf()'s grid condition: whichever of self_/o contributed r.hi
        // already has it on its own grid (wf); same_grid transfers that to
        // r.lo's anchor only when r.lo came from the other side.
        assert((r.hi().view() as int - r.lo().view() as int) % (self_.stride().view() as int)
            == 0) by {
            if r.hi().view() == self_.hi.view() {
                if r.lo().view() != self_.lo.view() {
                    Self::lemma_same_grid(self_, o, self_.hi);
                }
            } else {
                if r.lo().view() != o.lo.view() {
                    Self::lemma_same_grid(o, self_, o.hi);
                }
            }
        };
    }

    proof fn lemma_residue_mismatch_disjoint(self_: &Self, o: &Self, abs_diff: W)
        requires
            self_.wf(),
            o.wf(),
            self_.stride().view() == o.stride().view(),
            self_.stride().view() > 0,
            abs_diff.view() == if self_.lo().view() <= o.lo().view() {
                o.lo().view() - self_.lo().view()
            } else {
                self_.lo().view() - o.lo().view()
            },
            abs_diff.view() as int % (self_.stride().view() as int) != 0,
        ensures
            forall|c: W| #[trigger] self_.gamma(c) ==> !o.gamma(c),
    {
        Self::lemma_abs_diff_residue(self_.lo, o.lo, abs_diff, self_.stride);
        assert forall|c: W| #[trigger] self_.gamma(c) implies !o.gamma(c) by {
            if o.gamma(c) {
                Self::lemma_mod_zero_diff(
                    c.view() as int - o.lo.view() as int,
                    c.view() as int - self_.lo.view() as int,
                    self_.stride.view() as int,
                );
                assert((self_.lo.view() as int - o.lo.view() as int) == (c.view() as int
                    - o.lo.view() as int) - (c.view() as int - self_.lo.view() as int));
            }
        };
    }

    /// Rounding `l` up onto the grid `base + k*s`: with `r = (l - base) % s`
    /// nonzero, `l + (s - r)` is on the grid, and every grid point `c >= l`
    /// is at least that far up.
    proof fn lemma_round_up(base: int, l: int, s: int, c: int)
        requires
            s > 0,
            base <= l,
            l <= c,
            (c - base) % s == 0,
            (l - base) % s != 0,
        ensures
            c >= l + (s - (l - base) % s),
            (l + (s - (l - base) % s) - base) % s == 0,
    {
        let r = (l - base) % s;
        let q = (l - base) / s;
        let k = (c - base) / s;
        lemma_fundamental_div_mod(l - base, s);
        lemma_fundamental_div_mod(c - base, s);
        lemma_mod_pos_bound(l - base, s);
        assert(s * k > s * q);
        assert(k >= q + 1) by (nonlinear_arith)
            requires
                s * k > s * q,
                s > 0,
        ;
        assert(s * k >= s * (q + 1)) by (nonlinear_arith)
            requires
                k >= q + 1,
                s > 0,
        ;
        assert(s * (q + 1) == s * q + s) by (nonlinear_arith);
        assert(l + (s - r) - base == s * (q + 1));
        lemma_mod_multiples_basic(q + 1, s);
        lemma_mul_is_commutative(s, q + 1);
    }

    /// The points of `a` inside `[l, h]`, encoded canonically: `l` is
    /// rounded up onto `a`'s grid and `mk` rounds `h` down. `Bot` when no
    /// grid point of `a` lies in `[l, h]`.
    fn clip(a: &Self, l: W, h: W) -> (r: BotOr<Self>)
        requires
            a.wf(),
            a.stride().view() > 0,
            a.lo().view() <= l.view(),
            l.view() <= h.view(),
            h.view() <= a.hi().view(),
        ensures
            match r {
                BotOr::Bot => forall|c: W| #[trigger]
                    a.gamma(c) ==> !(l.view() <= c.view() && c.view() <= h.view()),
                BotOr::Val(m) => m.wf() && forall|c: W| #[trigger]
                    m.gamma(c) <== a.gamma(c) && l.view() <= c.view() && c.view() <= h.view(),
            },
    {
        let s = a.stride;
        let off = l.checked_sub(a.lo).expect("a.lo <= l");
        let rem = off.urem(s);
        proof {
            assert(rem.view() as int == (l.view() as int - a.lo.view() as int) % (s.view()
                as int));
            lemma_mod_pos_bound(off.view() as int, s.view() as int);
        }
        let lo = if rem.eq(W::zero()) {
            l
        } else {
            let gap = s.checked_sub(rem).expect("rem < stride");
            match l.checked_add(gap) {
                Some(v) => v,
                None => {
                    proof {
                        assert forall|c: W| #[trigger]
                            a.gamma(c) implies !(l.view() <= c.view() && c.view() <= h.view()) by {
                            c.lemma_view_bounded();
                            if l.view() <= c.view() && c.view() <= h.view() {
                                Self::lemma_round_up(
                                    a.lo.view() as int,
                                    l.view() as int,
                                    s.view() as int,
                                    c.view() as int,
                                );
                            }
                        }
                    }
                    return BotOr::Bot;
                },
            }
        };
        // Every point of `a` in `[l, h]` is a grid point `>= lo`.
        proof {
            assert forall|c: W|
                a.gamma(c) && l.view() <= c.view() && c.view() <= h.view() implies lo.view()
                <= #[trigger] c.view() && (c.view() as int - lo.view() as int) % (s.view() as int)
                == 0 by {
                if rem.view() != 0 {
                    Self::lemma_round_up(
                        a.lo.view() as int,
                        l.view() as int,
                        s.view() as int,
                        c.view() as int,
                    );
                }
                Self::lemma_mod_zero_diff(
                    c.view() as int - a.lo.view() as int,
                    lo.view() as int - a.lo.view() as int,
                    s.view() as int,
                );
                assert(c.view() as int - lo.view() as int == (c.view() as int - a.lo.view()
                    as int) - (lo.view() as int - a.lo.view() as int));
            }
        }
        if h.lt(lo) {
            proof {
                assert forall|c: W| #[trigger]
                    a.gamma(c) implies !(l.view() <= c.view() && c.view() <= h.view()) by {}
            }
            return BotOr::Bot;
        }
        if h.eq(a.hi) {
            // `a.hi` is already on the grid, so no `urem` is needed to snap it.
            let m = if lo.eq(h) {
                StridedInterval { stride: W::zero(), lo, hi: h }
            } else {
                StridedInterval { stride: s, lo, hi: h }
            };
            proof {
                a.lemma_contains_bounds();
                assert((h.view() as int - lo.view() as int) % (s.view() as int) == 0);
                assert forall|c: W|
                    a.gamma(c) && l.view() <= c.view() && c.view() <= h.view() implies #[trigger]
                    m.gamma(c) by {}
            }
            return BotOr::Val(m);
        }
        let m = Self::mk(s, lo, h);
        proof {
            assert forall|c: W|
                a.gamma(c) && l.view() <= c.view() && c.view() <= h.view() implies #[trigger]
                m.gamma(c) by {}
        }
        BotOr::Val(m)
    }

    /// Meet for two non-singletons with `a.stride > b.stride`. When
    /// `b.stride` divides `a.stride`, all of `a`'s points share one residue
    /// mod `b.stride`, so either none of them is on `b`'s grid (`Bot`) or
    /// all are, and clipping `a` to the common bounds is exact. Otherwise
    /// clipping `a` is sound but may keep points off `b`'s grid; the exact
    /// answer needs `crt_merge` (#112).
    fn meet_unequal_strides(a: &Self, b: &Self) -> (r: BotOr<Self>)
        requires
            a.wf(),
            b.wf(),
            a.stride().view() > b.stride().view(),
            b.stride().view() > 0,
            a.lo().view() <= b.hi().view(),
            b.lo().view() <= a.hi().view(),
        ensures
            match r {
                BotOr::Bot => forall|c: W| #[trigger] a.gamma(c) ==> !b.gamma(c),
                BotOr::Val(m) => m.wf() && forall|c: W| #[trigger]
                    m.gamma(c) <== a.gamma(c) && b.gamma(c),
            },
    {
        if a.stride.urem(b.stride).eq(W::zero()) {
            let abs_diff = if a.lo.le(b.lo) {
                b.lo.checked_sub(a.lo).expect("a.lo <= b.lo")
            } else {
                a.lo.checked_sub(b.lo).expect("b.lo <= a.lo")
            };
            if !abs_diff.urem(b.stride).eq(W::zero()) {
                proof {
                    Self::lemma_abs_diff_residue(a.lo, b.lo, abs_diff, b.stride);
                    assert forall|c: W| #[trigger] a.gamma(c) implies !b.gamma(c) by {
                        if b.gamma(c) {
                            Self::lemma_mod_zero_transitive(
                                c.view() as int - a.lo.view() as int,
                                a.stride.view() as int,
                                b.stride.view() as int,
                            );
                            Self::lemma_mod_zero_diff(
                                c.view() as int - b.lo.view() as int,
                                c.view() as int - a.lo.view() as int,
                                b.stride.view() as int,
                            );
                            assert(a.lo.view() as int - b.lo.view() as int == (c.view() as int
                                - b.lo.view() as int) - (c.view() as int - a.lo.view() as int));
                        }
                    }
                }
                return BotOr::Bot;
            }
        }
        let l = if a.lo.le(b.lo) {
            b.lo
        } else {
            a.lo
        };
        let h = if a.hi.le(b.hi) {
            a.hi
        } else {
            b.hi
        };
        match Self::clip(a, l, h) {
            BotOr::Bot => {
                proof {
                    assert forall|c: W| #[trigger] a.gamma(c) implies !b.gamma(c) by {}
                }
                BotOr::Bot
            },
            BotOr::Val(m) => {
                proof {
                    assert forall|c: W| a.gamma(c) && b.gamma(c) implies #[trigger] m.gamma(
                        c,
                    ) by {}
                }
                BotOr::Val(m)
            },
        }
    }

    /// Whether `self_`'s and `o`'s residues agree, expressed through the
    /// caller's already-computed native `abs_diff` (see
    /// `lemma_abs_diff_residue`) instead of a fresh spec-level formula.
    pub open spec fn residues_match(self_: &Self, o: &Self, abs_diff: W) -> bool {
        &&& abs_diff.view() == if self_.lo().view() <= o.lo().view() {
            o.lo().view() - self_.lo().view()
        } else {
            self_.lo().view() - o.lo().view()
        }
        &&& abs_diff.view() as int % (self_.stride().view() as int) == 0
    }

    /// `gamma(lo)` and `gamma(hi)` both hold for any wf value -- used
    /// everywhere a proof needs a point known to be in a domain's own
    /// gamma. `gamma(hi)` unfolds directly from `wf`'s own grid condition;
    /// `gamma(lo)` needs `0 % stride == 0` spelled out, since Z3 does not
    /// know that without a hint.
    proof fn lemma_contains_bounds(&self)
        requires
            self.wf(),
        ensures
            self.gamma(self.lo),
            self.gamma(self.hi),
    {
        if self.stride.view() > 0 {
            lemma_mod_multiples_basic(0, self.stride.view() as int);
        }
    }
}

impl<W: Word> Domain for StridedInterval<W> {
    type C = W;

    open spec fn wf(&self) -> bool {
        &&& self.lo().view() <= self.hi().view()
        &&& (self.stride().view() == 0 <==> self.lo().view() == self.hi().view())
        &&& (self.stride().view() > 0 ==> (self.hi().view() as int - self.lo().view() as int) % (
        self.stride().view() as int) == 0)
    }

    open spec fn gamma(&self, c: W) -> bool {
        self.lo().view() <= c.view() && c.view() <= self.hi().view() && (self.stride().view()
            == 0 || (c.view() as int - self.lo().view() as int) % (self.stride().view() as int)
            == 0)
    }

    fn dup(&self) -> (r: Self) {
        StridedInterval { stride: self.stride, lo: self.lo, hi: self.hi }
    }

    fn top() -> (r: Self) {
        let r = StridedInterval { stride: W::one(), lo: W::zero(), hi: W::max() };
        proof {
            W::lemma_modulus();
            assert((r.hi().view() as int - r.lo().view() as int) % 1 == 0) by (nonlinear_arith);
            assert forall|c: W| #[trigger] r.gamma(c) by {
                c.lemma_view_bounded();
                assert((c.view() as int - 0) % 1 == 0) by (nonlinear_arith);
            }
        }
        r
    }

    /// Complete as well as sound: `b` is false only when some point of
    /// `self` is outside `o`. The bound checks come first so the two
    /// `urem`s only run when the bounds have not already decided.
    fn leq(&self, o: &Self) -> (b: bool)
        ensures
            b <==> forall|c: W| #[trigger] self.gamma(c) ==> o.gamma(c),
    {
        proof {
            self.lemma_contains_bounds();
        }
        if self.lo.eq(self.hi) {
            return o.contains(self.lo);
        }
        if !(o.lo.le(self.lo) && self.hi.le(o.hi)) {
            return false;
        }
        // `o` spans at least `self`'s two distinct bounds, so it is not a
        // singleton and `o.stride > 0`.
        let offset = self.lo.checked_sub(o.lo).expect("o.lo <= self.lo");
        if !offset.urem(o.stride).eq(W::zero()) {
            return false;
        }
        let divides = self.stride.urem(o.stride).eq(W::zero());
        proof {
            if divides {
                Self::lemma_leq_sound(self, o, offset);
            } else if forall|c: W| #[trigger] self.gamma(c) ==> o.gamma(c) {
                Self::lemma_leq_complete(self, o);
            }
        }
        divides
    }

    /// `[min lo, max hi]` on a grid `g` dividing both strides and the
    /// distance between the `lo`s. The best `g` is `gcd(s1, s2, |lo1 - lo2|)`
    /// (Balakrishnan & Reps), which needs `gcd` from #112; until then `g` is
    /// whichever operand's stride works, else 1.
    fn join(&self, o: &Self) -> (r: Self) {
        let abs_diff = if self.lo.le(o.lo) {
            o.lo.checked_sub(self.lo).expect("self.lo <= o.lo")
        } else {
            self.lo.checked_sub(o.lo).expect("o.lo <= self.lo")
        };
        if self.stride.eq(W::zero()) && o.stride.eq(W::zero()) {
            if abs_diff.eq(W::zero()) {
                // the same singleton.
                return self.dup();
            }
            // two distinct singletons: exact as a two-point stride.
            let (lo, hi) = if self.lo.le(o.lo) {
                (self.lo, o.lo)
            } else {
                (o.lo, self.lo)
            };
            let r = StridedInterval { stride: abs_diff, lo, hi };
            proof {
                Self::lemma_join_two_points(self, o, &r);
            }
            return r;
        }
        let g = if !self.stride.eq(W::zero()) && o.stride.urem(self.stride).eq(W::zero())
            && abs_diff.urem(self.stride).eq(W::zero()) {
            self.stride
        } else if !o.stride.eq(W::zero()) && self.stride.urem(o.stride).eq(W::zero())
            && abs_diff.urem(o.stride).eq(W::zero()) {
            o.stride
        } else {
            proof {
                assert(self.stride.view() as int % 1 == 0) by (nonlinear_arith);
                assert(o.stride.view() as int % 1 == 0) by (nonlinear_arith);
                assert(abs_diff.view() as int % 1 == 0) by (nonlinear_arith);
            }
            W::one()
        };
        let lo = if self.lo.le(o.lo) {
            self.lo
        } else {
            o.lo
        };
        let hi = if self.hi.le(o.hi) {
            o.hi
        } else {
            self.hi
        };
        let r = StridedInterval { stride: g, lo, hi };
        proof {
            Self::lemma_join_on_grid(self, o, g.view() as int, abs_diff, &r);
        }
        r
    }

    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        if self.hi.lt(o.lo) || o.hi.lt(self.lo) {
            // Provably disjoint by bounds alone.
            proof {
                assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
            }
            BotOr::Bot
        } else if self.lo.eq(self.hi) {
            if o.contains(self.lo) {
                BotOr::Val(self.dup())
            } else {
                proof {
                    assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
                }
                BotOr::Bot
            }
        } else if o.lo.eq(o.hi) {
            if self.contains(o.lo) {
                BotOr::Val(o.dup())
            } else {
                proof {
                    assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
                }
                BotOr::Bot
            }
        } else if self.stride.eq(o.stride) {
            let abs_diff = if self.lo.le(o.lo) {
                o.lo.checked_sub(self.lo).expect("self.lo <= o.lo")
            } else {
                self.lo.checked_sub(o.lo).expect("o.lo <= self.lo")
            };
            if abs_diff.urem(self.stride).eq(W::zero()) {
                let lo = if self.lo.le(o.lo) {
                    o.lo
                } else {
                    self.lo
                };
                let hi = if self.hi.le(o.hi) {
                    self.hi
                } else {
                    o.hi
                };
                if lo.le(hi) {
                    // A same-residue intersection can still collapse to one
                    // point (e.g. touching at a single value), which must
                    // be re-spelled with stride 0 -- wf forbids stride != 0
                    // with lo == hi.
                    let stride = if lo.eq(hi) { W::zero() } else { self.stride };
                    let r = StridedInterval { stride, lo, hi };
                    proof {
                        Self::lemma_meet_same_stride(self, o, abs_diff, &r);
                    }
                    BotOr::Val(r)
                } else {
                    proof {
                        assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
                    }
                    BotOr::Bot
                }
            } else {
                proof {
                    Self::lemma_residue_mismatch_disjoint(self, o, abs_diff);
                }
                BotOr::Bot
            }
        } else if o.stride.lt(self.stride) {
            Self::meet_unequal_strides(self, o)
        } else {
            let r = Self::meet_unequal_strides(o, self);
            proof {
                match &r {
                    BotOr::Bot => {
                        assert forall|c: W| #[trigger] self.gamma(c) implies !o.gamma(c) by {}
                    },
                    BotOr::Val(m) => {
                        assert forall|c: W| self.gamma(c) && o.gamma(c) implies #[trigger] m.gamma(
                            c,
                        ) by {}
                    },
                }
            }
            r
        }
    }

    /// The usual Cousot move (see `Interval<W>::widen`) on the join's grid:
    /// an unstable bound jumps to the last grid point before the end of the
    /// range instead of to 0/MAX, which would usually be off the grid. The
    /// stride is the join's, so it is kept whenever the join keeps it.
    /// Soundness only, per `doc/domain-traits.md` -- termination is fuel's
    /// job, not widen's.
    fn widen(&self, o: &Self) -> (r: Self) {
        if o.leq(self) {
            return self.dup();
        }
        let j = self.join(o);
        if j.stride.eq(W::zero()) {
            return j;
        }
        let s = j.stride;
        let lo = if j.lo.lt(self.lo) {
            j.lo.urem(s)
        } else {
            j.lo
        };
        let hi_unstable = self.hi.lt(j.hi);
        let hi = if hi_unstable {
            W::max()
        } else {
            j.hi
        };
        proof {
            let q = j.lo.view() as int / (s.view() as int);
            lemma_fundamental_div_mod(j.lo.view() as int, s.view() as int);
            lemma_mod_multiples_basic(q, s.view() as int);
            lemma_mul_is_commutative(s.view() as int, q);
            assert(j.lo.view() as int - j.lo.view() as int % (s.view() as int) == s.view() as int
                * q);
            lemma_mul_nonnegative(s.view() as int, q);
            // `lo` is `j.lo` moved down by a multiple of `s`, so `j`'s grid
            // points are on the grid anchored at `lo`.
            if lo == j.lo {
                lemma_mod_multiples_basic(0, s.view() as int);
            } else {
                assert(j.lo.view() as int - lo.view() as int == s.view() as int * q);
                assert((q * s.view() as int) % (s.view() as int) == 0);
            }
            assert((j.lo.view() as int - lo.view() as int) % (s.view() as int) == 0);
            assert(lo.view() <= j.lo.view());
            j.hi.lemma_view_bounded();
        }
        // Only `W::max()` can be off the grid; a stable `j.hi` is already on it.
        let r = if hi_unstable {
            Self::mk(s, lo, hi)
        } else {
            proof {
                Self::lemma_mod_zero_sum(
                    j.hi.view() as int - j.lo.view() as int,
                    j.lo.view() as int - lo.view() as int,
                    s.view() as int,
                );
            }
            StridedInterval { stride: s, lo, hi }
        };
        proof {
            assert forall|c: W| self.gamma(c) || o.gamma(c) implies #[trigger] r.gamma(c) by {
                assert(j.gamma(c));
                c.lemma_view_bounded();
                Self::lemma_mod_zero_sum(
                    c.view() as int - j.lo.view() as int,
                    j.lo.view() as int - lo.view() as int,
                    s.view() as int,
                );
                assert(c.view() as int - lo.view() as int == (c.view() as int - j.lo.view() as int)
                    + (j.lo.view() as int - lo.view() as int));
            }
        }
        r
    }
}

impl<W: Word> Canonical for StridedInterval<W> {
    proof fn lemma_nonempty(&self) {
        self.lemma_contains_bounds();
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        a.lemma_contains_bounds();
        b.lemma_contains_bounds();
        assert(b.gamma(a.lo) && b.gamma(a.hi));
        assert(a.gamma(b.lo) && a.gamma(b.hi));
        // lo, hi agree: each side's own lo/hi is a member of the other side.
        assert(a.lo.view() <= b.lo.view() && b.lo.view() <= a.lo.view());
        assert(a.hi.view() <= b.hi.view() && b.hi.view() <= a.hi.view());
        W::lemma_view_injective(a.lo, b.lo);
        W::lemma_view_injective(a.hi, b.hi);
        // strides agree.
        if a.lo.view() == a.hi.view() {
            // both singletons (stride == 0) since lo == hi forces it in wf.
            W::lemma_view_injective(a.stride, b.stride);
        } else {
            Self::lemma_stride_le(a, b);
            Self::lemma_stride_le(b, a);
            W::lemma_view_injective(a.stride, b.stride);
        }
    }
}

} // verus!
