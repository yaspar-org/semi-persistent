// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Intervals over unbounded integers.
//!
//! Reference port of an unbounded domain onto the shared traits. Each bound is
//! an enum, so an infinite bound carries no stray number, and there is no
//! empty flag: `lo <= hi` whenever both are finite, and the empty set is
//! `BotOr::Bot`. `[-inf, +inf]` is representable, so the domain has an internal
//! top and needs no Verasco-style `t+⊤` lift.
//!
//! `DivRem<Euclid>` splits a divisor at 0 and takes Euclidean endpoint
//! quotients. `DivRem<Trunc>` is the same split with division toward zero.
//! A finite negative divided by `+∞` is `-1` in the Euclidean quotient and
//! `0` in the truncated one. Remainder uses that quotient when it is a
//! singleton and otherwise `0 <= r < |y|`, cut by `|r| <= |x|` where that
//! holds. Truncation also uses `|r| <= (|x| - 1) / 2` when every `|y| <= |x|`.
//! `Mul` is the endpoint product; `0 * ±∞ = 0`. `min`/`max` of those
//! products borrow the endpoints and copy only the winner.
// Proof-only bindings and lemma imports are erased outside Verus.
#![allow(unused_imports, unused_variables)]
use crate::ibig::*;
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

pub enum Lo {
    NegInf,
    Fin(IBig),
}

pub enum Hi {
    Fin(IBig),
    PosInf,
}

pub open spec fn lo_ok(l: Lo, c: int) -> bool {
    match l {
        Lo::NegInf => true,
        Lo::Fin(a) => a.view() <= c,
    }
}

pub open spec fn hi_ok(h: Hi, c: int) -> bool {
    match h {
        Hi::PosInf => true,
        Hi::Fin(b) => c <= b.view(),
    }
}

/// `a` is a lower bound no greater than `b`.
pub open spec fn lo_leq(a: Lo, b: Lo) -> bool {
    match (a, b) {
        (Lo::NegInf, _) => true,
        (Lo::Fin(_), Lo::NegInf) => false,
        (Lo::Fin(x), Lo::Fin(y)) => x.view() <= y.view(),
    }
}

/// `a` is an upper bound no greater than `b`.
pub open spec fn hi_leq(a: Hi, b: Hi) -> bool {
    match (a, b) {
        (_, Hi::PosInf) => true,
        (Hi::PosInf, Hi::Fin(_)) => false,
        (Hi::Fin(x), Hi::Fin(y)) => x.view() <= y.view(),
    }
}

fn dup_ibig(a: &IBig) -> (r: IBig)
    ensures
        r == *a,
{
    let b = a.dup();
    proof {
        IBig::axiom_view_injective(&b, a);
    }
    b
}

fn dup_lo(l: &Lo) -> (r: Lo)
    ensures
        r == *l,
{
    match l {
        Lo::NegInf => Lo::NegInf,
        Lo::Fin(a) => Lo::Fin(dup_ibig(a)),
    }
}

fn dup_hi(h: &Hi) -> (r: Hi)
    ensures
        r == *h,
{
    match h {
        Hi::PosInf => Hi::PosInf,
        Hi::Fin(a) => Hi::Fin(dup_ibig(a)),
    }
}

fn lo_le(a: &Lo, b: &Lo) -> (r: bool)
    ensures
        r == lo_leq(*a, *b),
        r <==> forall|c: int| #[trigger] lo_ok(*b, c) ==> lo_ok(*a, c),
{
    match (a, b) {
        (Lo::NegInf, _) => true,
        (Lo::Fin(x), Lo::NegInf) => {
            proof {
                assert(lo_ok(*b, x.view() - 1));
            }
            false
        },
        (Lo::Fin(x), Lo::Fin(y)) => {
            proof {
                assert(lo_ok(*b, y.view()));
            }
            x.le(y)
        },
    }
}

fn hi_le(a: &Hi, b: &Hi) -> (r: bool)
    ensures
        r == hi_leq(*a, *b),
        r <==> forall|c: int| #[trigger] hi_ok(*a, c) ==> hi_ok(*b, c),
{
    match (a, b) {
        (_, Hi::PosInf) => true,
        (Hi::PosInf, Hi::Fin(y)) => {
            proof {
                assert(hi_ok(*a, y.view() + 1));
            }
            false
        },
        (Hi::Fin(x), Hi::Fin(y)) => {
            proof {
                assert(hi_ok(*a, x.view()));
            }
            x.le(y)
        },
    }
}

spec fn quot_spec(trunc: bool, x: int, y: int) -> int {
    if trunc {
        tdiv(x, y)
    } else {
        x / y
    }
}

spec fn lo_is(trunc: bool, nlo: Lo, p: int, dhi: Hi, lo: Lo) -> bool {
    match (nlo, lo) {
        (Lo::NegInf, Lo::NegInf) => true,
        (Lo::Fin(a), Lo::Fin(l)) => {
            if a.view() < 0 {
                l.view() == quot_spec(trunc, a.view(), p)
            } else {
                match dhi {
                    Hi::PosInf => l.view() == 0,
                    Hi::Fin(q) => l.view() == quot_spec(trunc, a.view(), q.view()),
                }
            }
        },
        _ => false,
    }
}

spec fn hi_is(trunc: bool, nhi: Hi, p: int, dhi: Hi, hi: Hi) -> bool {
    match (nhi, hi) {
        (Hi::PosInf, Hi::PosInf) => true,
        (Hi::Fin(b), Hi::Fin(h)) => {
            if b.view() < 0 {
                match dhi {
                    Hi::PosInf => h.view() == if trunc {
                        0
                    } else {
                        -1
                    },
                    Hi::Fin(q) => h.view() == quot_spec(trunc, b.view(), q.view()),
                }
            } else {
                h.view() == quot_spec(trunc, b.view(), p)
            }
        },
        _ => false,
    }
}

proof fn lemma_quot_nonneg(trunc: bool, x: int, y: int)
    requires
        x >= 0,
        y > 0,
    ensures
        quot_spec(trunc, x, y) == x / y,
        quot_spec(trunc, x, y) >= 0,
{
    lemma_div_pos_is_pos(x, y);
}

proof fn lemma_quot_num_mono(trunc: bool, a: int, b: int, y: int)
    requires
        a <= b,
        y > 0,
    ensures
        quot_spec(trunc, a, y) <= quot_spec(trunc, b, y),
{
    if trunc {
        if a < 0 && b < 0 {
            lemma_div_is_ordered(-b, -a, y);
            assert(tdiv(a, y) == -((-a) / y));
            assert(tdiv(b, y) == -((-b) / y));
        } else if a < 0 && b >= 0 {
            lemma_div_pos_is_pos(-a, y);
            lemma_div_pos_is_pos(b, y);
            assert(tdiv(a, y) == -((-a) / y));
            assert(tdiv(b, y) == b / y);
        } else {
            lemma_div_is_ordered(a, b, y);
            assert(tdiv(a, y) == a / y);
            assert(tdiv(b, y) == b / y);
        }
    } else {
        lemma_div_is_ordered(a, b, y);
    }
}

proof fn lemma_quot_den_nonneg(trunc: bool, x: int, y: int, z: int)
    requires
        x >= 0,
        1 <= y <= z,
    ensures
        quot_spec(trunc, x, z) <= quot_spec(trunc, x, y),
{
    lemma_quot_nonneg(trunc, x, y);
    lemma_quot_nonneg(trunc, x, z);
    lemma_div_is_ordered_by_denominator(x, y, z);
}

proof fn lemma_quot_den_neg(trunc: bool, x: int, y: int, z: int)
    requires
        x < 0,
        1 <= y <= z,
    ensures
        quot_spec(trunc, x, y) <= quot_spec(trunc, x, z),
{
    if trunc {
        lemma_div_is_ordered_by_denominator(-x, y, z);
        assert(tdiv(x, y) == -((-x) / y));
        assert(tdiv(x, z) == -((-x) / z));
    } else {
        assert(x / y <= x / z) by (nonlinear_arith)
            requires
                x < 0,
                1 <= y <= z,
        ;
    }
}

proof fn lemma_quot_neg_upper(trunc: bool, x: int, y: int)
    requires
        x < 0,
        y >= 1,
    ensures
        quot_spec(trunc, x, y) <= if trunc {
            0
        } else {
            -1
        },
{
    if trunc {
        lemma_div_pos_is_pos(-x, y);
        assert(tdiv(x, y) == -((-x) / y));
    } else {
        lemma_div_is_ordered(x, -1, y);
        assert((-1) / y == -1) by (nonlinear_arith)
            requires
                y >= 1,
        ;
    }
}

proof fn lemma_quot_flip_den(trunc: bool, x: int, d: int)
    requires
        d > 0,
    ensures
        quot_spec(trunc, x, -d) == -quot_spec(trunc, x, d),
{
    if trunc {
        if x >= 0 {
            assert(tdiv(x, d) == x / d);
            assert(tdiv(x, -d) == -(x / d));
        } else {
            assert(tdiv(x, d) == -((-x) / d));
            assert(tdiv(x, -d) == (-x) / d);
        }
    } else {
        assert(x / (-d) == -(x / d)) by (nonlinear_arith)
            requires
                d > 0,
        ;
    }
}

proof fn lemma_div_pos_wf(trunc: bool, nlo: Lo, nhi: Hi, p: int, dhi: Hi, lo: Lo, hi: Hi)
    requires
        p >= 1,
        lo_is(trunc, nlo, p, dhi, lo),
        hi_is(trunc, nhi, p, dhi, hi),
        match dhi {
            Hi::Fin(q) => p <= q.view(),
            Hi::PosInf => true,
        },
        match (nlo, nhi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.view() <= b.view(),
            _ => true,
        },
    ensures
        match (lo, hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.view() <= b.view(),
            _ => true,
        },
{
    match (nlo, nhi, lo, hi) {
        (Lo::Fin(a), Hi::Fin(b), Lo::Fin(l), Hi::Fin(h)) => {
            if a.view() < 0 && b.view() < 0 {
                lemma_quot_num_mono(trunc, a.view(), b.view(), p);
                match dhi {
                    Hi::PosInf => {
                        lemma_quot_neg_upper(trunc, b.view(), p);
                    },
                    Hi::Fin(q) => {
                        lemma_quot_den_neg(trunc, b.view(), p, q.view());
                    },
                }
            } else if a.view() < 0 {
                lemma_quot_num_mono(trunc, a.view(), b.view(), p);
            } else {
                lemma_quot_nonneg(trunc, b.view(), p);
                match dhi {
                    Hi::PosInf => {},
                    Hi::Fin(q) => {
                        lemma_quot_den_nonneg(trunc, a.view(), p, q.view());
                        lemma_quot_num_mono(trunc, a.view(), b.view(), p);
                    },
                }
            }
            assert(l.view() <= h.view());
        },
        _ => {},
    }
}

proof fn lemma_div_pos_sound(trunc: bool, nlo: Lo, nhi: Hi, p: int, dhi: Hi, x: int, y: int, lo: Lo, hi: Hi)
    requires
        p >= 1,
        y >= p,
        hi_ok(dhi, y),
        lo_ok(nlo, x),
        hi_ok(nhi, x),
        lo_is(trunc, nlo, p, dhi, lo),
        hi_is(trunc, nhi, p, dhi, hi),
        match (nlo, nhi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.view() <= b.view(),
            _ => true,
        },
    ensures
        lo_ok(lo, quot_spec(trunc, x, y)),
        hi_ok(hi, quot_spec(trunc, x, y)),
{
    let q = quot_spec(trunc, x, y);
    match nlo {
        Lo::NegInf => {},
        Lo::Fin(a) => {
            if a.view() < 0 {
                lemma_quot_num_mono(trunc, a.view(), x, p);
                if x < 0 {
                    lemma_quot_den_neg(trunc, x, p, y);
                } else {
                    lemma_quot_neg_upper(trunc, a.view(), p);
                    lemma_div_pos_is_pos(x, y);
                }
            } else {
                match dhi {
                    Hi::PosInf => {
                        lemma_div_pos_is_pos(x, y);
                    },
                    Hi::Fin(den) => {
                        lemma_quot_num_mono(trunc, a.view(), x, den.view());
                        lemma_quot_den_nonneg(trunc, x, y, den.view());
                    },
                }
            }
        },
    }
    match (nhi, hi) {
        (Hi::PosInf, Hi::PosInf) => {},
        (Hi::Fin(b), Hi::Fin(h)) => {
            if b.view() < 0 {
                assert(x <= b.view());
                assert(x < 0);
                match dhi {
                    Hi::PosInf => {
                        lemma_quot_neg_upper(trunc, x, y);
                        assert(h.view() == if trunc { 0 } else { -1 });
                        assert(q <= h.view());
                    },
                    Hi::Fin(den) => {
                        assert(y <= den.view());
                        lemma_quot_num_mono(trunc, x, b.view(), y);
                        lemma_quot_den_neg(trunc, b.view(), y, den.view());
                        assert(h.view() == quot_spec(trunc, b.view(), den.view()));
                        assert(q <= quot_spec(trunc, b.view(), y));
                        assert(quot_spec(trunc, b.view(), y) <= h.view());
                        assert(q <= h.view());
                    },
                }
            } else {
                assert(h.view() == quot_spec(trunc, b.view(), p));
                if x >= 0 {
                    lemma_quot_den_nonneg(trunc, x, p, y);
                    lemma_quot_num_mono(trunc, x, b.view(), p);
                    assert(q <= quot_spec(trunc, x, p));
                    assert(quot_spec(trunc, x, p) <= h.view());
                } else {
                    lemma_quot_neg_upper(trunc, x, y);
                    lemma_quot_nonneg(trunc, b.view(), p);
                    assert(h.view() >= 0);
                }
                assert(q <= h.view());
            }
        },
        _ => {
            assert(false);
        },
    }
    assert(lo_ok(lo, q));
    assert(hi_ok(hi, q));
}

spec fn min2(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn max2(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn min4(a: int, b: int, c: int, d: int) -> int {
    min2(min2(a, b), min2(c, d))
}

spec fn max4(a: int, b: int, c: int, d: int) -> int {
    max2(max2(a, b), max2(c, d))
}

/// Compare first and copy nothing. The caller copies only the winner.
fn min_ibig<'a>(a: &'a IBig, b: &'a IBig) -> (r: &'a IBig)
    ensures
        r.view() == min2(a.view(), b.view()),
{
    if a.le(b) { a } else { b }
}

fn max_ibig<'a>(a: &'a IBig, b: &'a IBig) -> (r: &'a IBig)
    ensures
        r.view() == max2(a.view(), b.view()),
{
    if a.le(b) { b } else { a }
}

proof fn lemma_lo_point(a: Lo, b: Lo)
    ensures
        lo_leq(a, b) ==> forall|c: int| #[trigger] lo_ok(b, c) ==> lo_ok(a, c),
        !lo_leq(a, b) ==> exists|c: int| lo_ok(b, c) && !lo_ok(a, c),
{
    match (a, b) {
        (Lo::NegInf, _) => {},
        (Lo::Fin(x), Lo::NegInf) => {
            assert(lo_ok(b, x.view() - 1));
            assert(!lo_ok(a, x.view() - 1));
        },
        (Lo::Fin(x), Lo::Fin(y)) => {
            if x.view() <= y.view() {
                assert forall|c: int| #[trigger] lo_ok(b, c) implies lo_ok(a, c) by {
                    assert(x.view() <= y.view());
                }
            } else {
                assert(lo_ok(b, y.view()));
                assert(!lo_ok(a, y.view()));
            }
        },
    }
}

proof fn lemma_hi_point(a: Hi, b: Hi)
    ensures
        hi_leq(a, b) ==> forall|c: int| #[trigger] hi_ok(a, c) ==> hi_ok(b, c),
        !hi_leq(a, b) ==> exists|c: int| hi_ok(a, c) && !hi_ok(b, c),
{
    match (a, b) {
        (_, Hi::PosInf) => {},
        (Hi::PosInf, Hi::Fin(y)) => {
            assert(hi_ok(a, y.view() + 1));
            assert(!hi_ok(b, y.view() + 1));
        },
        (Hi::Fin(x), Hi::Fin(y)) => {
            if x.view() <= y.view() {
                assert forall|c: int| #[trigger] hi_ok(a, c) implies hi_ok(b, c) by {
                    assert(x.view() <= y.view());
                }
            } else {
                assert(hi_ok(a, x.view()));
                assert(!hi_ok(b, x.view()));
            }
        },
    }
}

proof fn lemma_euclid_rem_range(x: int, y: int)
    requires
        y != 0,
    ensures
        0 <= x % y < iabs(y),
{
    if y > 0 {
        lemma_mod_bound(x, y);
    } else {
        lemma_mod_bound(x, -y);
        lemma_fundamental_div_mod(x, y);
        lemma_fundamental_div_mod(x, -y);
        assert(x / (-y) == -(x / y)) by (nonlinear_arith)
            requires
                y < 0,
        ;
        assert((x / (-y)) * (-y) == (x / y) * y) by (nonlinear_arith)
            requires
                y < 0,
                x / (-y) == -(x / y),
        ;
    }
}

proof fn lemma_trem_range(x: int, y: int)
    requires
        y != 0,
    ensures
        x >= 0 ==> 0 <= trem(x, y) < iabs(y),
        x < 0 ==> -iabs(y) < trem(x, y) <= 0,
        iabs(trem(x, y)) == iabs(x) % iabs(y),
{
    let ax = iabs(x);
    let ay = iabs(y);
    assert(ay > 0);
    lemma_mod_bound(ax, ay);
    lemma_fundamental_div_mod(ax, ay);
    if x >= 0 && y > 0 {
        assert(tdiv(x, y) == x / y);
        assert(trem(x, y) == x % y);
        assert(ax == x && ay == y);
        assert(iabs(trem(x, y)) == ax % ay);
    } else if x >= 0 && y < 0 {
        assert(tdiv(x, y) == -(x / (-y)));
        assert(trem(x, y) == x % (-y)) by (nonlinear_arith)
            requires
                y < 0,
                tdiv(x, y) == -(x / (-y)),
        ;
        assert(ax == x && ay == -y);
        assert(0 <= trem(x, y));
        assert(iabs(trem(x, y)) == ax % ay);
    } else if x < 0 && y > 0 {
        assert(tdiv(x, y) == -((-x) / y));
        assert(trem(x, y) == -((-x) % y)) by (nonlinear_arith)
            requires
                x < 0,
                y > 0,
                tdiv(x, y) == -((-x) / y),
        ;
        assert(ax == -x && ay == y);
        assert(trem(x, y) <= 0);
        assert(iabs(trem(x, y)) == ax % ay);
    } else {
        assert(x < 0 && y < 0);
        assert(tdiv(x, y) == (-x) / (-y));
        assert(trem(x, y) == -((-x) % (-y))) by (nonlinear_arith)
            requires
                x < 0,
                y < 0,
                tdiv(x, y) == (-x) / (-y),
        ;
        assert(ax == -x && ay == -y);
        assert(trem(x, y) <= 0);
        assert(iabs(trem(x, y)) == ax % ay);
    }
}

/// A nonnegative integer modulo a positive integer is at most itself.
proof fn lemma_mod_le_self(n: int, k: int)
    requires
        n >= 0,
        k > 0,
    ensures
        n % k <= n,
{
    lemma_mod_bound(n, k);
    if n < k {
        lemma_small_mod(n as nat, k as nat);
        assert(n % k == n);
    } else {
        assert(n % k < k && k <= n);
        assert(n % k <= n);
    }
}

/// `|trem(x, y)| <= |x|`. Toward-zero division never makes a larger remainder.
proof fn lemma_trem_abs_le_x(x: int, y: int)
    requires
        y != 0,
    ensures
        iabs(trem(x, y)) <= iabs(x),
{
    let ax = iabs(x);
    let ay = iabs(y);
    lemma_trem_range(x, y);
    assert(ay > 0 && ax >= 0);
    lemma_mod_le_self(ax, ay);
    assert(iabs(trem(x, y)) == ax % ay);
}

/// Euclidean remainder of a nonnegative dividend is at most the dividend.
proof fn lemma_euclid_rem_le_x(x: int, y: int)
    requires
        y != 0,
        x >= 0,
    ensures
        0 <= x % y <= x,
{
    lemma_euclid_rem_range(x, y);
    lemma_fundamental_div_mod(x, y);
    assert(x == y * (x / y) + (x % y));
    if y > 0 {
        assert(x / y >= 0) by (nonlinear_arith)
            requires
                x >= 0,
                y > 0,
        ;
        assert(y * (x / y) >= 0) by (nonlinear_arith)
            requires
                y > 0,
                x / y >= 0,
        ;
    } else {
        assert(x / y <= 0) by (nonlinear_arith)
            requires
                x >= 0,
                y < 0,
        ;
        assert(y * (x / y) >= 0) by (nonlinear_arith)
            requires
                y < 0,
                x / y <= 0,
        ;
    }
    assert(x % y <= x) by (nonlinear_arith)
        requires
            x == y * (x / y) + (x % y),
            y * (x / y) >= 0,
    ;
}

/// For `1 <= k <= n`, `n % k` never exceeds `floor((n - 1) / 2)`.
proof fn lemma_pos_rem_half(n: int, k: int)
    requires
        n > 0,
        k > 0,
        k <= n,
    ensures
        n % k <= (n - 1) / 2,
{
    lemma_mod_bound(n, k);
    lemma_fundamental_div_mod(n, k);
    let q = n / k;
    let r = n % k;
    assert(n == k * q + r);
    assert(q >= 1) by (nonlinear_arith)
        requires
            n == k * q + r,
            n >= k,
            k > 0,
            r >= 0,
            r < k,
    ;
    if q >= 2 {
        assert(k * q <= n) by (nonlinear_arith)
            requires
                n == k * q + r,
                r >= 0,
        ;
        assert(2 * k <= n) by (nonlinear_arith)
            requires
                q >= 2,
                k > 0,
                k * q <= n,
        ;
        assert(r <= k - 1) by (nonlinear_arith)
            requires
                r < k,
        ;
        assert(2 * r <= n - 2) by (nonlinear_arith)
            requires
                r <= k - 1,
                2 * k <= n,
                r >= 0,
        ;
        assert(r <= (n - 1) / 2) by (nonlinear_arith)
            requires
                2 * r <= n - 2,
                r >= 0,
        ;
    } else {
        assert(q == 1);
        assert(r == n - k) by (nonlinear_arith)
            requires
                n == k * q + r,
                q == 1,
        ;
        assert(n < 2 * k) by (nonlinear_arith)
            requires
                r == n - k,
                r < k,
        ;
        assert(2 * k >= n + 1) by (nonlinear_arith)
            requires
                n < 2 * k,
        ;
        assert(2 * r <= n - 1) by (nonlinear_arith)
            requires
                r == n - k,
                2 * k >= n + 1,
        ;
        assert(r <= (n - 1) / 2) by (nonlinear_arith)
            requires
                2 * r <= n - 1,
                r >= 0,
        ;
    }
}

proof fn lemma_half_mono(a: int, b: int)
    requires
        0 <= a <= b,
    ensures
        (a - 1) / 2 <= (b - 1) / 2,
{
    assert((a - 1) / 2 <= (b - 1) / 2) by (nonlinear_arith)
        requires
            a <= b,
            0 <= a,
    ;
}

proof fn lemma_abs_fits(t: int, b: int)
    requires
        iabs(t) <= b,
    ensures
        -b <= t <= b,
{
    if t >= 0 {
        assert(iabs(t) == t);
    } else {
        assert(iabs(t) == -t);
    }
}

/// Smallest absolute value of an integer in `[lo, hi]`.
spec fn min_abs_of(lo: int, hi: int) -> int {
    if lo <= 0 && 0 <= hi {
        0
    } else if hi < 0 {
        -hi
    } else {
        lo
    }
}

proof fn lemma_min_abs(lo: int, hi: int, x: int)
    requires
        lo <= x <= hi,
    ensures
        min_abs_of(lo, hi) <= iabs(x),
{
    if lo <= 0 && 0 <= hi {
        assert(min_abs_of(lo, hi) == 0);
    } else if hi < 0 {
        assert(x < 0);
        assert(iabs(x) == -x);
        assert(min_abs_of(lo, hi) == -hi);
        assert(-hi <= -x);
    } else {
        assert(lo > 0);
        assert(x > 0);
        assert(iabs(x) == x);
        assert(min_abs_of(lo, hi) == lo);
    }
}

proof fn lemma_abs_le_ends(lo: int, hi: int, y: int)
    requires
        lo <= y <= hi,
    ensures
        iabs(y) <= max2(iabs(lo), iabs(hi)),
{
    if y >= 0 {
        assert(hi >= 0);
        assert(iabs(y) == y);
        assert(iabs(hi) == hi);
    } else {
        assert(lo < 0);
        assert(iabs(y) == -y);
        assert(iabs(lo) == -lo);
        assert(-y <= -lo);
    }
}

proof fn lemma_affine_hull(a: int, b: int, c: int, d: int, q: int, x: int, y: int)
    requires
        a <= x <= b,
        c <= y <= d,
    ensures
        min4(a - q * c, a - q * d, b - q * c, b - q * d) <= x - q * y,
        x - q * y <= max4(a - q * c, a - q * d, b - q * c, b - q * d),
{
    assert(a - q * y <= x - q * y && x - q * y <= b - q * y) by (nonlinear_arith)
        requires
            a <= x <= b,
    ;
    let ac = a - q * c;
    let ad = a - q * d;
    let bc = b - q * c;
    let bd = b - q * d;
    if q >= 0 {
        assert(a - q * d <= a - q * y && a - q * y <= a - q * c) by (nonlinear_arith)
            requires
                c <= y <= d,
                q >= 0,
        ;
        assert(b - q * d <= b - q * y && b - q * y <= b - q * c) by (nonlinear_arith)
            requires
                c <= y <= d,
                q >= 0,
        ;
        assert(ad == a - q * d && ac == a - q * c && bd == b - q * d && bc == b - q * c);
    } else {
        assert(a - q * c <= a - q * y && a - q * y <= a - q * d) by (nonlinear_arith)
            requires
                c <= y <= d,
                q < 0,
        ;
        assert(b - q * c <= b - q * y && b - q * y <= b - q * d) by (nonlinear_arith)
            requires
                c <= y <= d,
                q < 0,
        ;
        assert(ad == a - q * d && ac == a - q * c && bd == b - q * d && bc == b - q * c);
    }
    assert(min2(ac, ad) <= a - q * y && a - q * y <= max2(ac, ad));
    assert(min2(bc, bd) <= b - q * y && b - q * y <= max2(bc, bd));
    assert(min4(ac, ad, bc, bd) <= min2(ac, ad));
    assert(max2(bc, bd) <= max4(ac, ad, bc, bd));
    assert(min4(ac, ad, bc, bd) <= x - q * y);
    assert(x - q * y <= max4(ac, ad, bc, bd));
}

proof fn lemma_straddle_mul(a: int, b: int, c: int, d: int, x: int, y: int)
    requires
        a <= x <= b,
        c <= y <= d,
        a < 0 < b,
        c < 0 < d,
    ensures
        min2(a * d, b * c) <= x * y <= max2(a * c, b * d),
{
    if y >= 0 {
        assert(a * d <= x * y && x * y <= b * d) by (nonlinear_arith)
            requires
                a <= x <= b,
                0 <= y <= d,
                a < 0,
                b > 0,
        ;
        assert(min2(a * d, b * c) <= a * d);
        assert(b * d <= max2(a * c, b * d));
    } else {
        assert(b * c <= x * y && x * y <= a * c) by (nonlinear_arith)
            requires
                a <= x <= b,
                c <= y < 0,
                a < 0,
                b > 0,
                c < 0,
        ;
        assert(min2(a * d, b * c) <= b * c);
        assert(a * c <= max2(a * c, b * d));
    }
}

enum Class {
    NonNeg,
    NonPos,
    Mixed,
}

spec fn nonneg_lo(i: IntervalZ) -> bool {
    match i.lo() {
        Lo::Fin(a) => a.view() >= 0,
        Lo::NegInf => false,
    }
}

spec fn nonpos_hi(i: IntervalZ) -> bool {
    match i.hi() {
        Hi::Fin(b) => b.view() <= 0,
        Hi::PosInf => false,
    }
}

spec fn both_fin(i: IntervalZ) -> bool {
    &&& i.lo() is Fin
    &&& i.hi() is Fin
}

spec fn rem_spec(trunc: bool, x: int, y: int) -> int {
    if trunc {
        trem(x, y)
    } else {
        x % y
    }
}

proof fn lemma_rem_spec_def(trunc: bool, x: int, y: int)
    ensures
        trunc ==> rem_spec(trunc, x, y) == trem(x, y),
        !trunc ==> rem_spec(trunc, x, y) == x % y,
{
    reveal(rem_spec);
}

/// `{x | lo <= x <= hi}`.
pub struct IntervalZ {
    lo: Lo,
    hi: Hi,
}

impl IntervalZ {
    pub closed spec fn lo(&self) -> Lo {
        self.lo
    }

    pub closed spec fn hi(&self) -> Hi {
        self.hi
    }

    pub fn new(lo: Lo, hi: Hi) -> (r: Option<Self>)
        ensures
            match r {
                Some(i) => i.wf() && i.lo() == lo && i.hi() == hi,
                None => match (lo, hi) {
                    (Lo::Fin(a), Hi::Fin(b)) => a.view() > b.view(),
                    _ => false,
                },
            },
    {
        let ok = match (&lo, &hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.le(b),
            _ => true,
        };
        if ok {
            Some(IntervalZ { lo, hi })
        } else {
            None
        }
    }

    pub fn constant(c: IBig) -> (r: Self)
        ensures
            r.wf(),
            forall|x: int| #[trigger] r.gamma(x) <==> x == c.view(),
    {
        IntervalZ { lo: Lo::Fin(dup_ibig(&c)), hi: Hi::Fin(c) }
    }

    fn add_int(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: int, y: int| self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(x + y),
    {
        let lo = match (&self.lo, &o.lo) {
            (Lo::Fin(a), Lo::Fin(b)) => Lo::Fin(a.add(b)),
            _ => Lo::NegInf,
        };
        let hi = match (&self.hi, &o.hi) {
            (Hi::Fin(a), Hi::Fin(b)) => Hi::Fin(a.add(b)),
            _ => Hi::PosInf,
        };
        IntervalZ { lo, hi }
    }

    fn neg_int(&self) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            forall|x: int| self.gamma(x) ==> #[trigger] r.gamma(-x),
            match (self.hi(), r.lo()) {
                (Hi::Fin(b), Lo::Fin(a)) => a.view() == -b.view(),
                (Hi::PosInf, Lo::NegInf) => true,
                _ => false,
            },
    {
        let lo = match &self.hi {
            Hi::Fin(b) => Lo::Fin(b.neg()),
            Hi::PosInf => Lo::NegInf,
        };
        let hi = match &self.lo {
            Lo::Fin(a) => Hi::Fin(a.neg()),
            Lo::NegInf => Hi::PosInf,
        };
        IntervalZ { lo, hi }
    }

    fn sub_int(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: int, y: int| self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(x - y),
    {
        let n = o.neg_int();
        let r = self.add_int(&n);
        proof {
            assert forall|x: int, y: int| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                x - y,
            ) by {
                assert(n.gamma(-y));
                assert(r.gamma(x + (-y)));
            }
        }
        r
    }

    /// `Never` excludes 0, `Always` is exactly `{0}`, and both directions hold.
    fn classify(d: &Self) -> (f: DivZero)
        requires
            d.wf(),
        ensures
            f is Never <==> !d.gamma(0),
            f is Always <==> forall|y: int| #[trigger] d.gamma(y) ==> y == 0,
    {
        let zero_singleton = match (&d.lo, &d.hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.is_zero() && b.is_zero(),
            _ => false,
        };
        if zero_singleton {
            proof {
                assert forall|y: int| #[trigger] d.gamma(y) implies y == 0 by {
                    assert(lo_ok(d.lo, y) && hi_ok(d.hi, y));
                }
            }
            DivZero::Always
        } else if d.contains_zero_int() {
            proof {
                assert(d.gamma(0));
                match &d.lo {
                    Lo::Fin(a) => {
                        if a.view() < 0 {
                            assert(d.gamma(a.view()));
                        } else {
                            match &d.hi {
                                Hi::Fin(b) => {
                                    assert(d.gamma(b.view()));
                                },
                                Hi::PosInf => {
                                    assert(d.gamma(1));
                                },
                            }
                        }
                    },
                    Lo::NegInf => {
                        assert(d.gamma(-1));
                    },
                }
            }
            DivZero::Maybe
        } else {
            proof {
                d.lemma_nonempty();
            }
            DivZero::Never
        }
    }

    fn contains_zero_int(&self) -> (b: bool)
        requires
            self.wf(),
        ensures
            b == self.gamma(0),
    {
        let lo_ok0 = match &self.lo {
            Lo::NegInf => true,
            Lo::Fin(a) => {
                let z = IBig::from_i64(0);
                a.le(&z)
            },
        };
        let hi_ok0 = match &self.hi {
            Hi::PosInf => true,
            Hi::Fin(b) => {
                let z = IBig::from_i64(0);
                z.le(b)
            },
        };
        lo_ok0 && hi_ok0
    }

    fn quot(n: &IBig, d: &IBig, trunc: bool) -> (r: IBig)
        requires
            d.view() != 0,
        ensures
            r.view() == quot_spec(trunc, n.view(), d.view()),
    {
        if trunc {
            n.div_trunc(d)
        } else {
            n.div_euclid(d)
        }
    }

    /// Quotient by a divisor whose lower bound is at least 1.
    fn div_pos(&self, d: &Self, trunc: bool) -> (r: Self)
        requires
            self.wf(),
            d.wf(),
            match d.lo() {
                Lo::Fin(a) => a.view() >= 1,
                Lo::NegInf => false,
            },
        ensures
            r.wf(),
            forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) ==> #[trigger] r.gamma(quot_spec(trunc, x, y)),
    {
        match &d.lo {
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                Self::top()
            },
            Lo::Fin(p) => {
                let zero = IBig::from_i64(0);
                let lo = match &self.lo {
                    Lo::NegInf => Lo::NegInf,
                    Lo::Fin(a) => {
                        if a.le(&zero) && !a.is_zero() {
                            Lo::Fin(Self::quot(a, p, trunc))
                        } else {
                            match &d.hi {
                                Hi::PosInf => Lo::Fin(IBig::from_i64(0)),
                                Hi::Fin(q) => Lo::Fin(Self::quot(a, q, trunc)),
                            }
                        }
                    },
                };
                let hi = match &self.hi {
                    Hi::PosInf => Hi::PosInf,
                    Hi::Fin(b) => {
                        if b.le(&zero) && !b.is_zero() {
                            match &d.hi {
                                Hi::PosInf => {
                                    if trunc {
                                        Hi::Fin(IBig::from_i64(0))
                                    } else {
                                        Hi::Fin(IBig::from_i64(-1))
                                    }
                                },
                                Hi::Fin(q) => Hi::Fin(Self::quot(b, q, trunc)),
                            }
                        } else {
                            Hi::Fin(Self::quot(b, p, trunc))
                        }
                    },
                };
                proof {
                    assert(p.view() >= 1);
                    match d.hi() {
                        Hi::Fin(q) => {
                            assert(p.view() <= q.view());
                        },
                        Hi::PosInf => {},
                    }
                    assert(lo_is(trunc, self.lo(), p.view(), d.hi(), lo));
                    assert(hi_is(trunc, self.hi(), p.view(), d.hi(), hi));
                    lemma_div_pos_wf(trunc, self.lo(), self.hi(), p.view(), d.hi(), lo, hi);
                    assert(match (lo, hi) {
                        (Lo::Fin(a), Hi::Fin(b)) => a.view() <= b.view(),
                        _ => true,
                    });
                    assert forall|x: int, y: int|
                        self.gamma(x) && d.gamma(y) implies #[trigger] lo_ok(
                        lo,
                        quot_spec(trunc, x, y),
                    ) && hi_ok(hi, quot_spec(trunc, x, y)) by {
                        lemma_div_pos_sound(
                            trunc,
                            self.lo(),
                            self.hi(),
                            p.view(),
                            d.hi(),
                            x,
                            y,
                            lo,
                            hi,
                        );
                    }
                }
                IntervalZ { lo, hi }
            },
        }
    }

    /// Requires a divisor that does not contain 0. Private, so a caller cannot
    /// drop the nonzero premise.
    fn div_nonzero(&self, d: &Self, trunc: bool) -> (r: Self)
        requires
            self.wf(),
            d.wf(),
            !d.gamma(0),
        ensures
            r.wf(),
            forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) ==> #[trigger] r.gamma(quot_spec(trunc, x, y)),
    {
        let minus_one = IBig::from_i64(-1);
        match &d.hi {
            Hi::Fin(b) if b.le(&minus_one) => {
                let n = IntervalZ {
                    lo: Lo::Fin(b.neg()),
                    hi: match &d.lo {
                        Lo::Fin(a) => Hi::Fin(a.neg()),
                        Lo::NegInf => Hi::PosInf,
                    },
                };
                proof {
                    match &n.lo {
                        Lo::Fin(a) => {
                            assert(a.view() == -b.view());
                            assert(a.view() >= 1);
                        },
                        Lo::NegInf => {
                            assert(false);
                        },
                    }
                }
                let q = self.div_pos(&n, trunc);
                let r = q.neg_int();
                proof {
                    assert forall|x: int, y: int|
                        self.gamma(x) && d.gamma(y) implies #[trigger] r.gamma(quot_spec(
                        trunc,
                        x,
                        y,
                    )) by {
                        assert(y <= b.view());
                        assert(-y >= 1);
                        assert(n.gamma(-y));
                        lemma_quot_flip_den(trunc, x, -y);
                        assert(q.gamma(quot_spec(trunc, x, -y)));
                        assert(r.gamma(-quot_spec(trunc, x, -y)));
                    }
                }
                r
            },
            _ => {
                proof {
                    match d.lo() {
                        Lo::Fin(a) => {
                            assert(a.view() >= 1);
                        },
                        Lo::NegInf => {
                            assert(false);
                        },
                    }
                }
                self.div_pos(d, trunc)
            },
        }
    }

    fn pos_part(d: &Self) -> (r: Option<Self>)
        requires
            d.wf(),
        ensures
            match r {
                Some(v) => {
                    &&& v.wf()
                    &&& !v.gamma(0)
                    &&& match v.lo() {
                        Lo::Fin(a) => a.view() >= 1,
                        Lo::NegInf => false,
                    }
                    &&& forall|y: int| d.gamma(y) && y >= 1 ==> #[trigger] v.gamma(y)
                },
                None => forall|y: int| #[trigger] d.gamma(y) ==> y < 1,
            },
    {
        let one = IBig::from_i64(1);
        let lo = match &d.lo {
            Lo::NegInf => Lo::Fin(IBig::from_i64(1)),
            Lo::Fin(a) => if one.le(a) {
                Lo::Fin(a.dup())
            } else {
                Lo::Fin(IBig::from_i64(1))
            },
        };
        let hi = dup_hi(&d.hi);
        let r = IntervalZ::new(lo, hi);
        proof {
            match &r {
                Some(v) => {
                    assert(!v.gamma(0));
                    assert forall|y: int| d.gamma(y) && y >= 1 implies #[trigger] v.gamma(y) by {
                        assert(lo_ok(v.lo(), y));
                        assert(hi_ok(v.hi(), y));
                    }
                },
                None => {
                    assert forall|y: int| #[trigger] d.gamma(y) implies y < 1 by {
                        if y >= 1 {
                            assert(false);
                        }
                    }
                },
            }
        }
        r
    }

    fn neg_part(d: &Self) -> (r: Option<Self>)
        requires
            d.wf(),
        ensures
            match r {
                Some(v) => {
                    &&& v.wf()
                    &&& !v.gamma(0)
                    &&& match v.hi() {
                        Hi::Fin(b) => b.view() <= -1,
                        Hi::PosInf => false,
                    }
                    &&& forall|y: int| d.gamma(y) && y <= -1 ==> #[trigger] v.gamma(y)
                },
                None => forall|y: int| #[trigger] d.gamma(y) ==> y > -1,
            },
    {
        let lo = dup_lo(&d.lo);
        let hi = Hi::Fin(IBig::from_i64(-1));
        let r = IntervalZ::new(lo, hi);
        proof {
            match &r {
                Some(v) => {
                    assert(!v.gamma(0));
                    assert forall|y: int| d.gamma(y) && y <= -1 implies #[trigger] v.gamma(y) by {
                        assert(lo_ok(v.lo(), y));
                        assert(hi_ok(v.hi(), y));
                    }
                },
                None => {
                    assert forall|y: int| #[trigger] d.gamma(y) implies y > -1 by {
                        if y <= -1 {
                            assert(false);
                        }
                    }
                },
            }
        }
        r
    }

    fn div_general(&self, d: &Self, trunc: bool) -> (r: (BotOr<Self>, DivZero))
        requires
            self.wf(),
            d.wf(),
        ensures
            r.0.wf(),
            forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) && y != 0 ==> #[trigger] r.0.gamma(quot_spec(trunc, x, y)),
            r.1 is Never <==> !d.gamma(0),
            r.1 is Always <==> forall|y: int| #[trigger] d.gamma(y) ==> y == 0,
            (r.0 is Bot) <==> (r.1 is Always),
    {
        let flag = Self::classify(d);
        match flag {
            DivZero::Always => (BotOr::Bot, DivZero::Always),
            DivZero::Never => (BotOr::Val(self.div_nonzero(d, trunc)), DivZero::Never),
            DivZero::Maybe => {
                let neg = Self::neg_part(d);
                let pos = Self::pos_part(d);
                let q = match (neg, pos) {
                    (Some(n), Some(p)) => {
                        let qn = self.div_nonzero(&n, trunc);
                        let qp = self.div_nonzero(&p, trunc);
                        let q = qn.join(&qp);
                        proof {
                            assert forall|x: int, y: int|
                                self.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] q.gamma(
                                quot_spec(trunc, x, y),
                            ) by {
                                if y <= -1 {
                                    assert(n.gamma(y));
                                    assert(qn.gamma(quot_spec(trunc, x, y)));
                                } else {
                                    assert(p.gamma(y));
                                    assert(qp.gamma(quot_spec(trunc, x, y)));
                                }
                            }
                        }
                        q
                    },
                    (Some(n), None) => self.div_nonzero(&n, trunc),
                    (None, Some(p)) => self.div_nonzero(&p, trunc),
                    (None, None) => {
                        proof {
                            assert(false);
                        }
                        Self::top()
                    },
                };
                (BotOr::Val(q), DivZero::Maybe)
            },
        }
    }

    fn is_zero_iv(i: &IntervalZ) -> (b: bool)
        requires
            i.wf(),
        ensures
            b == (match (i.lo(), i.hi()) {
                (Lo::Fin(a), Hi::Fin(c)) => a.view() == 0 && c.view() == 0,
                _ => false,
            }),
    {
        match (&i.lo, &i.hi) {
            (Lo::Fin(a), Hi::Fin(c)) => a.is_zero() && c.is_zero(),
            _ => false,
        }
    }

    fn class_of(i: &IntervalZ) -> (c: Class)
        requires
            i.wf(),
        ensures
            c is NonNeg ==> nonneg_lo(*i),
            c is NonPos ==> nonpos_hi(*i),
            c is Mixed ==> !nonneg_lo(*i) && !nonpos_hi(*i),
    {
        let z = IBig::from_i64(0);
        match &i.lo {
            Lo::Fin(a) if z.le(a) => Class::NonNeg,
            _ => match &i.hi {
                Hi::Fin(b) if b.le(&z) => Class::NonPos,
                _ => Class::Mixed,
            },
        }
    }

    fn ends_fin(i: &IntervalZ) -> (b: bool)
        ensures
            b == both_fin(*i),
    {
        matches!((&i.lo, &i.hi), (Lo::Fin(_), Hi::Fin(_)))
    }

    fn mul_nn(a: &IntervalZ, b: &IntervalZ) -> (r: IntervalZ)
        requires
            a.wf(),
            b.wf(),
            nonneg_lo(*a),
            nonneg_lo(*b),
        ensures
            r.wf(),
            forall|x: int, y: int| a.gamma(x) && b.gamma(y) ==> #[trigger] r.gamma(x * y),
    {
        let alo = match &a.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let blo = match &b.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let lo_b = alo.mul(blo);
        let hi = match (&a.hi, &b.hi) {
            (Hi::Fin(ah), Hi::Fin(bh)) => Hi::Fin(ah.mul(bh)),
            (Hi::Fin(ah), Hi::PosInf) => if ah.is_zero() {
                Hi::Fin(IBig::from_i64(0))
            } else {
                Hi::PosInf
            },
            (Hi::PosInf, Hi::Fin(bh)) => if bh.is_zero() {
                Hi::Fin(IBig::from_i64(0))
            } else {
                Hi::PosInf
            },
            (Hi::PosInf, Hi::PosInf) => Hi::PosInf,
        };
        let lo = Lo::Fin(lo_b);
        proof {
            let (av, bv) = (alo.view(), blo.view());
            assert(av >= 0 && bv >= 0);
            assert forall|x: int, y: int|
                #[trigger] a.gamma(x) && #[trigger] b.gamma(y) implies lo_ok(lo, x * y) && hi_ok(hi, x * y)
            by {
                assert(av <= x && bv <= y);
                assert(lo_b.view() == av * bv);
                assert(av * bv <= x * y) by (nonlinear_arith)
                    requires
                        0 <= av <= x,
                        0 <= bv <= y,
                ;
                assert(lo_ok(lo, x * y));
                match (&a.hi, &b.hi) {
                    (Hi::Fin(ah), Hi::Fin(bh)) => {
                        let (ahv, bhv) = (ah.view(), bh.view());
                        assert(0 <= x <= ahv && 0 <= y <= bhv);
                        assert(x * y <= ahv * bhv) by (nonlinear_arith)
                            requires
                                0 <= x <= ahv,
                                0 <= y <= bhv,
                        ;
                        match &hi {
                            Hi::Fin(h) => {
                                assert(h.view() == ahv * bhv);
                            },
                            Hi::PosInf => {
                                assert(false);
                            },
                        }
                    },
                    (Hi::Fin(ah), Hi::PosInf) => {
                        if ah.view() == 0 {
                            assert(x == 0);
                            assert(x * y == 0) by (nonlinear_arith)
                                requires
                                    x == 0,
                            ;
                            match &hi {
                                Hi::Fin(h) => {
                                    assert(h.view() == 0);
                                },
                                Hi::PosInf => {
                                    assert(false);
                                },
                            }
                        } else {
                            match &hi {
                                Hi::PosInf => {},
                                Hi::Fin(_) => {
                                    assert(false);
                                },
                            }
                        }
                    },
                    (Hi::PosInf, Hi::Fin(bh)) => {
                        if bh.view() == 0 {
                            assert(y == 0);
                            assert(x * y == 0) by (nonlinear_arith)
                                requires
                                    y == 0,
                            ;
                            match &hi {
                                Hi::Fin(h) => {
                                    assert(h.view() == 0);
                                },
                                Hi::PosInf => {
                                    assert(false);
                                },
                            }
                        } else {
                            match &hi {
                                Hi::PosInf => {},
                                Hi::Fin(_) => {
                                    assert(false);
                                },
                            }
                        }
                    },
                    (Hi::PosInf, Hi::PosInf) => {
                        match &hi {
                            Hi::PosInf => {},
                            Hi::Fin(_) => {
                                assert(false);
                            },
                        }
                    },
                }
                assert(hi_ok(hi, x * y));
            }
            match (&a.hi, &b.hi) {
                (Hi::Fin(ah), Hi::Fin(bh)) => {
                    assert(av * bv <= ah.view() * bh.view()) by (nonlinear_arith)
                        requires
                            0 <= av <= ah.view(),
                            0 <= bv <= bh.view(),
                    ;
                },
                (Hi::Fin(ah), Hi::PosInf) => {
                    if ah.view() == 0 {
                        assert(av == 0);
                        assert(av * bv == 0) by (nonlinear_arith)
                            requires
                                av == 0,
                        ;
                    }
                },
                (Hi::PosInf, Hi::Fin(bh)) => {
                    if bh.view() == 0 {
                        assert(bv == 0);
                        assert(av * bv == 0) by (nonlinear_arith)
                            requires
                                bv == 0,
                        ;
                    }
                },
                _ => {},
            }
        }
        let r = IntervalZ { lo, hi };
        proof {
            assert forall|x: int, y: int| #[trigger] a.gamma(x) && #[trigger] b.gamma(y) implies r.gamma(x * y)
            by {
                assert(lo_ok(lo, x * y) && hi_ok(hi, x * y));
            }
        }
        r
    }

    fn mul_np(a: &IntervalZ, b: &IntervalZ) -> (r: IntervalZ)
        requires
            a.wf(),
            b.wf(),
            nonneg_lo(*a),
            nonpos_hi(*b),
        ensures
            r.wf(),
            forall|x: int, y: int| a.gamma(x) && b.gamma(y) ==> #[trigger] r.gamma(x * y),
    {
        let alo = match &a.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let bhi = match &b.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let hi_b = alo.mul(bhi);
        let lo = match (&a.hi, &b.lo) {
            (Hi::Fin(ah), Lo::Fin(bl)) => Lo::Fin(ah.mul(bl)),
            (Hi::Fin(ah), Lo::NegInf) => if ah.is_zero() {
                Lo::Fin(IBig::from_i64(0))
            } else {
                Lo::NegInf
            },
            (Hi::PosInf, _) => Lo::NegInf,
        };
        let hi = Hi::Fin(hi_b);
        proof {
            let (av, dv) = (alo.view(), bhi.view());
            assert(av >= 0 && dv <= 0);
            assert forall|x: int, y: int|
                #[trigger] a.gamma(x) && #[trigger] b.gamma(y) implies lo_ok(lo, x * y) && hi_ok(hi, x * y)
            by {
                assert(av <= x && y <= dv);
                assert(hi_b.view() == av * dv);
                assert(x * y <= av * dv) by (nonlinear_arith)
                    requires
                        av <= x,
                        y <= dv <= 0,
                        av >= 0,
                ;
                assert(hi_ok(hi, x * y));
                match (&a.hi, &b.lo) {
                    (Hi::Fin(ah), Lo::Fin(bl)) => {
                        let (bv, cv) = (ah.view(), bl.view());
                        assert(x <= bv && cv <= y);
                        assert(bv * cv <= x * y) by (nonlinear_arith)
                            requires
                                0 <= av <= x <= bv,
                                cv <= y <= dv <= 0,
                        ;
                        match &lo {
                            Lo::Fin(l) => {
                                assert(l.view() == bv * cv);
                            },
                            Lo::NegInf => {
                                assert(false);
                            },
                        }
                        assert(lo_ok(lo, x * y));
                    },
                    (Hi::Fin(ah), Lo::NegInf) => {
                        if ah.view() == 0 {
                            assert(x == 0);
                            assert(x * y == 0) by (nonlinear_arith)
                                requires
                                    x == 0,
                            ;
                        }
                    },
                    (Hi::PosInf, _) => {},
                }
            }
            match (&a.hi, &b.lo) {
                (Hi::Fin(ah), Lo::Fin(bl)) => {
                    assert(ah.view() * bl.view() <= av * dv) by (nonlinear_arith)
                        requires
                            0 <= av <= ah.view(),
                            bl.view() <= dv <= 0,
                    ;
                },
                (Hi::Fin(ah), Lo::NegInf) => {
                    if ah.view() == 0 {
                        assert(av == 0);
                        assert(av * dv == 0) by (nonlinear_arith)
                            requires
                                av == 0,
                        ;
                    }
                },
                _ => {},
            }
        }
        let r = IntervalZ { lo, hi };
        proof {
            assert forall|x: int, y: int| #[trigger] a.gamma(x) && #[trigger] b.gamma(y) implies r.gamma(x * y)
            by {
                assert(lo_ok(lo, x * y) && hi_ok(hi, x * y));
            }
        }
        r
    }

    fn mul_neg(a: &IntervalZ, b: &IntervalZ) -> (r: IntervalZ)
        requires
            a.wf(),
            b.wf(),
            nonpos_hi(*a),
            nonpos_hi(*b),
        ensures
            r.wf(),
            forall|x: int, y: int| a.gamma(x) && b.gamma(y) ==> #[trigger] r.gamma(x * y),
    {
        let ahi = match &a.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let bhi = match &b.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let lo_b = ahi.mul(bhi);
        let hi = match (&a.lo, &b.lo) {
            (Lo::Fin(al), Lo::Fin(bl)) => Hi::Fin(al.mul(bl)),
            _ => Hi::PosInf,
        };
        let lo = Lo::Fin(lo_b);
        proof {
            let (av, bv) = (ahi.view(), bhi.view());
            assert(av <= 0 && bv <= 0);
            assert forall|x: int, y: int|
                a.gamma(x) && b.gamma(y) implies #[trigger] lo_ok(lo, x * y) && hi_ok(
                hi,
                x * y,
            ) by {
                assert(x <= av && y <= bv);
                assert(lo_b.view() == av * bv);
                assert(av * bv <= x * y) by (nonlinear_arith)
                    requires
                        x <= av <= 0,
                        y <= bv <= 0,
                ;
                assert(lo_ok(lo, x * y));
                match (&a.lo, &b.lo) {
                    (Lo::Fin(al), Lo::Fin(bl)) => {
                        let (alv, blv) = (al.view(), bl.view());
                        assert(alv <= x && blv <= y);
                        assert(x * y <= alv * blv) by (nonlinear_arith)
                            requires
                                alv <= x <= av <= 0,
                                blv <= y <= bv <= 0,
                        ;
                        match &hi {
                            Hi::Fin(h) => {
                                assert(h.view() == alv * blv);
                            },
                            Hi::PosInf => {
                                assert(false);
                            },
                        }
                    },
                    _ => {
                        match &hi {
                            Hi::PosInf => {},
                            Hi::Fin(_) => {
                                assert(false);
                            },
                        }
                    },
                }
                assert(hi_ok(hi, x * y));
            }
            match (&a.lo, &b.lo) {
                (Lo::Fin(al), Lo::Fin(bl)) => {
                    assert(av * bv <= al.view() * bl.view()) by (nonlinear_arith)
                        requires
                            al.view() <= av <= 0,
                            bl.view() <= bv <= 0,
                    ;
                },
                _ => {},
            }
        }
        IntervalZ { lo, hi }
    }

    fn mul_nm(a: &IntervalZ, b: &IntervalZ) -> (r: IntervalZ)
        requires
            a.wf(),
            b.wf(),
            nonneg_lo(*a),
            !nonneg_lo(*b),
            !nonpos_hi(*b),
        ensures
            r.wf(),
            forall|x: int, y: int| a.gamma(x) && b.gamma(y) ==> #[trigger] r.gamma(x * y),
    {
        match &a.hi {
            Hi::PosInf => IntervalZ::top(),
            Hi::Fin(ah) => {
                if ah.is_zero() {
                    let z = IBig::from_i64(0);
                    let r = IntervalZ::constant(z);
                    proof {
                        assert(ah.view() == 0);
                        assert forall|x: int, y: int|
                            a.gamma(x) && b.gamma(y) implies #[trigger] r.gamma(x * y) by {
                            assert(x == 0);
                            assert(x * y == 0) by (nonlinear_arith)
                                requires
                                    x == 0,
                            ;
                        }
                    }
                    return r;
                }
                let lo = match &b.lo {
                    Lo::NegInf => Lo::NegInf,
                    Lo::Fin(bl) => Lo::Fin(ah.mul(bl)),
                };
                let hi = match &b.hi {
                    Hi::PosInf => Hi::PosInf,
                    Hi::Fin(bh) => Hi::Fin(ah.mul(bh)),
                };
                proof {
                    let bv = ah.view();
                    assert(bv > 0);
                    assert forall|x: int, y: int|
                        #[trigger] a.gamma(x) && #[trigger] b.gamma(y) implies lo_ok(lo, x * y)
                            && hi_ok(hi, x * y) by {
                        assert(0 <= x <= bv);
                        match (&b.lo, &b.hi) {
                            (Lo::Fin(bl), Hi::Fin(bh)) => {
                                let (cv, dv) = (bl.view(), bh.view());
                                assert(cv < 0 < dv);
                                assert(bv * cv <= x * y && x * y <= bv * dv) by (nonlinear_arith)
                                    requires
                                        0 <= x <= bv,
                                        cv <= y <= dv,
                                        bv > 0,
                                        cv < 0,
                                        dv > 0,
                                ;
                                match (&lo, &hi) {
                                    (Lo::Fin(l), Hi::Fin(h)) => {
                                        assert(l.view() == bv * cv && h.view() == bv * dv);
                                    },
                                    _ => {
                                        assert(false);
                                    },
                                }
                            },
                            (Lo::NegInf, Hi::Fin(bh)) => {
                                let dv = bh.view();
                                assert(dv > 0 && y <= dv);
                                assert(x * y <= bv * dv) by (nonlinear_arith)
                                    requires
                                        0 <= x <= bv,
                                        y <= dv,
                                        bv > 0,
                                        dv > 0,
                                ;
                                match &hi {
                                    Hi::Fin(h) => {
                                        assert(h.view() == bv * dv);
                                    },
                                    Hi::PosInf => {
                                        assert(false);
                                    },
                                }
                            },
                            (Lo::Fin(bl), Hi::PosInf) => {
                                let cv = bl.view();
                                assert(cv < 0 && cv <= y);
                                assert(bv * cv <= x * y) by (nonlinear_arith)
                                    requires
                                        0 <= x <= bv,
                                        cv <= y,
                                        bv > 0,
                                        cv < 0,
                                ;
                                match &lo {
                                    Lo::Fin(l) => {
                                        assert(l.view() == bv * cv);
                                    },
                                    Lo::NegInf => {
                                        assert(false);
                                    },
                                }
                            },
                            (Lo::NegInf, Hi::PosInf) => {},
                        }
                        assert(lo_ok(lo, x * y) && hi_ok(hi, x * y));
                    }
                    match (&b.lo, &b.hi) {
                        (Lo::Fin(bl), Hi::Fin(bh)) => {
                            assert(bv * bl.view() <= bv * bh.view()) by (nonlinear_arith)
                                requires
                                    bv > 0,
                                    bl.view() < 0 < bh.view(),
                            ;
                        },
                        _ => {},
                    }
                }
                let r = IntervalZ { lo, hi };
                proof {
                    assert forall|x: int, y: int|
                        #[trigger] a.gamma(x) && #[trigger] b.gamma(y) implies r.gamma(x * y) by {
                        assert(lo_ok(lo, x * y) && hi_ok(hi, x * y));
                    }
                }
                r
            },
        }
    }

    fn mul_mm(a: &IntervalZ, b: &IntervalZ) -> (r: IntervalZ)
        requires
            a.wf(),
            b.wf(),
            !nonneg_lo(*a) && !nonpos_hi(*a),
            !nonneg_lo(*b) && !nonpos_hi(*b),
        ensures
            r.wf(),
            forall|x: int, y: int| a.gamma(x) && b.gamma(y) ==> #[trigger] r.gamma(x * y),
    {
        if !Self::ends_fin(a) || !Self::ends_fin(b) {
            return IntervalZ::top();
        }
        let av = match &a.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let bv = match &a.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let cv = match &b.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let dv = match &b.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let ad = av.mul(dv);
        let bc = bv.mul(cv);
        let ac = av.mul(cv);
        let bd = bv.mul(dv);
        let lo_r = min_ibig(&ad, &bc);
        let hi_r = max_ibig(&ac, &bd);
        let lo = Lo::Fin(dup_ibig(lo_r));
        let hi = Hi::Fin(dup_ibig(hi_r));
        proof {
            let (a0, b0, c0, d0) = (av.view(), bv.view(), cv.view(), dv.view());
            assert(a0 < 0 < b0 && c0 < 0 < d0);
            assert(ad.view() == a0 * d0 && bc.view() == b0 * c0);
            assert(ac.view() == a0 * c0 && bd.view() == b0 * d0);
            assert(lo_r.view() == min2(ad.view(), bc.view()));
            assert(hi_r.view() == max2(ac.view(), bd.view()));
            assert(a0 * d0 <= 0 && b0 * c0 <= 0) by (nonlinear_arith)
                requires
                    a0 < 0,
                    d0 > 0,
                    b0 > 0,
                    c0 < 0,
            ;
            assert(a0 * c0 >= 0 && b0 * d0 >= 0) by (nonlinear_arith)
                requires
                    a0 < 0,
                    c0 < 0,
                    b0 > 0,
                    d0 > 0,
            ;
            assert forall|x: int, y: int|
                a.gamma(x) && b.gamma(y) implies #[trigger] lo_ok(lo, x * y) && hi_ok(
                hi,
                x * y,
            ) by {
                lemma_straddle_mul(a0, b0, c0, d0, x, y);
            }
        }
        IntervalZ { lo, hi }
    }

    fn mul_int(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: int, y: int| self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(x * y),
    {
        let zself = Self::is_zero_iv(self);
        let zo = Self::is_zero_iv(o);
        if zself || zo {
            let z = IBig::from_i64(0);
            let r = IntervalZ::constant(z);
            proof {
                assert forall|x: int, y: int| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                    x * y,
                ) by {
                    if zself {
                        assert(x == 0);
                    } else {
                        assert(y == 0);
                    }
                    assert(x * y == 0) by (nonlinear_arith)
                        requires
                            x == 0 || y == 0,
                    ;
                }
            }
            r
        } else {
            match (Self::class_of(self), Self::class_of(o)) {
                (Class::NonNeg, Class::NonNeg) => Self::mul_nn(self, o),
                (Class::NonNeg, Class::NonPos) => Self::mul_np(self, o),
                (Class::NonPos, Class::NonNeg) => {
                    let r = Self::mul_np(o, self);
                    proof {
                        assert forall|x: int, y: int|
                            self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(x * y) by {
                            assert(r.gamma(y * x));
                            assert(y * x == x * y) by (nonlinear_arith);
                        }
                    }
                    r
                },
                (Class::NonPos, Class::NonPos) => Self::mul_neg(self, o),
                (Class::NonNeg, Class::Mixed) => Self::mul_nm(self, o),
                (Class::Mixed, Class::NonNeg) => {
                    let r = Self::mul_nm(o, self);
                    proof {
                        assert forall|x: int, y: int|
                            self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(x * y) by {
                            assert(r.gamma(y * x));
                            assert(y * x == x * y) by (nonlinear_arith);
                        }
                    }
                    r
                },
                (Class::NonPos, Class::Mixed) => {
                    let ns = self.neg_int();
                    proof {
                        reveal(nonneg_lo);
                        reveal(nonpos_hi);
                        match (self.hi(), ns.lo()) {
                            (Hi::Fin(b), Lo::Fin(a)) => {
                                assert(b.view() <= 0);
                                assert(a.view() >= 0);
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                    let p = Self::mul_nm(&ns, o);
                    let r = p.neg_int();
                    proof {
                        assert(nonneg_lo(ns));
                        assert forall|x: int, y: int|
                            self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(x * y) by {
                            assert(ns.gamma(-x));
                            lemma_mul_unary_negation(x, y);
                            assert(p.gamma((-x) * y));
                            let z = -(x * y);
                            assert((-x) * y == z);
                            assert(p.gamma(z));
                            assert(r.gamma(-z));
                            assert(-z == x * y);
                        }
                    }
                    r
                },
                (Class::Mixed, Class::NonPos) => {
                    let ns = o.neg_int();
                    proof {
                        reveal(nonneg_lo);
                        reveal(nonpos_hi);
                        match (o.hi(), ns.lo()) {
                            (Hi::Fin(b), Lo::Fin(a)) => {
                                assert(b.view() <= 0);
                                assert(a.view() >= 0);
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                    let p = Self::mul_nm(&ns, self);
                    let r = p.neg_int();
                    proof {
                        assert(nonneg_lo(ns));
                        assert forall|x: int, y: int|
                            self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(x * y) by {
                            assert(ns.gamma(-y));
                            lemma_mul_unary_negation(y, x);
                            lemma_mul_is_commutative(x, y);
                            assert(p.gamma((-y) * x));
                            let z = -(x * y);
                            assert((-y) * x == z);
                            assert(p.gamma(z));
                            assert(r.gamma(-z));
                            assert(-z == x * y);
                        }
                    }
                    r
                },
                (Class::Mixed, Class::Mixed) => Self::mul_mm(self, o),
            }
        }
    }

    /// The intersection, exactly: an interval meet loses nothing.
    pub fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: int| #[trigger] r.gamma(c) <==> self.gamma(c) && o.gamma(c),
    {
        let lo = if lo_le(&self.lo, &o.lo) {
            dup_lo(&o.lo)
        } else {
            dup_lo(&self.lo)
        };
        let hi = if hi_le(&self.hi, &o.hi) {
            dup_hi(&self.hi)
        } else {
            dup_hi(&o.hi)
        };
        let ok = match (&lo, &hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.le(b),
            _ => true,
        };
        if ok {
            let v = IntervalZ { lo, hi };
            proof {
                lemma_lo_point(self.lo, o.lo);
                lemma_lo_point(o.lo, self.lo);
                lemma_lo_total(self.lo, o.lo);
                lemma_hi_point(self.hi, o.hi);
                lemma_hi_point(o.hi, self.hi);
                lemma_hi_total(self.hi, o.hi);
                assert forall|c: int| self.gamma(c) && o.gamma(c) implies #[trigger] v.gamma(c) by {
                    assert(lo_ok(lo, c) && hi_ok(hi, c));
                }
                assert forall|c: int| #[trigger] v.gamma(c) implies self.gamma(c) && o.gamma(c) by {
                    if lo_leq(self.lo, o.lo) {
                        assert(lo == o.lo);
                        assert(lo_ok(self.lo, c));
                    } else {
                        assert(lo_leq(o.lo, self.lo));
                        assert(lo == self.lo);
                        assert(lo_ok(o.lo, c));
                    }
                    if hi_leq(self.hi, o.hi) {
                        assert(hi == self.hi);
                        assert(hi_ok(o.hi, c));
                    } else {
                        assert(hi_leq(o.hi, self.hi));
                        assert(hi == o.hi);
                        assert(hi_ok(self.hi, c));
                    }
                }
            }
            BotOr::Val(v)
        } else {
            proof {
                assert forall|c: int| self.gamma(c) && o.gamma(c) implies false by {
                    assert(lo_ok(lo, c) && hi_ok(hi, c));
                }
            }
            BotOr::Bot
        }
    }

    /// Replace an infinite endpoint of `self` by the same endpoint of `t`.
    /// Crossed bounds are `Bot`. Every value in both intervals survives, and
    /// every surviving value was already in `self`.
    pub fn narrow(&self, t: &Self) -> (r: BotOr<Self>)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            forall|c: int| #[trigger] r.gamma(c) ==> self.gamma(c),
            forall|c: int| self.gamma(c) && t.gamma(c) ==> #[trigger] r.gamma(c),
    {
        let lo = match &self.lo {
            Lo::NegInf => dup_lo(&t.lo),
            Lo::Fin(_) => dup_lo(&self.lo),
        };
        let hi = match &self.hi {
            Hi::PosInf => dup_hi(&t.hi),
            Hi::Fin(_) => dup_hi(&self.hi),
        };
        let ok = match (&lo, &hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.le(b),
            _ => true,
        };
        if ok {
            let v = IntervalZ { lo, hi };
            proof {
                assert forall|c: int| #[trigger] v.gamma(c) implies self.gamma(c) by {
                    assert(lo_ok(self.lo(), c));
                    assert(hi_ok(self.hi(), c));
                }
                assert forall|c: int| self.gamma(c) && t.gamma(c) implies #[trigger] v.gamma(c) by {
                    assert(lo_ok(v.lo(), c));
                    assert(hi_ok(v.hi(), c));
                }
            }
            BotOr::Val(v)
        } else {
            proof {
                assert forall|c: int| self.gamma(c) && t.gamma(c) implies false by {
                    assert(lo_ok(lo, c) && hi_ok(hi, c));
                }
            }
            BotOr::Bot
        }
    }

    /// One meet, unless the budget is 0. The result contains exactly the values
    /// that satisfy both intervals when fuel is spent, and it never grows.
    pub fn refine(&self, fact: &Self, budget: u8) -> (r: (BotOr<Self>, u8))
        requires
            self.wf(),
            fact.wf(),
        ensures
            r.0.wf(),
            forall|c: int| #[trigger] r.0.gamma(c) ==> self.gamma(c),
            budget == 0 ==> r.0 == BotOr::Val(*self) && r.1 == 0,
            budget > 0 ==> forall|c: int|
                #[trigger] r.0.gamma(c) <==> self.gamma(c) && fact.gamma(c),
    {
        if budget == 0 {
            (BotOr::Val(self.dup()), 0)
        } else {
            let m = self.meet_exact(fact);
            let same = match &m {
                BotOr::Bot => false,
                BotOr::Val(v) => self.leq(v) && v.leq(self),
            };
            let fuel = if same { budget } else { budget - 1 };
            proof {
                assert forall|c: int| #[trigger] m.gamma(c) implies self.gamma(c) by {
                    if m.gamma(c) {
                        assert(self.gamma(c) && fact.gamma(c));
                    }
                }
            }
            (m, fuel)
        }
    }

    fn abs_of(a: &IBig) -> (r: IBig)
        ensures
            r.view() == iabs(a.view()),
    {
        let z = IBig::from_i64(0);
        if a.le(&z) && !a.is_zero() {
            a.neg()
        } else {
            a.dup()
        }
    }

    fn max_abs_fin(i: &IntervalZ) -> (r: IBig)
        requires
            i.wf(),
            both_fin(*i),
        ensures
            match (i.lo(), i.hi()) {
                (Lo::Fin(a), Hi::Fin(b)) => r.view() == max2(iabs(a.view()), iabs(b.view()))
                    && r.view() >= 0,
                _ => false,
            },
    {
        let a = match &i.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IBig::from_i64(0);
            },
        };
        let b = match &i.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IBig::from_i64(0);
            },
        };
        let aa = Self::abs_of(a);
        let bb = Self::abs_of(b);
        let m = max_ibig(&aa, &bb);
        proof {
            assert(m.view() >= 0);
        }
        dup_ibig(m)
    }

    fn min_abs_fin(i: &IntervalZ) -> (r: IBig)
        requires
            i.wf(),
            both_fin(*i),
        ensures
            match (i.lo(), i.hi()) {
                (Lo::Fin(a), Hi::Fin(b)) => r.view() == min_abs_of(a.view(), b.view()),
                _ => false,
            },
    {
        let z = IBig::from_i64(0);
        let a = match &i.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IBig::from_i64(0);
            },
        };
        let b = match &i.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IBig::from_i64(0);
            },
        };
        if a.le(&z) && z.le(b) {
            proof {
                assert(min_abs_of(a.view(), b.view()) == 0);
            }
            z
        } else if b.le(&z) && !b.is_zero() {
            proof {
                assert(b.view() < 0);
                assert(min_abs_of(a.view(), b.view()) == -b.view());
            }
            b.neg()
        } else {
            proof {
                assert(a.view() > 0);
                assert(min_abs_of(a.view(), b.view()) == a.view());
            }
            a.dup()
        }
    }

    fn quot_singleton(q: &IntervalZ) -> (r: Option<IBig>)
        requires
            q.wf(),
        ensures
            match r {
                Some(v) => forall|c: int| #[trigger] q.gamma(c) <==> c == v.view(),
                None => true,
            },
    {
        match (&q.lo, &q.hi) {
            (Lo::Fin(a), Hi::Fin(b)) => {
                if a.le(b) && b.le(a) {
                    let v = a.dup();
                    proof {
                        assert(a.view() == b.view());
                        IBig::axiom_view_injective(&v, a);
                        assert forall|c: int| #[trigger] q.gamma(c) implies c == v.view() by {
                            assert(a.view() <= c && c <= b.view());
                        }
                        assert forall|c: int| c == v.view() implies #[trigger] q.gamma(c) by {
                            assert(a.view() <= c && c <= b.view());
                        }
                    }
                    Some(v)
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    fn rem_affine(n: &IntervalZ, d: &IntervalZ, q: &IBig) -> (r: IntervalZ)
        requires
            n.wf(),
            d.wf(),
            both_fin(*n),
            both_fin(*d),
        ensures
            r.wf(),
            forall|x: int, y: int|
                n.gamma(x) && d.gamma(y) ==> #[trigger] r.gamma(x - y * q.view()),
    {
        let a = match &n.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let b = match &n.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let c = match &d.lo {
            Lo::Fin(v) => v,
            Lo::NegInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let e = match &d.hi {
            Hi::Fin(v) => v,
            Hi::PosInf => {
                proof {
                    assert(false);
                }
                return IntervalZ::top();
            },
        };
        let c1 = a.sub(&q.mul(c));
        let c2 = a.sub(&q.mul(e));
        let c3 = b.sub(&q.mul(c));
        let c4 = b.sub(&q.mul(e));
        let lo12 = min_ibig(&c1, &c2);
        let lo34 = min_ibig(&c3, &c4);
        let hi12 = max_ibig(&c1, &c2);
        let hi34 = max_ibig(&c3, &c4);
        let lo_r = min_ibig(lo12, lo34);
        let hi_r = max_ibig(hi12, hi34);
        let lo = Lo::Fin(dup_ibig(lo_r));
        let hi = Hi::Fin(dup_ibig(hi_r));
        proof {
            let qv = q.view();
            let (av, bv, cv, ev) = (a.view(), b.view(), c.view(), e.view());
            assert(c1.view() == av - qv * cv);
            assert(c2.view() == av - qv * ev);
            assert(c3.view() == bv - qv * cv);
            assert(c4.view() == bv - qv * ev);
            assert(lo_r.view() == min4(c1.view(), c2.view(), c3.view(), c4.view()));
            assert(hi_r.view() == max4(c1.view(), c2.view(), c3.view(), c4.view()));
            assert forall|x: int, y: int| n.gamma(x) && d.gamma(y) implies #[trigger] lo_ok(
                lo,
                x - y * qv,
            ) && hi_ok(hi, x - y * qv) by {
                lemma_affine_hull(av, bv, cv, ev, qv, x, y);
            }
        }
        IntervalZ { lo, hi }
    }

    /// Upper bound on `|r|`: the divisor magnitude, cut by `|r| <= |x|` when that
    /// is sound. Truncation also uses `(|x| - 1) / 2` once every `|y| <= |x|`.
    fn rem_cap(n: &IntervalZ, mm1: &IBig, m: &IBig, trunc: bool) -> (c: IBig)
        requires
            n.wf(),
            mm1.view() == m.view() - 1,
            m.view() >= 1,
        ensures
            c.view() >= 0,
            c.view() <= mm1.view(),
            forall|x: int, y: int|
                #![trigger rem_spec(trunc, x, y)]
                n.gamma(x) && y != 0 && iabs(y) <= m.view() ==> iabs(rem_spec(trunc, x, y))
                    <= c.view(),
    {
        if trunc && Self::ends_fin(n) {
            let xmax = Self::max_abs_fin(n);
            let xmin = Self::min_abs_fin(n);
            if m.le(&xmin) && !xmax.is_zero() {
                let one = IBig::from_i64(1);
                let two = IBig::from_i64(2);
                proof {
                    assert(xmax.view() >= 0);
                    assert(xmax.view() != 0);
                    assert(xmax.view() >= 1);
                }
                let half = xmax.sub(&one).div_euclid(&two);
                let c = dup_ibig(min_ibig(mm1, &half));
                proof {
                    assert(half.view() == (xmax.view() - 1) / 2);
                    assert(c.view() == min2(mm1.view(), half.view()));
                    assert(half.view() >= 0) by (nonlinear_arith)
                        requires
                            xmax.view() >= 1,
                            half.view() == (xmax.view() - 1) / 2,
                    ;
                    assert(c.view() >= 0);
                    assert forall|x: int, y: int|
                        #![trigger rem_spec(trunc, x, y)]
                        n.gamma(x) && y != 0 && iabs(y) <= m.view() implies iabs(
                        rem_spec(trunc, x, y),
                    ) <= c.view() by {
                        lemma_rem_spec_def(trunc, x, y);
                        lemma_trem_range(x, y);
                        lemma_trem_abs_le_x(x, y);
                        match (n.lo(), n.hi()) {
                            (Lo::Fin(a), Hi::Fin(b)) => {
                                assert(a.view() <= x && x <= b.view());
                                lemma_abs_le_ends(a.view(), b.view(), x);
                                lemma_min_abs(a.view(), b.view(), x);
                                assert(iabs(x) >= xmin.view());
                                assert(m.view() <= xmin.view());
                                assert(iabs(y) <= iabs(x));
                                assert(iabs(x) >= 1);
                                lemma_pos_rem_half(iabs(x), iabs(y));
                                lemma_half_mono(iabs(x), xmax.view());
                                assert(iabs(trem(x, y)) <= half.view());
                                assert(iabs(trem(x, y)) < iabs(y));
                                assert(iabs(trem(x, y)) <= mm1.view());
                                assert(iabs(trem(x, y)) <= c.view());
                                assert(iabs(rem_spec(trunc, x, y)) <= c.view());
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                }
                c
            } else {
                let c = dup_ibig(min_ibig(mm1, &xmax));
                proof {
                    assert(c.view() == min2(mm1.view(), xmax.view()));
                    assert(c.view() >= 0);
                    assert forall|x: int, y: int|
                        #![trigger rem_spec(trunc, x, y)]
                        n.gamma(x) && y != 0 && iabs(y) <= m.view() implies iabs(
                        rem_spec(trunc, x, y),
                    ) <= c.view() by {
                        lemma_rem_spec_def(trunc, x, y);
                        lemma_trem_range(x, y);
                        lemma_trem_abs_le_x(x, y);
                        match (n.lo(), n.hi()) {
                            (Lo::Fin(a), Hi::Fin(b)) => {
                                assert(a.view() <= x && x <= b.view());
                                lemma_abs_le_ends(a.view(), b.view(), x);
                                assert(iabs(x) <= xmax.view());
                                assert(iabs(trem(x, y)) <= xmax.view());
                                assert(iabs(trem(x, y)) < iabs(y));
                                assert(iabs(trem(x, y)) <= mm1.view());
                                assert(iabs(trem(x, y)) <= c.view());
                                assert(iabs(rem_spec(trunc, x, y)) <= c.view());
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                }
                c
            }
        } else if !trunc && matches!(Self::class_of(n), Class::NonNeg) {
            match &n.hi {
                Hi::Fin(h) => {
                    let c = dup_ibig(min_ibig(mm1, h));
                    proof {
                        assert(c.view() >= 0);
                        assert(c.view() <= mm1.view());
                        assert forall|x: int, y: int|
                            #![trigger rem_spec(trunc, x, y)]
                            n.gamma(x) && y != 0 && iabs(y) <= m.view() implies iabs(
                            rem_spec(trunc, x, y),
                        ) <= c.view() by {
                            lemma_rem_spec_def(trunc, x, y);
                            assert(x >= 0);
                            lemma_euclid_rem_le_x(x, y);
                            lemma_euclid_rem_range(x, y);
                            assert(x <= h.view());
                            assert(x % y <= c.view());
                            assert(iabs(x % y) == x % y);
                            assert(iabs(rem_spec(trunc, x, y)) <= c.view());
                        }
                    }
                    c
                },
                Hi::PosInf => {
                    let c = mm1.dup();
                    proof {
                        assert forall|x: int, y: int|
                            #![trigger rem_spec(trunc, x, y)]
                            n.gamma(x) && y != 0 && iabs(y) <= m.view() implies iabs(
                            rem_spec(trunc, x, y),
                        ) <= c.view() by {
                            lemma_rem_spec_def(trunc, x, y);
                            lemma_euclid_rem_range(x, y);
                            assert(x % y < m.view());
                            assert(iabs(x % y) == x % y);
                            assert(iabs(rem_spec(trunc, x, y)) <= c.view());
                        }
                    }
                    c
                },
            }
        } else {
            let c = mm1.dup();
            proof {
                assert forall|x: int, y: int|
                    #![trigger rem_spec(trunc, x, y)]
                    n.gamma(x) && y != 0 && iabs(y) <= m.view() implies iabs(rem_spec(trunc, x, y))
                    <= c.view() by {
                    lemma_rem_spec_def(trunc, x, y);
                    if trunc {
                        lemma_trem_range(x, y);
                        assert(iabs(trem(x, y)) < iabs(y));
                        assert(iabs(trem(x, y)) <= mm1.view());
                        assert(iabs(rem_spec(trunc, x, y)) <= c.view());
                    } else {
                        lemma_euclid_rem_range(x, y);
                        assert(x % y < m.view());
                        assert(iabs(x % y) == x % y);
                        assert(iabs(rem_spec(trunc, x, y)) <= c.view());
                    }
                }
            }
            c
        }
    }

    fn rem_fallback(n: &IntervalZ, d: &IntervalZ, trunc: bool) -> (r: IntervalZ)
        requires
            n.wf(),
            d.wf(),
            exists|y: int| d.gamma(y) && y != 0,
        ensures
            r.wf(),
            forall|x: int, y: int|
                n.gamma(x) && d.gamma(y) && y != 0 ==> #[trigger] r.gamma(rem_spec(trunc, x, y)),
    {
        if !Self::ends_fin(d) {
            if !trunc {
                if matches!(Self::class_of(n), Class::NonNeg) {
                    match &n.hi {
                        Hi::Fin(h) => {
                            let hv = h.dup();
                            let r = IntervalZ { lo: Lo::Fin(IBig::from_i64(0)), hi: Hi::Fin(hv) };
                            proof {
                                assert forall|x: int, y: int|
                                    n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                    x % y,
                                ) by {
                                    assert(x >= 0);
                                    lemma_euclid_rem_le_x(x, y);
                                    assert(x <= h.view());
                                }
                            }
                            r
                        },
                        Hi::PosInf => {
                            let r = IntervalZ { lo: Lo::Fin(IBig::from_i64(0)), hi: Hi::PosInf };
                            proof {
                                assert forall|x: int, y: int|
                                    n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                    x % y,
                                ) by {
                                    lemma_euclid_rem_range(x, y);
                                }
                            }
                            r
                        },
                    }
                } else {
                    let r = IntervalZ { lo: Lo::Fin(IBig::from_i64(0)), hi: Hi::PosInf };
                    proof {
                        assert forall|x: int, y: int|
                            n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(x % y) by {
                            lemma_euclid_rem_range(x, y);
                        }
                    }
                    r
                }
            } else if Self::ends_fin(n) {
                let xmax = Self::max_abs_fin(n);
                let lo_neg = IBig::from_i64(0).sub(&xmax);
                match Self::class_of(n) {
                    Class::NonNeg => {
                        let r = IntervalZ { lo: Lo::Fin(IBig::from_i64(0)), hi: Hi::Fin(xmax) };
                        proof {
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                assert(x >= 0);
                                lemma_trem_range(x, y);
                                lemma_trem_abs_le_x(x, y);
                                match (n.lo(), n.hi()) {
                                    (Lo::Fin(a), Hi::Fin(b)) => {
                                        lemma_abs_le_ends(a.view(), b.view(), x);
                                    },
                                    _ => {
                                        assert(false);
                                    },
                                }
                                lemma_abs_fits(trem(x, y), xmax.view());
                            }
                        }
                        r
                    },
                    Class::NonPos => {
                        let r = IntervalZ { lo: Lo::Fin(lo_neg), hi: Hi::Fin(IBig::from_i64(0)) };
                        proof {
                            assert(lo_neg.view() == -xmax.view());
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                assert(x <= 0);
                                lemma_trem_range(x, y);
                                lemma_trem_abs_le_x(x, y);
                                match (n.lo(), n.hi()) {
                                    (Lo::Fin(a), Hi::Fin(b)) => {
                                        lemma_abs_le_ends(a.view(), b.view(), x);
                                    },
                                    _ => {
                                        assert(false);
                                    },
                                }
                                lemma_abs_fits(trem(x, y), xmax.view());
                            }
                        }
                        r
                    },
                    Class::Mixed => {
                        let hi_b = xmax.dup();
                        let r = IntervalZ { lo: Lo::Fin(lo_neg), hi: Hi::Fin(hi_b) };
                        proof {
                            assert(lo_neg.view() == -xmax.view());
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                lemma_trem_range(x, y);
                                lemma_trem_abs_le_x(x, y);
                                match (n.lo(), n.hi()) {
                                    (Lo::Fin(a), Hi::Fin(b)) => {
                                        lemma_abs_le_ends(a.view(), b.view(), x);
                                    },
                                    _ => {
                                        assert(false);
                                    },
                                }
                                lemma_abs_fits(trem(x, y), xmax.view());
                            }
                        }
                        r
                    },
                }
            } else {
                match Self::class_of(n) {
                    Class::NonNeg => {
                        let r = IntervalZ { lo: Lo::Fin(IBig::from_i64(0)), hi: Hi::PosInf };
                        proof {
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                assert(x >= 0);
                                lemma_trem_range(x, y);
                            }
                        }
                        r
                    },
                    Class::NonPos => {
                        let r = IntervalZ { lo: Lo::NegInf, hi: Hi::Fin(IBig::from_i64(0)) };
                        proof {
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                assert(x <= 0);
                                lemma_trem_range(x, y);
                            }
                        }
                        r
                    },
                    Class::Mixed => IntervalZ::top(),
                }
            }
        } else {
            let dl = match &d.lo {
                Lo::Fin(v) => v,
                Lo::NegInf => {
                    proof {
                        assert(false);
                    }
                    return IntervalZ::top();
                },
            };
            let dh = match &d.hi {
                Hi::Fin(v) => v,
                Hi::PosInf => {
                    proof {
                        assert(false);
                    }
                    return IntervalZ::top();
                },
            };
            let al = Self::abs_of(dl);
            let ah = Self::abs_of(dh);
            let m = if al.le(&ah) {
                ah
            } else {
                al
            };
            let one = IBig::from_i64(1);
            let mm1 = m.sub(&one);
            proof {
                let mv = max2(iabs(dl.view()), iabs(dh.view()));
                assert(m.view() == mv);
                assert(mm1.view() == m.view() - 1);
                assert(mv >= 1) by {
                    if mv == 0 {
                        assert(dl.view() == 0 && dh.view() == 0);
                        assert forall|y: int| d.gamma(y) implies y == 0 by {
                            assert(y == 0);
                        }
                    }
                }
            }
            let cap = Self::rem_cap(n, &mm1, &m, trunc);
            let lo_neg = IBig::from_i64(0).sub(&cap);
            if !trunc {
                let r = IntervalZ { lo: Lo::Fin(IBig::from_i64(0)), hi: Hi::Fin(cap) };
                proof {
                    assert(cap.view() >= 0);
                    assert forall|x: int, y: int|
                        n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(x % y) by {
                        lemma_rem_spec_def(false, x, y);
                        lemma_euclid_rem_range(x, y);
                        lemma_abs_le_ends(dl.view(), dh.view(), y);
                        assert(iabs(y) <= m.view());
                        assert(iabs(rem_spec(false, x, y)) <= cap.view());
                        assert(iabs(x % y) == x % y);
                    }
                }
                r
            } else {
                match Self::class_of(n) {
                    Class::NonNeg => {
                        let r = IntervalZ { lo: Lo::Fin(IBig::from_i64(0)), hi: Hi::Fin(cap) };
                        proof {
                            assert(cap.view() >= 0);
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                assert(x >= 0);
                                lemma_rem_spec_def(true, x, y);
                                lemma_trem_range(x, y);
                                lemma_abs_le_ends(dl.view(), dh.view(), y);
                                assert(iabs(y) <= m.view());
                                assert(iabs(rem_spec(true, x, y)) <= cap.view());
                                lemma_abs_fits(trem(x, y), cap.view());
                            }
                        }
                        r
                    },
                    Class::NonPos => {
                        let r = IntervalZ { lo: Lo::Fin(lo_neg), hi: Hi::Fin(IBig::from_i64(0)) };
                        proof {
                            assert(lo_neg.view() == -cap.view());
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                assert(x <= 0);
                                lemma_rem_spec_def(true, x, y);
                                lemma_trem_range(x, y);
                                lemma_abs_le_ends(dl.view(), dh.view(), y);
                                assert(iabs(y) <= m.view());
                                assert(iabs(rem_spec(true, x, y)) <= cap.view());
                                lemma_abs_fits(trem(x, y), cap.view());
                            }
                        }
                        r
                    },
                    Class::Mixed => {
                        let hi_b = cap.dup();
                        let r = IntervalZ { lo: Lo::Fin(lo_neg), hi: Hi::Fin(hi_b) };
                        proof {
                            assert(lo_neg.view() == -cap.view());
                            assert(hi_b.view() == cap.view());
                            assert forall|x: int, y: int|
                                n.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                                trem(x, y),
                            ) by {
                                lemma_rem_spec_def(true, x, y);
                                lemma_trem_range(x, y);
                                lemma_abs_le_ends(dl.view(), dh.view(), y);
                                assert(iabs(y) <= m.view());
                                assert(iabs(rem_spec(true, x, y)) <= cap.view());
                                lemma_abs_fits(trem(x, y), cap.view());
                            }
                        }
                        r
                    },
                }
            }
        }
    }

    fn rem_one(&self, d: &IntervalZ, trunc: bool) -> (r: IntervalZ)
        requires
            self.wf(),
            d.wf(),
            !d.gamma(0),
        ensures
            r.wf(),
            forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) && y != 0 ==> #[trigger] r.gamma(rem_spec(trunc, x, y)),
    {
        let q = self.div_nonzero(d, trunc);
        let qv = if Self::ends_fin(self) && Self::ends_fin(d) {
            Self::quot_singleton(&q)
        } else {
            None
        };
        if let Some(qv) = qv {
            let r = Self::rem_affine(self, d, &qv);
            proof {
                assert forall|x: int, y: int|
                    self.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.gamma(
                    rem_spec(trunc, x, y),
                ) by {
                    assert(q.gamma(quot_spec(trunc, x, y)));
                    assert(quot_spec(trunc, x, y) == qv.view());
                    if trunc {
                        assert(trem(x, y) == x - y * tdiv(x, y));
                    } else {
                        lemma_fundamental_div_mod(x, y);
                        assert(x % y == x - y * (x / y));
                    }
                }
            }
            return r;
        }
        proof {
            d.lemma_nonempty();
            assert(exists|y: int| d.gamma(y) && y != 0);
        }
        Self::rem_fallback(self, d, trunc)
    }

    fn rem_general(&self, d: &Self, trunc: bool) -> (r: (BotOr<Self>, DivZero))
        requires
            self.wf(),
            d.wf(),
        ensures
            r.0.wf(),
            forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) && y != 0 ==> #[trigger] r.0.gamma(rem_spec(trunc, x, y)),
            r.1 is Never <==> !d.gamma(0),
            r.1 is Always <==> forall|y: int| #[trigger] d.gamma(y) ==> y == 0,
            (r.0 is Bot) <==> (r.1 is Always),
    {
        let flag = Self::classify(d);
        match flag {
            DivZero::Always => (BotOr::Bot, DivZero::Always),
            DivZero::Never => (BotOr::Val(self.rem_one(d, trunc)), DivZero::Never),
            DivZero::Maybe => {
                let neg = Self::neg_part(d);
                let pos = Self::pos_part(d);
                let v = match (neg, pos) {
                    (Some(n), Some(p)) => {
                        let rn = self.rem_one(&n, trunc);
                        let rp = self.rem_one(&p, trunc);
                        let v = rn.join(&rp);
                        proof {
                            assert forall|x: int, y: int|
                                self.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] v.gamma(
                                rem_spec(trunc, x, y),
                            ) by {
                                if y <= -1 {
                                    assert(n.gamma(y));
                                    assert(rn.gamma(rem_spec(trunc, x, y)));
                                } else {
                                    assert(p.gamma(y));
                                    assert(rp.gamma(rem_spec(trunc, x, y)));
                                }
                            }
                        }
                        v
                    },
                    (Some(n), None) => self.rem_one(&n, trunc),
                    (None, Some(p)) => self.rem_one(&p, trunc),
                    (None, None) => {
                        proof {
                            assert(false);
                        }
                        Self::top()
                    },
                };
                (BotOr::Val(v), DivZero::Maybe)
            },
        }
    }
}

impl Domain for IntervalZ {
    type C = int;

    open spec fn wf(&self) -> bool {
        match (self.lo(), self.hi()) {
            (Lo::Fin(a), Hi::Fin(b)) => a.view() <= b.view(),
            _ => true,
        }
    }

    open spec fn gamma(&self, c: int) -> bool {
        lo_ok(self.lo(), c) && hi_ok(self.hi(), c)
    }

    fn dup(&self) -> (r: Self) {
        IntervalZ { lo: dup_lo(&self.lo), hi: dup_hi(&self.hi) }
    }

    fn top() -> (r: Self) {
        IntervalZ { lo: Lo::NegInf, hi: Hi::PosInf }
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        lo_le(&o.lo, &self.lo) && hi_le(&self.hi, &o.hi)
    }

    fn join(&self, o: &Self) -> (r: Self) {
        let lo = if lo_le(&self.lo, &o.lo) {
            dup_lo(&self.lo)
        } else {
            dup_lo(&o.lo)
        };
        let hi = if hi_le(&self.hi, &o.hi) {
            dup_hi(&o.hi)
        } else {
            dup_hi(&self.hi)
        };
        IntervalZ { lo, hi }
    }

    // Duplicates `meet_exact`: calling it from here would make the impl
    // depend on a function whose contract mentions the impl (a Verus cycle).
    fn meet(&self, o: &Self) -> (r: BotOr<Self>)
    {
        let lo = if lo_le(&self.lo, &o.lo) {
            dup_lo(&o.lo)
        } else {
            dup_lo(&self.lo)
        };
        let hi = if hi_le(&self.hi, &o.hi) {
            dup_hi(&self.hi)
        } else {
            dup_hi(&o.hi)
        };
        let ok = match (&lo, &hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.le(b),
            _ => true,
        };
        if ok {
            BotOr::Val(IntervalZ { lo, hi })
        } else {
            proof {
                assert forall|c: int| #[trigger] self.gamma(c) implies !o.gamma(c) by {
                    if self.gamma(c) && o.gamma(c) {
                        assert(lo_ok(lo, c) && hi_ok(hi, c));
                    }
                }
            }
            BotOr::Bot
        }
    }

    /// Cousot-Cousot widening: an unstable bound jumps to infinity.
    fn widen(&self, o: &Self) -> (r: Self) {
        let lo = if lo_le(&self.lo, &o.lo) {
            dup_lo(&self.lo)
        } else {
            Lo::NegInf
        };
        let hi = if hi_le(&o.hi, &self.hi) {
            dup_hi(&self.hi)
        } else {
            Hi::PosInf
        };
        IntervalZ { lo, hi }
    }
}

impl Canonical for IntervalZ {
    proof fn lemma_nonempty(&self) {
        match (self.lo, self.hi) {
            (Lo::Fin(a), _) => assert(self.gamma(a.view())),
            (Lo::NegInf, Hi::Fin(b)) => assert(self.gamma(b.view())),
            (Lo::NegInf, Hi::PosInf) => assert(self.gamma(0)),
        }
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        // Each bound is fixed by the set: equal finite bounds are the extreme
        // members; a finite bound against an infinite one is refuted by a
        // member beyond it.
        match (a.lo, b.lo) {
            (Lo::Fin(x), Lo::Fin(y)) => {
                assert(a.gamma(x.view()) && b.gamma(y.view()));
                assert(a.gamma(y.view()) == b.gamma(y.view()));
                IBig::axiom_view_injective(&x, &y);
            },
            (Lo::Fin(x), Lo::NegInf) => {
                let w = match b.hi {
                    Hi::Fin(h) => if h.view() < x.view() {
                        h.view()
                    } else {
                        x.view() - 1
                    },
                    Hi::PosInf => x.view() - 1,
                };
                assert(b.gamma(w) && a.gamma(w) == b.gamma(w));
            },
            (Lo::NegInf, Lo::Fin(y)) => {
                let w = match a.hi {
                    Hi::Fin(h) => if h.view() < y.view() {
                        h.view()
                    } else {
                        y.view() - 1
                    },
                    Hi::PosInf => y.view() - 1,
                };
                assert(a.gamma(w));
            },
            _ => {},
        }
        match (a.hi, b.hi) {
            (Hi::Fin(x), Hi::Fin(y)) => {
                assert(a.gamma(x.view()) && b.gamma(y.view()));
                assert(a.gamma(y.view()) == b.gamma(y.view()));
                IBig::axiom_view_injective(&x, &y);
            },
            (Hi::Fin(x), Hi::PosInf) => {
                let w = match b.lo {
                    Lo::Fin(l) => if l.view() > x.view() {
                        l.view()
                    } else {
                        x.view() + 1
                    },
                    Lo::NegInf => x.view() + 1,
                };
                assert(b.gamma(w) && a.gamma(w) == b.gamma(w));
            },
            (Hi::PosInf, Hi::Fin(y)) => {
                let w = match a.lo {
                    Lo::Fin(l) => if l.view() > y.view() {
                        l.view()
                    } else {
                        y.view() + 1
                    },
                    Lo::NegInf => y.view() + 1,
                };
                assert(a.gamma(w));
            },
            _ => {},
        }
    }
}

impl Arith<Euclid> for IntervalZ {
    fn add(&self, o: &Self) -> (r: Self) {
        self.add_int(o)
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        self.sub_int(o)
    }

    fn neg(&self) -> (r: Self) {
        self.neg_int()
    }
}

impl Arith<Trunc> for IntervalZ {
    fn add(&self, o: &Self) -> (r: Self) {
        self.add_int(o)
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        self.sub_int(o)
    }

    fn neg(&self) -> (r: Self) {
        self.neg_int()
    }
}

impl DivRem<Euclid> for IntervalZ {
    fn contains_zero(&self) -> (b: bool) {
        self.contains_zero_int()
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let r = self.div_general(d, false);
        proof {
            assert forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.0.gamma(x / y) by {
                assert(quot_spec(false, x, y) == x / y);
                assert(r.0.gamma(quot_spec(false, x, y)));
            }
        }
        r
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let r = self.rem_general(d, false);
        proof {
            assert forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.0.gamma(x % y) by {
                assert(rem_spec(false, x, y) == x % y);
                assert(r.0.gamma(rem_spec(false, x, y)));
            }
        }
        r
    }
}

impl Mul<Euclid> for IntervalZ {
    fn mul(&self, o: &Self) -> (r: Self) {
        self.mul_int(o)
    }
}

impl Mul<Trunc> for IntervalZ {
    fn mul(&self, o: &Self) -> (r: Self) {
        self.mul_int(o)
    }
}

impl DivRem<Trunc> for IntervalZ {
    fn contains_zero(&self) -> (b: bool) {
        self.contains_zero_int()
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let r = self.div_general(d, true);
        proof {
            assert forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.0.gamma(tdiv(x, y)) by {
                assert(quot_spec(true, x, y) == tdiv(x, y));
                assert(r.0.gamma(quot_spec(true, x, y)));
            }
        }
        r
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let r = self.rem_general(d, true);
        proof {
            assert forall|x: int, y: int|
                self.gamma(x) && d.gamma(y) && y != 0 implies #[trigger] r.0.gamma(trem(x, y)) by {
                assert(rem_spec(true, x, y) == trem(x, y));
                assert(r.0.gamma(rem_spec(true, x, y)));
            }
        }
        r
    }
}

spec fn lo_meet(a: Lo, b: Lo) -> Lo {
    if lo_leq(a, b) {
        b
    } else {
        a
    }
}

spec fn hi_meet(a: Hi, b: Hi) -> Hi {
    if hi_leq(a, b) {
        a
    } else {
        b
    }
}

spec fn bounds_crossed(lo: Lo, hi: Hi) -> bool {
    match (lo, hi) {
        (Lo::Fin(a), Hi::Fin(b)) => a.view() > b.view(),
        _ => false,
    }
}

spec fn meet_of(a: IntervalZ, b: IntervalZ) -> BotOr<IntervalZ> {
    let lo = lo_meet(a.lo(), b.lo());
    let hi = hi_meet(a.hi(), b.hi());
    if bounds_crossed(lo, hi) {
        BotOr::Bot
    } else {
        BotOr::Val(IntervalZ { lo, hi })
    }
}

spec fn same_set(a: BotOr<IntervalZ>, b: BotOr<IntervalZ>) -> bool {
    forall|c: int| #[trigger] a.gamma(c) == b.gamma(c)
}

/// Meets `cur` with each fact. Fuel 0 keeps `cur`. A meet that does not change
/// the concretization spends nothing; a strict meet spends one unit.
spec fn meet_chain(cur: BotOr<IntervalZ>, facts: Seq<IntervalZ>, fuel: nat) -> BotOr<IntervalZ>
    decreases facts.len(),
{
    if facts.len() == 0 || fuel == 0 {
        cur
    } else {
        match cur {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(v) => {
                let next = meet_of(v, facts[0]);
                let fuel2 = if same_set(next, cur) {
                    fuel
                } else {
                    (fuel - 1) as nat
                };
                meet_chain(next, facts.skip(1), fuel2)
            },
        }
    }
}

proof fn lemma_lo_total(a: Lo, b: Lo)
    ensures
        lo_leq(a, b) || lo_leq(b, a),
{
    match (a, b) {
        (Lo::Fin(x), Lo::Fin(y)) => {
            if x.view() <= y.view() {
            } else {
                assert(y.view() <= x.view());
            }
        },
        _ => {},
    }
}

proof fn lemma_hi_total(a: Hi, b: Hi)
    ensures
        hi_leq(a, b) || hi_leq(b, a),
{
    match (a, b) {
        (Hi::Fin(x), Hi::Fin(y)) => {
            if x.view() <= y.view() {
            } else {
                assert(y.view() <= x.view());
            }
        },
        _ => {},
    }
}

proof fn lemma_meet_of_gamma(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
    ensures
        meet_of(a, b).wf(),
        forall|c: int| #[trigger] meet_of(a, b).gamma(c) <==> a.gamma(c) && b.gamma(c),
{
    reveal(lo_meet);
    reveal(hi_meet);
    reveal(bounds_crossed);
    reveal(meet_of);
    let lo = lo_meet(a.lo(), b.lo());
    let hi = hi_meet(a.hi(), b.hi());
    lemma_lo_point(a.lo(), b.lo());
    lemma_lo_point(b.lo(), a.lo());
    lemma_lo_total(a.lo(), b.lo());
    lemma_hi_point(a.hi(), b.hi());
    lemma_hi_point(b.hi(), a.hi());
    lemma_hi_total(a.hi(), b.hi());
    assert forall|c: int| a.gamma(c) && b.gamma(c) implies lo_ok(lo, c) && hi_ok(hi, c) by {
        if lo_leq(a.lo(), b.lo()) {
            assert(lo == b.lo());
        } else {
            assert(lo == a.lo());
        }
        if hi_leq(a.hi(), b.hi()) {
            assert(hi == a.hi());
        } else {
            assert(hi == b.hi());
        }
    }
    if bounds_crossed(lo, hi) {
        assert forall|c: int| a.gamma(c) && b.gamma(c) implies false by {
            assert(lo_ok(lo, c) && hi_ok(hi, c));
        }
    } else {
        assert forall|c: int| lo_ok(lo, c) && hi_ok(hi, c) implies a.gamma(c) && b.gamma(c) by {
            if lo_leq(a.lo(), b.lo()) {
                assert(lo == b.lo());
                assert(lo_ok(a.lo(), c));
            } else {
                assert(lo_leq(b.lo(), a.lo()));
                assert(lo == a.lo());
                assert(lo_ok(b.lo(), c));
            }
            if hi_leq(a.hi(), b.hi()) {
                assert(hi == a.hi());
                assert(hi_ok(b.hi(), c));
            } else {
                assert(hi_leq(b.hi(), a.hi()));
                assert(hi == b.hi());
                assert(hi_ok(a.hi(), c));
            }
        }
    }
}

/// Soundness, not only `result ⊆ cur`: a concrete value that lies in `cur` and
/// in every fact is still in the chain, including when fuel runs out early.
proof fn meet_chain_sound(cur: BotOr<IntervalZ>, facts: Seq<IntervalZ>, fuel: nat)
    requires
        cur.wf(),
        forall|i: int| 0 <= i < facts.len() ==> (#[trigger] facts[i]).wf(),
    ensures
        meet_chain(cur, facts, fuel).wf(),
        forall|c: int| #[trigger] meet_chain(cur, facts, fuel).gamma(c) ==> cur.gamma(c),
        forall|c: int|
            cur.gamma(c) && (forall|i: int|
                0 <= i < facts.len() ==> (#[trigger] facts[i]).gamma(c)) ==> meet_chain(
                cur,
                facts,
                fuel,
            ).gamma(c),
        fuel == 0 ==> meet_chain(cur, facts, fuel) == cur,
    decreases facts.len(),
{
    reveal(meet_chain);
    reveal(same_set);
    reveal(meet_of);
    if facts.len() == 0 || fuel == 0 {
        assert(meet_chain(cur, facts, fuel) == cur);
    } else {
        match cur {
            BotOr::Bot => {
                assert(meet_chain(cur, facts, fuel) == BotOr::Bot);
            },
            BotOr::Val(v) => {
                let next = meet_of(v, facts[0]);
                lemma_meet_of_gamma(v, facts[0]);
                let tail = facts.skip(1);
                assert forall|i: int| 0 <= i < tail.len() implies (#[trigger] tail[i]).wf() by {
                    assert(facts[i + 1].wf());
                }
                let fuel2 = if same_set(next, cur) {
                    fuel
                } else {
                    (fuel - 1) as nat
                };
                assert(meet_chain(cur, facts, fuel) == meet_chain(next, tail, fuel2));
                meet_chain_sound(next, tail, fuel2);
                assert forall|c: int|
                    cur.gamma(c) && (forall|i: int|
                        0 <= i < facts.len() ==> #[trigger] facts[i].gamma(c)) implies meet_chain(
                    cur,
                    facts,
                    fuel,
                ).gamma(c) by {
                    assert(facts[0].gamma(c));
                    assert(next.gamma(c));
                    assert forall|i: int| 0 <= i < tail.len() implies #[trigger] tail[i].gamma(c) by {
                        assert(facts[i + 1].gamma(c));
                    }
                }
            },
        }
    }
}

} // verus!
