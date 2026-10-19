// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Rounding a machine word onto a congruence grid.
//!
//! The grid of `(r, m)` is `{x | x % m == r}` when `m > 0` and `{r}` when
//! `m == 0`, the congruence encoding (`m == 0` is a singleton, `(1, 0)` is
//! every word). `round_up` and `round_down` find the nearest grid point on
//! each side of a word. They are the interval/congruence grid step of
//! `Facts::normalize` (doc/reduced-product.md), and give the smallest and
//! largest members of a congruence in `W`.
//!
//! Both compute in `W` with `urem`, `checked_add` and `checked_sub` only, and
//! return `None` instead of wrapping when no grid point lies on that side.
#![allow(unused_imports)]

use crate::word::*;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// `x` lies on the grid of `(r, m)`.
pub open spec fn on_grid(x: int, r: int, m: int) -> bool {
    if m == 0 {
        x == r
    } else {
        x % m == r
    }
}

/// `(r, m)` is a well-formed grid: a singleton, or a residue below its modulus.
pub open spec fn grid_wf<W: Word>(r: W, m: W) -> bool {
    m.view() == 0 || r.view() < m.view()
}

/// Rounding up over the integers: with `e = x % m`, the smallest `c >= x`
/// with `c % m == r` is `x - e + r`, plus `m` when `e > r`.
proof fn lemma_round_up(x: int, r: int, m: int)
    requires
        0 <= x,
        0 <= r < m,
    ensures
        ({
            let y = x - x % m + r + if x % m > r {
                m
            } else {
                0
            };
            x <= y && y % m == r && forall|c: int| x <= c && #[trigger] (c % m) == r ==> y <= c
        }),
{
    let e = x % m;
    let p = x / m;
    lemma_fundamental_div_mod(x, m);
    lemma_mod_pos_bound(x, m);
    let k = if e > r {
        p + 1
    } else {
        p
    };
    let y = x - e + r + if e > r {
        m
    } else {
        0
    };
    assert(y == m * k + r) by (nonlinear_arith)
        requires
            x == m * p + e,
            k == if e > r {
                p + 1
            } else {
                p
            },
            y == x - e + r + if e > r {
                m
            } else {
                0
            },
    ;
    lemma_mod_multiples_vanish(k, r, m);
    lemma_small_mod(r as nat, m as nat);
    assert forall|c: int| x <= c && #[trigger] (c % m) == r implies y <= c by {
        let q = c / m;
        lemma_fundamental_div_mod(c, m);
        // Below `k`, a grid point is below `x`: one grid step short when
        // `e > r`, and under `x`'s own multiple of `m` otherwise.
        if q < k {
            assert(m * q <= m * (k - 1)) by (nonlinear_arith)
                requires
                    q <= k - 1,
                    m > 0,
            ;
            assert(m * (k - 1) == m * k - m) by (nonlinear_arith);
        }
        assert(m * q >= m * k) by (nonlinear_arith)
            requires
                q >= k,
                m > 0,
        ;
    }
}

/// The smallest grid point `>= x`, or `None` when every grid point in `W`
/// is below `x`.
pub fn round_up<W: Word>(x: W, r: W, m: W) -> (o: Option<W>)
    requires
        grid_wf(r, m),
    ensures
        match o {
            Some(y) => x.view() <= y.view() && on_grid(y.view() as int, r.view() as int, m.view()
                as int) && forall|c: W| #[trigger]
                on_grid(c.view() as int, r.view() as int, m.view() as int) && x.view()
                    <= c.view() ==> y.view() <= c.view(),
            None => forall|c: W| #[trigger]
                on_grid(c.view() as int, r.view() as int, m.view() as int) ==> c.view()
                    < x.view(),
        },
{
    if m.eq(W::zero()) {
        return if x.le(r) {
            Some(r)
        } else {
            None
        };
    }
    let rem = x.urem(m);
    let ghost y_int: int = x.view() - rem.view() + r.view() + if rem.view() > r.view() {
        m.view() as int
    } else {
        0
    };
    proof {
        lemma_round_up(x.view() as int, r.view() as int, m.view() as int);
    }
    // Every grid point `>= x` is `>= y_int`; so when `y_int` does not fit in
    // `W`, no grid point `>= x` does.
    let o = if rem.eq(r) {
        Some(x)
    } else if rem.lt(r) {
        x.checked_add(r.checked_sub(rem).expect("rem < r"))
    } else {
        match x.checked_add(m.checked_sub(rem).expect("rem < m")) {
            Some(b) => b.checked_add(r),
            None => None,
        }
    };
    proof {
        if o is None {
            assert(y_int >= W::modulus());
            assert forall|c: W| #[trigger]
                on_grid(c.view() as int, r.view() as int, m.view() as int) implies c.view()
                < x.view() by {
                c.lemma_view_bounded();
            }
        }
    }
    o
}

/// Rounding down over the integers: with `e = x % m`, the largest `c <= x`
/// with `c % m == r` is `x - e + r`, minus `m` when `e < r`. It can be
/// negative, which means no such `c >= 0` exists.
proof fn lemma_round_down(x: int, r: int, m: int)
    requires
        0 <= x,
        0 <= r < m,
    ensures
        ({
            let y = x - x % m + r - if x % m < r {
                m
            } else {
                0
            };
            y <= x && y % m == r && forall|c: int| c <= x && #[trigger] (c % m) == r ==> c <= y
        }),
{
    let e = x % m;
    let p = x / m;
    lemma_fundamental_div_mod(x, m);
    lemma_mod_pos_bound(x, m);
    let k = if e < r {
        p - 1
    } else {
        p
    };
    let y = x - e + r - if e < r {
        m
    } else {
        0
    };
    assert(y == m * k + r) by (nonlinear_arith)
        requires
            x == m * p + e,
            k == if e < r {
                p - 1
            } else {
                p
            },
            y == x - e + r - if e < r {
                m
            } else {
                0
            },
    ;
    lemma_mod_multiples_vanish(k, r, m);
    lemma_small_mod(r as nat, m as nat);
    assert forall|c: int| c <= x && #[trigger] (c % m) == r implies c <= y by {
        let q = c / m;
        lemma_fundamental_div_mod(c, m);
        // Above `k`, a grid point is above `x`: past `x`'s own multiple of
        // `m` when `e < r`, and one grid step past it otherwise.
        if q > k {
            assert(m * q >= m * (k + 1)) by (nonlinear_arith)
                requires
                    q >= k + 1,
                    m > 0,
            ;
            assert(m * (k + 1) == m * k + m) by (nonlinear_arith);
        }
        assert(m * q <= m * k) by (nonlinear_arith)
            requires
                q <= k,
                m > 0,
        ;
    }
}

/// The largest grid point `<= x`, or `None` when every grid point in `W`
/// is above `x`.
pub fn round_down<W: Word>(x: W, r: W, m: W) -> (o: Option<W>)
    requires
        grid_wf(r, m),
    ensures
        match o {
            Some(y) => y.view() <= x.view() && on_grid(y.view() as int, r.view() as int, m.view()
                as int) && forall|c: W| #[trigger]
                on_grid(c.view() as int, r.view() as int, m.view() as int) && c.view()
                    <= x.view() ==> c.view() <= y.view(),
            None => forall|c: W| #[trigger]
                on_grid(c.view() as int, r.view() as int, m.view() as int) ==> x.view()
                    < c.view(),
        },
{
    if m.eq(W::zero()) {
        return if r.le(x) {
            Some(r)
        } else {
            None
        };
    }
    let rem = x.urem(m);
    let ghost y_int: int = x.view() - rem.view() + r.view() - if rem.view() < r.view() {
        m.view() as int
    } else {
        0
    };
    proof {
        lemma_round_down(x.view() as int, r.view() as int, m.view() as int);
        lemma_mod_decreases(x.view(), m.view());
    }
    // Every grid point `<= x` is `<= y_int`; so when `y_int` is negative, no
    // grid point `<= x` exists.
    let o = if rem.eq(r) {
        Some(x)
    } else if r.lt(rem) {
        x.checked_sub(rem.checked_sub(r).expect("r < rem"))
    } else {
        x.checked_sub(rem).expect("rem <= x").checked_sub(m.checked_sub(r).expect("r < m"))
    };
    proof {
        if o is None {
            assert(y_int < 0);
        }
    }
    o
}

} // verus!
