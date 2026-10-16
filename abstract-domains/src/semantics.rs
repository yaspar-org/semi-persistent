// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Concrete operation semantics that transfer-function contracts refer to.
//!
//! A `Semantics` names a value type `V` and the meaning of each operator on it
//! (zero test, add, sub, neg, mul, div, rem) and of the order (lt, le).
//! Transfer traits are indexed by a semantics (`DivRem<S>`), so one domain type
//! can carry several semantics over the same carrier:
//!
//! | marker        | `V`   | division               |
//! |---------------|-------|------------------------|
//! | `Unsigned<W>` | `W`   | unsigned, wrapping ops |
//! | `Signed<W>`   | `W`   | two's complement, truncated |
//! | `Euclid`      | `int` | Euclidean (Verus / SMT-LIB `div`) |
//! | `Trunc`       | `int` | truncated toward zero (C / Rust) |
//!
//! Division by zero has no meaning here: every division contract excludes zero
//! divisors and reports them through `transfer::DivZero`.
// `pow2` is used only by spec functions, which are erased outside Verus.
#![allow(unused_imports)]
use crate::word::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

pub trait Semantics {
    type V;

    spec fn zero() -> Self::V;

    spec fn is_zero(v: Self::V) -> bool;

    spec fn add(a: Self::V, b: Self::V) -> Self::V;

    spec fn sub(a: Self::V, b: Self::V) -> Self::V;

    spec fn neg(a: Self::V) -> Self::V;

    spec fn mul(a: Self::V, b: Self::V) -> Self::V;

    /// Meaningful only for a nonzero divisor.
    spec fn div(a: Self::V, b: Self::V) -> Self::V;

    /// Meaningful only for a nonzero divisor.
    spec fn rem(a: Self::V, b: Self::V) -> Self::V;

    /// Strict order: unsigned for `Unsigned<W>`, two's complement for
    /// `Signed<W>`, the integer order for `Euclid` and `Trunc`.
    spec fn lt(a: Self::V, b: Self::V) -> bool;

    spec fn le(a: Self::V, b: Self::V) -> bool;

    /// Whether `k` is a shift amount the shifts below are defined for: below
    /// the width for machine words (C makes larger ones undefined, Rust
    /// panics on them), nonnegative for integers.
    spec fn shift_ok(k: Self::V) -> bool;

    /// Left shift, meaningful only when `shift_ok(k)`.
    spec fn shl(a: Self::V, k: Self::V) -> Self::V;

    /// Right shift, meaningful only when `shift_ok(k)`: logical for unsigned
    /// words, arithmetic (rounding down) for signed words and integers.
    spec fn shr(a: Self::V, k: Self::V) -> Self::V;
}

pub open spec fn iabs(a: int) -> int {
    if a < 0 {
        -a
    } else {
        a
    }
}

/// Truncated quotient (rounds toward zero).
pub open spec fn tdiv(a: int, b: int) -> int {
    let q = iabs(a) / iabs(b);
    if (a < 0) != (b < 0) {
        -q
    } else {
        q
    }
}

/// Remainder of the truncated quotient; has the sign of the dividend.
pub open spec fn trem(a: int, b: int) -> int {
    a - b * tdiv(a, b)
}

pub struct Unsigned<W>(core::marker::PhantomData<W>);

pub struct Signed<W>(core::marker::PhantomData<W>);

pub struct Euclid;

pub struct Trunc;

impl<W: Word> Semantics for Unsigned<W> {
    type V = W;

    open spec fn zero() -> W {
        W::from_int(0)
    }

    open spec fn is_zero(v: W) -> bool {
        v.view() == 0
    }

    open spec fn add(a: W, b: W) -> W {
        W::from_int(a.view() as int + b.view() as int)
    }

    open spec fn sub(a: W, b: W) -> W {
        W::from_int(a.view() as int - b.view() as int)
    }

    open spec fn neg(a: W) -> W {
        W::from_int(-(a.view() as int))
    }

    open spec fn mul(a: W, b: W) -> W {
        W::from_int(a.view() as int * b.view() as int)
    }

    open spec fn div(a: W, b: W) -> W {
        W::from_int(a.view() as int / b.view() as int)
    }

    open spec fn rem(a: W, b: W) -> W {
        W::from_int(a.view() as int % b.view() as int)
    }

    open spec fn lt(a: W, b: W) -> bool {
        a.view() < b.view()
    }

    open spec fn le(a: W, b: W) -> bool {
        a.view() <= b.view()
    }

    open spec fn shift_ok(k: W) -> bool {
        k.view() < W::bits()
    }

    open spec fn shl(a: W, k: W) -> W {
        W::from_int((a.view() * pow2(k.view())) as int)
    }

    open spec fn shr(a: W, k: W) -> W {
        W::from_int((a.view() / pow2(k.view())) as int)
    }
}

impl<W: Word> Semantics for Signed<W> {
    type V = W;

    open spec fn zero() -> W {
        W::from_int(0)
    }

    open spec fn is_zero(v: W) -> bool {
        v.view() == 0
    }

    // Two's-complement addition, subtraction and negation are the unsigned
    // operations on bit patterns; they are restated on signed readings here
    // so contracts read naturally.
    open spec fn add(a: W, b: W) -> W {
        W::from_int(signed_view(a) + signed_view(b))
    }

    open spec fn sub(a: W, b: W) -> W {
        W::from_int(signed_view(a) - signed_view(b))
    }

    open spec fn neg(a: W) -> W {
        W::from_int(-signed_view(a))
    }

    open spec fn mul(a: W, b: W) -> W {
        W::from_int(signed_view(a) * signed_view(b))
    }

    /// Wraps on MIN / -1, as the two's-complement result does.
    open spec fn div(a: W, b: W) -> W {
        W::from_int(tdiv(signed_view(a), signed_view(b)))
    }

    open spec fn rem(a: W, b: W) -> W {
        W::from_int(trem(signed_view(a), signed_view(b)))
    }

    open spec fn lt(a: W, b: W) -> bool {
        signed_view(a) < signed_view(b)
    }

    open spec fn le(a: W, b: W) -> bool {
        signed_view(a) <= signed_view(b)
    }

    open spec fn shift_ok(k: W) -> bool {
        k.view() < W::bits()
    }

    open spec fn shl(a: W, k: W) -> W {
        W::from_int(signed_view(a) * pow2(k.view()))
    }

    /// `int` division by a positive divisor rounds down.
    open spec fn shr(a: W, k: W) -> W {
        W::from_int(signed_view(a) / (pow2(k.view()) as int))
    }
}

impl Semantics for Euclid {
    type V = int;

    open spec fn zero() -> int {
        0
    }

    open spec fn is_zero(v: int) -> bool {
        v == 0
    }

    open spec fn add(a: int, b: int) -> int {
        a + b
    }

    open spec fn sub(a: int, b: int) -> int {
        a - b
    }

    open spec fn neg(a: int) -> int {
        -a
    }

    open spec fn mul(a: int, b: int) -> int {
        a * b
    }

    /// Verus `int` division is Euclidean: `0 <= a % b < |b|`.
    open spec fn div(a: int, b: int) -> int {
        a / b
    }

    open spec fn rem(a: int, b: int) -> int {
        a % b
    }

    open spec fn lt(a: int, b: int) -> bool {
        a < b
    }

    open spec fn le(a: int, b: int) -> bool {
        a <= b
    }

    open spec fn shift_ok(k: int) -> bool {
        k >= 0
    }

    open spec fn shl(a: int, k: int) -> int {
        a * pow2(k as nat)
    }

    open spec fn shr(a: int, k: int) -> int {
        a / (pow2(k as nat) as int)
    }
}

impl Semantics for Trunc {
    type V = int;

    open spec fn zero() -> int {
        0
    }

    open spec fn is_zero(v: int) -> bool {
        v == 0
    }

    open spec fn add(a: int, b: int) -> int {
        a + b
    }

    open spec fn sub(a: int, b: int) -> int {
        a - b
    }

    open spec fn neg(a: int) -> int {
        -a
    }

    open spec fn mul(a: int, b: int) -> int {
        a * b
    }

    open spec fn div(a: int, b: int) -> int {
        tdiv(a, b)
    }

    open spec fn rem(a: int, b: int) -> int {
        trem(a, b)
    }

    open spec fn lt(a: int, b: int) -> bool {
        a < b
    }

    open spec fn le(a: int, b: int) -> bool {
        a <= b
    }

    open spec fn shift_ok(k: int) -> bool {
        k >= 0
    }

    open spec fn shl(a: int, k: int) -> int {
        a * pow2(k as nat)
    }

    open spec fn shr(a: int, k: int) -> int {
        a / (pow2(k as nat) as int)
    }
}

} // verus!
