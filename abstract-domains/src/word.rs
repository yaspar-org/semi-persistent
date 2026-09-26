// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Machine words, generic over the width.
//!
//! Domains over machine integers are written once, generic over `W: Word`, and
//! store native words (`u8`..`u64`). Specifications read a word through
//! `view()` as a `nat`, which is ghost and erased. Width-specific facts are
//! proof obligations of this trait, discharged once per width by `impl_word!`.
//!
//! A word is a bit pattern. Signedness is not a property of the carrier; it is
//! chosen by the operation semantics (`semantics::Unsigned` / `semantics::Signed`),
//! so there is one domain instance per width, not one per signedness.
use vstd::prelude::*;

verus! {

pub trait Word: Sized + Copy {
    /// 2^bits.
    spec fn modulus() -> nat;

    /// Unsigned reading of the bit pattern.
    spec fn view(self) -> nat;

    /// The word whose unsigned reading is `i mod 2^bits`.
    spec fn from_int(i: int) -> Self;

    proof fn lemma_modulus()
        ensures
            Self::modulus() >= 256,
            Self::modulus() % 2 == 0,
    ;

    proof fn lemma_view_bounded(self)
        ensures
            self.view() < Self::modulus(),
    ;

    proof fn lemma_view_injective(a: Self, b: Self)
        ensures
            a.view() == b.view() ==> a == b,
    ;

    proof fn lemma_from_int(i: int)
        ensures
            Self::from_int(i).view() == i % (Self::modulus() as int),
    ;

    fn zero() -> (r: Self)
        ensures
            r.view() == 0,
    ;

    fn one() -> (r: Self)
        ensures
            r.view() == 1,
    ;

    fn max() -> (r: Self)
        ensures
            r.view() == Self::modulus() - 1,
    ;

    fn le(self, o: Self) -> (b: bool)
        ensures
            b == (self.view() <= o.view()),
    ;

    fn lt(self, o: Self) -> (b: bool)
        ensures
            b == (self.view() < o.view()),
    ;

    fn eq(self, o: Self) -> (b: bool)
        ensures
            b == (self.view() == o.view()),
    ;

    /// Addition when it does not wrap.
    fn checked_add(self, o: Self) -> (r: Option<Self>)
        ensures
            match r {
                Some(s) => s.view() == self.view() + o.view(),
                None => self.view() + o.view() >= Self::modulus(),
            },
    ;

    /// Subtraction when it does not wrap.
    fn checked_sub(self, o: Self) -> (r: Option<Self>)
        ensures
            match r {
                Some(s) => s.view() == self.view() - o.view(),
                None => self.view() < o.view(),
            },
    ;

    /// `modulus - self` for a nonzero word.
    fn neg_nonzero(self) -> (r: Self)
        requires
            self.view() != 0,
        ensures
            r.view() == Self::modulus() - self.view(),
    ;

    fn udiv(self, o: Self) -> (r: Self)
        requires
            o.view() != 0,
        ensures
            r.view() == self.view() / o.view(),
    ;

    fn urem(self, o: Self) -> (r: Self)
        requires
            o.view() != 0,
        ensures
            r.view() == self.view() % o.view(),
    ;
}

/// Two's-complement reading of the bit pattern.
pub open spec fn signed_view<W: Word>(w: W) -> int {
    if w.view() < W::modulus() / 2 {
        w.view() as int
    } else {
        w.view() - W::modulus()
    }
}

} // verus!

macro_rules! impl_word {
    ($t:ty, $modulus:expr) => {
        verus! {
            impl Word for $t {
                open spec fn modulus() -> nat {
                    $modulus
                }

                open spec fn view(self) -> nat {
                    self as nat
                }

                open spec fn from_int(i: int) -> Self {
                    (i % ($modulus as int)) as $t
                }

                proof fn lemma_modulus() {
                }

                proof fn lemma_view_bounded(self) {
                }

                proof fn lemma_view_injective(a: Self, b: Self) {
                }

                proof fn lemma_from_int(i: int) {
                    vstd::arithmetic::div_mod::lemma_mod_bound(i, $modulus as int);
                }

                fn zero() -> (r: Self) {
                    0
                }

                fn one() -> (r: Self) {
                    1
                }

                fn max() -> (r: Self) {
                    <$t>::MAX
                }

                fn le(self, o: Self) -> (b: bool) {
                    self <= o
                }

                fn lt(self, o: Self) -> (b: bool) {
                    self < o
                }

                fn eq(self, o: Self) -> (b: bool) {
                    self == o
                }

                fn checked_add(self, o: Self) -> (r: Option<Self>) {
                    if self <= <$t>::MAX - o {
                        Some(self + o)
                    } else {
                        None
                    }
                }

                fn checked_sub(self, o: Self) -> (r: Option<Self>) {
                    if o <= self {
                        Some(self - o)
                    } else {
                        None
                    }
                }

                fn neg_nonzero(self) -> (r: Self) {
                    <$t>::MAX - (self - 1)
                }

                fn udiv(self, o: Self) -> (r: Self) {
                    self / o
                }

                fn urem(self, o: Self) -> (r: Self) {
                    self % o
                }
            }
        }
    };
}

impl_word!(u8, 0x100);
impl_word!(u16, 0x1_0000);
impl_word!(u32, 0x1_0000_0000);
impl_word!(u64, 0x1_0000_0000_0000_0000);
