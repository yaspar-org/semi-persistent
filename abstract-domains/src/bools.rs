// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Boolean type with method names matching bitvector operations.

use vstd::prelude::*;

verus! {

/// A boolean with bitvector-flavored operations.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Bit(pub bool);

impl Bit {
    pub open spec fn b(self) -> bool { self.0 }
    pub open spec fn n(self) -> nat { if self.0 { 1 } else { 0 } }

    pub open spec fn t() -> Bit  { Bit(true) }
    pub open spec fn f() -> Bit  { Bit(false) }

    pub open spec fn ctor(b: bool) -> Bit  { Bit(b) }
    pub open spec fn ctor_n(n: nat) -> Bit
        recommends n < 2
     { Bit(0 < n) }

    pub open spec fn not(self) -> Bit  { Bit(!self.0) }
    pub open spec fn or(self, n: Bit) -> Bit  { Bit(self.0 || n.0) }
    pub open spec fn and(self, n: Bit) -> Bit  { Bit(self.0 && n.0) }
    pub open spec fn and_not(self, n: Bit) -> Bit  { Bit(self.0 && !n.0) }
    pub open spec fn xor(self, n: Bit) -> Bit  { Bit(self.0 != n.0) }

    /// Full adder: add three bits producing (result, carry).
    /// ensures self.n() + b0.n() + b1.n() == 2 * r.1.n() + r.0.n()
    pub open spec fn full_add(self, b0: Bit, b1: Bit) -> (Bit, Bit) {
        (
            self.xor(b0).xor(b1),
            if self.0 { b0.or(b1) } else { b0.and(b1) },
        )
    }

    pub proof fn full_add_correct(self, b0: Bit, b1: Bit)
        ensures ({ let r = self.full_add(b0, b1); self.n() + b0.n() + b1.n() == 2 * r.1.n() + r.0.n() })
    {}

    pub open spec fn disj(self, n: Bit) -> bool { !self.0 || !n.0 }
    pub open spec fn imp(self, v: Bit) -> bool { self.0 ==> v.0 }
}

} // verus!
