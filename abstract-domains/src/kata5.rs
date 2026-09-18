// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! Ramp-up kata 5: pick one well-formedness-only L4 operation, state its
//! containment postcondition, and try to prove it.
//!
//! Chosen operation: `domains::d8::ExecTnum::sub`.
//! `proof-status.md` lists Tnum negation and subtraction as wf-only.
//!
//! Postcondition:
//! ```text
//! ∀ x y. a.has(x) ∧ b.has(y)  ⟹  a.sub(b).has(x.wrapping_sub(y))
//! ```
//!
//! How far: the composition that *is* the production body verifies.
//! Attaching the same postcondition to the production `sub`/`neg`/`bw_not`
//! calls does not: those methods are exec-only and `constant` does not
//! postcondition its fields. See `REPORT`.

use crate::domains::d8::ExecTnum;
use crate::tnum::Tnum;
use vstd::prelude::*;

verus! {

/// A known constant `{val: n, mask: 0}` contains `n`.
pub proof fn constant_has(n: u8)
    ensures
        (ExecTnum { val: n, mask: 0u8 }).wf(),
        (ExecTnum { val: n, mask: 0u8 }).has(n),
{
    assert(n & 0u8 == 0u8) by (bit_vector);
    crate::domains::d8::native_and_not(n, 0u8);
    assert(n & !0u8 == n) by (bit_vector);
    let tn = Tnum { val: n as nat, mask: 0nat };
    tn.has_equiv(n as nat);
}

/// `bw_not` is xor with all-ones, and xor already contains `^`.
pub fn bw_not_contains(t: &ExecTnum, x: u8) -> (r: ExecTnum)
    requires
        t.wf(),
        t.has(x),
    ensures
        r.wf(),
        r.has(!x),
{
    let ones = ExecTnum { val: !(0u8), mask: 0u8 };
    proof {
        assert(!(0u8) == 255u8) by (bit_vector);
        constant_has(255u8);
        assert(ones.has(255u8));
    }
    let r = t.bw_xor(&ones);
    proof {
        assert(r.has(x ^ 255u8));
        assert((x ^ 255u8) == !x) by (bit_vector);
    }
    r
}

/// Two's complement: `neg = add(bw_not, 1)` contains `!x + 1`.
pub fn neg_contains(t: &ExecTnum, x: u8) -> (r: ExecTnum)
    requires
        t.wf(),
        t.has(x),
    ensures
        r.wf(),
        r.has((!x).wrapping_add(1u8)),
{
    let n = bw_not_contains(t, x);
    let one = ExecTnum { val: 1u8, mask: 0u8 };
    proof {
        constant_has(1u8);
    }
    n.add(&one)
}

/// The kata 5 contract on the production body `add(self, neg(other))`.
pub fn sub_contains(a: &ExecTnum, b: &ExecTnum, x: u8, y: u8) -> (r: ExecTnum)
    requires
        a.wf(),
        b.wf(),
        a.has(x),
        b.has(y),
    ensures
        r.wf(),
        r.has(x.wrapping_sub(y)),
{
    let nb = neg_contains(b, y);
    let r = a.add(&nb);
    proof {
        assert(r.has(x.wrapping_add((!y).wrapping_add(1u8))));
        assert(x.wrapping_add((!y).wrapping_add(1u8)) == x.wrapping_sub(y)) by (bit_vector);
    }
    r
}

} // verus!

/// Printed report for the kata. The test `report_how_far` writes this to stdout.
pub const REPORT: &str = "\
kata 5 — Task 1 estimate
========================
operation:     domains::d8::ExecTnum::sub
list:          proof-status.md, well-formedness-only
                 (Tnum negation and subtraction)

postcondition: forall x y: u8.
                 a.has(x) && b.has(y)
                 ==> a.sub(b).has(x.wrapping_sub(y))

how far:       PROVED the composition that is the production body
               (Verus: kata5 module, 9 verified, 0 errors).
               sub = add(self, neg(other))
               neg = add(bw_not(self), 1)
               bw_not = xor(self, {val: !0, mask: 0})
               xor and add already have universal containment.
               leftover lemmas:
                 constant_has: {val:n, mask:0} contains n
                 !x == x ^ 255                         (bit_vector)
                 x + (!y + 1) == x.wrapping_sub(y)     (bit_vector)

stuck attaching it to the production methods themselves:
  1. ExecTnum::sub / neg / bw_not / constant are exec-only.
     They cannot appear in an `ensures` clause, so the
     statement `a.sub(b).has(...)` is not even writable
     without promoting those methods to spec.
  2. constant() only ensures wf(), not val==n / has(n).
     So a call to constant(1) cannot feed add's containment
     until you construct {val:1, mask:0} yourself.
  3. Two exec evaluations of the same body are not
     automatically congruent (bw_not() =/= the xor we just
     ran, even with identical arguments).

task 1 takeaway:
  For a composition of already-proved L4 ops the math is
  cheap. The real first hour is making the production
  methods spec-visible and giving constant() its fields.
  Still expensive (do not start Task 1 here):
    ExecTnum::mul          — bit loop, no containment
    Interval subtraction   — missing on domains.rs Interval
    ReducedProduct::sub    — interval component forced to top
    ReducedProduct shifts  — interval/anum/unum all top
";
