// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
use crate::anum::*;
use crate::bools::*;
use crate::chopped::*;
use crate::nats::*;
use crate::tnum::*;
/// Executable abstract domains for bitvector verification.
///
/// Four domains, each tracking different aspects of a value:
///
/// **ExecTnum (Tnum)**: Per-bit knowledge. Each bit is 0, 1, or X (unknown).
///   Precise for bitwise ops. Imprecise for arithmetic (carry propagation).
///   Rendering: `1010XX00` means bits 7,5 are 1; bits 4,3 unknown; bits 2,1,0 are 0.
///
/// **ExecAnum (Anum)**: Additive knowledge. A known base `v` plus uncertainty `m`.
///   Precise for arithmetic (base adds exactly). Imprecise for bitwise.
///   Rendering: `00000100+0000000X` means "4 plus 0 or 1" = {4, 5}.
///
/// **Interval**: Bounds knowledge. A range `[lo, hi]`.
///   Precise for comparisons and branches. Coarse for bit-level reasoning.
///
/// **ReducedProduct (reduced product)**: All three combined. Each operation computes on
///   all three domains, then *reduces* by propagating negative information:
///   if ANY domain says a value is impossible, ALL domains can exclude it.
///   - Interval `hi` clears high uncertain bits in Tnum and Anum
///   - Tnum/Anum min/max tighten the interval
///
/// The `bit_is_rust_bit` lemma bridges u64 native ops to the nat-level specs,
/// enabling `wf_implies_inv()` which links exec well-formedness to ghost invariants.
use vstd::prelude::*;

verus! {

pub spec const W: nat = 64;

// ================================================================
// ETn: Executable Tnum on u64
// ================================================================

#[derive(Clone, Copy)]
pub struct ExecTnum { pub val: u64, pub mask: u64 }

impl ExecTnum {
    pub open spec fn wf(self) -> bool { self.val & self.mask == 0 }
    pub open spec fn to_tn(self) -> Tnum { Tnum { val: self.val as nat, mask: self.mask as nat } }

    /// Membership (ghost).
    pub open spec fn has(self, x: u64) -> bool {
        self.to_tn().has(x as nat)
    }

    // --- Spec versions for proof use ---
    pub open spec fn spec_or(self, t: ExecTnum) -> ExecTnum {
        let v = self.val | t.val; ExecTnum { val: v, mask: (self.mask | t.mask) & !v }
    }
    pub open spec fn spec_and(self, t: ExecTnum) -> ExecTnum {
        ExecTnum { val: self.val & t.val, mask: self.mask | t.mask }
    }
    pub open spec fn spec_xor(self, t: ExecTnum) -> ExecTnum {
        let v = self.val ^ t.val; let m = self.mask | t.mask; ExecTnum { val: v & !m, mask: m }
    }
    pub open spec fn spec_plus(self, t: ExecTnum) -> ExecTnum {
        let lbv = self.val.wrapping_add(t.val);
        let lbm = self.mask.wrapping_add(t.mask);
        let ub = lbv.wrapping_add(lbm);
        let mask = (ub ^ lbv) | self.mask | t.mask;
        ExecTnum { val: lbv & !mask, mask: mask }
    }

    // --- Bridge lemmas ---
    proof fn bit_above_width(n: nat, w: nat, i: nat)
        requires n < exp(w), i >= w
        ensures !bit(n, i).b()
        decreases i
    {
        exp_pos(w);
        if w == 0 { bit_zero(i); }
        else if i > 0 { Self::bit_above_width(tl(n), (w-1) as nat, (i-1) as nat); }
    }

    pub proof fn bit_is_rust_bit(n: u64, i: u64)
        requires i < 64
        ensures bit(n as nat, i as nat).b() == ((n >> i) & 1u64 == 1u64)
        decreases i
    {
        if i == 0 {
            assert(((n >> 0u64) & 1u64) == (n % 2)) by(bit_vector);
        } else {
            assert((n >> 1u64) as nat == n as nat / 2) by(bit_vector);
            Self::bit_is_rust_bit(n >> 1u64, (i - 1) as u64);
            assert(((n >> i) & 1u64) == (((n >> 1u64) >> ((i-1) as u64)) & 1u64)) by(bit_vector)
                requires i < 64u64, i > 0u64;
        }
    }

    pub proof fn wf_implies_inv(self)
        requires self.wf()
        ensures self.to_tn().inv()
    {
        let sv = self.val; let sm = self.mask;
        assert forall|i: nat| #![auto] !(bit(sv as nat, i).b() && bit(sm as nat, i).b()) by {
            if i < 64 {
                let iu = i as u64;
                Self::bit_is_rust_bit(sv, iu);
                Self::bit_is_rust_bit(sm, iu);
                assert(((sv >> iu) & 1u64 == 1u64) && ((sm >> iu) & 1u64 == 1u64) ==>
                       sv & sm != 0u64) by(bit_vector) requires iu < 64u64;
            } else {
                assert(exp(64) == 0x10000000000000000nat) by { exp_64(); }
                Self::bit_above_width(sv as nat, 64, i);
            }
        };
        disj_bits(sv as nat, sm as nat);
    }

    // --- Exec operations ---
    #[inline] pub fn constant(n: u64) -> (r: ExecTnum) ensures r.wf() {
        proof { assert(n & 0u64 == 0u64) by(bit_vector); }
        ExecTnum { val: n, mask: 0 }
    }
    #[inline] pub fn top() -> (r: ExecTnum) ensures r.wf() {
        proof { assert(0u64 & !0u64 == 0u64) by(bit_vector); }
        ExecTnum { val: 0, mask: !0u64 }
    }
    #[inline] pub fn bw_or(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
        let v = sv | tv; let m = (sm | tm) & !v;
        proof { assert(sv & sm == 0u64 && tv & tm == 0u64 ==> ((sv|tv) & ((sm|tm) & !(sv|tv)) == 0u64)) by(bit_vector); }
        ExecTnum { val: v, mask: m }
    }
    #[inline] pub fn bw_and(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
        proof { assert(sv & sm == 0u64 && tv & tm == 0u64 ==> ((sv&tv) & (sm|tm) == 0u64)) by(bit_vector); }
        ExecTnum { val: sv & tv, mask: sm | tm }
    }
    #[inline] pub fn bw_xor(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        let v = self.val ^ t.val; let m = self.mask | t.mask;
        proof { assert(((v & !m) & m) == 0u64) by(bit_vector); }
        ExecTnum { val: v & !m, mask: m }
    }
    #[inline] pub fn add(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        let lbv = self.val.wrapping_add(t.val);
        let lbm = self.mask.wrapping_add(t.mask);
        let ub = lbv.wrapping_add(lbm);
        let mask = (ub ^ lbv) | self.mask | t.mask;
        proof { assert(((lbv & !mask) & mask) == 0u64) by(bit_vector); }
        ExecTnum { val: lbv & !mask, mask }
    }
    #[inline] pub fn neg(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
        proof { assert((!0u64) & 0u64 == 0u64) by(bit_vector); }
        self.bw_xor(&ExecTnum { val: !0u64, mask: 0 }).add(&ExecTnum::constant(1))
    }
    #[inline] pub fn sub(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        self.add(&t.neg())
    }
    #[inline] pub fn rsh(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
        let v = self.val; let m = self.mask;
        proof { assert(v & m == 0u64 ==> (v >> 1u64) & (m >> 1u64) == 0u64) by(bit_vector); }
        ExecTnum { val: v >> 1, mask: m >> 1 }
    }
    #[inline] pub fn lsh(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
        let v = self.val; let m = self.mask;
        proof { assert(v & m == 0u64 ==> (v << 1u64) & (m << 1u64) == 0u64) by(bit_vector); }
        ExecTnum { val: v << 1, mask: m << 1 }
    }
    #[inline] pub fn join(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
        let v = sv & tv;
        let u = (sv ^ sm) | (tv ^ tm);
        let m = v ^ u;
        proof { assert(sv & sm == 0u64 && tv & tm == 0u64 ==> ((v & !m) & m == 0u64)) by(bit_vector); }
        ExecTnum { val: v & !m, mask: m }
    }
    #[inline] pub fn min_val(&self) -> u64 { self.val }
    #[inline] pub fn max_val(&self) -> u64 { self.val | self.mask }
    #[inline] pub fn is_const(&self) -> bool { self.mask == 0 }
    #[inline] pub fn bw_not(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
        proof { assert((!0u64) & 0u64 == 0u64) by(bit_vector); }
        self.bw_xor(&ExecTnum { val: !0u64, mask: 0 })
    }
    #[inline] pub fn bw_and_not(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        self.bw_and(&t.bw_not())
    }
    pub fn meet(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
        // meet = Tn with v = v1 | v2, u = u1 & u2
        // u = v ^ m, so m = v ^ u
        let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
        let v = sv | tv;
        let u = (sv ^ sm) & (tv ^ tm);
        let m = v ^ u;
        let rv = v & !m;
        proof { assert(((v & !m) & m) == 0u64) by(bit_vector); }
        ExecTnum { val: rv, mask: m }
    }
    pub fn lshi(&self, i: u32) -> (r: ExecTnum) requires self.wf() ensures r.wf() decreases i {
        if i == 0 { *self } else { self.lshi(i - 1).lsh() }
    }
    pub fn rshi(&self, i: u32) -> (r: ExecTnum) requires self.wf() ensures r.wf() decreases i {
        if i == 0 { *self } else { self.rsh().rshi(i - 1) }
    }
    /// Multiplication by tbit: 0, 1, or unknown.
    pub fn mul_bit(&self, bv: bool, bm: bool) -> (r: ExecTnum)
        requires self.wf(), !(bv && bm)
        ensures r.wf()
    {
        if bv { *self }
        else if bm {
            proof { assert(0u64 & (self.val | self.mask) == 0u64) by(bit_vector); }
            ExecTnum { val: 0, mask: self.val | self.mask }
        }
        else { ExecTnum::constant(0) }
    }
    /// Full multiplication via shift-add loop.
    pub fn mul(&self, t: &ExecTnum) -> (r: ExecTnum)
        requires self.wf(), t.wf()
        ensures r.wf()
    {
        let mut acc = ExecTnum::constant(0);
        let mut multiplicand = *self;
        let mut multiplier = t.val;
        let mut mask = t.mask;
        let mut i: u32 = 0;
        while i < 64
            invariant acc.wf(), multiplicand.wf(), i <= 64, multiplier & mask == 0
            decreases 64 - i
        {
            let bv = (multiplier & 1) == 1;
            let bm = (mask & 1) == 1;
            if bv {
                acc = acc.add(&multiplicand);
            } else if bm {
                let tb = multiplicand.mul_bit(false, true);
                acc = acc.add(&tb);
            }
            multiplicand = multiplicand.lsh();
            proof {
                assert(multiplier & mask == 0u64 ==> (multiplier >> 1u64) & (mask >> 1u64) == 0u64) by(bit_vector);
            }
            multiplier >>= 1u64;
            mask >>= 1u64;
            i += 1;
        }
        acc
    }
    /// Division by constant.
    pub fn div_const(&self, d: u64) -> (r: ExecTnum)
        requires self.wf(), d > 0
        ensures r.wf()
    {
        // Use Anum division for better precision, convert back
        let an = ExecAnum::from_etn(self);
        an.div_const(d).to_etn()
    }
    /// Modulo by constant.
    pub fn mod_const(&self, d: u64) -> (r: ExecTnum)
        requires self.wf(), d > 0
        ensures r.wf()
    {
        // x % d = x - (x / d) * d
        let q = self.div_const(d);
        let qd = q.mul(&ExecTnum::constant(d));
        self.sub(&qd)
    }
    /// Check if a concrete value is contained.
    pub open spec fn contains(self, x: u64) -> bool {
        (x & !self.mask) == self.val
    }
}

#[derive(Clone, Copy)]
pub struct ExecAnum { pub base: u64, pub span: u64 }

impl ExecAnum {
    pub open spec fn wf(self) -> bool { true } // All Anums are valid
    pub open spec fn to_an(self) -> Anum { Anum { base: self.base as nat, span: self.span as nat } }

    /// Membership: x >= v and (x - v) has only bits in m.
    pub open spec fn has(self, x: u64) -> bool {
        self.to_an().has(x as nat)
    }

    #[inline] pub fn constant(n: u64) -> ExecAnum { ExecAnum { base: n, span: 0 } }
    #[inline] pub fn top() -> ExecAnum { ExecAnum { base: 0, span: !0u64 } }

    /// Anum addition: exact base, uncertainty via Tnum add of masks.
    #[inline]
    pub fn add(&self, t: &ExecAnum) -> (r: ExecAnum)
        ensures r.wf()
    {
        let v = self.base.wrapping_add(t.base);
        // Uncertainty: Tnum-add the masks
        let m1 = self.span; let m2 = t.span;
        let lbm = m1.wrapping_add(m2);
        let ub = lbm; // lbv for masks is 0, so ub = 0 + lbm = lbm
        let mask = ub | m1 | m2; // simplified: diff = ub ^ 0 = ub
        ExecAnum { base: v, span: mask }
    }

    /// Anum subtraction (bounded).
    #[inline]
    pub fn sub(&self, t: &ExecAnum) -> (r: ExecAnum)
        ensures r.wf()
    {
        let v = self.base.wrapping_sub(t.base.wrapping_add(t.span));
        let m1 = self.span; let m2 = t.span;
        let mask = m1.wrapping_add(m2) | m1 | m2;
        ExecAnum { base: v, span: mask }
    }

    /// Anum division by constant.
    #[inline]
    pub fn div_const(&self, d: u64) -> (r: ExecAnum)
        requires d > 0
        ensures r.wf()
    {
        let sv = self.base; let sm = self.span;
        let min_q = sv / d;
        let max_q = sv.wrapping_add(sm) / d;
        if max_q < min_q {
            // Overflow: go to top
            ExecAnum::top()
        } else {
            let range = max_q - min_q;
            // Compute ones mask >= range: find smallest 2^k - 1 >= range
            let mask = Self::ones_mask(range);
            ExecAnum { base: min_q, span: mask }
        }
    }

    /// Compute smallest (2^k - 1) >= n.
    #[inline]
    fn ones_mask(n: u64) -> (r: u64)
        ensures r >= n
    {
        if n == 0 { return 0; }
        let mut mask: u64 = 1;
        let mut k: u32 = 1;
        while mask < n && k < 64
            invariant k <= 64, k > 0
            decreases 64 - k
        {
            mask = (mask << 1u64) | 1;
            k += 1;
        }
        if mask >= n { mask } else {
            proof { assert(!0u64 >= n) by(bit_vector); }
            !0u64
        }
    }

    /// Convert to ExecTnum (loses additive precision).
    #[inline]
    pub fn to_etn(&self) -> (r: ExecTnum)
        ensures r.wf()
    {
        let sv = self.base; let sm = self.span;
        proof { assert(((sv & !sm) & sm) == 0u64) by(bit_vector); }
        ExecTnum { val: sv & !sm, mask: sm }
    }

    /// Convert from ETn.
    #[inline]
    pub fn from_etn(t: &ExecTnum) -> ExecAnum
        requires t.wf()
    {
        ExecAnum { base: t.val, span: t.mask }
    }

    #[inline] pub fn min_val(&self) -> u64 { self.base }
    #[inline] pub fn max_val(&self) -> u64 { self.base.wrapping_add(self.span) }

    /// Anum multiplication: use Tnum mul internally, keep Anum structure.
    pub fn mul(&self, t: &ExecAnum) -> (r: ExecAnum) {
        // Convert to Tnum, multiply, convert back
        // The Anum accumulator precision is captured internally by the Tnum mul loop
        let a = self.to_etn();
        let b = t.to_etn();
        let result = a.mul(&b);
        ExecAnum::from_etn(&result)
    }
}

// ================================================================
// Interval: [lo, hi] on u64
// ================================================================

#[derive(Clone, Copy)]
pub struct Interval { pub lo: u64, pub hi: u64 }

impl Interval {
    pub open spec fn wf(self) -> bool { self.lo <= self.hi }
    pub open spec fn has(self, x: u64) -> bool { self.lo <= x && x <= self.hi }

    #[inline] pub fn constant(n: u64) -> (r: Interval) ensures r.wf() {
        Interval { lo: n, hi: n }
    }
    #[inline] pub fn top() -> (r: Interval) ensures r.wf() {
        Interval { lo: 0, hi: !0u64 }
    }
    #[inline] pub fn add(&self, t: &Interval) -> (r: Interval)
        requires self.wf(), t.wf()
        ensures r.wf()
    {
        let lo = self.lo.wrapping_add(t.lo);
        let hi = self.hi.wrapping_add(t.hi);
        if lo < self.lo || hi < self.hi || hi < lo { Interval::top() }
        else { Interval { lo, hi } }
    }
    #[inline] pub fn meet(&self, t: &Interval) -> (r: Interval)
        ensures r.wf(),
                forall|x: u64| #![auto] self.has(x) && t.has(x) ==> r.has(x)
    {
        let lo = if self.lo > t.lo { self.lo } else { t.lo };
        let hi = if self.hi < t.hi { self.hi } else { t.hi };
        if hi < lo { Interval::top() } else { Interval { lo, hi } }
    }
    #[inline] pub fn join(&self, t: &Interval) -> (r: Interval)
        requires self.wf(), t.wf()
        ensures r.wf(),
                forall|x: u64| #![auto] self.has(x) ==> r.has(x),
                forall|x: u64| #![auto] t.has(x) ==> r.has(x)
    {
        let lo = if self.lo < t.lo { self.lo } else { t.lo };
        let hi = if self.hi > t.hi { self.hi } else { t.hi };
        Interval { lo, hi }
    }
    #[inline] pub fn sub(&self, t: &Interval) -> (r: Interval)
        requires self.wf(), t.wf()
        ensures r.wf()
    {
        if self.lo >= t.hi && self.hi >= t.lo {
            Interval { lo: self.lo - t.hi, hi: self.hi - t.lo }
        } else {
            Interval::top()
        }
    }
    #[inline] pub fn div_const(&self, d: u64) -> (r: Interval)
        requires self.wf(), d > 0
        ensures r.wf(),
                forall|x: u64| #![auto] self.has(x) ==> r.has(x / d)
    {
        proof {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(self.lo as int, self.hi as int, d as int);
            assert forall|x: u64| #![auto] self.has(x) implies Interval { lo: self.lo / d, hi: self.hi / d }.has(x / d) by {
                vstd::arithmetic::div_mod::lemma_div_is_ordered(self.lo as int, x as int, d as int);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, self.hi as int, d as int);
            };
        }
        Interval { lo: self.lo / d, hi: self.hi / d }
    }
    #[inline] pub fn mod_const(&self, d: u64) -> (r: Interval) requires self.wf(), d > 0 ensures r.wf() {
        if self.hi - self.lo < d && self.lo % d <= self.hi % d {
            // No wraparound within the interval
            Interval { lo: self.lo % d, hi: self.hi % d }
        } else {
            Interval { lo: 0, hi: d - 1 }
        }
    }
    #[inline] pub fn mul(&self, t: &Interval) -> (r: Interval) requires self.wf(), t.wf() ensures r.wf() {
        let (lo, _lo_of) = (self.lo.checked_mul(t.lo), false);
        let (hi, _hi_of) = (self.hi.checked_mul(t.hi), false);
        match (lo, hi) {
            (Some(l), Some(h)) if h >= l => Interval { lo: l, hi: h },
            _ => Interval::top(),
        }
    }
}

// ================================================================
// TI: Reduced product of Tnum × Interval
// ================================================================

#[derive(Clone, Copy)]
pub struct TnumInterval { pub tnum: ExecTnum, pub interval: Interval }

impl TnumInterval {
    pub open spec fn wf(self) -> bool { self.tnum.wf() && self.interval.wf() }
    pub open spec fn has(self, x: u64) -> bool { self.tnum.has(x) && self.interval.has(x) }

    #[inline] pub fn constant(n: u64) -> (r: TnumInterval) ensures r.wf() {
        TnumInterval { tnum: ExecTnum::constant(n), interval: Interval::constant(n) }
    }
    #[inline] pub fn top() -> (r: TnumInterval) ensures r.wf() {
        TnumInterval { tnum: ExecTnum::top(), interval: Interval::top() }
    }

    /// Reduce: tighten interval from Tnum and vice versa.
    #[inline]
    pub fn reduce(&self) -> (r: TnumInterval)
        requires self.wf()
        ensures r.wf()
    {
        // Tighten interval from Tnum bounds
        let tn_min = self.tnum.min_val();
        let tn_max = self.tnum.max_val();
        let lo = if tn_min > self.interval.lo { tn_min } else { self.interval.lo };
        let hi = if tn_max < self.interval.hi { tn_max } else { self.interval.hi };
        // TODO: tighten Tnum from interval (clear high uncertain bits)
        if hi < lo {
            // Empty — shouldn't happen in sound analysis, return top as fallback
            TnumInterval { tnum: ExecTnum::top(), interval: Interval::top() }
        } else {
            TnumInterval { tnum: self.tnum, interval: Interval { lo, hi } }
        }
    }

    // --- Operations with reduction ---
    #[inline] pub fn bw_or(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.bw_or(&t.tnum), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_and(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.bw_and(&t.tnum), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_xor(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.bw_xor(&t.tnum), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn add(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.add(&t.tnum), interval: self.interval.add(&t.interval) }.reduce()
    }
    #[inline] pub fn sub(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.sub(&t.tnum), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn join(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.join(&t.tnum), interval: self.interval.join(&t.interval) }.reduce()
    }
    #[inline] pub fn rsh(&self) -> (r: TnumInterval) requires self.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.rsh(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn lsh(&self) -> (r: TnumInterval) requires self.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.lsh(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn neg(&self) -> (r: TnumInterval) requires self.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.neg(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_and_not(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.bw_and_not(&t.tnum), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_not(&self) -> (r: TnumInterval) requires self.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.bw_not(), interval: Interval::top() }.reduce()
    }
    pub fn mul(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.mul(&t.tnum), interval: self.interval.mul(&t.interval) }.reduce()
    }
    pub fn div_const(&self, d: u64) -> (r: TnumInterval) requires self.wf(), d > 0 ensures r.wf() {
        TnumInterval { tnum: self.tnum.div_const(d), interval: self.interval.div_const(d) }.reduce()
    }
    pub fn mod_const(&self, d: u64) -> (r: TnumInterval) requires self.wf(), d > 0 ensures r.wf() {
        TnumInterval { tnum: self.tnum.mod_const(d), interval: self.interval.mod_const(d) }.reduce()
    }
    pub fn meet(&self, t: &TnumInterval) -> (r: TnumInterval) requires self.wf(), t.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.meet(&t.tnum), interval: self.interval.meet(&t.interval) }.reduce()
    }
    pub fn lshi(&self, i: u32) -> (r: TnumInterval) requires self.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.lshi(i), interval: Interval::top() }.reduce()
    }
    pub fn rshi(&self, i: u32) -> (r: TnumInterval) requires self.wf() ensures r.wf() {
        TnumInterval { tnum: self.tnum.rshi(i), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn is_const(&self) -> bool { self.tnum.is_const() && self.interval.lo == self.interval.hi }
    #[inline] pub fn min_val(&self) -> u64 {
        let a = self.tnum.min_val(); let b = self.interval.lo;
        if a > b { a } else { b }
    }
    #[inline] pub fn max_val(&self) -> u64 {
        let a = self.tnum.max_val(); let b = self.interval.hi;
        if a < b { a } else { b }
    }
}

// ================================================================
// TAI: Reduced product of Tnum × Anum × Interval
//
// The full abstract domain. Combines:
// - Tnum: precise for bitwise ops, tracks known/unknown bits
// - Anum: precise for arithmetic, tracks exact base + uncertainty
// - Interval: precise for bounds, tracks [lo, hi]
//
// Each operation computes on all three components, then reduces:
// - Tnum bounds tighten the interval
// - Anum bounds tighten the interval
// - Interval bounds tighten the Tnum (clear high uncertain bits)
// - Anum and Tnum cross-inform via conversion
// ================================================================

#[derive(Clone, Copy)]
pub struct ReducedProduct { pub tnum: ExecTnum, pub anum: ExecAnum, pub interval: Interval }

impl ReducedProduct {
    pub open spec fn wf(self) -> bool { self.tnum.wf() && self.interval.wf() }
    pub open spec fn has(self, x: u64) -> bool {
        self.tnum.has(x) && self.anum.has(x) && self.interval.has(x)
    }

    // Future reduction TODOs:
    // - tnum_range: when hi-lo is small, force known high bits in Tnum
    // - Anum→Tnum conversion + meet
    // - Tnum known bits → Anum base adjustment

    #[inline] pub fn constant(n: u64) -> (r: ReducedProduct) ensures r.wf() {
        ReducedProduct { tnum: ExecTnum::constant(n), anum: ExecAnum::constant(n), interval: Interval::constant(n) }
    }
    #[inline] pub fn top() -> (r: ReducedProduct) ensures r.wf() {
        ReducedProduct { tnum: ExecTnum::top(), anum: ExecAnum::top(), interval: Interval::top() }
    }

    /// Reduce: cross-tighten all three components.
    pub fn reduce(&self) -> (r: ReducedProduct)
        requires self.wf()
        ensures r.wf()
    {
        let tn_min = self.tnum.min_val();
        let tn_max = self.tnum.max_val();
        let an_min = self.anum.min_val();
        let an_max = self.anum.max_val();
        let lo = {
            let a = if tn_min > self.interval.lo { tn_min } else { self.interval.lo };
            if an_min > a { an_min } else { a }
        };
        let hi = {
            let a = if tn_max < self.interval.hi { tn_max } else { self.interval.hi };
            if an_max < a { an_max } else { a }
        };
        if hi < lo { return ReducedProduct::top(); }

        // Tighten Tnum from interval: clear uncertain bits above hi
        let possible = ExecAnum::ones_mask(hi);
        let old_v = self.tnum.val;
        let old_m = self.tnum.mask;
        let new_tn_v = old_v & possible;
        let new_tn_m = old_m & possible;
        proof {
            assert((old_v & possible) & (old_m & possible) == 0u64) by(bit_vector)
                requires old_v & old_m == 0u64;
        }
        let tn = ExecTnum { val: new_tn_v, mask: new_tn_m };
        let an = ExecAnum { base: self.anum.base, span: self.anum.span & possible };

        let lo2 = if tn.min_val() > lo { tn.min_val() } else { lo };
        let hi2 = if tn.max_val() < hi { tn.max_val() } else { hi };
        if hi2 < lo2 { ReducedProduct::top() }
        else { ReducedProduct { tnum: tn, anum: an, interval: Interval { lo: lo2, hi: hi2 } } }
    }

    // --- Bitwise ops: Tnum is precise, Anum/Interval get top ---
    #[inline] pub fn bw_or(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.bw_or(&t.tnum), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_and(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.bw_and(&t.tnum), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_xor(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.bw_xor(&t.tnum), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_not(&self) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.bw_not(), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn bw_and_not(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.bw_and_not(&t.tnum), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }

    // --- Arithmetic: Anum is precise, Tnum also computed, Interval added ---
    #[inline] pub fn add(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct {
            tnum: self.tnum.add(&t.tnum),
            anum: self.anum.add(&t.anum),
            interval: self.interval.add(&t.interval),
        }.reduce()
    }
    #[inline] pub fn sub(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct {
            tnum: self.tnum.sub(&t.tnum),
            anum: self.anum.sub(&t.anum),
            interval: Interval::top(),
        }.reduce()
    }
    #[inline] pub fn neg(&self) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.neg(), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    pub fn mul(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct {
            tnum: self.tnum.mul(&t.tnum),
            anum: self.anum.mul(&t.anum),
            interval: self.interval.mul(&t.interval),
        }.reduce()
    }
    pub fn div_const(&self, d: u64) -> (r: ReducedProduct) requires self.wf(), d > 0 ensures r.wf() {
        ReducedProduct {
            tnum: self.tnum.div_const(d),
            anum: self.anum.div_const(d),
            interval: self.interval.div_const(d),
        }.reduce()
    }
    pub fn mod_const(&self, d: u64) -> (r: ReducedProduct) requires self.wf(), d > 0 ensures r.wf() {
        ReducedProduct {
            tnum: self.tnum.mod_const(d),
            anum: ExecAnum::top(), // TODO: Anum mod
            interval: self.interval.mod_const(d),
        }.reduce()
    }

    // --- Shifts ---
    #[inline] pub fn rsh(&self) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.rsh(), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    #[inline] pub fn lsh(&self) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.lsh(), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    pub fn lshi(&self, i: u32) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.lshi(i), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }
    pub fn rshi(&self, i: u32) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
        ReducedProduct { tnum: self.tnum.rshi(i), anum: ExecAnum::top(), interval: Interval::top() }.reduce()
    }

    // --- Lattice ---
    pub fn join(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct {
            tnum: self.tnum.join(&t.tnum),
            anum: ExecAnum::top(), // TODO: Anum join
            interval: self.interval.join(&t.interval),
        }.reduce()
    }
    pub fn meet(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
        ReducedProduct {
            tnum: self.tnum.meet(&t.tnum),
            anum: ExecAnum::top(), // TODO: Anum meet
            interval: self.interval.meet(&t.interval),
        }.reduce()
    }

    // --- Queries ---
    #[inline] pub fn is_const(&self) -> bool { self.tnum.is_const() && self.interval.lo == self.interval.hi }
    #[inline] pub fn min_val(&self) -> u64 {
        let a = self.tnum.min_val();
        let b = self.interval.lo;
        let c = self.anum.min_val();
        let m = if a > b { a } else { b };
        if c > m { c } else { m }
    }
    #[inline] pub fn max_val(&self) -> u64 {
        let a = self.tnum.max_val();
        let b = self.interval.hi;
        let c = self.anum.max_val();
        let m = if a < b { a } else { b };
        if c < m { c } else { m }
    }
}

} // verus!
