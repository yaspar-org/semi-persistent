// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(dead_code)]
/// Fuzz testing for abstract domain soundness.
/// Pure Rust — no Verus. Reimplements the domain ops for testing.
use rand::rngs::StdRng;
use rand::{Rng, RngExt, SeedableRng};
use semi_persistent_abstract_domains::domains::DivAlarm;
use semi_persistent_abstract_domains::domains::d8::{
    ExecAnum as D8ExecAnum, ExecTnum as D8ExecTnum, ExecUnum as D8ExecUnum, Interval as D8Interval,
    ReducedProduct as D8ReducedProduct,
};

const DEFAULT_TEST_SEED: u64 = 0x5eed_5eed;

fn test_rng() -> StdRng {
    let seed = std::env::var("PROPTEST_RNG_SEED")
        .ok()
        .map(|value| value.parse().expect("PROPTEST_RNG_SEED must contain a u64"))
        .unwrap_or(DEFAULT_TEST_SEED);
    StdRng::seed_from_u64(seed)
}

// ================================================================
// Domain types (mirror the Verus definitions)
// ================================================================

#[derive(Clone, Copy, Debug)]
struct ExecTnum {
    val: u64,
    mask: u64,
}
#[derive(Clone, Copy, Debug)]
struct ExecAnum {
    base: u64,
    span: u64,
}
#[derive(Clone, Copy, Debug)]
struct Interval {
    is_bottom: bool,
    lo: u64,
    hi: u64,
}

impl ExecTnum {
    fn wf(&self) -> bool {
        self.val & self.mask == 0
    }
    fn constant(n: u64) -> Self {
        ExecTnum { val: n, mask: 0 }
    }
    fn top() -> Self {
        ExecTnum { val: 0, mask: !0 }
    }
    fn contains(&self, x: u64) -> bool {
        (x & !self.mask) == self.val
    }
    fn bw_or(&self, t: &ExecTnum) -> ExecTnum {
        let v = self.val | t.val;
        ExecTnum {
            val: v,
            mask: (self.mask | t.mask) & !v,
        }
    }
    fn bw_and(&self, t: &ExecTnum) -> ExecTnum {
        ExecTnum {
            val: self.val & t.val,
            mask: self.mask | t.mask,
        }
    }
    fn bw_xor(&self, t: &ExecTnum) -> ExecTnum {
        let v = self.val ^ t.val;
        let m = self.mask | t.mask;
        ExecTnum {
            val: v & !m,
            mask: m,
        }
    }
    fn bw_not(&self) -> ExecTnum {
        self.bw_xor(&ExecTnum { val: !0, mask: 0 })
    }
    fn add(&self, t: &ExecTnum) -> ExecTnum {
        let lbv = self.val.wrapping_add(t.val);
        let lbm = self.mask.wrapping_add(t.mask);
        let ub = lbv.wrapping_add(lbm);
        let mask = (ub ^ lbv) | self.mask | t.mask;
        ExecTnum {
            val: lbv & !mask,
            mask,
        }
    }
    fn neg(&self) -> ExecTnum {
        self.bw_not().add(&ExecTnum::constant(1))
    }
    fn sub(&self, t: &ExecTnum) -> ExecTnum {
        self.add(&t.neg())
    }
    fn rsh(&self) -> ExecTnum {
        ExecTnum {
            val: self.val >> 1,
            mask: self.mask >> 1,
        }
    }
    fn lsh(&self) -> ExecTnum {
        ExecTnum {
            val: self.val << 1,
            mask: self.mask << 1,
        }
    }
    fn join(&self, t: &ExecTnum) -> ExecTnum {
        let v = self.val & t.val;
        let u = (self.val ^ self.mask) | (t.val ^ t.mask);
        let m = v ^ u;
        ExecTnum {
            val: v & !m,
            mask: m,
        }
    }
    fn mul(&self, t: &ExecTnum) -> ExecTnum {
        let mut acc = ExecTnum::constant(0);
        let mut md = *self;
        let mut mr = t.val;
        let mut mm = t.mask;
        for _ in 0..64 {
            if (mr & 1) == 1 {
                acc = acc.add(&md);
            } else if (mm & 1) == 1 {
                acc = acc.add(&ExecTnum {
                    val: 0,
                    mask: md.val | md.mask,
                });
            }
            md = md.lsh();
            mr >>= 1;
            mm >>= 1;
        }
        acc
    }
}

impl ExecAnum {
    fn contains(&self, x: u64) -> bool {
        x >= self.base && (x - self.base) & !self.span == 0
    }
    fn add(&self, t: &ExecAnum) -> ExecAnum {
        let v = self.base.wrapping_add(t.base);
        let sm = self.span.wrapping_add(t.span) | self.span | t.span;
        let max1 = self.base.wrapping_add(self.span);
        let max2 = t.base.wrapping_add(t.span);
        let max_sum = max1.wrapping_add(max2);
        if max1 < self.base
            || max2 < t.base
            || max_sum < max1
            || max_sum < max2
            || v < self.base
            || sm < self.span
        {
            return ExecAnum { base: 0, span: !0 };
        }
        ExecAnum { base: v, span: sm }
    }
    fn div_const(&self, d: u64) -> ExecAnum {
        let min_q = self.base / d;
        let max_q = self.base.wrapping_add(self.span) / d;
        if max_q < min_q {
            return ExecAnum { base: 0, span: !0 };
        }
        let range = max_q - min_q;
        let mut mask = if range == 0 { 0u64 } else { 1u64 };
        while mask < range {
            mask = mask.wrapping_mul(2).wrapping_add(1);
            if mask == !0 {
                break;
            }
        }
        ExecAnum {
            base: min_q,
            span: mask,
        }
    }
}

impl Interval {
    fn wf(&self) -> bool {
        if self.is_bottom {
            self.lo == 0 && self.hi == 0
        } else {
            self.lo <= self.hi
        }
    }
    fn contains(&self, x: u64) -> bool {
        !self.is_bottom && self.lo <= x && x <= self.hi
    }
    fn bottom() -> Interval {
        Interval {
            is_bottom: true,
            lo: 0,
            hi: 0,
        }
    }
    fn top() -> Interval {
        Interval {
            is_bottom: false,
            lo: 0,
            hi: !0,
        }
    }
    fn bw_or(&self, t: &Interval) -> Interval {
        if self.is_bottom || t.is_bottom {
            Interval::bottom()
        } else {
            Interval::top()
        }
    }
    fn bw_and(&self, t: &Interval) -> Interval {
        if self.is_bottom || t.is_bottom {
            Interval::bottom()
        } else {
            Interval::top()
        }
    }
    fn bw_xor(&self, t: &Interval) -> Interval {
        if self.is_bottom || t.is_bottom {
            Interval::bottom()
        } else {
            Interval::top()
        }
    }
    fn add(&self, t: &Interval) -> Interval {
        if self.is_bottom || t.is_bottom {
            return Interval::bottom();
        }
        let lo = self.lo.wrapping_add(t.lo);
        let hi = self.hi.wrapping_add(t.hi);
        if lo < self.lo || hi < self.hi || hi < lo {
            Interval::top()
        } else {
            Interval {
                is_bottom: false,
                lo,
                hi,
            }
        }
    }
    fn sub(&self, t: &Interval) -> Interval {
        if self.is_bottom || t.is_bottom {
            return Interval::bottom();
        }
        if self.lo < t.hi {
            return Interval::top();
        }
        Interval {
            is_bottom: false,
            lo: self.lo.wrapping_sub(t.hi),
            hi: self.hi.wrapping_sub(t.lo),
        }
    }
    fn mul(&self, t: &Interval) -> Interval {
        if self.is_bottom || t.is_bottom {
            return Interval::bottom();
        }
        let hi = match self.hi.checked_mul(t.hi) {
            Some(value) => value,
            None => return Interval::top(),
        };
        let lo = match self.lo.checked_mul(t.lo) {
            Some(value) => value,
            None => return Interval::top(),
        };
        Interval {
            is_bottom: false,
            lo,
            hi,
        }
    }
    fn neg(&self) -> Interval {
        if self.is_bottom {
            return Interval::bottom();
        }
        if self.lo == 0 {
            return if self.hi == 0 {
                Interval {
                    is_bottom: false,
                    lo: 0,
                    hi: 0,
                }
            } else {
                Interval::top()
            };
        }
        Interval {
            is_bottom: false,
            lo: 0u64.wrapping_sub(self.hi),
            hi: 0u64.wrapping_sub(self.lo),
        }
    }
    fn rsh(&self) -> Interval {
        if self.is_bottom {
            Interval::bottom()
        } else {
            Interval {
                is_bottom: false,
                lo: self.lo >> 1,
                hi: self.hi >> 1,
            }
        }
    }
    fn lsh(&self) -> Interval {
        if self.is_bottom {
            return Interval::bottom();
        }
        if self.hi > u64::MAX >> 1 {
            return Interval::top();
        }
        Interval {
            is_bottom: false,
            lo: self.lo << 1,
            hi: self.hi << 1,
        }
    }
}

// ================================================================
// Random generation + sampling
// ================================================================

fn rand_etn(rng: &mut impl Rng) -> ExecTnum {
    let m: u64 = rng.random();
    let v = rng.random::<u64>() & !m;
    ExecTnum { val: v, mask: m }
}
fn rand_ean(rng: &mut impl Rng) -> ExecAnum {
    ExecAnum {
        base: rng.random(),
        span: rng.random(),
    }
}
fn rand_interval(rng: &mut impl Rng) -> Interval {
    let (a, b): (u64, u64) = (rng.random(), rng.random());
    if a <= b {
        Interval {
            is_bottom: false,
            lo: a,
            hi: b,
        }
    } else {
        Interval {
            is_bottom: false,
            lo: b,
            hi: a,
        }
    }
}
fn sample_etn(tn: &ExecTnum, rng: &mut impl Rng) -> u64 {
    tn.val | (rng.random::<u64>() & tn.mask)
}
fn sample_ean(an: &ExecAnum, rng: &mut impl Rng) -> u64 {
    an.base
        .checked_add(rng.random::<u64>() & an.span)
        .unwrap_or(an.base)
}
fn sample_interval(iv: &Interval, rng: &mut impl Rng) -> u64 {
    if iv.lo == iv.hi {
        iv.lo
    } else {
        iv.lo
            .wrapping_add(rng.random::<u64>() % (iv.hi - iv.lo + 1))
    }
}

// ================================================================
// Tests
// ================================================================

#[cfg(debug_assertions)]
const N: usize = 10_000;
#[cfg(not(debug_assertions))]
const N: usize = 1_000_000;
const S: usize = 8;

macro_rules! fuzz_binop {
    ($name:ident, $ty:ident, $rand:ident, $sample:ident, $contains:ident, $abs_op:ident, $conc_op:expr) => {
        #[test]
        fn $name() {
            let mut rng = test_rng();
            for _ in 0..N {
                let ax = $rand(&mut rng);
                let ay = $rand(&mut rng);
                let ar = ax.$abs_op(&ay);
                for _ in 0..S {
                    let x = $sample(&ax, &mut rng);
                    let y = $sample(&ay, &mut rng);
                    let r = $conc_op(x, y);
                    assert!(
                        ar.$contains(r),
                        "UNSOUND {}::{}: ax={:?} ay={:?} x={:#x} y={:#x} r={:#x} ar={:?}",
                        stringify!($ty),
                        stringify!($abs_op),
                        ax,
                        ay,
                        x,
                        y,
                        r,
                        ar
                    );
                }
            }
        }
    };
}

macro_rules! fuzz_unop {
    ($name:ident, $rand:ident, $sample:ident, $abs_op:ident, $conc_op:expr) => {
        #[test]
        fn $name() {
            let mut rng = test_rng();
            for _ in 0..N {
                let ax = $rand(&mut rng);
                let ar = ax.$abs_op();
                for _ in 0..S {
                    let x = $sample(&ax, &mut rng);
                    let r = $conc_op(x);
                    assert!(
                        ar.contains(r),
                        "UNSOUND ExecTnum::{}: ax={:?} x={:#x} r={:#x} ar={:?}",
                        stringify!($abs_op),
                        ax,
                        x,
                        r,
                        ar
                    );
                }
            }
        }
    };
}

// ExecTnum binary
fuzz_binop!(
    fuzz_etn_or,
    ExecTnum,
    rand_etn,
    sample_etn,
    contains,
    bw_or,
    |x: u64, y: u64| x | y
);
fuzz_binop!(
    fuzz_etn_and,
    ExecTnum,
    rand_etn,
    sample_etn,
    contains,
    bw_and,
    |x: u64, y: u64| x & y
);
fuzz_binop!(
    fuzz_etn_xor,
    ExecTnum,
    rand_etn,
    sample_etn,
    contains,
    bw_xor,
    |x: u64, y: u64| x ^ y
);
fuzz_binop!(
    fuzz_etn_plus,
    ExecTnum,
    rand_etn,
    sample_etn,
    contains,
    add,
    |x: u64, y: u64| x.wrapping_add(y)
);
fuzz_binop!(
    fuzz_etn_sub,
    ExecTnum,
    rand_etn,
    sample_etn,
    contains,
    sub,
    |x: u64, y: u64| x.wrapping_sub(y)
);
fuzz_binop!(
    fuzz_etn_mul,
    ExecTnum,
    rand_etn,
    sample_etn,
    contains,
    mul,
    |x: u64, y: u64| x.wrapping_mul(y)
);

// ExecTnum unary
fuzz_unop!(fuzz_etn_neg, rand_etn, sample_etn, neg, |x: u64| x
    .wrapping_neg());
fuzz_unop!(fuzz_etn_not, rand_etn, sample_etn, bw_not, |x: u64| !x);
fuzz_unop!(fuzz_etn_rsh, rand_etn, sample_etn, rsh, |x: u64| x >> 1);
fuzz_unop!(fuzz_etn_lsh, rand_etn, sample_etn, lsh, |x: u64| x << 1);

// ExecTnum join
#[test]
fn fuzz_etn_join() {
    let mut rng = test_rng();
    for _ in 0..N {
        let ax = rand_etn(&mut rng);
        let ay = rand_etn(&mut rng);
        let ar = ax.join(&ay);
        for _ in 0..S {
            assert!(
                ar.contains(sample_etn(&ax, &mut rng)),
                "join doesn't contain x"
            );
            assert!(
                ar.contains(sample_etn(&ay, &mut rng)),
                "join doesn't contain y"
            );
        }
    }
}

// EAn
fuzz_binop!(
    fuzz_ean_plus,
    ExecAnum,
    rand_ean,
    sample_ean,
    contains,
    add,
    |x: u64, y: u64| x.wrapping_add(y)
);

#[test]
fn fuzz_ean_div() {
    let mut rng = test_rng();
    for _ in 0..N {
        let ax = rand_ean(&mut rng);
        let d = (rng.random::<u64>() % 255) + 1;
        let ar = ax.div_const(d);
        for _ in 0..S {
            let x = sample_ean(&ax, &mut rng);
            let r = x / d;
            assert!(
                ar.contains(r),
                "UNSOUND ExecAnum::div_const: ax={:?} d={} x={:#x} r={:#x} ar={:?}",
                ax,
                d,
                x,
                r,
                ar
            );
        }
    }
}

// Interval
fuzz_binop!(
    fuzz_iv_or,
    Interval,
    rand_interval,
    sample_interval,
    contains,
    bw_or,
    |x: u64, y: u64| x | y
);
fuzz_binop!(
    fuzz_iv_and,
    Interval,
    rand_interval,
    sample_interval,
    contains,
    bw_and,
    |x: u64, y: u64| x & y
);
fuzz_binop!(
    fuzz_iv_xor,
    Interval,
    rand_interval,
    sample_interval,
    contains,
    bw_xor,
    |x: u64, y: u64| x ^ y
);
fuzz_binop!(
    fuzz_iv_plus,
    Interval,
    rand_interval,
    sample_interval,
    contains,
    add,
    |x: u64, y: u64| {
        let (r, of) = x.overflowing_add(y);
        if of { 0u64 } else { r } // skip overflow cases
    }
);
fuzz_binop!(
    fuzz_iv_sub,
    Interval,
    rand_interval,
    sample_interval,
    contains,
    sub,
    |x: u64, y: u64| x.wrapping_sub(y)
);
fuzz_binop!(
    fuzz_iv_mul,
    Interval,
    rand_interval,
    sample_interval,
    contains,
    mul,
    |x: u64, y: u64| x.wrapping_mul(y)
);
fuzz_unop!(
    fuzz_iv_neg,
    rand_interval,
    sample_interval,
    neg,
    |x: u64| x.wrapping_neg()
);
fuzz_unop!(
    fuzz_iv_rsh,
    rand_interval,
    sample_interval,
    rsh,
    |x: u64| x >> 1
);
fuzz_unop!(
    fuzz_iv_lsh,
    rand_interval,
    sample_interval,
    lsh,
    |x: u64| x << 1
);

// ================================================================
// ExecUnum (Unum) — horizontally composable additive tristate numbers
// ================================================================

#[derive(Clone, Copy, Debug)]
struct ExecUnum {
    base: u64,
    walls: u64,
    extent: u64,
}

// Helper: iterate bitfields defined by w. Calls f(field_start, field_end) for each.
fn for_each_field(w: u64, mut f: impl FnMut(u32, u32)) {
    let mut pos = 0u32;
    while pos < 64 {
        let w_shifted = w >> pos;
        if w_shifted == 0 {
            break;
        }
        let field_start = pos + w_shifted.trailing_zeros();
        let field_end = if field_start + 1 >= 64 {
            64
        } else {
            let w_after = w >> (field_start + 1);
            if w_after == 0 {
                64
            } else {
                field_start + 1 + w_after.trailing_zeros()
            }
        };
        f(field_start, field_end);
        pos = field_end;
    }
}

fn field_mask(start: u32, end: u32) -> u64 {
    let width = end - start;
    if width >= 64 {
        !0u64
    } else {
        ((1u64 << width) - 1) << start
    }
}

impl ExecUnum {
    fn constant(n: u64) -> Self {
        ExecUnum {
            base: n,
            walls: !0,
            extent: 0,
        }
    }
    fn top() -> Self {
        ExecUnum {
            base: 0,
            walls: 0,
            extent: !0,
        }
    }

    fn add(&self, t: &ExecUnum) -> ExecUnum {
        let v = self.base.wrapping_add(t.base);
        let x12 = self.extent.wrapping_add(t.extent);
        let max1 = self.base.wrapping_add(self.extent);
        let max2 = t.base.wrapping_add(t.extent);
        let max_sum = max1.wrapping_add(max2);
        if v < self.base
            || v < t.base
            || x12 < self.extent
            || x12 < t.extent
            || max1 < self.base
            || max2 < t.base
            || max_sum < max1
            || max_sum < max2
        {
            return ExecUnum::top();
        }
        let cout = (self.extent & t.extent) | ((self.extent | t.extent) & !x12);
        let carry_in = cout << 1;
        let w = (self.walls & t.walls) & !carry_in;
        ExecUnum {
            base: v,
            walls: w,
            extent: x12,
        }
    }

    fn neg(&self) -> ExecUnum {
        if self.base.checked_add(self.extent).is_none() {
            return ExecUnum::top();
        }
        let new_v = 0u64.wrapping_sub(self.base).wrapping_sub(self.extent);
        ExecUnum {
            base: new_v,
            walls: self.walls,
            extent: self.extent,
        }
    }

    fn sub(&self, t: &ExecUnum) -> ExecUnum {
        self.add(&t.neg())
    }

    fn mul(&self, t: &ExecUnum) -> ExecUnum {
        let v1 = self.base;
        let x1 = self.extent;
        let v2 = t.base;
        let x2 = t.extent;
        let Some(max1) = v1.checked_add(x1) else {
            return ExecUnum::top();
        };
        let Some(max2) = v2.checked_add(x2) else {
            return ExecUnum::top();
        };
        if max1.checked_mul(max2).is_none() {
            return ExecUnum::top();
        }
        let Some(base) = v1.checked_mul(v2) else {
            return ExecUnum::top();
        };
        let Some(v1x2) = v1.checked_mul(x2) else {
            return ExecUnum::top();
        };
        let Some(v2x1) = v2.checked_mul(x1) else {
            return ExecUnum::top();
        };
        let Some(x1x2) = x1.checked_mul(x2) else {
            return ExecUnum::top();
        };
        let Some(unc1) = v1x2.checked_add(v2x1) else {
            return ExecUnum::top();
        };
        let Some(unc) = unc1.checked_add(x1x2) else {
            return ExecUnum::top();
        };
        if base.checked_add(unc).is_none() {
            return ExecUnum::top();
        }
        ExecUnum {
            base,
            walls: 0,
            extent: unc,
        }
    }

    fn to_ean(self) -> ExecAnum {
        // Match the executable implementation: widen the whole register.
        let mut m = if self.extent == 0 { 0u64 } else { 1u64 };
        while m < self.extent {
            m = m.wrapping_mul(2).wrapping_add(1);
            if m == !0 {
                break;
            }
        }
        ExecAnum {
            base: self.base,
            span: m,
        }
    }

    fn to_etn(self) -> ExecTnum {
        let an = self.to_ean();
        // Sound Anum->Tnum: the Anum set is {v..v+m} (with bit constraints).
        // The Tnum must contain all of those. Use the Anum's own to_etn
        // which computes ETn(v & ~m, m). But this is only sound when v & m == 0.
        // For general Anums, we need to widen m to cover carry effects.
        // Safe: compute the Tnum plus of Tn(v,0) + Tn(0,m).
        let lbv = an.base;
        let lbm = an.span;
        let ub = lbv.wrapping_add(lbm);
        let mask = (ub ^ lbv) | an.span;
        ExecTnum {
            val: lbv & !mask,
            mask,
        }
    }

    fn from_ean(a: &ExecAnum) -> ExecUnum {
        ExecUnum {
            base: a.base,
            walls: !0,
            extent: a.span,
        }
    }

    fn from_interval(lo: u64, hi: u64) -> ExecUnum {
        if lo == hi {
            return ExecUnum::constant(lo);
        }
        ExecUnum {
            base: lo,
            walls: 0,
            extent: hi - lo,
        }
    }

    fn contains(&self, y: u64) -> bool {
        if y < self.base {
            return false;
        }
        let d = y - self.base;
        let mut borrow = false;
        for bit in 0..64 {
            let leader = (self.walls >> bit) & 1 == 1;
            if bit > 0 && leader && borrow {
                return false;
            }
            let x_bit = (self.extent >> bit) & 1;
            let d_bit = (d >> bit) & 1;
            borrow = x_bit < d_bit + u64::from(borrow);
        }
        !borrow
    }

    fn min_val(&self) -> u64 {
        self.base
    }
    fn max_val(&self) -> u64 {
        self.base.wrapping_add(self.extent)
    }
}

fn rand_eun(rng: &mut impl Rng) -> ExecUnum {
    let v: u64 = rng.random();
    let w: u64 = rng.random::<u64>() | 1; // bit 0 must be a leader
    let mut x: u64 = 0;
    for_each_field(w, |start, end| {
        let width = end - start;
        let field_max = if width == 1 {
            rng.random::<u64>() & 1
        } else if width >= 64 {
            rng.random::<u64>() | (1u64 << 63)
        } else {
            let leading = 1u64 << (width - 1);
            leading | (rng.random::<u64>() & (leading - 1))
        };
        x |= field_max << start;
    });
    ExecUnum {
        base: v,
        walls: w,
        extent: x,
    }
}

fn sample_eun(un: &ExecUnum, rng: &mut impl Rng) -> u64 {
    let mut d: u64 = 0;
    for_each_field(un.walls, |start, end| {
        let width = end - start;
        let fm = if width >= 64 {
            !0u64
        } else {
            (1u64 << width) - 1
        };
        let x_field = (un.extent >> start) & fm;
        let val = if x_field == 0 {
            0
        } else if x_field == !0u64 {
            rng.random()
        } else {
            rng.random::<u64>() % (x_field + 1)
        };
        d |= val << start;
    });
    un.base.checked_add(d).unwrap_or(un.base)
}

// ----------------------------------------------------------------
// Representation tests
// ----------------------------------------------------------------

#[test]
fn fuzz_eun_self_contains() {
    let mut rng = test_rng();
    for _ in 0..N {
        let un = rand_eun(&mut rng);
        for _ in 0..S {
            let x = sample_eun(&un, &mut rng);
            assert!(un.contains(x), "self-containment: un={:?} x={:#x}", un, x);
        }
    }
}

#[test]
fn fuzz_eun_constant() {
    let mut rng = test_rng();
    for _ in 0..N {
        let n: u64 = rng.random();
        let un = ExecUnum::constant(n);
        assert!(un.contains(n), "constant({:#x}) doesn't contain itself", n);
        let other: u64 = rng.random();
        if other != n {
            assert!(
                !un.contains(other),
                "constant({:#x}) contains {:#x}",
                n,
                other
            );
        }
    }
}

#[test]
fn fuzz_eun_top() {
    let mut rng = test_rng();
    let t = ExecUnum::top();
    for _ in 0..N {
        let x: u64 = rng.random();
        assert!(t.contains(x), "top doesn't contain {:#x}", x);
    }
}

#[test]
fn fuzz_eun_min_max() {
    let mut rng = test_rng();
    for _ in 0..N {
        let un = rand_eun(&mut rng);
        assert!(un.contains(un.min_val()), "doesn't contain min: {:?}", un);
        if un.base.checked_add(un.extent).is_some() {
            assert!(un.contains(un.max_val()), "doesn't contain max: {:?}", un);
        }
    }
}

#[test]
fn eun_add_returns_top_when_the_represented_range_wraps() {
    let a = ExecUnum {
        base: u64::MAX - 10,
        walls: 0,
        extent: 5,
    };
    let b = ExecUnum {
        base: 0,
        walls: 0,
        extent: 20,
    };
    let result = a.add(&b);
    assert!(result.contains((u64::MAX - 10).wrapping_add(20)));
    assert_eq!(result.base, 0);
    assert_eq!(result.extent, u64::MAX);
}

#[test]
fn eun_mul_returns_top_when_base_plus_uncertainty_wraps() {
    let a = ExecUnum {
        base: u64::MAX / 2,
        walls: 0,
        extent: 1,
    };
    let b = ExecUnum {
        base: 2,
        walls: 0,
        extent: 0,
    };
    let result = a.mul(&b);
    assert!(result.contains(u64::MAX - 1));
    assert_eq!(result.base, 0);
    assert_eq!(result.extent, u64::MAX);
}

// ----------------------------------------------------------------
// Conversion tests
// ----------------------------------------------------------------

#[test]
fn fuzz_eun_to_ean_sound() {
    let mut rng = test_rng();
    for _ in 0..N {
        let un = rand_eun(&mut rng);
        let an = un.to_ean();
        for _ in 0..S {
            let x = sample_eun(&un, &mut rng);
            assert!(
                an.contains(x),
                "to_ean unsound: un={:?} an={:?} x={:#x}",
                un,
                an,
                x
            );
        }
    }
}

#[test]
fn fuzz_eun_to_etn_sound() {
    let mut rng = test_rng();
    for _ in 0..N {
        let un = rand_eun(&mut rng);
        let tn = un.to_etn();
        for _ in 0..S {
            let x = sample_eun(&un, &mut rng);
            assert!(
                tn.contains(x),
                "to_etn unsound: un={:?} tn={:?} x={:#x}",
                un,
                tn,
                x
            );
        }
    }
}

#[test]
fn fuzz_eun_from_ean_sound() {
    let mut rng = test_rng();
    for _ in 0..N {
        let an = rand_ean(&mut rng);
        let un = ExecUnum::from_ean(&an);
        for _ in 0..S {
            let x = sample_ean(&an, &mut rng);
            assert!(
                un.contains(x),
                "from_ean unsound: an={:?} un={:?} x={:#x}",
                an,
                un,
                x
            );
        }
    }
}

#[test]
fn fuzz_eun_from_interval_sound() {
    let mut rng = test_rng();
    for _ in 0..N {
        let iv = rand_interval(&mut rng);
        let un = ExecUnum::from_interval(iv.lo, iv.hi);
        for _ in 0..S {
            let x = sample_interval(&iv, &mut rng);
            assert!(
                un.contains(x),
                "from_interval unsound: iv={:?} un={:?} x={:#x}",
                iv,
                un,
                x
            );
        }
    }
}

// ----------------------------------------------------------------
// Arithmetic soundness tests
// ----------------------------------------------------------------

fuzz_binop!(
    fuzz_eun_plus,
    ExecUnum,
    rand_eun,
    sample_eun,
    contains,
    add,
    |x: u64, y: u64| x.wrapping_add(y)
);

fuzz_binop!(
    fuzz_eun_sub,
    ExecUnum,
    rand_eun,
    sample_eun,
    contains,
    sub,
    |x: u64, y: u64| x.wrapping_sub(y)
);

fuzz_binop!(
    fuzz_eun_mul,
    ExecUnum,
    rand_eun,
    sample_eun,
    contains,
    mul,
    |x: u64, y: u64| x.wrapping_mul(y)
);

#[test]
fn fuzz_eun_neg() {
    let mut rng = test_rng();
    for _ in 0..N {
        let ax = rand_eun(&mut rng);
        let ar = ax.neg();
        for _ in 0..S {
            let x = sample_eun(&ax, &mut rng);
            let r = x.wrapping_neg();
            assert!(
                ar.contains(r),
                "neg unsound: ax={:?} x={:#x} r={:#x} ar={:?}",
                ax,
                x,
                r,
                ar
            );
        }
    }
}

// ----------------------------------------------------------------
// Structural properties
// ----------------------------------------------------------------

#[test]
fn fuzz_eun_plus_commutative() {
    let mut rng = test_rng();
    for _ in 0..N {
        let a = rand_eun(&mut rng);
        let b = rand_eun(&mut rng);
        let ab = a.add(&b);
        let ba = b.add(&a);
        for _ in 0..S {
            let va = sample_eun(&a, &mut rng);
            let vb = sample_eun(&b, &mut rng);
            let sum = va.wrapping_add(vb);
            assert!(
                ab.contains(sum),
                "a+b unsound: a={:?} b={:?} va={:#x} vb={:#x} sum={:#x} ab={:?}",
                a,
                b,
                va,
                vb,
                sum,
                ab
            );
            assert!(
                ba.contains(sum),
                "b+a unsound: a={:?} b={:?} va={:#x} vb={:#x} sum={:#x} ba={:?}",
                a,
                b,
                va,
                vb,
                sum,
                ba
            );
        }
    }
}

#[test]
fn fuzz_eun_plus_assoc() {
    let mut rng = test_rng();
    for _ in 0..N {
        let a = rand_eun(&mut rng);
        let b = rand_eun(&mut rng);
        let c = rand_eun(&mut rng);
        let ab_c = a.add(&b).add(&c);
        let a_bc = a.add(&b.add(&c));
        for _ in 0..S {
            let va = sample_eun(&a, &mut rng);
            let vb = sample_eun(&b, &mut rng);
            let vc = sample_eun(&c, &mut rng);
            let sum = va.wrapping_add(vb).wrapping_add(vc);
            assert!(
                ab_c.contains(sum),
                "(a+b)+c unsound: a={:?} b={:?} c={:?} sum={:#x} ab_c={:?}",
                a,
                b,
                c,
                sum,
                ab_c
            );
            assert!(
                a_bc.contains(sum),
                "a+(b+c) unsound: a={:?} b={:?} c={:?} sum={:#x} a_bc={:?}",
                a,
                b,
                c,
                sum,
                a_bc
            );
        }
    }
}

// ----------------------------------------------------------------
// Identity elements
// ----------------------------------------------------------------

#[test]
fn division_alarm_truth_table_and_join_laws() {
    use DivAlarm::{DefiniteError, MaybeError, NoError};

    assert!(NoError.has(false));
    assert!(!NoError.has(true));
    assert!(!DefiniteError.has(false));
    assert!(DefiniteError.has(true));
    assert!(MaybeError.has(false));
    assert!(MaybeError.has(true));

    let alarms = [NoError, DefiniteError, MaybeError];
    for left in alarms {
        assert!(left.join(&left) == left);
        for right in alarms {
            let joined = left.join(&right);
            assert!(joined == right.join(&left));
            for error in [false, true] {
                assert_eq!(joined.has(error), left.has(error) || right.has(error));
            }
            for third in alarms {
                assert!(left.join(&right).join(&third) == left.join(&right.join(&third)));
            }
        }
    }

    assert!(NoError.join(&DefiniteError) == MaybeError);
    assert!(NoError.join(&MaybeError) == MaybeError);
    assert!(DefiniteError.join(&MaybeError) == MaybeError);
}

#[test]
fn production_interval_bottom_is_empty_and_canonical() {
    let bottom = D8Interval::bottom();
    assert!(bottom.is_bottom);
    assert_eq!(bottom.lo, 0);
    assert_eq!(bottom.hi, 0);

    let seven = D8Interval::constant(7);
    assert!(bottom.add(&seven).is_bottom);
    assert!(bottom.meet(&seven).is_bottom);
    assert!(bottom.div_const(1).is_bottom);

    let joined = bottom.join(&seven);
    assert!(!joined.is_bottom);
    assert_eq!(joined.lo, 7);
    assert_eq!(joined.hi, 7);

    let disjoint = D8Interval::constant(1).meet(&D8Interval::constant(2));
    assert!(disjoint.is_bottom);
}

fn d8_interval_eq(a: &D8Interval, b: &D8Interval) -> bool {
    a.is_bottom == b.is_bottom && a.lo == b.lo && a.hi == b.hi
}

fn d8_interval_contains(iv: &D8Interval, value: u8) -> bool {
    !iv.is_bottom && iv.lo <= value && value <= iv.hi
}

fn d8_reduced_from_interval(interval: D8Interval) -> D8ReducedProduct {
    D8ReducedProduct {
        tnum: D8ExecTnum::top(),
        anum: D8ExecAnum::top(),
        interval,
        unum: D8ExecUnum::top(),
    }
}

fn d8_reduced_div_result_contains(value: &D8ReducedProduct, concrete: u8) -> bool {
    let tnum_contains = concrete & !value.tnum.mask == value.tnum.val;
    let anum_contains =
        concrete >= value.anum.base && (concrete - value.anum.base) & !value.anum.span == 0;
    let unum_contains =
        concrete >= value.unum.base && concrete - value.unum.base <= value.unum.extent;
    tnum_contains
        && anum_contains
        && d8_interval_contains(&value.interval, concrete)
        && unum_contains
}

fn small_d8_intervals() -> Vec<D8Interval> {
    let mut intervals = vec![D8Interval::bottom(), D8Interval::top()];
    for lo in 0u8..=7 {
        for hi in lo..=7 {
            intervals.push(D8Interval {
                is_bottom: false,
                lo,
                hi,
            });
        }
    }
    intervals
}

#[test]
fn production_interval_lattice_laws_small_exhaustive() {
    let intervals = small_d8_intervals();
    let bottom = D8Interval::bottom();
    let top = D8Interval::top();

    for a in &intervals {
        assert!(d8_interval_eq(&a.meet(a), a));
        assert!(d8_interval_eq(&a.join(a), a));
        assert!(d8_interval_eq(&a.meet(&top), a));
        assert!(d8_interval_eq(&a.join(&bottom), a));
        assert!(d8_interval_eq(&a.meet(&bottom), &bottom));
        assert!(d8_interval_eq(&a.join(&top), &top));

        for b in &intervals {
            let ab_meet = a.meet(b);
            let ab_join = a.join(b);
            assert!(d8_interval_eq(&ab_meet, &b.meet(a)));
            assert!(d8_interval_eq(&ab_join, &b.join(a)));

            for value in u8::MIN..=u8::MAX {
                assert_eq!(
                    d8_interval_contains(&ab_meet, value),
                    d8_interval_contains(a, value) && d8_interval_contains(b, value),
                );
                assert!(!d8_interval_contains(a, value) || d8_interval_contains(&ab_join, value));
                assert!(!d8_interval_contains(b, value) || d8_interval_contains(&ab_join, value));
            }

            for c in &intervals {
                let ab_c_meet = ab_meet.meet(c);
                let a_bc_meet = a.meet(&b.meet(c));
                assert!(d8_interval_eq(&ab_c_meet, &a_bc_meet));

                let ab_c_join = ab_join.join(c);
                let a_bc_join = a.join(&b.join(c));
                assert!(d8_interval_eq(&ab_c_join, &a_bc_join));
            }
        }
    }
}

#[test]
fn production_interval_rsh_small_exhaustive() {
    let bottom = D8Interval::bottom().rsh();
    assert!(bottom.is_bottom);
    assert_eq!(bottom.lo, 0);
    assert_eq!(bottom.hi, 0);

    let top = D8Interval::top().rsh();
    assert!(!top.is_bottom);
    assert_eq!(top.lo, 0);
    assert_eq!(top.hi, u8::MAX >> 1);

    for interval in small_d8_intervals() {
        let shifted = interval.rsh();
        if interval.is_bottom {
            assert!(shifted.is_bottom);
            continue;
        }

        assert!(!shifted.is_bottom);
        assert_eq!(shifted.lo, interval.lo >> 1);
        assert_eq!(shifted.hi, interval.hi >> 1);
        for value in u8::MIN..=u8::MAX {
            if d8_interval_contains(&interval, value) {
                assert!(d8_interval_contains(&shifted, value >> 1));
            }
        }
    }
}

#[test]
fn production_interval_lsh_u8_exhaustive() {
    let bottom = D8Interval::bottom().lsh();
    assert!(bottom.is_bottom);
    assert_eq!(bottom.lo, 0);
    assert_eq!(bottom.hi, 0);

    let top = D8Interval::top();
    for lo in u8::MIN..=u8::MAX {
        for hi in lo..=u8::MAX {
            let interval = D8Interval {
                is_bottom: false,
                lo,
                hi,
            };
            let shifted = interval.lsh();
            if hi > u8::MAX >> 1 {
                assert!(d8_interval_eq(&shifted, &top));
            } else {
                assert!(!shifted.is_bottom);
                assert_eq!(shifted.lo, lo << 1);
                assert_eq!(shifted.hi, hi << 1);
            }

            for value in lo..=hi {
                assert!(d8_interval_contains(&shifted, value << 1));
            }
        }
    }
}

fn arithmetic_d8_intervals() -> Vec<D8Interval> {
    let mut intervals = small_d8_intervals();
    intervals.extend([
        D8Interval {
            is_bottom: false,
            lo: 127,
            hi: 128,
        },
        D8Interval {
            is_bottom: false,
            lo: 128,
            hi: u8::MAX,
        },
        D8Interval {
            is_bottom: false,
            lo: 254,
            hi: u8::MAX,
        },
        D8Interval::constant(u8::MAX),
    ]);
    intervals
}

#[test]
fn production_interval_bitwise_small_exhaustive() {
    let intervals = arithmetic_d8_intervals();
    let bottom = D8Interval::bottom();
    let top = D8Interval::top();

    for left in &intervals {
        for right in &intervals {
            let or_result = left.bw_or(right);
            let and_result = left.bw_and(right);
            let xor_result = left.bw_xor(right);
            if left.is_bottom || right.is_bottom {
                assert!(d8_interval_eq(&or_result, &bottom));
                assert!(d8_interval_eq(&and_result, &bottom));
                assert!(d8_interval_eq(&xor_result, &bottom));
                continue;
            }

            assert!(d8_interval_eq(&or_result, &top));
            assert!(d8_interval_eq(&and_result, &top));
            assert!(d8_interval_eq(&xor_result, &top));
            for x in left.lo..=left.hi {
                for y in right.lo..=right.hi {
                    assert!(d8_interval_contains(&or_result, x | y));
                    assert!(d8_interval_contains(&and_result, x & y));
                    assert!(d8_interval_contains(&xor_result, x ^ y));
                }
            }
        }
    }
}

#[test]
fn production_interval_division_cases() {
    use DivAlarm::{DefiniteError, MaybeError, NoError};

    let dividend = D8Interval {
        is_bottom: false,
        lo: 10,
        hi: 20,
    };

    let safe = dividend.div(&D8Interval {
        is_bottom: false,
        lo: 2,
        hi: 5,
    });
    assert!(!safe.value.is_bottom);
    assert_eq!(safe.value.lo, 2);
    assert_eq!(safe.value.hi, 10);
    assert!(safe.alarm == NoError);

    let mixed = dividend.div(&D8Interval {
        is_bottom: false,
        lo: 0,
        hi: 5,
    });
    assert!(!mixed.value.is_bottom);
    assert_eq!(mixed.value.lo, 2);
    assert_eq!(mixed.value.hi, 20);
    assert!(mixed.alarm == MaybeError);

    let zero_only = dividend.div(&D8Interval::constant(0));
    assert!(zero_only.value.is_bottom);
    assert!(zero_only.alarm == DefiniteError);

    let unreachable = D8Interval::bottom().div(&D8Interval::constant(0));
    assert!(unreachable.value.is_bottom);
    assert!(unreachable.alarm == NoError);
}

#[test]
fn production_interval_division_small_exhaustive() {
    use DivAlarm::{DefiniteError, MaybeError, NoError};

    let intervals = arithmetic_d8_intervals();
    let bottom = D8Interval::bottom();

    for dividend in &intervals {
        for divisor in &intervals {
            let result = dividend.div(divisor);
            if dividend.is_bottom || divisor.is_bottom {
                assert!(d8_interval_eq(&result.value, &bottom));
                assert!(result.alarm == NoError);
                continue;
            }

            if divisor.hi == 0 {
                assert!(d8_interval_eq(&result.value, &bottom));
                assert!(result.alarm == DefiniteError);
            } else if divisor.lo == 0 {
                assert!(!result.value.is_bottom);
                assert_eq!(result.value.lo, dividend.lo / divisor.hi);
                assert_eq!(result.value.hi, dividend.hi);
                assert!(result.alarm == MaybeError);
            } else {
                assert!(!result.value.is_bottom);
                assert_eq!(result.value.lo, dividend.lo / divisor.hi);
                assert_eq!(result.value.hi, dividend.hi / divisor.lo);
                assert!(result.alarm == NoError);
            }

            for x in dividend.lo..=dividend.hi {
                for y in divisor.lo..=divisor.hi {
                    assert!(result.alarm.has(y == 0));
                    if y != 0 {
                        assert!(d8_interval_contains(&result.value, x / y));
                    }
                }
            }
        }
    }
}

#[test]
fn production_reduced_product_division_cases() {
    use DivAlarm::{DefiniteError, MaybeError, NoError};

    let dividend = d8_reduced_from_interval(D8Interval {
        is_bottom: false,
        lo: 10,
        hi: 20,
    });

    let safe = dividend.div(&d8_reduced_from_interval(D8Interval {
        is_bottom: false,
        lo: 2,
        hi: 5,
    }));
    assert_eq!(safe.value.interval.lo, 2);
    assert_eq!(safe.value.interval.hi, 10);
    assert!(safe.alarm == NoError);

    let mixed = dividend.div(&d8_reduced_from_interval(D8Interval {
        is_bottom: false,
        lo: 0,
        hi: 5,
    }));
    assert_eq!(mixed.value.interval.lo, 2);
    assert_eq!(mixed.value.interval.hi, 20);
    assert!(mixed.alarm == MaybeError);

    let zero_only = dividend.div(&D8ReducedProduct::constant(0));
    assert!(zero_only.value.interval.is_bottom);
    assert!(zero_only.alarm == DefiniteError);

    let unreachable =
        d8_reduced_from_interval(D8Interval::bottom()).div(&D8ReducedProduct::constant(0));
    assert!(unreachable.value.interval.is_bottom);
    assert!(unreachable.alarm == NoError);
}

#[test]
fn production_reduced_product_division_small_exhaustive() {
    let intervals = arithmetic_d8_intervals();

    for dividend_interval in &intervals {
        for divisor_interval in &intervals {
            let dividend = d8_reduced_from_interval(*dividend_interval);
            let divisor = d8_reduced_from_interval(*divisor_interval);
            let result = dividend.div(&divisor);

            if dividend_interval.is_bottom || divisor_interval.is_bottom {
                assert!(result.value.interval.is_bottom);
                assert!(result.alarm == DivAlarm::NoError);
                continue;
            }

            for x in dividend_interval.lo..=dividend_interval.hi {
                for y in divisor_interval.lo..=divisor_interval.hi {
                    assert!(result.alarm.has(y == 0));
                    if y != 0 {
                        assert!(d8_reduced_div_result_contains(&result.value, x / y));
                    }
                }
            }
        }
    }
}

#[test]
fn production_interval_sub_small_exhaustive() {
    let intervals = arithmetic_d8_intervals();
    let bottom = D8Interval::bottom();
    let top = D8Interval::top();

    for left in &intervals {
        for right in &intervals {
            let difference = left.sub(right);
            if left.is_bottom || right.is_bottom {
                assert!(d8_interval_eq(&difference, &bottom));
                continue;
            }

            if left.lo < right.hi {
                assert!(d8_interval_eq(&difference, &top));
            } else {
                assert!(!difference.is_bottom);
                assert_eq!(difference.lo, left.lo.wrapping_sub(right.hi));
                assert_eq!(difference.hi, left.hi.wrapping_sub(right.lo));
            }

            for x in left.lo..=left.hi {
                for y in right.lo..=right.hi {
                    assert!(d8_interval_contains(&difference, x.wrapping_sub(y)));
                }
            }
        }
    }
}

#[test]
fn production_interval_mul_small_exhaustive() {
    let intervals = arithmetic_d8_intervals();
    let bottom = D8Interval::bottom();
    let top = D8Interval::top();

    for left in &intervals {
        for right in &intervals {
            let product = left.mul(right);
            if left.is_bottom || right.is_bottom {
                assert!(d8_interval_eq(&product, &bottom));
                continue;
            }

            match left.hi.checked_mul(right.hi) {
                Some(hi) => {
                    assert!(!product.is_bottom);
                    assert_eq!(product.lo, left.lo * right.lo);
                    assert_eq!(product.hi, hi);
                }
                None => assert!(d8_interval_eq(&product, &top)),
            }

            for x in left.lo..=left.hi {
                for y in right.lo..=right.hi {
                    assert!(d8_interval_contains(&product, x.wrapping_mul(y)));
                }
            }
        }
    }
}

#[test]
fn production_interval_neg_u8_exhaustive() {
    let bottom = D8Interval::bottom().neg();
    assert!(bottom.is_bottom);
    assert_eq!(bottom.lo, 0);
    assert_eq!(bottom.hi, 0);

    let top = D8Interval::top();
    for lo in u8::MIN..=u8::MAX {
        for hi in lo..=u8::MAX {
            let interval = D8Interval {
                is_bottom: false,
                lo,
                hi,
            };
            let negated = interval.neg();
            if lo == 0 {
                if hi == 0 {
                    assert!(!negated.is_bottom);
                    assert_eq!(negated.lo, 0);
                    assert_eq!(negated.hi, 0);
                } else {
                    assert!(d8_interval_eq(&negated, &top));
                }
            } else {
                assert!(!negated.is_bottom);
                assert_eq!(negated.lo, 0u8.wrapping_sub(hi));
                assert_eq!(negated.hi, 0u8.wrapping_sub(lo));
            }

            for value in lo..=hi {
                assert!(d8_interval_contains(&negated, value.wrapping_neg()));
            }
        }
    }
}

#[test]
fn fuzz_eun_plus_zero_identity() {
    let mut rng = test_rng();
    let zero = ExecUnum::constant(0);
    for _ in 0..N {
        let a = rand_eun(&mut rng);
        let r = a.add(&zero);
        for _ in 0..S {
            let x = sample_eun(&a, &mut rng);
            assert!(r.contains(x), "a+0 unsound: a={:?} x={:#x} r={:?}", a, x, r);
        }
    }
}

#[test]
fn fuzz_eun_sub_self_contains_zero() {
    let mut rng = test_rng();
    for _ in 0..N {
        let a = rand_eun(&mut rng);
        let r = a.sub(&a);
        // a - a should always contain 0 (when same concrete value is picked)
        assert!(r.contains(0), "a-a doesn't contain 0: a={:?} r={:?}", a, r);
    }
}

fn main() {
    println!("Run with: cargo test --release");
}
