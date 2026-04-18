// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(dead_code)]
/// Fuzz testing for abstract domain soundness.
/// Pure Rust — no Verus. Reimplements the domain ops for testing.
use rand::Rng;
use rand::RngExt;

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
        x.wrapping_sub(self.base) & !self.span == 0
    }
    fn add(&self, t: &ExecAnum) -> ExecAnum {
        ExecAnum {
            base: self.base.wrapping_add(t.base),
            span: self.span.wrapping_add(t.span) | self.span | t.span,
        }
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
        self.lo <= self.hi
    }
    fn contains(&self, x: u64) -> bool {
        self.lo <= x && x <= self.hi
    }
    fn add(&self, t: &Interval) -> Interval {
        let lo = self.lo.wrapping_add(t.lo);
        let hi = self.hi.wrapping_add(t.hi);
        if lo < self.lo || hi < self.hi || hi < lo {
            Interval { lo: 0, hi: !0 }
        } else {
            Interval { lo, hi }
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
        Interval { lo: a, hi: b }
    } else {
        Interval { lo: b, hi: a }
    }
}
fn sample_etn(tn: &ExecTnum, rng: &mut impl Rng) -> u64 {
    tn.val | (rng.random::<u64>() & tn.mask)
}
fn sample_ean(an: &ExecAnum, rng: &mut impl Rng) -> u64 {
    an.base.wrapping_add(rng.random::<u64>() & an.span)
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
            let mut rng = rand::rng();
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
            let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
            walls: 1,
            extent: !0,
        }
    }

    fn add(&self, t: &ExecUnum) -> ExecUnum {
        let v = self.base.wrapping_add(t.base);
        let x12 = self.extent.wrapping_add(t.extent);
        if x12 < self.extent || x12 < t.extent {
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
        let (base, base_of) = v1.overflowing_mul(v2);
        let (v1x2, of1) = v1.overflowing_mul(x2);
        let (v2x1, of2) = v2.overflowing_mul(x1);
        let (x1x2, of3) = x1.overflowing_mul(x2);
        if base_of || of1 || of2 || of3 {
            return ExecUnum::top();
        }
        let (unc1, of4) = v1x2.overflowing_add(v2x1);
        let (unc, of5) = unc1.overflowing_add(x1x2);
        if of4 || of5 {
            return ExecUnum::top();
        }
        ExecUnum {
            base,
            walls: 1,
            extent: unc,
        }
    }

    fn to_ean(self) -> ExecAnum {
        // Widen each field's max to ones_mask (smallest 2^k-1 >= max)
        let mut m: u64 = 0;
        for_each_field(self.walls, |start, end| {
            let fm = field_mask(start, end);
            let x_field = (self.extent & fm) >> start;
            let mut mask = if x_field == 0 { 0u64 } else { 1u64 };
            while mask < x_field {
                mask = mask.wrapping_mul(2).wrapping_add(1);
                if mask == !0 {
                    break;
                }
            }
            m |= mask << start;
        });
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
            walls: 1,
            extent: hi - lo,
        }
    }

    fn contains(&self, y: u64) -> bool {
        let d = y.wrapping_sub(self.base);
        let mut ok = true;
        for_each_field(self.walls, |start, end| {
            let m = field_mask(start, end);
            let d_field = (d & m) >> start;
            let x_field = (self.extent & m) >> start;
            if d_field > x_field {
                ok = false;
            }
        });
        ok
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
    un.base.wrapping_add(d)
}

// ----------------------------------------------------------------
// Representation tests
// ----------------------------------------------------------------

#[test]
fn fuzz_eun_self_contains() {
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
    let t = ExecUnum::top();
    for _ in 0..N {
        let x: u64 = rng.random();
        assert!(t.contains(x), "top doesn't contain {:#x}", x);
    }
}

#[test]
fn fuzz_eun_min_max() {
    let mut rng = rand::rng();
    for _ in 0..N {
        let un = rand_eun(&mut rng);
        assert!(un.contains(un.min_val()), "doesn't contain min: {:?}", un);
        assert!(un.contains(un.max_val()), "doesn't contain max: {:?}", un);
    }
}

// ----------------------------------------------------------------
// Conversion tests
// ----------------------------------------------------------------

#[test]
fn fuzz_eun_to_ean_sound() {
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
fn fuzz_eun_plus_zero_identity() {
    let mut rng = rand::rng();
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
    let mut rng = rand::rng();
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
