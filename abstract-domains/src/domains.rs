// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
/// Multi-width abstract domains via macro instantiation.
///
/// The `abstract_domain!` macro stamps out ExecTnum, ExecAnum, ExecUnum,
/// Interval, and ReducedProduct for each unsigned integer width. All
/// `by(bit_vector)` proofs work
/// generically because they only use the type's native operators.
///
/// Usage:
/// ```ignore
/// use crate::domains::d64::{ExecTnum, ExecAnum, ExecUnum, Interval, ReducedProduct};
/// let x = ReducedProduct::constant(42);
/// let y = ReducedProduct::constant(10);
/// let sum = x.add(&y);  // ReducedProduct with Tnum=00110100, Anum=52, Iv=52
/// ```
macro_rules! abstract_domain {
    ($mod_name:ident, $uint:ty, $bits:expr, $max_val:expr) => {
        pub mod $mod_name {
            use vstd::prelude::*;
            use crate::bools::Bit;
            use crate::nats::*;
            use crate::tnum::Tnum;
            use crate::anum::Anum;
            use crate::unum::Unum;
            use crate::chopped::{ChoppedTnum, ChoppedUnum};
            verus! {

            // ============================================================
            // Bridge: native wrapping ops == chop(nat ops, W)
            // ============================================================
            pub proof fn bridge_add(a: $uint, b: $uint)
                ensures (a.wrapping_add(b)) as nat == chop(nat_add(a as nat, b as nat), $bits as nat)
            {
                let w: nat = $bits as nat;
                nat_add_correct(a as nat, b as nat);
                chop_is_mod(nat_add(a as nat, b as nat), w);
                // exp(W) == MAX+1: Verus knows wrapping_add == (a+b) % (MAX+1)
                // and chop(n, W) == n % exp(W), so we need exp(W) == MAX+1
                // exp(W) == MAX+1: call concrete lemma for this width
                exp_concrete($bits as nat);
            }

            pub proof fn bridge_mul(a: $uint, b: $uint)
                ensures (a.wrapping_mul(b)) as nat == chop(prod(a as nat, b as nat), $bits as nat)
            {
                let w: nat = $bits as nat;
                chop_is_mod(prod(a as nat, b as nat), w);
                // exp(W) == MAX+1: call concrete lemma for this width
                exp_concrete($bits as nat);
            }

            /// A native addition that did not wrap is the corresponding
            /// natural-number addition and fits in the native width.
            #[verifier::spinoff_prover]
            pub proof fn add_no_overflow(a: $uint, b: $uint, sum: $uint)
                requires
                    sum == a.wrapping_add(b),
                    sum >= a,
                    sum >= b,
                ensures
                    sum as nat == a as nat + b as nat,
                    nat_add(a as nat, b as nat) == sum as nat,
                    nat_add(a as nat, b as nat) < exp($bits as nat),
                    fits(nat_add(a as nat, b as nat), $bits as nat),
            {
                assert(sum as nat == a as nat + b as nat) by(bit_vector)
                    requires
                        sum == a.wrapping_add(b),
                        sum >= a,
                        sum >= b;
                nat_add_correct(a as nat, b as nat);
                exp_concrete($bits as nat);
                chop_id(nat_add(a as nat, b as nat), $bits as nat);
            }

            pub proof fn native_fits(n: $uint)
                ensures fits(n as nat, $bits as nat)
            {
                exp_concrete($bits as nat);
                chop_id(n as nat, $bits as nat);
            }

            /// Bridge a successful standard-library `checked_mul` result to
            /// the multiplication specification.
            pub proof fn mul_exact(a: $uint, b: $uint, product: $uint)
                requires
                    product as nat == (a as nat) * (b as nat),
                ensures
                    product as nat == (a as nat) * (b as nat),
                    prod(a as nat, b as nat) == product as nat,
                    prod(a as nat, b as nat) < exp($bits as nat),
                    fits(prod(a as nat, b as nat), $bits as nat),
            {
                native_fits(product);
                assert(prod(a as nat, b as nat) == product as nat);
                exp_concrete($bits as nat);
                assert((product as nat) <= ($max_val as nat));
                assert(($max_val as nat) < exp($bits as nat));
            }

            // ============================================================
            // Bridge: native bitwise ops == spec bitwise ops on nat
            // ============================================================

            /// For n < exp(W), bits at position >= W are false.
            pub proof fn bit_above_width(n: nat, w: nat, i: nat)
                requires n < exp(w), i >= w
                ensures !bit(n, i).b()
                decreases i
            {
                exp_pos(w);
                if w == 0 { bit_zero(i); }
                else if i > 0 { bit_above_width(tl(n), (w-1) as nat, (i-1) as nat); }
            }

            /// Per-bit bridge: spec bit(n, i) == native bit extraction.
            pub proof fn bit_is_native_bit(n: $uint, i: nat)
                requires i < ($bits as nat)
                ensures bit(n as nat, i).b() == ((n >> (i as $uint)) & (1 as $uint) == (1 as $uint))
                decreases i
            {
                if i == 0 {
                    assert(((n >> (0 as $uint)) & (1 as $uint)) == (n % 2)) by(bit_vector);
                } else {
                    let iu = i as $uint;
                    assert((n >> (1 as $uint)) as nat == n as nat / 2) by(bit_vector);
                    bit_is_native_bit(n >> (1 as $uint), (i - 1) as nat);
                    assert(((n >> iu) & (1 as $uint)) == (((n >> (1 as $uint)) >> ((iu - (1 as $uint)) as $uint)) & (1 as $uint))) by(bit_vector)
                        requires iu < ($bits as $uint), iu > (0 as $uint);
                }
            }

            /// Native XOR == spec bw_xor on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_xor(a: $uint, b: $uint)
                ensures (a ^ b) as nat == bw_xor(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a ^ b) as nat, i) == bit(bw_xor(a as nat, b as nat), i) by {
                    xor_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a ^ b, i);
                        let iu = i as $uint;
                        assert(((a ^ b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) != (((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a ^ b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a ^ b) as nat, bw_xor(a as nat, b as nat));
            }

            /// Native OR == spec bw_or on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_or(a: $uint, b: $uint)
                ensures (a | b) as nat == bw_or(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a | b) as nat, i) == bit(bw_or(a as nat, b as nat), i) by {
                    or_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a | b, i);
                        let iu = i as $uint;
                        assert(((a | b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) || (((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a | b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a | b) as nat, bw_or(a as nat, b as nat));
            }

            /// Native AND == spec bw_and on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_and(a: $uint, b: $uint)
                ensures (a & b) as nat == bw_and(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a & b) as nat, i) == bit(bw_and(a as nat, b as nat), i) by {
                    and_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a & b, i);
                        let iu = i as $uint;
                        assert(((a & b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) && (((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a & b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a & b) as nat, bw_and(a as nat, b as nat));
            }

            /// Native AND-NOT == spec bw_and_not on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_and_not(a: $uint, b: $uint)
                ensures (a & !b) as nat == bw_and_not(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a & !b) as nat, i) == bit(bw_and_not(a as nat, b as nat), i) by {
                    and_not_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a & !b, i);
                        let iu = i as $uint;
                        assert(((a & !b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) && !(((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a & !b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a & !b) as nat, bw_and_not(a as nat, b as nat));
            }

            /// Native fixed-width left shift is infinite-bitstring left shift,
            /// truncated back to the native width.
            #[verifier::spinoff_prover]
            pub proof fn native_lsh(a: $uint)
                ensures (a << (1 as $uint)) as nat == chop(lsh(a as nat), $bits as nat)
            {
                assert forall|i: nat| #![auto]
                    bit((a << (1 as $uint)) as nat, i)
                        == bit(chop(lsh(a as nat), $bits as nat), i) by {
                    chop_bit(lsh(a as nat), $bits as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a << (1 as $uint), i);
                        bit_cons(a as nat, Bit::f(), i);
                        let iu = i as $uint;
                        if i == 0 {
                            assert((((a << (1 as $uint)) >> iu) & (1 as $uint))
                                == (0 as $uint)) by(bit_vector)
                                requires iu == (0 as $uint);
                        } else {
                            bit_is_native_bit(a, (i - 1) as nat);
                            assert((((a << (1 as $uint)) >> iu) & (1 as $uint))
                                == ((a >> ((iu - (1 as $uint)) as $uint)) & (1 as $uint)))
                                by(bit_vector)
                                requires iu < ($bits as $uint), iu > (0 as $uint);
                        }
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a << (1 as $uint)) as nat, $bits as nat, i);
                    }
                };
                eq_from_bits(
                    (a << (1 as $uint)) as nat,
                    chop(lsh(a as nat), $bits as nat),
                );
            }

            // ============================================================
            // ExecTnum: Executable Tnum
            // ============================================================
            #[derive(Clone, Copy)]
            pub struct ExecTnum { pub val: $uint, pub mask: $uint }

            impl ExecTnum {
                pub open spec fn wf(self) -> bool { self.val & self.mask == 0 }
                pub open spec fn to_tn(self) -> Tnum { Tnum { val: self.val as nat, mask: self.mask as nat } }
                pub open spec fn has(self, x: $uint) -> bool { self.to_tn().has(x as nat) }
                proof fn wf_inv(self) requires self.wf() ensures self.to_tn().inv()
                {
                    native_and(self.val, self.mask);
                }
                proof fn to_chopped(self) requires self.wf()
                    ensures (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).inv()
                {
                    self.wf_inv();
                    exp_concrete($bits as nat);
                    chop_id(self.val as nat, $bits as nat);
                    chop_id(self.mask as nat, $bits as nat);
                }
                #[inline] pub fn constant(n: $uint) -> (r: ExecTnum) ensures r.wf() {
                    proof { assert(n & (0 as $uint) == (0 as $uint)) by(bit_vector); }
                    ExecTnum { val: n, mask: 0 }
                }
                #[inline] pub fn top() -> (r: ExecTnum) ensures r.wf() {
                    proof { assert((0 as $uint) & (!(0 as $uint)) == (0 as $uint)) by(bit_vector); }
                    ExecTnum { val: 0, mask: !(0 as $uint) }
                }
                pub proof fn top_has(c: $uint)
                    ensures (ExecTnum { val: 0, mask: !(0 as $uint) }).has(c)
                {
                    let tn = Tnum { val: 0, mask: (!(0 as $uint)) as nat };
                    native_and_not(c, !(0 as $uint));
                    assert((c & !(!(0 as $uint))) == (0 as $uint)) by(bit_vector);
                    tn.has_equiv(c as nat);
                }
                #[inline] pub fn bw_or(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1 | c2)
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let v = sv | tv; let m = (sm | tm) & !v;
                    let r = ExecTnum { val: v, mask: m };
                    proof {
                        assert(sv & sm == (0 as $uint) && tv & tm == (0 as $uint) ==> ((sv|tv) & ((sm|tm) & !(sv|tv)) == (0 as $uint))) by(bit_vector);
                        native_or(sv, tv);
                        native_or(sm, tm);
                        native_and_not(sm | tm, v);
                        self.wf_inv(); t.wf_inv();
                        self.to_tn().or_sound(t.to_tn());
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1 | c2) by {
                            native_or(c1, c2);
                        };
                    }
                    r
                }
                #[inline] pub fn bw_and(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1 & c2)
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let r = ExecTnum { val: sv & tv, mask: sm | tm };
                    proof {
                        assert(sv & sm == (0 as $uint) && tv & tm == (0 as $uint) ==> ((sv&tv) & (sm|tm) == (0 as $uint))) by(bit_vector);
                        native_and(sv, tv);
                        native_or(sm, tm);
                        self.wf_inv(); t.wf_inv();
                        self.to_tn().and_sound(t.to_tn());
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1 & c2) by {
                            native_and(c1, c2);
                        };
                    }
                    r
                }
                #[inline] pub fn bw_xor(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1 ^ c2)
                {
                    let v = self.val ^ t.val; let m = self.mask | t.mask;
                    let r = ExecTnum { val: v & !m, mask: m };
                    proof {
                        assert(((v & !m) & m) == (0 as $uint)) by(bit_vector);
                        native_xor(self.val, t.val);
                        native_or(self.mask, t.mask);
                        native_and_not(v, m);
                        self.wf_inv(); t.wf_inv();
                        self.to_tn().xor_sound(t.to_tn());
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1 ^ c2) by {
                            native_xor(c1, c2);
                        };
                    }
                    r
                }
                #[inline] pub fn bw_not(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
                    proof { assert((!(0 as $uint)) & (0 as $uint) == (0 as $uint)) by(bit_vector); }
                    self.bw_xor(&ExecTnum { val: !(0 as $uint), mask: 0 })
                }
                #[inline] pub fn bw_and_not(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
                    self.bw_and(&t.bw_not())
                }
                #[inline] pub fn add(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let lbv = self.val.wrapping_add(t.val);
                    let lbm = self.mask.wrapping_add(t.mask);
                    let ub = lbv.wrapping_add(lbm);
                    let mask = (ub ^ lbv) | self.mask | t.mask;
                    let r = ExecTnum { val: lbv & !mask, mask };
                    proof {
                        assert(((lbv & !mask) & mask) == (0 as $uint)) by(bit_vector);
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.add_sound(ct_t);
                        // Bridge: wrapping == chop(nat_add, W)
                        bridge_add(self.val, t.val);
                        bridge_add(self.mask, t.mask);
                        bridge_add(lbv, lbm);
                        // Bridge: native bitwise == spec bitwise
                        native_xor(ub, lbv);
                        native_or(ub ^ lbv, self.mask);
                        native_or((ub ^ lbv) | self.mask, t.mask);
                        native_and_not(lbv, mask);
                        // L2 spec intermediates
                        let sv_n = self.val as nat; let sm_n = self.mask as nat;
                        let tv_n = t.val as nat; let tm_n = t.mask as nat;
                        let lbv_s = nat_add(sv_n, tv_n);
                        let lbm_s = nat_add(sm_n, tm_n);
                        let ub_s = nat_add(lbv_s, lbm_s);
                        // chop distributes over each bitwise step (no closures!)
                        chop_bw_xor(ub_s, lbv_s, w);
                        chop_bw_or(bw_xor(ub_s, lbv_s), sm_n, w);
                        chop_bw_or(bw_or(bw_xor(ub_s, lbv_s), sm_n), tm_n, w);
                        chop_bw_and_not(lbv_s, bw_or(bw_or(bw_xor(ub_s, lbv_s), sm_n), tm_n), w);
                        exp_concrete(w);
                        chop_id(sm_n, w); chop_id(tm_n, w);
                        // r.to_tn() == ct_s.add(ct_t).tnum
                        // Spell out the chain for Z3:
                        // lbv as nat == chop(lbv_s, w), lbm as nat == chop(lbm_s, w)
                        chop_nat_add(sv_n, tv_n, w);
                        chop_nat_add(sm_n, tm_n, w);
                        chop_id(sv_n, w); chop_id(tv_n, w);
                        assert(lbv as nat == chop(lbv_s, w));
                        assert(lbm as nat == chop(lbm_s, w));
                        // ub as nat == chop(ub_s, w)
                        chop_nat_add(lbv_s, lbm_s, w);
                        assert(ub as nat == chop(ub_s, w));
                        // chop(xor_s, w) == (ub ^ lbv) as nat
                        assert(chop(bw_xor(ub_s, lbv_s), w) == bw_xor(ub as nat, lbv as nat));
                        // chop(or1_s, w) == ((ub^lbv)|sm) as nat
                        assert(chop(bw_or(bw_xor(ub_s, lbv_s), sm_n), w) == bw_or(bw_xor(ub as nat, lbv as nat), sm_n));
                        // chop(mask_s, w) == mask as nat
                        let mask_s = bw_or(bw_or(bw_xor(ub_s, lbv_s), sm_n), tm_n);
                        assert(chop(mask_s, w) == mask as nat);
                        // chop(val_s, w) == (lbv & !mask) as nat
                        assert(chop(bw_and_not(lbv_s, mask_s), w) == (lbv & !mask) as nat);
                        assert(r.to_tn() == ct_s.add(ct_t).tnum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_add(c2)) by {
                            bridge_add(c1, c2);
                            chop_id(c1 as nat, w);
                            chop_id(c2 as nat, w);
                        };
                    }
                    r
                }
                #[inline] pub fn neg(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
                    self.bw_not().add(&ExecTnum::constant(1))
                }
                #[inline] pub fn sub(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
                    self.add(&t.neg())
                }
                #[inline] pub fn rsh(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
                    let v = self.val; let m = self.mask;
                    proof { assert(v & m == (0 as $uint) ==> (v >> (1 as $uint)) & (m >> (1 as $uint)) == (0 as $uint)) by(bit_vector); }
                    ExecTnum { val: v >> 1, mask: m >> 1 }
                }
                #[inline] pub fn lsh(&self) -> (r: ExecTnum) requires self.wf() ensures r.wf() {
                    let v = self.val; let m = self.mask;
                    proof { assert(v & m == (0 as $uint) ==> (v << (1 as $uint)) & (m << (1 as $uint)) == (0 as $uint)) by(bit_vector); }
                    ExecTnum { val: v << 1, mask: m << 1 }
                }
                #[inline] pub fn join(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c), forall|c: $uint| #![auto] t.has(c) ==> r.has(c)
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let v = sv & tv;
                    let u = (sv ^ sm) | (tv ^ tm);
                    let m = v ^ u;
                    let r = ExecTnum { val: v & !m, mask: m };
                    proof {
                        assert(sv & sm == (0 as $uint) && tv & tm == (0 as $uint) ==> ((v & !m) & m == (0 as $uint))) by(bit_vector);
                        native_and(sv, tv);
                        native_xor(sv, sm); native_xor(tv, tm);
                        native_or(sv ^ sm, tv ^ tm);
                        native_xor(v, u);
                        native_and_not(v, m);
                        self.wf_inv(); t.wf_inv();
                        self.to_tn().join_sound(t.to_tn());
                        // r.to_tn() and spec join have same mask; vals agree mod mask
                        // so has_bw is identical: bw_and_not(x, m) == (v&!m) <==> bw_and_not(x, m) == v
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c) by {
                            self.to_tn().join_sound(t.to_tn());
                            self.to_tn().join(t.to_tn()).has_equiv(c as nat);
                            r.to_tn().has_equiv(c as nat);
                            assert((c & !m) == v ==> (c & !m) == (v & !m))
                                by(bit_vector);
                            native_and_not(c, m);
                        };
                        assert forall|c: $uint| #![auto] t.has(c) implies r.has(c) by {
                            self.to_tn().join_sound(t.to_tn());
                            self.to_tn().join(t.to_tn()).has_equiv(c as nat);
                            r.to_tn().has_equiv(c as nat);
                            assert((c & !m) == v ==> (c & !m) == (v & !m))
                                by(bit_vector);
                            native_and_not(c, m);
                        };
                    }
                    r
                }
                pub fn meet(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) && t.has(c) ==> r.has(c)
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let v = sv | tv;
                    let u = (sv ^ sm) & (tv ^ tm);
                    let m = v ^ u;
                    let r = ExecTnum { val: v & !m, mask: m };
                    proof {
                        assert(((v & !m) & m) == (0 as $uint)) by(bit_vector);
                        native_or(sv, tv);
                        native_xor(sv, sm); native_xor(tv, tm);
                        native_and(sv ^ sm, tv ^ tm);
                        native_xor(v, u);
                        native_and_not(v, m);
                        self.wf_inv(); t.wf_inv();
                        self.to_tn().meet_sound(t.to_tn());
                        assert forall|c: $uint| #![auto] self.has(c) && t.has(c) implies r.has(c) by {
                            self.to_tn().meet_sound(t.to_tn());
                            self.to_tn().meet(t.to_tn()).has_equiv(c as nat);
                            r.to_tn().has_equiv(c as nat);
                            assert((c & !m) == v ==> (c & !m) == (v & !m))
                                by(bit_vector);
                            native_and_not(c, m);
                        };
                    }
                    r
                }
                pub fn mul_bit(&self, bv: bool, bm: bool) -> (r: ExecTnum)
                    requires self.wf(), !(bv && bm) ensures r.wf()
                {
                    if bv { *self }
                    else if bm {
                        proof { assert((0 as $uint) & (self.val | self.mask) == (0 as $uint)) by(bit_vector); }
                        ExecTnum { val: 0, mask: self.val | self.mask }
                    }
                    else { ExecTnum::constant(0) }
                }
                pub fn mul(&self, t: &ExecTnum) -> (r: ExecTnum) requires self.wf(), t.wf() ensures r.wf() {
                    let mut acc = ExecTnum::constant(0);
                    let mut md = *self;
                    let mut mr = t.val;
                    let mut mm = t.mask;
                    let mut i: u32 = 0;
                    while i < $bits
                        invariant acc.wf(), md.wf(), i <= $bits, mr & mm == (0 as $uint)
                        decreases $bits - i
                    {
                        if (mr & 1) == 1 { acc = acc.add(&md); }
                        else if (mm & 1) == 1 { acc = acc.add(&md.mul_bit(false, true)); }
                        md = md.lsh();
                        proof { assert(mr & mm == (0 as $uint) ==> (mr >> (1 as $uint)) & (mm >> (1 as $uint)) == (0 as $uint)) by(bit_vector); }
                        mr >>= 1; mm >>= 1;
                        i += 1;
                    }
                    acc
                }
                #[inline] pub fn min_val(&self) -> (r: $uint) ensures r == self.val { self.val }
                #[inline] pub fn max_val(&self) -> (r: $uint) ensures r == (self.val | self.mask) { self.val | self.mask }
                proof fn has_bounds(&self, c: $uint)
                    requires self.wf(), self.has(c)
                    ensures c >= self.val, c <= (self.val | self.mask)
                {
                    self.wf_inv();
                    self.to_tn().has_equiv(c as nat);
                    native_and_not(c, self.mask);
                    let v = self.val; let m = self.mask;
                    assert(c >= v && c <= (v | m)) by(bit_vector)
                        requires (c & !m) == v, v & m == (0 as $uint);
                }
                #[inline] pub fn is_const(&self) -> bool { self.mask == 0 }
                /// If has(c) and c <= possible, then narrowed tnum (mask & possible, val & possible) also has c.
                proof fn has_narrow(&self, c: $uint, possible: $uint)
                    requires self.wf(), self.has(c), c <= possible,
                        possible & (possible.wrapping_add(1)) == 0, // possible = 2^k - 1
                    ensures (ExecTnum { val: self.val & possible, mask: self.mask & possible }).has(c)
                {
                    self.wf_inv();
                    self.to_tn().has_equiv(c as nat);
                    native_and_not(c, self.mask);
                    let v = self.val; let m = self.mask; let p = possible;
                    // c <= p and p = 2^k-1 means bits above k are 0 in c
                    // (c & !m) == v, so bits above k in v are also 0 (since c has them 0 and mask doesn't cover them... wait)
                    // Actually: (c & !m) == v means where mask=0, c==v. If c<=p, bits above p are 0 in c.
                    // For bits above p: mask could be 0 there, meaning v must be 0 there (since c is 0 there).
                    // So (v & !p) == 0 when c <= p and (c & !m) == v.
                    // Then (c & !(m & p)) == (c & (!m | !p)) == (c & !m) | (c & !p) == v | 0 == v
                    // And v == v & p (since v has no bits above p).
                    // So (c & !(m & p)) == v & p. QED.
                    assert((c & !(m & p)) == (v & p)) by(bit_vector)
                        requires (c & !m) == v, v & m == (0 as $uint), c <= p, p & p.wrapping_add(1) == (0 as $uint);
                    let tn2 = Tnum { val: (v & p) as nat, mask: (m & p) as nat };
                    native_and_not(c, m & p);
                    tn2.has_equiv(c as nat);
                }
            }

            // ============================================================
            // EAn: Executable Anum
            // ============================================================
            #[derive(Clone, Copy)]
            pub struct ExecAnum { pub base: $uint, pub span: $uint }
            impl ExecAnum {
                pub open spec fn to_an(self) -> Anum { Anum { base: self.base as nat, span: self.span as nat } }
                pub open spec fn has(self, x: $uint) -> bool { self.to_an().has(x as nat) }
                /// has in terms of $uint ops (for by(bit_vector) proofs)
                proof fn has_eq_uint(self, x: $uint)
                    ensures self.has(x) <==> (x >= self.base && ((x - self.base) as $uint) & !self.span == (0 as $uint))
                {
                    let w: nat = $bits as nat;
                    exp_concrete(w);
                    if x >= self.base {
                        self.to_an().mask_tnum().has_equiv(nat_sub(x as nat, self.base as nat));
                        native_and_not((x - self.base) as $uint, self.span);
                    }
                }
                pub proof fn top_has(n: $uint)
                    ensures (ExecAnum { base: 0, span: !(0 as $uint) }).has(n)
                {
                    let w: nat = $bits as nat;
                    let max_nat = !(0 as $uint) as nat;
                    exp_concrete(w);
                    // Prove bw_and_not(n, max_nat) == 0 per-bit
                    assert forall|i: nat| #![auto] bit(bw_and_not(n as nat, max_nat), i) == bit(0nat, i) by {
                        and_not_bit(n as nat, max_nat, i);
                        bit_zero(i);
                        if i < w {
                            let iu: $uint = i as $uint;
                            bit_is_native_bit(!(0 as $uint), i);
                            assert(((!(0 as $uint)) >> iu) & (1 as $uint) == (1 as $uint)) by(bit_vector)
                                requires iu < ($bits as $uint);
                        } else {
                            bit_above_width(n as nat, w, i);
                        }
                    };
                    eq_from_bits(bw_and_not(n as nat, max_nat), 0);
                    Tnum::ctor(0, max_nat).has_equiv(n as nat);
                }
                #[inline] pub fn constant(n: $uint) -> ExecAnum { ExecAnum { base: n, span: 0 } }
                #[inline] pub fn top() -> ExecAnum { ExecAnum { base: 0, span: !(0 as $uint) } }
                // No `rlimit` here, deliberately. This carried `rlimit(2000)` while
                // the soundness fact below was one 11-variable bit-vector query;
                // splitting it into the four single-purpose queries brought the
                // whole function under the *default* limit at every width, so the
                // annotation became a stale ceiling rather than a live requirement.
                // Measured at d64: 0.7s, and it still verifies with `--rlimit 1`.
                // Keeping it would have hidden a future regression -- an annotated
                // limit only reports the budget it was given, never the headroom.
                #[inline] pub fn add(&self, t: &ExecAnum) -> (r: ExecAnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let b1 = self.base; let s1 = self.span;
                    let b2 = t.base; let s2 = t.span;
                    let v = b1.wrapping_add(b2);
                    let sm = s1.wrapping_add(s2) | s1 | s2;
                    // Overflow check: if max1 + max2 overflows, or base sum overflows, return top
                    let max1 = b1.wrapping_add(s1);
                    let max2 = b2.wrapping_add(s2);
                    let max_sum = max1.wrapping_add(max2);
                    if max1 < b1 || max2 < b2 || max_sum < max1 || max_sum < max2 || v < b1 || sm < s1 {
                        let r = ExecAnum { base: 0, span: !(0 as $uint) };
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_add(c2)) by {
                                ExecAnum::top_has(c1.wrapping_add(c2));
                            };
                        }
                        return r;
                    }
                    let r = ExecAnum { base: v, span: sm };
                    proof {
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_add(c2)) by {
                            self.has_eq_uint(c1);
                            t.has_eq_uint(c2);
                            r.has_eq_uint(c1.wrapping_add(c2));
                            // The soundness fact is decomposed into four
                            // single-purpose bit-vector queries. As one query
                            // (11 variables, 13 hypotheses, conjunction goal)
                            // it diverges on the z3 4.16 bundled with Verus
                            // 0.2026.08.02 — z3 4.12 proved it in ~20s — and a
                            // by(bit_vector) assert sends the solver exactly
                            // the requires written on it, so the split is also
                            // what keeps every query's hypothesis set minimal.
                            let dd1 = (c1 - b1) as $uint;
                            let dd2 = (c2 - b2) as $uint;
                            // (1) Interval lower bound, mask-free: on the
                            // guarded no-overflow path, c1+c2 does not wrap
                            // and lands at or above v.
                            assert(
                                max_sum >= max1 && max1 >= b1 && max2 >= b2 && v >= b1 &&
                                c1 >= b1 && c1 <= max1 && c2 >= b2 && c2 <= max2
                                ==> c1.wrapping_add(c2) >= v
                            ) by(bit_vector)
                                requires v == b1.wrapping_add(b2),
                                         max_sum == max1.wrapping_add(max2);
                            // (2) Offset identity, a ring fact over Z/2^N:
                            // (c1+c2) - (b1+b2) == (c1-b1) + (c2-b2).
                            assert(
                                ((c1.wrapping_add(c2) - v) as $uint) == ((dd1 + dd2) as $uint)
                            ) by(bit_vector)
                                requires v == b1.wrapping_add(b2),
                                         dd1 == (c1 - b1) as $uint,
                                         dd2 == (c2 - b2) as $uint;
                            // (3) The span sum does not wrap: each span fits
                            // under its max, and the max sum fits.
                            assert(
                                max_sum >= max1 && max_sum >= max2 && max1 >= b1 && max2 >= b2
                                ==> s1.wrapping_add(s2) >= s1
                            ) by(bit_vector)
                                requires max1 == b1.wrapping_add(s1),
                                         max2 == b2.wrapping_add(s2),
                                         max_sum == max1.wrapping_add(max2);
                            // (4) The stride-closure core — the one hard fact,
                            // over exactly four unconstrained variables: bits
                            // of dd1 lie in s1 and bits of dd2 in s2, so bits
                            // of dd1+dd2 lie in (s1+s2)|s1|s2.
                            assert(
                                dd1 & !s1 == (0 as $uint) && dd2 & !s2 == (0 as $uint) &&
                                s1.wrapping_add(s2) >= s1
                                ==>
                                ((dd1 + dd2) as $uint) & !(s1.wrapping_add(s2) | s1 | s2) == (0 as $uint)
                            ) by(bit_vector);
                            // c1 <= max1: from has, c1 = b1 + d1 where d1 <= s1
                            assert(c1 >= b1 && (((c1 - b1) as $uint) & !s1 == (0 as $uint)) && max1 >= b1
                                ==> c1 <= max1) by(bit_vector)
                                requires max1 == b1.wrapping_add(s1);
                            assert(c2 >= b2 && (((c2 - b2) as $uint) & !s2 == (0 as $uint)) && max2 >= b2
                                ==> c2 <= max2) by(bit_vector)
                                requires max2 == b2.wrapping_add(s2);
                        };
                    }
                    r
                }
                #[inline] pub fn sub(&self, t: &ExecAnum) -> ExecAnum {
                    // The one ExecAnum method here with no soundness ensures: the
                    // guards below are the hand-checked analogue of add's, until
                    // sub gets its own has-postcondition. Without them the result
                    // window can be disjoint from the true difference set.
                    let max2 = t.base.wrapping_add(t.span);
                    let v = self.base.wrapping_sub(max2);
                    let m = self.span.wrapping_add(t.span) | self.span | t.span;
                    if max2 < t.base || v > self.base || m < self.span {
                        return ExecAnum { base: 0, span: !(0 as $uint) };
                    }
                    ExecAnum { base: v, span: m }
                }
                pub fn div_const(&self, d: $uint) -> (r: ExecAnum)
                    requires d > 0
                    ensures forall|c: $uint| #![auto] self.has(c) ==> r.has(c / d)
                {
                    let min_q = self.base / d;
                    let max_v = self.base.wrapping_add(self.span);
                    let max_q = max_v / d;
                    if max_q < min_q || max_v < self.base {
                        let r = ExecAnum { base: 0, span: !(0 as $uint) };
                        proof {
                            assert forall|c: $uint| #![auto] self.has(c) implies r.has(c / d) by {
                                ExecAnum::top_has(c / d);
                            };
                        }
                        return r;
                    }
                    let range = max_q - min_q;
                    let mask = Self::ones_mask(range);
                    let r = ExecAnum { base: min_q, span: mask };
                    proof {
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c / d) by {
                            self.has_eq_uint(c);
                            r.has_eq_uint(c / d);
                            // c >= base, (c-base) & !span == 0 ==> c <= base + span
                            // ==> base/d <= c/d <= max_q
                            // ==> (c/d - min_q) <= range <= mask
                            // ==> (c/d - min_q) & !mask == 0
                            let b = self.base; let s = self.span;
                            assert(c >= b && (((c - b) as $uint) & !s == (0 as $uint))
                                && max_v >= b
                                ==> c <= max_v) by(bit_vector)
                                requires max_v == b.wrapping_add(s);
                            vstd::arithmetic::div_mod::lemma_div_is_ordered(self.base as int, c as int, d as int);
                            vstd::arithmetic::div_mod::lemma_div_is_ordered(c as int, max_v as int, d as int);
                            // c/d - min_q <= range <= mask
                            let q = c / d;
                            assert(q >= min_q && q <= max_q);
                            let off: $uint = (q - min_q) as $uint;
                            assert(off <= range) by { assert(q <= max_q); }
                            // off <= mask (since range <= mask) and mask = 2^k-1
                            // ==> off & !mask == 0
                            assert(off <= mask && mask & mask.wrapping_add(1) == (0 as $uint)
                                ==> off & !mask == (0 as $uint))
                                by(bit_vector);
                        };
                    }
                    r
                }
                pub fn ones_mask(n: $uint) -> (r: $uint) ensures r >= n, r & r.wrapping_add(1) == 0 {
                    if n == 0 { proof { assert((0 as $uint) & (0 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector); } return 0; }
                    let _max: $uint = !(0 as $uint);
                    // Build 2^k - 1 by repeated doubling + 1
                    let mut mask: $uint = 1;
                    proof { assert((1 as $uint) & (1 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector); }
                    // At most BITS iterations since mask doubles each time
                    let mut i: u32 = 0;
                    while mask < n && i < $bits
                        invariant i <= $bits, mask & mask.wrapping_add(1) == 0
                        decreases ($bits - i)
                    {
                        proof { assert(mask & mask.wrapping_add(1) == (0 as $uint) ==>
                            (mask.wrapping_add(mask).wrapping_add(1)) & (mask.wrapping_add(mask).wrapping_add(1)).wrapping_add(1) == (0 as $uint))
                            by(bit_vector); }
                        mask = mask.wrapping_add(mask).wrapping_add(1);
                        i += 1;
                    }
                    if mask >= n { mask } else {
                        proof {
                            assert(!(0 as $uint) >= n) by(bit_vector);
                            assert(!(0 as $uint) & (!(0 as $uint)).wrapping_add(1) == (0 as $uint)) by(bit_vector);
                        }
                        !(0 as $uint)
                    }
                }
                pub fn to_etn(&self) -> (r: ExecTnum) ensures r.wf() {
                    let sv = self.base; let sm = self.span;
                    proof { assert(((sv & !sm) & sm) == (0 as $uint)) by(bit_vector); }
                    ExecTnum { val: sv & !sm, mask: sm }
                }
                #[inline] pub fn from_etn(t: &ExecTnum) -> ExecAnum requires t.wf() { ExecAnum { base: t.val, span: t.mask } }
                #[inline] pub fn min_val(&self) -> (r: $uint) ensures r == self.base { self.base }
                #[inline] pub fn max_val(&self) -> (r: $uint) ensures r == self.base.wrapping_add(self.span) { self.base.wrapping_add(self.span) }
                proof fn has_bounds(&self, c: $uint)
                    requires self.has(c)
                    ensures c >= self.base
                {
                    self.has_eq_uint(c);
                }
                /// Upper bound only valid when base + span doesn't wrap
                proof fn has_upper_bound(&self, c: $uint)
                    requires self.has(c), self.base.wrapping_add(self.span) >= self.base
                    ensures c <= self.base.wrapping_add(self.span)
                {
                    self.has_eq_uint(c);
                    let b = self.base; let s = self.span;
                    assert(c <= b.wrapping_add(s)) by(bit_vector)
                        requires c >= b, ((c - b) as $uint) & !s == (0 as $uint), b.wrapping_add(s) >= b;
                }
                proof fn has_narrow(&self, c: $uint, possible: $uint)
                    requires self.has(c), c <= possible,
                        possible & (possible.wrapping_add(1)) == 0,
                    ensures (ExecAnum { base: self.base, span: self.span & possible }).has(c)
                {
                    self.has_eq_uint(c);
                    let b = self.base; let s = self.span; let p = possible;
                    let d = (c - b) as $uint;
                    // d & !s == 0, c <= p, c >= b
                    // Need: d & !(s & p) == 0
                    // d & !(s & p) == d & (!s | !p) == (d & !s) | (d & !p) == 0 | (d & !p)
                    // d = c - b <= p - 0 = p (since c <= p and b >= 0), so d <= p
                    // d <= p and p = 2^k-1 means bits above k are 0 in d, so d & !p == 0
                    assert(((c - b) as $uint) & !(s & p) == (0 as $uint)) by(bit_vector)
                        requires c >= b, ((c - b) as $uint) & !s == (0 as $uint), c <= p, p & p.wrapping_add(1) == (0 as $uint);
                    let an2 = ExecAnum { base: b, span: s & p };
                    an2.has_eq_uint(c);
                }
            }

            // ============================================================
            // EUn: Executable Unum — horizontally composable Anum
            // ============================================================
            //
            // A Unum represents a set {v + d | d in D} where D is described
            // by bitfields in (w, x). Register w marks bitfield boundaries:
            //   - A 1-bit in w starts a new bitfield (the "leader").
            //   - A 0-bit in w continues the previous bitfield (a "follower").
            // Register x stores the maximum value for each bitfield.
            //
            // The set D is the set of all sums of per-bitfield values,
            // where each bitfield's value ranges from 0 to its max.
            //
            // The unbounded operation has the precise carry-boundary formula. The
            // executable operation below proves soundness at fixed width and widens
            // to top whenever a represented bound or result range would wrap.
            #[derive(Clone, Copy)]
            pub struct ExecUnum { pub base: $uint, pub walls: $uint, pub extent: $uint }

            impl ExecUnum {
                pub open spec fn to_un(self) -> Unum { Unum { base: self.base as nat, walls: self.walls as nat, extent: self.extent as nat } }
                pub open spec fn has(self, n: $uint) -> bool { self.to_un().has(n as nat) }

                proof fn to_chopped(self)
                    ensures (ChoppedUnum { unum: self.to_un(), w: $bits as nat }).inv()
                {
                    exp_concrete($bits as nat);
                    chop_id(self.base as nat, $bits as nat);
                    chop_id(self.walls as nat, $bits as nat);
                    chop_id(self.extent as nat, $bits as nat);
                }

                /// top contains everything.
                pub proof fn top_has(n: $uint)
                    ensures (ExecUnum { base: 0, walls: 0, extent: !(0 as $uint) }).has(n)
                {
                    assert(!(0 as $uint) >= n) by(bit_vector);
                    Unum::offset_from_bound((!(0 as $uint)) as nat, n as nat);
                }

                #[inline] pub fn constant(n: $uint) -> ExecUnum {
                    ExecUnum { base: n, walls: !(0 as $uint), extent: 0 }
                }
                #[inline] pub fn top() -> (r: ExecUnum)
                    ensures forall|n: $uint| #![auto] r.has(n)
                {
                    let r = ExecUnum { base: 0, walls: 0, extent: !(0 as $uint) };
                    proof {
                        assert forall|n: $uint| #![auto] r.has(n) by {
                            ExecUnum::top_has(n);
                        };
                    }
                    r
                }

                /// Sound fixed-width addition. Uses the precise field formula when
                /// represented bounds do not wrap; otherwise widens to top.
                /// cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))
                /// w = (w1 & w2) & ~(cout << 1)
                #[verifier::rlimit(30)]
                #[verifier::spinoff_prover]
                #[inline] pub fn add(&self, t: &ExecUnum) -> (r: ExecUnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let b1 = self.base; let sx = self.extent;
                    let b2 = t.base;    let tx = t.extent;
                    let v = b1.wrapping_add(b2);
                    let x12 = sx.wrapping_add(tx);
                    let max1 = b1.wrapping_add(sx);
                    let max2 = b2.wrapping_add(tx);
                    let max_sum = max1.wrapping_add(max2);
                    if v < b1 || v < b2
                        || x12 < sx || x12 < tx
                        || max1 < b1 || max2 < b2
                        || max_sum < max1 || max_sum < max2
                    {
                        let r = ExecUnum::top();
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto]
                                self.has(c1) && t.has(c2)
                                implies r.has(c1.wrapping_add(c2)) by {
                                ExecUnum::top_has(c1.wrapping_add(c2));
                            };
                        }
                        return r;
                    }
                    let cout = (sx & tx) | ((sx | tx) & !x12);
                    let carry_in = cout << 1;
                    let sw = self.walls; let tw = t.walls;
                    let w = (sw & tw) & !carry_in;
                    let r = ExecUnum { base: v, walls: w, extent: x12 };
                    proof {
                        let width = $bits as nat;
                        let left = ChoppedUnum { unum: self.to_un(), w: width };
                        let right = ChoppedUnum { unum: t.to_un(), w: width };
                        self.to_chopped();
                        t.to_chopped();

                        add_no_overflow(b1, b2, v);
                        add_no_overflow(sx, tx, x12);

                        native_and(sx, tx);
                        native_or(sx, tx);
                        native_and_not(sx | tx, x12);
                        native_or(sx & tx, (sx | tx) & !x12);
                        Unum::carry_out_formula(sx as nat, tx as nat);
                        assert(cout as nat == Unum::carry_out(sx as nat, tx as nat));

                        native_lsh(cout);
                        native_and(sw, tw);
                        native_and_not(sw & tw, carry_in);
                        chop_bw_and_not(
                            bw_and(sw as nat, tw as nat),
                            lsh(Unum::carry_out(sx as nat, tx as nat)),
                            width,
                        );
                        native_fits(sw & tw);
                        assert(w as nat
                            == chop(
                                bw_and_not(
                                    bw_and(sw as nat, tw as nat),
                                    lsh(Unum::carry_out(sx as nat, tx as nat)),
                                ),
                                width,
                            ));
                        assert(r.to_un() == self.to_un().add(t.to_un()).truncate(width));

                        assert forall|c1: $uint, c2: $uint| #![auto]
                            self.has(c1) && t.has(c2)
                            implies r.has(c1.wrapping_add(c2)) by {
                            self.has_upper_bound(c1);
                            t.has_upper_bound(c2);
                            assert(c1.wrapping_add(c2) >= c1
                                && c1.wrapping_add(c2) >= c2) by(bit_vector)
                                requires c1 <= max1, c2 <= max2,
                                    max_sum == max1.wrapping_add(max2),
                                    max_sum >= max1, max_sum >= max2;
                            add_no_overflow(c1, c2, c1.wrapping_add(c2));
                            native_fits(c1);
                            native_fits(c2);
                            assert(left.has(c1 as nat));
                            assert(right.has(c2 as nat));
                            self.to_un().add_bounded_sound(
                                t.to_un(),
                                c1 as nat,
                                c2 as nat,
                                width,
                            );
                            assert(r.has(c1.wrapping_add(c2)));
                        };
                    }
                    r
                }

                /// Convert to EAn: widen each field's max to ones_mask.
                /// Unum fields are contiguous ranges `[0, max]`; Anum needs
                /// per-bit independence, so we round max up to 2^k - 1.
                pub fn to_ean(&self) -> ExecAnum {
                    // Sound overapproximation: ones_mask(x) >= x for the whole register.
                    // This treats the entire x as one field, which is always sound
                    // (it may be less precise than per-field widening for multi-field Unums,
                    // but it avoids trailing_zeros which Verus doesn't support).
                    ExecAnum { base: self.base, span: ExecAnum::ones_mask(self.extent) }
                }

                /// Convert to ETn: Anum->Tnum via Tnum addition Tn(v,0)+Tn(0,m).
                pub fn to_etn(&self) -> (r: ExecTnum) ensures r.wf() {
                    let an = self.to_ean();
                    let lbv = an.base; let lbm = an.span;
                    let ub = lbv.wrapping_add(lbm);
                    let mask = (ub ^ lbv) | an.span;
                    proof { assert(((lbv & !mask) & mask) == (0 as $uint)) by(bit_vector); }
                    ExecTnum { val: lbv & !mask, mask }
                }

                /// Build from an EAn: each uncertain bit becomes its own 1-wide bitfield.
                #[inline] pub fn from_ean(a: &ExecAnum) -> ExecUnum {
                    // Each bit of a.span is an independent bitfield of width 1.
                    // w = all 1s (every bit is a leader), x = a.span
                    ExecUnum { base: a.base, walls: !(0 as $uint), extent: a.span }
                }

                /// Build from an Interval: single bitfield covering the range.
                pub fn from_interval(iv: &Interval) -> (r: ExecUnum)
                    requires iv.wf()
                    ensures forall|c: $uint| #![auto] iv.has(c) ==> r.has(c)
                {
                    let range = iv.hi - iv.lo;
                    let r = ExecUnum { base: iv.lo, walls: 0, extent: range };
                    proof {
                        assert forall|c: $uint| #![auto] iv.has(c) implies r.has(c) by {
                            assert(c >= iv.lo && c <= iv.hi);
                            assert((c - iv.lo) as nat <= range as nat);
                            Unum::offset_from_bound(range as nat, (c - iv.lo) as nat);
                            assert(nat_sub(c as nat, iv.lo as nat) == (c - iv.lo) as nat);
                        };
                    }
                    r
                }

                /// Negation: negate v, keep uncertainty structure.
                /// -(v + d) = -v - d. The set of d values is {0..max per bitfield}.
                /// We need -d which ranges from -max to 0.
                /// So result.base = -v - total_max, result uncertainty = same structure.
                #[inline] pub fn neg(&self) -> ExecUnum {
                    if self.base.wrapping_add(self.extent) < self.base {
                        return ExecUnum::top();
                    }
                    let new_v = (0 as $uint).wrapping_sub(self.base).wrapping_sub(self.extent);
                    ExecUnum { base: new_v, walls: self.walls, extent: self.extent }
                }

                #[inline] pub fn sub(&self, t: &ExecUnum) -> ExecUnum {
                    self.add(&t.neg())
                }

                /// Multiplication: bilinear expansion.
                /// (v1+d1)*(v2+d2) = v1*v2 + v1*d2 + v2*d1 + d1*d2
                /// Uncertainty bounded by v1*x2 + v2*x1 + x1*x2.
                pub fn mul(&self, t: &ExecUnum) -> (r: ExecUnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_mul(c2))
                {
                    let v1 = self.base; let x1 = self.extent;
                    let v2 = t.base;   let x2 = t.extent;
                    let max1 = v1.wrapping_add(x1);
                    let max2 = v2.wrapping_add(x2);
                    if max1 < v1 || max1 < x1 || max2 < v2 || max2 < x2 {
                        return ExecUnum::top();
                    }
                    let max_product = match max1.checked_mul(max2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let base = match v1.checked_mul(v2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let v1x2 = match v1.checked_mul(x2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let v2x1 = match v2.checked_mul(x1) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let x1x2 = match x1.checked_mul(x2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let unc1 = v1x2.wrapping_add(v2x1);
                    if unc1 < v1x2 || unc1 < v2x1 { return ExecUnum::top(); }
                    let unc = unc1.wrapping_add(x1x2);
                    if unc < unc1 || unc < x1x2 { return ExecUnum::top(); }
                    let upper = base.wrapping_add(unc);
                    if upper < base || upper < unc { return ExecUnum::top(); }
                    let r = ExecUnum { base, walls: 0, extent: unc };
                    proof {
                        let width = $bits as nat;
                        mul_exact(max1, max2, max_product);
                        mul_exact(v1, v2, base);
                        mul_exact(v1, x2, v1x2);
                        mul_exact(v2, x1, v2x1);
                        mul_exact(x1, x2, x1x2);
                        add_no_overflow(v1x2, v2x1, unc1);
                        add_no_overflow(unc1, x1x2, unc);
                        add_no_overflow(base, unc, upper);
                        assert(upper == max_product) by(nonlinear_arith)
                            requires
                                max1 as nat == v1 as nat + x1 as nat,
                                max2 as nat == v2 as nat + x2 as nat,
                                max_product as nat == (max1 as nat) * (max2 as nat),
                                base as nat == (v1 as nat) * (v2 as nat),
                                v1x2 as nat == (v1 as nat) * (x2 as nat),
                                v2x1 as nat == (v2 as nat) * (x1 as nat),
                                x1x2 as nat == (x1 as nat) * (x2 as nat),
                                unc1 as nat == v1x2 as nat + v2x1 as nat,
                                unc as nat == unc1 as nat + x1x2 as nat,
                                upper as nat == base as nat + unc as nat;
                        native_fits(base);
                        native_fits(unc);
                        assert(chop(base as nat, width) == base as nat);
                        assert(chop(unc as nat, width) == unc as nat);
                        chop_id(0, width);
                        assert(self.to_un().mul(t.to_un()).base == base as nat);
                        assert(self.to_un().mul(t.to_un()).walls == 0);
                        assert(self.to_un().mul(t.to_un()).extent == unc as nat);
                        assert(r.to_un() == self.to_un().mul(t.to_un()).truncate(width));

                        assert forall|c1: $uint, c2: $uint| #![auto]
                            self.has(c1) && t.has(c2)
                            implies r.has(c1.wrapping_mul(c2)) by {
                            self.has_upper_bound(c1);
                            t.has_upper_bound(c2);
                            let concrete = c1.wrapping_mul(c2);
                            vstd::arithmetic::mul::lemma_mul_upper_bound(
                                c1 as int,
                                max1 as int,
                                c2 as int,
                                max2 as int,
                            );
                            assert(prod(c1 as nat, c2 as nat) <= max_product as nat);
                            assert((max_product as nat) < exp(width));
                            chop_id(prod(c1 as nat, c2 as nat), width);
                            bridge_mul(c1, c2);
                            assert(concrete as nat == prod(c1 as nat, c2 as nat));
                            native_fits(v1);
                            native_fits(x1);
                            native_fits(v2);
                            native_fits(x2);
                            self.to_un().mul_bounded_sound(
                                t.to_un(),
                                c1 as nat,
                                c2 as nat,
                                width,
                            );
                            assert(r.has(concrete));
                        };
                    }
                    r
                }

                #[inline] pub fn min_val(&self) -> (r: $uint) ensures r == self.base { self.base }
                #[inline] pub fn max_val(&self) -> (r: $uint) ensures r == self.base.wrapping_add(self.extent) { self.base.wrapping_add(self.extent) }
                proof fn has_bounds(&self, c: $uint)
                    requires self.has(c)
                    ensures c >= self.base
                {
                }
                /// Upper bound only valid when base + extent doesn't wrap.
                proof fn has_upper_bound(&self, c: $uint)
                    requires self.has(c), self.base.wrapping_add(self.extent) >= self.base
                    ensures c <= self.base.wrapping_add(self.extent)
                {
                    Unum::offset_bounded(self.walls as nat, self.extent as nat, nat_sub(c as nat, self.base as nat));
                }
                #[inline] pub fn is_const(&self) -> bool { self.extent == 0 }
            }

            // ============================================================
            // Interval
            // ============================================================
            #[derive(Clone, Copy)]
            pub struct Interval { pub lo: $uint, pub hi: $uint }
            impl Interval {
                pub open spec fn wf(self) -> bool { self.lo <= self.hi }
                pub open spec fn has(self, x: $uint) -> bool { self.lo <= x && x <= self.hi }
                #[inline] pub fn constant(n: $uint) -> (r: Interval) ensures r.wf() { Interval { lo: n, hi: n } }
                #[inline] pub fn top() -> (r: Interval) ensures r.wf() { Interval { lo: 0, hi: !(0 as $uint) } }
                /// top contains everything.
                pub proof fn top_has(x: $uint)
                    ensures (Interval { lo: 0, hi: !(0 as $uint) }).has(x)
                {
                    assert(!(0 as $uint) >= x) by(bit_vector);
                }
                #[inline] pub fn add(&self, t: &Interval) -> (r: Interval)
                    ensures r.wf(),
                        forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let slo = self.lo; let shi = self.hi; let tlo = t.lo; let thi = t.hi;
                    let lo = slo.wrapping_add(tlo);
                    let hi = shi.wrapping_add(thi);
                    if lo < slo || hi < shi || hi < lo {
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies (Interval { lo: 0, hi: !(0 as $uint) }).has(c1.wrapping_add(c2)) by {
                                Self::top_has(c1.wrapping_add(c2));
                            };
                        }
                        Interval { lo: 0, hi: !(0 as $uint) }
                    } else {
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies (Interval { lo, hi }).has(c1.wrapping_add(c2)) by {
                                // In non-overflow branch: lo >= slo, hi >= shi, hi >= lo
                                // c1 <= shi, c2 <= thi, shi+thi = hi doesn't wrap
                                // So c1+c2 <= shi+thi doesn't wrap either
                                assert(c1.wrapping_add(c2) >= c1 && c1.wrapping_add(c2) >= c2) by(bit_vector)
                                    requires c1 <= shi, c2 <= thi, hi == shi.wrapping_add(thi), hi >= shi;
                                // lower bound
                                assert(slo.wrapping_add(tlo) <= c1.wrapping_add(c2)) by(bit_vector)
                                    requires slo <= c1, tlo <= c2, c1.wrapping_add(c2) >= c1, lo == slo.wrapping_add(tlo), lo >= slo;
                                // upper bound
                                assert(c1.wrapping_add(c2) <= shi.wrapping_add(thi)) by(bit_vector)
                                    requires c1 <= shi, c2 <= thi, c1.wrapping_add(c2) >= c2, hi == shi.wrapping_add(thi), hi >= shi;
                            };
                        }
                        Interval { lo, hi }
                    }
                }
                #[inline] pub fn meet(&self, t: &Interval) -> (r: Interval)
                    ensures r.wf(),
                        forall|x: $uint| #![auto] self.has(x) && t.has(x) ==> r.has(x)
                {
                    let lo = if self.lo > t.lo { self.lo } else { t.lo };
                    let hi = if self.hi < t.hi { self.hi } else { t.hi };
                    if hi < lo {
                        proof {
                            assert forall|x: $uint| #![auto] self.has(x) && t.has(x) implies (Interval { lo: 0, hi: !(0 as $uint) }).has(x) by {
                                Self::top_has(x);
                            };
                        }
                        Interval::top()
                    } else { Interval { lo, hi } }
                }
                #[inline] pub fn join(&self, t: &Interval) -> (r: Interval)
                    requires self.wf(), t.wf()
                    ensures r.wf(),
                        forall|x: $uint| #![auto] self.has(x) ==> r.has(x),
                        forall|x: $uint| #![auto] t.has(x) ==> r.has(x)
                {
                    Interval {
                        lo: if self.lo < t.lo { self.lo } else { t.lo },
                        hi: if self.hi > t.hi { self.hi } else { t.hi },
                    }
                }
                #[inline] pub fn div_const(&self, d: $uint) -> (r: Interval)
                    requires self.wf(), d > 0
                    ensures r.wf(),
                        forall|x: $uint| #![auto] self.has(x) ==> r.has(x / d)
                {
                    proof {
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(self.lo as int, self.hi as int, d as int);
                        assert forall|x: $uint| #![auto] self.has(x) implies Interval { lo: self.lo / d, hi: self.hi / d }.has(x / d) by {
                            vstd::arithmetic::div_mod::lemma_div_is_ordered(self.lo as int, x as int, d as int);
                            vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, self.hi as int, d as int);
                        };
                    }
                    Interval { lo: self.lo / d, hi: self.hi / d }
                }
            }

            // ============================================================
            // ReducedProduct: Tnum x Anum x Interval x Unum reduced product
            // ============================================================
            #[derive(Clone, Copy)]
            pub struct ReducedProduct { pub tnum: ExecTnum, pub anum: ExecAnum, pub interval: Interval, pub unum: ExecUnum }
            impl ReducedProduct {
                pub open spec fn wf(self) -> bool { self.tnum.wf() && self.interval.wf() }
                pub open spec fn has(self, x: $uint) -> bool {
                    self.tnum.has(x) && self.anum.has(x) && self.interval.has(x) && self.unum.has(x)
                }
                pub open spec fn top_spec() -> ReducedProduct {
                    ReducedProduct { tnum: ExecTnum { val: 0, mask: !(0 as $uint) },
                        anum: ExecAnum { base: 0, span: !(0 as $uint) },
                        interval: Interval { lo: 0, hi: !(0 as $uint) },
                        unum: ExecUnum { base: 0, walls: 0, extent: !(0 as $uint) } }
                }
                #[inline] pub fn constant(n: $uint) -> (r: ReducedProduct) ensures r.wf() {
                    ReducedProduct { tnum: ExecTnum::constant(n), anum: ExecAnum::constant(n), interval: Interval::constant(n), unum: ExecUnum::constant(n) }
                }
                #[inline] pub fn top() -> (r: ReducedProduct) ensures r.wf() {
                    proof {
                        assert((0 as $uint) & (!(0 as $uint)) == (0 as $uint)) by(bit_vector);
                        assert(!(0 as $uint) >= (0 as $uint)) by(bit_vector);
                    }
                    ReducedProduct { tnum: ExecTnum { val: 0, mask: !(0 as $uint) },
                        anum: ExecAnum { base: 0, span: !(0 as $uint) },
                        interval: Interval { lo: 0, hi: !(0 as $uint) },
                        unum: ExecUnum { base: 0, walls: 0, extent: !(0 as $uint) } }
                }
                proof fn top_has(c: $uint)
                    ensures Self::top_spec().has(c)
                {
                    ExecTnum::top_has(c);
                    ExecAnum::top_has(c);
                    Interval::top_has(c);
                    ExecUnum::top_has(c);
                }
                #[inline] fn top_ret() -> (r: ReducedProduct)
                    ensures r.wf(), r == Self::top_spec()
                {
                    proof {
                        assert((0 as $uint) & (!(0 as $uint)) == (0 as $uint)) by(bit_vector);
                        assert(!(0 as $uint) >= (0 as $uint)) by(bit_vector);
                    }
                    ReducedProduct { tnum: ExecTnum { val: 0, mask: !(0 as $uint) },
                        anum: ExecAnum { base: 0, span: !(0 as $uint) },
                        interval: Interval { lo: 0, hi: !(0 as $uint) },
                        unum: ExecUnum { base: 0, walls: 0, extent: !(0 as $uint) } }
                }
                pub fn reduce(&self) -> (r: ReducedProduct)
                    requires self.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c)
                {
                    // Step 1: Tighten interval from Tnum, Anum, and Unum bounds
                    let tmin = self.tnum.min_val(); let tmax = self.tnum.max_val();
                    let amin = self.anum.min_val(); let amax = self.anum.max_val();
                    let umin = self.unum.min_val(); let umax = self.unum.max_val();
                    let ilo = self.interval.lo; let ihi = self.interval.hi;
                    let lo = {
                        let a = if tmin > ilo { tmin } else { ilo };
                        let b = if amin > a { amin } else { a };
                        if umin > b { umin } else { b }
                    };
                    let hi = {
                        let a = if tmax < ihi { tmax } else { ihi };
                        let b = if amax < a { amax } else { a };
                        if umax < b { umax } else { b }
                    };
                    proof {
                        assert(hi <= tmax && hi <= amax && hi <= umax && hi <= ihi);
                        assert(lo >= tmin && lo >= amin && lo >= umin && lo >= ilo);
                    }
                    if hi < lo {
                        proof {
                            assert forall|c: $uint| #![auto] self.has(c) implies Self::top_spec().has(c) by {
                                ReducedProduct::top_has(c);
                            };
                        }
                        return Self::top_ret();
                    }

                    // Step 2: Tighten Tnum from interval — clear uncertain bits above hi
                    let possible = Self::ones_above(hi);
                    let new_tn_m = self.tnum.mask & possible;
                    let new_tn_v = self.tnum.val & possible;
                    let old_tn_v = self.tnum.val;
                    let old_tn_m = self.tnum.mask;
                    proof {
                        assert((old_tn_v & possible) & (old_tn_m & possible) == (0 as $uint)) by(bit_vector)
                            requires old_tn_v & old_tn_m == (0 as $uint);
                    }
                    let tn = ExecTnum { val: new_tn_v, mask: new_tn_m };

                    // Step 3: Tighten Anum from interval
                    let new_an_m = self.anum.span & possible;
                    let an = ExecAnum { base: self.anum.base, span: new_an_m };

                    // Step 4: Re-tighten interval from new Tnum bounds
                    let lo2 = if tn.min_val() > lo { tn.min_val() } else { lo };
                    let hi2 = if tn.max_val() < hi { tn.max_val() } else { hi };
                    if hi2 < lo2 {
                        proof {
                            assert forall|c: $uint| #![auto] self.has(c) implies Self::top_spec().has(c) by {
                                ReducedProduct::top_has(c);
                            };
                        }
                        Self::top_ret()
                    }
                    else {
                        let un = ExecUnum::from_interval(&Interval { lo: lo2, hi: hi2 });
                        let r = ReducedProduct { tnum: tn, anum: an, interval: Interval { lo: lo2, hi: hi2 }, unum: un };
                        proof {
                            assert(hi >= lo);
                            assert(hi <= amax);
                            assert(lo >= amin);
                            assert(amax >= self.anum.base);
                            assert forall|c: $uint| #![auto] self.has(c) implies r.has(c) by {
                                self.tnum.has_bounds(c);
                                self.anum.has_bounds(c);
                                self.anum.has_upper_bound(c);
                                self.unum.has_bounds(c);
                                self.unum.has_upper_bound(c);
                                assert(c <= hi);
                                assert(c >= lo);
                                assert(c <= possible);
                                self.tnum.has_narrow(c, possible);
                                self.anum.has_narrow(c, possible);
                                tn.has_bounds(c);
                            };
                        }
                        r
                    }
                }

                /// Smallest (2^k - 1) >= n.
                fn ones_above(n: $uint) -> (r: $uint)
                    ensures r >= n, r & r.wrapping_add(1) == (0 as $uint)
                {
                    if n == 0 { proof { assert((0 as $uint) & (0 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector); } return 0; }
                    let mut mask: $uint = 1;
                    let mut k: u32 = 1;
                    proof { assert((1 as $uint) & (1 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector); }
                    while mask < n && k < $bits
                        invariant k <= $bits, mask & mask.wrapping_add(1) == (0 as $uint)
                        decreases ($bits - k)
                    {
                        let old_mask = mask;
                        mask = mask.wrapping_add(mask).wrapping_add(1);
                        proof {
                            assert(mask & mask.wrapping_add(1) == (0 as $uint)) by(bit_vector)
                                requires old_mask & old_mask.wrapping_add(1) == (0 as $uint),
                                    mask == old_mask.wrapping_add(old_mask).wrapping_add(1);
                        }
                        k += 1;
                    }
                    if mask >= n { mask } else {
                        proof {
                            assert(!(0 as $uint) >= n) by(bit_vector);
                            assert((!(0 as $uint)) & (!(0 as $uint)).wrapping_add(1) == (0 as $uint)) by(bit_vector);
                        }
                        !(0 as $uint)
                    }
                }
                #[inline] pub fn bw_or(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.bw_or(&t.tnum), anum: ExecAnum::top(), interval: Interval::top(), unum: ExecUnum::top() }.reduce()
                }
                #[inline] pub fn bw_and(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.bw_and(&t.tnum), anum: ExecAnum::top(), interval: Interval::top(), unum: ExecUnum::top() }.reduce()
                }
                #[inline] pub fn bw_xor(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.bw_xor(&t.tnum), anum: ExecAnum::top(), interval: Interval::top(), unum: ExecUnum::top() }.reduce()
                }
                #[inline] pub fn add(&self, t: &ReducedProduct) -> (r: ReducedProduct)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let tn = self.tnum.add(&t.tnum);
                    let an = self.anum.add(&t.anum);
                    let iv = self.interval.add(&t.interval);
                    let un = self.unum.add(&t.unum);
                    let combined = ReducedProduct { tnum: tn, anum: an, interval: iv, unum: un };
                    let r = combined.reduce();
                    proof {
                        assert forall|c1: $uint, c2: $uint| #![auto]
                            self.has(c1) && t.has(c2) implies r.has(c1.wrapping_add(c2)) by {
                            let s = c1.wrapping_add(c2);
                            assert(tn.has(s));
                            assert(an.has(s));
                            assert(iv.has(s));
                            assert(un.has(s));
                        };
                    }
                    r
                }
                #[inline] pub fn sub(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.sub(&t.tnum), anum: self.anum.sub(&t.anum), interval: Interval::top(), unum: self.unum.sub(&t.unum) }.reduce()
                }
                pub fn mul(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.mul(&t.tnum), anum: ExecAnum::top(), interval: Interval::top(), unum: self.unum.mul(&t.unum) }.reduce()
                }
                pub fn div_const(&self, d: $uint) -> (r: ReducedProduct) requires self.wf(), d > 0 ensures r.wf() {
                    ReducedProduct { tnum: ExecTnum::top(), anum: self.anum.div_const(d), interval: self.interval.div_const(d), unum: ExecUnum::top() }.reduce()
                }
                #[inline] pub fn rsh(&self) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.rsh(), anum: ExecAnum::top(), interval: Interval::top(), unum: ExecUnum::top() }.reduce()
                }
                #[inline] pub fn lsh(&self) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.lsh(), anum: ExecAnum::top(), interval: Interval::top(), unum: ExecUnum::top() }.reduce()
                }
                pub fn join(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.join(&t.tnum), anum: ExecAnum::top(), interval: self.interval.join(&t.interval), unum: ExecUnum::top() }.reduce()
                }
                pub fn meet(&self, t: &ReducedProduct) -> (r: ReducedProduct) requires self.wf(), t.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.meet(&t.tnum), anum: ExecAnum::top(), interval: self.interval.meet(&t.interval), unum: ExecUnum::top() }.reduce()
                }
                #[inline] pub fn neg(&self) -> (r: ReducedProduct) requires self.wf() ensures r.wf() {
                    ReducedProduct { tnum: self.tnum.neg(), anum: ExecAnum::top(), interval: Interval::top(), unum: self.unum.neg() }.reduce()
                }
                #[inline] pub fn is_const(&self) -> bool { self.tnum.is_const() && self.interval.lo == self.interval.hi }
                #[inline] pub fn min_val(&self) -> $uint {
                    let a = self.tnum.min_val(); let b = self.interval.lo;
                    let c = self.anum.min_val(); let d = self.unum.min_val();
                    let m = if a > b { a } else { b };
                    let m = if c > m { c } else { m };
                    if d > m { d } else { m }
                }
                #[inline] pub fn max_val(&self) -> $uint {
                    let a = self.tnum.max_val(); let b = self.interval.hi;
                    let c = self.anum.max_val(); let d = self.unum.max_val();
                    let m = if a < b { a } else { b };
                    let m = if c < m { c } else { m };
                    if d < m { d } else { m }
                }
            }

            } // verus!
        }
    };
}

abstract_domain!(d8, u8, 8u32, 0xFFu8);
abstract_domain!(d16, u16, 16u32, 0xFFFFu16);
abstract_domain!(d32, u32, 32u32, 0xFFFF_FFFFu32);
abstract_domain!(d64, u64, 64u32, 0xFFFF_FFFF_FFFF_FFFFu64);
// d128 disabled: u128 bitvector proofs exceed Z3 capacity
// abstract_domain!(d128, u128, 128u32, 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFFu128);
