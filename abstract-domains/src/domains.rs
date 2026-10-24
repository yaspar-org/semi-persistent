// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
/// Multi-width abstract domains via macro instantiation.
///
/// The `abstract_domain!` macro stamps out ExecTnum, ExecAnum, ExecUnum and
/// Interval for each unsigned integer width. All `by(bit_vector)` proofs work
/// generically because they only use the type's native operators. These
/// domains are combined through `reduce::Product`, not a product of their own.
macro_rules! abstract_domain {
    ($mod_name:ident, $uint:ty, $bits:expr, $max_val:expr) => {
        pub mod $mod_name {
            use vstd::prelude::*;
            use crate::bools::Bit;
            use crate::nats::*;
            use crate::tnum::Tnum;
            use crate::anum::Anum;
            use crate::unum::Unum;
            use crate::chopped::{ChoppedAnum, ChoppedTnum, ChoppedUnum};
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

            /// The executable join's value equals the spec join's value: for
            /// well-formed operands `sv & tv` has no bit in the join mask.
            pub proof fn native_join_val(sv: $uint, sm: $uint, tv: $uint, tm: $uint)
                requires sv & sm == (0 as $uint), tv & tm == (0 as $uint)
                ensures ((sv & tv) & !((sv & tv) ^ ((sv ^ sm) | (tv ^ tm)))) == sv & tv
            {
                assert(((sv & tv) & !((sv & tv) ^ ((sv ^ sm) | (tv ^ tm)))) == sv & tv) by(bit_vector)
                    requires sv & sm == (0 as $uint), tv & tm == (0 as $uint);
            }

            /// A value that is some word with the mask bits cleared has no bit in
            /// the mask: normalizing it again changes nothing.
            pub proof fn native_and_not_idem(c: $uint, m: $uint, v: $uint)
                requires (c & !m) == v
                ensures (v & !m) == v
            {
                assert((v & !m) == v) by(bit_vector)
                    requires (c & !m) == v;
            }

            /// XOR with all ones is bitwise NOT.
            pub proof fn native_xor_ones(c: $uint)
                ensures c ^ !(0 as $uint) == !c
            {
                assert(c ^ !(0 as $uint) == !c) by(bit_vector);
            }

            /// Native wrapping negation == chop(2^W - c, W).
            pub proof fn native_neg(c: $uint)
                ensures ((0 as $uint).wrapping_sub(c)) as nat == chop((exp($bits as nat) - c as nat) as nat, $bits as nat)
            {
                let w: nat = $bits as nat;
                exp_concrete(w);
                if c == 0 {
                    nat_add_correct(0, exp(w));
                    chop_nat_add_pow2(0, w);
                    chop_id(0, w);
                } else {
                    chop_id((exp(w) - c as nat) as nat, w);
                }
            }

            /// Native wrapping subtraction == chop(a + (2^W - b), W).
            pub proof fn native_sub(a: $uint, b: $uint)
                ensures (a.wrapping_sub(b)) as nat == chop(nat_add(a as nat, (exp($bits as nat) - b as nat) as nat), $bits as nat)
            {
                let w: nat = $bits as nat;
                exp_concrete(w);
                nat_add_correct(a as nat, (exp(w) - b as nat) as nat);
                if a >= b {
                    let d = (a - b) as nat;
                    nat_add_correct(d, exp(w));
                    chop_nat_add_pow2(d, w);
                    chop_id(d, w);
                } else {
                    chop_id(nat_add(a as nat, (exp(w) - b as nat) as nat), w);
                }
            }

            /// The native low bit is the spec head bit.
            pub proof fn native_low_bit(x: $uint)
                ensures ((x & (1 as $uint)) == (1 as $uint)) == hd(x as nat).b()
            {
                bit_is_native_bit(x, 0);
                assert(x >> (0 as $uint) == x) by(bit_vector);
            }

            /// Native right shift by one == spec rsh on nat.
            pub proof fn native_rsh(a: $uint)
                ensures (a >> (1 as $uint)) as nat == rsh(a as nat)
            {
                assert((a >> (1 as $uint)) as nat == a as nat / 2) by(bit_vector);
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

            /// Native right shift by k == spec rshi on nat.
            pub proof fn native_rshi(a: $uint, k: nat)
                requires k < ($bits as nat)
                ensures (a >> (k as $uint)) as nat == rshi(a as nat, k)
                decreases k
            {
                if k == 0 {
                    assert(a >> (0 as $uint) == a) by(bit_vector);
                } else {
                    let ku = k as $uint;
                    native_rsh(a);
                    native_rshi(a >> (1 as $uint), (k - 1) as nat);
                    assert(a >> ku == (a >> (1 as $uint)) >> ((ku - (1 as $uint)) as $uint)) by(bit_vector)
                        requires ku < ($bits as $uint), ku > (0 as $uint);
                }
            }

            /// Native left shift by k == spec lshi on nat, truncated to the width.
            pub proof fn native_lshi(a: $uint, k: nat)
                requires k < ($bits as nat)
                ensures (a << (k as $uint)) as nat == chop(lshi(a as nat, k), $bits as nat)
                decreases k
            {
                let w: nat = $bits as nat;
                if k == 0 {
                    assert(a << (0 as $uint) == a) by(bit_vector);
                    native_fits(a);
                } else {
                    let ku = k as $uint;
                    let b = a << ((ku - (1 as $uint)) as $uint);
                    native_lshi(a, (k - 1) as nat);
                    native_lsh(b);
                    chop_lsh(lshi(a as nat, (k - 1) as nat), w);
                    assert(a << ku == b << (1 as $uint)) by(bit_vector)
                        requires ku < ($bits as $uint), ku > (0 as $uint), b == a << ((ku - (1 as $uint)) as $uint);
                }
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
                #[inline] pub fn constant(n: $uint) -> (r: ExecTnum) ensures r.wf(), r.has(n) {
                    proof {
                        assert(n & (0 as $uint) == (0 as $uint)) by(bit_vector);
                        assert(n & !(0 as $uint) == n) by(bit_vector);
                        native_and_not(n, 0);
                        Tnum { val: n as nat, mask: 0 }.has_equiv(n as nat);
                    }
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
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1 | c2),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).bw_or(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let v = sv | tv; let m = (sm | tm) & !v;
                    let r = ExecTnum { val: v, mask: m };
                    proof {
                        assert(sv & sm == (0 as $uint) && tv & tm == (0 as $uint) ==> ((sv|tv) & ((sm|tm) & !(sv|tv)) == (0 as $uint))) by(bit_vector);
                        native_or(sv, tv);
                        native_or(sm, tm);
                        native_and_not(sm | tm, v);
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.or_sound(ct_t);
                        assert(r.to_tn() == ct_s.bw_or(ct_t).tnum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1 | c2) by {
                            native_fits(c1); native_fits(c2);
                            native_or(c1, c2);
                            assert(ct_s.has(c1 as nat) && ct_t.has(c2 as nat));
                        };
                    }
                    r
                }
                #[inline] pub fn bw_and(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1 & c2),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).bw_and(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let r = ExecTnum { val: sv & tv, mask: sm | tm };
                    proof {
                        assert(sv & sm == (0 as $uint) && tv & tm == (0 as $uint) ==> ((sv&tv) & (sm|tm) == (0 as $uint))) by(bit_vector);
                        native_and(sv, tv);
                        native_or(sm, tm);
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.and_sound(ct_t);
                        assert(r.to_tn() == ct_s.bw_and(ct_t).tnum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1 & c2) by {
                            native_fits(c1); native_fits(c2);
                            native_and(c1, c2);
                            assert(ct_s.has(c1 as nat) && ct_t.has(c2 as nat));
                        };
                    }
                    r
                }
                #[inline] pub fn bw_xor(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1 ^ c2),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).bw_xor(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let v = self.val ^ t.val; let m = self.mask | t.mask;
                    let r = ExecTnum { val: v & !m, mask: m };
                    proof {
                        assert(((v & !m) & m) == (0 as $uint)) by(bit_vector);
                        native_xor(self.val, t.val);
                        native_or(self.mask, t.mask);
                        native_and_not(v, m);
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.xor_sound(ct_t);
                        assert(r.to_tn() == ct_s.bw_xor(ct_t).tnum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1 ^ c2) by {
                            native_fits(c1); native_fits(c2);
                            native_xor(c1, c2);
                            assert(ct_s.has(c1 as nat) && ct_t.has(c2 as nat));
                        };
                    }
                    r
                }
                /// Logical shift right by k bits.
                #[inline] pub fn rshi(&self, k: u32) -> (r: ExecTnum)
                    requires self.wf(), k < $bits
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c >> (k as $uint)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).rshi(k as nat).tnum
                {
                    let v = self.val; let m = self.mask; let ku = k as $uint;
                    proof { assert(v & m == (0 as $uint) ==> (v >> ku) & (m >> ku) == (0 as $uint)) by(bit_vector); }
                    let r = ExecTnum { val: v >> ku, mask: m >> ku };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ct = ChoppedTnum { tnum: self.to_tn(), w };
                        ct.rshi_sound(k as nat);
                        // Bridge: native >> k == spec rshi
                        native_rshi(v, k as nat);
                        native_rshi(m, k as nat);
                        assert(r.to_tn() == ct.rshi(k as nat).tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c >> ku) by {
                            native_fits(c);
                            native_rshi(c, k as nat);
                            assert(ct.has(c as nat));
                        };
                    }
                    r
                }
                /// Shift left by k bits, truncated to the width.
                #[inline] pub fn lshi(&self, k: u32) -> (r: ExecTnum)
                    requires self.wf(), k < $bits
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c << (k as $uint)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).lshi(k as nat).tnum
                {
                    let v = self.val; let m = self.mask; let ku = k as $uint;
                    proof { assert(v & m == (0 as $uint) ==> (v << ku) & (m << ku) == (0 as $uint)) by(bit_vector); }
                    let r = ExecTnum { val: v << ku, mask: m << ku };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ct = ChoppedTnum { tnum: self.to_tn(), w };
                        ct.lshi_sound(k as nat);
                        // Bridge: native << k == chop(spec lshi, W)
                        native_lshi(v, k as nat);
                        native_lshi(m, k as nat);
                        assert(r.to_tn() == ct.lshi(k as nat).tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c << ku) by {
                            native_fits(c);
                            native_lshi(c, k as nat);
                            assert(ct.has(c as nat));
                            assert(ct.lshi(k as nat).has(chop(lshi(c as nat, k as nat), w)));
                        };
                    }
                    r
                }
                /// Bitwise NOT: flip the known bits, keep the unknown ones. This is
                /// the spec XOR with the all-ones word.
                #[inline] pub fn bw_not(&self) -> (r: ExecTnum)
                    requires self.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(!c),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).bw_not().tnum
                {
                    let v = self.val; let m = self.mask;
                    let ones: $uint = !(0 as $uint);
                    let x = v ^ ones;
                    let r = ExecTnum { val: x & !m, mask: m };
                    proof {
                        assert(((x & !m) & m) == (0 as $uint)) by(bit_vector);
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ct = ChoppedTnum { tnum: self.to_tn(), w };
                        ct.not_sound();
                        // Bridge: the native all-ones word is spec all_ones(W).
                        exp_concrete(w);
                        assert(ones == $max_val) by(bit_vector) requires ones == !(0 as $uint);
                        assert(ones as nat == all_ones(w));
                        native_xor(v, ones);
                        native_or(m, 0);
                        assert(m | (0 as $uint) == m) by(bit_vector);
                        native_and_not(x, m);
                        assert(r.to_tn() == ct.bw_not().tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(!c) by {
                            native_fits(c);
                            native_xor(c, ones);
                            native_xor_ones(c);
                            assert(ct.has(c as nat));
                        };
                    }
                    r
                }
                /// AND with the complement of the second operand: the spec
                /// bw_and_not, computed directly.
                #[inline] pub fn bw_and_not(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1 & !c2),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).bw_and_not(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let v = (sv & !tv) & !tm;
                    let m = sm | tm;
                    let r = ExecTnum { val: v, mask: m };
                    proof {
                        assert(sv & sm == (0 as $uint) ==> (((sv & !tv) & !tm) & (sm | tm)) == (0 as $uint)) by(bit_vector);
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.and_not_sound(ct_t);
                        // Bridge: native bitwise == spec bitwise
                        native_and_not(sv, tv);
                        native_and_not(sv & !tv, tm);
                        native_or(sm, tm);
                        assert(r.to_tn() == ct_s.bw_and_not(ct_t).tnum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1 & !c2) by {
                            native_fits(c1); native_fits(c2);
                            native_and_not(c1, c2);
                            assert(ct_s.has(c1 as nat) && ct_t.has(c2 as nat));
                        };
                    }
                    r
                }
                #[inline] pub fn add(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).add(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
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
                /// Two's complement negation, encoded as NOT then add one: the spec
                /// neg is bw_not followed by add of the unit 1.
                #[inline] pub fn neg(&self) -> (r: ExecTnum)
                    requires self.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has((0 as $uint).wrapping_sub(c)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).neg().tnum
                {
                    let n = self.bw_not();
                    proof { assert((1 as $uint) & (0 as $uint) == (0 as $uint)) by(bit_vector); }
                    let one = ExecTnum { val: 1, mask: 0 };
                    let r = n.add(&one);
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ct = ChoppedTnum { tnum: self.to_tn(), w };
                        ct.neg_sound();
                        assert(one.to_tn() == Tnum::unit(1));
                        assert(r.to_tn() == ct.neg().tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has((0 as $uint).wrapping_sub(c)) by {
                            native_fits(c);
                            native_neg(c);
                            assert(ct.has(c as nat));
                        };
                    }
                    r
                }
                /// Subtraction, encoded as adding the negation: the spec sub.
                #[inline] pub fn sub(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_sub(c2)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).sub(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let nt = t.neg();
                    let r = self.add(&nt);
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.sub_sound(ct_t);
                        assert(r.to_tn() == ct_s.sub(ct_t).tnum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_sub(c2)) by {
                            native_fits(c1); native_fits(c2);
                            native_sub(c1, c2);
                            assert(ct_s.has(c1 as nat) && ct_t.has(c2 as nat));
                        };
                    }
                    r
                }
                #[inline] pub fn rsh(&self) -> (r: ExecTnum)
                    requires self.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c >> (1 as $uint)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).rsh().tnum
                {
                    let v = self.val; let m = self.mask;
                    proof { assert(v & m == (0 as $uint) ==> (v >> (1 as $uint)) & (m >> (1 as $uint)) == (0 as $uint)) by(bit_vector); }
                    let r = ExecTnum { val: v >> 1, mask: m >> 1 };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ct = ChoppedTnum { tnum: self.to_tn(), w };
                        ct.rsh_sound();
                        // Bridge: native >> 1 == spec rsh
                        native_rsh(v);
                        native_rsh(m);
                        assert(r.to_tn() == ct.rsh().tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c >> (1 as $uint)) by {
                            native_fits(c);
                            native_rsh(c);
                        };
                    }
                    r
                }
                #[inline] pub fn lsh(&self) -> (r: ExecTnum)
                    requires self.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c << (1 as $uint)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).lsh().tnum
                {
                    let v = self.val; let m = self.mask;
                    proof { assert(v & m == (0 as $uint) ==> (v << (1 as $uint)) & (m << (1 as $uint)) == (0 as $uint)) by(bit_vector); }
                    let r = ExecTnum { val: v << 1, mask: m << 1 };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ct = ChoppedTnum { tnum: self.to_tn(), w };
                        ct.lsh_sound();
                        // Bridge: native << 1 == chop(spec lsh, W)
                        native_lsh(v);
                        native_lsh(m);
                        assert(r.to_tn() == ct.lsh().tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c << (1 as $uint)) by {
                            native_fits(c);
                            native_lsh(c);
                            assert(ct.has(c as nat));
                            assert(ct.lsh().has(chop(lsh(c as nat), w)));
                            assert((c << (1 as $uint)) as nat == chop(lsh(c as nat), w));
                        };
                    }
                    r
                }
                #[inline] pub fn join(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c), forall|c: $uint| #![auto] t.has(c) ==> r.has(c),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).join(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let sv = self.val; let sm = self.mask; let tv = t.val; let tm = t.mask;
                    let v = sv & tv;
                    let u = (sv ^ sm) | (tv ^ tm);
                    let m = v ^ u;
                    let r = ExecTnum { val: v & !m, mask: m };
                    proof {
                        assert(sv & sm == (0 as $uint) && tv & tm == (0 as $uint) ==> ((v & !m) & m == (0 as $uint))) by(bit_vector);
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.join_sound(ct_t);
                        // Bridge: native bitwise == spec bitwise
                        native_and(sv, tv);
                        native_xor(sv, sm); native_xor(tv, tm);
                        native_or(sv ^ sm, tv ^ tm);
                        native_xor(v, u);
                        native_join_val(sv, sm, tv, tm);
                        assert(r.to_tn() == ct_s.join(ct_t).tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c) by {
                            native_fits(c);
                            assert(ct_s.has(c as nat));
                        };
                        assert forall|c: $uint| #![auto] t.has(c) implies r.has(c) by {
                            native_fits(c);
                            assert(ct_t.has(c as nat));
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
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: self.to_tn(), w };
                        let ct_t = ChoppedTnum { tnum: t.to_tn(), w };
                        ct_s.meet_sound(ct_t);
                        // Bridge: native bitwise == spec bitwise
                        native_or(sv, tv);
                        native_xor(sv, sm); native_xor(tv, tm);
                        native_and(sv ^ sm, tv ^ tm);
                        native_xor(v, u);
                        let spec = ct_s.meet(ct_t).tnum;
                        assert(spec.val == v as nat && spec.mask == m as nat);
                        // A common member makes the spec meet's value disjoint from
                        // its mask, so the executable normalization is the identity.
                        assert forall|c: $uint| #![auto] self.has(c) && t.has(c) implies r.has(c) by {
                            native_fits(c);
                            assert(ct_s.has(c as nat) && ct_t.has(c as nat));
                            assert(spec.has(c as nat));
                            spec.has_equiv(c as nat);
                            native_and_not(c, m);
                            native_and_not_idem(c, m, v);
                            native_and_not(v, m);
                            assert(r.to_tn() == spec);
                        };
                    }
                    r
                }
                /// Multiplication following Anum::mul_step_rc: the exact product of the
                /// known bits is computed once, and an accumulator Tnum with val 0
                /// collects only the uncertainty masks of the shifted multiplicand.
                /// The loop simulates mul_step_rc through to_chopped(), and
                /// Anum::mul_step_r equates mul_step_rc with tnum_mul, which is the
                /// L3 ChoppedTnum::mul.
                pub fn mul(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_mul(c2)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).mul(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let ghost w: nat = $bits as nat;
                    let ghost t0 = self.to_tn();
                    let ghost t1 = t.to_tn();
                    let ghost avs = Tnum::ctor(mul(t0.val, t1.val), 0);
                    // The exact product of the known bits.
                    let pv = self.val.wrapping_mul(t.val);
                    proof { assert(pv & (0 as $uint) == (0 as $uint)) by(bit_vector); }
                    let acc_v = ExecTnum { val: pv, mask: 0 };
                    proof { assert((0 as $uint) & (0 as $uint) == (0 as $uint)) by(bit_vector); }
                    let mut acc_m = ExecTnum { val: 0, mask: 0 };
                    let mut p = *self;
                    let mut q = *t;
                    let ghost mut ps = t0;
                    let ghost mut qs = t1;
                    let ghost mut ams = Tnum::ctor(0, 0);
                    let ghost mut a_s = Anum::zero();
                    proof {
                        // From the initial state, mul_step_rc is tnum_mul.
                        nat_mul_acc_correct(t0.val, t1.val, 0);
                        Anum::mul_step_r(t0, t1, t0, t1, avs, ams, a_s);
                        // The executable state is the chopped spec state.
                        native_fits(t.val); native_fits(t.mask);
                        exp_pos(w);
                        chop_id(0, w);
                        disj_zero(0);
                    }
                    while !(p.val == 0 && p.mask == 0)
                        invariant
                            w == $bits as nat,
                            p.wf(), q.wf(), acc_m.wf(),
                            p.to_tn() == ps,
                            q.to_tn() == qs.chop_tn(w),
                            acc_m.to_tn() == ams.chop_tn(w),
                            ams.inv(),
                            Anum::mul_step_rc(t0, t1, ps, qs, avs, ams, a_s) == Anum::tnum_mul(t0, t1),
                        decreases p.val as nat + p.mask as nat
                    {
                        let ghost ps0 = ps;
                        let ghost qs0 = qs;
                        let ghost ams0 = ams;
                        let ghost a0 = a_s;
                        proof {
                            // The branch tests are the spec head bit of p.
                            native_low_bit(p.val);
                            native_low_bit(p.mask);
                            exp_pos(w);
                            chop_id(0, w);
                        }
                        if (p.val & 1) == 1 {
                            proof { assert((0 as $uint) & q.mask == (0 as $uint)) by(bit_vector); }
                            let add_t = ExecTnum { val: 0, mask: q.mask };
                            acc_m = acc_m.add(&add_t);
                            proof {
                                let c = Tnum::ctor(0, qs0.mask);
                                assert(add_t.to_tn() == c.chop_tn(w));
                                Tnum::chop_add_bitwise(ams0, c, w);
                                disj_zero(qs0.mask);
                                ams0.add_bitwise_eq(c);
                                ams0.add_inv(c);
                                ams = ams0.add(c);
                            }
                        } else if (p.mask & 1) == 1 {
                            proof { assert((0 as $uint) & (q.val | q.mask) == (0 as $uint)) by(bit_vector); }
                            let add_t = ExecTnum { val: 0, mask: q.val | q.mask };
                            acc_m = acc_m.add(&add_t);
                            proof {
                                let c = Tnum::ctor(0, qs0.max());
                                native_or(q.val, q.mask);
                                chop_bw_or(qs0.val, qs0.mask, w);
                                assert(add_t.to_tn() == c.chop_tn(w));
                                Tnum::chop_add_bitwise(ams0, c, w);
                                disj_zero(qs0.max());
                                ams0.add_bitwise_eq(c);
                                ams0.add_inv(c);
                                ams = ams0.add(c);
                            }
                        }
                        proof { a_s = a0.add(Anum::from_tnum(qs0.mul_bit(ps0.head()))); }
                        p = p.rsh();
                        q = q.lsh();
                        proof {
                            ps = ps0.rsh();
                            qs = qs0.lsh();
                            Tnum::chop_lsh_tn(qs0, w);
                        }
                    }
                    let r = acc_m.add(&acc_v);
                    proof {
                        // p is zero, so mul_step_rc has returned ams + avs.
                        assert(ps.is_zero());
                        assert(ams.add(avs) == Anum::tnum_mul(t0, t1));
                        // Bridge: the native product is the chopped spec product.
                        bridge_mul(self.val, t.val);
                        exp_pos(w);
                        chop_id(0, w);
                        assert(acc_v.to_tn() == avs.chop_tn(w));
                        Tnum::chop_add_bitwise(ams, avs, w);
                        disj_zero_r(mul(t0.val, t1.val));
                        ams.add_bitwise_eq(avs);
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: t0, w };
                        let ct_t = ChoppedTnum { tnum: t1, w };
                        assert(r.to_tn() == ct_s.mul(ct_t).tnum);
                        ct_s.mul_sound(ct_t);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_mul(c2)) by {
                            native_fits(c1); native_fits(c2);
                            assert(ct_s.has(c1 as nat) && ct_t.has(c2 as nat));
                            nat_mul_acc_correct(c1 as nat, c2 as nat, 0);
                            bridge_mul(c1, c2);
                        };
                    }
                    r
                }
                /// Pair-join multiplication (Tnum::pair_mul on W-bit registers).
                /// Start from the exact product of the known parts; for each
                /// unknown bit l of t, join the accumulator with itself plus the
                /// constant self.val << l; then for each unknown bit k of self,
                /// join it with itself plus t << k. The two loops shift the
                /// registers as the L2 recursions pj_const and pj_tnum do, and
                /// each step is the chopped L2 step (chop_add_bitwise, chop_join,
                /// chop_lsh_tn).
                pub fn mul_pj(&self, t: &ExecTnum) -> (r: ExecTnum)
                    requires self.wf(), t.wf()
                    ensures r.wf(), forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_mul(c2)),
                        r.to_tn() == (ChoppedTnum { tnum: self.to_tn(), w: $bits as nat }).pair_mul(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).tnum
                {
                    let ghost w: nat = $bits as nat;
                    let ghost t0 = self.to_tn();
                    let ghost t1 = t.to_tn();
                    let ghost acc0 = Tnum::unit(prod(t0.val, t1.val));
                    let ghost cst = Tnum::pj_const(t0.val, t1.mask, acc0);
                    let ghost whole = Tnum::pj_tnum(t1, t0.mask, cst);
                    let pv = self.val.wrapping_mul(t.val);
                    proof { assert(pv & (0 as $uint) == (0 as $uint)) by(bit_vector); }
                    let mut acc = ExecTnum { val: pv, mask: 0 };
                    let mut s: $uint = self.val;
                    let mut ym: $uint = t.mask;
                    let ghost mut ss: nat = t0.val;
                    let ghost mut acc_s: Tnum = acc0;
                    proof {
                        bridge_mul(self.val, t.val);
                        exp_pos(w);
                        chop_id(0, w);
                        native_fits(self.val);
                        disj_zero_r(prod(t0.val, t1.val));
                    }
                    // Phase 1: the unknown bits of t, with the shifted known part of self.
                    while ym != 0
                        invariant
                            w == $bits as nat,
                            acc.wf(),
                            acc.to_tn() == acc_s.chop_tn(w),
                            acc_s.inv(),
                            s as nat == chop(ss, w),
                            Tnum::pj_const(ss, ym as nat, acc_s) == cst,
                        decreases ym
                    {
                        let ghost acc_s0 = acc_s;
                        let ghost ss0 = ss;
                        let ghost ym0 = ym;
                        proof {
                            native_low_bit(ym);
                            exp_pos(w);
                            chop_id(0, w);
                        }
                        if (ym & 1) == 1 {
                            proof { assert(s & (0 as $uint) == (0 as $uint)) by(bit_vector); }
                            let c = ExecTnum { val: s, mask: 0 };
                            let sum = acc.add(&c);
                            acc = acc.join(&sum);
                            proof {
                                let u = Tnum::unit(ss0);
                                assert(c.to_tn() == u.chop_tn(w));
                                disj_zero_r(ss0);
                                Tnum::chop_add_bitwise(acc_s0, u, w);
                                acc_s0.add_bitwise_eq(u);
                                acc_s0.add_inv(u);
                                Tnum::chop_join(acc_s0, acc_s0.add(u), w);
                                Tnum::pj_step_inv(acc_s0, u);
                                acc_s = acc_s0.join(acc_s0.add(u));
                            }
                        }
                        proof {
                            native_lsh(s);
                            chop_lsh(ss0, w);
                            native_rsh(ym);
                            ss = lsh(ss0);
                        }
                        proof { assert(ym >> (1 as $uint) < ym) by(bit_vector) requires ym != (0 as $uint); }
                        s = s << 1;
                        ym = ym >> 1;
                    }
                    let mut y = *t;
                    let mut xm: $uint = self.mask;
                    let ghost mut ys: Tnum = t1;
                    proof {
                        native_fits(t.val); native_fits(t.mask);
                        t.wf_inv();
                    }
                    // Phase 2: the unknown bits of self, with t shifted.
                    while xm != 0
                        invariant
                            w == $bits as nat,
                            acc.wf(), y.wf(),
                            acc.to_tn() == acc_s.chop_tn(w),
                            y.to_tn() == ys.chop_tn(w),
                            acc_s.inv(), ys.inv(),
                            Tnum::pj_tnum(ys, xm as nat, acc_s) == whole,
                        decreases xm
                    {
                        let ghost acc_s0 = acc_s;
                        let ghost ys0 = ys;
                        proof { native_low_bit(xm); }
                        if (xm & 1) == 1 {
                            let sum = acc.add(&y);
                            acc = acc.join(&sum);
                            proof {
                                Tnum::chop_add_bitwise(acc_s0, ys0, w);
                                acc_s0.add_bitwise_eq(ys0);
                                acc_s0.add_inv(ys0);
                                Tnum::chop_join(acc_s0, acc_s0.add(ys0), w);
                                Tnum::pj_step_inv(acc_s0, ys0);
                                acc_s = acc_s0.join(acc_s0.add(ys0));
                            }
                        }
                        y = y.lsh();
                        proof {
                            Tnum::chop_lsh_tn(ys0, w);
                            disj_cons(ys0.val, Bit::f(), ys0.mask, Bit::f());
                            ys = ys0.lsh();
                            native_rsh(xm);
                            assert(xm >> (1 as $uint) < xm) by(bit_vector) requires xm != (0 as $uint);
                        }
                        xm = xm >> 1;
                    }
                    let r = acc;
                    proof {
                        self.to_chopped(); t.to_chopped();
                        let ct_s = ChoppedTnum { tnum: t0, w };
                        let ct_t = ChoppedTnum { tnum: t1, w };
                        assert(r.to_tn() == ct_s.pair_mul(ct_t).tnum);
                        ct_s.pair_mul_sound(ct_t);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_mul(c2)) by {
                            native_fits(c1); native_fits(c2);
                            assert(ct_s.has(c1 as nat) && ct_t.has(c2 as nat));
                            nat_mul_acc_correct(c1 as nat, c2 as nat, 0);
                            bridge_mul(c1, c2);
                        };
                    }
                    r
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
                proof fn to_chopped(self)
                    ensures (ChoppedAnum { anum: self.to_an(), w: $bits as nat }).inv()
                {
                    self.to_an().to_tnum_inv();
                    native_fits(self.base);
                    native_fits(self.span);
                }
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
                #[inline] pub fn constant(n: $uint) -> (r: ExecAnum) ensures r.has(n) {
                    let r = ExecAnum { base: n, span: 0 };
                    proof {
                        r.has_eq_uint(n);
                        assert((0 as $uint) & !(0 as $uint) == (0 as $uint)) by(bit_vector);
                    }
                    r
                }
                #[inline] pub fn top() -> (r: ExecAnum)
                    ensures forall|n: $uint| #![auto] r.has(n)
                {
                    let r = ExecAnum { base: 0, span: !(0 as $uint) };
                    proof {
                        assert forall|n: $uint| #![auto] r.has(n) by {
                            ExecAnum::top_has(n);
                        };
                    }
                    r
                }
                /// Sound fixed-width addition, through ChoppedAnum::add_sound: top when
                /// a represented bound or the span sum would wrap, otherwise the spec
                /// add, whose members cannot wrap because each is at most base + span.
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
                    if max1 < b1 || max2 < b2 || max_sum < max1 || max_sum < max2 || v < b1 {
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
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ca_s = ChoppedAnum { anum: self.to_an(), w };
                        let ca_t = ChoppedAnum { anum: t.to_an(), w };
                        ca_s.add_sound(ca_t);
                        // On this path no sum wraps: each max is above its base and
                        // the max sum is above both maxes.
                        let s12 = s1.wrapping_add(s2);
                        assert(v >= b2 && max1 >= s1 && max2 >= s2 && s12 >= s1 && s12 >= s2) by(bit_vector)
                            requires v == b1.wrapping_add(b2), v >= b1,
                                     max1 == b1.wrapping_add(s1), max1 >= b1,
                                     max2 == b2.wrapping_add(s2), max2 >= b2,
                                     max_sum == max1.wrapping_add(max2), max_sum >= max1, max_sum >= max2,
                                     s12 == s1.wrapping_add(s2);
                        add_no_overflow(b1, b2, v);
                        add_no_overflow(b1, s1, max1);
                        add_no_overflow(b2, s2, max2);
                        add_no_overflow(max1, max2, max_sum);
                        add_no_overflow(s1, s2, s12);
                        // Bridge: the executable span is the spec span, which adds
                        // the two span Tnums (0, s1) + (0, s2).
                        let mt_s = self.to_an().mask_tnum();
                        let mt_t = t.to_an().mask_tnum();
                        disj_zero(s1 as nat); disj_zero(s2 as nat);
                        mt_s.add_bitwise_eq(mt_t);
                        nat_add_correct(0, 0);
                        nat_add_correct(0, nat_add(s1 as nat, s2 as nat));
                        native_xor(s12, 0);
                        assert(s12 ^ (0 as $uint) == s12) by(bit_vector);
                        native_or(s12, s1);
                        native_or(s12 | s1, s2);
                        assert(r.to_an() == self.to_an().add(t.to_an()));
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_add(c2)) by {
                            native_fits(c1); native_fits(c2);
                            // Members are at most their max, so the sum does not wrap.
                            self.to_an().has_le_max(c1 as nat);
                            t.to_an().has_le_max(c2 as nat);
                            let cs = c1.wrapping_add(c2);
                            assert(cs as nat == c1 as nat + c2 as nat);
                            nat_add_correct(c1 as nat, c2 as nat);
                            native_fits(cs);
                            assert(ca_s.has(c1 as nat) && ca_t.has(c2 as nat));
                            assert(fits(nat_add(c1 as nat, c2 as nat), w));
                        };
                    }
                    r
                }
                /// Sound fixed-width subtraction, through ChoppedAnum::sub_sound: top
                /// when t's maximum wraps or exceeds self's base, otherwise the spec
                /// sub, whose differences cannot wrap because every member of t is at
                /// most t's maximum.
                #[inline] pub fn sub(&self, t: &ExecAnum) -> (r: ExecAnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_sub(c2))
                {
                    let b1 = self.base; let s1 = self.span;
                    let b2 = t.base; let s2 = t.span;
                    let max2 = b2.wrapping_add(s2);
                    let v = b1.wrapping_sub(max2);
                    let s12 = s1.wrapping_add(s2);
                    let m = s12 | s1 | s2;
                    if max2 < b2 || v > b1 {
                        return Self::top();
                    }
                    let r = ExecAnum { base: v, span: m };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ca_s = ChoppedAnum { anum: self.to_an(), w };
                        let ca_t = ChoppedAnum { anum: t.to_an(), w };
                        // On this path t's maximum does not wrap and is at most b1.
                        assert(max2 >= s2 && b1 >= max2) by(bit_vector)
                            requires max2 == b2.wrapping_add(s2), max2 >= b2,
                                     v == b1.wrapping_sub(max2), v <= b1;
                        add_no_overflow(b2, s2, max2);
                        ca_s.sub_sound(ca_t);
                        // Bridge: the executable span is the chopped spec span,
                        // which adds the span Tnums (0, s1) + (0, s2).
                        let mt_s = self.to_an().mask_tnum();
                        let mt_t = t.to_an().mask_tnum();
                        disj_zero(s1 as nat); disj_zero(s2 as nat);
                        mt_s.add_bitwise_eq(mt_t);
                        let sn = nat_add(s1 as nat, s2 as nat);
                        nat_add_correct(0, 0);
                        nat_add_correct(0, sn);
                        bridge_add(s1, s2);
                        native_xor(s12, 0);
                        assert(s12 ^ (0 as $uint) == s12) by(bit_vector);
                        native_or(s12, s1);
                        native_or(s12 | s1, s2);
                        exp_concrete(w);
                        chop_id(0, w); chop_id(s1 as nat, w); chop_id(s2 as nat, w);
                        chop_bw_xor(sn, 0, w);
                        chop_bw_or(bw_xor(sn, 0), s1 as nat, w);
                        chop_bw_or(bw_or(bw_xor(sn, 0), s1 as nat), s2 as nat, w);
                        assert(r.to_an() == ca_s.sub(ca_t).anum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_sub(c2)) by {
                            native_fits(c1); native_fits(c2);
                            // Every member of t is at most max2 <= b1 <= c1, so no wrap.
                            t.to_an().has_le_max(c2 as nat);
                            assert(ca_s.has(c1 as nat) && ca_t.has(c2 as nat));
                            assert(c1.wrapping_sub(c2) as nat == (c1 - c2) as nat);
                        };
                    }
                    r
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
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ca = ChoppedAnum { anum: self.to_an(), w };
                        ca.div_const_sound(d as nat);
                        // On this path base + span does not wrap.
                        let b = self.base; let sp = self.span;
                        assert(max_v >= sp) by(bit_vector)
                            requires max_v == b.wrapping_add(sp), max_v >= b;
                        add_no_overflow(b, sp, max_v);
                        assert(r.to_an() == self.to_an().div_const(d as nat));
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c / d) by {
                            native_fits(c);
                            assert(ca.has(c as nat));
                        };
                    }
                    r
                }
                /// The least 2^k - 1 at or above n, which is the spec all_ones(len(n)).
                pub fn ones_mask(n: $uint) -> (r: $uint)
                    ensures r >= n, r & r.wrapping_add(1) == 0, r as nat == all_ones(len(n as nat))
                {
                    if n == 0 {
                        proof {
                            assert((0 as $uint) & (0 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector);
                            assert(exp(0) == 1) by { assert(lshi(1, 0) == 1); }
                        }
                        return 0;
                    }
                    // Build 2^k - 1 by repeated doubling + 1
                    let mut mask: $uint = 1;
                    proof {
                        assert((1 as $uint) & (1 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector);
                        assert(exp(0) == 1) by { assert(lshi(1, 0) == 1); }
                        exp_succ(0);
                        exp_concrete($bits as nat);
                    }
                    let mut i: u32 = 0;
                    while mask < n && i < $bits
                        invariant
                            n > 0,
                            i < $bits,
                            mask & mask.wrapping_add(1) == 0,
                            mask as nat == all_ones((i + 1) as nat),
                            all_ones(i as nat) < n as nat,
                            exp($bits as nat) == ($max_val as nat) + 1,
                        decreases ($bits - i)
                    {
                        proof {
                            assert(mask & mask.wrapping_add(1) == (0 as $uint) ==>
                                (mask.wrapping_add(mask).wrapping_add(1)) & (mask.wrapping_add(mask).wrapping_add(1)).wrapping_add(1) == (0 as $uint))
                                by(bit_vector);
                            // mask < n <= MAX = all_ones(bits), so i + 1 < bits and doubling does not wrap.
                            exp_succ((i + 1) as nat);
                            exp_succ(i as nat);
                            if (i + 1) as nat >= $bits as nat {
                                exp_le($bits as nat, (i + 1) as nat);
                            }
                            assert((i + 2) as nat <= $bits as nat);
                            exp_le((i + 2) as nat, $bits as nat);
                            exp_pos((i + 1) as nat);
                            assert(2 * (mask as nat) + 1 <= $max_val as nat);
                        }
                        let ghost old = mask;
                        mask = mask.wrapping_add(mask).wrapping_add(1);
                        i += 1;
                        proof {
                            assert(mask as nat == 2 * (old as nat) + 1);
                        }
                    }
                    proof {
                        all_ones_len_unique(n as nat, (i + 1) as nat);
                    }
                    mask
                }
                /// An Anum read as a Tnum: Tn(0, span) + Tn(base, 0), the spec
                /// ChoppedAnum::to_tnum. The addition carries the base into the
                /// span, so a base whose bits overlap the span is covered.
                pub fn to_etn(&self) -> (r: ExecTnum)
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c),
                        r.to_tn() == (ChoppedAnum { anum: self.to_an(), w: $bits as nat }).to_tnum().tnum
                {
                    proof {
                        assert((0 as $uint) & self.span == (0 as $uint)) by(bit_vector);
                        assert(self.base & (0 as $uint) == (0 as $uint)) by(bit_vector);
                    }
                    let m = ExecTnum { val: 0, mask: self.span };
                    let v = ExecTnum { val: self.base, mask: 0 };
                    let r = m.add(&v);
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ca = ChoppedAnum { anum: self.to_an(), w };
                        ca.to_tnum_sound();
                        let an = self.to_an();
                        disj_zero(an.span);
                        disj_zero_r(an.base);
                        an.mask_tnum().add_bitwise_eq(an.val_tnum());
                        assert(m.to_tn() == an.mask_tnum() && v.to_tn() == an.val_tnum());
                        assert(r.to_tn() == ca.to_tnum().tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c) by {
                            native_fits(c);
                            assert(ca.has(c as nat));
                        };
                    }
                    r
                }
                /// A Tnum read as an Anum: the spec ChoppedAnum::from_tnum.
                #[inline] pub fn from_etn(t: &ExecTnum) -> (r: ExecAnum)
                    requires t.wf()
                    ensures forall|c: $uint| #![auto] t.has(c) ==> r.has(c),
                        r.to_an() == ChoppedAnum::from_tnum(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).anum
                {
                    let r = ExecAnum { base: t.val, span: t.mask };
                    proof {
                        let w: nat = $bits as nat;
                        t.to_chopped();
                        let ct = ChoppedTnum { tnum: t.to_tn(), w };
                        ChoppedAnum::from_tnum_sound(ct);
                        assert(r.to_an() == ChoppedAnum::from_tnum(ct).anum);
                        assert forall|c: $uint| #![auto] t.has(c) implies r.has(c) by {
                            native_fits(c);
                            assert(ct.has(c as nat));
                        };
                    }
                    r
                }
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

                #[inline] pub fn constant(n: $uint) -> (r: ExecUnum) ensures r.has(n) {
                    proof { Unum::zero_offset_admitted((!(0 as $uint)) as nat, true); }
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
                    // The negated range wraps when the input range does, or when it
                    // holds 0 and something else: -[0, e] = {0} u [-e, MAX].
                    if self.base.wrapping_add(self.extent) < self.base || (self.base == 0 && self.extent != 0) {
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
