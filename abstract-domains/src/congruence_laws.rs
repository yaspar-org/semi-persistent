// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Lattice-law verification harnesses for canonical congruences, including bottom.
//! Local bottom lifting calls the existing Congruence operations; no arithmetic
//! implementation is duplicated.
#![allow(unused_imports, unused_variables)]
use crate::congruence::Congruence;
use crate::lattice::{BotOr, Domain};
use crate::word::Word;
use vstd::prelude::*;

verus! {
type C<W> = BotOr<Congruence<W>>;

pub open spec fn subset<W: Word>(a: &C<W>, b: &C<W>) -> bool {
    forall|x: W| #[trigger] a.gamma(x) ==> b.gamma(x)
}

proof fn canonical<W: Word>(a: &C<W>, b: &C<W>)
    requires a.wf(), b.wf(), subset(a, b), subset(b, a),
    ensures *a == *b,
{
    match (a, b) {
        (BotOr::Val(av), BotOr::Val(bv)) => {
            assert forall|x: W| #[trigger] av.gamma(x) == bv.gamma(x) by {
                assert(a.gamma(x) == b.gamma(x));
            }
            Congruence::lemma_canonical(av, bv);
        },
        (BotOr::Val(av), BotOr::Bot) => {
            av.residue_member();
            assert(a.gamma(av.residue()));
        },
        (BotOr::Bot, BotOr::Val(bv)) => {
            bv.residue_member();
            assert(b.gamma(bv.residue()));
        },
        _ => {},
    }
}

// Local copy of BotOr::meet in lattice.rs: call Congruence::meet directly to
// retain exact intersection. The generic Domain contract allows inexactness.
fn meet<W: Word>(a: &C<W>, b: &C<W>) -> (r: C<W>)
    requires a.wf(), b.wf(),
    ensures r.wf(), forall|x: W| #[trigger] r.gamma(x) == (a.gamma(x) && b.gamma(x)),
{
    match (a, b) {
        (BotOr::Val(av), BotOr::Val(bv)) => {
            let r = av.meet(bv);
            proof {
                assert forall|x: W| #[trigger] r.gamma(x) == (a.gamma(x) && b.gamma(x)) by {
                    assert(a.gamma(x) == av.has(x));
                    assert(b.gamma(x) == bv.has(x));
                    match &r {
                        BotOr::Val(v) => { assert(r.gamma(x) == v.has(x)); },
                        _ => {},
                    }
                }
            }
            r
        },
        _ => BotOr::Bot,
    }
}

// Local copy of BotOr::join in lattice.rs: call Congruence::join directly to
// retain its least-upper-bound contract, absent from the generic Domain interface.
fn join<W: Word>(a: &C<W>, b: &C<W>) -> (r: C<W>)
    requires a.wf(), b.wf(),
    ensures r.wf(), subset(a, &r), subset(b, &r),
        forall|c: C<W>| #[trigger] c.wf() && subset(a, &c) && subset(b, &c)
            ==> subset(&r, &c),
{
    match (a, b) {
        (BotOr::Bot, _) => b.dup(),
        (_, BotOr::Bot) => a.dup(),
        (BotOr::Val(av), BotOr::Val(bv)) => {
            let r = BotOr::Val(av.join(bv));
            proof {
                assert forall|x: W| #[trigger] a.gamma(x) implies r.gamma(x) by {
                    assert(av.has(x));
                    assert(r->Val_0.has(x));
                }
                assert forall|x: W| #[trigger] b.gamma(x) implies r.gamma(x) by {
                    assert(bv.has(x));
                    assert(r->Val_0.has(x));
                }
                assert forall|c: C<W>| #[trigger] c.wf() && subset(a, &c) && subset(b, &c)
                    implies subset(&r, &c) by {
                    match c {
                        BotOr::Bot => {
                            av.residue_member();
                            assert(a.gamma(av.residue()));
                        },
                        BotOr::Val(cv) => {
                            assert forall|x: W| #[trigger] av.has(x) implies cv.has(x) by {
                                assert(a.gamma(x));
                            }
                            assert forall|x: W| #[trigger] bv.has(x) implies cv.has(x) by {
                                assert(b.gamma(x));
                            }
                            assert forall|x: W| #[trigger] r.gamma(x) implies c.gamma(x) by {
                                assert(r->Val_0.has(x));
                            }
                        },
                    }
                }
            }
            r
        },
    }
}

/// Verifies structural equality for all five meet laws, for arbitrary words
/// and arbitrary well-formed operands (including bottom).
#[allow(dead_code)] // Verification harness, not a runtime API.
fn verify_meet_laws<W: Word>(a: &C<W>, b: &C<W>, c: &C<W>)
    requires a.wf(), b.wf(), c.wf(),
{
    let aa = meet(a, a);
    let ab = meet(a, b);
    let ba = meet(b, a);
    let bc = meet(b, c);
    let left = meet(&ab, c);
    let right = meet(a, &bc);
    let top = C::<W>::top();
    let bottom = BotOr::Bot;
    let at = meet(a, &top);
    let az = meet(a, &bottom);
    proof {
        canonical(&aa, a);
        assert(aa == *a); // idempotence
        canonical(&ab, &ba);
        assert(ab == ba); // commutativity
        canonical(&left, &right);
        assert(left == right); // associativity
        canonical(&at, a);
        assert(at == *a); // top identity
        canonical(&az, &bottom);
        assert(az == bottom); // bottom absorption
    }
}

/// Verifies structural equality for all five join laws from the existing LUB
/// contract, without assuming that join is exact set union.
#[allow(dead_code)] // Verification harness, not a runtime API.
fn verify_join_laws<W: Word>(a: &C<W>, b: &C<W>, c: &C<W>)
    requires a.wf(), b.wf(), c.wf(),
{
    let aa = join(a, a);
    let ab = join(a, b);
    let ba = join(b, a);
    let bc = join(b, c);
    let left = join(&ab, c);
    let right = join(a, &bc);
    let top = C::<W>::top();
    let bottom = BotOr::Bot;
    let at = join(a, &top);
    let az = join(a, &bottom);
    proof {
        canonical(&aa, a);
        assert(aa == *a); // idempotence
        canonical(&ab, &ba);
        assert(ab == ba); // commutativity
        assert(subset(a, &right));
        assert(subset(b, &right));
        assert(subset(&ab, &right));
        assert(subset(b, &left));
        assert(subset(c, &left));
        assert(subset(&bc, &left));
        canonical(&left, &right);
        assert(left == right); // associativity
        canonical(&at, &top);
        assert(at == top); // top absorption
        canonical(&az, a);
        assert(az == *a); // bottom identity
    }
}
// Instantiate both generic harnesses at the widest supported Word.
#[allow(dead_code)]
fn verify_u128_laws(a: &C<u128>, b: &C<u128>, c: &C<u128>)
    requires a.wf(), b.wf(), c.wf(),
{
    verify_meet_laws(a, b, c);
    verify_join_laws(a, b, c);
}
} // verus!
