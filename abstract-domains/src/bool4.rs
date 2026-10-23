// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Four-point boolean domain for Task 1.
//!
//! ```text
//! Bool4  = Bottom | False | True | Top
//! values = Bottom {}, False {false}, True {true}, Top {false, true}
//! ```
//!
//! `Top` is the running example's unknown. `Bottom` is the lattice's empty
//! value. It is not well formed for `Domain`: `wf` is false there, so every
//! well-formed value is nonempty and `Canonical` still holds. `Domain::meet`
//! returns `BotOr::Bot` when the intersection is empty. The lattice `meet`
//! still returns `Bottom`.

use crate::lattice::*;
use crate::reduce::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Bool4 {
    Bottom,
    False,
    True,
    Top,
}

impl Bool4 {
    #[inline]
    pub fn bottom() -> (r: Bool4)
        ensures
            r == Bool4::Bottom,
            forall|b: bool| !(#[trigger] r.has(b)),
    {
        Bool4::Bottom
    }

    #[inline]
    pub fn top() -> (r: Bool4)
        ensures
            r == Bool4::Top,
            forall|b: bool| #[trigger] r.has(b),
    {
        Bool4::Top
    }

    #[inline]
    pub fn constant(value: bool) -> (r: Bool4)
        ensures
            r == if value { Bool4::True } else { Bool4::False },
            forall|b: bool| #[trigger] r.has(b) <==> b == value,
    {
        if value { Bool4::True } else { Bool4::False }
    }

    pub open spec fn has(self, b: bool) -> bool {
        match self {
            Bool4::Bottom => false,
            Bool4::False => !b,
            Bool4::True => b,
            Bool4::Top => true,
        }
    }

    pub open spec fn refines(self, other: Bool4) -> bool {
        forall|b: bool| #[trigger] self.has(b) ==> other.has(b)
    }

    pub fn contains(self, b: bool) -> (r: bool)
        ensures
            r == self.has(b),
    {
        match self {
            Bool4::Bottom => false,
            Bool4::False => !b,
            Bool4::True => b,
            Bool4::Top => true,
        }
    }

    pub open spec fn join_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            (Bool4::Bottom, x) => x,
            (x, Bool4::Bottom) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Top,
        }
    }

    pub open spec fn meet_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::Top, x) => x,
            (x, Bool4::Top) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Bottom,
        }
    }

    pub open spec fn not_spec(self) -> Bool4 {
        match self {
            Bool4::Bottom => Bool4::Bottom,
            Bool4::False => Bool4::True,
            Bool4::True => Bool4::False,
            Bool4::Top => Bool4::Top,
        }
    }

    pub open spec fn and_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::False, _) | (_, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::True, Bool4::Top) | (Bool4::Top, Bool4::True) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        }
    }

    /// Exists direction of `and`, closed so the case split stays a boolean fact.
    pub closed spec fn and_exact_spec(self, other: Bool4, r: Bool4) -> bool {
        forall|b: bool|
            #[trigger] r.has(b) ==> exists|x: bool, y: bool|
                self.has(x) && other.has(y) && b == (x && y)
    }

    pub open spec fn or_spec(self, other: Bool4) -> Bool4 {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::True, _) | (_, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::False, Bool4::Top) | (Bool4::Top, Bool4::False) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        }
    }

    /// Exists direction of `or`, closed so the case split stays a boolean fact.
    pub closed spec fn or_exact_spec(self, other: Bool4, r: Bool4) -> bool {
        forall|b: bool|
            #[trigger] r.has(b) ==> exists|x: bool, y: bool|
                self.has(x) && other.has(y) && b == (x || y)
    }

    pub fn join(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.join_spec(other),
            forall|b: bool| #[trigger] self.has(b) ==> r.has(b),
            forall|b: bool| #[trigger] other.has(b) ==> r.has(b),
    {
        match (self, other) {
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            (Bool4::Bottom, x) => x,
            (x, Bool4::Bottom) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Top,
        }
    }

    pub fn meet(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.meet_spec(other),
            forall|b: bool| #[trigger] r.has(b) ==> self.has(b) && other.has(b),
            forall|b: bool|
                (#[trigger] self.has(b)) && (#[trigger] other.has(b)) ==> r.has(b),
    {
        match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::Top, x) => x,
            (x, Bool4::Top) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Bottom,
        }
    }

    // `not` keeps its concretization ensures. `std::ops::Not` cannot state them,
    // so this stays an inherent method, as `shl` and `shr` do.
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> (r: Bool4)
        ensures
            r == self.not_spec(),
            forall|b: bool| #[trigger] self.has(b) ==> r.has(!b),
            forall|b: bool| #[trigger] r.has(b) ==> self.has(!b),
    {
        match self {
            Bool4::Bottom => Bool4::Bottom,
            Bool4::False => Bool4::True,
            Bool4::True => Bool4::False,
            Bool4::Top => Bool4::Top,
        }
    }

    pub fn and(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.and_spec(other),
            forall|x: bool, y: bool|
                (#[trigger] self.has(x)) && (#[trigger] other.has(y)) ==> r.has(x && y),
            forall|b: bool|
                #[trigger] r.has(b) ==> exists|x: bool, y: bool|
                    self.has(x) && other.has(y) && b == (x && y),
    {
        let r = match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::False, _) | (_, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::True, Bool4::Top) | (Bool4::Top, Bool4::True) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        };
        proof {
            lemma_and_exact(self, other, r);
            reveal(Bool4::and_exact_spec);
            assert(self.and_exact_spec(other, r));
        }
        r
    }

    pub fn or(self, other: Bool4) -> (r: Bool4)
        ensures
            r == self.or_spec(other),
            forall|x: bool, y: bool|
                (#[trigger] self.has(x)) && (#[trigger] other.has(y)) ==> r.has(x || y),
            forall|b: bool|
                #[trigger] r.has(b) ==> exists|x: bool, y: bool|
                    self.has(x) && other.has(y) && b == (x || y),
    {
        let r = match (self, other) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::True, _) | (_, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::False, Bool4::Top) | (Bool4::Top, Bool4::False) | (Bool4::Top, Bool4::Top) => Bool4::Top,
        };
        proof {
            assert(r == self.or_spec(other));
            lemma_or_sound(self, other, r);
            lemma_or_exact(self, other, r);
            reveal(Bool4::or_exact_spec);
            assert(self.or_exact_spec(other, r));
        }
        r
    }

    /// Boolean equality. `Bottom` has no inputs, so the result is `Bottom`.
    pub fn eq(&self, o: &Self) -> (r: Bool4)
        ensures
            forall|x: bool, y: bool|
                (#[trigger] self.has(x)) && (#[trigger] o.has(y)) ==> r.has(x == y),
    {
        match (self, o) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => Bool4::Bottom,
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            (Bool4::False, Bool4::False) | (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::False,
        }
    }
}

impl Domain for Bool4 {
    type C = bool;

    open spec fn wf(&self) -> bool {
        *self != Bool4::Bottom
    }

    open spec fn gamma(&self, c: bool) -> bool {
        self.has(c)
    }

    fn dup(&self) -> (r: Self) {
        *self
    }

    fn top() -> (r: Self) {
        Bool4::Top
    }

    // A `match` is required: `matches!` does not connect `*self == *o` to the `leq` postcondition.
    #[allow(clippy::match_like_matches_macro)]
    fn leq(&self, o: &Self) -> (b: bool) {
        match (*self, *o) {
            (_, Bool4::Top) => true,
            (Bool4::False, Bool4::False) | (Bool4::True, Bool4::True) => true,
            (Bool4::Bottom, Bool4::Bottom) => true,
            _ => false,
        }
    }

    fn join(&self, o: &Self) -> (r: Self) {
        match (*self, *o) {
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            (Bool4::Bottom, x) | (x, Bool4::Bottom) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Top,
        }
    }

    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        match (*self, *o) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => BotOr::Bot,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => BotOr::Bot,
            (Bool4::Top, x) | (x, Bool4::Top) => BotOr::Val(x),
            (Bool4::False, Bool4::False) => BotOr::Val(Bool4::False),
            (Bool4::True, Bool4::True) => BotOr::Val(Bool4::True),
        }
    }

    fn widen(&self, o: &Self) -> (r: Self) {
        match (*self, *o) {
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            (Bool4::Bottom, x) | (x, Bool4::Bottom) => x,
            (Bool4::False, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => Bool4::Top,
        }
    }
}

impl Canonical for Bool4 {
    proof fn lemma_nonempty(&self) {
        match *self {
            Bool4::False => {
                assert(self.gamma(false));
            },
            Bool4::True => {
                assert(self.gamma(true));
            },
            Bool4::Top => {
                assert(self.gamma(true));
            },
            Bool4::Bottom => {
                assert(self.wf());
            },
        }
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        assert(a.gamma(false) == b.gamma(false));
        assert(a.gamma(true) == b.gamma(true));
        assert(*a != Bool4::Bottom && *b != Bool4::Bottom);
        if *a != *b {
            assert(a.gamma(false) != b.gamma(false) || a.gamma(true) != b.gamma(true));
        }
    }
}

impl Channel for Bool4 {
    open spec fn pre_wf(&self) -> bool {
        self.wf()
    }

    proof fn lemma_wf_pre(&self) {
    }

    fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>) {
        match (*self, *o) {
            (Bool4::Bottom, _) | (_, Bool4::Bottom) => BotOr::Bot,
            (Bool4::False, Bool4::True) | (Bool4::True, Bool4::False) => BotOr::Bot,
            (Bool4::Top, x) | (x, Bool4::Top) => BotOr::Val(x),
            (Bool4::False, Bool4::False) => BotOr::Val(Bool4::False),
            (Bool4::True, Bool4::True) => BotOr::Val(Bool4::True),
        }
    }

    fn normalize(&self) -> (r: BotOr<Self>) {
        BotOr::Val(*self)
    }
}

impl Refine for Bool4 {
    type F = Bool4;

    fn to_channel(&self) -> (f: BotOr<Bool4>) {
        BotOr::Val(*self)
    }

    fn refine(&self, f: &Bool4) -> (r: BotOr<Self>) {
        meet_normalize(self, f)
    }
}

proof fn lemma_and_bottom(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.and_spec(c),
        a == Bool4::Bottom || c == Bool4::Bottom,
    ensures
        a.and_exact_spec(c, r),
{
    assert(r == Bool4::Bottom);
    reveal(Bool4::and_exact_spec);
    assert(a.and_exact_spec(c, r));
}

proof fn lemma_and_false_left(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.and_spec(c),
        a == Bool4::False,
        c != Bool4::Bottom,
    ensures
        a.and_exact_spec(c, r),
{
    assert(r == Bool4::False);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x && y) by {
        let y = c == Bool4::True;
        assert(a.has(false) && c.has(y) && b == (false && y));
    }
    reveal(Bool4::and_exact_spec);
    assert(a.and_exact_spec(c, r));
}

proof fn lemma_and_false_right(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.and_spec(c),
        c == Bool4::False,
        a == Bool4::True || a == Bool4::Top,
    ensures
        a.and_exact_spec(c, r),
{
    assert(r == Bool4::False);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x && y) by {
        let x = a == Bool4::True;
        assert(a.has(x) && c.has(false) && b == (x && false));
    }
    reveal(Bool4::and_exact_spec);
    assert(a.and_exact_spec(c, r));
}

proof fn lemma_and_true(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.and_spec(c),
        a == Bool4::True && c == Bool4::True,
    ensures
        a.and_exact_spec(c, r),
{
    assert(r == Bool4::True);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x && y) by {
        assert(a.has(true) && c.has(true) && b == (true && true));
    }
    reveal(Bool4::and_exact_spec);
    assert(a.and_exact_spec(c, r));
}

proof fn lemma_and_top(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.and_spec(c),
        (a == Bool4::True && c == Bool4::Top) || (a == Bool4::Top && c == Bool4::True) || (a
            == Bool4::Top && c == Bool4::Top),
    ensures
        a.and_exact_spec(c, r),
{
    assert(r == Bool4::Top);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x && y) by {
        if a == Bool4::True {
            assert(a.has(true) && c.has(b) && b == (true && b));
        } else {
            assert(a.has(b) && c.has(true) && b == (b && true));
        }
    }
    reveal(Bool4::and_exact_spec);
    assert(a.and_exact_spec(c, r));
}

proof fn lemma_and_exact(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.and_spec(c),
    ensures
        a.and_exact_spec(c, r),
{
    match (a, c) {
        (Bool4::Bottom, _) | (_, Bool4::Bottom) => {
            lemma_and_bottom(a, c, r);
        },
        (Bool4::False, Bool4::False) => {
            lemma_and_false_left(a, c, r);
        },
        (Bool4::False, Bool4::True) => {
            lemma_and_false_left(a, c, r);
        },
        (Bool4::False, Bool4::Top) => {
            lemma_and_false_left(a, c, r);
        },
        (Bool4::True, Bool4::False) => {
            lemma_and_false_right(a, c, r);
        },
        (Bool4::Top, Bool4::False) => {
            lemma_and_false_right(a, c, r);
        },
        (Bool4::True, Bool4::True) => {
            lemma_and_true(a, c, r);
        },
        (Bool4::True, Bool4::Top) => {
            lemma_and_top(a, c, r);
        },
        (Bool4::Top, Bool4::True) => {
            lemma_and_top(a, c, r);
        },
        (Bool4::Top, Bool4::Top) => {
            lemma_and_top(a, c, r);
        },
    }
}

proof fn lemma_or_sound(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.or_spec(c),
    ensures
        forall|x: bool, y: bool|
            (#[trigger] a.has(x)) && (#[trigger] c.has(y)) ==> r.has(x || y),
{
    match (a, c) {
        (Bool4::Bottom, _) | (_, Bool4::Bottom) => {
            assert(r == Bool4::Bottom);
        },
        (Bool4::True, Bool4::False | Bool4::True | Bool4::Top) | (Bool4::False | Bool4::Top, Bool4::True) => {
            assert(r == Bool4::True);
        },
        (Bool4::False, Bool4::False) => {
            assert(r == Bool4::False);
        },
        (Bool4::False, Bool4::Top) | (Bool4::Top, Bool4::False) | (Bool4::Top, Bool4::Top) => {
            assert(r == Bool4::Top);
        },
    }
}

proof fn lemma_or_bottom(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.or_spec(c),
        a == Bool4::Bottom || c == Bool4::Bottom,
    ensures
        a.or_exact_spec(c, r),
{
    assert(r == Bool4::Bottom);
    reveal(Bool4::or_exact_spec);
    assert(a.or_exact_spec(c, r));
}

proof fn lemma_or_false(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.or_spec(c),
        a == Bool4::False && c == Bool4::False,
    ensures
        a.or_exact_spec(c, r),
{
    assert(r == Bool4::False);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x || y) by {
        assert(a.has(false) && c.has(false) && b == (false || false));
    }
    reveal(Bool4::or_exact_spec);
    assert(a.or_exact_spec(c, r));
}

proof fn lemma_or_true_left(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.or_spec(c),
        a == Bool4::True,
        c != Bool4::Bottom,
    ensures
        a.or_exact_spec(c, r),
{
    assert(r == Bool4::True);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x || y) by {
        let y = c == Bool4::True;
        assert(a.has(true) && c.has(y) && b == (true || y));
    }
    reveal(Bool4::or_exact_spec);
    assert(a.or_exact_spec(c, r));
}

proof fn lemma_or_true_right(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.or_spec(c),
        c == Bool4::True,
        a == Bool4::False || a == Bool4::Top,
    ensures
        a.or_exact_spec(c, r),
{
    assert(r == Bool4::True);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x || y) by {
        let x = a == Bool4::Top;
        assert(a.has(x) && c.has(true) && b == (x || true));
    }
    reveal(Bool4::or_exact_spec);
    assert(a.or_exact_spec(c, r));
}

proof fn lemma_or_mixed(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.or_spec(c),
        (a == Bool4::False && c == Bool4::Top) || (a == Bool4::Top && c == Bool4::False) || (a
            == Bool4::Top && c == Bool4::Top),
    ensures
        a.or_exact_spec(c, r),
{
    assert(r == Bool4::Top);
    assert forall|b: bool|
        #[trigger] r.has(b) implies exists|x: bool, y: bool|
            a.has(x) && c.has(y) && b == (x || y) by {
        if c == Bool4::False {
            assert(a.has(b) && c.has(false) && b == (b || false));
        } else {
            assert(a.has(false) && c.has(b) && b == (false || b));
        }
    }
    reveal(Bool4::or_exact_spec);
    assert(a.or_exact_spec(c, r));
}

proof fn lemma_or_exact(a: Bool4, c: Bool4, r: Bool4)
    requires
        r == a.or_spec(c),
    ensures
        a.or_exact_spec(c, r),
{
    if a == Bool4::Bottom || c == Bool4::Bottom {
        lemma_or_bottom(a, c, r);
    } else if a == Bool4::False && c == Bool4::False {
        lemma_or_false(a, c, r);
    } else if a == Bool4::True {
        lemma_or_true_left(a, c, r);
    } else if c == Bool4::True {
        lemma_or_true_right(a, c, r);
    } else {
        lemma_or_mixed(a, c, r);
    }
}

pub proof fn join_idempotent(a: Bool4)
    ensures
        a.join_spec(a) == a,
{
}

pub proof fn join_comm(a: Bool4, b: Bool4)
    ensures
        a.join_spec(b) == b.join_spec(a),
{
}

pub proof fn join_assoc(a: Bool4, b: Bool4, c: Bool4)
    ensures
        a.join_spec(b).join_spec(c) == a.join_spec(b.join_spec(c)),
{
}

pub proof fn join_bottom(a: Bool4)
    ensures
        a.join_spec(Bool4::Bottom) == a,
{
}

pub proof fn join_top(a: Bool4)
    ensures
        a.join_spec(Bool4::Top) == Bool4::Top,
{
}

pub proof fn meet_idempotent(a: Bool4)
    ensures
        a.meet_spec(a) == a,
{
}

pub proof fn meet_comm(a: Bool4, b: Bool4)
    ensures
        a.meet_spec(b) == b.meet_spec(a),
{
}

pub proof fn meet_assoc(a: Bool4, b: Bool4, c: Bool4)
    ensures
        a.meet_spec(b).meet_spec(c) == a.meet_spec(b.meet_spec(c)),
{
}

pub proof fn meet_top(a: Bool4)
    ensures
        a.meet_spec(Bool4::Top) == a,
{
}

pub proof fn meet_bottom(a: Bool4)
    ensures
        a.meet_spec(Bool4::Bottom) == Bool4::Bottom,
{
}

proof fn lemma_refines_cases(a: Bool4, b: Bool4)
    requires
        a.refines(b),
    ensures
        a == Bool4::Bottom || (a == Bool4::False && (b == Bool4::False || b == Bool4::Top)) || (a
            == Bool4::True && (b == Bool4::True || b == Bool4::Top)) || (a == Bool4::Top && b
            == Bool4::Top),
{
    match (a, b) {
        (Bool4::Bottom, _) => {},
        (Bool4::False, Bool4::False) | (Bool4::False, Bool4::Top) => {},
        (Bool4::True, Bool4::True) | (Bool4::True, Bool4::Top) => {},
        (Bool4::Top, Bool4::Top) => {},
        (Bool4::False, Bool4::Bottom) | (Bool4::False, Bool4::True) => {
            assert(a.has(false) && !b.has(false));
        },
        (Bool4::True, Bool4::Bottom) | (Bool4::True, Bool4::False) => {
            assert(a.has(true) && !b.has(true));
        },
        (Bool4::Top, Bool4::Bottom) | (Bool4::Top, Bool4::False) => {
            assert(a.has(true) && !b.has(true));
        },
        (Bool4::Top, Bool4::True) => {
            assert(a.has(false) && !b.has(false));
        },
    }
}

pub proof fn not_monotone(a: Bool4, b: Bool4)
    requires
        a.refines(b),
    ensures
        a.not_spec().refines(b.not_spec()),
{
    lemma_refines_cases(a, b);
}

pub proof fn and_monotone(a: Bool4, b: Bool4, c: Bool4)
    requires
        a.refines(b),
    ensures
        a.and_spec(c).refines(b.and_spec(c)),
{
    lemma_refines_cases(a, b);
}

pub proof fn or_monotone(a: Bool4, b: Bool4, c: Bool4)
    requires
        a.refines(b),
    ensures
        a.or_spec(c).refines(b.or_spec(c)),
{
    lemma_refines_cases(a, b);
}

} // verus!
