// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Configurable literal model with macro-generated minimal enums.

use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::Zero;
use ordered_float::OrderedFloat;

use crate::lit_model::{LitModel, LitOpDesc, LitSortDesc};
use crate::literal::LitVal;

// ---------------------------------------------------------------------------
// Macro: generate a LitVal enum with Bool + selected variants
// ---------------------------------------------------------------------------

macro_rules! define_litval {
    ($name:ident, [ $( $Var:ident($Ty:ty) => $sort:literal ),* $(,)? ]) => {
        #[derive(Clone, PartialEq, Eq, Hash)]
        pub enum $name { Bool(bool), $( $Var($Ty), )* }
        impl LitVal for $name {}
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self { Self::Bool(v) => write!(f, "{v}"), $( Self::$Var(v) => write!(f, "{v:?}"), )* }
            }
        }
        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self { Self::Bool(v) => write!(f, "{v}"), $( Self::$Var(v) => write!(f, "{v}"), )* }
            }
        }
        impl $name {
            pub fn sort_of(&self) -> &'static str {
                match self { Self::Bool(_) => "bool", $( Self::$Var(_) => $sort, )* }
            }
            pub fn is_truthy(&self) -> bool { matches!(self, Self::Bool(true)) }
        }
    };
}

define_litval!(MachineLit, [
    I64(i64) => "i64", U64(u64) => "u64", F64(OrderedFloat<f64>) => "f64",
    Usize(usize) => "usize", Str(String) => "String",
]);
define_litval!(BignumLit, [
    IBig(BigInt) => "IBig", UBig(BigUint) => "UBig", RBig(BigRational) => "RBig",
]);
define_litval!(AllLit, [
    I64(i64) => "i64", U64(u64) => "u64", F64(OrderedFloat<f64>) => "f64",
    Usize(usize) => "usize", Str(String) => "String",
    IBig(BigInt) => "IBig", UBig(BigUint) => "UBig", RBig(BigRational) => "RBig",
]);

// ---------------------------------------------------------------------------
// Type groups and selection
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeGroup {
    Machine,
    Bignum,
}

impl TypeGroup {
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "machine" => Some(Self::Machine),
            "bignum" => Some(Self::Bignum),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitValChoice {
    Machine,
    Bignum,
    All,
}

pub fn choose_litval(groups: &[TypeGroup]) -> LitValChoice {
    let m = groups.contains(&TypeGroup::Machine);
    let b = groups.contains(&TypeGroup::Bignum);
    match (m, b) {
        (true, false) => LitValChoice::Machine,
        (false, true) | (false, false) => LitValChoice::Bignum,
        (true, true) => LitValChoice::All,
    }
}

// ---------------------------------------------------------------------------
// Op-generation macros (parameterized by enum name)
// ---------------------------------------------------------------------------

macro_rules! bool_ops {
    ($E:ident) => {
        &[
            LitOpDesc {
                name: "and",
                arg_sorts: &["bool", "bool"],
                ret_sort: "bool",
                eval: |a| match (a[0], a[1]) {
                    ($E::Bool(x), $E::Bool(y)) => $E::Bool(*x && *y),
                    _ => panic!(),
                },
            },
            LitOpDesc {
                name: "or",
                arg_sorts: &["bool", "bool"],
                ret_sort: "bool",
                eval: |a| match (a[0], a[1]) {
                    ($E::Bool(x), $E::Bool(y)) => $E::Bool(*x || *y),
                    _ => panic!(),
                },
            },
            LitOpDesc {
                name: "not",
                arg_sorts: &["bool"],
                ret_sort: "bool",
                eval: |a| match a[0] {
                    $E::Bool(x) => $E::Bool(!x),
                    _ => panic!(),
                },
            },
            LitOpDesc {
                name: "bool::if",
                arg_sorts: &["bool", "bool", "bool"],
                ret_sort: "bool",
                eval: |a| match a[0] {
                    $E::Bool(c) => {
                        if *c {
                            a[1].clone()
                        } else {
                            a[2].clone()
                        }
                    }
                    _ => panic!(),
                },
            },
        ]
    };
}

macro_rules! checked_binop {
    ($E:ident,$V:ident,$n:expr,$s:expr,$m:ident) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &[$s, $s],
            ret_sort: $s,
            eval: |a| match (a[0], a[1]) {
                ($E::$V(x), $E::$V(y)) => $E::$V(x.$m(*y).expect($n)),
                _ => panic!(),
            },
        }
    };
}
macro_rules! wrapping_binop {
    ($E:ident,$V:ident,$n:expr,$s:expr,$m:ident) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &[$s, $s],
            ret_sort: $s,
            eval: |a| match (a[0], a[1]) {
                ($E::$V(x), $E::$V(y)) => $E::$V(x.$m(*y)),
                _ => panic!(),
            },
        }
    };
}
macro_rules! saturating_binop {
    ($E:ident,$V:ident,$n:expr,$s:expr,$m:ident) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &[$s, $s],
            ret_sort: $s,
            eval: |a| match (a[0], a[1]) {
                ($E::$V(x), $E::$V(y)) => $E::$V(x.$m(*y)),
                _ => panic!(),
            },
        }
    };
}
macro_rules! cmp_op { ($E:ident,$V:ident,$n:expr,$s:expr,$op:tt) => {
    LitOpDesc { name: $n, arg_sorts: &[$s,$s], ret_sort: "bool",
        eval: |a| match (a[0],a[1]) { ($E::$V(x),$E::$V(y)) => $E::Bool(x $op y), _=>panic!() } }
};}
macro_rules! if_op {
    ($E:ident,$n:expr,$s:expr) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &["bool", $s, $s],
            ret_sort: $s,
            eval: |a| match a[0] {
                $E::Bool(c) => {
                    if *c {
                        a[1].clone()
                    } else {
                        a[2].clone()
                    }
                }
                _ => panic!(),
            },
        }
    };
}
macro_rules! min_op {
    ($E:ident,$V:ident,$n:expr,$s:expr) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &[$s, $s],
            ret_sort: $s,
            eval: |a| match (a[0], a[1]) {
                ($E::$V(x), $E::$V(y)) => $E::$V(*x.min(y)),
                _ => panic!(),
            },
        }
    };
}
macro_rules! max_op {
    ($E:ident,$V:ident,$n:expr,$s:expr) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &[$s, $s],
            ret_sort: $s,
            eval: |a| match (a[0], a[1]) {
                ($E::$V(x), $E::$V(y)) => $E::$V(*x.max(y)),
                _ => panic!(),
            },
        }
    };
}

macro_rules! signed_int_ops { ($E:ident, $V:ident, $s:expr) => { &[
    checked_binop!($E,$V,concat!($s,"::+"),$s,checked_add),
    checked_binop!($E,$V,concat!($s,"::-"),$s,checked_sub),
    checked_binop!($E,$V,concat!($s,"::*"),$s,checked_mul),
    checked_binop!($E,$V,concat!($s,"::/"),$s,checked_div),
    checked_binop!($E,$V,concat!($s,"::%"),$s,checked_rem),
    LitOpDesc { name: concat!($s,"::neg"), arg_sorts: &[$s], ret_sort: $s,
        eval: |a| match a[0] { $E::$V(x) => $E::$V(x.checked_neg().expect(concat!($s,"::neg overflow"))), _=>panic!() } },
    LitOpDesc { name: concat!($s,"::abs"), arg_sorts: &[$s], ret_sort: $s,
        eval: |a| match a[0] { $E::$V(x) => $E::$V(x.checked_abs().expect(concat!($s,"::abs overflow"))), _=>panic!() } },
    wrapping_binop!($E,$V,concat!($s,"::wrapping_add"),$s,wrapping_add),
    wrapping_binop!($E,$V,concat!($s,"::wrapping_sub"),$s,wrapping_sub),
    wrapping_binop!($E,$V,concat!($s,"::wrapping_mul"),$s,wrapping_mul),
    LitOpDesc { name: concat!($s,"::wrapping_neg"), arg_sorts: &[$s], ret_sort: $s,
        eval: |a| match a[0] { $E::$V(x) => $E::$V(x.wrapping_neg()), _=>panic!() } },
    LitOpDesc { name: concat!($s,"::wrapping_abs"), arg_sorts: &[$s], ret_sort: $s,
        eval: |a| match a[0] { $E::$V(x) => $E::$V(x.wrapping_abs()), _=>panic!() } },
    saturating_binop!($E,$V,concat!($s,"::saturating_add"),$s,saturating_add),
    saturating_binop!($E,$V,concat!($s,"::saturating_sub"),$s,saturating_sub),
    saturating_binop!($E,$V,concat!($s,"::saturating_mul"),$s,saturating_mul),
    LitOpDesc { name: concat!($s,"::saturating_neg"), arg_sorts: &[$s], ret_sort: $s,
        eval: |a| match a[0] { $E::$V(x) => $E::$V(x.saturating_neg()), _=>panic!() } },
    LitOpDesc { name: concat!($s,"::saturating_abs"), arg_sorts: &[$s], ret_sort: $s,
        eval: |a| match a[0] { $E::$V(x) => $E::$V(x.saturating_abs()), _=>panic!() } },
    min_op!($E,$V,concat!($s,"::min"),$s), max_op!($E,$V,concat!($s,"::max"),$s),
    cmp_op!($E,$V,concat!($s,"::<"),$s,<), cmp_op!($E,$V,concat!($s,"::<="),$s,<=),
    cmp_op!($E,$V,concat!($s,"::>"),$s,>), cmp_op!($E,$V,concat!($s,"::>="),$s,>=),
    cmp_op!($E,$V,concat!($s,"::=="),$s,==), cmp_op!($E,$V,concat!($s,"::!="),$s,!=),
    if_op!($E,concat!($s,"::if"),$s),
]};}

macro_rules! unsigned_int_ops { ($E:ident, $V:ident, $s:expr) => { &[
    checked_binop!($E,$V,concat!($s,"::+"),$s,checked_add),
    checked_binop!($E,$V,concat!($s,"::-"),$s,checked_sub),
    checked_binop!($E,$V,concat!($s,"::*"),$s,checked_mul),
    checked_binop!($E,$V,concat!($s,"::/"),$s,checked_div),
    checked_binop!($E,$V,concat!($s,"::%"),$s,checked_rem),
    wrapping_binop!($E,$V,concat!($s,"::wrapping_add"),$s,wrapping_add),
    wrapping_binop!($E,$V,concat!($s,"::wrapping_sub"),$s,wrapping_sub),
    wrapping_binop!($E,$V,concat!($s,"::wrapping_mul"),$s,wrapping_mul),
    saturating_binop!($E,$V,concat!($s,"::saturating_add"),$s,saturating_add),
    saturating_binop!($E,$V,concat!($s,"::saturating_sub"),$s,saturating_sub),
    saturating_binop!($E,$V,concat!($s,"::saturating_mul"),$s,saturating_mul),
    min_op!($E,$V,concat!($s,"::min"),$s), max_op!($E,$V,concat!($s,"::max"),$s),
    cmp_op!($E,$V,concat!($s,"::<"),$s,<), cmp_op!($E,$V,concat!($s,"::<="),$s,<=),
    cmp_op!($E,$V,concat!($s,"::>"),$s,>), cmp_op!($E,$V,concat!($s,"::>="),$s,>=),
    cmp_op!($E,$V,concat!($s,"::=="),$s,==), cmp_op!($E,$V,concat!($s,"::!="),$s,!=),
    if_op!($E,concat!($s,"::if"),$s),
]};}

macro_rules! f64_ops { ($E:ident) => { &[
    LitOpDesc { name: "f64::+", arg_sorts: &["f64","f64"], ret_sort: "f64",
        eval: |a| match (a[0],a[1]) { ($E::F64(x),$E::F64(y)) => $E::F64(OrderedFloat(*x.as_ref()+*y.as_ref())), _=>panic!() } },
    LitOpDesc { name: "f64::-", arg_sorts: &["f64","f64"], ret_sort: "f64",
        eval: |a| match (a[0],a[1]) { ($E::F64(x),$E::F64(y)) => $E::F64(OrderedFloat(*x.as_ref()-*y.as_ref())), _=>panic!() } },
    LitOpDesc { name: "f64::*", arg_sorts: &["f64","f64"], ret_sort: "f64",
        eval: |a| match (a[0],a[1]) { ($E::F64(x),$E::F64(y)) => $E::F64(OrderedFloat(*x.as_ref()*(*y.as_ref()))), _=>panic!() } },
    LitOpDesc { name: "f64::/", arg_sorts: &["f64","f64"], ret_sort: "f64",
        eval: |a| match (a[0],a[1]) { ($E::F64(x),$E::F64(y)) => $E::F64(OrderedFloat(*x.as_ref()/(*y.as_ref()))), _=>panic!() } },
    LitOpDesc { name: "f64::neg", arg_sorts: &["f64"], ret_sort: "f64",
        eval: |a| match a[0] { $E::F64(x) => $E::F64(OrderedFloat(-*x.as_ref())), _=>panic!() } },
    LitOpDesc { name: "f64::abs", arg_sorts: &["f64"], ret_sort: "f64",
        eval: |a| match a[0] { $E::F64(x) => $E::F64(OrderedFloat(x.as_ref().abs())), _=>panic!() } },
    LitOpDesc { name: "f64::min", arg_sorts: &["f64","f64"], ret_sort: "f64",
        eval: |a| match (a[0],a[1]) { ($E::F64(x),$E::F64(y)) => $E::F64(*x.min(y)), _=>panic!() } },
    LitOpDesc { name: "f64::max", arg_sorts: &["f64","f64"], ret_sort: "f64",
        eval: |a| match (a[0],a[1]) { ($E::F64(x),$E::F64(y)) => $E::F64(*x.max(y)), _=>panic!() } },
    cmp_op!($E,F64,"f64::<","f64",<), cmp_op!($E,F64,"f64::<=","f64",<=),
    cmp_op!($E,F64,"f64::>","f64",>), cmp_op!($E,F64,"f64::>=","f64",>=),
    cmp_op!($E,F64,"f64::==","f64",==), cmp_op!($E,F64,"f64::!=","f64",!=),
    if_op!($E,"f64::if","f64"),
]};}

macro_rules! string_ops { ($E:ident) => { &[
    LitOpDesc { name: "String::concat", arg_sorts: &["String","String"], ret_sort: "String",
        eval: |a| match (a[0],a[1]) { ($E::Str(x),$E::Str(y)) => { let mut r=x.clone(); r.push_str(y); $E::Str(r) } _=>panic!() } },
    LitOpDesc { name: "String::contains", arg_sorts: &["String","String"], ret_sort: "bool",
        eval: |a| match (a[0],a[1]) { ($E::Str(x),$E::Str(y)) => $E::Bool(x.contains(y.as_str())), _=>panic!() } },
    LitOpDesc { name: "String::replace", arg_sorts: &["String","String","String"], ret_sort: "String",
        eval: |a| match (a[0],a[1],a[2]) { ($E::Str(s),$E::Str(f),$E::Str(t)) => $E::Str(s.replacen(f.as_str(),t.as_str(),1)), _=>panic!() } },
    cmp_op!($E,Str,"String::==","String",==), cmp_op!($E,Str,"String::!=","String",!=),
    if_op!($E,"String::if","String"),
    LitOpDesc { name: "String::len", arg_sorts: &["String"], ret_sort: "usize",
        eval: |a| match a[0] { $E::Str(s) => $E::Usize(s.len()), _=>panic!() } },
    LitOpDesc { name: "String::substr", arg_sorts: &["String","usize","usize"], ret_sort: "String",
        eval: |a| match (a[0],a[1],a[2]) {
            ($E::Str(s),$E::Usize(st),$E::Usize(ln)) => $E::Str(s.get(*st..(*st+*ln).min(s.len())).unwrap_or("").to_owned()),
            _=>panic!(),
        } },
    LitOpDesc { name: "String::at", arg_sorts: &["String","usize"], ret_sort: "String",
        eval: |a| match (a[0],a[1]) { ($E::Str(s),$E::Usize(i)) => $E::Str(s.get(*i..*i+1).unwrap_or("").to_owned()), _=>panic!() } },
]};}

// ---------------------------------------------------------------------------
// Parsers
// ---------------------------------------------------------------------------

fn parse_str(s: &str) -> Option<String> {
    Some(s.strip_prefix('"')?.strip_suffix('"')?.to_owned())
}
fn parse_ibig(s: &str) -> Option<BigInt> {
    s.parse().ok()
}
fn parse_ubig(s: &str) -> Option<BigUint> {
    s.parse().ok()
}
fn parse_rbig(s: &str) -> Option<BigRational> {
    let (n, d) = s.split_once('/')?;
    let num: BigInt = n.parse().ok()?;
    let den: BigInt = d.parse().ok()?;
    if den.is_zero() {
        return None;
    }
    Some(BigRational::new(num, den))
}

// ---------------------------------------------------------------------------
// Bignum op macros (use operator overloading, not checked_ methods)
// ---------------------------------------------------------------------------

macro_rules! bignum_binop { ($E:ident,$V:ident,$n:expr,$s:expr,$op:tt) => {
    LitOpDesc { name: $n, arg_sorts: &[$s,$s], ret_sort: $s,
        eval: |a| match (a[0],a[1]) { ($E::$V(x),$E::$V(y)) => $E::$V(x $op y), _=>panic!() } }
};}
macro_rules! bignum_min {
    ($E:ident,$V:ident,$n:expr,$s:expr) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &[$s, $s],
            ret_sort: $s,
            eval: |a| match (a[0], a[1]) {
                ($E::$V(x), $E::$V(y)) => $E::$V(x.min(y).clone()),
                _ => panic!(),
            },
        }
    };
}
macro_rules! bignum_max {
    ($E:ident,$V:ident,$n:expr,$s:expr) => {
        LitOpDesc {
            name: $n,
            arg_sorts: &[$s, $s],
            ret_sort: $s,
            eval: |a| match (a[0], a[1]) {
                ($E::$V(x), $E::$V(y)) => $E::$V(x.max(y).clone()),
                _ => panic!(),
            },
        }
    };
}

macro_rules! ibig_ops { ($E:ident) => { &[
    bignum_binop!($E,IBig,"IBig::+","IBig",+), bignum_binop!($E,IBig,"IBig::-","IBig",-),
    bignum_binop!($E,IBig,"IBig::*","IBig",*), bignum_binop!($E,IBig,"IBig::/","IBig",/),
    bignum_binop!($E,IBig,"IBig::%","IBig",%),
    LitOpDesc { name: "IBig::neg", arg_sorts: &["IBig"], ret_sort: "IBig",
        eval: |a| match a[0] { $E::IBig(x) => $E::IBig(-x), _=>panic!() } },
    LitOpDesc { name: "IBig::abs", arg_sorts: &["IBig"], ret_sort: "IBig",
        eval: |a| match a[0] { $E::IBig(x) => $E::IBig(if *x<BigInt::zero() {-x} else {x.clone()}), _=>panic!() } },
    bignum_min!($E,IBig,"IBig::min","IBig"), bignum_max!($E,IBig,"IBig::max","IBig"),
    cmp_op!($E,IBig,"IBig::<","IBig",<), cmp_op!($E,IBig,"IBig::<=","IBig",<=),
    cmp_op!($E,IBig,"IBig::>","IBig",>), cmp_op!($E,IBig,"IBig::>=","IBig",>=),
    cmp_op!($E,IBig,"IBig::==","IBig",==), cmp_op!($E,IBig,"IBig::!=","IBig",!=),
    if_op!($E,"IBig::if","IBig"),
]};}
macro_rules! ubig_ops { ($E:ident) => { &[
    bignum_binop!($E,UBig,"UBig::+","UBig",+), bignum_binop!($E,UBig,"UBig::-","UBig",-),
    bignum_binop!($E,UBig,"UBig::*","UBig",*), bignum_binop!($E,UBig,"UBig::/","UBig",/),
    bignum_binop!($E,UBig,"UBig::%","UBig",%),
    bignum_min!($E,UBig,"UBig::min","UBig"), bignum_max!($E,UBig,"UBig::max","UBig"),
    cmp_op!($E,UBig,"UBig::<","UBig",<), cmp_op!($E,UBig,"UBig::<=","UBig",<=),
    cmp_op!($E,UBig,"UBig::>","UBig",>), cmp_op!($E,UBig,"UBig::>=","UBig",>=),
    cmp_op!($E,UBig,"UBig::==","UBig",==), cmp_op!($E,UBig,"UBig::!=","UBig",!=),
    if_op!($E,"UBig::if","UBig"),
]};}
macro_rules! rbig_ops { ($E:ident) => { &[
    bignum_binop!($E,RBig,"RBig::+","RBig",+), bignum_binop!($E,RBig,"RBig::-","RBig",-),
    bignum_binop!($E,RBig,"RBig::*","RBig",*), bignum_binop!($E,RBig,"RBig::/","RBig",/),
    LitOpDesc { name: "RBig::neg", arg_sorts: &["RBig"], ret_sort: "RBig",
        eval: |a| match a[0] { $E::RBig(x) => $E::RBig(-x), _=>panic!() } },
    LitOpDesc { name: "RBig::abs", arg_sorts: &["RBig"], ret_sort: "RBig",
        eval: |a| match a[0] { $E::RBig(x) => { let v=x.clone(); $E::RBig(if v<BigRational::zero() {-v} else {v}) } _=>panic!() } },
    bignum_min!($E,RBig,"RBig::min","RBig"), bignum_max!($E,RBig,"RBig::max","RBig"),
    cmp_op!($E,RBig,"RBig::<","RBig",<), cmp_op!($E,RBig,"RBig::<=","RBig",<=),
    cmp_op!($E,RBig,"RBig::>","RBig",>), cmp_op!($E,RBig,"RBig::>=","RBig",>=),
    cmp_op!($E,RBig,"RBig::==","RBig",==), cmp_op!($E,RBig,"RBig::!=","RBig",!=),
    if_op!($E,"RBig::if","RBig"),
]};}

// ---------------------------------------------------------------------------
// MachineModel
// ---------------------------------------------------------------------------

pub struct MachineModel;
const MACHINE_SORTS: &[LitSortDesc<MachineLit>] = &[
    LitSortDesc {
        name: "bool",
        parse: |s| match s {
            "true" => Some(MachineLit::Bool(true)),
            "false" => Some(MachineLit::Bool(false)),
            _ => None,
        },
    },
    LitSortDesc {
        name: "i64",
        parse: |s| s.parse().ok().map(MachineLit::I64),
    },
    LitSortDesc {
        name: "u64",
        parse: |s| s.parse().ok().map(MachineLit::U64),
    },
    LitSortDesc {
        name: "f64",
        parse: |s| {
            s.parse::<f64>()
                .ok()
                .map(|v| MachineLit::F64(OrderedFloat(v)))
        },
    },
    LitSortDesc {
        name: "usize",
        parse: |s| s.parse().ok().map(MachineLit::Usize),
    },
    LitSortDesc {
        name: "String",
        parse: |s| parse_str(s).map(MachineLit::Str),
    },
];
impl LitModel for MachineModel {
    type Value = MachineLit;
    fn sorts(&self) -> &[LitSortDesc<MachineLit>] {
        MACHINE_SORTS
    }
    fn ops(&self) -> &[LitOpDesc<MachineLit>] {
        use std::sync::LazyLock;
        static OPS: LazyLock<Vec<LitOpDesc<MachineLit>>> = LazyLock::new(|| {
            let mut v = Vec::new();
            v.extend_from_slice(bool_ops!(MachineLit));
            v.extend_from_slice(signed_int_ops!(MachineLit, I64, "i64"));
            v.extend_from_slice(unsigned_int_ops!(MachineLit, U64, "u64"));
            v.extend_from_slice(unsigned_int_ops!(MachineLit, Usize, "usize"));
            v.extend_from_slice(f64_ops!(MachineLit));
            v.extend_from_slice(string_ops!(MachineLit));
            v
        });
        &OPS
    }
    fn sort_of(val: &MachineLit) -> &'static str {
        val.sort_of()
    }
    fn is_truthy(val: &MachineLit) -> bool {
        val.is_truthy()
    }
}

// ---------------------------------------------------------------------------
// BignumModel
// ---------------------------------------------------------------------------

pub struct BignumModel;
const BIGNUM_SORTS: &[LitSortDesc<BignumLit>] = &[
    LitSortDesc {
        name: "bool",
        parse: |s| match s {
            "true" => Some(BignumLit::Bool(true)),
            "false" => Some(BignumLit::Bool(false)),
            _ => None,
        },
    },
    LitSortDesc {
        name: "IBig",
        parse: |s| parse_ibig(s).map(BignumLit::IBig),
    },
    LitSortDesc {
        name: "UBig",
        parse: |s| parse_ubig(s).map(BignumLit::UBig),
    },
    LitSortDesc {
        name: "RBig",
        parse: |s| parse_rbig(s).map(BignumLit::RBig),
    },
];
impl LitModel for BignumModel {
    type Value = BignumLit;
    fn sorts(&self) -> &[LitSortDesc<BignumLit>] {
        BIGNUM_SORTS
    }
    fn ops(&self) -> &[LitOpDesc<BignumLit>] {
        use std::sync::LazyLock;
        static OPS: LazyLock<Vec<LitOpDesc<BignumLit>>> = LazyLock::new(|| {
            let mut v = Vec::new();
            v.extend_from_slice(bool_ops!(BignumLit));
            v.extend_from_slice(ibig_ops!(BignumLit));
            v.extend_from_slice(ubig_ops!(BignumLit));
            v.extend_from_slice(rbig_ops!(BignumLit));
            v
        });
        &OPS
    }
    fn sort_of(val: &BignumLit) -> &'static str {
        val.sort_of()
    }
    fn is_truthy(val: &BignumLit) -> bool {
        val.is_truthy()
    }
}

// ---------------------------------------------------------------------------
// AllModel
// ---------------------------------------------------------------------------

pub struct AllModel;
const ALL_SORTS: &[LitSortDesc<AllLit>] = &[
    LitSortDesc {
        name: "bool",
        parse: |s| match s {
            "true" => Some(AllLit::Bool(true)),
            "false" => Some(AllLit::Bool(false)),
            _ => None,
        },
    },
    LitSortDesc {
        name: "i64",
        parse: |s| s.parse().ok().map(AllLit::I64),
    },
    LitSortDesc {
        name: "u64",
        parse: |s| s.parse().ok().map(AllLit::U64),
    },
    LitSortDesc {
        name: "f64",
        parse: |s| s.parse::<f64>().ok().map(|v| AllLit::F64(OrderedFloat(v))),
    },
    LitSortDesc {
        name: "usize",
        parse: |s| s.parse().ok().map(AllLit::Usize),
    },
    LitSortDesc {
        name: "String",
        parse: |s| parse_str(s).map(AllLit::Str),
    },
    LitSortDesc {
        name: "IBig",
        parse: |s| parse_ibig(s).map(AllLit::IBig),
    },
    LitSortDesc {
        name: "UBig",
        parse: |s| parse_ubig(s).map(AllLit::UBig),
    },
    LitSortDesc {
        name: "RBig",
        parse: |s| parse_rbig(s).map(AllLit::RBig),
    },
];
impl LitModel for AllModel {
    type Value = AllLit;
    fn sorts(&self) -> &[LitSortDesc<AllLit>] {
        ALL_SORTS
    }
    fn ops(&self) -> &[LitOpDesc<AllLit>] {
        use std::sync::LazyLock;
        static OPS: LazyLock<Vec<LitOpDesc<AllLit>>> = LazyLock::new(|| {
            let mut v = Vec::new();
            v.extend_from_slice(bool_ops!(AllLit));
            v.extend_from_slice(signed_int_ops!(AllLit, I64, "i64"));
            v.extend_from_slice(unsigned_int_ops!(AllLit, U64, "u64"));
            v.extend_from_slice(unsigned_int_ops!(AllLit, Usize, "usize"));
            v.extend_from_slice(f64_ops!(AllLit));
            v.extend_from_slice(string_ops!(AllLit));
            v.extend_from_slice(ibig_ops!(AllLit));
            v.extend_from_slice(ubig_ops!(AllLit));
            v.extend_from_slice(rbig_ops!(AllLit));
            v
        });
        &OPS
    }
    fn sort_of(val: &AllLit) -> &'static str {
        val.sort_of()
    }
    fn is_truthy(val: &AllLit) -> bool {
        val.is_truthy()
    }
}
