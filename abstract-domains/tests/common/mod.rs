// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Brute-force soundness and optimality checks for u8 abstract operations.
//!
//! The Verus proofs establish soundness for every width; these checks exercise
//! the executable code, whose contracts are erased at runtime, and measure
//! precision, which no contract states. Each test file includes this module
//! with `mod common;`.
#![allow(dead_code)]

use semi_persistent_abstract_domains::bool4::Bool4;

/// Concretization of an abstract u8 value as a membership table.
pub type Set8 = [bool; 256];

/// Counts from `check_binop_u8`.
#[derive(Debug, Default, Clone, Copy)]
pub struct OpReport {
    /// Operand pairs checked.
    pub cases: u64,
    /// Pairs whose result is sound but larger than the best abstraction.
    pub non_optimal: u64,
}

impl OpReport {
    pub fn pct_non_optimal(&self) -> f64 {
        if self.cases == 0 {
            0.0
        } else {
            100.0 * self.non_optimal as f64 / self.cases as f64
        }
    }
}

pub fn set_of<D>(d: &D, gamma: &impl Fn(&D, u8) -> bool) -> Set8 {
    let mut s = [false; 256];
    for x in 0..=255u8 {
        s[x as usize] = gamma(d, x);
    }
    s
}

/// Checks a binary abstract operation against its concrete counterpart on
/// every pair of `samples`, and every pair of members of their
/// concretizations.
///
/// - `gamma(d, x)`: membership of `x` in the concretization of `d`.
/// - `abs(a, b)`: the abstract result; `None` stands for `Bot`.
/// - `conc(x, y)`: the concrete result; `None` where it is undefined (a zero
///   divisor), so those pairs impose nothing.
/// - `alpha(s)`: the best abstraction of a nonempty set `s`, the reference
///   for optimality.
///
/// Panics on the first unsound result. A result is optimal when its
/// concretization equals that of `alpha` of the concrete result set (or it is
/// `None` and the set is empty).
pub fn check_binop_u8<D>(
    name: &str,
    samples: &[D],
    gamma: impl Fn(&D, u8) -> bool,
    abs: impl Fn(&D, &D) -> Option<D>,
    conc: impl Fn(u8, u8) -> Option<u8>,
    alpha: impl Fn(&Set8) -> D,
) -> OpReport {
    let members: Vec<Vec<u8>> = samples
        .iter()
        .map(|d| (0..=255u8).filter(|&x| gamma(d, x)).collect())
        .collect();
    let mut rep = OpReport::default();
    for (i, a) in samples.iter().enumerate() {
        for (j, b) in samples.iter().enumerate() {
            let r = abs(a, b);
            let mut want = [false; 256];
            let mut any = false;
            for &x in &members[i] {
                for &y in &members[j] {
                    if let Some(z) = conc(x, y) {
                        want[z as usize] = true;
                        any = true;
                    }
                }
            }
            let got = r.as_ref().map(|d| set_of(d, &gamma));
            for z in 0..256 {
                if want[z] {
                    assert!(
                        got.is_some_and(|g| g[z]),
                        "{name}: unsound on sample pair ({i}, {j}): misses {z}"
                    );
                }
            }
            rep.cases += 1;
            let optimal = match (got, any) {
                (None, _) => true,
                (Some(_), false) => false,
                (Some(g), true) => g == set_of(&alpha(&want), &gamma),
            };
            if !optimal {
                rep.non_optimal += 1;
            }
        }
    }
    rep
}

/// Membership of a truth value in a `Bool4`.
pub fn bool4_has(b: &Bool4, x: bool) -> bool {
    match b {
        Bool4::False => !x,
        Bool4::True => x,
        Bool4::Top => true,
    }
}

/// Checks a forward comparison on every pair of `samples` against `conc`.
/// Optimal means the answer holds exactly the truth values that some operand
/// pair produces. Panics on the first unsound answer.
pub fn check_cmp_u8<D>(
    name: &str,
    samples: &[D],
    gamma: impl Fn(&D, u8) -> bool,
    fwd: impl Fn(&D, &D) -> Bool4,
    conc: impl Fn(u8, u8) -> bool,
) -> OpReport {
    let members: Vec<Vec<u8>> = samples
        .iter()
        .map(|d| (0..=255u8).filter(|&x| gamma(d, x)).collect())
        .collect();
    let mut rep = OpReport::default();
    for (i, a) in samples.iter().enumerate() {
        for (j, b) in samples.iter().enumerate() {
            let r = fwd(a, b);
            let mut want = [false; 2];
            for &x in &members[i] {
                for &y in &members[j] {
                    want[conc(x, y) as usize] = true;
                }
            }
            for t in [false, true] {
                if want[t as usize] {
                    assert!(
                        bool4_has(&r, t),
                        "{name}: unsound on sample pair ({i}, {j}): misses {t}"
                    );
                }
            }
            rep.cases += 1;
            if [bool4_has(&r, false), bool4_has(&r, true)] != want {
                rep.non_optimal += 1;
            }
        }
    }
    rep
}

/// Checks a backward comparison `bwd(a, b, t)` for both `t` on every pair of
/// `samples`: every operand pair with `conc(x, y) == t` survives, and neither
/// operand grows. Optimal means each side equals `alpha` of the surviving
/// values (or is `None` when none survive). Counts one case per `(a, b, t)`.
pub fn check_assume_u8<D>(
    name: &str,
    samples: &[D],
    gamma: impl Fn(&D, u8) -> bool,
    bwd: impl Fn(&D, &D, bool) -> (Option<D>, Option<D>),
    conc: impl Fn(u8, u8) -> bool,
    alpha: impl Fn(&Set8) -> D,
) -> OpReport {
    let members: Vec<Vec<u8>> = samples
        .iter()
        .map(|d| (0..=255u8).filter(|&x| gamma(d, x)).collect())
        .collect();
    let mut rep = OpReport::default();
    for (i, a) in samples.iter().enumerate() {
        for (j, b) in samples.iter().enumerate() {
            let (sa, sb) = (set_of(a, &gamma), set_of(b, &gamma));
            for t in [false, true] {
                let (r0, r1) = bwd(a, b, t);
                let mut keep0 = [false; 256];
                let mut keep1 = [false; 256];
                for &x in &members[i] {
                    for &y in &members[j] {
                        if conc(x, y) == t {
                            keep0[x as usize] = true;
                            keep1[y as usize] = true;
                        }
                    }
                }
                let g0 = r0.as_ref().map(|d| set_of(d, &gamma));
                let g1 = r1.as_ref().map(|d| set_of(d, &gamma));
                for z in 0..256 {
                    assert!(
                        !keep0[z] || g0.is_some_and(|g| g[z]),
                        "{name}: lost left {z} on ({i}, {j}, {t})"
                    );
                    assert!(
                        !keep1[z] || g1.is_some_and(|g| g[z]),
                        "{name}: lost right {z} on ({i}, {j}, {t})"
                    );
                    assert!(g0.is_none_or(|g| !g[z] || sa[z]), "{name}: left grew");
                    assert!(g1.is_none_or(|g| !g[z] || sb[z]), "{name}: right grew");
                }
                let best = |keep: &Set8, g: Option<Set8>| match g {
                    None => true,
                    Some(g) => keep.iter().any(|&k| k) && g == set_of(&alpha(keep), &gamma),
                };
                rep.cases += 1;
                if !(best(&keep0, g0) && best(&keep1, g1)) {
                    rep.non_optimal += 1;
                }
            }
        }
    }
    rep
}
