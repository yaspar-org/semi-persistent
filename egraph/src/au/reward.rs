// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Selection reward (§2.5, §2.5.1): normalized compression ratio of an expected size.
//!
//! The functions here are the single place where sizes cross into the bounded
//! reward unit; everything upstream (Q values, backpropagation, AND composition)
//! stays in raw size units (§2.5.1 property C), and the basis `(a, b)` is a per-OR-
//! state constant shared by every action scored at that state (properties A, B).

/// Normalized compression ratio of an expected size against a state basis
/// `a = min(best_size(l), best_size(r))`, `b = max(best_size(l), best_size(r))`:
///
/// ```text
/// cr  = (expected_size - a) / b
/// ncr = 0                       if cr <= 0
///     = 1 - exp(-lambda * cr)   otherwise, lambda = -ln(1 - x_target)
/// ```
///
/// Landmarks (§2.5.1): `ncr(a) = 0` (perfect compression); `ncr(a + b) = x_target`
/// (the bare-Variants no-sharing result); `ncr` approaches 1 asymptotically for
/// unbounded sizes. Strictly increasing on `[a, +inf)`; the `cr <= 0` clamp is
/// unreachable for distinct classes (a valid anti-unifier projects into both
/// classes, so its size is at least `b`).
pub fn ncr(expected_size: f64, a: f64, b: f64, x_target: f64) -> f64 {
    debug_assert!(b > 0.0, "basis scale must be positive (§2.5.1 K)");
    debug_assert!(
        x_target > 0.0 && x_target < 1.0,
        "x_target must lie in (0,1) (§2.5.1 K)"
    );
    if b <= 0.0 {
        return 0.0;
    }
    let cr = (expected_size - a) / b;
    if cr <= 0.0 {
        return 0.0;
    }
    let lambda = -(1.0 - x_target).ln();
    1.0 - (-lambda * cr).exp()
}

/// Selection reward: `1 - ncr`. Reward 1 at perfect compression, `1 - x_target`
/// at the bare-Variants point, approaching 0 for unbounded sizes.
pub fn reward(expected_size: f64, a: f64, b: f64, x_target: f64) -> f64 {
    1.0 - ncr(expected_size, a, b, x_target)
}

#[cfg(test)]
mod tests {
    use super::*;

    const X: f64 = 0.8;

    #[test]
    fn landmark_values() {
        // ncr(a) = 0, ncr(a+b) = x_target, monotone past a+b.
        let (a, b) = (5.0, 10.0);
        assert_eq!(ncr(a, a, b, X), 0.0);
        assert!((ncr(a + b, a, b, X) - X).abs() < 1e-12);
        let past = ncr(a + b + 10.0, a, b, X);
        assert!(past <= 1.0);
        assert!(past > X);
    }

    #[test]
    fn equal_representative_sizes_keep_strict_ordering() {
        // b stays positive when both representatives have equal size, so distinct
        // sizes get distinct ncr values (§2.5: the max-min scale would collapse here).
        let (a, b) = (5.0, 5.0);
        let n6 = ncr(6.0, a, b, X);
        let n8 = ncr(8.0, a, b, X);
        let n10 = ncr(10.0, a, b, X);
        assert!(0.0 < n6 && n6 < n8 && n8 < n10 && n10 < 1.0);
        assert!((n10 - X).abs() < 1e-12);
    }
}
