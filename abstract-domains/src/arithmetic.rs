// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Shared GCD, Bézout and finite-word CRT helpers. No domain operations.
#![allow(unused_imports, unused_variables)]
use crate::word::Word;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Deterministic Euclidean specification, including gcd(0, 0) = 0.
pub open spec fn gcd_spec(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 { a } else { gcd_spec(b, a % b) }
}

/// Returns true if d is a positive common divisor of a and b.
/// A common divisor divides both a and b without a remainder.
pub open spec fn is_common_divisor(d: nat, a: nat, b: nat) -> bool {
    d > 0 && a % d == 0 && b % d == 0
}

/// Returns true if d is the greatest common divisor of a and b.
/// The special case gcd(0, 0) = 0 is handled separately.
pub open spec fn is_gcd(d: nat, a: nat, b: nat) -> bool {
    if a == 0 && b == 0 {
        d == 0
    } else {
        is_common_divisor(d, a, b)
        && forall|k: nat|
            #[trigger] is_common_divisor(k, a, b) ==> k <= d
    }
}

/// Proves that a Euclidean step preserves common divisors.
pub proof fn euclidean_step(a: nat, b: nat, d: nat)
    requires
        b > 0,
        d > 0,
    ensures
        is_common_divisor(d, a, b)
            <==> is_common_divisor(d, b, a % b),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        a as int,
        b as int,
    );

    if is_common_divisor(d, a, b) {
        assert(a % d == 0);
        assert(b % d == 0);

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            a as int,
            d as int,
        );
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            b as int,
            d as int,
        );

        assert((a % b) % d == 0) by {
            let ai = a as int;
            let bi = b as int;
            let di = d as int;

            assert(di > 0);
            assert(bi > 0);

            assert(ai % di == 0);
            assert(bi % di == 0);

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ai, bi);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ai, di);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bi, di);

            let q = ai / bi;
            let ad = ai / di;
            let bd = bi / di;
            let k = ad - q * bd;

            vstd::arithmetic::mul::lemma_mul_is_commutative(bi, q);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, ad);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, bd);
            assert(ai == q * bi + ai % bi);
            assert(ai == ad * di);
            assert(bi == bd * di);

            assert((a % b) as int == k * di) by (nonlinear_arith)
                requires
                    ai == q * bi + ai % bi,
                    ai == ad * di,
                    bi == bd * di,
                    (a % b) as int == ai % bi,
                    k == ad - q * bd,
            {
            }

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                (a % b) as int,
                di,
                k,
                0,
            );

            assert(((a % b) as int) % di == 0);
        }

        assert(is_common_divisor(d, b, a % b));
    }

    if is_common_divisor(d, b, a % b) {
        assert(b % d == 0);
        assert((a % b) % d == 0);

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            b as int,
            d as int,
        );

        assert(a % d == 0) by {
            let ai = a as int;
            let bi = b as int;
            let di = d as int;
            let ri = (a % b) as int;

            let q = ai / bi;
            let bd = bi / di;
            let rd = ri / di;
            let k = q * bd + rd;

            assert(di > 0);
            assert(bi > 0);
            assert(bi % di == 0);
            assert(ri % di == 0);

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ai, bi);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bi, di);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ri, di);

            vstd::arithmetic::mul::lemma_mul_is_commutative(bi, q);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, bd);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, rd);

            assert(ai == q * bi + ri);
            assert(bi == bd * di);
            assert(ri == rd * di);

            assert(ai == k * di) by (nonlinear_arith)
                requires
                    ai == q * bi + ri,
                    bi == bd * di,
                    ri == rd * di,
                    k == q * bd + rd,
            {
            }

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                ai,
                di,
                k,
                0,
            );

            assert(ai % di == 0);
        };

        assert(is_common_divisor(d, a, b));
    }
}


/// Returns true if g, x, and y satisfy Bézout's identity for a and b.
pub open spec fn is_extended_gcd(
    g: nat,
    x: int,
    y: int,
    a: nat,
    b: nat,
) -> bool {
    is_gcd(g, a, b)
        && x * a as int + y * b as int == g as int
}

/// Returns true if x satisfies both congruences.
pub open spec fn is_common_congruence_solution(
    x: int,
    m1: nat,
    r1: nat,
    m2: nat,
    r2: nat,
) -> bool {
    x % (m1 as int) == (r1 as int) % (m1 as int)
        && x % (m2 as int) == (r2 as int) % (m2 as int)
}

/// Returns true if the residues are compatible modulo the GCD.
pub open spec fn are_congruences_compatible(
    g: nat,
    r1: nat,
    r2: nat,
) -> bool {
    r1 % g == r2 % g
}

/// Proves that a common solution implies compatibility of the congruences.
pub proof fn crt_solution_implies_compatible(
    g: nat,
    m1: nat,
    r1: nat,
    m2: nat,
    r2: nat,
    x: int,
)
    requires
        m1 > 0,
        m2 > 0,
        is_gcd(g, m1, m2),
        is_common_congruence_solution(
            x,
            m1,
            r1,
            m2,
            r2,
        ),
    ensures
        are_congruences_compatible(
            g,
            r1,
            r2,
        ),
{
    // 1. Since g = gcd(m1, m2), g divides both moduli.
    assert(!(m1 == 0 && m2 == 0));
    assert(is_common_divisor(g, m1, m2));

    assert(g > 0);
    assert(m1 % g == 0);
    assert(m2 % g == 0);

    let gi = g as int;
    let m1i = m1 as int;
    let m2i = m2 as int;
    let r1i = r1 as int;
    let r2i = r2 as int;

    assert(gi > 0);


    // 2. From x ≡ r1 (mod m1), express x - r1 as a multiple of m1.
    assert(x % m1i == r1i % m1i);

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        x,
        m1i,
    );

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        r1i,
        m1i,
    );

    let xq1 = x / m1i;
    let r1q = r1i / m1i;
    let rem1 = x % m1i;

    assert(r1i % m1i == rem1);

    assert(
        x == xq1 * m1i + rem1
    );

    assert(
        r1i == r1q * m1i + rem1
    );

    let k1 = xq1 - r1q;

    assert(
        x - r1i == k1 * m1i
    ) by (nonlinear_arith)
        requires
            x == xq1 * m1i + rem1,
            r1i == r1q * m1i + rem1,
            k1 == xq1 - r1q,
    {
    }


    // 3. From x ≡ r2 (mod m2), express x - r2 as a multiple of m2.
    assert(x % m2i == r2i % m2i);

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        x,
        m2i,
    );

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        r2i,
        m2i,
    );

    let xq2 = x / m2i;
    let r2q = r2i / m2i;
    let rem2 = x % m2i;

    assert(r2i % m2i == rem2);

    assert(
        x == xq2 * m2i + rem2
    );

    assert(
        r2i == r2q * m2i + rem2
    );

    let k2 = xq2 - r2q;

    assert(
        x - r2i == k2 * m2i
    ) by (nonlinear_arith)
        requires
            x == xq2 * m2i + rem2,
            r2i == r2q * m2i + rem2,
            k2 == xq2 - r2q,
    {
    }


    // 4. Since g divides m1 and m2, write
    //     m1 = d1*g
    //     m2 = d2*g.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        m1i,
        gi,
    );

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        m2i,
        gi,
    );

    assert(m1i % gi == 0);
    assert(m2i % gi == 0);

    let d1 = m1i / gi;
    let d2 = m2i / gi;

    assert(
        m1i == d1 * gi
    );

    assert(
        m2i == d2 * gi
    );


    // 5. Subtract the two equations:
    // x - r1 = k1*m1
    // x - r2 = k2*m2
    // therefore: r2 - r1 = k1*m1 - k2*m2,
    // which is a multiple of g.
    let k = k1 * d1 - k2 * d2;

    assert(
        r2i - r1i == k * gi
    ) by (nonlinear_arith)
        requires
            x - r1i == k1 * m1i,
            x - r2i == k2 * m2i,
            m1i == d1 * gi,
            m2i == d2 * gi,
            k == k1 * d1 - k2 * d2,
    {
    }


    // 6. If r2 - r1 is a multiple of g, then r1 and r2 have the same remainder modulo g
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        r1i,
        gi,
    );

    let q = r1i / gi;
    let rem = r1i % gi;

    assert(
        r1i == q * gi + rem
    );

    assert(0 <= rem);
    assert(rem < gi);

    assert(
        r2i == (q + k) * gi + rem
    ) by (nonlinear_arith)
        requires
            r2i - r1i == k * gi,
            r1i == q * gi + rem,
    {
    }

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        r2i,
        gi,
        q + k,
        rem,
    );

    assert(r2i % gi == rem);
    assert(r1i % gi == rem);

    assert(r1i % gi == r2i % gi);

    // Bridge int modulo back to nat modulo.
    assert(r1 % g == r2 % g);

    assert(are_congruences_compatible(
        g,
        r1,
        r2,
    ));
}

/// Incompatible residues admit no common integer solution.
pub proof fn crt_incompatible_no_solution(
    g: nat, m1: nat, r1: nat, m2: nat, r2: nat,
)
    requires m1 > 0, m2 > 0, is_gcd(g, m1, m2),
        !are_congruences_compatible(g, r1, r2),
    ensures forall|x: int| !#[trigger] is_common_congruence_solution(
        x, m1, r1, m2, r2),
{
    assert forall|x: int| !#[trigger] is_common_congruence_solution(
        x, m1, r1, m2, r2) by {
        if is_common_congruence_solution(x, m1, r1, m2, r2) {
            crt_solution_implies_compatible(g, m1, r1, m2, r2, x);
        }
    }
}

/// A positive exact divisor has a positive quotient.
pub proof fn positive_exact_quotient(a: nat, d: nat)
    requires a > 0, d > 0, a % d == 0,
    ensures a / d > 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, d as int);
    assert(a / d > 0) by (nonlinear_arith)
        requires a > 0, d > 0, a == d * (a / d);
}

/// Adding a multiple of a modulus preserves its remainder.
pub proof fn congruence_shift(x: int, y: int, m: int, q: int)
    requires m > 0, x == y + m * q,
    ensures x % m == y % m,
{
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, y, m);
}

/// Convert Rust's signed remainder to a canonical mathematical residue.
pub proof fn signed_remainder_normalized(s: int, n: int, rem: int)
    requires n > 0, rem == vstd::arithmetic::div_mod::rust_rem(s, n),
    ensures (if rem < 0 { rem + n } else { rem }) == s % n,
{
    if s < 0 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(-s, n);
        let q = -((-s) / n);
        assert(s == n * q + rem) by (nonlinear_arith)
            requires -s == n * ((-s) / n) + (-s) % n,
                q == -((-s) / n), rem == -((-s) % n);
        let r = if rem < 0 { rem + n } else { rem };
        let quotient = if rem < 0 { q - 1 } else { q };
        assert(s == n * quotient + r) by (nonlinear_arith)
            requires s == n * q + rem,
                r == if rem < 0 { rem + n } else { rem },
                quotient == if rem < 0 { q - 1 } else { q };
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(s, n, quotient, r);
    }
}

/// The reduced CRT multiplier constructs a common solution.
pub proof fn crt_candidate_solution(
    m1: int, a1: int, m2: int, a2: int,
    g: int, s: int, t: int, k: int,
)
    requires
        m1 > 0, m2 > 0, g > 0,
        m1 % g == 0, m2 % g == 0,
        s * m1 + t * m2 == g,
        a1 % g == a2 % g,
        k % (m2 / g) == ((a2 / g - a1 / g) * s) % (m2 / g),
    ensures
        (a1 + m1 * k) % m1 == a1 % m1,
        (a1 + m1 * k) % m2 == a2 % m2,
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    let n = m2 / g;
    let delta = a2 / g - a1 / g;
    lemma_fundamental_div_mod(m2, g);
    positive_exact_quotient(m2 as nat, g as nat);
    lemma_fundamental_div_mod(a1, g);
    lemma_fundamental_div_mod(a2, g);
    assert(a2 - a1 == g * delta) by (nonlinear_arith)
        requires a1 == g * (a1 / g) + a1 % g,
            a2 == g * (a2 / g) + a2 % g, a1 % g == a2 % g,
            delta == a2 / g - a1 / g;
    lemma_fundamental_div_mod(k, n);
    lemma_fundamental_div_mod(delta * s, n);
    let h = k / n - (delta * s) / n;
    assert(k == delta * s + n * h) by (nonlinear_arith)
        requires k == n * (k / n) + k % n,
            delta * s == n * ((delta * s) / n) + (delta * s) % n,
            k % n == (delta * s) % n,
            h == k / n - (delta * s) / n;
    lemma_fundamental_div_mod(m1, g);
    let p = m1 / g;
    assert(m1 * n == m2 * p) by (nonlinear_arith)
        requires m1 == g * p, m2 == g * n;
    assert(m1 * (delta * s + n * h)
        == (s * m1) * delta + (m1 * n) * h) by (nonlinear_arith);
    assert((g - t * m2) * delta + (m2 * p) * h
        == g * delta + m2 * (p * h - t * delta)) by (nonlinear_arith);
    assert(a1 + m1 * k == a2 + m2 * (p * h - t * delta));
    congruence_shift(a1 + m1 * k, a1, m1, k);
    congruence_shift(a1 + m1 * k, a2, m2, p * h - t * delta);
}

/// Reduction by a common multiple preserves each input constraint.
pub proof fn crt_normalize_solution(x: int, m1: nat, m2: nat, d: nat)
    requires m1 > 0, m2 > 0, is_gcd(d, m1, m2),
    ensures
        (x % (((m1 / d) * m2) as int)) % (m1 as int) == x % (m1 as int),
        (x % (((m1 / d) * m2) as int)) % (m2 as int) == x % (m2 as int),
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    let a = m1 as int;
    let b = m2 as int;
    let g = d as int;
    let p = a / g;
    let n = b / g;
    lemma_fundamental_div_mod(a, g);
    lemma_fundamental_div_mod(b, g);
    positive_exact_quotient(m1, d);
    let l = p * b;
    assert(l > 0) by (nonlinear_arith) requires p > 0, b > 0, l == p * b;
    assert(l == a * n) by (nonlinear_arith)
        requires a == g * p, b == g * n, l == p * b;
    lemma_fundamental_div_mod(x, l);
    let q = x / l;
    let r = x % l;
    assert(x == r + a * (n * q)) by (nonlinear_arith)
        requires x == l * q + r, l == a * n;
    assert(x == r + b * (p * q)) by (nonlinear_arith)
        requires x == l * q + r, l == p * b;
    congruence_shift(x, r, a, n * q);
    congruence_shift(x, r, b, p * q);
}

/// The GCD is unique, including gcd(0, 0).
pub proof fn gcd_unique(g: nat, d: nat, a: nat, b: nat)
    requires is_gcd(g, a, b), is_gcd(d, a, b),
    ensures g == d,
{
    if a != 0 || b != 0 {
        assert(is_common_divisor(g, a, b));
        assert(is_common_divisor(d, a, b));
        assert(g <= d);
        assert(d <= g);
    }
}

/// Regroup four factors using associativity and commutativity.
pub proof fn mul_regroup(a: int, b: int, c: int, d: int)
    ensures (a * b) * (c * d) == (b * c) * (a * d),
{
    use vstd::arithmetic::mul::{lemma_mul_is_associative, lemma_mul_is_commutative};
    lemma_mul_is_associative(a * b, c, d);
    lemma_mul_is_associative(a, b, c);
    lemma_mul_is_commutative(a, b * c);
    lemma_mul_is_associative(b * c, a, d);
}

/// Bezout's identity makes every common multiple a multiple of the LCM.
pub proof fn common_multiple_is_lcm_multiple(
    z: int, a: int, b: int, g: int, s: int, t: int,
)
    requires a > 0, b > 0, g > 0,
        a % g == 0, b % g == 0,
        s * a + t * b == g,
        z % a == 0, z % b == 0,
    ensures z % ((a / g) * b) == 0,
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    lemma_fundamental_div_mod(a, g);
    lemma_fundamental_div_mod(z, a);
    lemma_fundamental_div_mod(z, b);
    positive_exact_quotient(a as nat, g as nat);
    let p = a / g;
    let l = p * b;
    let u = z / a;
    let v = z / b;
    let w = s * v + t * u;
    assert(l > 0) by (nonlinear_arith) requires p > 0, b > 0, l == p * b;
    assert(g * l == a * b) by (nonlinear_arith)
        requires a == g * p, l == p * b;
    assert((s * a + t * b) * z == s * a * z + t * b * z)
        by (nonlinear_arith);
    mul_regroup(s, a, b, v);
    mul_regroup(t, b, a, u);
    vstd::arithmetic::mul::lemma_mul_is_commutative(a, b);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(a * b, s * v, t * u);
    assert(s * a * (b * v) + t * b * (a * u)
        == (a * b) * (s * v + t * u));
    assert(g * z == (g * l) * w);
    assert(z == l * w) by (nonlinear_arith)
        requires g > 0, g * z == (g * l) * w;
    congruence_shift(z, 0, l, w);
}

/// A canonical common solution generates exactly the intersection.
pub proof fn crt_solution_class_exact(
    x: int, residue: nat, m1: nat, r1: nat, m2: nat, r2: nat,
    g: nat, s: int, t: int,
)
    requires m1 > 0, m2 > 0,
        is_extended_gcd(g, s, t, m1, m2),
        residue < (m1 / g) * m2,
        is_common_congruence_solution(residue as int, m1, r1, m2, r2),
    ensures
        (x % (((m1 / g) * m2) as int) == residue as int)
            <==> is_common_congruence_solution(x, m1, r1, m2, r2),
{
    let l = ((m1 / g) * m2) as int;
    let r = residue as int;
    crt_normalize_solution(x, m1, m2, g);
    if is_common_congruence_solution(x, m1, r1, m2, r2) {
        vstd::arithmetic::div_mod::lemma_mod_equivalence(x, r, m1 as int);
        vstd::arithmetic::div_mod::lemma_mod_equivalence(x, r, m2 as int);
        common_multiple_is_lcm_multiple(x - r, m1 as int, m2 as int,
            g as int, s, t);
        vstd::arithmetic::div_mod::lemma_mod_equivalence(x, r, l);
        vstd::arithmetic::div_mod::lemma_small_mod(residue, l as nat);
    }
}

/// Normalizing modulo m preserves residues modulo every divisor of m.
pub proof fn normalize_preserves_divisor(r: nat, m: nat, d: nat)
    requires m > 0, d > 0, m % d == 0,
    ensures (r % m) % d == r % d,
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    lemma_fundamental_div_mod(r as int, m as int);
    lemma_fundamental_div_mod(m as int, d as int);
    let q = (r / m) as int;
    let k = (m / d) as int;
    assert(r as int == (r % m) as int + (d as int) * (k * q))
        by (nonlinear_arith)
        requires r as int == (m as int) * q + (r % m) as int,
            m as int == (d as int) * k;
    congruence_shift(r as int, (r % m) as int, d as int, k * q);
}

/// Connect the recursive specification to the traditional greatest divisor.
pub proof fn lemma_gcd_spec(a: nat, b: nat)
    ensures is_gcd(gcd_spec(a, b), a, b),
    decreases b,
{
    if b == 0 {
        if a > 0 {
            lemma_mod_self_0(a as int);
            assert forall|k: nat| #[trigger] is_common_divisor(k, a, 0) implies k <= a by {
                assert(k <= a) by (nonlinear_arith) requires a > 0, k > 0, a % k == 0;
            }
        }
    } else {
        lemma_mod_bound(a as int, b as int);
        lemma_gcd_spec(b, a % b);
        let g = gcd_spec(b, a % b);
        euclidean_step(a, b, g);
        assert forall|k: nat| #[trigger] is_common_divisor(k, a, b) implies k <= g by {
            euclidean_step(a, b, k);
        }
    }
}

/// Divisibility maximality, stronger than numerical maximality.
pub proof fn lemma_gcd_divisor(a: nat, b: nat, d: nat)
    requires d > 0, is_common_divisor(d, a, b),
    ensures gcd_spec(a, b) % d == 0,
    decreases b,
{
    if b > 0 {
        euclidean_step(a, b, d);
        lemma_mod_bound(a as int, b as int);
        lemma_gcd_divisor(b, a % b, d);
    }
}

pub proof fn lemma_gcd_symmetric(a: nat, b: nat)
    ensures gcd_spec(a, b) == gcd_spec(b, a),
{
    lemma_gcd_spec(a, b);
    lemma_gcd_spec(b, a);
    if a != 0 || b != 0 {
        assert forall|k: nat| #[trigger] is_common_divisor(k, a, b) implies k <= gcd_spec(b, a) by {
            assert(is_common_divisor(k, b, a));
        }
    }
    gcd_unique(gcd_spec(a, b), gcd_spec(b, a), a, b);
}

/// Divisibility is transitive, including a zero dividend.
pub proof fn lemma_divides_transitive(a: nat, b: nat, d: nat)
    requires b > 0, d > 0, a % b == 0, b % d == 0,
    ensures a % d == 0,
{
    lemma_fundamental_div_mod(a as int, b as int);
    lemma_fundamental_div_mod(b as int, d as int);
    let q = (a / b) * (b / d);
    assert(a == d * q) by (nonlinear_arith)
        requires a == b * (a / b), b == d * (b / d), q == (a / b) * (b / d);
    lemma_fundamental_div_mod_converse(a as int, d as int, q as int, 0);
}

pub proof fn lemma_gcd_divisor_iff(a: nat, b: nat, d: nat)
    requires d > 0,
    ensures (gcd_spec(a, b) % d == 0) <==> is_common_divisor(d, a, b),
{
    lemma_gcd_spec(a, b);
    if is_common_divisor(d, a, b) { lemma_gcd_divisor(a, b, d); }
    let g = gcd_spec(a, b);
    if g > 0 && g % d == 0 {
        lemma_divides_transitive(a, g, d);
        lemma_divides_transitive(b, g, d);
    }
}

pub proof fn lemma_gcd_associative(a: nat, b: nat, c: nat)
    ensures gcd_spec(gcd_spec(a, b), c) == gcd_spec(a, gcd_spec(b, c)),
{
    let ab = gcd_spec(a, b);
    let bc = gcd_spec(b, c);
    let left = gcd_spec(ab, c);
    let right = gcd_spec(a, bc);
    lemma_gcd_spec(a, b);
    lemma_gcd_spec(b, c);
    lemma_gcd_spec(ab, c);
    lemma_gcd_spec(a, bc);
    if left > 0 {
        lemma_gcd_divisor_iff(a, b, left);
        lemma_gcd_divisor_iff(b, c, left);
        assert(is_common_divisor(left, a, bc));
    }
    if right > 0 {
        lemma_gcd_divisor_iff(b, c, right);
        lemma_gcd_divisor_iff(a, b, right);
        assert(is_common_divisor(right, ab, c));
    }
}

/// Generic machine-word Euclidean algorithm.
pub fn gcd<W: Word>(a: W, b: W) -> (r: W)
    ensures r.view() == gcd_spec(a.view(), b.view()),
        is_gcd(r.view(), a.view(), b.view()),
    decreases b.view(),
{
    proof { lemma_gcd_spec(a.view(), b.view()); }
    if b.eq(W::zero()) { a }
    else {
        let rem = a.urem(b);
        proof { lemma_mod_bound(a.view() as int, b.view() as int); }
        gcd(b, rem)
    }
}

/// Finite-word intersection of two positive-modulus classes.
pub enum CrtMergeResult<W> {
    Class { modulus: W, residue: W },
    Singleton { value: W },
    Empty,
}

impl<W: Word> CrtMergeResult<W> {
    pub open spec fn wf(&self) -> bool {
        match self {
            Self::Class { modulus, residue } => modulus.view() > 0
                && residue.view() < modulus.view()
                && residue.view() + modulus.view() < W::modulus(),
            _ => true,
        }
    }

    pub open spec fn has(&self, x: W) -> bool {
        match self {
            Self::Class { modulus, residue } => x.view() % modulus.view() == residue.view(),
            Self::Singleton { value } => x == *value,
            Self::Empty => false,
        }
    }
}

/// The least nonnegative member and the next possible member of a class.
proof fn lemma_class_member(x: nat, m: nat, r: nat)
    requires m > 0, r < m,
    ensures x % m == r ==> r <= x && (x == r || r + m <= x),
{
    if x % m == r {
        lemma_mod_decreases(x, m);
        lemma_fundamental_div_mod(x as int, m as int);
        assert(x == r || r + m <= x) by (nonlinear_arith)
            requires m > 0, x == m * (x / m) + r;
    }
}

/// Subtraction modulo a positive modulus, with already reduced operands.
fn submod<W: Word>(a: W, b: W, m: W) -> (r: W)
    requires m.view() > 0, a.view() < m.view(), b.view() < m.view(),
    ensures r.view() < m.view(),
        r.view() as int == (a.view() as int - b.view() as int) % (m.view() as int),
{
    if b.le(a) {
        let r = match a.checked_sub(b) { Some(r) => r, None => { proof { assert(false); } return W::zero(); } };
        proof { lemma_small_mod(r.view(), m.view()); }
        r
    } else {
        let d = match b.checked_sub(a) { Some(d) => d, None => { proof { assert(false); } return W::zero(); } };
        let r = match m.checked_sub(d) { Some(r) => r, None => { proof { assert(false); } return W::zero(); } };
        proof {
            lemma_mod_add_multiples_vanish(a.view() as int - b.view() as int, m.view() as int);
            lemma_small_mod(r.view(), m.view());
        }
        r
    }
}

/// Dividing positive inputs by their GCD leaves coprime inputs.
pub proof fn lemma_gcd_reduced(a: nat, b: nat)
    requires a > 0, b > 0,
    ensures gcd_spec(a / gcd_spec(a, b), b / gcd_spec(a, b)) == 1,
{
    lemma_gcd_spec(a, b);
    let g = gcd_spec(a, b);
    let p = a / g;
    let n = b / g;
    positive_exact_quotient(a, g);
    positive_exact_quotient(b, g);
    lemma_gcd_spec(p, n);
    let d = gcd_spec(p, n);
    lemma_fundamental_div_mod(a as int, g as int);
    lemma_fundamental_div_mod(b as int, g as int);
    lemma_fundamental_div_mod(p as int, d as int);
    lemma_fundamental_div_mod(n as int, d as int);
    assert(a == (g * d) * (p / d) && b == (g * d) * (n / d)) by (nonlinear_arith)
        requires a == g * p, b == g * n, p == d * (p / d), n == d * (n / d);
    assert(g * d > 0) by (nonlinear_arith) requires g > 0, d > 0;
    lemma_mod_multiples_basic((p / d) as int, (g * d) as int);
    lemma_mod_multiples_basic((n / d) as int, (g * d) as int);
    assert(a == (p / d) * (g * d) && b == (n / d) * (g * d)) by (nonlinear_arith)
        requires a == (g * d) * (p / d), b == (g * d) * (n / d);
    assert(is_common_divisor(g * d, a, b));
    assert(d == 1) by (nonlinear_arith) requires g > 0, d > 0, g * d <= g;
}

/// Iterative Euclid: only the inverse coefficient is stored at runtime,
/// reduced modulo n after each update. Signed Bézout witnesses are ghost-only.
fn inverse_mod<W: Word>(a: W, n: W) -> (s: W)
    requires n.view() > 0, gcd_spec(a.view(), n.view()) == 1,
    ensures s.view() < n.view(),
        (s.view() * a.view()) % n.view() == 1nat % n.view(),
{
    if n.eq(W::one()) { return W::zero(); }
    let mut old_r = a;
    let mut r = n;
    let mut old_s = W::one();
    let mut s = W::zero();
    let ghost mut old_x: int = 1;
    let ghost mut x: int = 0;
    let ghost mut old_y: int = 0;
    let ghost mut y: int = 1;
    proof {
        lemma_small_mod(1, n.view());
        lemma_small_mod(0, n.view());
    }
    while !r.eq(W::zero())
        invariant
            n.view() > 1,
            gcd_spec(old_r.view(), r.view()) == 1,
            old_r.view() as int == old_x * a.view() + old_y * n.view(),
            r.view() as int == x * a.view() + y * n.view(),
            old_s.view() as int == old_x % (n.view() as int),
            s.view() as int == x % (n.view() as int),
            old_s.view() < n.view(), s.view() < n.view(),
        decreases r.view(),
    {
        let q = old_r.udiv(r);
        let next_r = old_r.urem(r);
        let product = q.mulmod(s, n);
        proof { lemma_mod_bound((q.view() * s.view()) as int, n.view() as int); }
        let next_s = submod(old_s, product, n);
        let ghost next_x = old_x - q.view() * x;
        let ghost next_y = old_y - q.view() * y;
        proof {
            lemma_fundamental_div_mod(old_r.view() as int, r.view() as int);
            lemma_mod_bound(old_r.view() as int, r.view() as int);
            assert(next_r.view() as int == next_x * a.view() + next_y * n.view()) by (nonlinear_arith)
                requires
                    old_r.view() as int == old_x * a.view() + old_y * n.view(),
                    r.view() as int == x * a.view() + y * n.view(),
                    old_r.view() == q.view() * r.view() + next_r.view(),
                    next_x == old_x - q.view() * x, next_y == old_y - q.view() * y;
            lemma_mul_mod_noop_right(q.view() as int, x, n.view() as int);
            lemma_sub_mod_noop(old_x, q.view() * x, n.view() as int);
            lemma_sub_mod_noop(old_s.view() as int, product.view() as int, n.view() as int);
            lemma_small_mod(old_s.view(), n.view());
            lemma_small_mod(product.view(), n.view());
        }
        old_r = r;
        r = next_r;
        old_s = s;
        s = next_s;
        proof { old_x = x; x = next_x; old_y = y; y = next_y; }
    }
    proof {
        assert(old_r.view() == 1);
        assert(old_x * a.view() == 1 + n.view() * (-old_y)) by (nonlinear_arith)
            requires 1 == old_x * a.view() + old_y * n.view();
        congruence_shift(old_x * a.view(), 1, n.view() as int, -old_y);
        lemma_mul_mod_noop_left(old_x, a.view() as int, n.view() as int);
    }
    old_s
}

/// Recover an exact mathematical Bézout witness from a modular inverse.
proof fn inverse_bezout(a: nat, n: nat, s: nat) -> (t: int)
    requires n > 0, (s * a) % n == 1nat % n,
    ensures s * a + t * n == 1,
{
    lemma_mod_equivalence(1, (s * a) as int, n as int);
    lemma_fundamental_div_mod(1 - s * a, n as int);
    (1 - s * a) / (n as int)
}

/// Exact CRT over representable words. Moduli MUST be positive.
/// Congruence's modulus-zero constants must be handled by callers first.
pub fn crt_merge<W: Word>(m1: W, r1: W, m2: W, r2: W) -> (result: CrtMergeResult<W>)
    requires m1.view() > 0, m2.view() > 0,
    ensures result.wf(),
        forall|x: W| #[trigger] result.has(x) <==>
            is_common_congruence_solution(x.view() as int, m1.view(), r1.view(), m2.view(), r2.view()),
{
    let a1 = r1.urem(m1);
    let a2 = r2.urem(m2);
    let g = gcd(m1, m2);
    proof {
        lemma_mod_bound(r1.view() as int, m1.view() as int);
        lemma_mod_bound(r2.view() as int, m2.view() as int);
        lemma_small_mod(a1.view(), m1.view());
        lemma_small_mod(a2.view(), m2.view());
    }
    if !a1.urem(g).eq(a2.urem(g)) {
        proof {
            crt_incompatible_no_solution(g.view(), m1.view(), a1.view(), m2.view(), a2.view());
            assert forall|x: W| !#[trigger] is_common_congruence_solution(
                x.view() as int, m1.view(), r1.view(), m2.view(), r2.view()) by {
                assert(!is_common_congruence_solution(x.view() as int, m1.view(), a1.view(), m2.view(), a2.view()));
            }
        }
        return CrtMergeResult::Empty;
    }
    let p = m1.udiv(g);
    let n = m2.udiv(g);
    proof {
        positive_exact_quotient(m1.view(), g.view());
        positive_exact_quotient(m2.view(), g.view());
        lemma_gcd_reduced(m1.view(), m2.view());
    }
    let s = inverse_mod(p, n);
    let ghost t = inverse_bezout(p.view(), n.view(), s.view());
    let q1 = a1.udiv(g).urem(n);
    let q2 = a2.udiv(g).urem(n);
    proof {
        lemma_mod_bound((a1.view() / g.view()) as int, n.view() as int);
        lemma_mod_bound((a2.view() / g.view()) as int, n.view() as int);
    }
    let delta = submod(q2, q1, n);
    let k = delta.mulmod(s, n);
    let ghost lcm = p.view() * m2.view();
    let ghost candidate = a1.view() + m1.view() * k.view();
    proof {
        lemma_fundamental_div_mod(m1.view() as int, g.view() as int);
        lemma_fundamental_div_mod(m2.view() as int, g.view() as int);
        assert(s.view() * m1.view() + t * m2.view() == g.view()) by (nonlinear_arith)
            requires m1.view() == g.view() * p.view(), m2.view() == g.view() * n.view(),
                s.view() * p.view() + t * n.view() == 1;
        assert(is_extended_gcd(g.view(), s.view() as int, t, m1.view(), m2.view()));
        lemma_mod_bound((delta.view() * s.view()) as int, n.view() as int);
        lemma_sub_mod_noop((a2.view() / g.view()) as int, (a1.view() / g.view()) as int, n.view() as int);
        lemma_mul_mod_noop_left((a2.view() / g.view()) as int - (a1.view() / g.view()) as int,
            s.view() as int, n.view() as int);
        lemma_small_mod(k.view(), n.view());
        crt_candidate_solution(m1.view() as int, a1.view() as int, m2.view() as int, a2.view() as int,
            g.view() as int, s.view() as int, t, k.view() as int);
        assert(lcm == m1.view() * n.view()) by (nonlinear_arith)
            requires m1.view() == g.view() * p.view(), m2.view() == g.view() * n.view(), lcm == p.view() * m2.view();
        assert(0 < lcm && candidate < lcm) by (nonlinear_arith)
            requires m1.view() > 0, n.view() > 0, a1.view() < m1.view(), k.view() < n.view(),
                candidate == a1.view() + m1.view() * k.view(), lcm == m1.view() * n.view();
        assert forall|x: W| #[trigger] is_common_congruence_solution(x.view() as int, m1.view(), r1.view(), m2.view(), r2.view())
            <==> x.view() % lcm == candidate by {
            crt_solution_class_exact(x.view() as int, candidate, m1.view(), r1.view(), m2.view(), r2.view(),
                g.view(), s.view() as int, t);
        }
    }
    let modulus = p.checked_mul(m2);
    let term = m1.checked_mul(k);
    let residue = match term { Some(term) => term.checked_add(a1), None => None };
    let result = match residue {
        None => CrtMergeResult::Empty,
        Some(residue) => match modulus {
            None => CrtMergeResult::Singleton { value: residue },
            Some(modulus) => match residue.checked_add(modulus) {
                None => CrtMergeResult::Singleton { value: residue },
                Some(next) => { proof { next.lemma_view_bounded(); } CrtMergeResult::Class { modulus, residue } },
            },
        },
    };
    proof {
        assert forall|x: W| #[trigger] result.has(x) <==>
            is_common_congruence_solution(x.view() as int, m1.view(), r1.view(), m2.view(), r2.view()) by {
            x.lemma_view_bounded();
            lemma_class_member(x.view(), lcm, candidate);
            match result {
                CrtMergeResult::Singleton { value } => {
                    W::lemma_view_injective(x, value);
                    lemma_small_mod(candidate, lcm);
                },
                _ => {},
            }
        }
    }
    result
}

/// An odd number is coprime with every power of two. These coefficients
/// exist only in proofs; no signed or widened arithmetic is executed.
proof fn odd_pow2_bezout(a: nat, bits: nat) -> (witness: (int, int))
    requires a % 2 == 1,
    ensures witness.0 * a + witness.1 * pow2(bits) == 1,
    decreases bits,
{
    if bits == 0 {
        vstd::arithmetic::power::lemma_pow0(2);
        (0, 1)
    } else {
        let (s, t) = odd_pow2_bezout(a, (bits - 1) as nat);
        let p = pow2((bits - 1) as nat);
        lemma_pow2_unfold(bits);
        lemma_fundamental_div_mod(t, 2);
        if t % 2 == 0 {
            assert(s * a + (t / 2) * pow2(bits) == 1) by (nonlinear_arith)
                requires s * a + t * p == 1, pow2(bits) == 2 * p, t == 2 * (t / 2);
            (s, t / 2)
        } else {
            lemma_mod_bound(t, 2);
            lemma_sub_mod_noop(t, a as int, 2);
            lemma_fundamental_div_mod(t - a, 2);
            assert((s + p) * a + ((t - a) / 2) * pow2(bits) == 1) by (nonlinear_arith)
                requires s * a + t * p == 1, pow2(bits) == 2 * p, t - a == 2 * ((t - a) / 2);
            (s + p, (t - a) / 2)
        }
    }
}

/// The Word valuation contract determines the exact mathematical GCD.
pub proof fn lemma_gcd_pow2(m: nat, bits: nat, exponent: nat)
    requires
        exponent <= bits,
        m == 0 ==> exponent == bits,
        m != 0 ==> crate::word::tz_spec(m, exponent),
    ensures gcd_spec(m, pow2(bits)) == pow2(exponent),
{
    lemma_pow2_pos(bits);
    lemma_pow2_pos(exponent);
    if m == 0 {
        lemma_gcd_symmetric(m, pow2(bits));
    } else {
        let p = pow2(exponent);
        let q = m / p;
        let k = (bits - exponent) as nat;
        lemma_pow2_adds(exponent, k);
        lemma_fundamental_div_mod(m as int, p as int);
        let (s, t) = odd_pow2_bezout(q, k);
        assert(s * m + t * pow2(bits) == p) by (nonlinear_arith)
            requires m == q * p, pow2(bits) == p * pow2(k), s * q + t * pow2(k) == 1;
        lemma_mod_multiples_basic(pow2(k) as int, p as int);
        assert(pow2(bits) == pow2(k) * p) by (nonlinear_arith)
            requires pow2(bits) == p * pow2(k);
        lemma_gcd_spec(m, pow2(bits));
        let g = gcd_spec(m, pow2(bits));
        assert(is_common_divisor(p, m, pow2(bits)));
        lemma_fundamental_div_mod(m as int, g as int);
        lemma_fundamental_div_mod(pow2(bits) as int, g as int);
        let h = s * (m / g) + t * (pow2(bits) / g);
        assert(p == h * g) by (nonlinear_arith)
            requires s * m + t * pow2(bits) == p,
                m == g * (m / g), pow2(bits) == g * (pow2(bits) / g),
                h == s * (m / g) + t * (pow2(bits) / g);
        lemma_mod_multiples_basic(h, g as int);
        assert(g <= p) by (nonlinear_arith) requires p > 0, g > 0, p % g == 0;
    }
}

/// Exact GCD with 2^bits, represented by its exponent. This is total:
/// zero returns `bits`, representing 2^bits mathematically, never as a W.
pub fn gcd_machine_modulus_exponent<W: Word>(m: W) -> (exponent: u32)
    ensures
        exponent as nat <= W::bits(),
        pow2(exponent as nat) == gcd_spec(m.view(), W::modulus()),
        m.view() == 0 ==> exponent as nat == W::bits(),
        m.view() != 0 ==> (exponent as nat) < W::bits(),
        m.view() % pow2(exponent as nat) == 0,
        W::modulus() % pow2(exponent as nat) == 0,
{
    let exponent = m.trailing_zeros();
    proof {
        W::lemma_modulus();
        lemma_gcd_pow2(m.view(), W::bits(), exponent as nat);
        lemma_gcd_spec(m.view(), W::modulus());
    }
    exponent
}

/// For a nonzero word the GCD with the machine modulus is representable.
/// Zero must use `gcd_machine_modulus_exponent`: its GCD is 2^bits, not a word.
pub fn gcd_machine_modulus<W: Word>(m: W) -> (r: W)
    requires m.view() > 0,
    ensures r.view() == gcd_spec(m.view(), W::modulus()), r.view() > 0,
        m.view() % r.view() == 0, W::modulus() % r.view() == 0,
{
    let complement = m.neg_nonzero();
    let r = gcd(m, complement);
    proof {
        W::lemma_modulus();
        m.lemma_view_bounded();
        lemma_gcd_symmetric(m.view(), W::modulus());
        lemma_gcd_symmetric(m.view(), complement.view());
        lemma_mod_sub_multiples_vanish(W::modulus() as int, m.view() as int);
        assert(gcd_spec(W::modulus(), m.view()) == gcd_spec(complement.view(), m.view()));
        lemma_gcd_spec(m.view(), W::modulus());
    }
    r
}

/// Wrapping preserves congruence modulo gcd(m, 2^N), for negative integers too.
/// This is a shared mathematical fact, not a Congruence transfer operation.
pub proof fn lemma_wrapping_congruence<W: Word>(m: nat, x: int)
    ensures gcd_spec(m, W::modulus()) > 0,
        (x % (W::modulus() as int)) % (gcd_spec(m, W::modulus()) as int)
            == x % (gcd_spec(m, W::modulus()) as int),
{
    W::lemma_modulus();
    let n = W::modulus() as int;
    let g = gcd_spec(m, W::modulus()) as int;
    lemma_gcd_spec(m, W::modulus());
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(n, g);
    let q = x / n;
    let k = n / g;
    assert(x == x % n + g * (k * q)) by (nonlinear_arith)
        requires x == n * q + x % n, n == g * k;
    congruence_shift(x, x % n, g, k * q);
}

} // verus!
