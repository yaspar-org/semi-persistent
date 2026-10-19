// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Differential tests of the real shared helpers (not a mirror implementation).
use semi_persistent_abstract_domains::arithmetic::{
    CrtMergeResult, crt_merge, gcd, gcd_machine_modulus, gcd_machine_modulus_exponent,
};

macro_rules! crt_cases {
    ($name:ident, $uint:ty) => {
        #[test]
        fn $name() {
            assert!(matches!(
                crt_merge::<$uint>(6, 13, 4, 11),
                CrtMergeResult::Class { modulus: 12, residue: 7 }
            ));
            assert!(matches!(crt_merge::<$uint>(6, 1, 4, 2), CrtMergeResult::Empty));
            let max = <$uint>::MAX;
            for expected in [0, 1, max] {
                match crt_merge(max, expected % max, max - 1, expected % (max - 1)) {
                    CrtMergeResult::Singleton { value } => assert_eq!(value, expected),
                    _ => panic!("expected a singleton with an overflowing LCM"),
                }
            }
            assert!(matches!(crt_merge(max, max - 1, max - 1, max - 2), CrtMergeResult::Empty));
            // The LCM fits, but no second value does. This must also collapse.
            assert!(matches!(crt_merge(max, 1, max, 1), CrtMergeResult::Singleton { value: 1 }));
            assert!(matches!(crt_merge(max, 0, max, 0), CrtMergeResult::Class { modulus, residue: 0 } if modulus == max));
            // Exact boundary: residue + modulus == MAX still has two members.
            let step = max / 2 + 1;
            let residue = max / 2;
            assert!(matches!(crt_merge(step, residue, step, residue), CrtMergeResult::Class { modulus, residue: r } if modulus == step && r == residue));
            assert_eq!(gcd(max, max - 1), 1);
            assert_eq!(gcd_machine_modulus_exponent(0 as $uint), <$uint>::BITS);
            assert_eq!(gcd_machine_modulus(max), 1);
            assert_eq!(gcd_machine_modulus(step), step);
            assert_eq!(gcd_machine_modulus_exponent(max), 0);
            assert_eq!(gcd_machine_modulus_exponent(step), <$uint>::BITS - 1);
            assert!(matches!(crt_merge::<$uint>(1, max, 1, max), CrtMergeResult::Class { modulus: 1, residue: 0 }));
            assert!(matches!(crt_merge::<$uint>(6, 1, 3, 1), CrtMergeResult::Class { modulus: 6, residue: 1 }));
        }
    };
}
crt_cases!(crt_u8, u8);
crt_cases!(crt_u16, u16);
crt_cases!(crt_u32, u32);
crt_cases!(crt_u64, u64);
crt_cases!(crt_u128, u128);

type Bits = [u64; 4];

fn brute_class(m: u8, r: u8) -> Bits {
    let mut bits = [0; 4];
    // Each input set is brute-forced over all 256 concrete values once.
    for x in 0..=u8::MAX {
        if x % m == r % m {
            bits[usize::from(x / 64)] |= 1u64 << (x % 64);
        }
    }
    bits
}

fn check_result(result: CrtMergeResult<u8>, expected: Bits, table: &[Bits]) {
    match result {
        CrtMergeResult::Empty => assert_eq!(expected, [0; 4]),
        CrtMergeResult::Singleton { value } => {
            let mut bits = [0; 4];
            bits[usize::from(value / 64)] = 1u64 << (value % 64);
            assert_eq!(bits, expected);
        }
        CrtMergeResult::Class { modulus, residue } => {
            assert!(modulus > 0 && residue < modulus);
            assert!(u16::from(residue) + u16::from(modulus) <= 255);
            assert_eq!(
                table[usize::from(modulus) * 256 + usize::from(residue)],
                expected
            );
        }
    }
}

#[test]
fn exhaustive_u8_crt_intersections() {
    let mut table = vec![[0; 4]; 256 * 256];
    let mut classes = Vec::new();
    for m in 1..=u8::MAX {
        for r in 0..m {
            let bits = brute_class(m, r);
            table[usize::from(m) * 256 + usize::from(r)] = bits;
            classes.push((m, r, bits));
        }
    }
    // Exercise every normalized positive-modulus pair, including duplicate
    // finite singleton encodings. CRT is symmetric, so enumerate unordered
    // pairs; focused/raw-input tests below also exercise swapped operands.
    let mut pairs = 0u64;
    for (i, &(m1, r1, a)) in classes.iter().enumerate() {
        for &(m2, r2, b) in &classes[i..] {
            // Bitwise intersection is exactly the 256-value brute-force oracle,
            // cached to avoid re-enumerating those values for every pair.
            let expected = [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]];
            check_result(crt_merge(m1, r1, m2, r2), expected, &table);
            pairs += 1;
        }
    }
    assert_eq!(classes.len(), 32_640);
    assert_eq!(pairs, 532_701_120);
}

#[test]
fn all_raw_u8_residues_and_operand_orders() {
    let mut table = vec![[0; 4]; 256 * 256];
    for m in 1..=u8::MAX {
        for r in 0..m {
            table[usize::from(m) * 256 + usize::from(r)] = brute_class(m, r);
        }
    }
    for m in 1..=u8::MAX {
        for r in 0..=u8::MAX {
            for (n, s) in [(1, 0), (2, 1), (7, 3), (128, 127), (201, 200), (255, 254)] {
                let a = brute_class(m, r);
                let b = brute_class(n, s);
                let expected = [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]];
                check_result(crt_merge(m, r, n, s), expected, &table);
                check_result(crt_merge(n, s, m, r), expected, &table);
            }
        }
    }
}

#[test]
fn exhaustive_u8_gcd() {
    for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
            let expected = if a == 0 && b == 0 {
                0
            } else {
                (1..=u8::MAX)
                    .rev()
                    .find(|&d| a % d == 0 && b % d == 0)
                    .unwrap()
            };
            let g = gcd(a, b);
            assert_eq!(g, expected);
            assert_eq!(gcd(b, a), g);
            for d in 1..=u8::MAX {
                if a % d == 0 && b % d == 0 {
                    assert_eq!(g % d, 0);
                }
            }
        }
    }
}

#[test]
fn gcd_associativity_and_machine_modulus() {
    // Exhaustively test associativity over a small cube; the proof is unbounded.
    for a in 0..32u8 {
        for b in 0..32u8 {
            for c in 0..32u8 {
                assert_eq!(gcd(gcd(a, b), c), gcd(a, gcd(b, c)));
            }
        }
    }
    for m in 0..=u8::MAX {
        let exponent = gcd_machine_modulus_exponent(m);
        let g = 1u16 << exponent;
        // The finite oracle includes zero, whose GCD is 256, not a u8.
        let expected = (1..=256u16)
            .rev()
            .find(|d| u16::from(m) % d == 0 && 256 % d == 0)
            .unwrap();
        assert_eq!(g, expected);
        if m != 0 {
            assert_eq!(u16::from(gcd_machine_modulus(m)), g);
        }
        for x in -512..=512i128 {
            assert_eq!(
                x.rem_euclid(256).rem_euclid(i128::from(g)),
                x.rem_euclid(i128::from(g))
            );
        }
    }
}

/// Independent arbitrary-precision oracle. Widening is confined to tests.
fn check_u128_bigint(m1: u128, r1: u128, m2: u128, r2: u128) {
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    let a = BigInt::from(m1);
    let b = BigInt::from(m2);
    let a1 = BigInt::from(r1) % &a;
    let a2 = BigInt::from(r2) % &b;
    let (mut old_r, mut r) = (a.clone(), b.clone());
    let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
    while !r.is_zero() {
        let q = &old_r / &r;
        (old_r, r) = (r.clone(), old_r - &q * &r);
        (old_s, s) = (s.clone(), old_s - q * &s);
    }
    let g = old_r;
    let actual = crt_merge(m1, r1, m2, r2);
    if &a1 % &g != &a2 % &g {
        assert!(matches!(actual, CrtMergeResult::Empty));
        return;
    }
    let n = &b / &g;
    let lcm = (&a / &g) * &b;
    let multiplier = ((&a2 - &a1) / &g) * old_s;
    let k = ((multiplier % &n) + &n) % &n;
    let candidate = a1 + a * k;
    let max = BigInt::from(u128::MAX);
    assert!(candidate >= BigInt::zero() && candidate < lcm);
    if candidate > max {
        assert!(matches!(actual, CrtMergeResult::Empty));
    } else if &candidate + &lcm > max {
        match actual {
            CrtMergeResult::Singleton { value } => assert_eq!(BigInt::from(value), candidate),
            _ => panic!("expected singleton: ({m1}, {r1}) intersect ({m2}, {r2})"),
        }
    } else {
        match actual {
            CrtMergeResult::Class { modulus, residue } => {
                assert_eq!(BigInt::from(modulus), lcm);
                assert_eq!(BigInt::from(residue), candidate);
            }
            _ => panic!("expected class: ({m1}, {r1}) intersect ({m2}, {r2})"),
        }
    }
}

#[test]
fn u128_crt_overflow_paths() {
    let half = 1u128 << 127;
    // Compatible, overflowing LCM, but the least solution fits.
    for value in [0, 1, u128::MAX] {
        check_u128_bigint(
            u128::MAX,
            value % u128::MAX,
            u128::MAX - 1,
            value % (u128::MAX - 1),
        );
        assert!(
            matches!(crt_merge(u128::MAX, value % u128::MAX, u128::MAX - 1, value % (u128::MAX - 1)),
            CrtMergeResult::Singleton { value: actual } if actual == value)
        );
    }
    // k = 2: the multiplication itself overflows.
    assert!((half + 1).checked_mul(2).is_none());
    check_u128_bigint(half + 1, 0, half, 2);
    assert!(matches!(
        crt_merge(half + 1, 0, half, 2),
        CrtMergeResult::Empty
    ));
    // k = 2: multiplication fits, addition reaches exactly 2^128.
    let term = (half - 1).checked_mul(2).unwrap();
    assert!(term.checked_add(2).is_none());
    check_u128_bigint(half - 1, 2, half, 0);
    assert!(matches!(
        crt_merge(half - 1, 2, half, 0),
        CrtMergeResult::Empty
    ));
    // Same multiplication, but the sum is MAX and must not be called empty.
    check_u128_bigint(half - 1, 1, half, half - 1);
    assert!(matches!(
        crt_merge(half - 1, 1, half, half - 1),
        CrtMergeResult::Singleton { value: u128::MAX }
    ));
}

#[test]
fn u128_crt_bigint_oracle() {
    let half = 1u128 << 127;
    let moduli = [
        1,
        2,
        3,
        6,
        1 << 63,
        (1 << 64) - 1,
        1 << 64,
        (1 << 64) + 1,
        half - 1,
        half,
        half + 1,
        u128::MAX - 1,
        u128::MAX,
    ];
    for &m1 in &moduli {
        for &m2 in &moduli {
            for r1 in [0, 1, m1 - 1, half, u128::MAX] {
                for r2 in [0, 1, m2 - 1, half, u128::MAX] {
                    check_u128_bigint(m1, r1, m2, r2);
                }
            }
        }
    }
    // Consecutive Fibonacci numbers exercise long Euclidean chains.
    let (mut a, mut b) = (1u128, 1u128);
    while let Some(next) = a.checked_add(b) {
        check_u128_bigint(a, u128::MAX, b, half);
        (a, b) = (b, next);
    }
    let mut seed = 0x5f37_59df_1234_5678_9abc_def0_8765_4321u128;
    let mut next = || {
        seed = seed
            .wrapping_mul(0x2360_ed05_1fc6_5da4_4385_df64_9fcc_f645)
            .wrapping_add(1);
        seed
    };
    for _ in 0..2000 {
        let (m1, r1, m2, r2) = (next().max(1), next(), next().max(1), next());
        check_u128_bigint(m1, r1, m2, r2);
        check_u128_bigint(m2, r2, m1, r1);
        // Force compatible inputs with a representable member as well.
        check_u128_bigint(m1, r1 % m1, m2, r1 % m2);
    }
}

#[test]
fn u128_machine_modulus_all_exponents() {
    use num_bigint::BigUint;
    use num_traits::One;
    let period = BigUint::one() << 128usize;
    let zero_exponent = gcd_machine_modulus_exponent(0u128);
    assert_eq!(zero_exponent, 128);
    assert_eq!(BigUint::one() << zero_exponent, period);
    for exponent in 0..128 {
        let power = 1u128 << exponent;
        for m in [power, u128::MAX << exponent] {
            assert_eq!(gcd_machine_modulus_exponent(m), exponent);
            assert_eq!(gcd_machine_modulus(m), power);
            assert_eq!(m % power, 0);
            assert_eq!(&period % BigUint::from(power), BigUint::from(0u8));
        }
    }
}
