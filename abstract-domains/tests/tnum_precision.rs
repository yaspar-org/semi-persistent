// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive u8 checks of the precision-optimized Tnum multiplication and division
//! (`mul_pj`, `divrem_g`) against the existing `mul`, on every pair of Tnums: soundness
//! against the concrete results, and the number of unknown bits relative to the best
//! Tnum (the AND and OR of every concrete result). Run with `--release --ignored`.
use semi_persistent_abstract_domains::domains::d8::ExecTnum;

fn tnums() -> Vec<ExecTnum> {
    let mut v = Vec::new();
    for m in 0..=255u8 {
        for x in 0..=255u8 {
            if x & m == 0 {
                v.push(ExecTnum { val: x, mask: m });
            }
        }
    }
    v
}

fn members(t: &ExecTnum) -> Vec<u8> {
    let mut out = Vec::new();
    let mut s = t.mask;
    loop {
        out.push(t.val | s);
        if s == 0 {
            return out;
        }
        s = (s - 1) & t.mask;
    }
}

fn has(t: &ExecTnum, x: u8) -> bool {
    x & !t.mask == t.val
}

fn best<I: Iterator<Item = u8>>(it: I) -> u32 {
    let (mut a, mut o) = (0xffu8, 0u8);
    for x in it {
        a &= x;
        o |= x;
    }
    (o ^ a).count_ones()
}

#[test]
#[ignore = "exhaustive over 43M pairs; run with --release --ignored"]
fn exhaustive_u8_mul_and_divrem_precision() {
    let ts = tnums();
    let (mut n_mul, mut n_div) = (0u64, 0u64);
    let (mut opt_old, mut opt_pj, mut lost_old, mut lost_pj) = (0u64, 0u64, 0u64, 0u64);
    let (mut opt_q, mut opt_r, mut lost_q, mut lost_r) = (0u64, 0u64, 0u64, 0u64);
    for a in &ts {
        let xs = members(a);
        for b in &ts {
            let ys = members(b);
            n_mul += 1;
            let bm = best(
                xs.iter()
                    .flat_map(|&x| ys.iter().map(move |&y| x.wrapping_mul(y))),
            );
            let (old, pj) = (a.mul(b), a.mul_pj(b));
            for &x in &xs {
                for &y in &ys {
                    assert!(has(&old, x.wrapping_mul(y)) && has(&pj, x.wrapping_mul(y)));
                }
            }
            let (lo, lp) = (old.mask.count_ones() - bm, pj.mask.count_ones() - bm);
            opt_old += (lo == 0) as u64;
            opt_pj += (lp == 0) as u64;
            lost_old += lo as u64;
            lost_pj += lp as u64;
            if b.val == 0 {
                continue;
            }
            n_div += 1;
            let (q, r) = a.divrem_g(b);
            for &x in &xs {
                for &y in &ys {
                    assert!(has(&q, x / y) && has(&r, x % y));
                }
            }
            let bq = best(xs.iter().flat_map(|&x| ys.iter().map(move |&y| x / y)));
            let br = best(xs.iter().flat_map(|&x| ys.iter().map(move |&y| x % y)));
            let (lq, lr) = (q.mask.count_ones() - bq, r.mask.count_ones() - br);
            opt_q += (lq == 0) as u64;
            opt_r += (lr == 0) as u64;
            lost_q += lq as u64;
            lost_r += lr as u64;
        }
    }
    let pct = |a: u64, n: u64| 100.0 * a as f64 / n as f64;
    let avg = |a: u64, n: u64| a as f64 / n as f64;
    println!(
        "mul ({n_mul} pairs): mul optimal {:.1}%, {:.3} bits lost; mul_pj optimal {:.1}%, {:.3} bits lost",
        pct(opt_old, n_mul),
        avg(lost_old, n_mul),
        pct(opt_pj, n_mul),
        avg(lost_pj, n_mul)
    );
    println!(
        "divrem_g ({n_div} pairs): q optimal {:.1}%, {:.3} bits lost; r optimal {:.1}%, {:.3} bits lost",
        pct(opt_q, n_div),
        avg(lost_q, n_div),
        pct(opt_r, n_div),
        avg(lost_r, n_div)
    );
}
