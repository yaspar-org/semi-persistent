#!/usr/bin/env python3
"""Exhaustive simulation: compare plus_bv (non-recursive) vs plus_c (recursive)
for all 3-bit Tnum additions. Confirms they always agree."""

def hd(n): return n % 2
def tl(n): return n // 2
def cons(n, b): return b + 2 * n
def b_plus(a, b, c):
    s = a + b + c
    return (s % 2, s // 2)

def plus_c(a, b, c):
    if a == 0 and b == 0: return c
    r, c1 = b_plus(hd(a), hd(b), c)
    return cons(plus_c(tl(a), tl(b), c1), r)

def plus(a, b): return plus_c(a, b, 0)
def bw_xor(a, b): return a ^ b
def bw_or(a, b): return a | b
def bw_and_not(a, b): return a & ~b

def plus_bv(sv, sm, tv, tm):
    lbv = plus(sv, tv)
    lbm = plus(sm, tm)
    ub = plus(lbv, lbm)
    diff = bw_xor(ub, lbv)
    mask = bw_or(bw_or(diff, sm), tm)
    return (bw_and_not(lbv, mask), mask)

def tb_plus_c(sv, sm, tv, tm, cv, cm):
    lbvv, lbvc = b_plus(sv, tv, cv)
    lbmv, lbmc = b_plus(sm, tm, cm)
    ubv, ubc1 = b_plus(lbvv, lbmv, 0)
    ubc, _ = b_plus(lbvc, lbmc, ubc1)
    maskv = (ubv ^ lbvv) | sm | tm
    maskc = ubc ^ lbvc
    b1_v = lbvv & (~maskv & 1)
    b1_m = maskv
    c1_v = lbvc & (~maskc & 1)
    c1_m = maskc
    return (b1_v, b1_m, c1_v, c1_m)

def plus_c_recursive(sv, sm, tv, tm, cv, cm):
    if sv == 0 and sm == 0 and tv == 0 and tm == 0:
        return (cv, cm)
    b1_v, b1_m, c1_v, c1_m = tb_plus_c(hd(sv), hd(sm), hd(tv), hd(tm), cv, cm)
    tail_v, tail_m = plus_c_recursive(tl(sv), tl(sm), tl(tv), tl(tm), c1_v, c1_m)
    return (cons(tail_v, b1_v), cons(tail_m, b1_m))

BITS = 4
mismatches = 0
total = 0
for sv in range(1 << BITS):
    for sm in range(1 << BITS):
        if sv & sm: continue
        for tv in range(1 << BITS):
            for tm in range(1 << BITS):
                if tv & tm: continue
                total += 1
                bv_v, bv_m = plus_bv(sv, sm, tv, tm)
                rc_v, rc_m = plus_c_recursive(sv, sm, tv, tm, 0, 0)
                if bv_v != rc_v or bv_m != rc_m:
                    mismatches += 1
                    print(f"MISMATCH: Tn({sv},{sm})+Tn({tv},{tm}): "
                          f"bv=({bv_v},{bv_m}) rc=({rc_v},{rc_m})")

print(f"\n{total} cases checked, {mismatches} mismatches")
if mismatches == 0:
    print(f"ALL MATCH: plus_bv == plus_c for all {BITS}-bit Tnums")
