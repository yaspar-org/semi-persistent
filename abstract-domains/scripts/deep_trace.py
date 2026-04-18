#!/usr/bin/env python3
"""Deep trace: dump every intermediate value at each recursion level for both
the non-recursive (plus_bv) and recursive (plus_c) formulations, side by side.
This is the script that revealed the carry compensation property."""

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

def tb_plus_c(sv, sm, tv, tm, cv, cm):
    lbvv, lbvc = b_plus(sv, tv, cv)
    lbmv, lbmc = b_plus(sm, tm, cm)
    ubv, ubc1 = b_plus(lbvv, lbmv, 0)
    ubc, _ = b_plus(lbvc, lbmc, ubc1)
    maskv = (ubv ^ lbvv) | sm | tm
    maskc = ubc ^ lbvc
    return {
        'rv0': lbvv, 'cv1': lbvc, 'rm0': lbmv, 'cm1': lbmc,
        'ub0': ubv, 'ubc1': ubc1, 'ubc': ubc,
        'maskv': maskv, 'maskc': maskc,
        'b1_v': lbvv & (~maskv & 1), 'b1_m': maskv,
        'c1_v': lbvc & (~maskc & 1), 'c1_m': maskc,
    }

def plus_cbv(sv, sm, tv, tm, cv, cm):
    lbv = plus_c(sv, tv, cv)
    lbm = plus_c(sm, tm, cm)
    ub = plus(lbv, lbm)
    diff = ub ^ lbv
    mask = diff | sm | tm
    rv = lbv & ~mask
    return rv, mask

# Trace a specific case at each recursion level
cases = [(5, 2, 1, 4), (3, 4, 5, 2), (6, 1, 6, 1), (7, 0, 1, 6)]

for sv0, sm0, tv0, tm0 in cases:
    if sv0 & sm0 or tv0 & tm0: continue
    print(f"{'='*90}")
    print(f"self=Tn({sv0:04b},{sm0:04b}) t=Tn({tv0:04b},{tm0:04b})")
    sv, sm, tv, tm = sv0, sm0, tv0, tm0
    cv, cm = 0, 0
    level = 0
    while not (sv == 0 and sm == 0 and tv == 0 and tm == 0):
        d = tb_plus_c(hd(sv), hd(sm), hd(tv), hd(tm), cv, cm)
        nr_rv, nr_mask = plus_cbv(sv, sm, tv, tm, cv, cm)
        print(f"  Level {level}: sv={hd(sv)} sm={hd(sm)} tv={hd(tv)} tm={hd(tm)} cv={cv} cm={cm}")
        print(f"    rv0={d['rv0']} cv1={d['cv1']} rm0={d['rm0']} cm1={d['cm1']} "
              f"ubc1={d['ubc1']} ubc={d['ubc']}")
        print(f"    maskv={d['maskv']} maskc={d['maskc']} "
              f"c1=({d['c1_v']},{d['c1_m']})")
        print(f"    NR: rv={nr_rv} mask={nr_mask}")
        # KEY: when c1_m == 1, check cm1 vs ubc1
        if d['c1_m'] == 1:
            print(f"    *** c1.m=1: cm1={d['cm1']} ubc1={d['ubc1']} "
                  f"cm1 XOR ubc1 = {d['cm1'] ^ d['ubc1']}")
        sv, sm, tv, tm = tl(sv), tl(sm), tl(tv), tl(tm)
        cv, cm = d['c1_v'], d['c1_m']
        level += 1
    print()
