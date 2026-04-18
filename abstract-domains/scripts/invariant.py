#!/usr/bin/env python3
"""Search for per-bit invariants relating the non-recursive and recursive
carry structures. Tests candidate invariants across all 3-bit cases."""

def hd(n): return n % 2
def tl(n): return n // 2
def b_plus(a, b, c):
    s = a + b + c
    return (s % 2, s // 2)

def tb_plus_c(sv, sm, tv, tm, cv, cm):
    lbvv, lbvc = b_plus(sv, tv, cv)
    lbmv, lbmc = b_plus(sm, tm, cm)
    ubv, ubc1 = b_plus(lbvv, lbmv, 0)
    ubc, _ = b_plus(lbvc, lbmc, ubc1)
    maskv = (ubv ^ lbvv) | sm | tm
    maskc = ubc ^ lbvc
    c1_v = lbvc & (~maskc & 1)
    c1_m = maskc
    return {
        'rv0': lbvv, 'cv1': lbvc,
        'rm0': lbmv, 'cm1': lbmc,
        'ub0': ubv, 'ubc1': ubc1, 'ubc': ubc,
        'maskv': maskv, 'maskc': maskc,
        'c1_v': c1_v, 'c1_m': c1_m,
    }

# Test candidate invariants
invariants = {
    'carry_u <= cm':       lambda d: d['ubc1'] <= d['cm1'],
    'cm==0 ==> carry_u==0': lambda d: d['cm1'] == 1 or d['ubc1'] == 0,
    'cm==1 ==> mask==1':   lambda d: d['cm1'] == 0 or d['maskv'] == 1,
    'c1.m==1 ==> cm1 XOR ubc1': lambda d: d['c1_m'] == 0 or (d['cm1'] != d['ubc1']),
    'cv1==1 ==> cm1==ubc1': lambda d: d['cv1'] == 0 or (d['cm1'] == d['ubc1']),
}

BITS = 3
for name, check in invariants.items():
    holds = True
    for sv in range(2):
        for sm in range(2):
            if sv & sm: continue
            for tv in range(2):
                for tm in range(2):
                    if tv & tm: continue
                    for cv in range(2):
                        for cm in range(2):
                            if cv & cm: continue
                            d = tb_plus_c(sv, sm, tv, tm, cv, cm)
                            if not check(d):
                                holds = False
    status = "HOLDS" if holds else "FAILS"
    print(f"  {status}: {name}")
