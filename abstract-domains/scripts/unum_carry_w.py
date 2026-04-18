#!/usr/bin/env python3
"""
unum_carry_w.py — Discover the correct w formula for Unum addition.

The spec proposed:
  w = w1 & w2 & ((~x12 & ~x1 & ~x2) | (x12 & (~x1 | ~x2)))

This script shows that formula is wrong (63% failure rate on 4-bit Unums)
and discovers the correct carry-out formula:
  cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))
  w = (w1 & w2) & ~(cout << 1)

Verified sound on all 1,183,744 pairs of valid 4-bit Unums.
"""

BITS = 4
MAX = (1 << BITS) - 1

def fields(w):
    pos = 0
    while pos < BITS:
        found = None
        for i in range(pos, BITS):
            if (w >> i) & 1: found = i; break
        if found is None: break
        start = found
        end = BITS
        for i in range(start+1, BITS):
            if (w >> i) & 1: end = i; break
        yield (start, end)
        pos = end

def field_mask(start, end):
    return ((1 << (end-start)) - 1) << start

def unum_set(v, w, x):
    result = set()
    fl = list(fields(w))
    if not fl: return {v & MAX}
    def gen(idx, d):
        if idx == len(fl): result.add((v+d)&MAX); return
        s,e = fl[idx]; m = field_mask(s,e); xf = (x&m)>>s
        for val in range(xf+1): gen(idx+1, d|(val<<s))
    gen(0,0); return result

def is_valid(v,w,x):
    if not (w&1): return False
    for s,e in fields(w):
        width = e-s; xf = (x>>s)&((1<<width)-1)
        if width > 1 and not (xf>>(width-1)): return False
    return True

def spec_plus(v1,w1,x1,v2,w2,x2):
    """The spec's original (wrong) formula."""
    v = (v1+v2)&MAX; x12 = (x1+x2)&MAX
    w = w1&w2&((~x12&~x1&~x2)|(x12&(~x1|~x2)))&MAX
    return v, w, x12

def carry_plus(v1,w1,x1,v2,w2,x2):
    """The correct carry-out formula."""
    v = (v1+v2)&MAX
    x12_full = x1+x2
    x12 = x12_full&MAX
    if x12_full > MAX: return 0, 1, MAX  # overflow -> top
    cout = (x1&x2)|((x1|x2)&~x12)&MAX
    carry_in = (cout<<1)&MAX
    w = (w1&w2)&~carry_in&MAX
    return v, w, x12

def contains(v,w,x,y):
    d = (y-v)&MAX
    for s,e in fields(w):
        m = field_mask(s,e)
        if ((d&m)>>s) > ((x&m)>>s): return False
    return True

unums = [(v,w,x) for v in range(1<<BITS) for w in range(1<<BITS)
         for x in range(1<<BITS) if is_valid(v,w,x)]
print(f"Valid 4-bit Unums: {len(unums)}")

total = len(unums)**2
spec_unsound = carry_unsound = 0
for v1,w1,x1 in unums:
    for v2,w2,x2 in unums:
        s1 = unum_set(v1,w1,x1); s2 = unum_set(v2,w2,x2)
        exact = {(a+b)&MAX for a in s1 for b in s2}
        for formula, counter in [(spec_plus, 'spec'), (carry_plus, 'carry')]:
            rv,rw,rx = formula(v1,w1,x1,v2,w2,x2)
            rs = {y for y in range(1<<BITS) if contains(rv,rw,rx,y)}
            if exact - rs:
                if counter == 'spec': spec_unsound += 1
                else: carry_unsound += 1

print(f"\nSpec formula:  {spec_unsound:,} / {total:,} unsound ({100*spec_unsound/total:.0f}%)")
print(f"Carry formula: {carry_unsound:,} / {total:,} unsound ({100*carry_unsound/total:.0f}%)")
print()
if carry_unsound == 0:
    print("Carry formula is SOUND on all pairs.")
    print()
    print("The correct formula:")
    print("  cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))")
    print("  w = (w1 & w2) & ~(cout << 1)")
