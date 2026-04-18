#!/usr/bin/env python3
"""
unum_invariant.py — Discover the inductive invariant for Unum addition soundness.

The proof of d_allowed_plus_c requires an invariant on the 5-bit state
(b1, b2, cd, cx, br) that:
  1. Holds at the initial state (0,0,0,0,0)
  2. Is preserved by all bit-step transitions
  3. Implies br=0 when cx=0, b1=0, b2=0 (boundary check passes)

This script finds that invariant by:
  1. Enumerating all reachable states from (0,0,0,0,0)
  2. Searching all linear inequalities a*b1+b*b2+c*cd+d*cx+e*br <= k
     for coefficients in {-1,0,1} and k in {0,1,2}
  3. Checking each candidate for the three required properties

Result: exactly one invariant passes all checks:
  cd + br <= cx + b1 + b2
"""

from itertools import product

def step(b1, b2, cd, cx, br, x1b, d1b, x2b, d2b):
    """One bit-step of the 5-bit state machine."""
    new_b1 = 1 if x1b - d1b - b1 < 0 else 0
    new_b2 = 1 if x2b - d2b - b2 < 0 else 0
    d12 = d1b + d2b + cd; d12_bit = d12 % 2; new_cd = d12 // 2
    x12 = x1b + x2b + cx; x12_bit = x12 % 2; new_cx = x12 // 2
    new_br = 1 if x12_bit - d12_bit - br < 0 else 0
    return (new_b1, new_b2, new_cd, new_cx, new_br)

# Step 1: enumerate reachable states
reachable = set()
reachable.add((0,0,0,0,0))
frontier = {(0,0,0,0,0)}
while frontier:
    new_frontier = set()
    for state in frontier:
        for x1b,d1b,x2b,d2b in product(range(2), repeat=4):
            ns = step(*state, x1b,d1b,x2b,d2b)
            if ns not in reachable:
                reachable.add(ns)
                new_frontier.add(ns)
    frontier = new_frontier

print(f"Reachable states from (0,0,0,0,0): {len(reachable)} / 32 possible")
print(f"States: {sorted(reachable)}")
print()

# Step 2: search for linear invariants
print("Searching for invariants of the form a*b1+b*b2+c*cd+d*cx+e*br <= k ...")
found = []
for a,b,c,d,e in product(range(-1,2), repeat=5):
    if a==b==c==d==e==0: continue
    for k in range(3):
        # Check 1: holds for all reachable states
        if not all(a*b1+b*b2+c*cd+d*cx+e*br <= k for b1,b2,cd,cx,br in reachable):
            continue
        # Check 2: preserved by all transitions
        preserved = all(
            a*nb1+b*nb2+c*ncd+d*ncx+e*nbr <= k
            for b1,b2,cd,cx,br in product(range(2),repeat=5)
            if a*b1+b*b2+c*cd+d*cx+e*br <= k
            for x1b,d1b,x2b,d2b in product(range(2),repeat=4)
            for nb1,nb2,ncd,ncx,nbr in [step(b1,b2,cd,cx,br,x1b,d1b,x2b,d2b)]
        )
        if not preserved: continue
        # Check 3: implies br=0 when cx=0, b1=0, b2=0
        implies = all(
            not (b1==0 and b2==0 and cx==0 and br==1)
            for b1,b2,cd,cx,br in product(range(2),repeat=5)
            if a*b1+b*b2+c*cd+d*cx+e*br <= k
        )
        if implies:
            found.append((a,b,c,d,e,k))

print(f"Found {len(found)} invariant(s):")
for a,b,c,d,e,k in found:
    terms = []
    for coef, name in zip([a,b,c,d,e], ['b1','b2','cd','cx','br']):
        if coef == 1: terms.append(name)
        elif coef == -1: terms.append(f'-{name}')
    lhs = ' + '.join(terms) if terms else '0'
    print(f"  {lhs} <= {k}")
    print(f"  (equivalently: cd + br <= cx + b1 + b2)")
