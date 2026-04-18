#!/usr/bin/env python3
"""Brute-force 4-bit Unum explorer.

Enumerates all valid 4-bit Unums, computes their concrete sets,
and checks plus/to_ean for correctness. Logs failures with full detail.
"""

BITS = 4
MAX = (1 << BITS) - 1  # 15

# ================================================================
# Unum representation
# ================================================================

def fields(w):
    """Yield (start, end) for each bitfield defined by w."""
    pos = 0
    while pos < BITS:
        # find next leader at or above pos
        found = None
        for i in range(pos, BITS):
            if (w >> i) & 1:
                found = i
                break
        if found is None:
            break
        start = found
        # find next leader above start
        end = BITS
        for i in range(start + 1, BITS):
            if (w >> i) & 1:
                end = i
                break
        yield (start, end)
        pos = end

def field_mask(start, end):
    width = end - start
    return ((1 << width) - 1) << start

def unum_set(v, w, x):
    """Compute the concrete set of a 4-bit Unum by enumeration."""
    result = set()
    # Generate all valid offsets d by iterating per-field values
    field_list = list(fields(w))
    if not field_list:
        return {v & MAX}

    def gen(idx, d_acc):
        if idx == len(field_list):
            result.add((v + d_acc) & MAX)
            return
        start, end = field_list[idx]
        m = field_mask(start, end)
        x_field = (x & m) >> start
        for val in range(x_field + 1):
            gen(idx + 1, d_acc | (val << start))

    gen(0, 0)
    return result

def unum_contains(v, w, x, y):
    """Membership test."""
    d = (y - v) & MAX
    for start, end in fields(w):
        m = field_mask(start, end)
        d_field = (d & m) >> start
        x_field = (x & m) >> start
        if d_field > x_field:
            return False
    return True

def is_valid_unum(v, w, x):
    """Check well-formedness: bit 0 of w must be 1, and for width>1 fields, MSB of max must be 1."""
    if not (w & 1):
        return False
    for start, end in fields(w):
        width = end - start
        x_field = (x >> start) & ((1 << width) - 1)
        if width == 1:
            pass  # max can be 0 or 1
        else:
            # leading bit must be 1
            if not (x_field >> (width - 1)):
                return False
    return True

# ================================================================
# Plus algorithm (from spec)
# ================================================================

def unum_plus(v1, w1, x1, v2, w2, x2):
    v = (v1 + v2) & MAX
    x12 = (x1 + x2) & MAX
    # The w formula from the spec
    w = w1 & w2 & ((~x12 & ~x1 & ~x2) | (x12 & (~x1 | ~x2)))
    w &= MAX
    return v, w, x12

# ================================================================
# to_ean conversion
# ================================================================

def ean_set(v, m):
    """Concrete set of Anum(v, m)."""
    result = set()
    # d & ~m == 0 means d is a subset of m's bits
    for d in range(MAX + 1):
        if d & ~m & MAX == 0:
            result.add((v + d) & MAX)
    return result

def unum_to_ean(v, w, x):
    return v, x  # current implementation

# ================================================================
# Enumerate and test
# ================================================================

def enum_valid_unums():
    """All valid 4-bit Unums."""
    results = []
    for v in range(1 << BITS):
        for w in range(1 << BITS):
            for x in range(1 << BITS):
                if is_valid_unum(v, w, x):
                    results.append((v, w, x))
    return results

def fmt_bin(n):
    return format(n, f'0{BITS}b')

def fmt_unum(v, w, x):
    return f"(v={fmt_bin(v)}, w={fmt_bin(w)}, x={fmt_bin(x)})"

def main():
    unums = enum_valid_unums()
    print(f"Valid 4-bit Unums: {len(unums)}")

    # Verify self-containment
    bad_self = 0
    for v, w, x in unums:
        s = unum_set(v, w, x)
        for y in range(1 << BITS):
            in_set = y in s
            in_contains = unum_contains(v, w, x, y)
            if in_set != in_contains:
                print(f"  CONTAINS BUG: {fmt_unum(v,w,x)} y={fmt_bin(y)} in_set={in_set} contains={in_contains}")
                bad_self += 1
    print(f"Self-containment bugs: {bad_self}")

    # Test plus
    print(f"\n{'='*70}")
    print(f"Testing plus on {len(unums)}^2 = {len(unums)**2} pairs...")
    plus_unsound = 0
    plus_total = 0
    first_failures = []

    for v1, w1, x1 in unums:
        for v2, w2, x2 in unums:
            plus_total += 1
            s1 = unum_set(v1, w1, x1)
            s2 = unum_set(v2, w2, x2)

            # Exact concrete sum set
            exact = set()
            for a in s1:
                for b in s2:
                    exact.add((a + b) & MAX)

            # Abstract plus
            rv, rw, rx = unum_plus(v1, w1, x1, v2, w2, x2)

            # What does the result contain?
            result_set = set()
            for y in range(1 << BITS):
                if unum_contains(rv, rw, rx, y):
                    result_set.add(y)

            # Soundness: exact must be subset of result_set
            missing = exact - result_set
            if missing:
                plus_unsound += 1
                if len(first_failures) < 20:
                    first_failures.append({
                        'u1': (v1, w1, x1), 'u2': (v2, w2, x2),
                        's1': s1, 's2': s2,
                        'exact': exact, 'result': (rv, rw, rx),
                        'result_set': result_set, 'missing': missing,
                        'extra': result_set - exact,
                    })

    print(f"Plus unsound: {plus_unsound} / {plus_total}")

    # Separate: how many failures are due to x overflow vs w formula?
    plus_overflow_unsound = 0
    plus_no_overflow_unsound = 0
    no_overflow_failures = []
    for v1, w1, x1 in unums:
        for v2, w2, x2 in unums:
            s1 = unum_set(v1, w1, x1)
            s2 = unum_set(v2, w2, x2)
            exact = set()
            for a in s1:
                for b in s2:
                    exact.add((a + b) & MAX)
            rv, rw, rx = unum_plus(v1, w1, x1, v2, w2, x2)
            result_set = set()
            for y in range(1 << BITS):
                if unum_contains(rv, rw, rx, y):
                    result_set.add(y)
            missing = exact - result_set
            if missing:
                if (x1 + x2) > MAX:
                    plus_overflow_unsound += 1
                else:
                    plus_no_overflow_unsound += 1
                    if len(no_overflow_failures) < 10:
                        no_overflow_failures.append({
                            'u1': (v1, w1, x1), 'u2': (v2, w2, x2),
                            's1': s1, 's2': s2,
                            'exact': exact, 'result': (rv, rw, rx),
                            'result_set': result_set, 'missing': missing,
                        })

    print(f"  overflow failures:    {plus_overflow_unsound}")
    print(f"  no-overflow failures: {plus_no_overflow_unsound}")

    if no_overflow_failures:
        print(f"\n  --- Non-overflow failures ---")
        for i, f in enumerate(no_overflow_failures):
            v1, w1, x1 = f['u1']
            v2, w2, x2 = f['u2']
            rv, rw, rx = f['result']
            x12 = (x1 + x2) & MAX
            print(f"  {i+1}. u1={fmt_unum(v1,w1,x1)} set={sorted(f['s1'])}")
            print(f"     u2={fmt_unum(v2,w2,x2)} set={sorted(f['s2'])}")
            print(f"     exact={sorted(f['exact'])}")
            print(f"     result={fmt_unum(rv,rw,rx)} set={sorted(f['result_set'])}")
            print(f"     MISSING={sorted(f['missing'])}")
            print(f"     x1+x2={x1+x2} x12={x12} (no overflow)")
    else:
        print(f"\n  ALL non-overflow cases are SOUND!")
    print()

    for i, f in enumerate(first_failures):
        v1, w1, x1 = f['u1']
        v2, w2, x2 = f['u2']
        rv, rw, rx = f['result']
        print(f"--- Failure {i+1} ---")
        print(f"  u1 = {fmt_unum(v1,w1,x1)}  set={sorted(f['s1'])}")
        print(f"  u2 = {fmt_unum(v2,w2,x2)}  set={sorted(f['s2'])}")
        print(f"  exact sum = {sorted(f['exact'])}")
        print(f"  result    = {fmt_unum(rv,rw,rx)}  set={sorted(f['result_set'])}")
        print(f"  MISSING   = {sorted(f['missing'])}")
        print(f"  extra     = {sorted(f['extra'])}")

        # Show the intermediate computation
        x12 = (x1 + x2) & MAX
        w_raw = w1 & w2
        no_carry = (~x12 & ~x1 & ~x2) | (x12 & (~x1 | ~x2))
        no_carry &= MAX
        w_final = w_raw & no_carry & MAX
        print(f"  x1={fmt_bin(x1)} x2={fmt_bin(x2)} x12={fmt_bin(x12)}")
        print(f"  w1={fmt_bin(w1)} w2={fmt_bin(w2)} w1&w2={fmt_bin(w_raw & MAX)}")
        print(f"  no_carry_formula={fmt_bin(no_carry)} w_final={fmt_bin(w_final)}")

        # What SHOULD w be? For each bit in w1&w2, check if a carry actually
        # crosses that boundary in any concrete addition of field values.
        # A boundary at bit i is safe if for all d1 in fields(x1) and d2 in fields(x2),
        # the carry out of bit i-1 in (d1+d2) is always 0.
        print(f"  --- carry analysis ---")
        for bit in range(BITS):
            if not ((w_raw >> bit) & 1):
                continue
            # Check: can x1[0:bit] + x2[0:bit] produce a carry into bit?
            mask_below = (1 << bit) - 1 if bit > 0 else 0
            max_below = (x1 & mask_below) + (x2 & mask_below) if bit > 0 else 0
            carries = max_below >= (1 << bit) if bit > 0 else False
            w_kept = (w_final >> bit) & 1
            print(f"    bit {bit}: x1_below={x1 & mask_below} x2_below={x2 & mask_below} "
                  f"max_sum_below={max_below} carries={carries} w_kept={w_kept} "
                  f"{'WRONG' if carries and w_kept else 'ok' if carries != (not w_kept) else '??'}")
        print()

    # Test to_ean
    print(f"\n{'='*70}")
    print(f"Testing to_ean...")
    ean_unsound = 0
    ean_failures = []
    for v, w, x in unums:
        us = unum_set(v, w, x)
        av, am = unum_to_ean(v, w, x)
        es = ean_set(av, am)
        missing = us - es
        if missing:
            ean_unsound += 1
            if len(ean_failures) < 10:
                ean_failures.append({
                    'unum': (v, w, x), 'unum_set': us,
                    'ean': (av, am), 'ean_set': es,
                    'missing': missing,
                })

    print(f"to_ean unsound: {ean_unsound} / {len(unums)}")
    for i, f in enumerate(ean_failures):
        v, w, x = f['unum']
        av, am = f['ean']
        print(f"  {fmt_unum(v,w,x)} set={sorted(f['unum_set'])}")
        print(f"    -> EAn(v={fmt_bin(av)}, m={fmt_bin(am)}) set={sorted(f['ean_set'])}")
        print(f"    MISSING: {sorted(f['missing'])}")
        # Show fields
        for start, end in fields(w):
            m = field_mask(start, end)
            print(f"    field [{start}:{end}] max={fmt_bin((x & m) >> start)}")

def test_carry_based_w():
    """Test plus with w computed by checking actual carry at each boundary."""
    unums = enum_valid_unums()

    def unum_plus_carry_w(v1, w1, x1, v2, w2, x2):
        v = (v1 + v2) & MAX
        x12_full = x1 + x2
        x12 = x12_full & MAX
        if x12_full > MAX:
            return 0, 1, MAX  # total overflow → top
        w_cand = w1 & w2
        w_result = 0
        for bit in range(BITS):
            if not ((w_cand >> bit) & 1):
                continue
            if bit == 0:
                w_result |= 1
            else:
                mask_below = (1 << bit) - 1
                sum_below = (x1 & mask_below) + (x2 & mask_below)
                if sum_below < (1 << bit):
                    w_result |= (1 << bit)
        return v, w_result, x12

    print(f"\n{'='*70}")
    print("Testing plus with CARRY-BASED w...")
    unsound = 0
    imprecise = 0
    total = 0
    failures = []
    for v1, w1, x1 in unums:
        for v2, w2, x2 in unums:
            total += 1
            s1 = unum_set(v1, w1, x1)
            s2 = unum_set(v2, w2, x2)
            exact = set()
            for a in s1:
                for b in s2:
                    exact.add((a + b) & MAX)
            rv, rw, rx = unum_plus_carry_w(v1, w1, x1, v2, w2, x2)
            result_set = set()
            for y in range(1 << BITS):
                if unum_contains(rv, rw, rx, y):
                    result_set.add(y)
            missing = exact - result_set
            extra = result_set - exact
            if missing:
                unsound += 1
                if len(failures) < 5:
                    failures.append({
                        'u1': (v1, w1, x1), 'u2': (v2, w2, x2),
                        's1': s1, 's2': s2,
                        'exact': exact, 'result': (rv, rw, rx),
                        'result_set': result_set, 'missing': missing,
                    })
            elif extra:
                imprecise += 1

    print(f"  unsound={unsound}, imprecise={imprecise} / {total}")
    if failures:
        for i, f in enumerate(failures):
            v1, w1, x1 = f['u1']
            v2, w2, x2 = f['u2']
            rv, rw, rx = f['result']
            print(f"  {i+1}. u1={fmt_unum(v1,w1,x1)} set={sorted(f['s1'])}")
            print(f"     u2={fmt_unum(v2,w2,x2)} set={sorted(f['s2'])}")
            print(f"     exact={sorted(f['exact'])}")
            print(f"     result={fmt_unum(rv,rw,rx)} set={sorted(f['result_set'])}")
            print(f"     MISSING={sorted(f['missing'])}")
    else:
        print(f"  ALL SOUND!")

if __name__ == '__main__':
    main()
    test_carry_based_w()
