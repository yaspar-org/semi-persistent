// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
/// Demo: verified abstract interpreter with branches and alignment.
use crate::domains::d8::{ExecAnum, ExecTnum, ExecUnum, Interval, ReducedProduct};

fn tn(v: u8, m: u8) -> String {
    (0..8)
        .rev()
        .map(|i| {
            if (m >> i) & 1 == 1 {
                'X'
            } else if (v >> i) & 1 == 1 {
                '1'
            } else {
                '0'
            }
        })
        .collect()
}
fn an(v: u8, m: u8) -> String {
    let b: String = (0..8)
        .rev()
        .map(|i| if (v >> i) & 1 == 1 { '1' } else { '0' })
        .collect();
    if m == 0 {
        b
    } else {
        let k: String = (0..8)
            .rev()
            .map(|i| if (m >> i) & 1 == 1 { 'X' } else { '0' })
            .collect();
        format!("{}+{}", b, k)
    }
}
fn iv(lo: u8, hi: u8) -> String {
    if lo == hi {
        format!("{}", lo)
    } else {
        format!("[{},{}]", lo, hi)
    }
}
fn show(label: &str, t: &ReducedProduct) {
    println!(
        "  {:36} Tn={}  An={}  Iv={}",
        label,
        tn(t.tnum.val, t.tnum.mask),
        an(t.anum.base, t.anum.span),
        iv(t.interval.lo, t.interval.hi)
    );
}

/// Narrow ReducedProduct with "value < bound" (branch taken).
fn assume_lt(t: &ReducedProduct, bound: u8) -> ReducedProduct {
    let iv = Interval {
        lo: t.interval.lo,
        hi: if bound == 0 { 0 } else { bound - 1 },
    };
    ReducedProduct {
        tnum: t.tnum,
        anum: t.anum,
        interval: iv,
        unum: ExecUnum::from_interval(&iv),
    }
    .reduce()
}

/// Narrow ReducedProduct with "value >= bound" (branch taken).
fn assume_ge(t: &ReducedProduct, bound: u8) -> ReducedProduct {
    let iv = Interval {
        lo: bound,
        hi: t.interval.hi,
    };
    ReducedProduct {
        tnum: t.tnum,
        anum: t.anum,
        interval: iv,
        unum: ExecUnum::from_interval(&iv),
    }
    .reduce()
}

/// AND with constant (precise: forces known-zero bits).
fn mask(t: &ReducedProduct, c: u8) -> ReducedProduct {
    let iv = Interval {
        lo: t.interval.lo & c,
        hi: t.interval.hi.min(c),
    };
    ReducedProduct {
        tnum: ExecTnum {
            val: t.tnum.val & c,
            mask: t.tnum.mask & c,
        },
        anum: ExecAnum {
            base: 0,
            span: (t.anum.base.wrapping_add(t.anum.span)) & c,
        },
        interval: iv,
        unum: ExecUnum::from_interval(&iv),
    }
    .reduce()
}

pub fn demo() {
    println!("╔══════════════════════════════════════════════════════════════════════════════╗");
    println!(
        "║  semi-persistent-abstract-domains — Verified Abstract Domains Demo (8-bit)                                ║"
    );
    println!("╚══════════════════════════════════════════════════════════════════════════════╝");

    // ── Example 1: Branch narrows bounds, then bounds check ──
    println!("\n━━━ Example 1: Branch-based bounds narrowing ━━━");
    println!("  u8 x = packet_read();          // unknown");
    println!("  if (x < 16) {{                   // branch narrows to [0,15]");
    println!("    buf[x] = 1;                   // safe: x < 16");
    println!("  }}");
    println!();

    let x = ReducedProduct {
        tnum: ExecTnum { val: 0, mask: 0xFF },
        anum: ExecAnum {
            base: 0,
            span: 0xFF,
        },
        interval: Interval { lo: 0, hi: 255 },
        unum: ExecUnum::top(),
    };
    show("x = packet_read():", &x);
    let x_lt16 = assume_lt(&x, 16);
    show("if (x < 16):  // branch taken", &x_lt16);
    println!("  → buf[x] safe? max={} < 16 ✓", x_lt16.max_val());

    // ── Example 2: Alignment via shift ──
    println!("\n━━━ Example 2: Align pointer via shift ━━━");
    println!("  u8 ptr = packet_read();         // unknown byte");
    println!("  u8 aligned = (ptr >> 2) << 2;   // clear low 2 bits → 4-aligned");
    println!("  // VERIFY: aligned & 0x03 == 0");
    println!();

    let ptr = ReducedProduct {
        tnum: ExecTnum { val: 0, mask: 0xFF },
        anum: ExecAnum {
            base: 0,
            span: 0xFF,
        },
        interval: Interval { lo: 0, hi: 255 },
        unum: ExecUnum::top(),
    };
    show("ptr = packet_read():", &ptr);
    let shifted_r = ptr.rsh().rsh();
    show("ptr >> 2:", &shifted_r);
    let aligned = shifted_r.lsh().lsh();
    show("(ptr >> 2) << 2:", &aligned);
    let low_bits = mask(&aligned, 0x03);
    show("aligned & 0x03:", &low_bits);
    let is_aligned = low_bits.tnum.val == 0 && low_bits.tnum.mask == 0;
    println!(
        "  → 4-byte aligned? {} (low 2 bits = {})",
        if is_aligned { "YES ✓" } else { "NO ✗" },
        tn(low_bits.tnum.val, low_bits.tnum.mask)
    );

    // ── Example 3: Loop counter with branch + Anum precision ──
    println!("\n━━━ Example 3: Loop counter — branch + Anum ━━━");
    println!("  u8 i = 0;");
    println!("  u8 x = flag & 1;               // 0 or 1");
    println!("  while (i < 4) {{ i = i + 1; x = x + 2; }}");
    println!("  // After loop: what do we know about x?");
    println!();

    let mut i_val = ReducedProduct::constant(0);
    let flag = ReducedProduct {
        tnum: ExecTnum { val: 0, mask: 1 },
        anum: ExecAnum { base: 0, span: 1 },
        interval: Interval { lo: 0, hi: 1 },
        unum: ExecUnum::from_interval(&Interval { lo: 0, hi: 1 }),
    };
    let mut x_val = flag;
    let two = ReducedProduct::constant(2);
    let one = ReducedProduct::constant(1);

    show("x = flag & 1:", &x_val);
    for iter in 0..4 {
        // Loop head: assume i < 4
        i_val = assume_lt(&i_val, 4);
        // Loop body
        i_val = i_val.add(&one);
        x_val = x_val.add(&two);
        show(&format!("  iter {}: x = x + 2:", iter), &x_val);
    }
    // After loop: i >= 4
    println!();
    show("after loop, x:", &x_val);
    println!(
        "  Tnum: {} ({} uncertain bits)",
        tn(x_val.tnum.val, x_val.tnum.mask),
        x_val.tnum.mask.count_ones()
    );
    println!(
        "  Anum: {} (base={}, exactly +0 or +1)",
        an(x_val.anum.base, x_val.anum.span),
        x_val.anum.base
    );
    println!(
        "  Interval: {} (tight!)",
        iv(x_val.interval.lo, x_val.interval.hi)
    );

    // ── Example 4: Packet parsing with length check ──
    println!("\n━━━ Example 4: Packet parsing with bounds ━━━");
    println!("  u8 hdr_len = pkt[0] & 0x0F;    // 4-bit length field");
    println!("  if (hdr_len >= 4) {{              // minimum header = 4");
    println!("    u8 payload = hdr_len - 4;     // payload offset");
    println!("    if (payload < 8) {{             // fits in buffer");
    println!("      read(buf + payload);        // safe!");
    println!("    }}");
    println!("  }}");
    println!();

    let hdr_len = ReducedProduct {
        tnum: ExecTnum { val: 0, mask: 0x0F },
        anum: ExecAnum {
            base: 0,
            span: 0x0F,
        },
        interval: Interval { lo: 0, hi: 15 },
        unum: ExecUnum::from_interval(&Interval { lo: 0, hi: 15 }),
    };
    show("hdr_len = pkt[0] & 0x0F:", &hdr_len);

    let hdr_ge4 = assume_ge(&hdr_len, 4);
    show("if (hdr_len >= 4):", &hdr_ge4);

    let payload = hdr_ge4.sub(&ReducedProduct::constant(4));
    show("payload = hdr_len - 4:", &payload);

    let payload_lt8 = assume_lt(&payload, 8);
    show("if (payload < 8):", &payload_lt8);
    println!("  → buf+payload safe? max={} < 8 ✓", payload_lt8.max_val());

    // ── Example 5: Alignment + offset within aligned region ──
    println!("\n━━━ Example 5: Aligned access within struct ━━━");
    println!("  u8 base = (ptr >> 3) << 3;      // 8-aligned base");
    println!("  u8 field = base + 4;            // offset to field at +4");
    println!("  // VERIFY: field is 4-aligned");
    println!();

    let base = ReducedProduct {
        tnum: ExecTnum {
            val: 0,
            mask: 0b11111000,
        },
        anum: ExecAnum {
            base: 0,
            span: 0b11111000,
        },
        interval: Interval { lo: 0, hi: 248 },
        unum: ExecUnum::from_interval(&Interval { lo: 0, hi: 248 }),
    };
    show("base (8-aligned):", &base);
    let field = base.add(&ReducedProduct::constant(4));
    show("field = base + 4:", &field);
    let field_low2 = mask(&field, 0x03);
    show("field & 0x03:", &field_low2);
    let aligned4 = field_low2.tnum.val == 0 && field_low2.tnum.mask == 0;
    println!(
        "  → 4-byte aligned? {} (low bits = {})",
        if aligned4 { "YES ✓" } else { "NO ✗" },
        tn(field_low2.tnum.val, field_low2.tnum.mask)
    );
}
