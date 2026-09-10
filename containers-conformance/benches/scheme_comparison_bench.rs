// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Head-to-head scheme comparison across the e-graph's column shapes, to decide
//! value-major's fate (goal step 4). For each shape it reports the achievable
//! bytes under every scheme: plain, index-major (write-order and sort-first, REAL
//! run counts from the verified encoders), and value-major at three code widths —
//! usize codes (as built, the known loser), byte-granular codes (u8/u16/u32 by
//! D), and optimally bit-packed codes (ceil(log2 D) bits). Index columns are
//! shown both stored full-width and bit-packed. This says whether a packed
//! value-major would ever beat plain / sorted-index-major on a real column, i.e.
//! whether it is worth building or should be retired.

use criterion::{Criterion, criterion_group, criterion_main};

use semi_persistent_containers_verus as verus;
use verus::diff_compress::{compress, compress_runs_sorted, compress_runs_writeorder};

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

fn ceil_div(a: usize, b: usize) -> usize {
    a.div_ceil(b)
}
fn bits_for(n: usize) -> usize {
    // bits to distinguish n symbols (>=1 so a single symbol still costs 1 bit-slot=0? use 1).
    if n <= 1 {
        0
    } else {
        (usize::BITS - (n - 1).leading_zeros()) as usize
    }
}
fn code_byte_width(distinct: usize) -> usize {
    if distinct <= 256 {
        1
    } else if distinct <= 65536 {
        2
    } else {
        4
    }
}

// -- workload shapes ---------------------------------------------------------

// union-find parent: N cells scattered over a large space, values drawn from D
// representatives (D << N). Value-major's target; index-major's worst case.
fn union_find(n: usize, distinct: u32) -> Vec<(u32, u32)> {
    let mut rng = XorShift(0x2545F491 ^ (n as u64).wrapping_mul(2654435761) ^ distinct as u64);
    let mut used = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let idx = (rng.next() % (n as u64 * 8)) as u32;
        if used.insert(idx) {
            out.push(((rng.next() % distinct as u64) as u32, idx));
        }
    }
    out
}

// contiguous batch: R runs of consecutive indices, values arbitrary (all
// distinct-ish). Index-major's target.
fn contiguous(n: usize, runs: usize) -> Vec<(u32, u32)> {
    let mut rng = XorShift(0x1D2C_6E43 ^ n as u64);
    let per = n / runs.max(1);
    let mut out = Vec::with_capacity(n);
    let mut base = 0u32;
    for _ in 0..runs {
        for o in 0..per {
            out.push(((rng.next() & 0xFFFF_FFFF) as u32, base + o as u32));
        }
        base += (per as u32) * 2; // gap so runs stay separate
    }
    let mut extra = base;
    while out.len() < n {
        out.push(((rng.next() as u32), extra));
        extra += 2;
    }
    out
}

// scattered unique: scattered indices, all-distinct values. Neither axis helps.
fn scattered_unique(n: usize) -> Vec<(u32, u32)> {
    let mut rng = XorShift(0x85EB_CA6B ^ n as u64);
    let mut used = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(n);
    let mut v = 1u32;
    while out.len() < n {
        let idx = (rng.next() % (n as u64 * 8)) as u32;
        if used.insert(idx) {
            out.push((v.wrapping_mul(2654435761), idx));
            v += 1;
        }
    }
    out
}

// -- sizing ------------------------------------------------------------------

fn distinct_values(d: &[(u32, u32)]) -> usize {
    d.iter()
        .map(|e| e.0)
        .collect::<std::collections::HashSet<_>>()
        .len()
}
fn max_index(d: &[(u32, u32)]) -> usize {
    d.iter().map(|e| e.1 as usize).max().unwrap_or(0)
}

fn report(shape: &str, d: &[(u32, u32)]) {
    let n = d.len();
    if n == 0 {
        return;
    }
    let t = 4usize; // u32 value
    let i = 4usize; // u32 index
    let dc = distinct_values(d);
    let maxidx = max_index(d);

    let plain = n * (t + i);

    // index-major, REAL run counts from the verified encoders.
    let wo = compress_runs_writeorder(&d.iter().map(|&(v, ix)| (v, ix as usize)).collect());
    let so = compress_runs_sorted::<u32, u32>(&d.to_vec());
    let wo_runs = wo.starts.len();
    let so_runs = so.starts.len();
    let idx_wo = wo_runs * 8 + n * t; // starts(usize) + vals
    let idx_so = so_runs * 8 + n * t;

    // value-major: dict + codes + indices, at three code widths; indices full or packed.
    let dict = dc * t;
    let codes_usize = n * 8;
    let codes_byte = n * code_byte_width(dc);
    let codes_packed = ceil_div(n * bits_for(dc), 8);
    let idxs_full = n * i;
    let idxs_packed = ceil_div(n * bits_for(maxidx + 1), 8);

    let vm_usize = dict + codes_usize + idxs_full;
    let vm_byte = dict + codes_byte + idxs_full;
    let vm_packed = dict + codes_packed + idxs_packed;

    // REAL value-major, from the shipped verified encoder (narrow codes):
    // dict + codes.byte_len() + idxs, so this is a realized size, not a formula.
    let df = compress::<u32, u32>(&d.to_vec());
    let vm_real = df.dict.len() * t + df.codes.byte_len() + df.idxs.len() * i;

    let r = |x: usize| x as f64 / plain as f64;
    eprintln!("  [{shape}] N={n} D={dc} maxidx={maxidx}");
    eprintln!("    plain            {plain:>9}  1.00x");
    eprintln!(
        "    idx-major wo     {idx_wo:>9}  {:.2}x  ({wo_runs} runs)",
        r(idx_wo)
    );
    eprintln!(
        "    idx-major sorted {idx_so:>9}  {:.2}x  ({so_runs} runs)",
        r(idx_so)
    );
    eprintln!("    val-major usize  {vm_usize:>9}  {:.2}x", r(vm_usize));
    eprintln!("    val-major byte   {vm_byte:>9}  {:.2}x", r(vm_byte));
    eprintln!(
        "    val-major REAL   {vm_real:>9}  {:.2}x  (shipped encoder)",
        r(vm_real)
    );
    eprintln!(
        "    val-major packed {vm_packed:>9}  {:.2}x  (codes {} bits, idx {} bits)",
        r(vm_packed),
        bits_for(dc),
        bits_for(maxidx + 1)
    );
}

fn bench_compare(_c: &mut Criterion) {
    eprintln!("\n=== scheme comparison (bytes; ratio vs plain, <1.0 wins) ===");
    report("union_find", &union_find(10_000, 64));
    report("union_find", &union_find(10_000, 4));
    report("contiguous", &contiguous(10_000, 100));
    report("scattered_unique", &scattered_unique(10_000));
    eprintln!();
}

criterion_group!(benches, bench_compare);
criterion_main!(benches);
