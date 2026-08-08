// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Is the verus `BPlusTreeSet::from_sorted` a bulk load, or `n` inserts?
//!
//! A cross-binary bench put the verus tree +2626% on `sorted_input_100k/
//! bplus_from_sorted`. That number alone is not trustworthy — this crate exists
//! partly because cross-binary A/Bs measure heap position and code layout
//! (`containers-verus/doc/design/11-layout-parity.md`). Two things here make the
//! reading falsifiable:
//!
//! 1. **One binary, both impls** — same heap, same codegen unit.
//! 2. **A scaling sweep** — the ratio is compared across three decades of `n`.
//!    Layout artifacts are a roughly constant factor; an algorithmic difference
//!    grows. That is the discriminator, and it is the one a previous
//!    investigation got wrong by blaming layout for a real regression.
//!
//! The `insert` columns are the control: if `from_sorted` tracks a plain insert
//! loop, it *is* an insert loop.
//!
//! **This probe answers only that question — do NOT read its ratios as parity.**
//! It has the fixed-order confound it warns about above, and once `from_sorted`
//! became a real bulk loader that confound dominated the row: this harness scored
//! the loader at 1.0x while `onesite_bplus.rs` (one call site, both orders) scored
//! the same build at +29%, and the disassembly confirmed the +29%. Its production
//! column swings 0.72-4.5 ns/key across runs of one binary. The scaling sweep is
//! still a valid *shape* test — a ratio growing across decades means an insert
//! loop — but for a level in the 10-30% band use `onesite_bplus.rs`.
//!
//! Run: `cargo run --release --example bulkload -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;
use std::time::Instant;

prod::define_id31! { pub struct PId / StoredPId, "p"; }
verus::define_id31! { pub struct VId / StoredVId, "v"; }

type ProdTree =
    prod::bplus::BPlusTreeSet<PId, prod::bplus::Layout256, prod::bplus::BinarySearch, false>;
type VerusTree =
    verus::bplus::BPlusTreeSet<VId, verus::bplus::Layout256, verus::bplus::BinarySearch, false>;

const REPS: usize = 5;

fn main() {
    println!(
        "{:>8} {:>11} {:>11} {:>7}  {:>11} {:>11} {:>7}  {:>11} {:>11} {:>7}",
        "n",
        "p_sorted",
        "v_sorted",
        "ratio",
        "p_ins_asc",
        "v_ins_asc",
        "ratio",
        "p_ins_rand",
        "v_ins_rand",
        "ratio"
    );
    for &n in &[1_000usize, 10_000, 100_000] {
        let pk: Vec<PId> = (0..n as u32).map(PId::new).collect();
        let vk: Vec<VId> = (0..n as u32).map(VId::new).collect();

        // Shuffled order: production's append fast path (keyed on `last_leaf`)
        // cannot fire, so both sides pay a full root-to-leaf descent per key.
        // If the ascending-order gap is the fast path, this ratio collapses.
        let mut sh: Vec<u32> = (0..n as u32).collect();
        let mut st = 0x2545_F491_4F6C_DD1Du64;
        for i in (1..sh.len()).rev() {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            let j = (st >> 33) as usize % (i + 1);
            sh.swap(i, j);
        }
        let pks: Vec<PId> = sh.iter().copied().map(PId::new).collect();
        let vks: Vec<VId> = sh.iter().copied().map(VId::new).collect();

        let (mut ps, mut vs, mut pi, mut vi) = (u128::MAX, u128::MAX, u128::MAX, u128::MAX);
        let (mut pr, mut vr) = (u128::MAX, u128::MAX);
        for _ in 0..REPS {
            let t = Instant::now();
            let a = ProdTree::from_sorted(&pk);
            ps = ps.min(t.elapsed().as_nanos());
            black_box(a.len());

            let t = Instant::now();
            let b = VerusTree::from_sorted(&vk);
            vs = vs.min(t.elapsed().as_nanos());
            black_box(b.len());

            let t = Instant::now();
            let mut c = ProdTree::new();
            for &k in &pk {
                c.insert(k);
            }
            pi = pi.min(t.elapsed().as_nanos());
            black_box(c.len());

            let t = Instant::now();
            let mut d = VerusTree::new();
            for &k in &vk {
                d.insert(k);
            }
            vi = vi.min(t.elapsed().as_nanos());
            black_box(d.len());

            let t = Instant::now();
            let mut e = ProdTree::new();
            for &k in &pks {
                e.insert(k);
            }
            pr = pr.min(t.elapsed().as_nanos());
            black_box(e.len());

            let t = Instant::now();
            let mut f = VerusTree::new();
            for &k in &vks {
                f.insert(k);
            }
            vr = vr.min(t.elapsed().as_nanos());
            black_box(f.len());
        }
        assert_eq!(ProdTree::from_sorted(&pk).len(), n, "prod contents");
        assert_eq!(VerusTree::from_sorted(&vk).len(), n, "verus contents");
        let us = |x: u128| x as f64 / 1000.0;
        println!(
            "{:>8} {:>9.1}µs {:>9.1}µs {:>6.1}x  {:>9.1}µs {:>9.1}µs {:>6.1}x  {:>9.1}µs {:>9.1}µs {:>6.1}x",
            n,
            us(ps),
            us(vs),
            vs as f64 / ps as f64,
            us(pi),
            us(vi),
            vi as f64 / pi as f64,
            us(pr),
            us(vr),
            vr as f64 / pr as f64
        );
    }
    println!(
        "\nRead: verus_sorted ~= verus_insert, and ratio growing with n, means\n\
         from_sorted loops inserts instead of bulk-loading leaves.\n\
         Do NOT read the ratio itself as parity -- fixed build order confounds it\n\
         by 10-30%. For a level, use `--example onesite_bplus`."
    );
}
