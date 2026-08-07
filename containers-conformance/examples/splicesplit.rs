// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Where does `perf_gate::class_splice`'s +55% live?
//!
//! The gate's class-ring rows read: `class_walk` −0.3% (parity),
//! `class_merge_restore` −8.5% (verus faster), but untracked `class_splice`
//! **+55%**. A delta that big on a row whose two arms do the same two stores is
//! not the layout artifact of `doc/design/11-layout-parity.md` — and it is
//! confined to the surgery, since the walk over the same rings is at parity.
//!
//! The consumer's post-swap `splice_classes` is
//!
//!     ring.splice(survivor, absorbed);              // swap the two `next`s
//!     let mut p = ring.payload_of(absorbed);        // re-READ the cell
//!     p.set_none();
//!     ring.set_payload(absorbed, p);                // re-WRITE the cell
//!
//! whereas the pre-swap hand-rolled version did two `Vec::set`s total, each
//! carrying the new `next` **and** the payload in one full-cell store. So the
//! suspicion is store count, not `splice` itself: verus touches the absorbed
//! cell twice (once inside `splice`, once for the presence bit) where production
//! touched it once.
//!
//! This probe separates the two candidate costs by timing `splice` ALONE against
//! the full `splice` + payload-clear sequence, and against a payload-carrying
//! splice that folds the presence-bit clear into the two stores the surgery
//! already performs.
//!
//! ## What it found
//!
//! The +55% split into two unequal halves, and only one of them was real:
//!
//!   * **`splice` alone was +23%** — and the cause was NOT the ring code. Verus's
//!     `InlineStore::set_raw` preserved the inline capture flag across every
//!     write (read the old repr's tag, re-set it on the new one) where
//!     production guards that with `TRACK &&` (`containers/src/diff_store.rs:263`)
//!     — dead work in an untracked container. `DiffStore::set_raw`'s
//!     postcondition asserted flag preservation unconditionally, which is what
//!     forced it; weakening that clause to `TRACK ==>` (matching `push`/`pop`,
//!     which were already stated that way) let the guard back in. `splice` alone
//!     went +23% → **−30%**. This is the third time an `inline`/`TRACK` detail of
//!     production's has turned out to be interface rather than incident.
//!
//!   * **The separate payload write was +17%** — and folding it into the splice
//!     did **nothing** (5.58 vs 5.59 µs). LLVM forwards the redundant load, so
//!     the `payload_of`/`set_payload` pair costs what the folded form costs. The
//!     payload-carrying `splice_with_payloads` was implemented, verified (it is
//!     free proof-wise: `wf` does not constrain payloads), measured, and then
//!     REVERTED — a wider verified API is not worth carrying for a delta that
//!     does not exist. The `VerusSpliceAndClear` arm below is what the consumer
//!     does; the `VerusSpliceWithPayloads` arm is kept only so the negative
//!     result stays reproducible rather than becoming folklore.
//!
//! Run: `cargo run --release --example splicesplit -p containers-conformance`.
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

// The shared pre-swap baseline (see `prod_class_ring`'s doc for why it is shared).
use containers_conformance::prod_class_ring::{self as pring, PNodeId};
use verus::opt::DenseId as _;

verus::define_id31! { pub struct VNodeId / StoredVNodeId, "n"; }

type ProdRing = pring::ProdRing<false>;
type VerusRing = verus::CircularList<verus::Opt<u32>, VNodeId, false>;

const RING_N: usize = 20_000;
const MERGES: usize = RING_N / 2;

/// Which arm/variant to time.
#[derive(Copy, Clone, PartialEq)]
enum Arm {
    /// Production's hand-rolled surgery: two full-cell stores.
    Prod,
    /// `CircularList::splice` alone (no payload clear) — not what the consumer
    /// does, but it isolates the verified surgery's own cost.
    VerusSpliceOnly,
    /// `splice` + a separate payload read-modify-write — what the consumer did
    /// BEFORE `splice_with_payloads` existed. Kept as the row that shows why the
    /// payload-carrying form is worth having.
    VerusSpliceAndClear,
    /// The folded form that was tried and reverted: the presence-bit clear
    /// carried through the splice, so the merge costs two stores total. Emulated
    /// here through the public API (`set_payload` first, then `splice` — which
    /// provably preserves payloads, so the order is observationally identical)
    /// because `splice_with_payloads` no longer exists: it measured no faster.
    VerusSpliceWithPayloads,
}

fn time_once(arm: Arm) -> f64 {
    match arm {
        Arm::Prod => {
            let mut ring: ProdRing = pring::build(RING_N);
            let t = std::time::Instant::now();
            for i in 0..MERGES {
                pring::splice(
                    &mut ring,
                    PNodeId::new(2 * i as u32),
                    PNodeId::new(2 * i as u32 + 1),
                );
            }
            let us = t.elapsed().as_nanos() as f64 / 1000.0;
            black_box(ring.len());
            us
        }
        Arm::VerusSpliceOnly => {
            let mut ring: VerusRing = VerusRing::new();
            for i in 0..RING_N {
                ring.add_singleton(verus::Opt::some(i as u32));
            }
            let t = std::time::Instant::now();
            for i in 0..MERGES {
                ring.splice(VNodeId::from_usize(2 * i), VNodeId::from_usize(2 * i + 1));
            }
            let us = t.elapsed().as_nanos() as f64 / 1000.0;
            black_box(ring.len());
            us
        }
        Arm::VerusSpliceAndClear => {
            let mut ring: VerusRing = VerusRing::new();
            for i in 0..RING_N {
                ring.add_singleton(verus::Opt::some(i as u32));
            }
            let t = std::time::Instant::now();
            for i in 0..MERGES {
                let (s, a) = (VNodeId::from_usize(2 * i), VNodeId::from_usize(2 * i + 1));
                ring.splice(s, a);
                let mut p = ring.payload_of(a);
                p.set_none();
                ring.set_payload(a, p);
            }
            let us = t.elapsed().as_nanos() as f64 / 1000.0;
            black_box(ring.len());
            us
        }
        Arm::VerusSpliceWithPayloads => {
            let mut ring: VerusRing = VerusRing::new();
            for i in 0..RING_N {
                ring.add_singleton(verus::Opt::some(i as u32));
            }
            let t = std::time::Instant::now();
            for i in 0..MERGES {
                let (s, a) = (VNodeId::from_usize(2 * i), VNodeId::from_usize(2 * i + 1));
                let mut ap = ring.payload_of(a);
                ap.set_none();
                ring.set_payload(a, ap);
                ring.splice(s, a);
            }
            let us = t.elapsed().as_nanos() as f64 / 1000.0;
            black_box(ring.len());
            us
        }
    }
}

fn best(arm: Arm) -> f64 {
    let mut b = f64::MAX;
    for _ in 0..40 {
        b = b.min(time_once(arm));
    }
    b
}

fn main() {
    // Interleave the three arms per sample so none is systematically second on a
    // warmed heap (the confound `perf::compare` exists to remove).
    let mut bp = f64::MAX;
    let mut bs = f64::MAX;
    let mut bc = f64::MAX;
    let mut bw = f64::MAX;
    const ARMS: [Arm; 4] = [
        Arm::Prod,
        Arm::VerusSpliceOnly,
        Arm::VerusSpliceAndClear,
        Arm::VerusSpliceWithPayloads,
    ];
    for s in 0..40 {
        // Rotate the lead each sample so no arm is systematically last.
        for k in 0..ARMS.len() {
            let arm = ARMS[(s + k) % ARMS.len()];
            let us = time_once(arm);
            match arm {
                Arm::Prod => bp = bp.min(us),
                Arm::VerusSpliceOnly => bs = bs.min(us),
                Arm::VerusSpliceAndClear => bc = bc.min(us),
                Arm::VerusSpliceWithPayloads => bw = bw.min(us),
            }
        }
    }
    let _ = best; // kept for ad-hoc single-arm probing

    println!("{MERGES} ring merges over {RING_N} singletons, untracked:\n");
    println!("{:<44} {:>10} {:>10}", "variant", "us", "vs prod");
    println!(
        "{:<44} {:>10.2} {:>10}",
        "prod: 2 full-cell stores", bp, "--"
    );
    for (label, us) in [
        ("verus: splice alone", bs),
        ("verus: splice + payload write (consumer)", bc),
        ("verus: payload folded into splice (reverted)", bw),
    ] {
        println!(
            "{:<44} {:>10.2} {:>+9.1}%",
            label,
            us,
            (us / bp - 1.0) * 100.0
        );
    }
    println!(
        "\nseparate-payload-write surcharge: {:+.1}% of prod ({:+.2} us); \
         folded into the splice: {:+.1}% ({:+.2} us)",
        (bc - bs) / bp * 100.0,
        bc - bs,
        (bw - bs) / bp * 100.0,
        bw - bs
    );
}
