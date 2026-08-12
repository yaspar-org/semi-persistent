// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! ListArena differential trace: production vs verus on identical randomized
//! operation sequences (new_list / append / prepend / len / iter / splice /
//! mark / restore) with typed 31-bit ids on both sides. The container pair
//! previously missing from the differential harness.

use containers_conformance::Rng;
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

prod::define_id31! { pub struct PElem / StoredPElem, "e"; }
prod::define_id31! { pub struct PList / StoredPList, "l"; }
prod::define_id31! { pub struct PNode / StoredPNode, "n"; }
verus::define_id31! { pub struct VElem / StoredVElem, "e"; }
verus::define_id31! { pub struct VList / StoredVList, "l"; }
verus::define_id31! { pub struct VNode / StoredVNode, "n"; }

fn list_arena_trace(seed: u64, steps: usize) {
    let mut p: prod::ListArena<PElem, PList, PNode, true> = prod::ListArena::new();
    let mut v: verus::ListArena<VElem, VList, VNode, true> = verus::ListArena::new();

    let mut rng = Rng::new(seed);
    let mut lists: usize = 0;
    // Upper bound on node slots ever allocated (drives the CaptureBits ceiling
    // in the memory-parity assertion below). Only grows — matching the backing
    // vec's capacity, which restore never shrinks.
    let mut nodes_pushed: usize = 0;
    // (prod token, verus token, list count at mark time): restore rolls the
    // heads vec back, so the number of live lists reverts with it.
    let mut marks: Vec<(prod::ListArenaToken, verus::ListArenaToken, usize)> = Vec::new();

    for step in 0..steps {
        match rng.below(100) {
            0..=14 => {
                let pl = p.new_list();
                let vl = v.new_list();
                assert_eq!(
                    pl.raw() as usize,
                    vl.raw() as usize,
                    "step {step}: new_list id diverged"
                );
                lists += 1;
            }
            15..=49 => {
                if lists == 0 {
                    continue;
                }
                let l = rng.below(lists as u64) as u32;
                let val = (rng.next() as u32) & 0x7FFF_FFFF;
                if rng.below(2) == 0 {
                    p.append(PList::new(l), PElem::new(val));
                    v.append(VList::new(l), VElem::new(val));
                } else {
                    p.prepend(PList::new(l), PElem::new(val));
                    v.prepend(VList::new(l), VElem::new(val));
                }
                nodes_pushed += 1;
            }
            50..=69 => {
                if lists == 0 {
                    continue;
                }
                let l = rng.below(lists as u64) as u32;
                let pv: Vec<u32> = p.iter(PList::new(l)).map(|e| e.raw()).collect();
                let vv: Vec<u32> = v.iter(VList::new(l)).map(|e| e.raw()).collect();
                assert_eq!(pv, vv, "step {step}: iter({l}) diverged");
                // Compared without a cast on either side: both `len`s return the node
                // arena's `N::Index`, which at a 31-bit id is `u32` on both crates. The
                // absence of a conversion here is itself part of the parity claim — if
                // one side's cached count went back to a fixed width while the other
                // followed the id family, this would stop type-checking rather than
                // silently agreeing at small lengths.
                assert_eq!(
                    p.len(PList::new(l)),
                    v.len(VList::new(l)),
                    "step {step}: len({l}) diverged"
                );
            }
            70..=79 => {
                if lists < 2 {
                    continue;
                }
                let dst = rng.below(lists as u64) as u32;
                let src = rng.below(lists as u64) as u32;
                if dst == src {
                    continue;
                }
                p.splice(PList::new(dst), PList::new(src));
                v.splice(VList::new(dst), VList::new(src));
            }
            80..=89 => {
                if marks.len() >= 8 {
                    continue;
                }
                let tp = p.mark(prod::ShrinkPolicy::Never);
                let tv = v.mark(verus::ShrinkPolicy::Never);
                marks.push((tp, tv, lists));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv, count_at_mark) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
                lists = count_at_mark;
            }
        }
    }

    // Final sweep: all lists agree.
    for l in 0..lists as u32 {
        let pv: Vec<u32> = p.iter(PList::new(l)).map(|e| e.raw()).collect();
        let vv: Vec<u32> = v.iter(VList::new(l)).map(|e| e.raw()).collect();
        assert_eq!(pv, vv, "final: list {l} diverged");
    }

    // Memory parity, to the byte modulo ONE understood constant.
    //
    // Both arenas store their two columns in an `InlineStore` (capture flag
    // stolen from a niche in the element's own `Tagged` repr), so neither side
    // carries a side capture bit-vector, and both index those columns by
    // `L::Index`/`N::Index` (production `containers/src/list.rs:151-152`), so a
    // diff-log entry is `(T, u32)` and a frame is `u32`-keyed on both sides.
    // Elements match too: `ListNode` is 8 bytes and `ListHead` 12 on both. And
    // `total_bytes` is literally the same expression in the two crates
    // (`size_of::<Self>() + store.heap_bytes() + tracking_bytes()`).
    //
    // The single residual difference is a CONSTANT 8 bytes per inner vec — 16
    // per arena — because verus's `ContainerId` is a `u64` where production's is
    // a `u32` (migration plan 2.6: widened so the id-exhaustion guard is
    // unconditional; `container_id.rs`'s module doc records the two u32
    // alternatives that were measured and rejected, one unsound and one 21.8%
    // slower). It does not scale with nodes, lists, capacity, or mark depth.
    //
    // So both halves of the footprint are asserted EXACTLY: tracking to the
    // byte, and the total to the byte plus that constant. This is a far sharper
    // regression detector than a per-node allowance — anything that reintroduces
    // a capture bit-vector, widens an element or a diff-log index, or
    // double-stores the nodes moves a delta off its constant immediately, at any
    // size.
    const CONTAINER_ID_WIDENING: usize = 16; // 2 vecs x (u64 - u32)
    let (pt, vt) = (p.total_bytes(), v.total_bytes());

    // Diff tracking must match to the byte: same entry widths, same frame
    // widths, same log contents (ShrinkPolicy::Never throughout this trace).
    assert_eq!(
        p.tracking_bytes(),
        v.tracking_bytes(),
        "seed {seed}: tracking_bytes diverged (nodes_pushed {nodes_pushed}, \
         lists {lists}) — both arenas index their columns by `L::Index`/\
         `N::Index`, so diff-log entries and frames must be the same width",
    );

    assert_eq!(
        vt,
        pt + CONTAINER_ID_WIDENING,
        "seed {seed}: verus ListArena total_bytes {vt} != production's {pt} + the \
         {CONTAINER_ID_WIDENING}-byte ContainerId widening (delta {}, \
         nodes_pushed {nodes_pushed}, lists {lists}). The delta must be exactly \
         that constant and must NOT scale with node count — a growing delta \
         means a side capture bit-vector, a widened index, or duplicated node \
         storage has come back",
        vt as i64 - pt as i64,
    );
}

#[test]
fn differential_list_arena() {
    for seed in [11, 0x11A7, 3141, 0xACE5, 99] {
        list_arena_trace(seed, 2000);
    }
}
