// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime property tests for the two intrusive-arena containers: `ListArena`
//! (many singly-linked lists sharing one node arena, with prepend/append/splice)
//! and `CircularList` (a partition of nodes into rings, with O(1) splice-merge).
//!
//! `cargo test` erases the Verus contracts and runs the executable bodies. We
//! read results back by walking the actual `next` pointers over the arena (the
//! ghost `model` is erased), and check against plain-`Vec`/`Vec<Vec>` oracles.
//! The `Ghost(..)` argument to `restore` is a compile-time-only marker
//! (`Ghost::assume_new()`), erased here.

use vstd::prelude::Ghost;

use semi_persistent_containers_verus::circular_list::CircularList;
use semi_persistent_containers_verus::list::ListArena;
use semi_persistent_containers_verus::vec::ShrinkPolicy;

struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 17
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() as usize) % n
    }
}

// --------------------------------------------------------------------------
// ListArena: walk list `l` by following head -> next* over the arena.
// --------------------------------------------------------------------------

type Arena = ListArena<u32, false>;

fn read_list(a: &Arena, l: usize) -> Vec<u32> {
    let mut out = Vec::new();
    let head = a.heads.get(l).head;
    let mut cur = head;
    // Guard against a corrupt cycle: never walk more than the arena size.
    let mut budget = a.nodes.len() + 1;
    while cur.some {
        assert!(
            budget > 0,
            "list {l} walk exceeded arena size — cycle/corruption"
        );
        budget -= 1;
        let node = a.nodes.get(cur.idx);
        out.push(node.payload);
        cur = node.next;
    }
    out
}

#[test]
fn list_arena_prepend_append_match_oracle() {
    for seed in 0..16u64 {
        let mut a = Arena::new();
        let mut oracle: Vec<Vec<u32>> = Vec::new();
        let mut rng = Lcg::new(seed ^ 0x1157);

        // a handful of lists.
        let nlists = 1 + rng.below(5);
        for _ in 0..nlists {
            let l = a.new_list();
            assert_eq!(l, oracle.len(), "seed={seed}: new_list index mismatch");
            oracle.push(Vec::new());
        }

        for _ in 0..1500 {
            let l = rng.below(oracle.len());
            let v = rng.next() as u32;
            if rng.below(2) == 0 {
                a.prepend(l, v);
                oracle[l].insert(0, v);
            } else {
                a.append(l, v);
                oracle[l].push(v);
            }
            // is_empty agrees, and a random list reads back exactly.
            let probe = rng.below(oracle.len());
            assert_eq!(
                a.is_empty(probe),
                oracle[probe].is_empty(),
                "seed={seed}: is_empty({probe})"
            );
            assert_eq!(
                read_list(&a, probe),
                oracle[probe],
                "seed={seed}: list {probe} contents"
            );
            // O(1) cached len agrees with the oracle length.
            assert_eq!(
                a.len(probe),
                oracle[probe].len(),
                "seed={seed}: len({probe})"
            );
        }
        // full sweep.
        for (l, expected) in oracle.iter().enumerate() {
            assert_eq!(read_list(&a, l), *expected, "seed={seed}: final list {l}");
            assert_eq!(a.len(l), expected.len(), "seed={seed}: final len {l}");
        }
        println!("list_arena prepend/append seed={seed}: OK ({nlists} lists)");
    }
}

#[test]
fn list_arena_splice_match_oracle() {
    for seed in 0..16u64 {
        let mut a = Arena::new();
        let mut oracle: Vec<Vec<u32>> = Vec::new();
        let mut rng = Lcg::new(seed ^ 0x5217);

        let nlists = 3 + rng.below(6);
        for _ in 0..nlists {
            a.new_list();
            oracle.push(Vec::new());
        }
        // seed each list with a few values.
        for (l, olist) in oracle.iter_mut().enumerate() {
            for _ in 0..rng.below(6) {
                let v = rng.next() as u32;
                a.append(l, v);
                olist.push(v);
            }
        }

        for _ in 0..400 {
            // splice(dst, src): dst := dst ++ src; src := [].  dst != src.
            let dst = rng.below(nlists);
            let mut src = rng.below(nlists);
            if src == dst {
                src = (src + 1) % nlists;
            }
            a.splice(dst, src);
            let tail = std::mem::take(&mut oracle[src]);
            oracle[dst].extend(tail);

            // refill occasionally so lists do not all collapse to empty.
            if rng.below(3) == 0 {
                let l = rng.below(nlists);
                let v = rng.next() as u32;
                a.append(l, v);
                oracle[l].push(v);
            }

            for (l, expected) in oracle.iter().enumerate() {
                assert_eq!(
                    read_list(&a, l),
                    *expected,
                    "seed={seed}: list {l} after splice"
                );
                assert_eq!(
                    a.len(l),
                    expected.len(),
                    "seed={seed}: len {l} after splice"
                );
            }
        }
        println!("list_arena splice seed={seed}: OK");
    }
}

#[test]
fn list_arena_mark_restore() {
    for seed in 0..10u64 {
        let mut a = Arena::new();
        let mut oracle: Vec<Vec<u32>> = Vec::new();
        let mut rng = Lcg::new(seed ^ 0x9988);
        let nlists = 2 + rng.below(4);
        for _ in 0..nlists {
            a.new_list();
            oracle.push(Vec::new());
        }
        let mut frames: Vec<(_, Vec<Vec<u32>>)> = Vec::new();

        for _ in 0..250 {
            match rng.below(8) {
                0 => {
                    let token = a.mark(ShrinkPolicy::Never);
                    frames.push((token, oracle.clone()));
                }
                1 if !frames.is_empty() => {
                    let (tok, snap) = frames.pop().unwrap();
                    a.restore(tok, Ghost::assume_new());
                    oracle = snap;
                }
                _ => {
                    let l = rng.below(nlists);
                    let v = rng.next() as u32;
                    if rng.below(2) == 0 {
                        a.prepend(l, v);
                        oracle[l].insert(0, v);
                    } else {
                        a.append(l, v);
                        oracle[l].push(v);
                    }
                }
            }
            let l = rng.below(nlists);
            assert_eq!(
                read_list(&a, l),
                oracle[l],
                "seed={seed}: list {l} after op"
            );
        }
        // unwind fully.
        while let Some((tok, snap)) = frames.pop() {
            a.restore(tok, Ghost::assume_new());
            for (l, expected) in snap.iter().enumerate() {
                assert_eq!(
                    read_list(&a, l),
                    *expected,
                    "seed={seed}: list {l} after restore"
                );
            }
        }
        println!("list_arena_mark_restore seed={seed}: OK");
    }
}

// --------------------------------------------------------------------------
// CircularList: nodes partitioned into rings. add_singleton(p) makes a new ring
// [n] (self-loop); splice(s, a) merges the ring containing s with the ring
// containing a (must be different rings). We read a ring back by following
// next_of from a start node until we return to it.
// --------------------------------------------------------------------------

type Ring = CircularList<u32, false>;

/// The cyclic sequence of payloads starting at node `start`, walking `next_of`
/// until we loop back. Rotation-invariant comparison is done by the caller.
fn read_ring(c: &Ring, start: usize) -> Vec<u32> {
    let mut out = Vec::new();
    let mut cur = start;
    let mut budget = c.len() + 1;
    loop {
        assert!(
            budget > 0,
            "ring walk from {start} exceeded node count — corruption"
        );
        budget -= 1;
        // payload of node `cur`.
        out.push(payload_of(c, cur));
        cur = c.next_of(cur);
        if cur == start {
            break;
        }
    }
    out
}

fn payload_of(c: &Ring, i: usize) -> u32 {
    c.entries.get(i).payload
}

/// Are two sequences equal up to rotation (same ring, different start)?
fn eq_up_to_rotation(a: &[u32], b: &[u32]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    if a.is_empty() {
        return true;
    }
    let n = a.len();
    (0..n).any(|shift| (0..n).all(|i| a[i] == b[(i + shift) % n]))
}

#[test]
fn circular_list_singleton_and_splice() {
    for seed in 0..16u64 {
        let mut c = Ring::new();
        let mut rng = Lcg::new(seed ^ 0x3C12);

        // Disjoint-set-style oracle: ring_id[node] = representative, and
        // ring_order[rep] = the in-ring payload order starting at `rep`.
        let mut node_payload: Vec<u32> = Vec::new();
        // For each node, its ring as an ordered Vec of node ids (canonical:
        // stored on the representative = smallest start we created it from).
        // We track, per node, which ring Vec it belongs to via an index.
        let mut rings: Vec<Vec<usize>> = Vec::new(); // ring -> node ids in order
        let mut ring_of: Vec<usize> = Vec::new(); // node -> ring index

        for _ in 0..600 {
            let make_new = rng.below(3) == 0 || node_payload.len() < 2;
            if make_new {
                let p = rng.next() as u32;
                let id = c.add_singleton(p);
                assert_eq!(
                    id,
                    node_payload.len(),
                    "seed={seed}: add_singleton id mismatch"
                );
                node_payload.push(p);
                ring_of.push(rings.len());
                rings.push(vec![id]);
            } else {
                // pick two nodes in different rings and splice.
                let s = rng.below(node_payload.len());
                let mut a = rng.below(node_payload.len());
                let mut tries = 0;
                while ring_of[a] == ring_of[s] && tries < 8 {
                    a = rng.below(node_payload.len());
                    tries += 1;
                }
                if ring_of[a] == ring_of[s] {
                    continue; // could not find a different ring this time
                }
                c.splice(s, a);

                // Oracle merge mirroring the proven semantics: the new ring of s
                // is rotate(ring_s, pos_s+1) ++ rotate(ring_a, pos_a+1), i.e.
                // starting just after s through s, then just after a through a.
                let rs = ring_of[s];
                let ra = ring_of[a];
                let ring_s = rings[rs].clone();
                let ring_a = rings[ra].clone();
                let ps = ring_s.iter().position(|&x| x == s).unwrap();
                let pa = ring_a.iter().position(|&x| x == a).unwrap();
                let mut merged = Vec::new();
                let ns = ring_s.len();
                for k in 0..ns {
                    merged.push(ring_s[(ps + 1 + k) % ns]);
                }
                let na = ring_a.len();
                for k in 0..na {
                    merged.push(ring_a[(pa + 1 + k) % na]);
                }
                // commit: rs gets merged, ra becomes empty; repoint ring_of.
                for &nd in &merged {
                    ring_of[nd] = rs;
                }
                rings[rs] = merged;
                rings[ra].clear();
            }

            // Validate: pick a random node, read its ring by pointer-walk, and
            // compare (up to rotation) with the oracle ring it belongs to.
            if !node_payload.is_empty() {
                let nd = rng.below(node_payload.len());
                let walked = read_ring(&c, nd);
                let oracle_ring: Vec<u32> = rings[ring_of[nd]]
                    .iter()
                    .map(|&x| node_payload[x])
                    .collect();
                // walked starts at nd; rotate oracle so it also starts at nd.
                let start_pos = rings[ring_of[nd]].iter().position(|&x| x == nd).unwrap();
                let oracle_nodes = &rings[ring_of[nd]];
                let rotated: Vec<u32> = (0..oracle_nodes.len())
                    .map(|i| node_payload[oracle_nodes[(start_pos + i) % oracle_nodes.len()]])
                    .collect();
                assert_eq!(
                    walked, rotated,
                    "seed={seed}: ring of node {nd} pointer-walk != oracle"
                );
                assert!(eq_up_to_rotation(&walked, &oracle_ring));
            }
        }
        println!(
            "circular_list seed={seed}: OK ({} nodes)",
            node_payload.len()
        );
    }
}

#[test]
fn circular_list_mark_restore() {
    for seed in 0..10u64 {
        let mut c = Ring::new();
        let mut rng = Lcg::new(seed ^ 0x7A7A);
        let mut node_payload: Vec<u32> = Vec::new();
        let mut rings: Vec<Vec<usize>> = Vec::new();
        let mut ring_of: Vec<usize> = Vec::new();

        // snapshot of (node_payload, rings, ring_of) alongside the token.
        type Snap = (Vec<u32>, Vec<Vec<usize>>, Vec<usize>);
        let mut frames: Vec<(_, Snap)> = Vec::new();

        for _ in 0..250 {
            match rng.below(7) {
                0 => {
                    let token = c.mark(ShrinkPolicy::Never);
                    frames.push((
                        token,
                        (node_payload.clone(), rings.clone(), ring_of.clone()),
                    ));
                }
                1 if !frames.is_empty() => {
                    let (tok, (np, rg, ro)) = frames.pop().unwrap();
                    c.restore(tok, Ghost::assume_new());
                    node_payload = np;
                    rings = rg;
                    ring_of = ro;
                }
                _ => {
                    let p = rng.next() as u32;
                    let id = c.add_singleton(p);
                    node_payload.push(p);
                    ring_of.push(rings.len());
                    rings.push(vec![id]);
                }
            }
            // a random node's ring reads back consistent with the oracle.
            if !node_payload.is_empty() {
                let nd = rng.below(node_payload.len());
                let walked = read_ring(&c, nd);
                let oracle_nodes = &rings[ring_of[nd]];
                let start_pos = oracle_nodes.iter().position(|&x| x == nd).unwrap();
                let rotated: Vec<u32> = (0..oracle_nodes.len())
                    .map(|i| node_payload[oracle_nodes[(start_pos + i) % oracle_nodes.len()]])
                    .collect();
                assert_eq!(walked, rotated, "seed={seed}: ring of {nd} after op");
            }
        }
        println!("circular_list_mark_restore seed={seed}: OK");
    }
}
