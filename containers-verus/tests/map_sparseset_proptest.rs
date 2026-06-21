// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime property tests for `SpMap` (semi-persistent insert-or-overwrite map)
//! and `SparseSet` (stable-id set with O(1) add/remove/contains).
//!
//! `cargo test` erases the Verus contracts and runs the executable bodies, so
//! these check the compiled code against plain-`std` oracles (a `HashMap` and a
//! `HashMap<id, value>` respectively), including the mark/restore rollback that
//! is the crate's reason for existing.

use std::collections::HashMap;

use semi_persistent_containers_verus::inline_store::InlineStore;
use semi_persistent_containers_verus::map::SpMap;
use semi_persistent_containers_verus::parallel_store::ParallelStore;
use semi_persistent_containers_verus::sparse_set::SparseSet;
use semi_persistent_containers_verus::vec::{ShrinkPolicy, Vec as SpVec};

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
// SpMap: insert (overwrite-on-dup), contains_key, id_of, get, vs a HashMap.
// --------------------------------------------------------------------------

type Map = SpMap<u32, u64, false>;

#[test]
fn map_ops_match_oracle() {
    for seed in 0..16u64 {
        let mut m = Map::new();
        // oracle: key -> latest value, and key -> latest log index.
        let mut vals: HashMap<u32, u64> = HashMap::new();
        let mut last_idx: HashMap<u32, usize> = HashMap::new();
        let mut rng = Lcg::new(seed ^ 0x3AA3);

        for _ in 0..1500 {
            // Keys drawn from a small space so duplicates (overwrites) happen.
            let key = (rng.below(64)) as u32;
            let val = rng.next();
            let id = m.insert(key, val);
            // insert returns the new dense log index == previous log length.
            vals.insert(key, val);
            last_idx.insert(key, id);

            // contains_key / id_of agree with the oracle for a random probe key.
            let probe = (rng.below(80)) as u32;
            assert_eq!(
                m.contains_key(&probe),
                vals.contains_key(&probe),
                "seed={seed}: contains_key({probe}) mismatch"
            );
            assert_eq!(
                m.id_of(&probe),
                last_idx.get(&probe).copied(),
                "seed={seed}: id_of({probe}) mismatch"
            );
            // the value at the key's current id matches the latest write.
            if let Some(&i) = last_idx.get(&key) {
                let (gk, gv) = m.get(i);
                assert_eq!(*gk, key, "seed={seed}: get key mismatch");
                assert_eq!(*gv, vals[&key], "seed={seed}: get value mismatch");
            }
        }
        println!("map seed={seed}: OK ({} distinct keys)", vals.len());
    }
}

#[test]
fn map_mark_restore() {
    for seed in 0..10u64 {
        let mut m = Map::new();
        let mut oracle: HashMap<u32, u64> = HashMap::new();
        let mut rng = Lcg::new(seed ^ 0x9F9F);
        // (token, oracle snapshot), LIFO.
        let mut frames: Vec<(_, HashMap<u32, u64>)> = Vec::new();

        for _ in 0..400 {
            match rng.below(8) {
                0 => {
                    let token = m.mark(ShrinkPolicy::Never);
                    frames.push((token, oracle.clone()));
                }
                1 if !frames.is_empty() => {
                    let (tok, snap) = frames.pop().unwrap();
                    m.restore(tok);
                    oracle = snap;
                }
                _ => {
                    let key = (rng.below(48)) as u32;
                    let val = rng.next();
                    m.insert(key, val);
                    oracle.insert(key, val);
                }
            }
            // Whole-map agreement: every oracle key resolves to its value, and
            // a probe of an absent key is reported absent.
            for (&k, &v) in oracle.iter() {
                assert!(m.contains_key(&k), "seed={seed}: lost key {k} after op");
                let i = m.id_of(&k).expect("present key has an id");
                assert_eq!(m.get(i).1, v, "seed={seed}: key {k} value mismatch");
            }
            let absent = 200u32 + (rng.below(50) as u32);
            assert_eq!(m.contains_key(&absent), oracle.contains_key(&absent));
        }
        println!("map_mark_restore seed={seed}: OK");
    }
}

// --------------------------------------------------------------------------
// SparseSet: add (stable id) / remove / contains / get / set, vs a HashMap
// from live id -> value. SparseSet has public fields and no constructor, so we
// build it from three empty verified Vecs (its actual representation).
//
// Idx = u32 (which is IndexLike + Tagged + Default — DenseId31 is not Default,
// which SparseSet::restore requires; DenseId31's own MSB-capture behaviour is
// verified separately in dense_id.rs). The id IS the u32, so no `.index()` hop.
// The sparse/indices columns use InlineStore<u32,u32> per the struct's types.
// --------------------------------------------------------------------------

type Set = SparseSet<u32, u32, ParallelStore<u32, u32>, false>;

fn empty_set() -> Set {
    SparseSet {
        dense: SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new(),
        sparse: SpVec::<u32, u32, InlineStore<u32, u32>, false>::new(),
        indices: SpVec::<u32, u32, InlineStore<u32, u32>, false>::new(),
    }
}

#[test]
fn sparse_set_ops_match_oracle() {
    for seed in 0..16u64 {
        let mut s = empty_set();
        // oracle: live id (u32) -> value.
        let mut live: HashMap<u32, u32> = HashMap::new();
        let mut ids: Vec<u32> = Vec::new(); // live ids, for random pick
        let mut rng = Lcg::new(seed ^ 0x7C7C);

        for _ in 0..1500 {
            let pick = rng.below(10);
            if pick < 5 || ids.is_empty() {
                // add
                let val = rng.next() as u32;
                let id_u = s.add(val);
                assert!(
                    !live.contains_key(&id_u),
                    "seed={seed}: add returned a live id {id_u}"
                );
                live.insert(id_u, val);
                ids.push(id_u);
            } else if pick < 7 {
                // remove a random live id
                let k = rng.below(ids.len());
                let id_u = ids.swap_remove(k);
                s.remove(id_u);
                live.remove(&id_u);
            } else if pick < 8 {
                // set (overwrite) a random live id
                let id_u = ids[rng.below(ids.len())];
                let val = rng.next() as u32;
                s.set(id_u, val);
                live.insert(id_u, val);
            } else {
                // get + contains a random live id
                let id_u = ids[rng.below(ids.len())];
                assert!(s.contains(id_u), "seed={seed}: id {id_u} not contained");
                assert_eq!(
                    s.get(id_u),
                    live[&id_u],
                    "seed={seed}: get({id_u}) value mismatch"
                );
            }

            // invariants vs oracle: size, and a probe of a never-allocated id.
            assert_eq!(s.len() as usize, live.len(), "seed={seed}: len mismatch");
            assert_eq!(s.is_empty(), live.is_empty());
            let big = 1_000_000 + (rng.below(1000) as u32);
            assert!(!s.contains(big), "seed={seed}: contains a never-added id");
        }
        // full sweep: every live id contained with the right value.
        for (&id_u, &v) in live.iter() {
            assert!(s.contains(id_u));
            assert_eq!(s.get(id_u), v);
        }
        println!("sparse_set seed={seed}: OK ({} live)", live.len());
    }
}

#[test]
fn sparse_set_mark_restore() {
    for seed in 0..10u64 {
        let mut s = empty_set();
        let mut live: HashMap<u32, u32> = HashMap::new();
        let mut ids: Vec<u32> = Vec::new();
        let mut rng = Lcg::new(seed ^ 0x1234);
        let mut frames: Vec<(_, HashMap<u32, u32>, Vec<u32>)> = Vec::new();

        for _ in 0..300 {
            match rng.below(8) {
                0 => {
                    let token = s.mark(ShrinkPolicy::Never);
                    frames.push((token, live.clone(), ids.clone()));
                }
                1 if !frames.is_empty() => {
                    let (tok, lsnap, isnap) = frames.pop().unwrap();
                    s.restore(tok);
                    live = lsnap;
                    ids = isnap;
                }
                2 if !ids.is_empty() => {
                    let k = rng.below(ids.len());
                    let id_u = ids.swap_remove(k);
                    s.remove(id_u);
                    live.remove(&id_u);
                }
                _ => {
                    let val = rng.next() as u32;
                    let id_u = s.add(val);
                    live.insert(id_u, val);
                    ids.push(id_u);
                }
            }
            assert_eq!(s.len() as usize, live.len(), "seed={seed}: len mismatch after op");
            // every live id present with the oracle value.
            for (&id_u, &v) in live.iter() {
                assert!(s.contains(id_u), "seed={seed}: lost id {id_u}");
                assert_eq!(s.get(id_u), v, "seed={seed}: id {id_u} value drift");
            }
        }
        println!("sparse_set_mark_restore seed={seed}: OK");
    }
}
