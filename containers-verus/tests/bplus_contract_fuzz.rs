// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Direct postcondition fuzzer for the trusted `NodeLayout` primitives.
//!
//! The B+tree's `external_body` primitives (the u64 layouts' `child`,
//! `new_internal2`, `set_internal_child` — trusted for the `u64 as usize` index
//! cast — plus, defensively, every OTHER layout primitive) carry precise Verus
//! `ensures`. Under plain `cargo test` those `ensures` are ERASED, so a wrong
//! body would go unnoticed. This harness re-derives each primitive's spec view
//! in plain Rust from the node's PUBLIC fields and asserts, on random nodes /
//! positions / values, that the exec result equals what the `ensures` claims.
//!
//! This is the runtime stand-in for the machine check we don't get on the
//! trusted bodies: if `child`'s cast were ever value-changing, or a `copy_within`
//! shift were off-by-one, these fire — independent of the tree algorithm above.
//!
//! Coverage: all SIX layouts (3 u32 + 3 u64) via the `fuzz_layout!` macro, so
//! the u64 cast path and the u32 no-cast path are both exercised. We treat the
//! spec view as the oracle:
//!
//! - `keys_view(n)  == data[0..count]`
//! - `child_view(n, i) == if i < key_cap { data[key_cap + i] } else { link }`
//! - `link_view(n)  == link`
//!
//! and check each exec accessor / mutator refines it.

use semi_persistent_containers_verus::bplus_layout::NodeLayout;
use semi_persistent_containers_verus::index_like::IndexLike;

// ---------------------------------------------------------------------------
// Reproducible LCG (no rand dep; fixed seeds so any failure is replayable).
// ---------------------------------------------------------------------------
struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(0xD1B5_4A32))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 1
    }
    fn upto(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() as usize) % n
        }
    }
}

// ---------------------------------------------------------------------------
// The generic fuzzer body, stamped once per concrete layout. `$W` is the word
// type (u32 / u64), `$wfrom` builds a `$W` from the LCG (masked to the type),
// `$node_new` builds a node literal of the right field types.
// ---------------------------------------------------------------------------
macro_rules! fuzz_layout {
    ($name:ident, $L:ty, $Node:ty, $W:ty, $leaf_cap:expr, $key_cap:expr, $data_len:expr) => {
        mod $name {
            use super::*;
            use semi_persistent_containers_verus::bplus_layout::{$L, $Node};

            type L = $L;
            const LEAF_CAP: usize = $leaf_cap;
            const KEY_CAP: usize = $key_cap;
            const DATA_LEN: usize = $data_len;

            fn word(lcg: &mut Lcg) -> $W {
                lcg.next() as $W
            }

            // --- shadow views recomputed from the node's PUBLIC fields ---
            fn shadow_keys(n: &$Node) -> Vec<$W> {
                (0..n.count).map(|i| n.data[i]).collect()
            }
            // child_view as a u128 so u32/u64 compare uniformly with the
            // exec result widened the same way.
            fn shadow_child(n: &$Node, i: usize) -> u128 {
                if i < KEY_CAP {
                    n.data[KEY_CAP + i] as u128
                } else {
                    n.link as u128
                }
            }

            // Build a random INTERNAL node with `count` separators (0..=KEY_CAP)
            // and `count+1` child slots filled with random ids.
            fn rand_internal(lcg: &mut Lcg) -> $Node {
                let count = lcg.upto(KEY_CAP + 1);
                let mut data = [0 as $W; DATA_LEN];
                // separators data[0..count]
                for i in 0..count {
                    data[i] = word(lcg);
                }
                // child ids data[key_cap .. key_cap+count] (last child uses link)
                for i in 0..count {
                    data[KEY_CAP + i] = word(lcg);
                }
                let link = lcg.next() as usize; // last child / arena id
                let mut n: $Node = L::new_leaf();
                n.is_leaf = false;
                n.count = count;
                n.data = data;
                n.link = link as _;
                n
            }

            fn rand_leaf(lcg: &mut Lcg, full: bool) -> $Node {
                let count = if full { LEAF_CAP } else { lcg.upto(LEAF_CAP) };
                let mut data = [0 as $W; DATA_LEN];
                // sorted distinct-ish keys so leaf is a valid node_wf leaf
                let mut k: $W = (lcg.next() & 0xFF) as $W;
                for i in 0..count {
                    data[i] = k;
                    k = k.wrapping_add(1 + (lcg.next() & 0x7) as $W);
                }
                let mut n: $Node = L::new_leaf();
                n.is_leaf = true;
                n.count = count;
                n.data = data;
                n
            }

            #[test]
            fn accessors_refine_views() {
                let mut lcg = Lcg::new(0xACCE_5500 ^ (LEAF_CAP as u64));
                for _ in 0..20_000 {
                    let internal = lcg.next() & 1 == 0;
                    let n = if internal {
                        rand_internal(&mut lcg)
                    } else {
                        rand_leaf(&mut lcg, false)
                    };

                    // is_leaf / count
                    assert_eq!(L::is_leaf(&n), n.is_leaf, "is_leaf mismatch");
                    assert_eq!(L::count(&n), n.count, "count mismatch");
                    // link_view
                    assert_eq!(
                        L::link(&n).as_usize() as u128,
                        n.link as u128,
                        "link mismatch"
                    );

                    // key(i) == keys_view[i]  (the data[0..count] projection)
                    let keys = shadow_keys(&n);
                    for i in 0..n.count {
                        assert_eq!(L::key(&n, i), keys[i], "key[{i}] mismatch");
                    }
                    // child(i) == child_view(i) for internal nodes, i in 0..=count.
                    // THIS is the u64->usize cast under test for the u64 layouts.
                    if !n.is_leaf {
                        for i in 0..=n.count {
                            let got = L::child(&n, i).as_usize() as u128;
                            assert_eq!(
                                got,
                                shadow_child(&n, i),
                                "child[{i}] mismatch (the as-usize cast?): got {got}, shadow {}",
                                shadow_child(&n, i)
                            );
                        }
                    }
                }
            }

            #[test]
            fn new_internal2_refines_view() {
                let mut lcg = Lcg::new(0x4E00_0002 ^ (KEY_CAP as u64));
                for _ in 0..20_000 {
                    let sep = word(&mut lcg);
                    let left = lcg.next() as usize;
                    let right = lcg.next() as usize;
                    let left_idx = <<L as NodeLayout>::ArenaIdx as IndexLike>::try_from_usize(left)
                        .unwrap_or(<<L as NodeLayout>::ArenaIdx as IndexLike>::max());
                    let right_idx =
                        <<L as NodeLayout>::ArenaIdx as IndexLike>::try_from_usize(right)
                            .unwrap_or(<<L as NodeLayout>::ArenaIdx as IndexLike>::max());
                    let lw = left_idx.as_usize();
                    let rw = right_idx.as_usize();

                    let n = L::new_internal2(sep, left_idx, right_idx);
                    // ensures: !is_leaf, count==1, keys_view==[sep], child(0)==left, child(1)==right.
                    assert!(!L::is_leaf(&n), "new_internal2 produced a leaf");
                    assert_eq!(L::count(&n), 1, "new_internal2 count != 1");
                    assert_eq!(L::key(&n, 0), sep, "new_internal2 sep mismatch");
                    assert_eq!(
                        L::child(&n, 0).as_usize(),
                        lw,
                        "new_internal2 child(0) != left"
                    );
                    assert_eq!(
                        L::child(&n, 1).as_usize(),
                        rw,
                        "new_internal2 child(1) != right"
                    );
                }
            }

            #[test]
            fn set_internal_child_refines_view() {
                let mut lcg = Lcg::new(0x5E70_C41D ^ (DATA_LEN as u64));
                for _ in 0..20_000 {
                    let mut n = rand_internal(&mut lcg);
                    if n.count == 0 {
                        n.count = 1;
                        n.data[0] = word(&mut lcg);
                    } // need >= 1 child slot
                    let i = lcg.upto(n.count + 1); // 0..=count
                    let v = lcg.next() as usize;
                    let v_idx = <<L as NodeLayout>::ArenaIdx as IndexLike>::try_from_usize(v)
                        .unwrap_or(<<L as NodeLayout>::ArenaIdx as IndexLike>::max());
                    let vw = v_idx.as_usize();

                    let before = n;
                    L::set_internal_child(&mut n, i, v_idx);

                    // ensures: still internal, same count/keys/link-as-last-child semantics,
                    // child(i) == v, every OTHER child unchanged.
                    assert_eq!(
                        L::is_leaf(&n),
                        L::is_leaf(&before),
                        "set_internal_child flipped is_leaf"
                    );
                    assert_eq!(
                        L::count(&n),
                        before.count,
                        "set_internal_child changed count"
                    );
                    // keys_view unchanged
                    for j in 0..before.count {
                        assert_eq!(
                            L::key(&n, j),
                            L::key(&before, j),
                            "set_internal_child changed key[{j}]"
                        );
                    }
                    assert_eq!(
                        L::child(&n, i).as_usize(),
                        vw,
                        "set_internal_child target child[{i}] != v"
                    );
                    for j in 0..=before.count {
                        if j != i {
                            assert_eq!(
                                L::child(&n, j).as_usize(),
                                L::child(&before, j).as_usize(),
                                "set_internal_child disturbed sibling child[{j}] (set {i})"
                            );
                        }
                    }
                }
            }

            #[test]
            fn set_link_refines_view() {
                let mut lcg = Lcg::new(0x5E70_11C4 ^ (LEAF_CAP as u64));
                for _ in 0..10_000 {
                    let mut n = rand_leaf(&mut lcg, false);
                    let v = lcg.next() as usize;
                    let v_idx = <<L as NodeLayout>::ArenaIdx as IndexLike>::try_from_usize(v)
                        .unwrap_or(<<L as NodeLayout>::ArenaIdx as IndexLike>::max());
                    let before = n;
                    L::set_link(&mut n, v_idx);
                    // ensures: only the link changes.
                    assert_eq!(L::is_leaf(&n), L::is_leaf(&before));
                    assert_eq!(L::count(&n), before.count);
                    for j in 0..before.count {
                        assert_eq!(
                            L::key(&n, j),
                            L::key(&before, j),
                            "set_link changed key[{j}]"
                        );
                    }
                    assert_eq!(
                        L::link(&n).as_usize(),
                        v_idx.as_usize(),
                        "set_link target mismatch"
                    );
                }
            }

            #[test]
            fn leaf_insert_at_refines_view() {
                let mut lcg = Lcg::new(0x1EAF_1227 ^ (KEY_CAP as u64));
                for _ in 0..20_000 {
                    let mut n = rand_leaf(&mut lcg, false);
                    if n.count >= LEAF_CAP {
                        continue;
                    } // requires count < leaf_cap
                    let pos = lcg.upto(n.count + 1); // 0..=count
                    let w = word(&mut lcg);
                    let before_keys = shadow_keys(&n);
                    let old_link = n.link;
                    L::leaf_insert_at(&mut n, pos, w);
                    // ensures: count+1, keys == before.insert(pos, w), still leaf, link same.
                    assert!(L::is_leaf(&n));
                    assert_eq!(L::count(&n), before_keys.len() + 1, "leaf_insert_at count");
                    let mut want = before_keys.clone();
                    want.insert(pos, w);
                    let got = shadow_keys(&n);
                    assert_eq!(got, want, "leaf_insert_at keys: pos={pos} w={w}");
                    assert_eq!(n.link, old_link, "leaf_insert_at changed link");
                }
            }

            #[test]
            fn leaf_split_at_refines_view() {
                let mut lcg = Lcg::new(0x1EAF_5917 ^ (DATA_LEN as u64));
                let mid = L::split_mid();
                for _ in 0..20_000 {
                    let n = rand_leaf(&mut lcg, true); // FULL leaf (count == leaf_cap)
                    assert_eq!(n.count, LEAF_CAP);
                    let pos = lcg.upto(LEAF_CAP + 1); // 0..=leaf_cap
                    let w = word(&mut lcg);
                    // combined = keys_view.insert(pos, w)
                    let mut combined = shadow_keys(&n);
                    combined.insert(pos, w);
                    let (l, r) = L::leaf_split_at(&n, pos, w);
                    // ensures on the two halves.
                    assert!(L::is_leaf(&l) && L::is_leaf(&r));
                    assert_eq!(L::count(&l), mid, "leaf_split left count");
                    assert_eq!(L::count(&r), LEAF_CAP + 1 - mid, "leaf_split right count");
                    assert_eq!(
                        shadow_keys(&l),
                        combined[0..mid].to_vec(),
                        "leaf_split left keys"
                    );
                    assert_eq!(
                        shadow_keys(&r),
                        combined[mid..].to_vec(),
                        "leaf_split right keys"
                    );
                    assert_eq!(r.link, n.link, "leaf_split right must inherit old link");
                }
            }

            #[test]
            fn internal_split_at_refines_view() {
                let mut lcg = Lcg::new(0x142E_5917 ^ (KEY_CAP as u64));
                let imid = L::isplit_mid();
                for _ in 0..20_000 {
                    // FULL internal node: count == key_cap.
                    let mut n = rand_internal(&mut lcg);
                    n.count = KEY_CAP;
                    for i in 0..KEY_CAP {
                        n.data[i] = word(&mut lcg);
                    }
                    for i in 0..KEY_CAP {
                        n.data[KEY_CAP + i] = word(&mut lcg);
                    }
                    n.link = lcg.next() as _;

                    let cp = lcg.upto(KEY_CAP + 1); // 0..=key_cap
                    let new_sep = word(&mut lcg);
                    let new_child = lcg.next() as usize;
                    let nc_idx =
                        <<L as NodeLayout>::ArenaIdx as IndexLike>::try_from_usize(new_child)
                            .unwrap_or(<<L as NodeLayout>::ArenaIdx as IndexLike>::max());

                    // combined separator seq = keys_view.insert(cp, new_sep)
                    let mut cseps = (0..KEY_CAP).map(|i| n.data[i]).collect::<Vec<$W>>();
                    cseps.insert(cp, new_sep);
                    // combined child id at position j (isplit_cchild):
                    //   j <= cp        -> child_view(n, j)
                    //   j == cp + 1    -> new_child
                    //   else           -> child_view(n, j-1)
                    let cchild = |j: usize| -> u128 {
                        if j <= cp {
                            shadow_child(&n, j)
                        } else if j == cp + 1 {
                            nc_idx.as_usize() as u128
                        } else {
                            shadow_child(&n, j - 1)
                        }
                    };

                    let (pl, pr, promoted) = L::internal_split_at(&n, cp, new_sep, nc_idx);

                    // ensures: counts, key subranges, promoted == cseps[imid], children.
                    assert!(!L::is_leaf(&pl) && !L::is_leaf(&pr));
                    assert_eq!(L::count(&pl), imid, "internal_split left count");
                    assert_eq!(L::count(&pr), KEY_CAP - imid, "internal_split right count");
                    assert_eq!(
                        promoted, cseps[imid],
                        "internal_split promoted != cseps[imid]"
                    );
                    // left seps == cseps[0..imid]
                    for j in 0..imid {
                        assert_eq!(L::key(&pl, j), cseps[j], "internal_split left sep[{j}]");
                    }
                    // right seps == cseps[imid+1..]
                    for j in 0..(KEY_CAP - imid) {
                        assert_eq!(
                            L::key(&pr, j),
                            cseps[imid + 1 + j],
                            "internal_split right sep[{j}]"
                        );
                    }
                    // left children == isplit_cchild(0..=imid)
                    for j in 0..=imid {
                        assert_eq!(
                            L::child(&pl, j).as_usize() as u128,
                            cchild(j),
                            "internal_split left child[{j}] cp={cp}"
                        );
                    }
                    // right children == isplit_cchild(imid+1 ..)
                    for j in 0..=(KEY_CAP - imid) {
                        assert_eq!(
                            L::child(&pr, j).as_usize() as u128,
                            cchild(imid + 1 + j),
                            "internal_split right child[{j}] cp={cp}"
                        );
                    }
                }
            }

            #[test]
            fn internal_key_insert_refines_view() {
                let mut lcg = Lcg::new(0x142E_0001 ^ (LEAF_CAP as u64));
                for _ in 0..20_000 {
                    let mut n = rand_internal(&mut lcg);
                    if n.count >= KEY_CAP {
                        continue;
                    } // requires count < key_cap
                    let pos = lcg.upto(n.count + 1);
                    let w = word(&mut lcg);
                    let before = (0..n.count).map(|i| n.data[i]).collect::<Vec<$W>>();
                    L::internal_key_insert(&mut n, pos, w);
                    // ensures: count+1, keys == before.insert(pos, w), still internal.
                    assert!(!L::is_leaf(&n));
                    assert_eq!(L::count(&n), before.len() + 1, "internal_key_insert count");
                    let mut want = before.clone();
                    want.insert(pos, w);
                    let got = (0..n.count).map(|i| n.data[i]).collect::<Vec<$W>>();
                    assert_eq!(got, want, "internal_key_insert keys pos={pos}");
                }
            }
        }
    };
}

fuzz_layout!(l64u32, Layout64U32, Node64U32, u32, 14, 7, 14);
fuzz_layout!(l128u32, Layout128U32, Node128U32, u32, 30, 14, 30);
fuzz_layout!(l256u32, Layout256U32, Node256U32, u32, 62, 30, 62);
fuzz_layout!(l128u64, Layout128U64, Node128U64, u64, 14, 6, 14);
fuzz_layout!(l256u64, Layout256U64, Node256U64, u64, 30, 14, 30);
fuzz_layout!(l512u64, Layout512U64, Node512U64, u64, 62, 30, 62);
