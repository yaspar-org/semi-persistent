// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `HintedArena` differential test: the verified probe against a naive linear
//! scan of the live column, through pushes, recanonize-style rewrites, marks
//! and deep restores.
//!
//! The theorems say a probe can never miss a collision; this drives the
//! oscillation pattern that made the e-graph's unverified predecessor loop
//! (a cell rewritten to new content and then rolled BACK to the old one, with
//! another cell holding that same old content), plus deep restores past
//! several marks.
use semi_persistent_containers_verus::hinted_arena::HintedArena;
use semi_persistent_containers_verus::{ShrinkPolicy, StoreKind};

type Node = semi_persistent_containers_verus::Pair<u32, u32>;

fn node(a: u32, b: u32) -> Node {
    semi_persistent_containers_verus::Pair { a, b }
}

fn oracle_probe(live: &[Node], t: &Node) -> Option<usize> {
    live.iter().position(|c| c.a == t.a && c.b == t.b)
}

fn check(arena: &HintedArena<Node, u32, true>, live: &[Node], ctx: &str) {
    // Every live content must be findable (completeness), and every probe
    // answer must really collide (soundness).
    for (i, c) in live.iter().enumerate() {
        let got = arena.probe(c);
        assert!(
            got.is_some(),
            "{ctx}: probe missed live cell {i} ({c:?}) - completeness violated"
        );
        let id = got.unwrap() as usize;
        assert!(id < live.len(), "{ctx}: probe returned dead id {id}");
        assert!(
            live[id].a == c.a && live[id].b == c.b,
            "{ctx}: probe returned non-colliding cell"
        );
    }
    // Absent contents must probe None.
    for k in 0..40u32 {
        let t = node(k, 0xDEAD_0000 + k);
        let got = arena.probe(&t);
        let want = oracle_probe(live, &t);
        assert_eq!(
            got.is_some(),
            want.is_some(),
            "{ctx}: probe/oracle disagree on {t:?}"
        );
    }
}

#[test]
fn probe_matches_scan_through_marks_and_restores() {
    for kind in [StoreKind::Inline, StoreKind::Parallel, StoreKind::Trail] {
        let mut arena = HintedArena::<Node, u32, true>::new_kind(kind);
        let mut live: Vec<Node> = Vec::new();
        let mut marks: Vec<(semi_persistent_containers_verus::VecToken, Vec<Node>)> = Vec::new();

        // Build a column with heavy fingerprint collisions (same `a`).
        for i in 0..24u32 {
            let n = node(i % 4, i);
            arena.push(n).expect("capacity");
            live.push(n);
        }
        check(&arena, &live, "after build");

        // Mark, then rewrite cells (recanonize shape) including an
        // oscillation: cell 5 takes cell 9's content and back.
        for depth in 0..5u32 {
            let tok = arena.mark(ShrinkPolicy::Never).expect("mark");
            marks.push((tok, live.clone()));
            for w in 0..6u32 {
                let idx = (depth * 3 + w) % 24;
                let n = node((idx + depth) % 4, 1000 * depth + w);
                arena.set(idx, n);
                live[idx as usize] = n;
            }
            // Oscillate cell 5 onto cell 9's content, then back.
            let c9 = live[9];
            arena.set(5, c9);
            live[5] = c9;
            let back = node(1, 5);
            arena.set(5, back);
            live[5] = back;
            check(&arena, &live, "after frame writes");
        }

        // Deep restore past four marks: the index does no work, so this is
        // exactly where a missed collision would show.
        let (tok, snap) = marks[1].clone();
        arena.restore(tok).expect("restore");
        live = snap;
        check(&arena, &live, "after deep restore");

        // Post-restore writes must still be found.
        for w in 0..5u32 {
            let n = node(3, 7000 + w);
            arena.set(w, n);
            live[w as usize] = n;
        }
        check(&arena, &live, "after post-restore writes");
    }
}
