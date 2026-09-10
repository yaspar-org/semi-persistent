// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Differential check for the mark/restore member fan-out: the same
//! saturation-and-backtrack workload driven through `mark_with`/`restore_with`
//! with `par = false` and `par = true` yields identical e-graph observables at
//! every checkpoint (canonical form of every node, class count, node count,
//! and re-add probe ids), and the parallel path observably spawns onto the
//! rayon pool (`take_fanout_witness`).

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::take_fanout_witness;

type Eg = EGraph31<NiraLitVal, true, false>;

const ROUNDS: usize = 6;
const LEAVES_PER_ROUND: usize = 8;

/// The observable state: every node's canonical representative, plus the
/// class count those representatives imply. Two graphs that agree on this
/// vector agree on the whole congruence (node ids are allocation-ordered and
/// the workload is deterministic, so equal ids name equal terms).
fn observables(eg: &Eg) -> (usize, Vec<ENodeId>, usize) {
    let n = eg.node_count();
    let reprs: Vec<ENodeId> = eg.node_ids().map(|id| eg.class_repr(id)).collect();
    let mut roots: Vec<ENodeId> = reprs.clone();
    roots.sort_unstable();
    roots.dedup();
    (n, reprs, roots.len())
}

/// One round of growth: fresh leaves, a parent over each, a chain of merges,
/// and a rebuild. Deterministic, so both instances stay in lockstep.
fn grow(eg: &mut Eg, round: usize) -> Vec<ENodeId> {
    let sort = eg.intern_sort("E");
    let f = eg.register_op1(&format!("f{round}"), sort, sort);
    let leaves: Vec<ENodeId> = (0..LEAVES_PER_ROUND)
        .map(|i| {
            let op = eg.register_op0(&format!("a{round}_{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let parents: Vec<ENodeId> = leaves.iter().map(|&l| eg.add(f, &[l])).collect();
    // Merge every other leaf into the first; congruence then collapses the
    // corresponding parents on rebuild.
    for k in (2..LEAVES_PER_ROUND).step_by(2) {
        eg.merge(leaves[0], leaves[k]);
    }
    eg.rebuild();
    parents
}

#[test]
fn par_fanout_matches_sequential_and_spawns() {
    let mut seq = Eg::new();
    let mut par = Eg::new();
    let mut seq_tokens = Vec::new();
    let mut par_tokens = Vec::new();

    let _ = take_fanout_witness();
    for round in 0..ROUNDS {
        let sp = grow(&mut seq, round);
        let pp = grow(&mut par, round);
        assert_eq!(sp, pp, "round {round}: parent ids diverge");
        seq_tokens.push(seq.mark_with(ShrinkPolicy::Never, false));
        par_tokens.push(par.mark_with(ShrinkPolicy::Never, true));
        assert_eq!(
            observables(&seq),
            observables(&par),
            "round {round}: observables diverge after mark"
        );
    }
    let (mark_spawns, mark_workers) = take_fanout_witness();
    assert_eq!(
        mark_spawns,
        7 * ROUNDS,
        "every parallel mark spawns all seven member closures"
    );
    assert!(
        mark_workers >= 2,
        "the mark fan-out must observably run on more than one rayon worker \
         (got {mark_workers})"
    );

    // Restore to an inner frame, regrow, then restore PAST unrestored inner
    // marks straight to an outer frame: the ordering every member must handle.
    let restores = [4usize, 1, 0];
    for (step, &target) in restores.iter().enumerate() {
        seq_tokens.truncate(target + 1);
        par_tokens.truncate(target + 1);
        seq.restore_with(seq_tokens.pop().unwrap(), false);
        par.restore_with(par_tokens.pop().unwrap(), true);
        assert_eq!(
            observables(&seq),
            observables(&par),
            "restore step {step} (to frame {target}): observables diverge"
        );
        // Regrow after the first restore so the second one crosses a live
        // scope boundary rather than an empty one.
        if step == 0 {
            let sp = grow(&mut seq, ROUNDS + step);
            let pp = grow(&mut par, ROUNDS + step);
            assert_eq!(sp, pp, "post-restore regrow diverges");
            seq_tokens.push(seq.mark_with(ShrinkPolicy::Never, false));
            par_tokens.push(par.mark_with(ShrinkPolicy::Never, true));
        }
    }
    let (restore_spawns, restore_workers) = take_fanout_witness();
    // 3 parallel restores plus 1 parallel regrow mark ran since the reset.
    assert_eq!(
        restore_spawns,
        7 * 4,
        "every parallel restore/mark spawns all seven member closures"
    );
    assert!(
        restore_workers >= 2,
        "the restore fan-out must observably run on more than one rayon \
         worker (got {restore_workers})"
    );

    // Re-add probes: a pre-mark term re-added after the deepest restore must
    // come back with its original id in BOTH instances, and the graphs must
    // still agree node-for-node.
    let sp = grow(&mut seq, 99);
    let pp = grow(&mut par, 99);
    assert_eq!(sp, pp, "final probe parents diverge");
    assert_eq!(
        observables(&seq),
        observables(&par),
        "final observables diverge"
    );
}
