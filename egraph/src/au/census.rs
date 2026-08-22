// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The certification budget of an instance: `sum of A(v)` over the reachable
//! OR states. See `egraph/doc/design/19-anti-unification.md`.
//!
//! MCGS realizes one action edge per playout and reports `Completion::Exact`
//! only after every action of every reachable OR node is realized or proven
//! non-optimal, so the number of playouts a certificate costs is bounded below
//! by `sum over reachable v of A(v)`, the total action count of the search
//! graph. That sum is a property of the instance, not of a run: this module
//! computes it by enumerating the graph without solving anything: no term is
//! interned, no transport problem is costed beyond the feasibility gate the
//! action count itself depends on, and no value is backed up.
//!
//! The enumeration follows the MCGS conventions exactly, because MCGS is what
//! the budget is a prediction about: `A(v)` counts cycle-filtered structural
//! actions plus feasible transport descriptors (one per AC/ACI representation
//! pair), `l == r` nodes are terminal with `A(v) = 0`, and child contexts are
//! derived without the exact solver's identity-padding extension. On an
//! instance with no AC operator the MCGS conventions coincide with side-mode
//! contextual Exact, and their state counts agree; the
//! `census_matches_exact_arena` test pins that internal correspondence. This is
//! not a comparison with pair-mode root Exact's bare-pair graph.
//!
//! Both flavors of pruning shrink the real budget below this number:
//! `dominance_pruning` drops provably non-optimal actions before they are
//! counted against `num_actions`, and a node whose actions are all dropped
//! closes without realization. The census reports the unpruned budget, the
//! quantity the knee prediction is stated over.
//!
//! Enumeration is bounded: `max_states` caps the OR states visited and
//! `deadline` caps the wall time. Either limit sets [`Census::capped`], and
//! the returned counts are then lower bounds on the true ones.

use std::time::Instant;

use crate::canon::{MSetCanon, VarCanon};
use crate::config::{AuIds, EGraphConfig};
use crate::containers::DenseId;
use crate::literal::LitVal;

use super::actions::{ActionCache, generate_actions};
use super::egraph_api::{AuSnapshot, ClassOf};
use super::mcgs::transport_actions;
use super::space::{CycleMode, SearchSpace};

/// The size of one instance's search graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Census {
    /// Reachable OR states, terminals included.
    pub or_states: u64,
    /// `sum of A(v)`: the certification budget, in playouts.
    pub sum_actions: u128,
    /// The widest single node's action count.
    pub max_actions: u64,
    /// Whether `max_states` or `deadline` stopped the enumeration, which makes
    /// both counts lower bounds.
    pub capped: bool,
}

/// Enumerate the reachable OR states of `(l_root, r_root)` and total their
/// action counts. See the module doc for the conventions and the limits.
pub fn certification_budget<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l_root: ClassOf<Cfg>,
    r_root: ClassOf<Cfg>,
    cycle_mode: CycleMode,
    max_states: u64,
    deadline: Option<Instant>,
) -> Result<Census, super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(l_root)?;
    snap.validate_finite_from(r_root)?;

    let mut space: SearchSpace<Cfg::Au> = SearchSpace::new(cycle_mode);
    let mut cache: ActionCache<Cfg::O, Cfg::Au, Cfg::M> =
        ActionCache::without_ac_actions(usize::MAX);
    let (empty_l, empty_r) = space.empty_contexts();
    let (root_or, _) = space.get_or_insert_or_node(
        l_root,
        r_root,
        empty_l,
        empty_r,
        snap.best_size(l_root),
        snap.best_size(r_root),
    );

    let mut census = Census {
        or_states: 0,
        sum_actions: 0,
        max_actions: 0,
        capped: false,
    };
    let mut stack: Vec<<Cfg::Au as AuIds>::Or> = vec![root_or];
    // OR ids are dense and minted in creation order, so a bitmap indexed by id
    // is the visited set.
    let mut visited: Vec<bool> = vec![false; 1];
    let mut since_poll = 0u32;

    while let Some(or_id) = stack.pop() {
        let idx = or_id.to_usize();
        if idx < visited.len() && visited[idx] {
            continue;
        }
        if idx >= visited.len() {
            visited.resize(idx + 1, false);
        }
        visited[idx] = true;
        census.or_states += 1;
        if census.or_states >= max_states {
            census.capped = true;
            break;
        }
        since_poll += 1;
        if since_poll >= 1024 {
            since_poll = 0;
            if deadline.is_some_and(|d| Instant::now() >= d) {
                census.capped = true;
                break;
            }
        }

        let arena_idx = or_id.to_index();
        let l = *space.or_arena.left.get(arena_idx);
        let r = *space.or_arena.right.get(arena_idx);
        if l == r {
            continue;
        }
        let mut n_actions = 0u64;
        generate_actions(snap, &mut cache, l, r);
        let structural: Vec<(Vec<(ClassOf<Cfg>, ClassOf<Cfg>)>, bool)> = cache
            .get(l, r)
            .expect("generate_actions populated the cache")
            .iter()
            .map(|action| {
                let pairs: Vec<(ClassOf<Cfg>, ClassOf<Cfg>)> =
                    action.pairs.iter().map(|p| (p.left, p.right)).collect();
                let blocked = pairs
                    .iter()
                    .any(|(cl, cr)| space.is_cycle_blocked(or_id, *cl, *cr));
                (pairs, blocked)
            })
            .collect();
        for (pairs, blocked) in &structural {
            if *blocked {
                continue;
            }
            n_actions += 1;
            for &(cl, cr) in pairs {
                let child = child_or(snap, &mut space, or_id, cl, cr);
                push_unvisited(&mut stack, &visited, child);
            }
        }

        let descs = transport_actions(snap, &space, or_id, l, r);
        for desc in &descs {
            n_actions += 1;
            let n_cols = desc.right.len();
            for (i, &(lc, _)) in desc.left.iter().enumerate() {
                for (j, &(rc, _)) in desc.right.iter().enumerate() {
                    if !desc.legal_cells[i * n_cols + j] {
                        continue;
                    }
                    let child = child_or(snap, &mut space, or_id, lc, rc);
                    push_unvisited(&mut stack, &visited, child);
                }
            }
        }

        census.sum_actions += u128::from(n_actions);
        census.max_actions = census.max_actions.max(n_actions);
    }

    Ok(census)
}

/// The OR node one child pair lands in, derived as MCGS derives it.
fn child_or<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    parent_or: <Cfg::Au as AuIds>::Or,
    cl: ClassOf<Cfg>,
    cr: ClassOf<Cfg>,
) -> <Cfg::Au as AuIds>::Or
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let (child_ctx_l, child_ctx_r) = space.derive_child_contexts(
        parent_or,
        cl,
        cr,
        |c| snap.reachability().is_reachable(cl, c),
        |c| snap.reachability().is_reachable(cr, c),
    );
    let (or, _) = space.get_or_insert_or_node(
        cl,
        cr,
        child_ctx_l,
        child_ctx_r,
        snap.best_size(cl),
        snap.best_size(cr),
    );
    or
}

fn push_unvisited<O: DenseId>(stack: &mut Vec<O>, visited: &[bool], or: O) {
    let idx = or.to_usize();
    if idx >= visited.len() || !visited[idx] {
        stack.push(or);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::exact;
    use crate::containers::IndexLike;
    use crate::egraph::EGraph31;
    use crate::id::ENodeId;
    use crate::literal::NiraLitVal;

    type Eg = EGraph31<NiraLitVal, false, false>;

    /// A cyclic instance with no AC operator: mutually reachable `w` classes
    /// under a shared binary backbone, the crossover family's shape.
    fn build(cycles: usize, depth: usize) -> (Eg, ENodeId, ENodeId) {
        let mut eg = Eg::new();
        let sort = eg.intern_sort("S");
        let f = eg.register_op2("f", sort, sort, sort);
        let b = eg.register_op2("b", sort, sort, sort);
        let h = eg.register_op1("h", sort, sort);
        let p_op = eg.register_op0("p", sort);
        let w: Vec<ENodeId> = (0..cycles)
            .map(|i| {
                let op = eg.register_op0(&format!("w{i}"), sort);
                eg.add(op, &[])
            })
            .collect();
        let tags: Vec<ENodeId> = (0..cycles)
            .map(|i| {
                let op = eg.register_op0(&format!("t{i}"), sort);
                eg.add(op, &[])
            })
            .collect();
        for &wi in &w {
            let hw = eg.add(h, &[wi]);
            eg.merge(hw, wi);
        }
        for (i, &tag) in tags.iter().enumerate() {
            let member = eg.add(b, &[w[(i + 1) % cycles], tag]);
            eg.merge(member, w[i]);
        }
        eg.rebuild();
        let shared = eg.add(p_op, &[]);
        let mut left = w[0];
        let mut right = w[1 % cycles];
        for _ in 0..depth {
            left = eg.add(f, &[left, shared]);
            right = eg.add(f, &[right, shared]);
        }
        eg.rebuild();
        (eg, left, right)
    }

    /// Without AC the census walks the same states the unpruned contextual
    /// Exact solver creates, so the state counts must agree exactly.
    #[test]
    fn census_matches_exact_arena() {
        for (cycles, depth) in [(2usize, 1usize), (3, 2), (4, 2), (5, 3)] {
            let (eg, left, right) = build(cycles, depth);
            let snap = AuSnapshot::new(&eg).unwrap();
            let l = snap.class_of(left).unwrap();
            let r = snap.class_of(right).unwrap();
            let census =
                certification_budget(&snap, l, r, CycleMode::AncestorOnly, u64::MAX, None).unwrap();
            let run =
                exact::run_exact(&snap, l, r, CycleMode::AncestorOnly, None, false, false).unwrap();
            let arena = run.space.or_arena.len().as_usize() as u64;
            assert_eq!(
                census.or_states, arena,
                "cycles={cycles} depth={depth}: census visited {} OR states, \
                 the exact arena holds {arena}",
                census.or_states
            );
            assert!(!census.capped);
            assert!(census.sum_actions > 0 && census.max_actions > 0);
        }
    }

    #[test]
    fn census_caps_report_lower_bounds() {
        let (eg, left, right) = build(5, 3);
        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(left).unwrap();
        let r = snap.class_of(right).unwrap();
        let full =
            certification_budget(&snap, l, r, CycleMode::AncestorOnly, u64::MAX, None).unwrap();
        let capped = certification_budget(&snap, l, r, CycleMode::AncestorOnly, 3, None).unwrap();
        assert!(capped.capped);
        assert!(capped.or_states <= full.or_states);
        assert!(capped.sum_actions <= full.sum_actions);
    }
}
