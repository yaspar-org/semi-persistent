// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The stops of a `:flatten` enumeration (`crate::flatten`, "Three bounds" and
//! "Regrouped views"), reached by lowering the bounds (`MatchPool::set_flatten_bounds`):
//! each stop is counted on the pool (`flatten_skipped`, `flatten_regroup_truncated`), and
//! the matches a stopped run reports are matches of the run without bounds, never
//! others (`regroupBounded_query_exact` is the exactness the counters being zero gives;
//! this is the soundness the counters being nonzero keeps).

use std::collections::BTreeSet;

use semi_persistent_egraph::ematch::{MatchPool, run_query_into};
use semi_persistent_egraph::flatten::FlattenBounds;
use semi_persistent_egraph::id::{ENodeId, SortId};
use semi_persistent_egraph::index::{IndexStore, VariantIndex};
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::schedule::{IndexStats, schedule_with_stats};

type EG = semi_persistent_egraph::EGraph<DefaultConfig, MachineLit, true, false>;

/// `F{ab, cd}` over `ab ∋ F{A, B}` and `cd ∋ F{C, D}`, and `F{A, B, C, D}` itself: the
/// flattened node opens both children, and the flat node regroups by both.
const PROGRAM: &str = "\
(sort E)
(function A () E) (function B () E) (function C () E) (function D () E)
(function F (E) E :assoc-comm)
(let ab (F (A) (B)))
(let cd (F (C) (D)))
(let abcd (F (A) (B) (C) (D)))
(let t (F ab cd))
";

fn build() -> EG {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(PROGRAM).expect("parse");
    let mut it =
        Interpreter::<DefaultConfig, MachineLit, MachineModel, true, false>::new(MachineModel);
    let mut globals = GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut it.eg,
        &it.model,
        &mut globals,
    )
    .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    let mut eg = it.eg;
    eg.rebuild();
    eg
}

/// A match of `(F x y)` as (root class, x class, y class).
type Key = (ENodeId, ENodeId, ENodeId);

/// Run `(F x y)` under `:flatten` with `bounds`; the matches and the pool's counters
/// (skipped, regroup-truncated, overflowed).
fn run(eg: &EG, bounds: FlattenBounds) -> (BTreeSet<Key>, (usize, usize, usize)) {
    let index = IndexStore::build(eg);
    let pats = semi_persistent_egraph::parser::parse_patterns("(F x y)").expect("parse");
    let fq = semi_persistent_egraph::sortcheck::flatten_surface(&pats, eg.ops()).expect("flatten");
    let mut rq = semi_persistent_egraph::resolve::resolve(
        &fq,
        eg.ops(),
        eg.sorts(),
        &MachineModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .expect("resolve");
    rq.flatten = true;
    let root = rq.shape.find_var(&fq.root_vars[0]).expect("root");
    let x = rq.shape.find_var("x").expect("x");
    let y = rq.shape.find_var("y").expect("y");
    let plan = schedule_with_stats(&rq, &IndexStats::from_index(&index));
    let globals = GlobalCtx::<SortId, ENodeId>::new();
    let mut pool = MatchPool::<DefaultConfig>::new();
    pool.set_flatten_bounds(bounds);
    run_query_into(&plan, eg, &VariantIndex::naive(&index), &globals, &mut pool);
    let canon = |g: ENodeId| eg.find_const(g);
    let keys = (0..pool.len())
        .map(|j| {
            let m = pool.clone_match(j);
            (canon(m.get(root)), canon(m.get(x)), canon(m.get(y)))
        })
        .collect();
    (
        keys,
        (
            pool.flatten_skipped(),
            pool.flatten_regroup_truncated(),
            pool.flatten_overflowed(),
        ),
    )
}

/// The class of the global `name`.
fn class(eg: &mut EG, name: &str) -> ENodeId {
    let op = eg.ops().id_by_name(name).expect(name);
    let g = eg.add(op, &[]);
    eg.find(g)
}

/// The run without bounds stops nowhere, and finds the regrouped match `F{ab, cd}` on
/// the flat node (`flatten_regroup_ac.egg` pins the fixture-level behaviour).
#[test]
fn unbounded_run_is_exact() {
    let mut eg = build();
    let (keys, counters) = run(&eg, FlattenBounds::DEFAULT);
    assert_eq!(counters, (0, 0, 0), "no stop without bounds");
    let f = eg.ops().id_by_name("F").expect("F");
    let (a, b, c, d) = (
        class(&mut eg, "A"),
        class(&mut eg, "B"),
        class(&mut eg, "C"),
        class(&mut eg, "D"),
    );
    let ab = eg.add(f, &[a, b]);
    let ab = eg.find(ab);
    let cd = eg.add(f, &[c, d]);
    let cd = eg.find(cd);
    let abcd = eg.add(f, &[a, b, c, d]);
    let abcd = eg.find(abcd);
    assert!(
        keys.contains(&(abcd, ab, cd)),
        "regrouped match missing: {keys:?}"
    );
    assert!(
        keys.contains(&(abcd, cd, ab)),
        "regrouped match missing: {keys:?}"
    );
}

/// A run that stops is counted on the pool, and reports matches of the run without
/// bounds only.
fn assert_sound_stop(
    bounds: FlattenBounds,
    counter: fn((usize, usize, usize)) -> usize,
    what: &str,
) {
    let eg = build();
    let (full, _) = run(&eg, FlattenBounds::DEFAULT);
    let (keys, counters) = run(&eg, bounds);
    assert!(
        counter(counters) > 0,
        "{what}: not counted, counters {counters:?}"
    );
    assert!(
        keys.is_subset(&full),
        "{what}: matches not in the unbounded run: {:?}",
        keys.difference(&full).collect::<Vec<_>>()
    );
}

/// `MAX_REGROUP_VIEWS`: regrouping stops after the first regrouped record.
#[test]
fn regroup_views_bound_truncates() {
    assert_sound_stop(
        FlattenBounds {
            regroup_views: 1,
            ..FlattenBounds::DEFAULT
        },
        |c| c.1,
        "regroup views",
    );
}

/// `MAX_REGROUP_WORK`: regrouping stops on the first candidate examined.
#[test]
fn regroup_work_bound_truncates() {
    assert_sound_stop(
        FlattenBounds {
            regroup_work: 1,
            ..FlattenBounds::DEFAULT
        },
        |c| c.1,
        "regroup work",
    );
}

/// `MAX_ELEMS`: the stored view elements run out while regrouping, and the node is skipped.
#[test]
fn elems_bound_skips_the_node() {
    assert_sound_stop(
        FlattenBounds {
            elems: 6,
            ..FlattenBounds::DEFAULT
        },
        |c| c.0,
        "elems",
    );
}

/// `MAX_VIEWS`: the first complete combination is past the bound, and the node is skipped.
#[test]
fn views_bound_skips_the_node() {
    assert_sound_stop(
        FlattenBounds {
            views: 0,
            ..FlattenBounds::DEFAULT
        },
        |c| c.0,
        "views",
    );
}

/// `MAX_WORK`: the second option taken is past the bound, and the node is skipped.
#[test]
fn work_bound_skips_the_node() {
    assert_sound_stop(
        FlattenBounds {
            work: 1,
            ..FlattenBounds::DEFAULT
        },
        |c| c.0,
        "work",
    );
}
