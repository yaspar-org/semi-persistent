// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The cursor matcher (`ematch::MatchIterator`, `run_query_iter`) against the recursive
//! one (`run_query`) on the n-ary decompositions' corner shapes: a sequence pattern
//! against a node shorter than its fixed children or with no window that binds, in each
//! pre/suffix shape (`enter_expand_a`); an exact AC or ACI pattern with several free
//! elements, whose later assignments the cursor finds by backtracking (`backtrack`,
//! `ACDecompose`/`ACIDecompose` without a rest); an exact pattern on a node with more
//! entries than elements; and a rest-only pattern. The two matchers must find the same
//! match set, and that set must be the one the shapes describe.

use std::collections::BTreeSet;

use semi_persistent_egraph::ast::{MsetVarId, SeqVarId, SetVarId};
use semi_persistent_egraph::config::EGraphConfig;
use semi_persistent_egraph::ematch::{Match, run_query, run_query_iter};
use semi_persistent_egraph::id::{ENodeId, SortId};
use semi_persistent_egraph::index::{IndexStore, VariantIndex};
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::multiplicity::MultiplicityLike;
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::{GlobalCtx, MatchShape};
use semi_persistent_egraph::schedule::{IndexStats, schedule_with_stats};

type EG = semi_persistent_egraph::EGraph<DefaultConfig, MachineLit, true, false>;

const PROGRAM: &str = "\
(sort E)
(function a () E) (function b () E) (function c () E) (function k () E)
(function S (E) E :assoc)
(function F (E) E :assoc-comm)
(function G (E) E :assoc-comm-idem)
(let short (S (a) (b)))
(let long (S (a) (b) (c)))
(let fab (F (a) (b)))
(let fabc (F (a) (b) (c)))
(let gabc (G (a) (b) (c)))
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

/// A match, canonized: every node binding, then every rest, as text.
fn key(m: &Match<DefaultConfig>, shape: &MatchShape, eg: &EG) -> String {
    let canon = |g: ENodeId| eg.find_const(g).to_usize();
    let mut parts: Vec<String> = m
        .nodes
        .iter()
        .map(|g| g.map(canon).map_or("_".to_string(), |c| c.to_string()))
        .collect();
    for i in 0..shape.seqs.len() {
        let s = m.seq_slice(SeqVarId::new(u16::try_from(i).expect("index")));
        parts.push(format!(
            "seq{:?}",
            s.iter().map(|&g| canon(g)).collect::<Vec<_>>()
        ));
    }
    for i in 0..shape.sets.len() {
        let s = m.set_slice(SetVarId::new(u16::try_from(i).expect("index")));
        let mut v: Vec<_> = s.iter().map(|&g| canon(g)).collect();
        v.sort_unstable();
        parts.push(format!("set{v:?}"));
    }
    for i in 0..shape.msets.len() {
        let s = m.mset_slice(MsetVarId::new(u16::try_from(i).expect("index")));
        let mut v: Vec<_> = s
            .iter()
            .map(|c| {
                (
                    canon(DefaultConfig::mset_child_id(c)),
                    DefaultConfig::mset_child_mult(c).to_u64().expect("count"),
                )
            })
            .collect();
        v.sort_unstable();
        parts.push(format!("mset{v:?}"));
    }
    parts.join(" ")
}

/// Both matchers' match sets for `pattern`, which must agree; the set is returned.
fn agree(eg: &EG, pattern: &str) -> BTreeSet<String> {
    let index = IndexStore::build(eg);
    let pats = semi_persistent_egraph::parser::parse_patterns(pattern).expect("parse");
    let fq = semi_persistent_egraph::sortcheck::flatten_surface(&pats, eg.ops()).expect("flatten");
    let rq = semi_persistent_egraph::resolve::resolve(
        &fq,
        eg.ops(),
        eg.sorts(),
        &MachineModel,
        &GlobalCtx::<SortId, ()>::new(),
    )
    .expect("resolve");
    let plan = schedule_with_stats(&rq, &IndexStats::from_index(&index));
    let vindex = VariantIndex::naive(&index);
    let globals = GlobalCtx::<SortId, ENodeId>::new();
    let recursive: BTreeSet<String> = run_query(&plan, eg, &vindex, &globals)
        .iter()
        .map(|m| key(m, &rq.shape, eg))
        .collect();
    let cursor: Vec<String> = run_query_iter(&plan, eg, &vindex)
        .iter()
        .map(|m| key(m, &rq.shape, eg))
        .collect();
    let cursor_set: BTreeSet<String> = cursor.iter().cloned().collect();
    assert_eq!(
        cursor.len(),
        cursor_set.len(),
        "{pattern}: the cursor repeated a match: {cursor:?}"
    );
    assert_eq!(cursor_set, recursive, "{pattern}: the matchers disagree");
    recursive
}

/// Sequence windows: three fixed children fit the three-element node at its one window
/// and not the two-element node; a constant child absent from both nodes binds nowhere.
#[test]
fn sequence_windows_short_node_and_no_binding() {
    let eg = build();
    for (pattern, n) in [
        ("(S ..p x y z ..s)", 1),
        ("(S x y z)", 1),
        ("(S ..p x y z)", 1),
        ("(S x y z ..s)", 1),
        ("(S ..p (k) ..s)", 0),
        ("(S x (k))", 0),
        ("(S ..p (k))", 0),
        ("(S (k) ..s)", 0),
        // A window exists in each sequence; the two-element one gives one, the other two.
        ("(S ..p x y ..s)", 3),
    ] {
        assert_eq!(agree(&eg, pattern).len(), n, "{pattern}");
    }
}

/// Exact AC and ACI patterns with three free elements over the entries `{a, b}` and
/// `{a, b, c}`: on the three-entry node every order is a match, and on the two-entry node
/// the third element fails and the search must backtrack. The cursor's initial search
/// (`ac_find_first`, `aci_find_first`) scanned every element but the first from entry 0
/// after a backtrack, re-took the entry just undone and never terminated; it now resumes
/// from the advanced index (GUIDE.md §10, item 19).
#[test]
fn exact_decompositions_backtrack_without_a_rest() {
    let eg = build();
    assert_eq!(agree(&eg, "(F x y z)").len(), 6);
    assert_eq!(agree(&eg, "(G x y z)").len(), 6);
}

/// Exact and rest-only patterns the cursor handles: two elements over `F{a, b}` fit in
/// both orders and leave an entry of `F{a, b, c}` behind, which is no match; a rest-only
/// pattern matches each node once.
#[test]
fn exact_and_rest_only_patterns() {
    let eg = build();
    assert_eq!(agree(&eg, "(F x y)").len(), 2);
    assert_eq!(agree(&eg, "(G x y)").len(), 0);
    assert_eq!(agree(&eg, "(F ..r)").len(), 2);
    assert_eq!(agree(&eg, "(G ..r)").len(), 1);
}
