// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Test-only JSON dump of the exact solver's search graph.
//!
//! After [`run_exact`] finishes, the OR arena, action cache, and best-result
//! table together describe the full memoized search graph. This module
//! serializes it: one record per OR state (class pair, cycle contexts,
//! memoized optimal cost, chosen action), one record per surviving action
//! (with the child OR ids the solver descended into), and a per-`(l, r)`
//! summary of how many distinct `(ctx_l, ctx_r)` variants each class pair was
//! solved under — the context-duplication evidence for the scaling analysis.
//!
//! Child OR ids and chosen actions are not recorded during the solve; they
//! are re-derived here by replaying each node's action enumeration
//! (generalize incumbent, cached non-AC actions in order, AC/ACI
//! representation-pair cells). The replay is deterministic from the same
//! snapshot and contexts, so every `get_or_insert_or_node` lookup must hit an
//! existing node; the replay asserts that it never creates one.
//!
//! Class names use the smallest concrete member of each class (the instance
//! constants `w0..`, `p`, `dl`, `dr`, `t0..`), via `best_node`'s operator.

use std::collections::HashMap;

use crate::canon::{MSetCanon, VarCanon};
use crate::config::{AuIds, EGraphConfig};
use crate::containers::{DenseId, IndexLike};
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;

use super::ac_repr;
use super::actions::ActionCache;
use super::egraph_api::{AuSnapshot, ClassOf};
use super::exact::ExactRun;
use super::results::BestResults;
use super::space::{CycleContext, SearchSpace};
use super::terms::{TermOp, TermPool, evaluate_generalize_action};

/// One serialized search graph plus the counts the caller reports.
pub(crate) struct Dump {
    pub(crate) json: String,
    pub(crate) n_nodes: usize,
    pub(crate) n_edges: usize,
}

/// The readable name of a class: its smallest concrete member's operator.
fn class_name<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    class: ClassOf<Cfg>,
) -> String
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let eg = snap.egraph();
    eg.ops()
        .info(snap.node_op(snap.best_node(class)))
        .name
        .clone()
}

/// JSON string literal with minimal escaping (quotes, backslashes, controls).
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_name_list(ids: &[usize], names: &HashMap<usize, String>) -> String {
    let items: Vec<String> = ids.iter().map(|c| json_str(&names[c])).collect();
    format!("[{}]", items.join(","))
}

/// One replayed action of one OR node: its label (matches `chosen_action`),
/// its operator name, and the child OR ids the solver descended into.
struct EdgeRow {
    action: String,
    kind: String,
    to: Vec<usize>,
}

/// Replay one non-terminal OR node's action enumeration. Returns the chosen
/// action's label, the surviving-alternative count (generalize included), and
/// the edge rows. Mirrors `solve_iterative`'s evaluation order exactly:
/// generalize incumbent first, cached non-AC actions in order, then AC/ACI
/// representation pairs; strict improvement only.
#[allow(clippy::too_many_arguments)]
fn replay_node<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    cache: &ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    results: &BestResults<Cfg::Au>,
    or_id: <Cfg::Au as AuIds>::Or,
) -> (String, usize, Vec<EdgeRow>)
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let idx = or_id.to_index();
    let l = *space.or_arena.left.get(idx);
    let r = *space.or_arena.right.get(idx);
    let eg = snap.egraph();

    let generalize = evaluate_generalize_action(snap, pool, l, r);
    let mut best_quality = pool.quality(generalize);
    let mut chosen = "generalize".to_owned();
    let mut n_actions = 1usize;
    let mut edges = vec![EdgeRow {
        action: "generalize".to_owned(),
        kind: "generalize".to_owned(),
        to: Vec::new(),
    }];

    // A child pair's OR node, re-derived exactly as the solve derived it. The
    // solve already created every node this can ask for, hence the assert.
    let child_or = |space: &mut SearchSpace<Cfg::Au>,
                    cl: ClassOf<Cfg>,
                    cr: ClassOf<Cfg>,
                    pad: Option<ClassOf<Cfg>>|
     -> <Cfg::Au as AuIds>::Or {
        let (mut child_ctx_l, mut child_ctx_r) = space.derive_child_contexts(
            or_id,
            cl,
            cr,
            |c| snap.reachability().is_reachable(cl, c),
            |c| snap.reachability().is_reachable(cr, c),
        );
        if let Some(id_class) = pad {
            (child_ctx_l, child_ctx_r) =
                space.extend_child_contexts(child_ctx_l, child_ctx_r, id_class);
        }
        let (or, is_new) = space.get_or_insert_or_node(
            cl,
            cr,
            child_ctx_l,
            child_ctx_r,
            snap.best_size(cl),
            snap.best_size(cr),
        );
        assert!(!is_new, "replay repeated a descent the solve never made");
        or
    };

    // Cached non-AC actions, in the solver's order.
    let actions = cache
        .get(l, r)
        .expect("every solved non-terminal node has cached actions")
        .to_vec();
    for (ai, action) in actions.iter().enumerate() {
        if action
            .pairs
            .iter()
            .any(|p| space.is_cycle_blocked(or_id, p.left, p.right))
        {
            continue;
        }
        n_actions += 1;
        let kind = eg.ops().info(action.op).name.clone();
        let label = format!("{kind}[{ai}]");
        let mut to: Vec<usize> = Vec::with_capacity(action.pairs.len());
        let mut child_terms: Vec<(<Cfg::Au as AuIds>::Term, u64)> =
            Vec::with_capacity(action.pairs.len());
        for pair in &action.pairs {
            let or = child_or(space, pair.left, pair.right, None);
            to.push(or.to_usize());
            let term = results
                .best_term(or)
                .expect("every reachable child OR node was solved");
            child_terms.push((term, pair.count.to_u64()));
        }
        let candidate = pool.intern_action_result(
            TermOp::EGraph(action.op),
            &child_terms,
            snap.op_is_commutative(action.op),
        );
        let quality = pool.quality(candidate);
        if quality < best_quality {
            best_quality = quality;
            chosen = label.clone();
        }
        edges.push(EdgeRow {
            action: label,
            kind,
            to,
        });
    }

    // AC/ACI operators: one alternative per representation pair, its children
    // being the unblocked transport cells. The winning matching is a transport
    // solve this replay does not repeat; if the memoized quality beats every
    // candidate above, the winner was a transport pair.
    for op in ac_repr::common_ac_ops(snap, l, r) {
        let kind = eg.ops().info(op).name.clone();
        for (pi, (lm, rm, pad_identity)) in ac_repr::representation_pairs(snap, l, r, op)
            .iter()
            .enumerate()
        {
            n_actions += 1;
            let mut to: Vec<usize> = Vec::new();
            for &(lc, _) in lm {
                for &(rc, _) in rm {
                    if space.is_cycle_blocked(or_id, lc, rc) {
                        continue;
                    }
                    to.push(child_or(space, lc, rc, *pad_identity).to_usize());
                }
            }
            edges.push(EdgeRow {
                action: format!("ac:{kind}#p{pi}"),
                kind: kind.clone(),
                to,
            });
        }
    }

    let memo_quality = results.best_quality(or_id);
    assert!(
        best_quality >= memo_quality,
        "replay found a better candidate than the memoized optimum"
    );
    if memo_quality < best_quality {
        chosen = "ac-transport".to_owned();
    }
    (chosen, n_actions, edges)
}

/// Render a term flat, as a one-line s-expression.
pub(crate) fn term_sexp<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    term: <Cfg::Au as AuIds>::Term,
    col_limit: usize,
) -> String
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let eg = snap.egraph();
    super::pretty::pretty_print(
        pool,
        term,
        |op| match op {
            TermOp::EGraph(o) => eg.ops().info(*o).name.clone(),
            TermOp::Variants => "Variants".to_owned(),
            TermOp::Literal(o, v) => format!("{}#{v:?}", eg.ops().info(*o).name),
        },
        col_limit,
    )
}

/// Serialize the search graph of one exact solve. `include_edges` gates the
/// `edges` array (drop it for large graphs); nodes and the per-pair summary
/// are always emitted. Replaying mutates nothing observably: every context
/// and term the replay interns was already interned by the solve.
pub(crate) fn dump_search_graph<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    run: &mut ExactRun<Cfg>,
    label: &str,
    include_edges: bool,
) -> Dump
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let ExactRun {
        term,
        pool,
        space,
        cache,
        results,
        root_or,
        complete: _,
    } = run;
    let n_nodes = space.or_arena.len().as_usize();

    // Pass 1: raw per-node state, the class-name table, and the per-(l, r)
    // context-variant counts.
    struct NodeRow {
        l: usize,
        r: usize,
        ctx_l: Vec<usize>,
        ctx_r: Vec<usize>,
        best: (u32, u32),
        terminal: bool,
    }
    let mut rows: Vec<NodeRow> = Vec::with_capacity(n_nodes);
    let mut names: HashMap<usize, String> = HashMap::new();
    let mut variants: HashMap<(usize, usize), usize> = HashMap::new();
    for i in 0..n_nodes {
        let or: <Cfg::Au as AuIds>::Or = crate::id::id_at(i);
        let idx = or.to_index();
        let l = *space.or_arena.left.get(idx);
        let r = *space.or_arena.right.get(idx);
        let (ctx_l, ctx_r): (Vec<usize>, Vec<usize>) = match space.cycle_context(or) {
            CycleContext::Sides { left, right } => (
                left.iter().map(|c| c.to_usize()).collect(),
                right.iter().map(|c| c.to_usize()).collect(),
            ),
            CycleContext::Pairs(pairs) => (
                pairs.iter().map(|(left, _)| left.to_usize()).collect(),
                pairs.iter().map(|(_, right)| right.to_usize()).collect(),
            ),
        };
        for &c in ctx_l.iter().chain(ctx_r.iter()) {
            names
                .entry(c)
                .or_insert_with(|| class_name(snap, crate::id::id_at::<ClassOf<Cfg>>(c)));
        }
        names
            .entry(l.to_usize())
            .or_insert_with(|| class_name(snap, l));
        names
            .entry(r.to_usize())
            .or_insert_with(|| class_name(snap, r));
        *variants.entry((l.to_usize(), r.to_usize())).or_insert(0) += 1;
        rows.push(NodeRow {
            l: l.to_usize(),
            r: r.to_usize(),
            ctx_l,
            ctx_r,
            best: results.best_quality(or),
            terminal: *space.or_arena.terminal.get(idx),
        });
    }

    // Pass 2: replay each non-terminal node's actions.
    let mut chosen: Vec<(String, usize)> = Vec::with_capacity(n_nodes);
    let mut edges: Vec<(usize, EdgeRow)> = Vec::new();
    for i in 0..n_nodes {
        let or: <Cfg::Au as AuIds>::Or = crate::id::id_at(i);
        if rows[i].terminal {
            chosen.push(("terminal".to_owned(), 0));
            continue;
        }
        let (choice, n_actions, node_edges) = replay_node(snap, space, pool, cache, results, or);
        chosen.push((choice, n_actions));
        edges.extend(node_edges.into_iter().map(|e| (i, e)));
    }
    assert_eq!(
        space.or_arena.len().as_usize(),
        n_nodes,
        "replay must not create OR nodes"
    );

    // Assemble.
    let mut out = String::new();
    out.push_str("{\n");
    out.push_str(&format!("  \"instance\": {},\n", json_str(label)));
    out.push_str(&format!(
        "  \"cycle_mode\": {},\n",
        json_str(&format!("{:?}", space.cycle_mode))
    ));
    out.push_str(&format!("  \"root_or\": {},\n", root_or.to_usize()));
    out.push_str(&format!("  \"n_or_states\": {n_nodes},\n"));
    let (size, vmass) = pool.quality(*term);
    out.push_str(&format!(
        "  \"optimal\": {{\"size\": {size}, \"variant_mass\": {vmass}, \"term\": {}}},\n",
        json_str(&term_sexp(snap, pool, *term, usize::MAX))
    ));

    out.push_str("  \"nodes\": [\n");
    for (i, row) in rows.iter().enumerate() {
        let (choice, n_actions) = &chosen[i];
        out.push_str(&format!(
            "    {{\"or_id\": {i}, \"l\": {}, \"r\": {}, \"ctx_l\": {}, \"ctx_r\": {}, \
             \"best_cost\": {}, \"best_vmass\": {}, \"chosen_action\": {}, \"n_actions\": {}}}{}\n",
            json_str(&names[&row.l]),
            json_str(&names[&row.r]),
            json_name_list(&row.ctx_l, &names),
            json_name_list(&row.ctx_r, &names),
            row.best.0,
            row.best.1,
            json_str(choice),
            n_actions,
            if i + 1 < rows.len() { "," } else { "" }
        ));
    }
    out.push_str("  ],\n");

    if include_edges {
        out.push_str("  \"edges\": [\n");
        for (i, (from, edge)) in edges.iter().enumerate() {
            let to: Vec<String> = edge.to.iter().map(usize::to_string).collect();
            out.push_str(&format!(
                "    {{\"from_or\": {from}, \"action\": {}, \"action_kind\": {}, \"to_or\": [{}]}}{}\n",
                json_str(&edge.action),
                json_str(&edge.kind),
                to.join(","),
                if i + 1 < edges.len() { "," } else { "" }
            ));
        }
        out.push_str("  ],\n");
    }

    let mut summary: Vec<((usize, usize), usize)> = variants.into_iter().collect();
    summary.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    out.push_str("  \"pair_context_variants\": [\n");
    for (i, ((l, r), n)) in summary.iter().enumerate() {
        out.push_str(&format!(
            "    {{\"l\": {}, \"r\": {}, \"n_context_variants\": {}}}{}\n",
            json_str(&names[l]),
            json_str(&names[r]),
            n,
            if i + 1 < summary.len() { "," } else { "" }
        ));
    }
    out.push_str("  ]\n}\n");

    Dump {
        json: out,
        n_nodes,
        n_edges: edges.len(),
    }
}

// ---------------------------------------------------------------------------
// Tests: build small crossover instances (mirroring
// egraph/tests/au_scaling_crossover.rs `build_instance`), run the exact
// solver, and dump.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::space::CycleMode;
    use crate::egraph::EGraph31;
    use crate::id::{ENodeId, OpId};
    use crate::literal::NiraLitVal;

    type Eg = EGraph31<NiraLitVal, false, false>;

    /// Mirror of `build_instance` from tests/au_scaling_crossover.rs (same
    /// mechanism, no symbolic trace): `cycles` mutually reachable cyclic W
    /// classes, `width` same-op `b` members each, and a depth-`depth` binary
    /// `f` backbone whose leaves cycle through hot (distinct W pair), shared
    /// (`p`), and diff (`dl`/`dr`) kinds.
    fn build_crossover(depth: usize, width: usize, cycles: usize) -> (Eg, ENodeId, ENodeId) {
        assert!(cycles >= 2, "hot leaves need two distinct W classes");
        let mut eg = Eg::new();
        let sort = eg.intern_sort("S");
        let f = eg.register_op2("f", sort, sort, sort); // shared backbone
        let b = eg.register_op2("b", sort, sort, sort); // shared width op
        let h = eg.register_op1("h", sort, sort); // shared self-wrap op
        let p_op = eg.register_op0("p", sort); // shared filler leaf
        let dl_op = eg.register_op0("dl", sort); // left-only fresh leaf
        let dr_op = eg.register_op0("dr", sort); // right-only fresh leaf
        let w_ops: Vec<OpId> = (0..cycles)
            .map(|i| eg.register_op0(&format!("w{i}"), sort))
            .collect();
        let tag_ops: Vec<OpId> = (0..cycles)
            .map(|i| eg.register_op0(&format!("t{i}"), sort))
            .collect();

        let w: Vec<ENodeId> = w_ops.iter().map(|&op| eg.add(op, &[])).collect();
        let tags: Vec<ENodeId> = tag_ops.iter().map(|&op| eg.add(op, &[])).collect();
        for &wi in &w {
            let hw = eg.add(h, &[wi]);
            eg.merge(hw, wi);
        }
        let fan = width.min(cycles - 1);
        for (i, &tag) in tags.iter().enumerate() {
            for j in 1..=fan {
                let target = w[(i + j) % cycles];
                let member = eg.add(b, &[target, tag]);
                eg.merge(member, w[i]);
            }
        }
        eg.rebuild();

        let shared = eg.add(p_op, &[]);
        let dl = eg.add(dl_op, &[]);
        let dr = eg.add(dr_op, &[]);
        let n_leaves = 1usize << depth;
        let mut left_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
        let mut right_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
        for t in 0..n_leaves {
            match t % 4 {
                0 => {
                    left_level.push(w[t % cycles]);
                    right_level.push(w[(t + 1) % cycles]);
                }
                2 => {
                    left_level.push(dl);
                    right_level.push(dr);
                }
                _ => {
                    left_level.push(shared);
                    right_level.push(shared);
                }
            }
        }
        while left_level.len() > 1 {
            left_level = left_level.chunks(2).map(|c| eg.add(f, c)).collect();
            right_level = right_level.chunks(2).map(|c| eg.add(f, c)).collect();
        }
        eg.rebuild();
        (eg, left_level[0], right_level[0])
    }

    /// Solve one instance exactly, print the optimal term and OR-state count,
    /// and write (or size-check) the JSON dump. Edges are dropped when the
    /// graph exceeds ~50k nodes or the serialized dump exceeds ~5 MB.
    fn dump_case(depth: usize, width: usize, cycles: usize, file: &str, dir: Option<&str>) {
        let (eg, left, right) = build_crossover(depth, width, cycles);
        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(left).unwrap();
        let r = snap.class_of(right).unwrap();
        let mut run =
            crate::au::exact::run_exact(&snap, l, r, CycleMode::AncestorOnly, None, false, false)
                .unwrap();

        let label = format!("crossover depth={depth} width={width} cycles={cycles}");
        let n_nodes = run.space.or_arena.len().as_usize();
        let mut dump = dump_search_graph(&snap, &mut run, &label, n_nodes < 50_000);
        if dump.json.len() > 5_000_000 {
            dump = dump_search_graph(&snap, &mut run, &label, false);
            println!("{label}: dump exceeded 5 MB, edges dropped");
        }

        let (size, vmass) = run.pool.quality(run.term);
        println!(
            "{label}: {n_nodes} OR states, {} edges dumped",
            dump.n_edges
        );
        println!("{label}: optimal size={size} variant_mass={vmass}");
        println!("{label}: optimal term:");
        println!("{}", term_sexp(&snap, &run.pool, run.term, 72));
        assert!(!dump.json.is_empty());
        assert_eq!(dump.n_nodes, n_nodes);
        match dir {
            Some(dir) => {
                let path = std::path::Path::new(dir).join(file);
                std::fs::write(&path, &dump.json).unwrap();
                println!(
                    "{label}: wrote {} ({} bytes)",
                    path.display(),
                    dump.json.len()
                );
            }
            None => println!("{label}: AU_DUMP_DIR unset, skipped writing {file}"),
        }
    }

    /// Manual dump of the search graphs behind the scaling-crossover analysis.
    /// Run with:
    /// `AU_DUMP_DIR=... cargo test -p semi-persistent-egraph --lib -- --ignored --nocapture dump_crossover_search_graphs`
    #[test]
    #[ignore = "manual: dumps exact-solver search graphs as JSON (set AU_DUMP_DIR)"]
    fn dump_crossover_search_graphs() {
        let dir = std::env::var("AU_DUMP_DIR").ok();
        let dir = dir.as_deref();
        dump_case(2, 2, 2, "au-graph-c2.json", dir);
        dump_case(2, 2, 3, "au-graph-c3.json", dir);
        dump_case(4, 9, 2, "au-summary-d4w9c2.json", dir);
    }

    /// Context-subsumption acceptance on the c3 dump instance (depth=2 width=2 cycles=3, the
    /// `au-graph-c3.json` case): context subsumption shrinks the OR-state
    /// count from 23 to 19 at unchanged optimal quality, and the counts are
    /// pinned for all four flag combinations so a regression in the reuse
    /// condition (too strict: count rises; unsound: the quality assert in
    /// `au_differential.rs` catches it) fails here.
    ///
    /// One state per distinct class pair would predict 23 -> 14. That
    /// is not reachable by entry-time reuse: four of the nine duplicate
    /// states are context variants nested inside the first occurrence's own
    /// solve (a W pair's self-re-entry through its `h` member), entered
    /// while that first occurrence is still `Visiting`, so no completed
    /// bare-pair result exists to reuse; one more is a duplicated terminal,
    /// which has no children to save. The remaining four collapse (23 -> 19,
    /// one reuse of the (w2, w0) pair dropping its whole subtree). Projection
    /// pruning removes the self-re-entry descents outright (bound 3 > the
    /// generalize incumbent 2) and collapses the instance to 6 states with
    /// or without subsumption, which isolates context reuse from pruning in
    /// numbers: at this scale pruning subsumes the win.
    ///
    /// The dump replay is not run on the subsumed solve: reused states have
    /// no expanded children to replay.
    #[test]
    fn context_subsumption_collapses_c3_states() {
        let (eg, left, right) = build_crossover(2, 2, 3);
        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(left).unwrap();
        let r = snap.class_of(right).unwrap();
        let reference =
            crate::au::exact::run_exact(&snap, l, r, CycleMode::AncestorOnly, None, false, false)
                .unwrap();
        let reference_quality = reference.pool.quality(reference.term);
        for (pruning, subsumption, states) in [
            (false, false, 23),
            (false, true, 19),
            (true, false, 6),
            (true, true, 6),
        ] {
            let run = crate::au::exact::run_exact(
                &snap,
                l,
                r,
                CycleMode::AncestorOnly,
                None,
                pruning,
                subsumption,
            )
            .unwrap();
            assert_eq!(
                run.pool.quality(run.term),
                reference_quality,
                "pruning={pruning} subsumption={subsumption}: exact optimum changed"
            );
            assert_eq!(
                run.space.or_arena.len().as_usize(),
                states,
                "pruning={pruning} subsumption={subsumption}: OR-state count moved"
            );
        }
    }

    /// The dump machinery itself stays green in CI: non-empty JSON, node
    /// count matching the arena, and a replay that neither creates OR nodes
    /// nor beats the memoized optimum (both asserted inside the dump).
    #[test]
    fn dump_replay_is_consistent() {
        let (eg, left, right) = build_crossover(2, 2, 2);
        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(left).unwrap();
        let r = snap.class_of(right).unwrap();
        let mut run =
            crate::au::exact::run_exact(&snap, l, r, CycleMode::AncestorOnly, None, false, false)
                .unwrap();
        let dump = dump_search_graph(&snap, &mut run, "consistency", true);
        assert!(dump.n_nodes > 0);
        assert!(dump.n_edges >= dump.n_nodes - 1);
        assert!(dump.json.contains("\"pair_context_variants\""));
    }
}
