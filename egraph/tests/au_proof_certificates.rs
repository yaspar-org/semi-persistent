// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Prototype of the AU proof-certificate generation pipeline
//! (egraph/doc/future/au-proof-certificates.md §5) under `PROOFS = true`.
//!
//! Exercises, end to end: run exact AU on a proof-mode e-graph, materialize
//! both projections of the backbone (each AU variable replaced by a witness
//! from its left resp. right class), re-add them, and extract equality chains
//! with `explain_deep`. Each certificate test prints the full §1 certificate
//! `(t, s1, s2, chain1, chain2)` as a self-contained block: input terms and
//! equalities, backbone with variables, both substitutions, and both chains
//! with the from/to terms of every step rendered as s-expressions.
//!
//! Key empirical finding, pinned by `certificate_trace_free_operators`: the
//! pipeline as written in §5 (materialize the projections AFTER the justified
//! merges) produces only EMPTY chains. `EGraph::add` canonicalizes children
//! by `find` before hash-consing, and rebuild recanonizes stored children to
//! representatives, so every node of an instantiated projection interns to an
//! already-existing node of the same class — inductively the whole instance
//! interns to the root's node id itself. The §5 step-4 claim "congruence
//! closure merges the instantiated spine up to the roots" never fires: there
//! is no fresh spine, and `chain1`/`chain2` are reflexivity. Non-trivial
//! chains require a two-phase replay: restore to a pre-merge mark, add the
//! instances there (fresh nodes, since the leaf classes are still distinct),
//! re-apply the justified merges, rebuild. Phase B below does exactly that
//! and recovers the chains the certificate needs.

use std::collections::HashMap;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, AuResult, anti_unify};
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::{AxiomId, ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::multiplicity::MultiplicityLike;
use semi_persistent_egraph::nodes::{DefaultConfig, LitValId};
use semi_persistent_egraph::union_find::{Justification, ProofBuf};

type Eg<const TRACK: bool, const PROOFS: bool> = EGraph31<NiraLitVal, TRACK, PROOFS>;

// ---------------------------------------------------------------------------
// Projection materialization, copied from egraph/tests/au_metamorphic.rs
// (own_projected / materialize / projected_terms).
// ---------------------------------------------------------------------------

/// Own a projected result so the snapshot and result borrows can end before
/// the projection is materialized back into the mutable e-graph.
#[derive(Clone, Debug)]
enum OwnedTerm {
    App(OpId, Vec<OwnedTerm>),
    Lit(OpId, LitValId),
}

fn own_projected(pool: &TermPool<OpId, LitValId>, id: TermId) -> OwnedTerm {
    match pool.op(id) {
        TermOp::EGraph(op) => OwnedTerm::App(
            *op,
            pool.children(id)
                .iter()
                .map(|&child| own_projected(pool, child))
                .collect(),
        ),
        TermOp::Literal(op, value) => OwnedTerm::Lit(*op, *value),
        TermOp::Variants => panic!("projection still contains Variants"),
    }
}

fn materialize<const T: bool, const P: bool>(eg: &mut Eg<T, P>, term: &OwnedTerm) -> ENodeId {
    match term {
        OwnedTerm::App(op, children) => {
            let child_ids: Vec<ENodeId> = children.iter().map(|c| materialize(eg, c)).collect();
            eg.add(*op, &child_ids)
        }
        OwnedTerm::Lit(op, value) => eg.add_lit(*op, *value),
    }
}

fn projected_terms(mut result: AuResult<DefaultConfig>) -> (OwnedTerm, OwnedTerm) {
    let left = result.pool.project(result.term_id, 0);
    let right = result.pool.project(result.term_id, 1);
    (
        own_projected(&result.pool, left),
        own_projected(&result.pool, right),
    )
}

fn count_variants(pool: &TermPool<OpId, LitValId>, id: TermId) -> u32 {
    let own = u32::from(matches!(pool.op(id), TermOp::Variants));
    own + pool
        .children(id)
        .iter()
        .map(|&c| count_variants(pool, c))
        .sum::<u32>()
}

fn term_depth(pool: &TermPool<OpId, LitValId>, id: TermId) -> u32 {
    1 + pool
        .children(id)
        .iter()
        .map(|&c| term_depth(pool, c))
        .max()
        .unwrap_or(0)
}

// ---------------------------------------------------------------------------
// Term rendering: e-graph nodes and AU pool terms as s-expressions.
// ---------------------------------------------------------------------------

/// Render the term rooted at e-node `id` as an s-expression by walking the
/// stored children (MSet children repeated per multiplicity). After a rebuild
/// the stored children are find-canonical representatives, so a post-merge
/// rendering can show a merged sibling in place of the originally added
/// child; callers that need the as-added syntax snapshot the renderings
/// before the merges (`snapshot_terms`).
fn sexpr<const T: bool, const P: bool>(eg: &Eg<T, P>, id: ENodeId) -> String {
    let mut parts: Vec<String> = Vec::new();
    eg.for_each_child(id, |c, m| {
        let rendered = sexpr(eg, c);
        for _ in 0..m.to_u64() {
            parts.push(rendered.clone());
        }
    });
    let name = eg.node_op_name(id);
    if parts.is_empty() {
        name.to_string()
    } else {
        format!("({name} {})", parts.join(" "))
    }
}

/// Snapshot the s-expression of every node while the stored children are
/// still the as-added ones (call before `merge_justified`/`rebuild`).
fn snapshot_terms<const T: bool, const P: bool>(eg: &Eg<T, P>) -> HashMap<usize, String> {
    eg.node_ids()
        .map(|id| (id.to_usize(), sexpr(eg, id)))
        .collect()
}

/// Render a node id through the pre-merge snapshot; ids minted after the
/// snapshot (rebuild recanonization) fall back to the live, canonicalized
/// rendering and say so.
fn render_node<const T: bool, const P: bool>(
    eg: &Eg<T, P>,
    id: ENodeId,
    terms: &HashMap<usize, String>,
) -> String {
    terms.get(&id.to_usize()).cloned().unwrap_or_else(|| {
        format!(
            "{} ; post-snapshot node, rendered from find-canonical children",
            sexpr(eg, id)
        )
    })
}

/// Render an AU pool term. `Variants` nodes are named V1, V2, ... in first-
/// visit order; the assignment is recorded in `vars` so witnesses and
/// substitutions use the same names.
fn render_pool_term<const T: bool, const P: bool>(
    eg: &Eg<T, P>,
    pool: &TermPool<OpId, LitValId>,
    id: TermId,
    vars: &mut Vec<(TermId, String)>,
) -> String {
    match pool.op(id) {
        TermOp::EGraph(op) => {
            let name = eg.ops().info(*op).name.clone();
            let children = pool.children(id);
            if children.is_empty() {
                name
            } else {
                let parts: Vec<String> = children
                    .iter()
                    .map(|&c| render_pool_term(eg, pool, c, vars))
                    .collect();
                format!("({name} {})", parts.join(" "))
            }
        }
        TermOp::Literal(op, _) => format!("<lit {}>", eg.ops().info(*op).name),
        TermOp::Variants => {
            if let Some((_, n)) = vars.iter().find(|(t, _)| *t == id) {
                n.clone()
            } else {
                let n = format!("V{}", vars.len() + 1);
                vars.push((id, n.clone()));
                n
            }
        }
    }
}

/// Rendered AU result: backbone with variables, per-variable witness pair
/// (s1/s2 bindings), and the two owned projections for materialization.
struct AuRendering {
    backbone: String,
    /// (variable name, s1 witness, s2 witness)
    bindings: Vec<(String, String, String)>,
    left: OwnedTerm,
    right: OwnedTerm,
}

fn render_au<const T: bool, const P: bool>(
    eg: &Eg<T, P>,
    mut result: AuResult<DefaultConfig>,
) -> AuRendering {
    let mut vars = Vec::new();
    let backbone = render_pool_term(eg, &result.pool, result.term_id, &mut vars);
    let mut bindings = Vec::new();
    for (vid, name) in &vars {
        // Projecting the Variants node itself yields exactly its witness.
        let l = result.pool.project(*vid, 0);
        let r = result.pool.project(*vid, 1);
        let mut none = Vec::new();
        let ls = render_pool_term(eg, &result.pool, l, &mut none);
        let rs = render_pool_term(eg, &result.pool, r, &mut none);
        assert!(none.is_empty(), "witness contains Variants");
        bindings.push((name.clone(), ls, rs));
    }
    let left = result.pool.project(result.term_id, 0);
    let right = result.pool.project(result.term_id, 1);
    AuRendering {
        backbone,
        bindings,
        left: own_projected(&result.pool, left),
        right: own_projected(&result.pool, right),
    }
}

fn print_input<const T: bool, const P: bool>(
    eg: &Eg<T, P>,
    t1: ENodeId,
    t2: ENodeId,
    equalities: &[String],
) {
    eprintln!("\n=== input ===");
    eprintln!("t1 = {}", sexpr(eg, t1));
    eprintln!("t2 = {}", sexpr(eg, t2));
    eprintln!("equalities = [{}]", equalities.join(", "));
}

fn print_au(au: &AuRendering) {
    eprintln!("=== AU result ===");
    eprintln!("backbone t = {}", au.backbone);
    let s1: Vec<String> = au
        .bindings
        .iter()
        .map(|(n, l, _)| format!("{n} -> {l}"))
        .collect();
    let s2: Vec<String> = au
        .bindings
        .iter()
        .map(|(n, _, r)| format!("{n} -> {r}"))
        .collect();
    eprintln!("s1 = {{ {} }}", s1.join(", "));
    eprintln!("s2 = {{ {} }}", s2.join(", "));
}

// ---------------------------------------------------------------------------
// Chain rendering. Extends the op-name-only rendering that was copied from
// egraph/src/egraph_proof_test.rs (print_proof) with full from/to terms via
// the pre-merge snapshot.
// ---------------------------------------------------------------------------

fn reason<const T: bool, const P: bool>(
    eg: &Eg<T, P>,
    just: &Justification<ENodeId>,
    terms: &HashMap<usize, String>,
) -> String {
    match just {
        Justification::Axiom { axiom_id } => {
            format!("axiom {:?} \"{}\"", axiom_id, eg.axioms().name(*axiom_id))
        }
        Justification::Congruence { node_a, node_b } => format!(
            "congruence({}, {})",
            render_node(eg, *node_a, terms),
            render_node(eg, *node_b, terms)
        ),
        // C2 (doc §5): the log names the rule id only — no substitution and
        // no matched instance — so this is all a checker gets.
        Justification::Rewrite { rule_id } => {
            format!(
                "rewrite rule {rule_id:?} ; C2: rule id only, no substitution/instance in the log"
            )
        }
        Justification::ACSuperposition { .. }
        | Justification::ACInterReduction { .. }
        | Justification::ACAxiomCP { .. }
        | Justification::Cancellative { .. }
        | Justification::InverseCancel { .. } => "ac-algebraic".to_string(),
        Justification::Filler => unreachable!("filler is never a real proof step"),
    }
}

fn print_chain<const T: bool, const P: bool>(
    label: &str,
    buf: &ProofBuf<ENodeId>,
    eg: &Eg<T, P>,
    terms: &HashMap<usize, String>,
) {
    eprintln!("=== {label} ===");
    if buf.steps.is_empty() {
        eprintln!("(empty chain: reflexivity)");
    }
    for (i, (from, to, just)) in buf.steps.iter().enumerate() {
        eprintln!(
            "[{i}] {} ≡ {}  by {}",
            render_node(eg, *from, terms),
            render_node(eg, *to, terms),
            reason(eg, just, terms)
        );
    }
}

fn has_congruence(buf: &ProofBuf<ENodeId>) -> bool {
    buf.steps
        .iter()
        .any(|(_, _, j)| matches!(j, Justification::Congruence { .. }))
}

fn has_axiom(buf: &ProofBuf<ENodeId>) -> bool {
    buf.steps
        .iter()
        .any(|(_, _, j)| matches!(j, Justification::Axiom { .. }))
}

/// Every `Axiom` step must reference an id in `registered`.
fn assert_axioms_registered(buf: &ProofBuf<ENodeId>, registered: &[AxiomId], what: &str) {
    for (_, _, j) in &buf.steps {
        if let Justification::Axiom { axiom_id } = j {
            assert!(
                registered.contains(axiom_id),
                "{what}: chain references unregistered axiom id {axiom_id:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Test 1: free (non-AC) operators, full §5 pipeline, PROOFS = true.
// ---------------------------------------------------------------------------

/// Backbone g(f(V1), V2) over free operators with two differing leaf
/// positions. Phase A runs the §5 pipeline literally (instances added after
/// the merges) and pins that the chains are empty because hash-consing
/// dedupes the entire instantiation onto the root nodes. Phase B replays the
/// instances into the pre-merge state (via mark/restore), re-applies the
/// justified merges, and prints the full certificate block.
#[test]
fn certificate_trace_free_operators() {
    // TRACK = true for mark/restore, PROOFS = true for justifications.
    let mut eg = Eg::<true, true>::new();
    let int = eg.intern_sort("Int");
    let f = eg.register_op1("f", int, int);
    let g = eg.register_op2("g", int, int, int);
    let h1 = eg.register_op1("h1", int, int);
    let h2 = eg.register_op1("h2", int, int);
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let c_op = eg.register_op0("c", int);
    let d_op = eg.register_op0("d", int);
    let p_op = eg.register_op0("p", int);
    let q_op = eg.register_op0("q", int);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let p = eg.add(p_op, &[]);
    let q = eg.add(q_op, &[]);

    // t1 = g(f(h1(a)), p), t2 = g(f(h2(b)), q): shared backbone g(f(.), .),
    // two differing leaf positions.
    let h1a = eg.add(h1, &[a]);
    let h2b = eg.add(h2, &[b]);
    let fh1a = eg.add(f, &[h1a]);
    let fh2b = eg.add(f, &[h2b]);
    let t1 = eg.add(g, &[fh1a, p]);
    let t2 = eg.add(g, &[fh2b, q]);

    // Justified merges: h1(a) = c and h2(b) = d, so the differing classes each
    // contain a cheaper constant that witness extraction will pick.
    let ax1 = eg.register_axiom("h1a=c", h1a, c);
    let ax2 = eg.register_axiom("h2b=d", h2b, d);
    let registered = [ax1, ax2];

    print_input(
        &eg,
        t1,
        t2,
        &[
            format!("{} = {} ({:?})", sexpr(&eg, h1a), sexpr(&eg, c), ax1),
            format!("{} = {} ({:?})", sexpr(&eg, h2b), sexpr(&eg, d), ax2),
        ],
    );

    let len_premerge = eg.len();
    // Mark BEFORE the merges: phase B restores to here.
    let token = eg.mark(ShrinkPolicy::Never);

    eg.merge_justified(h1a, c, Justification::Axiom { axiom_id: ax1 });
    eg.merge_justified(h2b, d, Justification::Axiom { axiom_id: ax2 });
    eg.rebuild();
    assert_ne!(eg.find_const(t1), eg.find_const(t2));

    // Exact AU on the merged graph; the snapshot borrow ends before phase A.
    let au = {
        let snap = AuSnapshot::new(&eg).unwrap();
        let result = anti_unify(
            &snap,
            t1,
            t2,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            count_variants(&result.pool, result.term_id),
            2,
            "expected exactly the two planted differing positions"
        );
        render_au(&eg, result)
    };
    print_au(&au);

    // --- Phase A: the §5 pipeline as written (instances added post-merge) ---
    let len_before_inst = eg.len();
    let inst_l = materialize(&mut eg, &au.left);
    let inst_r = materialize(&mut eg, &au.right);
    eg.rebuild();

    // §5 step 4 membership check holds ...
    assert_eq!(eg.find_const(inst_l), eg.find_const(t1));
    assert_eq!(eg.find_const(inst_r), eg.find_const(t2));

    // ... but trivially: add() hash-conses over find-canonical children, so
    // the instantiation dedupes node-by-node onto existing nodes and the root
    // instance IS the root node. No fresh spine is created, congruence
    // closure has nothing to merge, and the §5 chains are reflexivity. This
    // contradicts the doc's reading that "congruence closure merges the
    // instantiated spine up to the roots".
    assert_eq!(
        eg.len(),
        len_before_inst,
        "materializing the projections post-merge minted fresh nodes; \
         the empty-chain finding no longer holds"
    );
    assert_eq!(inst_l, t1, "left instance deduped onto the left root");
    assert_eq!(inst_r, t2, "right instance deduped onto the right root");

    let mut buf = ProofBuf::new();
    assert!(eg.explain_deep(inst_l, t1, &mut buf));
    assert!(
        buf.steps.is_empty(),
        "post-merge materialization produced a non-empty chain"
    );
    buf.clear();
    assert!(eg.explain_deep(inst_r, t2, &mut buf));
    assert!(buf.steps.is_empty());
    eprintln!(
        "; phase A: instances deduped onto roots ({inst_l:?} == t1, {inst_r:?} == t2); \
         both chains empty"
    );

    // --- Phase B: replay into the pre-merge state to obtain real chains ---
    eg.restore(token);
    assert_eq!(
        eg.len(),
        len_premerge,
        "restore did not roll the node count back to the mark"
    );
    // Pre-merge the leaf classes are distinct, so the instances mint a fresh
    // spine: f(c) and g(f(c), p) do not exist yet.
    let inst_l2 = materialize(&mut eg, &au.left);
    let inst_r2 = materialize(&mut eg, &au.right);
    assert_ne!(inst_l2, t1, "pre-merge left instance must be a fresh node");
    assert_ne!(inst_r2, t2, "pre-merge right instance must be a fresh node");
    assert!(eg.len() > len_premerge);

    // Snapshot the as-added term of every node (instances included) before
    // the merges, so chain steps can print pristine from/to terms.
    let terms = snapshot_terms(&eg);

    // Re-apply the same justified merges and close congruence.
    eg.merge_justified(h1a, c, Justification::Axiom { axiom_id: ax1 });
    eg.merge_justified(h2b, d, Justification::Axiom { axiom_id: ax2 });
    eg.rebuild();

    assert_eq!(eg.find_const(inst_l2), eg.find_const(t1));
    assert_eq!(eg.find_const(inst_r2), eg.find_const(t2));

    // chain1 = explain_deep(t*s1, t1): now non-trivial.
    buf.clear();
    assert!(
        eg.explain_deep(inst_l2, t1, &mut buf),
        "chain1 extraction failed"
    );
    print_chain("chain1: t*s1 ~ t1", &buf, &eg, &terms);
    assert!(!buf.steps.is_empty());
    assert!(
        has_congruence(&buf),
        "non-trivial backbone must produce at least one Congruence step"
    );
    assert_axioms_registered(&buf, &registered, "chain1");

    // chain2 symmetrically.
    buf.clear();
    assert!(
        eg.explain_deep(inst_r2, t2, &mut buf),
        "chain2 extraction failed"
    );
    print_chain("chain2: t*s2 ~ t2", &buf, &eg, &terms);
    assert!(!buf.steps.is_empty());
    assert!(has_congruence(&buf));
    assert_axioms_registered(&buf, &registered, "chain2");
}

// ---------------------------------------------------------------------------
// Test 2: a chain that carries a Rewrite step (C2), alongside congruence and
// axiom steps. Backbone g(f(V1), V2), depth 3, two variables.
// ---------------------------------------------------------------------------

/// Same two-phase pipeline as `certificate_trace_free_operators`, but the
/// left leaf equality h1(a) = c is derived by a registered rewrite rule
/// `(h1 x) -> (c)` (compile_rewrite + apply_rule, as in
/// egraph/src/apply.rs::rewrite_produces_rewrite_justification) instead of an
/// axiom. chain1 then contains all three step kinds: Congruence for the
/// spine, Rewrite for h1(a) = c, and Axiom for k1(u) = p. The Rewrite step
/// demonstrates the C2 gap: the log names the rule id and nothing else, so
/// the printed reason cannot show a substitution or the matched instance.
#[test]
fn certificate_trace_with_rewrite_step() {
    use semi_persistent_egraph::apply::{apply_rule, compile_rewrite};
    use semi_persistent_egraph::ast::RhsTerm;
    use semi_persistent_egraph::id::SortId;
    use semi_persistent_egraph::index::IndexStore;
    use semi_persistent_egraph::literal::NiraModel;
    use semi_persistent_egraph::parser;
    use semi_persistent_egraph::registry::RuleRegistry;
    use semi_persistent_egraph::resolve::GlobalCtx;
    use semi_persistent_egraph::schedule::IndexStats;
    use semi_persistent_egraph::surface_ast::{SurfaceCommand, SurfacePattern};

    fn parse_pattern(src: &str) -> SurfacePattern {
        let mut pats = parser::parse_patterns(src).unwrap();
        assert_eq!(pats.len(), 1);
        pats.remove(0)
    }
    fn parse_rhs(src: &str) -> RhsTerm {
        let wrapped = format!("(rewrite x {src})");
        match parser::parse_program_v2(&wrapped)
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
        {
            SurfaceCommand::Rewrite { rhs, .. } => rhs,
            _ => panic!("expected Rewrite"),
        }
    }

    let mut eg = Eg::<true, true>::from_model(&NiraModel);
    let model = NiraModel;
    let mut rules = RuleRegistry::<true>::new();
    let globals = GlobalCtx::<SortId, ENodeId>::new();

    let int = eg.intern_sort("Int");
    let f = eg.register_op1("f", int, int);
    let g = eg.register_op2("g", int, int, int);
    let h1 = eg.register_op1("h1", int, int);
    let h2 = eg.register_op1("h2", int, int);
    let k1 = eg.register_op1("k1", int, int);
    let k2 = eg.register_op1("k2", int, int);
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let c_op = eg.register_op0("c", int);
    let d_op = eg.register_op0("d", int);
    let u_op = eg.register_op0("u", int);
    let w_op = eg.register_op0("w", int);
    let p_op = eg.register_op0("p", int);
    let q_op = eg.register_op0("q", int);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let u = eg.add(u_op, &[]);
    let w = eg.add(w_op, &[]);
    let p = eg.add(p_op, &[]);
    let q = eg.add(q_op, &[]);

    // t1 = g(f(h1(a)), k1(u)), t2 = g(f(h2(b)), k2(w)): shared backbone
    // g(f(V1), V2) — depth 3, two variables.
    let h1a = eg.add(h1, &[a]);
    let h2b = eg.add(h2, &[b]);
    let fh1a = eg.add(f, &[h1a]);
    let fh2b = eg.add(f, &[h2b]);
    let k1u = eg.add(k1, &[u]);
    let k2w = eg.add(k2, &[w]);
    let t1 = eg.add(g, &[fh1a, k1u]);
    let t2 = eg.add(g, &[fh2b, k2w]);

    // Left leaf equality h1(a) = c comes from a rewrite rule; the other
    // three differing classes get axioms.
    let lhs = parse_pattern("(h1 x)");
    let rhs = parse_rhs("(c)");
    let rule = compile_rewrite(
        "h1-to-c",
        "(h1 x)",
        "(c)",
        &lhs,
        &rhs,
        &[],
        false,
        eg.ops(),
        eg.sorts(),
        &mut rules,
        &model,
        &globals,
    )
    .unwrap();
    let ax_h2 = eg.register_axiom("h2b=d", h2b, d);
    let ax_k1 = eg.register_axiom("k1u=p", k1u, p);
    let ax_k2 = eg.register_axiom("k2w=q", k2w, q);
    let registered = [ax_h2, ax_k1, ax_k2];

    print_input(
        &eg,
        t1,
        t2,
        &[
            format!("(h1 x) -> c (rule {:?} \"h1-to-c\")", rule.rule_id),
            format!("{} = {} ({:?})", sexpr(&eg, h2b), sexpr(&eg, d), ax_h2),
            format!("{} = {} ({:?})", sexpr(&eg, k1u), sexpr(&eg, p), ax_k1),
            format!("{} = {} ({:?})", sexpr(&eg, k2w), sexpr(&eg, q), ax_k2),
        ],
    );

    let len_premerge = eg.len();
    let token = eg.mark(ShrinkPolicy::Never);

    // Phase one: run the rule (merges h1(a) with c under Rewrite {rule_id})
    // and assert the axioms, then close congruence.
    let index = IndexStore::build(&eg);
    let stats = IndexStats::from_index(&index);
    let fired = apply_rule(&rule, &mut eg, &index, &stats, &model, &globals)
        .expect("the rule's RHS applies no primitive");
    assert!(fired > 0, "rule (h1 x) -> (c) must fire on h1(a)");
    eg.merge_justified(h2b, d, Justification::Axiom { axiom_id: ax_h2 });
    eg.merge_justified(k1u, p, Justification::Axiom { axiom_id: ax_k1 });
    eg.merge_justified(k2w, q, Justification::Axiom { axiom_id: ax_k2 });
    eg.rebuild();
    assert_eq!(eg.find_const(h1a), eg.find_const(c), "rule merge missing");
    assert_ne!(eg.find_const(t1), eg.find_const(t2));

    let au = {
        let snap = AuSnapshot::new(&eg).unwrap();
        let result = anti_unify(
            &snap,
            t1,
            t2,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(count_variants(&result.pool, result.term_id), 2);
        assert!(
            term_depth(&result.pool, result.term_id) >= 3,
            "backbone must have depth >= 3"
        );
        render_au(&eg, result)
    };
    print_au(&au);

    // Two-phase replay: restore, mint the fresh instance spines, re-derive
    // the equalities (rule application included), rebuild.
    eg.restore(token);
    assert_eq!(eg.len(), len_premerge);
    let inst_l = materialize(&mut eg, &au.left);
    let inst_r = materialize(&mut eg, &au.right);
    assert_ne!(inst_l, t1);
    assert_ne!(inst_r, t2);

    let terms = snapshot_terms(&eg);

    let index = IndexStore::build(&eg);
    let stats = IndexStats::from_index(&index);
    let fired = apply_rule(&rule, &mut eg, &index, &stats, &model, &globals)
        .expect("the rule's RHS applies no primitive");
    assert!(fired > 0, "rule must fire again after restore");
    eg.merge_justified(h2b, d, Justification::Axiom { axiom_id: ax_h2 });
    eg.merge_justified(k1u, p, Justification::Axiom { axiom_id: ax_k1 });
    eg.merge_justified(k2w, q, Justification::Axiom { axiom_id: ax_k2 });
    eg.rebuild();

    assert_eq!(eg.find_const(inst_l), eg.find_const(t1));
    assert_eq!(eg.find_const(inst_r), eg.find_const(t2));

    let mut buf = ProofBuf::new();
    assert!(eg.explain_deep(inst_l, t1, &mut buf));
    print_chain("chain1: t*s1 ~ t1", &buf, &eg, &terms);
    assert!(has_congruence(&buf));
    assert!(has_axiom(&buf));
    assert!(
        buf.steps.iter().any(|&(_, _, j)| j
            == Justification::Rewrite {
                rule_id: rule.rule_id
            }),
        "chain1 must contain the Rewrite step for h1(a) = c, got {:?}",
        buf.steps
    );
    assert_axioms_registered(&buf, &registered, "chain1");

    buf.clear();
    assert!(eg.explain_deep(inst_r, t2, &mut buf));
    print_chain("chain2: t*s2 ~ t2", &buf, &eg, &terms);
    assert!(has_congruence(&buf));
    assert!(has_axiom(&buf));
    assert_axioms_registered(&buf, &registered, "chain2");
}

// ---------------------------------------------------------------------------
// Test 3: a chain that crosses an AC (MSet) congruence (C3). The two sides
// differ inside the AC node, so explain_deep must expand an MSet congruence
// step via explain_grouped's find-keyed child pairing.
// ---------------------------------------------------------------------------

/// t1 = mplus(h1(a), x, y) and t2 = mplus(h2(b), x, y) differ in one element
/// of the multiset; h1(a) = c and h2(b) = d are axioms, so exact AU yields
/// the backbone mplus(V1, x, y) with witnesses c and d. The replayed chain
/// crosses the AC congruence between mplus(c, x, y) and mplus(h1(a), x, y):
/// explain_grouped pairs the children by canonical representative (c vs
/// h1(a)) and skips the identical x, y. What the step does NOT carry is the
/// C3 gap: no multiset bijection witness, and multiplicities are dropped by
/// the pairing, so a checker must recompute the child matching itself.
#[test]
fn certificate_trace_ac_projection() {
    let mut eg = Eg::<true, true>::new();
    let int = eg.intern_sort("Int");
    let mplus = eg.register_mset("mplus", int, int);
    let h1 = eg.register_op1("h1", int, int);
    let h2 = eg.register_op1("h2", int, int);
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let c_op = eg.register_op0("c", int);
    let d_op = eg.register_op0("d", int);
    let x_op = eg.register_op0("x", int);
    let y_op = eg.register_op0("y", int);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);

    // t1 = mplus(h1(a), x, y), t2 = mplus(h2(b), x, y): the sides differ in
    // one multiset element.
    let h1a = eg.add(h1, &[a]);
    let h2b = eg.add(h2, &[b]);
    let t1 = eg.add(mplus, &[h1a, x, y]);
    let t2 = eg.add(mplus, &[h2b, x, y]);
    assert_ne!(t1, t2);

    let ax1 = eg.register_axiom("h1a=c", h1a, c);
    let ax2 = eg.register_axiom("h2b=d", h2b, d);
    let registered = [ax1, ax2];

    print_input(
        &eg,
        t1,
        t2,
        &[
            format!("{} = {} ({:?})", sexpr(&eg, h1a), sexpr(&eg, c), ax1),
            format!("{} = {} ({:?})", sexpr(&eg, h2b), sexpr(&eg, d), ax2),
        ],
    );

    let len_premerge = eg.len();
    let token = eg.mark(ShrinkPolicy::Never);

    eg.merge_justified(h1a, c, Justification::Axiom { axiom_id: ax1 });
    eg.merge_justified(h2b, d, Justification::Axiom { axiom_id: ax2 });
    eg.rebuild();
    assert_ne!(eg.find_const(t1), eg.find_const(t2));

    let au = {
        let snap = AuSnapshot::new(&eg).unwrap();
        let result = anti_unify(
            &snap,
            t1,
            t2,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            count_variants(&result.pool, result.term_id),
            1,
            "the sides differ in exactly one multiset element"
        );
        assert!(
            matches!(result.pool.op(result.term_id), TermOp::EGraph(op) if *op == mplus),
            "backbone root must be the MSet operator"
        );
        render_au(&eg, result)
    };
    print_au(&au);

    // Two-phase replay: mplus(c, x, y) is fresh pre-merge because c and
    // h1(a) are still in distinct classes.
    eg.restore(token);
    assert_eq!(eg.len(), len_premerge);
    let inst_l = materialize(&mut eg, &au.left);
    let inst_r = materialize(&mut eg, &au.right);
    assert_ne!(inst_l, t1, "pre-merge left instance must be a fresh node");
    assert_ne!(inst_r, t2, "pre-merge right instance must be a fresh node");

    let terms = snapshot_terms(&eg);

    eg.merge_justified(h1a, c, Justification::Axiom { axiom_id: ax1 });
    eg.merge_justified(h2b, d, Justification::Axiom { axiom_id: ax2 });
    eg.rebuild();

    assert_eq!(eg.find_const(inst_l), eg.find_const(t1));
    assert_eq!(eg.find_const(inst_r), eg.find_const(t2));

    // The chain must cross the AC congruence between the two MSet nodes.
    let ac_congruence = |buf: &ProofBuf<ENodeId>| {
        buf.steps.iter().any(|(_, _, j)| {
            matches!(j, Justification::Congruence { node_a, node_b }
                if eg.node_op_name(*node_a) == "mplus" && eg.node_op_name(*node_b) == "mplus")
        })
    };

    let mut buf = ProofBuf::new();
    assert!(eg.explain_deep(inst_l, t1, &mut buf));
    print_chain("chain1: t*s1 ~ t1", &buf, &eg, &terms);
    assert!(
        ac_congruence(&buf),
        "chain1 must cross an MSet congruence, got {:?}",
        buf.steps
    );
    assert!(has_axiom(&buf));
    assert_axioms_registered(&buf, &registered, "chain1");

    buf.clear();
    assert!(eg.explain_deep(inst_r, t2, &mut buf));
    print_chain("chain2: t*s2 ~ t2", &buf, &eg, &terms);
    assert!(ac_congruence(&buf));
    assert!(has_axiom(&buf));
    assert_axioms_registered(&buf, &registered, "chain2");

    eprintln!(
        "; C3: the MSet congruence step names the two node ids only; explain_grouped \
         pairs children by find and drops multiplicities — no multiset bijection witness"
    );
}

// ---------------------------------------------------------------------------
// Test 4: AC (MSet) operator, order/nesting difference only.
// ---------------------------------------------------------------------------

/// The two sides differ only by argument order and nesting, so build-time AC
/// canonization (flatten, sort, coalesce) interns them to the SAME node id.
/// The instantiated projection likewise interns onto the root's member and
/// the explanation chain is empty: canonization is definitional and untraced
/// (doc §3), which is exactly what the checker-side-canonizer decision (doc
/// §4) assumes. Modeled on egraph/tests/ac_matrix.rs assert_eq_class.
#[test]
fn ac_equal_projection_explains_to_empty_chain() {
    let mut eg = Eg::<false, true>::new();
    let int = eg.intern_sort("Int");
    let plus = eg.register_mset("plus", int, int);
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let c_op = eg.register_op0("c", int);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);

    // t1 = plus(a, plus(b, c)); t2 = plus(plus(c, a), b): same multiset
    // {a, b, c} after flattening and sorting, so the same node id at build.
    let bc = eg.add(plus, &[b, c]);
    let t1 = eg.add(plus, &[a, bc]);
    let ca = eg.add(plus, &[c, a]);
    let t2 = eg.add(plus, &[ca, b]);
    assert_eq!(
        t1, t2,
        "build-time AC canonization must intern order/nesting variants to one node"
    );
    eg.rebuild();

    let (left_proj, right_proj) = {
        let snap = AuSnapshot::new(&eg).unwrap();
        let result = anti_unify(
            &snap,
            t1,
            t2,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            count_variants(&result.pool, result.term_id),
            0,
            "identical classes must anti-unify without variables"
        );
        projected_terms(result)
    };

    let inst_l = materialize(&mut eg, &left_proj);
    let inst_r = materialize(&mut eg, &right_proj);
    eg.rebuild();

    // The projection interns to the root's member node itself.
    assert_eq!(inst_l, t1, "projection must intern onto the root member");
    assert_eq!(inst_r, t2);

    // The equality is definitional at the hash-cons level: the chain is empty
    // (reflexivity), pinning the doc §3 claim that build-time canonization is
    // untraced by design.
    let mut buf = ProofBuf::new();
    assert!(eg.explain_deep(inst_l, t1, &mut buf));
    assert!(buf.steps.is_empty(), "canonization must not be traced");
    buf.clear();
    assert!(eg.explain_deep(inst_r, t2, &mut buf));
    assert!(buf.steps.is_empty());
}

// ---------------------------------------------------------------------------
// Test 5: post-rebuild degeneracy merge carries the wrong label.
// ---------------------------------------------------------------------------

/// Pins the documented post-rebuild degeneracy
/// merge — here an ACI singleton collapse, and(a,b) with a = b recanonizing
/// to {a} = a — is pushed through the collision queue and logged as
/// `Congruence { node, child }` (egraph.rs recanonize_parent /
/// degeneracy_merge). The label is wrong: no congruence happened, an
/// idempotence law did, and the two nodes in the step do not even share an
/// operator. C1 proposes dedicated variants (`UnitDrop`, `NilpotentClamp`,
/// `SingletonCollapse`); when C1 lands, this test must fail and be updated.
#[test]
fn degeneracy_merge_is_labelled_congruence() {
    // cc (AC completion) stays off — the default — so the only mechanism that
    // can derive and(a,b) = a is the recanonize degeneracy path, not a
    // completion inference with its own AC label.
    let mut eg = Eg::<false, true>::new();
    let int = eg.intern_sort("Int");
    let and = eg.register_set("and", int, int);
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let and_ab = eg.add(and, &[a, b]);
    assert_ne!(eg.find_const(and_ab), eg.find_const(a));

    let terms = snapshot_terms(&eg);

    let ax = eg.register_axiom("a=b", a, b);
    eg.merge_justified(a, b, Justification::Axiom { axiom_id: ax });
    eg.rebuild();

    // Recanonization coalesced {a, b} to the singleton {a}, and the
    // degeneracy merge equated and(a,b) with a.
    assert_eq!(eg.find_const(and_ab), eg.find_const(a));

    let mut buf = ProofBuf::new();
    assert!(eg.explain(and_ab, a, &mut buf));
    print_chain("degeneracy: and(a,b) ≡ a after a=b", &buf, &eg, &terms);

    // The degeneracy step is labelled Congruence and involves the collapsed
    // Set node itself.
    let degeneracy_step = buf
        .steps
        .iter()
        .find_map(|(_, _, j)| match j {
            Justification::Congruence { node_a, node_b }
                if *node_a == and_ab || *node_b == and_ab =>
            {
                Some((*node_a, *node_b))
            }
            _ => None,
        })
        .expect("degeneracy merge must appear as a Congruence step (doc §3, C1)");

    // No congruence happened: the equated nodes do not share an operator (a
    // Set node against a nullary leaf). This is the C1 mislabelling.
    let (na, nb) = degeneracy_step;
    assert_ne!(
        eg.node_op(na),
        eg.node_op(nb),
        "the 'Congruence' step relates nodes of different operators, \
         so it cannot be a congruence; it is the ACI idempotence law \
         (SingletonCollapse)"
    );

    // And explain_deep's congruence expansion has nothing to pair the MSet/Set
    // children against on the leaf side: the deep chain adds no steps over
    // the shallow one (doc §3: "explain_deep then tries to pair an MSet
    // node's children against a leaf's and emits nothing").
    let shallow_len = buf.steps.len();
    buf.clear();
    assert!(eg.explain_deep(and_ab, a, &mut buf));
    assert_eq!(
        buf.steps.len(),
        shallow_len,
        "congruence expansion of the degeneracy step should emit no sub-steps"
    );
}
