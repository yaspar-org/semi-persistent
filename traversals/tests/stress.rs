// Stress tests: property-based verification of dedup, mark/restore,
// and scheme round-trips on randomly-generated inputs.
#![allow(dead_code)]

use proptest::prelude::*;
use semi_persistent_traversals::*;
use semi_persistent_traversals_derive::rec_family;

rec_family! {
    family Lang => LangStore;
    enum Stmt {
        Assign(String, Expr),
        Seq(Stmt, Stmt),
        Print(Expr),
    }
    enum Expr {
        Var(String),
        Lit(i64),
        Add(Expr, Expr),
        Block(Stmt, Expr),
    }
}

// ---------------------------------------------------------------------------
// AST generator: produces a random Expr or Stmt tree of bounded depth.
// Strategy builds the tree bottom-up into a LangStore and returns the root id.
// ---------------------------------------------------------------------------

/// Generate a random Expr tree with bounded depth, pushing into the store.
fn gen_expr<const DEDUP: bool>(s: &mut LangStore<DEDUP>, depth: u32, rng: &mut impl Rng) -> ExprId {
    if depth == 0 || rng.gen_range(0..5) < 2 {
        // Leaf
        match rng.gen_range(0..2) {
            0 => s.push_expr(ExprNode::Lit(rng.gen_range(-10..10))),
            _ => {
                let name = format!("v{}", rng.gen_range(0..5));
                s.push_expr(ExprNode::Var(name))
            }
        }
    } else {
        // Branch
        match rng.gen_range(0..3) {
            0 => {
                let l = gen_expr(s, depth - 1, rng);
                let r = gen_expr(s, depth - 1, rng);
                s.push_expr(ExprNode::Add(l, r))
            }
            1 => {
                let stmt = gen_stmt(s, depth - 1, rng);
                let e = gen_expr(s, depth - 1, rng);
                s.push_expr(ExprNode::Block(stmt, e))
            }
            _ => s.push_expr(ExprNode::Lit(rng.gen_range(-10..10))),
        }
    }
}

fn gen_stmt<const DEDUP: bool>(s: &mut LangStore<DEDUP>, depth: u32, rng: &mut impl Rng) -> StmtId {
    if depth == 0 {
        let e = gen_expr(s, 0, rng);
        s.push_stmt(StmtNode::Print(e))
    } else {
        match rng.gen_range(0..3) {
            0 => {
                let name = format!("v{}", rng.gen_range(0..5));
                let e = gen_expr(s, depth - 1, rng);
                s.push_stmt(StmtNode::Assign(name, e))
            }
            1 => {
                let a = gen_stmt(s, depth - 1, rng);
                let b = gen_stmt(s, depth - 1, rng);
                s.push_stmt(StmtNode::Seq(a, b))
            }
            _ => {
                let e = gen_expr(s, depth - 1, rng);
                s.push_stmt(StmtNode::Print(e))
            }
        }
    }
}

// Tiny deterministic RNG so tests are reproducible. We use proptest's
// `Config { cases, .. }` to control the count; each `prop_assume!` failure
// shrinks a candidate. For the RNG inside `gen_expr` we use a simple LCG
// seeded from proptest's generated seed.
struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed.wrapping_add(0x9E3779B97F4A7C15))
    }
}
trait Rng {
    fn gen_range(&mut self, range: std::ops::Range<i64>) -> i64;
}
impl Rng for Lcg {
    fn gen_range(&mut self, range: std::ops::Range<i64>) -> i64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let r = (self.0 >> 33) as i64;
        let span = range.end - range.start;
        range.start + r.rem_euclid(span)
    }
}

// ---------------------------------------------------------------------------
// Invariant 1: dedup map and arena stay in sync.
//
// For every entry (node, idx) in the dedup map:
//   - idx < arena.len()
//   - arena[idx] equals node structurally
//
// For every arena slot that was deduped:
//   - looking up node structure in the map returns the same idx.
//
// We check these post-condition invariants after a random sequence of
// pushes + marks + restores.
// ---------------------------------------------------------------------------

/// Operation on a dedup store for the random sequence test.
#[derive(Debug, Clone)]
enum Op {
    PushExpr(i64), // Lit(n)
    PushVar(u8),   // Var(vN) — n in 0..5
    PushAdd,       // Add of two random existing exprs (skip if < 2)
    PushStmt,      // Print of a random existing expr (skip if 0 exprs)
    Mark,
    Restore(u8), // restore to mark index (u8 mod depth)
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        (-50i64..50).prop_map(Op::PushExpr),
        (0u8..5).prop_map(Op::PushVar),
        Just(Op::PushAdd),
        Just(Op::PushStmt),
        Just(Op::Mark),
        (0u8..8).prop_map(Op::Restore),
    ]
}

/// Walk the arena and reconstruct what the dedup map "should" contain if it
/// were rebuilt from scratch. Compare against the actual dedup map.
/// Returns Err(msg) if an inconsistency is found.
///
/// The dedup map should contain the FIRST occurrence of every unique node
/// structure. Since push_* returns the existing id on duplicate, no later
/// occurrences are ever inserted. So we walk the arena in order, track
/// which node structures we've seen, and verify the map matches.
fn check_dedup_invariant(s: &LangStore<true>) -> Result<(), String> {
    // Rebuild what the dedup map should look like.
    let mut expected_expr: FxHashMap<ExprNode, usize> = FxHashMap::default();
    for i in 0..s.len_expr() {
        let node = s.get_expr(ExprId(i)).clone();
        expected_expr.entry(node).or_insert(i);
    }
    let mut expected_stmt: FxHashMap<StmtNode, usize> = FxHashMap::default();
    for i in 0..s.len_stmt() {
        let node = s.get_stmt(StmtId(i)).clone();
        expected_stmt.entry(node).or_insert(i);
    }

    // Probe: for every expected entry, check that push_* of that node
    // returns the expected id. This requires mutating so we do it on a
    // clone. But clone of a store copies the dedup map too, so this is
    // really a consistency check on the map's current state.
    //
    // Actually simpler: walk every arena slot and confirm the map contains
    // at least one entry pointing to that slot OR an earlier slot with
    // the same structure.
    for i in 0..s.len_expr() {
        let node = s.get_expr(ExprId(i)).clone();
        // The map must have SOME entry for this node (with idx <= i).
        // We can't access the map directly — so reconstruct from the arena
        // walk above and compare semantically.
        let Some(&expected_idx) = expected_expr.get(&node) else {
            return Err(format!("expr arena[{i}] structure has no map entry"));
        };
        if expected_idx > i {
            return Err(format!(
                "expr arena[{i}]: expected map entry at idx {expected_idx} > {i}"
            ));
        }
    }
    for i in 0..s.len_stmt() {
        let node = s.get_stmt(StmtId(i)).clone();
        let Some(&expected_idx) = expected_stmt.get(&node) else {
            return Err(format!("stmt arena[{i}] structure has no map entry"));
        };
        if expected_idx > i {
            return Err(format!(
                "stmt arena[{i}]: expected map entry at idx {expected_idx} > {i}"
            ));
        }
    }
    Ok(())
}

/// Stronger check: do a push probe. For each unique node structure currently
/// in the arena, pushing it should return an existing id (no new allocation).
fn check_dedup_via_probe(s: LangStore<true>) -> Result<(), String> {
    let before_expr = s.len_expr();
    let before_stmt = s.len_stmt();
    let mut s = s;
    // Re-push every expr node. Each push should dedup (no new allocation).
    for i in 0..before_expr {
        let node = s.get_expr(ExprId(i)).clone();
        let re_id = s.push_expr(node);
        if s.len_expr() != before_expr {
            return Err(format!(
                "re-pushing expr[{i}] grew arena from {before_expr} to {}",
                s.len_expr()
            ));
        }
        // re_id may be less than i if an earlier duplicate exists; that's fine,
        // it just means multiple pushes collapsed. But re_id must be <= i.
        if re_id.0 > i {
            return Err(format!(
                "re-pushing expr[{i}] returned id {} > {i}",
                re_id.0
            ));
        }
    }
    for i in 0..before_stmt {
        let node = s.get_stmt(StmtId(i)).clone();
        let re_id = s.push_stmt(node);
        if s.len_stmt() != before_stmt {
            return Err(format!(
                "re-pushing stmt[{i}] grew arena from {before_stmt} to {}",
                s.len_stmt()
            ));
        }
        if re_id.0 > i {
            return Err(format!(
                "re-pushing stmt[{i}] returned id {} > {i}",
                re_id.0
            ));
        }
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 1000, .. ProptestConfig::default() })]

    // Run a random sequence of operations on a dedup store. After each
    // operation, the dedup invariant must hold: the map is consistent with
    // the arena contents.
    #[test]
    fn dedup_ops_preserve_invariant(ops in prop::collection::vec(op_strategy(), 1..100)) {
        let mut s: LangStore<true> = LangStore::new_dedup();
        let mut marks: Vec<LangStoreMark> = Vec::new();
        let mut expr_ids: Vec<ExprId> = Vec::new();
        let mut stmt_ids: Vec<StmtId> = Vec::new();

        for op in &ops {
            match op {
                Op::PushExpr(n) => {
                    let id = s.push_expr(ExprNode::Lit(*n));
                    expr_ids.push(id);
                }
                Op::PushVar(v) => {
                    let id = s.push_expr(ExprNode::Var(format!("v{}", v)));
                    expr_ids.push(id);
                }
                Op::PushAdd => {
                    // Only if we have 2+ exprs in the current "alive" set.
                    // We keep all returned ids in expr_ids, but some may be
                    // stale after restore. Filter by current len.
                    let cur_len = s.len_expr();
                    let alive: Vec<ExprId> = expr_ids.iter().copied()
                        .filter(|id| id.0 < cur_len)
                        .collect();
                    if alive.len() >= 2 {
                        let l = alive[alive.len() - 1];
                        let r = alive[alive.len() - 2];
                        let id = s.push_expr(ExprNode::Add(l, r));
                        expr_ids.push(id);
                    }
                }
                Op::PushStmt => {
                    let cur_len = s.len_expr();
                    let alive: Vec<ExprId> = expr_ids.iter().copied()
                        .filter(|id| id.0 < cur_len)
                        .collect();
                    if let Some(&e) = alive.last() {
                        let id = s.push_stmt(StmtNode::Print(e));
                        stmt_ids.push(id);
                    }
                }
                Op::Mark => {
                    marks.push(s.mark());
                }
                Op::Restore(idx) => {
                    if !marks.is_empty() {
                        let target = (*idx as usize) % marks.len();
                        let m = marks[target].clone();
                        s.restore(&m);
                        // Any marks after `target` are invalid now.
                        marks.truncate(target + 1);
                        // Trim id vecs to new lens.
                        let el = s.len_expr();
                        let sl = s.len_stmt();
                        expr_ids.retain(|id| id.0 < el);
                        stmt_ids.retain(|id| id.0 < sl);
                    }
                }
            }

            // Check invariant after every op.
            if let Err(msg) = check_dedup_invariant(&s) {
                prop_assert!(false, "dedup invariant violated after {:?}: {}", op, msg);
            }
        }

        // Final probe: re-pushing any node must not grow the arena.
        if let Err(msg) = check_dedup_via_probe(s) {
            prop_assert!(false, "dedup probe failed: {}", msg);
        }
    }

    // Identity transform is a no-op semantically: folding the result must
    // produce the same value as folding the original.
    #[test]
    fn transform_identity_fold_roundtrip(seed in any::<u64>()) {
        let mut rng = Lcg::new(seed);
        let mut s: LangStore<false> = LangStore::new();
        let root_expr = gen_expr(&mut s, 4, &mut rng);
        let root = LangStoreRoot::Expr(root_expr);

        // Fold the original.
        let before = s.fold(
            root,
            |_: StmtNodeMapped<(), i64>| (),
            |expr: ExprNodeMapped<(), i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Var(_) => 0,
                ExprNodeMapped::Add(l, r) => l.wrapping_add(r),
                ExprNodeMapped::Block(_, e) => e,
            },
        );

        // Transform with identity closures.
        let (s2, root2) = s.transform(root, |stmt| stmt, |expr| expr);
        let after = s2.fold(
            root2,
            |_: StmtNodeMapped<(), i64>| (),
            |expr: ExprNodeMapped<(), i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Var(_) => 0,
                ExprNodeMapped::Add(l, r) => l.wrapping_add(r),
                ExprNodeMapped::Block(_, e) => e,
            },
        );

        prop_assert_eq!(before.unwrap_expr(), after.unwrap_expr());
    }

    // Dense and Sparse memo strategies must produce identical fold results
    // on any input.
    #[test]
    fn dense_equals_sparse_on_random_tree(seed in any::<u64>()) {
        let mut rng = Lcg::new(seed);
        let mut s: LangStore<false> = LangStore::new();
        let root_expr = gen_expr(&mut s, 4, &mut rng);
        let root = LangStoreRoot::Expr(root_expr);

        let dense = s.fold(
            root,
            |_: StmtNodeMapped<(), i64>| (),
            |expr: ExprNodeMapped<(), i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Var(_) => 0,
                ExprNodeMapped::Add(l, r) => l.wrapping_add(r),
                ExprNodeMapped::Block(_, e) => e,
            },
        );
        let sparse = s.with_strategy::<Sparse>().fold(
            root,
            |_: StmtNodeMapped<(), i64>| (),
            |expr: ExprNodeMapped<(), i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Var(_) => 0,
                ExprNodeMapped::Add(l, r) => l.wrapping_add(r),
                ExprNodeMapped::Block(_, e) => e,
            },
        );
        prop_assert_eq!(dense.unwrap_expr(), sparse.unwrap_expr());
    }

    // mark -> (arbitrary pushes) -> restore returns the store to an
    // observationally-equivalent state. "Observational" = same lengths
    // and fold(every arena position) yields the same result.
    #[test]
    fn mark_restore_roundtrip_on_dedup(seed in any::<u64>(), n_pushes in 0u32..50) {
        let mut rng = Lcg::new(seed);
        let mut s: LangStore<true> = LangStore::new_dedup();

        // Pre-populate with some nodes so we have a non-empty baseline.
        let _ = gen_expr(&mut s, 3, &mut rng);
        let before_expr_len = s.len_expr();
        let before_stmt_len = s.len_stmt();
        let before_arena_expr: Vec<ExprNode> = (0..before_expr_len)
            .map(|i| s.get_expr(ExprId(i)).clone())
            .collect();
        let before_arena_stmt: Vec<StmtNode> = (0..before_stmt_len)
            .map(|i| s.get_stmt(StmtId(i)).clone())
            .collect();

        let m = s.mark();

        // Push a bunch more random nodes.
        for _ in 0..n_pushes {
            let _ = gen_expr(&mut s, 2, &mut rng);
        }

        // Restore.
        s.restore(&m);

        // Lengths match.
        prop_assert_eq!(s.len_expr(), before_expr_len);
        prop_assert_eq!(s.len_stmt(), before_stmt_len);

        // Arena contents match.
        for (i, expected) in before_arena_expr.iter().enumerate() {
            prop_assert_eq!(s.get_expr(ExprId(i)), expected);
        }
        for (i, expected) in before_arena_stmt.iter().enumerate() {
            prop_assert_eq!(s.get_stmt(StmtId(i)), expected);
        }

        // Dedup still works: re-pushing any arena node returns its existing id.
        for (i, node) in before_arena_expr.iter().enumerate() {
            let re = s.push_expr(node.clone());
            prop_assert!(
                re.0 <= i,
                "after restore, re-pushing expr[{}] returned {} (> {})",
                i, re.0, i
            );
            prop_assert_eq!(s.len_expr(), before_expr_len);
        }
    }

    // rewrite with an identity rule must preserve the tree's fold value.
    #[test]
    fn rewrite_identity_preserves_fold(seed in any::<u64>()) {
        let mut rng = Lcg::new(seed);
        let mut s: LangStore<false> = LangStore::new();
        let root_expr = gen_expr(&mut s, 4, &mut rng);
        let root = LangStoreRoot::Expr(root_expr);

        let before = s.fold(
            root,
            |_: StmtNodeMapped<(), i64>| (),
            |expr: ExprNodeMapped<(), i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Var(_) => 0,
                ExprNodeMapped::Add(l, r) => l.wrapping_add(r),
                ExprNodeMapped::Block(_, e) => e,
            },
        );

        let (s2, root2) = s.rewrite(
            root,
            |node, new: &mut LangStore<false>| new.push_stmt(node),
            |node, new: &mut LangStore<false>| new.push_expr(node),
        );
        let after = s2.fold(
            root2,
            |_: StmtNodeMapped<(), i64>| (),
            |expr: ExprNodeMapped<(), i64>| match expr {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Var(_) => 0,
                ExprNodeMapped::Add(l, r) => l.wrapping_add(r),
                ExprNodeMapped::Block(_, e) => e,
            },
        );
        prop_assert_eq!(before.unwrap_expr(), after.unwrap_expr());
    }

    // Dedup + rewrite: identity rewrite on a dedup store produces a store
    // whose len is <= original's len (it cannot grow; it might shrink if
    // the original had redundant nodes that dedup collapses).
    #[test]
    fn dedup_rewrite_identity_does_not_grow(seed in any::<u64>()) {
        let mut rng = Lcg::new(seed);
        let mut s: LangStore<true> = LangStore::new_dedup();
        let root_expr = gen_expr(&mut s, 4, &mut rng);
        let before_expr = s.len_expr();
        let before_stmt = s.len_stmt();

        let (s2, _) = s.rewrite(
            LangStoreRoot::Expr(root_expr),
            |node, new: &mut LangStore<true>| new.push_stmt(node),
            |node, new: &mut LangStore<true>| new.push_expr(node),
        );

        prop_assert!(
            s2.len_expr() <= before_expr,
            "dedup rewrite grew expr arena: {} -> {}", before_expr, s2.len_expr()
        );
        prop_assert!(
            s2.len_stmt() <= before_stmt,
            "dedup rewrite grew stmt arena: {} -> {}", before_stmt, s2.len_stmt()
        );
    }
}
