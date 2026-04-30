// Adversarial tests: try to break the DEDUP const-generic machinery.
// These exercise edge cases, interleaving, and boundary conditions
// that the happy-path tests don't cover.
#![allow(dead_code)]

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
// 1. Mark/restore on dedup: push duplicates, restore, push again.
//    The dedup map must be pruned so the second push allocates fresh.
// ---------------------------------------------------------------------------
#[test]
fn dedup_mark_restore_then_repush() {
    let mut s = LangStore::new_dedup();
    let mark = s.mark();

    let a = s.push_expr(ExprNode::Lit(42));
    let b = s.push_expr(ExprNode::Lit(42));
    assert_eq!(a, b); // dedup works before restore

    s.restore(&mark); // wipe everything after the mark
    assert_eq!(s.len_expr(), 0);

    // The dedup map entry for Lit(42) pointed at index 0, which was pruned.
    // If the map wasn't pruned, this push would return the stale id.
    let c = s.push_expr(ExprNode::Lit(42));
    assert_eq!(c, ExprId(0)); // fresh allocation at index 0
    assert_eq!(s.len_expr(), 1);
}

// ---------------------------------------------------------------------------
// 2. Nested mark/restore on dedup: two levels deep.
// ---------------------------------------------------------------------------
#[test]
fn dedup_nested_mark_restore() {
    let mut s = LangStore::new_dedup();
    let a = s.push_expr(ExprNode::Lit(1));

    let m1 = s.mark();
    let b = s.push_expr(ExprNode::Lit(2));
    let dup_b = s.push_expr(ExprNode::Lit(2));
    assert_eq!(b, dup_b);

    let m2 = s.mark();
    let _c = s.push_expr(ExprNode::Lit(3));
    assert_eq!(s.len_expr(), 3);

    // Restore to m2: Lit(3) gone, Lit(1) and Lit(2) survive.
    s.restore(&m2);
    assert_eq!(s.len_expr(), 2);
    let c2 = s.push_expr(ExprNode::Lit(3));
    assert_eq!(c2, ExprId(2)); // fresh at index 2

    // Restore to m1: only Lit(1) survives.
    s.restore(&m1);
    assert_eq!(s.len_expr(), 1);
    let b2 = s.push_expr(ExprNode::Lit(2));
    assert_eq!(b2, ExprId(1)); // fresh at index 1

    // Lit(1) should still be deduped.
    let a2 = s.push_expr(ExprNode::Lit(1));
    assert_eq!(a, a2);
    assert_eq!(s.len_expr(), 2); // Lit(1) deduped, Lit(2) new
}

// ---------------------------------------------------------------------------
// 3. Dedup with String fields: verify structural equality, not pointer.
// ---------------------------------------------------------------------------
#[test]
fn dedup_string_structural_equality() {
    let mut s = LangStore::new_dedup();
    let a = s.push_expr(ExprNode::Var("hello".to_string()));
    let b = s.push_expr(ExprNode::Var(String::from("hello")));
    assert_eq!(
        a, b,
        "dedup should use structural equality for String fields"
    );
    assert_eq!(s.len_expr(), 1);

    // Different string -> different id.
    let c = s.push_expr(ExprNode::Var("world".to_string()));
    assert_ne!(a, c);
    assert_eq!(s.len_expr(), 2);
}

// ---------------------------------------------------------------------------
// 4. Dedup cross-sort isolation: identical-looking nodes in different sorts
//    must not interfere.
// ---------------------------------------------------------------------------
#[test]
fn dedup_cross_sort_isolation() {
    let mut s = LangStore::new_dedup();
    // Push a Stmt and an Expr. They live in separate arenas and separate
    // dedup maps. Even if the internal representation happened to collide,
    // the ids must be independent.
    let e = s.push_expr(ExprNode::Lit(0));
    let pr1 = s.push_stmt(StmtNode::Print(e));
    let pr2 = s.push_stmt(StmtNode::Print(e));
    assert_eq!(pr1, pr2, "same Stmt node should dedup");
    assert_eq!(s.len_stmt(), 1);
    assert_eq!(s.len_expr(), 1);
}

// ---------------------------------------------------------------------------
// 5. Non-dedup store: push identical nodes, get different ids.
// ---------------------------------------------------------------------------
#[test]
fn non_dedup_no_sharing() {
    let mut s = LangStore::new();
    let a = s.push_expr(ExprNode::Lit(42));
    let b = s.push_expr(ExprNode::Lit(42));
    assert_ne!(a, b, "non-dedup store must not share identical nodes");
    assert_eq!(s.len_expr(), 2);
}

// ---------------------------------------------------------------------------
// 6. Rewrite on dedup: the rule itself pushes duplicates into the new store.
//    Verify the new store deduplicates them.
// ---------------------------------------------------------------------------
#[test]
fn dedup_rewrite_rule_pushes_duplicates() {
    let mut s = LangStore::new_dedup();
    let one = s.push_expr(ExprNode::Lit(1));
    let two = s.push_expr(ExprNode::Lit(2));
    let sum = s.push_expr(ExprNode::Add(one, two));
    let pr = s.push_stmt(StmtNode::Print(sum));

    // The rule replaces every Lit with Lit(0). Since both children become
    // identical, the dedup store should collapse them.
    let (s2, _r2) = s.rewrite(
        LangStoreRoot::Stmt(pr),
        |node, new: &mut LangStore<true>| new.push_stmt(node),
        |node, new: &mut LangStore<true>| match node {
            ExprNode::Lit(_) => new.push_expr(ExprNode::Lit(0)),
            other => new.push_expr(other),
        },
    );

    // s2 should have: Lit(0) [deduped], Add(Lit(0), Lit(0)), Print(Add(...))
    assert_eq!(
        s2.len_expr(),
        2,
        "Lit(0) should be deduped in the rewrite output"
    );
    assert_eq!(s2.len_stmt(), 1);

    // Verify the Add subtree is correct by folding from the Expr root.
    // Find the Add node: it's the child of Print. We know the structure,
    // so just fold the Expr at index 1 (the Add).
    let add_root = LangStoreRoot::Expr(ExprId(1));
    let result = s2.fold(
        add_root,
        |_: StmtNodeMapped<(), i64>| (),
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            _ => 0,
        },
    );
    assert_eq!(result.unwrap_expr(), 0); // 0 + 0
}

// ---------------------------------------------------------------------------
// 7. Transform on dedup: transform that makes previously-distinct nodes
//    identical. The output store should collapse them.
// ---------------------------------------------------------------------------
#[test]
fn dedup_transform_collapses_duplicates() {
    let mut s = LangStore::new_dedup();
    let one = s.push_expr(ExprNode::Lit(1));
    let two = s.push_expr(ExprNode::Lit(2));
    assert_eq!(s.len_expr(), 2); // distinct

    let sum = s.push_expr(ExprNode::Add(one, two));
    let pr = s.push_stmt(StmtNode::Print(sum));

    // Transform: replace all Lit(n) with Lit(0).
    let (s2, r2) = s.transform(
        LangStoreRoot::Stmt(pr),
        |stmt| stmt,
        |expr| match expr {
            ExprNode::Lit(_) => ExprNode::Lit(0),
            other => other,
        },
    );

    // Both Lit(1) and Lit(2) became Lit(0) -> dedup collapses to one node.
    assert_eq!(s2.len_expr(), 2, "Lit(0) deduped + Add = 2 expr nodes");

    // Fold from the Add node to verify correctness.
    // The Add is at ExprId(1) in the new store (Lit(0) at 0, Add at 1).
    let add_root = match r2 {
        LangStoreRoot::Stmt(sid) => {
            // Print(expr_child) — get the expr child
            match s2.get_stmt(sid) {
                StmtNode::Print(eid) => LangStoreRoot::Expr(*eid),
                _ => panic!("expected Print"),
            }
        }
        other => other,
    };
    let result = s2.fold(
        add_root,
        |_: StmtNodeMapped<(), i64>| (),
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            _ => 0,
        },
    );
    assert_eq!(result.unwrap_expr(), 0); // Lit(0) + Lit(0)
}

// ---------------------------------------------------------------------------
// 8. rewrite_down on dedup: top-down rewrite should also preserve DEDUP.
// ---------------------------------------------------------------------------
#[test]
fn dedup_rewrite_down_preserves_dedup() {
    let mut s = LangStore::new_dedup();
    let one = s.push_expr(ExprNode::Lit(1));
    let sum = s.push_expr(ExprNode::Add(one, one));
    let pr = s.push_stmt(StmtNode::Print(sum));

    let (mut s2, _r2) = s.rewrite_down(LangStoreRoot::Stmt(pr), |stmt| stmt, |expr| expr);

    // Identity rewrite_down: output should be dedup.
    let a = s2.push_expr(ExprNode::Lit(1));
    let b = s2.push_expr(ExprNode::Lit(1));
    assert_eq!(a, b, "rewrite_down output store should be dedup");
}

// ---------------------------------------------------------------------------
// 9. ZipperCow on dedup: edit a leaf in a DAG. Because the source is a DAG
//    (shared nodes), the COW rebuilds the reachable tree. The focused node's
//    id is shared, so the replacement propagates to all references.
// ---------------------------------------------------------------------------
#[test]
fn dedup_zipper_cow_spine_rebuild() {
    let mut s = LangStore::new_dedup();
    let shared = s.push_expr(ExprNode::Lit(99));
    let inner = s.push_expr(ExprNode::Add(shared, shared));
    // top = Add(inner, inner), but inner is shared (dedup).
    let top = s.push_expr(ExprNode::Add(inner, inner));
    assert_eq!(s.len_expr(), 3);

    let mut z = LangStoreZipperCow::new(&s, LangStoreRoot::Expr(top));
    z.down(0); // focus on inner Add
    z.down(0); // focus on Lit(99)
    let (s2, r2) = z.set_focus_expr(ExprNode::Lit(0));

    let result = s2.fold(
        r2,
        |_: StmtNodeMapped<(), i64>| (),
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            _ => 0,
        },
    );
    // The COW replaces Lit(99) (a shared node) with Lit(0). Since the
    // source is a DAG, every reference to that id sees the replacement.
    // Result: Add(Add(0,0), Add(0,0)) = 0.
    assert_eq!(result.unwrap_expr(), 0);
}

// ---------------------------------------------------------------------------
// 10. Fold on a deep DAG created by dedup: verify memoization handles
//     the sharing correctly (each shared node folded once, not re-folded).
// ---------------------------------------------------------------------------
#[test]
fn dedup_fold_deep_dag() {
    let mut s = LangStore::new_dedup();
    // Build: e0 = Lit(1), e1 = Add(e0, e0), e2 = Add(e1, e1), ...
    // Each level doubles the "logical" tree size but dedup keeps it linear.
    let mut prev = s.push_expr(ExprNode::Lit(1));
    for _ in 0..20 {
        prev = s.push_expr(ExprNode::Add(prev, prev));
    }
    // 21 unique nodes (1 Lit + 20 Adds), but the logical tree has 2^20 leaves.
    assert_eq!(s.len_expr(), 21);

    let result = s.fold(
        LangStoreRoot::Expr(prev),
        |_: StmtNodeMapped<(), i64>| (),
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            _ => 0,
        },
    );
    // Each level doubles: 1, 2, 4, 8, ..., 2^20 = 1048576
    assert_eq!(result.unwrap_expr(), 1 << 20);
}

// ---------------------------------------------------------------------------
// 11. Mark at depth 0 (empty store), push, restore to empty.
// ---------------------------------------------------------------------------
#[test]
fn dedup_mark_empty_restore_to_empty() {
    let mut s = LangStore::new_dedup();
    let mark = s.mark();
    let _ = s.push_expr(ExprNode::Lit(1));
    let _ = s.push_stmt(StmtNode::Print(ExprId(0)));
    s.restore(&mark);
    assert_eq!(s.len_expr(), 0);
    assert_eq!(s.len_stmt(), 0);

    // Dedup map should be empty too.
    let a = s.push_expr(ExprNode::Lit(1));
    assert_eq!(a, ExprId(0));
}

// ---------------------------------------------------------------------------
// 12. Sparse memo on a dedup DAG: verify Sparse produces the same result
//     as Dense on shared structure.
// ---------------------------------------------------------------------------
#[test]
fn dedup_sparse_memo_on_dag() {
    let mut s = LangStore::new_dedup();
    let one = s.push_expr(ExprNode::Lit(1));
    let sum = s.push_expr(ExprNode::Add(one, one));
    let big = s.push_expr(ExprNode::Add(sum, sum));

    let dense = s.fold(
        LangStoreRoot::Expr(big),
        |_: StmtNodeMapped<(), i64>| (),
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            _ => 0,
        },
    );

    let sparse = s.with_strategy::<Sparse>().fold(
        LangStoreRoot::Expr(big),
        |_: StmtNodeMapped<(), i64>| (),
        |expr: ExprNodeMapped<(), i64>| match expr {
            ExprNodeMapped::Lit(n) => n,
            ExprNodeMapped::Add(l, r) => l + r,
            _ => 0,
        },
    );

    let d = dense.unwrap_expr();
    let sp = sparse.unwrap_expr();
    assert_eq!(d, sp);
    assert_eq!(d, 4);
}
