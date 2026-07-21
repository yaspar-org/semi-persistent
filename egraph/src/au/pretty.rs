// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Pretty-printer for anti-unifier terms: multi-line indented s-expressions
//! with a configurable column limit.
//!
//! The algorithm: render each subterm flat; if the flat form fits within the
//! remaining columns at the current indent level, emit it inline. Otherwise
//! break after the operator and emit each child on its own line, indented by
//! two spaces, applying the same rule recursively. Both passes are iterative
//! with explicit stacks, so rendering depth is heap-bounded rather than
//! call-stack-bounded.

use crate::containers::DenseId;

use super::terms::{TermOp, TermPool};
use crate::config::AuIds;

/// Pretty-print a term from the pool using `op_name` for rendering operators.
/// `col_limit` is the target line width (0 means always break).
pub fn pretty_print<O, V, A: AuIds, F>(
    pool: &TermPool<O, V, A>,
    root: A::Term,
    op_name: F,
    col_limit: usize,
) -> String
where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    F: Fn(&TermOp<O, V>) -> String + Copy,
{
    // Explicit frame stack replacing the recursive descent: a frame is an
    // open (broken) node whose children still need their own lines.
    struct Frame<T> {
        children: Vec<T>,
        cursor: usize,
        indent: usize,
    }
    let mut buf = String::new();
    let mut stack: Vec<Frame<A::Term>> = Vec::new();
    let mut pending = Some((root, 0usize));
    loop {
        if let Some((id, indent)) = pending.take() {
            let flat = render_flat(pool, id, op_name);
            let children = pool.children(id);
            if indent + flat.len() <= col_limit || children.is_empty() {
                buf.push_str(&flat);
            } else {
                buf.push('(');
                buf.push_str(&op_name(pool.op(id)));
                stack.push(Frame {
                    children: children.to_vec(),
                    cursor: 0,
                    indent: indent + 2,
                });
            }
        }
        let Some(top) = stack.last_mut() else {
            return buf;
        };
        if top.cursor < top.children.len() {
            let child = top.children[top.cursor];
            top.cursor += 1;
            buf.push('\n');
            for _ in 0..top.indent {
                buf.push(' ');
            }
            pending = Some((child, top.indent));
        } else {
            buf.push(')');
            stack.pop();
        }
    }
}

/// Render the flat one-line form of a term. Iterative preorder emission with
/// open/space/close markers on an explicit stack; produces exactly the string
/// of the recursive definition `({name} {children joined by spaces})`.
fn render_flat<O, V, A: AuIds, F>(pool: &TermPool<O, V, A>, id: A::Term, op_name: F) -> String
where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    F: Fn(&TermOp<O, V>) -> String + Copy,
{
    enum Item<T> {
        Node(T),
        Space,
        Close,
    }
    let mut out = String::new();
    let mut stack: Vec<Item<A::Term>> = vec![Item::Node(id)];
    while let Some(item) = stack.pop() {
        match item {
            Item::Node(t) => {
                let children = pool.children(t);
                let name = op_name(pool.op(t));
                if children.is_empty() {
                    out.push_str(&name);
                } else {
                    out.push('(');
                    out.push_str(&name);
                    stack.push(Item::Close);
                    for &c in children.iter().rev() {
                        stack.push(Item::Node(c));
                        stack.push(Item::Space);
                    }
                }
            }
            Item::Space => out.push(' '),
            Item::Close => out.push(')'),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::OpId;

    #[test]
    fn flat_when_short() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let a = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
        let b = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let f = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[a, b]);

        let out = pretty_print(
            &pool,
            f,
            |op| match op {
                TermOp::EGraph(o) => ["a", "b", "f"][o.to_usize()].to_string(),
                _ => "?".to_string(),
            },
            80,
        );
        assert_eq!(out, "(f a b)");
    }

    #[test]
    fn breaks_when_long() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let leaf = |pool: &mut TermPool<OpId, crate::id::ENodeId>, i: usize| {
            pool.intern(TermOp::EGraph(OpId::from_usize(i)), &[])
        };
        let a = leaf(&mut pool, 0);
        let b = leaf(&mut pool, 1);
        let c = leaf(&mut pool, 2);
        let inner = pool.intern(TermOp::EGraph(OpId::from_usize(3)), &[a, b, c]);
        let root = pool.intern(TermOp::EGraph(OpId::from_usize(4)), &[inner, inner, inner]);

        let names = [
            "alpha",
            "beta",
            "gamma",
            "long_inner_op",
            "very_long_outer_op",
        ];
        let out = pretty_print(
            &pool,
            root,
            |op| match op {
                TermOp::EGraph(o) => names[o.to_usize()].to_string(),
                _ => "?".to_string(),
            },
            40,
        );

        assert!(out.contains('\n'), "should break into multiple lines");
        assert!(out.starts_with("(very_long_outer_op"));
        for line in out.lines().skip(1) {
            assert!(line.starts_with("  "), "children should be indented");
        }
    }

    #[test]
    fn variants_rendered() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let a = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
        let b = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let v = pool.intern(TermOp::Variants, &[a, b]);

        let out = pretty_print(
            &pool,
            v,
            |op| match op {
                TermOp::EGraph(o) => ["a", "b"][o.to_usize()].to_string(),
                TermOp::Variants => "Variants".to_string(),
                _ => "?".to_string(),
            },
            80,
        );
        assert_eq!(out, "(Variants a b)");
    }
}
