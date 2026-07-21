// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Pretty-printer for anti-unifier terms: multi-line indented s-expressions
//! with a configurable column limit.
//!
//! The algorithm: render each subterm flat; if the flat form fits within the
//! remaining columns at the current indent level, emit it inline. Otherwise
//! break after the operator and emit each child on its own line, indented by
//! two spaces, applying the same rule recursively.

use crate::containers::DenseId;

use super::terms::{TermId, TermOp, TermPool};

/// Pretty-print a term from the pool using `op_name` for rendering operators.
/// `col_limit` is the target line width (0 means always break).
pub fn pretty_print<O, V, F>(
    pool: &TermPool<O, V>,
    root: TermId,
    op_name: F,
    col_limit: usize,
) -> String
where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    F: Fn(&TermOp<O, V>) -> String + Copy,
{
    let mut buf = String::new();
    pp_recursive(pool, root, op_name, col_limit, 0, &mut buf);
    buf
}

fn pp_recursive<O, V, F>(
    pool: &TermPool<O, V>,
    id: TermId,
    op_name: F,
    col_limit: usize,
    indent: usize,
    buf: &mut String,
) where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    F: Fn(&TermOp<O, V>) -> String + Copy,
{
    let flat = render_flat(pool, id, op_name);
    if indent + flat.len() <= col_limit {
        buf.push_str(&flat);
        return;
    }

    let children = pool.children(id);
    if children.is_empty() {
        buf.push_str(&flat);
        return;
    }

    let name = op_name(pool.op(id));
    buf.push('(');
    buf.push_str(&name);

    let child_indent = indent + 2;
    for &child in children {
        buf.push('\n');
        for _ in 0..child_indent {
            buf.push(' ');
        }
        pp_recursive(pool, child, op_name, col_limit, child_indent, buf);
    }
    buf.push(')');
}

fn render_flat<O, V, F>(pool: &TermPool<O, V>, id: TermId, op_name: F) -> String
where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    F: Fn(&TermOp<O, V>) -> String + Copy,
{
    let children = pool.children(id);
    let name = op_name(pool.op(id));
    if children.is_empty() {
        name
    } else {
        let child_strs: Vec<String> = children
            .iter()
            .map(|&c| render_flat(pool, c, op_name))
            .collect();
        format!("({} {})", name, child_strs.join(" "))
    }
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
