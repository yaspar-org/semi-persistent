// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Pattern compiler: flatten recursive patterns into atomic constraints.

use crate::ast::{CmpOp, MultSpec, Pattern, Span};

/// A flat atomic pattern — one e-node shape to match.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// `node_var = (op child_vars...)`
    Plain {
        node: String,
        op: String,
        children: Vec<String>,
        span: Span,
    },
    /// `node_var = lit_text`
    Lit {
        node: String,
        text: String,
        span: Span,
    },
    /// `node_var = (op [children...])` — A exact match
    AExact {
        node: String,
        op: String,
        children: Vec<String>,
        span: Span,
    },
    /// A with prefix rest
    APrefix {
        node: String,
        op: String,
        rest: String,
        fixed: Vec<String>,
        span: Span,
    },
    /// A with suffix rest
    ASuffix {
        node: String,
        op: String,
        fixed: Vec<String>,
        rest: String,
        span: Span,
    },
    /// A with both rests
    ABoth {
        node: String,
        op: String,
        pre: String,
        fixed: Vec<String>,
        suf: String,
        span: Span,
    },
    /// `node_var = (op {e:m ...})` — AC exact
    ACExact {
        node: String,
        op: String,
        elems: Vec<(String, FlatMult)>,
        span: Span,
    },
    /// AC subset with rest
    ACSub {
        node: String,
        op: String,
        elems: Vec<(String, FlatMult)>,
        rest: String,
        span: Span,
    },
    /// ACI exact
    ACIExact {
        node: String,
        op: String,
        elems: Vec<String>,
        span: Span,
    },
    /// ACI subset with rest
    ACISub {
        node: String,
        op: String,
        elems: Vec<String>,
        rest: String,
        span: Span,
    },
    /// Equality constraint: two vars must be in the same e-class.
    Eq(String, String),
}

/// Flattened multiplicity spec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatMult {
    Exact(u64),
    Var {
        name: String,
        constraint: Option<(CmpOp, u64)>,
    },
}

/// Result of flattening a set of patterns.
#[derive(Clone, Debug)]
pub struct FlatQuery {
    pub atoms: Vec<Atom>,
    /// Root variable name for each top-level pattern (index matches input pattern order).
    pub root_vars: Vec<String>,
}

/// Flatten one or more patterns into a `FlatQuery`.
pub fn flatten(patterns: &[Pattern]) -> FlatQuery {
    let mut ctx = FlatCtx {
        atoms: Vec::new(),
        next_fresh: 0,
    };
    let root_vars: Vec<String> = patterns.iter().map(|pat| ctx.flatten_root(pat)).collect();
    FlatQuery {
        atoms: ctx.atoms,
        root_vars,
    }
}

struct FlatCtx {
    atoms: Vec<Atom>,
    next_fresh: usize,
}

impl FlatCtx {
    fn fresh(&mut self, hint: &str) -> String {
        let id = self.next_fresh;
        self.next_fresh += 1;
        format!("?{hint}{id}")
    }

    /// Flatten a pattern that appears at the top level (not nested inside another).
    fn flatten_root(&mut self, pat: &Pattern) -> String {
        match pat {
            Pattern::Var(v, _) => v.clone(),
            Pattern::Lit(text, span) => {
                let v = self.fresh("lit");
                self.atoms.push(Atom::Lit {
                    node: v.clone(),
                    text: text.clone(),
                    span: *span,
                });
                v
            }
            _ => {
                let node = self.fresh("n");
                self.flatten_into(pat, &node);
                node
            }
        }
    }

    /// Flatten `pat`, binding its result to `target`.
    fn flatten_child(&mut self, pat: &Pattern) -> String {
        match pat {
            Pattern::Var(v, _) => v.clone(),
            Pattern::Lit(text, span) => {
                let v = self.fresh("lit");
                self.atoms.push(Atom::Lit {
                    node: v.clone(),
                    text: text.clone(),
                    span: *span,
                });
                v
            }
            _ => {
                let v = self.fresh("n");
                self.flatten_into(pat, &v);
                v
            }
        }
    }

    /// Emit atoms for `pat`, assigning the node to `node_var`.
    fn flatten_into(&mut self, pat: &Pattern, node_var: &str) {
        let span = pat.span();
        match pat {
            Pattern::Var(v, _) => {
                if v != node_var {
                    self.atoms.push(Atom::Eq(node_var.to_owned(), v.clone()));
                }
            }
            Pattern::Lit(text, _) => {
                self.atoms.push(Atom::Lit {
                    node: node_var.to_owned(),
                    text: text.clone(),
                    span,
                });
            }
            Pattern::Plain { op, children, .. } => {
                let cvars: Vec<String> = children.iter().map(|c| self.flatten_child(c)).collect();
                self.atoms.push(Atom::Plain {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    children: cvars,
                    span,
                });
            }
            Pattern::AExact { op, children, .. } => {
                let cvars: Vec<String> = children.iter().map(|c| self.flatten_child(c)).collect();
                self.atoms.push(Atom::AExact {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    children: cvars,
                    span,
                });
            }
            Pattern::APrefix {
                op, rest, fixed, ..
            } => {
                let fvars: Vec<String> = fixed.iter().map(|c| self.flatten_child(c)).collect();
                self.atoms.push(Atom::APrefix {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    rest: rest.clone(),
                    fixed: fvars,
                    span,
                });
            }
            Pattern::ASuffix {
                op, fixed, rest, ..
            } => {
                let fvars: Vec<String> = fixed.iter().map(|c| self.flatten_child(c)).collect();
                self.atoms.push(Atom::ASuffix {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    fixed: fvars,
                    rest: rest.clone(),
                    span,
                });
            }
            Pattern::ABoth {
                op,
                pre,
                fixed,
                suf,
                ..
            } => {
                let fvars: Vec<String> = fixed.iter().map(|c| self.flatten_child(c)).collect();
                self.atoms.push(Atom::ABoth {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    pre: pre.clone(),
                    fixed: fvars,
                    suf: suf.clone(),
                    span,
                });
            }
            Pattern::ACExact { op, elems, .. } => {
                let felems: Vec<(String, FlatMult)> = elems
                    .iter()
                    .map(|(p, m)| (self.flatten_child(p), flatten_mult(m)))
                    .collect();
                self.atoms.push(Atom::ACExact {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    elems: felems,
                    span,
                });
            }
            Pattern::ACSub {
                op, elems, rest, ..
            } => {
                let felems: Vec<(String, FlatMult)> = elems
                    .iter()
                    .map(|(p, m)| (self.flatten_child(p), flatten_mult(m)))
                    .collect();
                self.atoms.push(Atom::ACSub {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    elems: felems,
                    rest: rest.clone(),
                    span,
                });
            }
            Pattern::ACIExact { op, elems, .. } => {
                let evars: Vec<String> = elems.iter().map(|c| self.flatten_child(c)).collect();
                self.atoms.push(Atom::ACIExact {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    elems: evars,
                    span,
                });
            }
            Pattern::ACISub {
                op, elems, rest, ..
            } => {
                let evars: Vec<String> = elems.iter().map(|c| self.flatten_child(c)).collect();
                self.atoms.push(Atom::ACISub {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    elems: evars,
                    rest: rest.clone(),
                    span,
                });
            }
        }
    }
}

fn flatten_mult(m: &MultSpec) -> FlatMult {
    match m {
        MultSpec::Exact(n) => FlatMult::Exact(*n),
        MultSpec::Var { name, constraint } => FlatMult::Var {
            name: name.clone(),
            constraint: *constraint,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{OpId, SortId};
    use crate::registry::{OpRegistry, SortRegistry};
    use crate::sortcheck::flatten_surface;
    use crate::test_helpers::parse_pattern;

    fn setup() -> (OpRegistry<OpId, SortId, false>, SortRegistry<SortId, false>) {
        let mut sorts = SortRegistry::new();
        let e = sorts.intern("Expr");
        let mut ops = OpRegistry::new();
        ops.register("f", &[e, e], e);
        ops.register("g", &[e], e);
        ops.register("h", &[e], e);
        ops.register("f1", &[e], e);
        ops.register("f3", &[e, e, e], e);
        ops.register("a", &[], e);
        ops.register("b", &[], e);
        ops.register_a("concat", e, e, crate::registry::AssocDir::Right);
        ops.register_ac("add", e, e);
        ops.register_aci("union", e, e);
        let ibig = sorts.intern("IBig");
        ops.register("ILit", &[ibig], e);
        (ops, sorts)
    }

    fn flat(src: &str) -> FlatQuery {
        let (ops, _sorts) = setup();
        let pat = parse_pattern(src);
        flatten_surface(&[pat], &ops).unwrap()
    }

    #[test]
    fn plain_no_nesting() {
        let fq = flat("(f x y)");
        assert_eq!(fq.atoms.len(), 1);
        match &fq.atoms[0] {
            Atom::Plain { op, children, .. } => {
                assert_eq!(op, "f");
                assert_eq!(children.len(), 2);
                // children should be the user vars x, y
                assert_eq!(children[0], "x");
                assert_eq!(children[1], "y");
            }
            _ => panic!("expected Plain"),
        }
    }

    #[test]
    fn nested_introduces_intermediate() {
        // (f x (g y)) → two atoms: ?n1 = (g y), ?n0 = (f x ?n1)
        let fq = flat("(f x (g y))");
        assert_eq!(fq.atoms.len(), 2);
        // First atom emitted is the inner (g y)
        match &fq.atoms[0] {
            Atom::Plain { op, children, .. } => {
                assert_eq!(op, "g");
                assert_eq!(children[0], "y");
            }
            _ => panic!("expected inner Plain"),
        }
        // Second atom is the outer (f x ?intermediate)
        match &fq.atoms[1] {
            Atom::Plain { op, children, .. } => {
                assert_eq!(op, "f");
                assert_eq!(children[0], "x");
                // children[1] is the intermediate var
                assert!(children[1].starts_with("?"));
            }
            _ => panic!("expected outer Plain"),
        }
    }

    #[test]
    fn deeply_nested() {
        // (f1 (g (h x))) → 3 atoms
        let fq = flat("(f1 (g (h x)))");
        assert_eq!(fq.atoms.len(), 3);
        assert!(matches!(&fq.atoms[0], Atom::Plain { op, .. } if op == "h"));
        assert!(matches!(&fq.atoms[1], Atom::Plain { op, .. } if op == "g"));
        assert!(matches!(&fq.atoms[2], Atom::Plain { op, .. } if op == "f1"));
    }

    #[test]
    fn nonlinear_no_extra_atoms() {
        // (f x x) — same var twice, no nesting
        let fq = flat("(f x x)");
        assert_eq!(fq.atoms.len(), 1);
        match &fq.atoms[0] {
            Atom::Plain { children, .. } => assert_eq!(children[0], children[1]),
            _ => panic!("expected Plain"),
        }
    }

    #[test]
    fn literal_child() {
        let fq = flat("(f1 42)");
        assert_eq!(fq.atoms.len(), 2); // Lit atom + Plain atom
        assert!(matches!(&fq.atoms[0], Atom::Lit { text, .. } if text == "42"));
        assert!(matches!(&fq.atoms[1], Atom::Plain { op, .. } if op == "f1"));
    }

    #[test]
    fn nullary() {
        let fq = flat("(a)");
        assert_eq!(fq.atoms.len(), 1);
        match &fq.atoms[0] {
            Atom::Plain { op, children, .. } => {
                assert_eq!(op, "a");
                assert!(children.is_empty());
            }
            _ => panic!("expected Plain"),
        }
    }

    #[test]
    fn ac_subset_nested() {
        // (add (f1 x):2 ..rest)
        let fq = flat("(add (f1 x):2 ..rest)");
        // Should produce: inner Plain for (f1 x), then ACSub
        assert_eq!(fq.atoms.len(), 2);
        assert!(matches!(&fq.atoms[0], Atom::Plain { op, .. } if op == "f1"));
        match &fq.atoms[1] {
            Atom::ACSub {
                op, elems, rest, ..
            } => {
                assert_eq!(op, "add");
                assert_eq!(elems.len(), 1);
                assert_eq!(elems[0].1, FlatMult::Exact(2));
                assert_eq!(rest, "rest");
            }
            _ => panic!("expected ACSub"),
        }
    }

    #[test]
    fn a_prefix() {
        let fq = flat("(concat ..pre x y)");
        assert_eq!(fq.atoms.len(), 1);
        match &fq.atoms[0] {
            Atom::APrefix {
                op, rest, fixed, ..
            } => {
                assert_eq!(op, "concat");
                assert_eq!(rest, "pre");
                assert_eq!(fixed.len(), 2);
            }
            _ => panic!("expected APrefix"),
        }
    }

    #[test]
    fn multi_pattern_rule() {
        // Two patterns in a rule body: (f x y), (f y z)
        let (ops, _) = setup();
        let p1 = parse_pattern("(f x y)");
        let p2 = parse_pattern("(f y z)");
        let fq = flatten_surface(&[p1, p2], &ops).unwrap();
        assert_eq!(fq.atoms.len(), 2);
        // y should be shared between the two atoms
        match (&fq.atoms[0], &fq.atoms[1]) {
            (Atom::Plain { children: c1, .. }, Atom::Plain { children: c2, .. }) => {
                assert_eq!(c1[1], c2[0]); // y is child[1] of first f and child[0] of second f
            }
            _ => panic!("expected two Plain atoms"),
        }
    }

    #[test]
    fn fresh_vars_generated() {
        let fq = flat("(f (g x) (h y))");
        // 3 atoms: (g x), (h y), (f ?n0 ?n1)
        assert_eq!(fq.atoms.len(), 3);
        // Root should be a fresh name
        assert!(fq.root_vars[0].starts_with("?"));
    }
}
