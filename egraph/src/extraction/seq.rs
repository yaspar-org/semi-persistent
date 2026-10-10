// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Bracketings of sequences: the tree rungs of an associative operator.
//!
//! An `:assoc` node's operands keep their order, so a bracketing is a set of
//! intervals: each internal node of the tree covers a contiguous run of positions.
//! Every interval of two or more positions other than the whole sequence has a
//! literal `x[i..=j]`, true when the tree has that internal node. The rungs constrain
//! them as follows:
//!
//! | rung | constraint | trees of `k` operands |
//! | --- | --- | --- |
//! | levels | no two chosen intervals disjoint (a chain of nested blocks) | the chains |
//! | splits | no two chosen intervals crossing (a laminar family) | every tree, each once: the little Schröder numbers |
//! | binary | laminar, and exactly `k - 2` intervals | every full binary bracketing, each once: the Catalan numbers |
//!
//! A laminar family of intervals is exactly one tree: an interval's children are its
//! maximal chosen sub-intervals and the positions they leave out, in order. A tree
//! over `k` leaves whose internal nodes have at least two children has at most `k - 1`
//! internal nodes, and exactly `k - 1`, root included, when it is binary. There is no
//! orders rung: the order is fixed, so `orders` treats a sequence as `splits` does.
//!
//! A fold (`:assoc-left`, `:assoc-right`) has one bracketing. Its intervals are
//! constants, the prefixes or the suffixes, and it emits no clause.

use crate::extraction::Lit;
use crate::extraction::graph::{ClassId, Tree};
use crate::extraction::oint::{Build, Exact, OInt};
use crate::extraction::pb::Pb;
use crate::extraction::rung::Inner;
use crate::extraction::target::Cmp;
use std::collections::BTreeMap;

/// Which bracketings a sequence may take.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SeqFamily {
    Chains,
    Trees,
    Binary,
}

/// The interval literals of one sequence node.
pub(crate) struct SeqVars {
    /// The leaves, by position.
    kids: Vec<ClassId>,
    /// Every interval of two or more positions but the whole, with its literal.
    iv: Vec<(usize, usize, Lit)>,
    pub(crate) inner: Vec<Inner>,
}

fn crossing(a: (usize, usize), b: (usize, usize)) -> bool {
    (a.0 < b.0 && b.0 <= a.1 && a.1 < b.1) || (b.0 < a.0 && a.0 <= b.1 && b.1 < a.1)
}

fn disjoint(a: (usize, usize), b: (usize, usize)) -> bool {
    a.1 < b.0 || b.1 < a.0
}

fn intervals(k: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for i in 0..k {
        for j in (i + 1)..k {
            if (i, j) != (0, k - 1) {
                out.push((i, j));
            }
        }
    }
    out
}

impl SeqVars {
    /// A free bracketing of `kids` under `sel`, from `family`.
    pub(crate) fn free(b: &mut Build, sel: Lit, kids: Vec<ClassId>, family: SeqFamily) -> SeqVars {
        let k = kids.len();
        let iv: Vec<(usize, usize, Lit)> = intervals(k)
            .into_iter()
            .map(|(i, j)| (i, j, b.target().fresh()))
            .collect();
        for (a, &(i, j, x)) in iv.iter().enumerate() {
            for &(i2, j2, y) in &iv[a + 1..] {
                let forbidden = crossing((i, j), (i2, j2))
                    || (family == SeqFamily::Chains && disjoint((i, j), (i2, j2)));
                if forbidden {
                    b.target().clause(&[x.not(), y.not()]);
                }
            }
        }
        if family == SeqFamily::Binary {
            let terms: Vec<(i64, Lit)> = iv.iter().map(|&(_, _, x)| (1, x)).collect();
            b.pb(&terms, Cmp::Eq, k as i64 - 2);
        }
        let mut s = SeqVars {
            kids,
            iv,
            inner: Vec::new(),
        };
        s.inner = s.inner_nodes(b, sel);
        s
    }

    /// The one bracketing of a fold: the prefixes of a left fold, the suffixes of a
    /// right one.
    pub(crate) fn fold(b: &mut Build, sel: Lit, kids: Vec<ClassId>, left: bool) -> SeqVars {
        let k = kids.len();
        let iv = intervals(k)
            .into_iter()
            .map(|(i, j)| {
                let on = if left { i == 0 } else { j == k - 1 };
                (i, j, if on { Lit::True } else { Lit::False })
            })
            .collect();
        let mut s = SeqVars {
            kids,
            iv,
            inner: Vec::new(),
        };
        s.inner = s.inner_nodes(b, sel);
        s
    }

    /// Literals whose conjunction says that positions `p` and `s` share their
    /// innermost block containing `inside`: no chosen interval containing `inside`
    /// leaves `s` out. `None` when a constant interval already separates them.
    fn together(&self, inside: (usize, usize), s: usize, strict: bool) -> Option<Vec<Lit>> {
        let mut g = Vec::new();
        for &(i, j, x) in &self.iv {
            let contains = i <= inside.0 && inside.1 <= j && (!strict || (i, j) != inside);
            if contains && (s < i || j < s) {
                match x {
                    Lit::True => return None,
                    Lit::False => {}
                    x => g.push(x.not()),
                }
            }
        }
        Some(g)
    }

    fn inner_nodes(&self, b: &mut Build, sel: Lit) -> Vec<Inner> {
        let mut out = Vec::new();
        for &(i, j, x) in &self.iv {
            if x == Lit::False {
                continue;
            }
            let exists = if x == Lit::True { sel } else { b.and(sel, x) };
            let members = (i..=j).map(|p| (Vec::new(), self.kids[p])).collect();
            let mut siblings = Vec::new();
            for s in (0..self.kids.len()).filter(|&s| s < i || j < s) {
                if let Some(g) = self.together((i, j), s, true) {
                    siblings.push((g, self.kids[s]));
                }
            }
            out.push(Inner {
                exists,
                members,
                siblings,
            });
        }
        out
    }

    /// The siblings of class `c`: at each position `c` holds, every other position in
    /// the innermost block around it, under `sel` and the literals that keep it there.
    pub(crate) fn sibling_parts(&self, sel: Lit, c: ClassId) -> Vec<(Vec<Lit>, ClassId)> {
        let mut out = Vec::new();
        for p in (0..self.kids.len()).filter(|&p| self.kids[p] == c) {
            for s in (0..self.kids.len()).filter(|&s| s != p) {
                if let Some(mut g) = self.together((p, p), s, false) {
                    g.insert(0, sel);
                    g.retain(|l| *l != Lit::True);
                    out.push((g, self.kids[s]));
                }
            }
        }
        out
    }

    /// The tree a model denotes.
    pub(crate) fn decode(&self, model: &dyn Fn(u32) -> bool) -> Tree {
        let on: Vec<(usize, usize)> = self
            .iv
            .iter()
            .filter(|&&(_, _, x)| match x {
                Lit::True => true,
                Lit::False => false,
                Lit::Var { var, sign } => model(var) == sign,
            })
            .map(|&(i, j, _)| (i, j))
            .collect();
        fn build(i: usize, j: usize, on: &[(usize, usize)]) -> Tree {
            let mut kids = Vec::new();
            let mut p = i;
            while p <= j {
                let widest = on
                    .iter()
                    .filter(|&&(a, b)| a == p && b <= j && (a, b) != (i, j))
                    .map(|&(_, b)| b)
                    .max();
                match widest {
                    Some(q) => {
                        kids.push(build(p, q, on));
                        p = q + 1;
                    }
                    None => {
                        kids.push(Tree::Leaf(p));
                        p += 1;
                    }
                }
            }
            Tree::Node(kids)
        }
        build(0, self.kids.len() - 1, &on)
    }

    /// The interval literals under `tree`.
    pub(crate) fn canonical(&self, tree: &Tree, out: &mut BTreeMap<u32, bool>) {
        fn spans(t: &Tree, top: bool, out: &mut Vec<(usize, usize)>) -> (usize, usize) {
            match t {
                Tree::Leaf(p) => (*p, *p),
                Tree::Node(kids) => {
                    let s: Vec<(usize, usize)> =
                        kids.iter().map(|k| spans(k, false, out)).collect();
                    let span = (s[0].0, s[s.len() - 1].1);
                    if !top {
                        out.push(span);
                    }
                    span
                }
            }
        }
        let mut on = Vec::new();
        spans(tree, true, &mut on);
        for &(i, j, x) in &self.iv {
            if let Lit::Var { var, sign } = x {
                out.insert(var, on.contains(&(i, j)) == sign);
            }
        }
    }

    /// The model's interval literals, which fix its tree.
    pub(crate) fn primary(&self, model: &dyn Fn(u32) -> bool) -> Vec<Lit> {
        self.iv
            .iter()
            .filter_map(|&(_, _, x)| match x {
                Lit::Var { var, .. } => Some(if model(var) {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                }),
                _ => None,
            })
            .collect()
    }

    /// The depth of class `c` (at its first position): one plus the chosen intervals
    /// around it.
    pub(crate) fn depth(&self, b: &mut Build, c: ClassId) -> Option<OInt<Exact>> {
        let p = self.kids.iter().position(|&x| x == c)?;
        let t = self
            .iv
            .iter()
            .filter(|&&(i, j, _)| i <= p && p <= j)
            .fold(Pb::<Exact>::constant(1), |t, &(_, _, x)| {
                t.plus(&Pb::lit(x, 1))
            });
        b.sorted(&t).ok()
    }
}
