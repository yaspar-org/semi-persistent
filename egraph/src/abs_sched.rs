// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Scheduling state for the abstract-value saturation engine.
//!
//! The queues, the per-class change budget, the sticky conflict, and the
//! value table the drain reads. The saturation drivers call
//! [`AbsSched::begin_epoch`] and [`EGraph::take_abs_conflict`].
//!
//! Class values belong in the class-layer pool (#146). Until that pool
//! exists they sit in [`AbsSched::values`], keyed by class-key index, and an
//! undo log in this file rolls them back on `restore` and `pop`, together with
//! the literal table [`AbsSched::constants`]. Transfers belong to the domain
//! registry (#148): nothing is analysed until an [`AbsDomain`] is installed,
//! so a program without one pushes nothing on the queues.

use crate::canon::{MSetCanon, VarCanon};
use crate::containers::DenseId;
use std::collections::{HashMap, VecDeque};

/// Substring the conflict programs match. The interpreter reports this text unchanged.
pub(crate) const ABS_CONFLICT: &str = "abstract conflict";

/// Default per-class change budget for one epoch. A class past this keeps its
/// current value, which stays sound and only loses precision. A `set-option`
/// may replace the constant.
pub(crate) const ABS_CHANGE_BUDGET: u32 = 64;

/// Fuel passed to [`AbsDomain::reduce`] for one write. It costs precision only.
const ABS_REDUCE_FUEL: u8 = 4;

/// Transfers and tests the engine calls. #148 supplies the real registry;
/// tests supply a stand-in. Values are opaque `u64`s, compared with `==`.
pub(crate) trait AbsDomain: Send {
    fn analysed_sort(&self, sort: usize) -> bool;
    fn top(&self, sort: usize) -> u64;
    /// `None` is an empty meet: a conflict, not a value.
    fn meet(&self, a: u64, b: u64) -> Option<u64>;
    fn reduce(&self, value: u64, fuel: u8) -> Option<u64> {
        let _ = (value, fuel);
        Some(value)
    }
    fn forward(&self, op: usize, args: &[u64]) -> u64;
    /// One refined value per child. `None` means the children are unchanged.
    fn backward(&self, op: usize, result: u64, args: &[u64]) -> Option<Vec<u64>>;
    fn as_constant(&self, value: u64) -> Option<i64> {
        let _ = value;
        None
    }
    fn encode_lit(&self, sort: usize, lit: usize) -> Option<u64> {
        let _ = (sort, lit);
        None
    }
    /// Child index to merge with an `ite` node whose condition value is decided.
    fn decided_branch(&self, op: usize, cond: u64) -> Option<usize> {
        let _ = (op, cond);
        None
    }
}

#[derive(Default)]
pub(crate) struct AbsSched {
    domain: Option<Box<dyn AbsDomain>>,
    budget: u32,
    /// Accepted strict changes of each class key in the current epoch.
    changes: HashMap<usize, u32>,
    /// Class-key index → value. A missing key is that sort's top.
    values: HashMap<usize, u64>,
    /// Node ids. Drained after congruence, when the survivor's use list is whole.
    merges: VecDeque<usize>,
    forward: VecDeque<usize>,
    backward: VecDeque<usize>,
    /// `(class node, partner node)` applied as ordinary merges after the drain.
    derived: Vec<(usize, usize)>,
    /// `(sort, constant payload)` → literal node id, for singleton derived merges.
    constants: HashMap<(usize, i64), usize>,
    conflict: Option<String>,
    /// Mark-time state, one entry per open scope: the conflict and the undo-log
    /// length. `restore` and `pop` return to the top entry.
    saved: Vec<(Option<String>, usize)>,
    /// Previous entries of `values` and `constants`, written only while a scope
    /// is open. Stands in for the class-layer pool's own rollback (#146).
    undo: Vec<AbsUndo>,
}

/// One overwritten table entry. `None` means the key was absent.
enum AbsUndo {
    Value(usize, Option<u64>),
    Constant((usize, i64), Option<usize>),
}

impl AbsSched {
    pub(crate) fn new() -> Self {
        Self {
            budget: ABS_CHANGE_BUDGET,
            ..Self::default()
        }
    }

    pub(crate) fn set_domain(&mut self, domain: Box<dyn AbsDomain>) {
        self.domain = Some(domain);
    }

    pub(crate) fn set_budget(&mut self, budget: u32) {
        self.budget = budget;
    }

    pub(crate) fn begin_epoch(&mut self) {
        self.changes.clear();
    }

    pub(crate) fn has_domain(&self) -> bool {
        self.domain.is_some()
    }

    pub(crate) fn pending(&self) -> usize {
        self.merges.len() + self.forward.len() + self.backward.len() + self.derived.len()
    }

    pub(crate) fn conflict(&self) -> Option<&str> {
        self.conflict.as_deref()
    }

    pub(crate) fn take_conflict(&mut self) -> Option<String> {
        self.conflict.take()
    }

    /// Queues, the derived-merge batch, and the budget counters. Values, constants
    /// and the conflict flag are not cleared here: `undo_to` rolls the tables back,
    /// and the conflict is restored from the mark token.
    pub(crate) fn clear_transient(&mut self) {
        self.merges.clear();
        self.forward.clear();
        self.backward.clear();
        self.derived.clear();
        self.changes.clear();
    }

    pub(crate) fn on_mark(&mut self) -> bool {
        let flagged = self.conflict.is_some();
        self.saved.push((self.conflict.clone(), self.undo.len()));
        flagged
    }

    pub(crate) fn on_restore(&mut self, flagged: bool) {
        let (saved, len) = self.saved.last().cloned().unwrap_or((None, 0));
        self.conflict = if flagged {
            saved.or_else(|| Some(ABS_CONFLICT.to_string()))
        } else {
            None
        };
        self.undo_to(len);
        self.clear_transient();
    }

    pub(crate) fn on_pop(&mut self) {
        let (saved, len) = self.saved.pop().unwrap_or((None, 0));
        self.conflict = saved;
        self.undo_to(len);
        self.clear_transient();
    }

    pub(crate) fn on_restore_and_pop(&mut self, flagged: bool) {
        self.on_restore(flagged);
        self.saved.pop();
    }

    /// Undo table writes back to log length `len`, newest first.
    fn undo_to(&mut self, len: usize) {
        while self.undo.len() > len {
            match self.undo.pop().unwrap() {
                AbsUndo::Value(key, old) => match old {
                    Some(v) => {
                        self.values.insert(key, v);
                    }
                    None => {
                        self.values.remove(&key);
                    }
                },
                AbsUndo::Constant(key, old) => match old {
                    Some(node) => {
                        self.constants.insert(key, node);
                    }
                    None => {
                        self.constants.remove(&key);
                    }
                },
            }
        }
    }

    /// Write a class value (`None` is top), logging the old entry inside a scope.
    fn set_value(&mut self, key: usize, value: Option<u64>) {
        let old = match value {
            Some(v) => self.values.insert(key, v),
            None => self.values.remove(&key),
        };
        if !self.saved.is_empty() && old != value {
            self.undo.push(AbsUndo::Value(key, old));
        }
    }

    /// Bind a literal node to `(sort, constant)`, logging the old entry inside a scope.
    fn set_constant(&mut self, key: (usize, i64), node: usize) {
        let old = self.constants.insert(key, node);
        if !self.saved.is_empty() && old != Some(node) {
            self.undo.push(AbsUndo::Constant(key, old));
        }
    }

    fn note_conflict(&mut self) {
        if self.conflict.is_none() {
            self.conflict = Some(ABS_CONFLICT.to_string());
            self.merges.clear();
            self.forward.clear();
            self.backward.clear();
            self.derived.clear();
        }
    }
}

impl<Cfg, L, const TRACK: bool, const PROOFS: bool> super::EGraph<Cfg, L, TRACK, PROOFS>
where
    Cfg: crate::config::EGraphConfig,
    L: crate::literal::LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    pub(crate) fn set_abs_domain(&mut self, domain: Box<dyn AbsDomain>) {
        self.abs.set_domain(domain);
    }

    pub(crate) fn set_abs_budget(&mut self, budget: u32) {
        self.abs.set_budget(budget);
    }

    /// One budget epoch. Called at the start of each saturation iteration and
    /// of each top-level command outside a run.
    pub(crate) fn abs_begin_epoch(&mut self) {
        self.abs.begin_epoch();
    }

    pub(crate) fn abs_pending(&self) -> usize {
        self.abs.pending()
    }

    pub(crate) fn abs_has_conflict(&self) -> bool {
        self.abs.conflict().is_some()
    }

    pub(crate) fn abs_value(&self, node: Cfg::G) -> Option<u64> {
        let key = self.abs_class_key(node)?;
        self.abs.values.get(&key).copied()
    }

    /// Meet `value` into `node`'s class. Tests and, later, part B's `refine`.
    pub(crate) fn abs_seed(&mut self, node: Cfg::G, value: u64) {
        self.abs_meet_node(node, value);
    }

    pub(crate) fn abs_bind_constant(&mut self, k: i64, node: Cfg::G) {
        let sort = self.abs_sort_of(node);
        self.abs.set_constant((sort, k), node.to_usize());
    }

    fn abs_class_key(&self, node: Cfg::G) -> Option<usize> {
        use crate::containers::DenseId;
        let root = self.classes.find_const(node);
        self.classes.repr_id(root).map(|k| k.to_usize())
    }

    fn abs_sort_of(&self, node: Cfg::G) -> usize {
        use crate::containers::DenseId;
        self.node_sort(node).to_usize()
    }

    fn abs_analysed(&self, node: Cfg::G) -> bool {
        if self.abs.domain.is_none() {
            return false;
        }
        let sort = self.abs_sort_of(node);
        self.abs.domain.as_ref().unwrap().analysed_sort(sort)
    }

    /// Make: the fresh class starts at top (a missing table entry) and the node
    /// waits on the forward queue until the drain, which runs after congruence
    /// has spliced use lists.
    pub(crate) fn abs_on_make(&mut self, id: Cfg::G) {
        if self.abs.conflict.is_some() {
            return;
        }
        if !self.abs_analysed(id) {
            return;
        }
        self.abs.forward.push_back(id.to_usize());
    }

    /// A literal's class starts at the singleton of that literal, not at top.
    pub(crate) fn abs_on_lit(&mut self, id: Cfg::G, lit: Cfg::V) {
        if !self.abs_analysed(id) {
            return;
        }
        let sort = self.abs_sort_of(id);
        let Some(value) = self
            .abs
            .domain
            .as_ref()
            .and_then(|domain| domain.encode_lit(sort, lit.to_usize()))
        else {
            return;
        };
        let constant = self.abs.domain.as_ref().unwrap().as_constant(value);
        if let Some(k) = constant {
            self.abs.set_constant((sort, k), id.to_usize());
        }
        self.abs_meet_node(id, value);
    }

    /// Meet the absorbed class's value into the survivor. Both were read before
    /// the union; the survivor's table entry is still its own pre-merge value,
    /// so meeting the absorbed one is the whole meet. #146's `absorbed_abs`
    /// replaces the pre-merge read, not this write.
    ///
    /// The merged class is queued even when its value does not change: the
    /// absorbed side's parents and members now read the survivor's value, which
    /// may be narrower than the one they last saw. `absorbed_value` is `None`
    /// both without a domain and for an absorbed class at top.
    pub(crate) fn abs_on_merge(&mut self, survivor: Cfg::G, absorbed_value: Option<u64>) {
        if !self.abs.has_domain() {
            return;
        }
        let queued = match absorbed_value {
            Some(value) => self.abs_meet_node(survivor, value),
            None => false,
        };
        if !queued && self.abs.conflict.is_none() && self.abs_analysed(survivor) {
            self.abs.merges.push_back(survivor.to_usize());
        }
    }

    pub(crate) fn abs_value_of_root(&self, node: Cfg::G) -> Option<u64> {
        if !self.abs.has_domain() {
            return None;
        }
        let key = self.abs_class_key(node)?;
        self.abs.values.get(&key).copied()
    }

    /// Returns whether the class was queued, that is, whether its value changed.
    fn abs_meet_node(&mut self, node: Cfg::G, incoming: u64) -> bool {
        if self.abs.conflict.is_some() {
            return false;
        }
        if !self.abs_analysed(node) {
            return false;
        }
        let Some(key) = self.abs_class_key(node) else {
            return false;
        };
        let sort = self.abs_sort_of(node);
        let top = self.abs.domain.as_ref().unwrap().top(sort);
        let old = self.abs.values.get(&key).copied().unwrap_or(top);
        let met = self.abs.domain.as_ref().unwrap().meet(old, incoming);
        let Some(met) = met else {
            self.abs.note_conflict();
            return false;
        };
        let reduced = self
            .abs
            .domain
            .as_ref()
            .unwrap()
            .reduce(met, ABS_REDUCE_FUEL);
        let Some(reduced) = reduced else {
            self.abs.note_conflict();
            return false;
        };
        if reduced == old {
            return false;
        }
        let over_budget = {
            let seen = self.abs.changes.entry(key).or_insert(0);
            if *seen >= self.abs.budget {
                true
            } else {
                *seen += 1;
                false
            }
        };
        if over_budget {
            return false;
        }
        self.abs.set_value(key, (reduced != top).then_some(reduced));
        self.abs.merges.push_back(node.to_usize());
        self.abs_touch(node);
        self.abs_note_singleton(node, reduced);
        true
    }

    /// Members and parents of a changed class, under the same gate as merge
    /// tracking: only semi-naive saturation reads `touched`.
    fn abs_touch(&mut self, node: Cfg::G) {
        if !self.track_merge_members {
            return;
        }
        let root = self.classes.find_const(node);
        let members: Vec<Cfg::G> = self.classes.iter_class(root).collect();
        let parents: Vec<Cfg::G> = match self.classes.repr_id(root) {
            Some(key) => {
                let list = self.classes.use_list_id(key);
                self.classes.uses().iter(list).collect()
            }
            None => Vec::new(),
        };
        self.touched.extend(members);
        self.touched.extend(parents);
    }

    fn abs_note_singleton(&mut self, node: Cfg::G, value: u64) {
        let Some(k) = self.abs.domain.as_ref().unwrap().as_constant(value) else {
            return;
        };
        let sort = self.abs_sort_of(node);
        let Some(&partner) = self.abs.constants.get(&(sort, k)) else {
            return;
        };
        let partner_node = Cfg::G::from_usize(partner);
        if self.classes.find_const(partner_node) == self.classes.find_const(node) {
            return;
        }
        self.abs.derived.push((node.to_usize(), partner));
    }

    /// Drain the three queues to a fixpoint, then apply derived merges. Returns
    /// whether a derived merge unioned two classes, so `rebuild` can run
    /// congruence again. Stops at the first conflict and leaves the graph
    /// otherwise as it is.
    pub(crate) fn abs_drain(&mut self) -> bool {
        if !self.abs.has_domain() {
            return false;
        }
        let mut merged = false;
        loop {
            if self.abs.conflict.is_some() {
                break;
            }
            self.abs_drain_queues();
            if self.abs.conflict.is_some() {
                break;
            }
            if self.abs_apply_derived() {
                merged = true;
            }
            if self.abs.pending() == 0 {
                break;
            }
        }
        merged
    }

    fn abs_drain_queues(&mut self) {
        use crate::containers::DenseId;
        while self.abs.conflict.is_none()
            && !(self.abs.merges.is_empty()
                && self.abs.forward.is_empty()
                && self.abs.backward.is_empty())
        {
            while let Some(raw) = self.abs.merges.pop_front() {
                if self.abs.conflict.is_some() {
                    return;
                }
                let node = Cfg::G::from_usize(raw);
                let root = self.classes.find_const(node);
                let members: Vec<Cfg::G> = self.classes.iter_class(root).collect();
                let parents: Vec<Cfg::G> = match self.classes.repr_id(root) {
                    Some(key) => {
                        let list = self.classes.use_list_id(key);
                        self.classes.uses().iter(list).collect()
                    }
                    None => Vec::new(),
                };
                for parent in parents {
                    self.abs.forward.push_back(parent.to_usize());
                }
                for member in members {
                    self.abs.backward.push_back(member.to_usize());
                }
            }
            while let Some(raw) = self.abs.forward.pop_front() {
                if self.abs.conflict.is_some() {
                    return;
                }
                self.abs_forward_one(Cfg::G::from_usize(raw));
            }
            while let Some(raw) = self.abs.backward.pop_front() {
                if self.abs.conflict.is_some() {
                    return;
                }
                self.abs_backward_one(Cfg::G::from_usize(raw));
            }
        }
    }

    fn abs_forward_one(&mut self, node: Cfg::G) {
        use crate::containers::DenseId;
        if !self.abs_analysed(node) {
            return;
        }
        let kids = self.abs_child_nodes(node);
        let mut args = Vec::with_capacity(kids.len());
        for kid in &kids {
            args.push(self.abs_read(*kid));
        }
        let op = self.node_op(node).to_usize();
        let value = self.abs.domain.as_ref().unwrap().forward(op, &args);
        self.abs_meet_node(node, value);
        let branch = args
            .first()
            .copied()
            .and_then(|cond| self.abs.domain.as_ref().unwrap().decided_branch(op, cond));
        if let Some(index) = branch
            && let Some(&child) = kids.get(index)
        {
            self.abs.derived.push((node.to_usize(), child.to_usize()));
        }
    }

    fn abs_backward_one(&mut self, node: Cfg::G) {
        use crate::containers::DenseId;
        if !self.abs_analysed(node) {
            return;
        }
        let kids = self.abs_child_nodes(node);
        if kids.is_empty() {
            return;
        }
        let args: Vec<u64> = kids.iter().copied().map(|k| self.abs_read(k)).collect();
        let op = self.node_op(node).to_usize();
        let result = self.abs_read(node);
        let Some(refined) = self
            .abs
            .domain
            .as_ref()
            .unwrap()
            .backward(op, result, &args)
        else {
            return;
        };
        if refined.len() != kids.len() {
            return;
        }
        for (kid, value) in kids.into_iter().zip(refined) {
            self.abs_meet_node(kid, value);
        }
    }

    fn abs_read(&self, node: Cfg::G) -> u64 {
        let sort = self.abs_sort_of(node);
        let top = self.abs.domain.as_ref().unwrap().top(sort);
        match self.abs_class_key(node) {
            Some(key) => self.abs.values.get(&key).copied().unwrap_or(top),
            None => top,
        }
    }

    fn abs_child_nodes(&mut self, node: Cfg::G) -> Vec<Cfg::G> {
        let mut out = Vec::new();
        self.for_each_child(node, |child, _| out.push(child));
        out
    }

    fn abs_apply_derived(&mut self) -> bool {
        use crate::containers::DenseId;
        let batch = std::mem::take(&mut self.abs.derived);
        let mut merged = false;
        for (class_node, partner) in batch {
            if self.abs.conflict.is_some() {
                break;
            }
            let a = Cfg::G::from_usize(class_node);
            let b = Cfg::G::from_usize(partner);
            if self.classes.find_const(a) == self.classes.find_const(b) {
                continue;
            }
            if self.merge(a, b).is_some() {
                merged = true;
            }
        }
        merged
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::EGraph31;
    use crate::literal::NiraLitVal;

    const TOP: u64 = u64::MAX;

    fn pack(lo: i32, hi: i32) -> u64 {
        ((lo as u32 as u64) << 32) | (hi as u32 as u64)
    }

    fn unpack(v: u64) -> (i32, i32) {
        ((v >> 32) as u32 as i32, v as u32 as i32)
    }

    struct Interval {
        sort: usize,
        add: usize,
        /// A second analysed sort, for tests that need two.
        also: Option<usize>,
    }

    impl AbsDomain for Interval {
        fn analysed_sort(&self, sort: usize) -> bool {
            sort == self.sort || Some(sort) == self.also
        }
        fn top(&self, _sort: usize) -> u64 {
            TOP
        }
        fn meet(&self, a: u64, b: u64) -> Option<u64> {
            if a == TOP {
                return Some(b);
            }
            if b == TOP {
                return Some(a);
            }
            let (alo, ahi) = unpack(a);
            let (blo, bhi) = unpack(b);
            let lo = alo.max(blo);
            let hi = ahi.min(bhi);
            if lo > hi { None } else { Some(pack(lo, hi)) }
        }
        fn forward(&self, op: usize, args: &[u64]) -> u64 {
            if op != self.add || args.len() != 2 || args[0] == TOP || args[1] == TOP {
                return TOP;
            }
            let (alo, ahi) = unpack(args[0]);
            let (blo, bhi) = unpack(args[1]);
            pack(alo.saturating_add(blo), ahi.saturating_add(bhi))
        }
        fn backward(&self, op: usize, result: u64, args: &[u64]) -> Option<Vec<u64>> {
            if op != self.add || args.len() != 2 || result == TOP {
                return None;
            }
            let (rlo, rhi) = unpack(result);
            let mut out = Vec::with_capacity(2);
            for i in 0..2 {
                let other = args[1 - i];
                if other == TOP {
                    out.push(TOP);
                    continue;
                }
                let (olo, ohi) = unpack(other);
                let lo = rlo.saturating_sub(ohi);
                let hi = rhi.saturating_sub(olo);
                if lo > hi {
                    return None;
                }
                out.push(pack(lo, hi));
            }
            Some(out)
        }
        fn as_constant(&self, value: u64) -> Option<i64> {
            if value == TOP {
                return None;
            }
            let (lo, hi) = unpack(value);
            if lo == hi { Some(lo as i64) } else { None }
        }
    }

    fn eg_with_add() -> (EGraph31<NiraLitVal>, crate::id::OpId, crate::id::OpId) {
        // Mark and restore need the semi-persistent columns (`TRACK`).
        let mut eg = EGraph31::<NiraLitVal>::new();
        let int = eg.intern_sort("Int");
        let add = eg.register_op2("add", int, int, int);
        eg.set_abs_domain(Box::new(Interval {
            sort: int.to_usize(),
            add: add.to_usize(),
            also: None,
        }));
        let c = eg.register_op0("c", int);
        (eg, add, c)
    }

    #[test]
    fn no_domain_pushes_nothing() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a = eg.register_op0("a", int);
        let b = eg.register_op0("b", int);
        let x = eg.add(a, &[]);
        let y = eg.add(b, &[]);
        eg.merge(x, y);
        eg.rebuild();
        assert!(eg.take_abs_conflict().is_none());
        assert_eq!(eg.abs_pending(), 0);
    }

    #[test]
    fn merge_meets_intervals_and_reports_a_conflict() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let d = eg.register_op0("d", sort);
        let y = eg.add(d, &[]);
        eg.abs_seed(x, pack(0, 9));
        eg.abs_seed(y, pack(5, 20));
        eg.merge(x, y);
        assert_eq!(eg.abs_value(x), Some(pack(5, 9)));
        assert!(eg.take_abs_conflict().is_none());

        let p_op = eg.register_op0("p", sort);
        let p = eg.add(p_op, &[]);
        let q_op = eg.register_op0("q", sort);
        let q = eg.add(q_op, &[]);
        eg.abs_seed(p, pack(0, 4));
        eg.abs_seed(q, pack(10, 20));
        eg.merge(p, q);
        let msg = eg.take_abs_conflict().expect("empty meet");
        assert!(msg.contains("abstract conflict"));
    }

    #[test]
    fn forward_and_backward_run_in_rebuild() {
        let (mut eg, add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let one_op = eg.register_op0("one", sort);
        let one = eg.add(one_op, &[]);
        let sum = eg.add(add, &[x, one]);
        eg.abs_seed(x, pack(0, 9));
        eg.abs_seed(one, pack(1, 1));
        eg.rebuild();
        assert_eq!(eg.abs_value(sum), Some(pack(1, 10)));

        let (mut eg, add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let one_op = eg.register_op0("one", sort);
        let one = eg.add(one_op, &[]);
        let sum = eg.add(add, &[x, one]);
        eg.abs_seed(one, pack(1, 1));
        eg.abs_seed(sum, pack(1, 5));
        eg.rebuild();
        assert_eq!(eg.abs_value(x), Some(pack(0, 4)));
    }

    #[test]
    fn budget_keeps_the_last_accepted_value() {
        let (mut eg, _add, c) = eg_with_add();
        eg.set_abs_budget(2);
        let x = eg.add(c, &[]);
        eg.abs_seed(x, pack(0, 100));
        eg.abs_seed(x, pack(1, 100));
        eg.abs_seed(x, pack(2, 100));
        assert_eq!(eg.abs_value(x), Some(pack(1, 100)));
        eg.abs_begin_epoch();
        eg.abs_seed(x, pack(2, 100));
        assert_eq!(eg.abs_value(x), Some(pack(2, 100)));
    }

    #[test]
    fn restore_clears_queues_and_puts_the_conflict_back() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        eg.abs_seed(x, pack(0, 10));
        assert!(eg.abs_pending() > 0);
        let token = eg.mark(crate::containers::ShrinkPolicy::Never);
        assert_eq!(eg.abs_pending(), 0);
        eg.abs_seed(x, pack(0, 3));
        assert!(eg.abs_pending() > 0);
        eg.restore(token);
        assert_eq!(eg.abs_pending(), 0);
        assert!(eg.take_abs_conflict().is_none());

        let y_sort = eg.node_sort(x);
        let y_op = eg.register_op0("y", y_sort);
        let y = eg.add(y_op, &[]);
        eg.abs_seed(x, pack(0, 4));
        eg.abs_seed(y, pack(10, 20));
        let token = eg.mark(crate::containers::ShrinkPolicy::Never);
        eg.merge(x, y);
        assert!(eg.abs_has_conflict());
        eg.restore(token);
        assert!(!eg.abs_has_conflict());
    }

    #[test]
    fn value_change_enters_the_touched_log_when_tracking() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        eg.clear_touched();
        eg.set_track_merge_members(true);
        eg.abs_seed(x, pack(0, 1));
        assert!(eg.touched().contains(&x));
    }

    #[test]
    fn singleton_derives_a_merge_with_its_literal() {
        let (mut eg, _add, c) = eg_with_add();
        let seeded = eg.add(c, &[]);
        let sort = eg.node_sort(seeded);
        let three = eg.register_op0("three", sort);
        let lit = eg.add(three, &[]);
        let class = eg.add(c, &[]);
        eg.abs_bind_constant(3, lit);
        eg.abs_seed(class, pack(3, 3));
        eg.rebuild();
        let class_root = eg.find(class);
        let lit_root = eg.find(lit);
        assert_eq!(class_root, lit_root);
    }

    /// `c` at {3} and the literal `three` share no parent until the derived merge
    /// joins them; then `f(c)` and `f(three)` are congruent. Returns the graph and
    /// those two nodes, before any rebuild.
    fn derived_merge_needs_congruence()
    -> (EGraph31<NiraLitVal>, crate::id::ENodeId, crate::id::ENodeId) {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let f = eg.register_op1("f", sort, sort);
        let three = eg.register_op0("three", sort);
        let lit = eg.add(three, &[]);
        let fx = eg.add(f, &[x]);
        let flit = eg.add(f, &[lit]);
        eg.abs_bind_constant(3, lit);
        eg.abs_seed(x, pack(3, 3));
        (eg, fx, flit)
    }

    #[test]
    fn completion_recloses_congruence_after_a_derived_merge() {
        let (mut eg, fx, flit) = derived_merge_needs_congruence();
        eg.set_cc(true);
        eg.rebuild();
        assert_eq!(
            eg.find(fx),
            eg.find(flit),
            "rebuild returned before re-closing congruence"
        );
    }

    #[test]
    fn completion_goal_sees_congruence_from_a_derived_merge() {
        let (mut eg, fx, flit) = derived_merge_needs_congruence();
        eg.set_cc(true);
        eg.set_cc_goal(Some((fx, flit)));
        eg.rebuild();
        assert!(
            matches!(
                eg.completion_outcome(),
                Some(super::super::CompletionOutcome::GoalMet { .. })
            ),
            "outcome: {:?}",
            eg.completion_outcome()
        );
    }

    /// `x` at [0,9] with parent `add(x, two)`, `y` at [0,4] with parent
    /// `add(two, y)`, `two` at {2}. Both sides have a parent, so whichever class
    /// survives, the other side's parent sees a narrower argument after the merge.
    /// The parents differ in argument order so that congruence does not join them.
    fn two_sides_with_parents() -> (EGraph31<NiraLitVal>, [crate::id::ENodeId; 4]) {
        let (mut eg, add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let d = eg.register_op0("d", sort);
        let y = eg.add(d, &[]);
        let two_op = eg.register_op0("two", sort);
        let two = eg.add(two_op, &[]);
        let sx = eg.add(add, &[x, two]);
        let sy = eg.add(add, &[two, y]);
        eg.abs_seed(x, pack(0, 9));
        eg.abs_seed(y, pack(0, 4));
        eg.abs_seed(two, pack(2, 2));
        eg.rebuild();
        assert_eq!(eg.abs_value(sx), Some(pack(2, 11)));
        assert_eq!(eg.abs_value(sy), Some(pack(2, 6)));
        (eg, [x, y, sx, sy])
    }

    /// Remi's item 4: when the survivor's value does not change, the absorbed
    /// side's parents must still be revisited.
    #[test]
    fn merge_revisits_the_absorbed_parents_in_either_order() {
        for swap in [false, true] {
            let (mut eg, [x, y, sx, sy]) = two_sides_with_parents();
            if swap {
                eg.merge(y, x);
            } else {
                eg.merge(x, y);
            }
            eg.rebuild();
            assert_eq!(eg.abs_value(x), Some(pack(0, 4)), "swap = {swap}");
            assert_eq!(eg.abs_value(sx), Some(pack(2, 6)), "swap = {swap}");
            assert_eq!(eg.abs_value(sy), Some(pack(2, 6)), "swap = {swap}");
        }
    }

    /// The absorbed side at top contributes nothing to the meet, but its parents
    /// still read the survivor's value after the merge.
    #[test]
    fn merge_with_a_top_class_revisits_its_parents() {
        for swap in [false, true] {
            let (mut eg, add, c) = eg_with_add();
            let x = eg.add(c, &[]);
            let sort = eg.node_sort(x);
            let d = eg.register_op0("d", sort);
            let y = eg.add(d, &[]);
            let two_op = eg.register_op0("two", sort);
            let two = eg.add(two_op, &[]);
            let sx = eg.add(add, &[x, two]);
            let sy = eg.add(add, &[two, y]);
            eg.abs_seed(y, pack(0, 4));
            eg.abs_seed(two, pack(2, 2));
            eg.rebuild();
            assert_eq!(eg.abs_value(sx), None);
            if swap {
                eg.merge(y, x);
            } else {
                eg.merge(x, y);
            }
            eg.rebuild();
            assert_eq!(eg.abs_value(sx), Some(pack(2, 6)), "swap = {swap}");
            assert_eq!(eg.abs_value(sy), Some(pack(2, 6)), "swap = {swap}");
        }
    }

    /// Remi's item 2: values written after a mark are undone by restore.
    #[test]
    fn restore_rolls_values_back() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        eg.abs_seed(x, pack(0, 10));
        let token = eg.mark(crate::containers::ShrinkPolicy::Never);
        eg.abs_seed(x, pack(0, 3));
        assert_eq!(eg.abs_value(x), Some(pack(0, 3)));
        eg.restore(token);
        assert_eq!(eg.abs_value(x), Some(pack(0, 10)));
    }

    /// A class made after the mark is gone after restore; a class made later may
    /// reuse its key and must start at top, not at the discarded value.
    #[test]
    fn restore_does_not_leak_a_value_to_a_reused_class_key() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let z_op = eg.register_op0("z", sort);
        let w_op = eg.register_op0("w", sort);
        let token = eg.mark(crate::containers::ShrinkPolicy::Never);
        let z = eg.add(z_op, &[]);
        eg.abs_seed(z, pack(0, 1));
        eg.restore(token);
        let w = eg.add(w_op, &[]);
        eg.rebuild();
        assert_eq!(eg.abs_value(w), None);
    }

    /// Nested scopes: each restore or pop undoes only its own scope's writes.
    #[test]
    fn nested_scopes_roll_values_back_one_level_at_a_time() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        eg.abs_seed(x, pack(0, 10));
        let outer = eg.mark(crate::containers::ShrinkPolicy::Never);
        eg.abs_seed(x, pack(0, 8));
        let inner = eg.mark(crate::containers::ShrinkPolicy::Never);
        eg.abs_seed(x, pack(0, 5));
        eg.restore_and_pop(inner);
        assert_eq!(eg.abs_value(x), Some(pack(0, 8)));
        eg.abs_seed(x, pack(0, 6));
        eg.restore(outer);
        assert_eq!(eg.abs_value(x), Some(pack(0, 10)));
        eg.abs_seed(x, pack(0, 7));
        eg.pop_scope();
        assert_eq!(eg.abs_value(x), Some(pack(0, 10)));
    }

    /// Remi's item 3: a singleton of one sort does not merge with a literal of another.
    #[test]
    fn a_constant_of_another_sort_is_not_a_partner() {
        let mut eg = EGraph31::<NiraLitVal>::new();
        let int = eg.intern_sort("Int");
        let real = eg.intern_sort("Real");
        let add = eg.register_op2("add", int, int, int);
        eg.set_abs_domain(Box::new(Interval {
            sort: int.to_usize(),
            add: add.to_usize(),
            also: Some(real.to_usize()),
        }));
        let three_real = eg.register_op0("three_r", real);
        let lit = eg.add(three_real, &[]);
        eg.abs_bind_constant(3, lit);
        let c = eg.register_op0("c", int);
        let x = eg.add(c, &[]);
        eg.abs_seed(x, pack(3, 3));
        eg.rebuild();
        assert_ne!(eg.find(x), eg.find(lit));
    }

    /// A constant bound after a mark is forgotten by restore: its literal node is gone.
    #[test]
    fn restore_forgets_a_constant_bound_after_the_mark() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let three = eg.register_op0("three", sort);
        let token = eg.mark(crate::containers::ShrinkPolicy::Never);
        let lit = eg.add(three, &[]);
        eg.abs_bind_constant(3, lit);
        eg.restore(token);
        let before = eg.len();
        eg.abs_seed(x, pack(3, 3));
        eg.rebuild();
        assert_eq!(eg.len(), before);
        assert_eq!(eg.find(x), x);
    }

    /// A constant bound before the mark survives restore and still derives its merge.
    #[test]
    fn restore_keeps_a_constant_bound_before_the_mark() {
        let (mut eg, _add, c) = eg_with_add();
        let x = eg.add(c, &[]);
        let sort = eg.node_sort(x);
        let three = eg.register_op0("three", sort);
        let lit = eg.add(three, &[]);
        eg.abs_bind_constant(3, lit);
        let token = eg.mark(crate::containers::ShrinkPolicy::Never);
        eg.abs_bind_constant(3, x);
        eg.restore(token);
        let y_op = eg.register_op0("y", sort);
        let y = eg.add(y_op, &[]);
        eg.abs_seed(y, pack(3, 3));
        eg.rebuild();
        assert_eq!(eg.find(y), eg.find(lit));
    }
}
