// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The e-graph's members as one typed-group member: a borrowed forwarding
//! struct over the nine member fields, driven by the e-graph's `History`
//! through `History::{mark_member, restore_member, restore_and_pop_member,
//! pop_member}` (design doc 10, "one external manager"). One stamp per scope
//! for the whole e-graph; the members carry no tokens.
//!
//! The `Member` impl is glue in an unverified crate: its spec parts are
//! trivial, its exec parts forward to the members' structural frame
//! operations, fanned out over a `rayon::scope` on disjoint `&mut` borrows
//! above the fan-out threshold (the same soundness argument the token-era
//! `mark_with`/`restore_with` used).

use crate::canon::{MSetCanon, VarCanon};
use crate::classes::EClasses;
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::containers::ShrinkPolicy;
use crate::containers::group::Member;
use crate::egraph::fanout_witness;
use crate::literal::{LitVal, LitValStore};
use crate::node_store::NodeStore;
use crate::registry::{AxiomRegistry, OpRegistry, RuleRegistry, SortRegistry};
use vstd::prelude::*;

pub(crate) struct EGraphMembers<
    'a,
    Cfg: EGraphConfig,
    L: LitVal,
    const TRACK: bool,
    const PROOFS: bool,
> where
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    pub sorts: &'a mut SortRegistry<Cfg::S, TRACK>,
    pub ops: &'a mut OpRegistry<Cfg::O, Cfg::S, TRACK>,
    pub rules: &'a mut RuleRegistry<TRACK>,
    pub axioms: &'a mut AxiomRegistry<Cfg::G, Cfg::A, TRACK>,
    pub lits: &'a mut LitValStore<L, Cfg::V, TRACK>,
    pub classes:
        &'a mut EClasses<Cfg::G, Cfg::ClassKey, Cfg::UL, Cfg::UN, TRACK, PROOFS, Cfg::Policy>,
    pub nodes:
        &'a mut NodeStore<Cfg::G, Cfg::O, Cfg::V, Cfg::C, Cfg::Ids, TRACK, PROOFS, Cfg::Policy>,
    pub unit_node:
        &'a mut crate::containers::SpUniqueMap<Cfg::O, Cfg::G, <Cfg::O as DenseId>::Index, TRACK>,
    pub inverse_op:
        &'a mut crate::containers::SpUniqueMap<Cfg::O, Cfg::O, <Cfg::O as DenseId>::Index, TRACK>,
    pub par: bool,
}

impl<'a, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraphMembers<'a, Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn depth_all(&self) -> usize {
        Member::depth_exec(&*self.classes)
    }

    fn can_push_all(&self) -> bool {
        Member::can_push_now(&*self.classes)
            && Member::can_push_now(&*self.unit_node)
            && Member::can_push_now(&*self.inverse_op)
            && self.nodes.frame_depth() < u32::MAX as usize
            && self.sorts.frame_depth() < u32::MAX as usize
            && self.ops.frame_depth() < u32::MAX as usize
            && self.rules.frame_depth() < u32::MAX as usize
            && self.axioms.frame_depth() < u32::MAX as usize
            && self.lits.frame_depth() < u32::MAX as usize
    }

    /// Fan one structural operation out over the seven wide members (parallel
    /// above the threshold), then the two small maps.
    fn each(
        &mut self,
        f_classes: impl FnOnce(
            &mut EClasses<Cfg::G, Cfg::ClassKey, Cfg::UL, Cfg::UN, TRACK, PROOFS, Cfg::Policy>,
        ) + Send,
        f_nodes: impl FnOnce(
            &mut NodeStore<Cfg::G, Cfg::O, Cfg::V, Cfg::C, Cfg::Ids, TRACK, PROOFS, Cfg::Policy>,
        ) + Send,
        f_sorts: impl FnOnce(&mut SortRegistry<Cfg::S, TRACK>) + Send,
        f_ops: impl FnOnce(&mut OpRegistry<Cfg::O, Cfg::S, TRACK>) + Send,
        f_rules: impl FnOnce(&mut RuleRegistry<TRACK>) + Send,
        f_axioms: impl FnOnce(&mut AxiomRegistry<Cfg::G, Cfg::A, TRACK>) + Send,
        f_lits: impl FnOnce(&mut LitValStore<L, Cfg::V, TRACK>) + Send,
    ) {
        if self.par {
            let (c, n, so, o, r, a, l) = (
                &mut *self.classes,
                &mut *self.nodes,
                &mut *self.sorts,
                &mut *self.ops,
                &mut *self.rules,
                &mut *self.axioms,
                &mut *self.lits,
            );
            rayon::scope(|s| {
                s.spawn(move |_| {
                    fanout_witness();
                    f_classes(c);
                });
                s.spawn(move |_| {
                    fanout_witness();
                    f_nodes(n);
                });
                s.spawn(move |_| {
                    fanout_witness();
                    f_sorts(so);
                });
                s.spawn(move |_| {
                    fanout_witness();
                    f_ops(o);
                });
                s.spawn(move |_| {
                    fanout_witness();
                    f_rules(r);
                });
                s.spawn(move |_| {
                    fanout_witness();
                    f_axioms(a);
                });
                s.spawn(move |_| {
                    fanout_witness();
                    f_lits(l);
                });
            });
        } else {
            f_classes(&mut *self.classes);
            f_nodes(&mut *self.nodes);
            f_sorts(&mut *self.sorts);
            f_ops(&mut *self.ops);
            f_rules(&mut *self.rules);
            f_axioms(&mut *self.axioms);
            f_lits(&mut *self.lits);
        }
    }

    fn push_all(&mut self, shrink: ShrinkPolicy) {
        self.each(
            |c| Member::push_frame(c, shrink),
            |n| n.push_frame(shrink),
            |so| so.push_frame(shrink),
            |o| o.push_frame(shrink),
            |r| r.push_frame(shrink),
            |a| a.push_frame(shrink),
            |l| l.push_frame(shrink),
        );
        Member::push_frame(&mut *self.unit_node, shrink);
        Member::push_frame(&mut *self.inverse_op, shrink);
    }

    fn reset_all(&mut self, depth: usize) {
        self.each(
            |c| Member::reset_frame(c, depth),
            |n| n.reset_frame(depth),
            |so| so.reset_frame(depth),
            |o| o.reset_frame(depth),
            |r| r.reset_frame(depth),
            |a| a.reset_frame(depth),
            |l| l.reset_frame(depth),
        );
        Member::reset_frame(&mut *self.unit_node, depth);
        Member::reset_frame(&mut *self.inverse_op, depth);
    }

    fn restore_all(&mut self, depth: usize) {
        self.each(
            |c| Member::restore_frame(c, depth),
            |n| n.restore_frame(depth),
            |so| so.restore_frame(depth),
            |o| o.restore_frame(depth),
            |r| r.restore_frame(depth),
            |a| a.restore_frame(depth),
            |l| l.restore_frame(depth),
        );
        Member::restore_frame(&mut *self.unit_node, depth);
        Member::restore_frame(&mut *self.inverse_op, depth);
    }

    fn pop_all(&mut self) {
        self.each(
            Member::pop_frame,
            |n| n.pop_frame(),
            |so| so.pop_frame(),
            |o| o.pop_frame(),
            |r| r.pop_frame(),
            |a| a.pop_frame(),
            |l| l.pop_frame(),
        );
        Member::pop_frame(&mut *self.unit_node);
        Member::pop_frame(&mut *self.inverse_op);
    }
}

verus! {

// Glue: the spec side is trivial (this crate is not verified); the exec side
// forwards to the fan-out above.
impl<'a, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> Member
    for EGraphMembers<'a, Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    type Model = ();

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn depth_spec(&self) -> nat {
        0
    }

    open spec fn can_push(&self) -> bool {
        true
    }

    open spec fn model(&self) -> () {
        ()
    }

    open spec fn archive(&self) -> Seq<()> {
        Seq::empty()
    }

    proof fn lemma_archive_depth(&self) {
    }

    fn can_push_now(&self) -> (b: bool) {
        self.can_push_all()
    }

    fn depth_exec(&self) -> (d: usize) {
        self.depth_all()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        self.push_all(shrink);
    }

    fn restore_frame(&mut self, depth: usize) {
        self.restore_all(depth);
    }

    fn reset_frame(&mut self, depth: usize) {
        self.reset_all(depth);
    }

    fn pop_frame(&mut self) {
        self.pop_all();
    }
}

} // verus!
