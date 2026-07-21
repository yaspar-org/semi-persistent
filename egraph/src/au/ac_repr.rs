// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical AC/ACI monomial representations, shared by the exact solver's and
//! MCGS's min-cost transport paths (§3.4.4).
//!
//! A class viewed under an AC/ACI operator has one monomial representation per
//! member with that operator (the member's canonical child multiset), plus, when
//! the operator declares an identity, the virtual singleton monomial `{class¹}`
//! for classes with no such member (the e-graph canonizes one-child applications
//! to the bare child, so the member disappears while the algebraic reading
//! `op(x) = x` remains). Centralizing this here keeps the exact and MCGS paths
//! from drifting on identity, padding, and dedup semantics.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::id::ENodeKind;
use crate::literal::LitVal;

use super::egraph_api::{AuSnapshot, ClassOf};

/// One canonical monomial: sorted, deduplicated `(child class, multiplicity)`
/// pairs with all multiplicities positive.
pub type Monomial<C> = Vec<(C, u32)>;

fn canonize<C: DenseId>(mut m: Monomial<C>) -> Monomial<C> {
    m.sort_unstable_by_key(|(c, _)| c.to_usize());
    // Merge duplicate classes (defensive; canonical members are already merged).
    let mut out: Monomial<C> = Vec::with_capacity(m.len());
    for (c, k) in m {
        if k == 0 {
            continue;
        }
        match out.last_mut() {
            Some((lc, lk)) if *lc == c => *lk += k,
            _ => out.push((c, k)),
        }
    }
    out
}

/// All canonical monomial representations of `class` under `op`.
/// `op` must have canon class MSet or Set.
pub fn monomials_of<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    class: ClassOf<Cfg>,
    op: Cfg::O,
) -> Vec<Monomial<ClassOf<Cfg>>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let eg = snap.egraph();
    let kind = eg.ops().info(op).canon_class();
    debug_assert!(matches!(kind, ENodeKind::MSet | ENodeKind::Set));

    let mut reprs: Vec<Monomial<ClassOf<Cfg>>> = Vec::new();

    for &(member_op, member_id) in snap.members(class) {
        if member_op != op {
            continue;
        }
        let mono: Monomial<ClassOf<Cfg>> = if kind == ENodeKind::MSet {
            let mut buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
            eg.mset_children(member_id, &mut buf);
            canonize(
                buf.iter()
                    .map(|(g, m)| (snap.class_of(*g).unwrap(), (*m).into()))
                    .collect(),
            )
        } else {
            let mut children: Monomial<ClassOf<Cfg>> = Vec::new();
            eg.for_each_child(member_id, |child, _| {
                children.push((snap.class_of(child).unwrap(), 1));
            });
            canonize(children)
        };
        if !reprs.contains(&mono) {
            reprs.push(mono);
        }
    }

    // Virtual singleton: with an identity, any class is also the monomial
    // {class¹} (algebraically op(x) = x via the identity collapse). This
    // reading is valid regardless of whether explicit op-members exist: a
    // class containing combine(a,b) is still itself a valid singleton
    // argument to combine, reading as combine(class, identity) = class.
    if snap.op_identity_class(op).is_some() {
        let singleton = vec![(class, 1)];
        if !reprs.contains(&singleton) {
            reprs.push(singleton);
        }
    }

    reprs
}

/// Total multiplicity of a monomial.
pub fn total<C: DenseId>(m: &Monomial<C>) -> u32 {
    m.iter().map(|(_, k)| *k).sum()
}

/// Pad the smaller of two monomials with identity copies so totals are equal.
/// Returns `None` when totals differ and the operator has no identity.
pub fn pad_pair<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    op: Cfg::O,
    left: &Monomial<ClassOf<Cfg>>,
    right: &Monomial<ClassOf<Cfg>>,
) -> Option<(Monomial<ClassOf<Cfg>>, Monomial<ClassOf<Cfg>>)>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let lt = total(left);
    let rt = total(right);
    if lt == rt {
        return Some((left.clone(), right.clone()));
    }
    let id_class = snap.op_identity_class(op)?;
    let mut l = left.clone();
    let mut r = right.clone();
    if lt < rt {
        add_identity(&mut l, id_class, rt - lt);
    } else {
        add_identity(&mut r, id_class, lt - rt);
    }
    Some((canonize(l), canonize(r)))
}

fn add_identity<C: DenseId>(m: &mut Monomial<C>, id_class: C, deficit: u32) {
    if let Some(entry) = m.iter_mut().find(|(c, _)| *c == id_class) {
        entry.1 += deficit;
    } else {
        m.push((id_class, deficit));
    }
}

/// All padded representation pairs of classes `l` and `r` under `op`, ready for
/// matrix enumeration or transport solving. Pairs with unequal totals and no
/// identity are skipped. Deduplicated.
pub fn representation_pairs<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
    op: Cfg::O,
) -> Vec<(Monomial<ClassOf<Cfg>>, Monomial<ClassOf<Cfg>>)>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let l_reprs = monomials_of(snap, l, op);
    let r_reprs = monomials_of(snap, r, op);
    // A pair of virtual singletons ({l¹} vs {r¹}) degenerates to AU(l, r)
    // itself and would recurse unproductively; require at least one real
    // op-member representation in the pair. A representation is virtual
    // exactly when it is the singleton of its own class.
    let is_virtual = |m: &Monomial<ClassOf<Cfg>>, class: ClassOf<Cfg>| {
        m.len() == 1 && m[0].0 == class && m[0].1 == 1
    };

    let mut out: Vec<(Monomial<ClassOf<Cfg>>, Monomial<ClassOf<Cfg>>)> = Vec::new();
    for lm in &l_reprs {
        for rm in &r_reprs {
            if is_virtual(lm, l) && is_virtual(rm, r) {
                continue;
            }
            if let Some(pair) = pad_pair(snap, op, lm, rm)
                && !out.contains(&pair)
            {
                out.push(pair);
            }
        }
    }
    out
}

/// The distinct AC/ACI operators relevant to the class pair `(l, r)`: any MSet
/// or Set operator appearing in either side's members. (Operators appearing on
/// one side only still matter through the virtual singleton of the other side.)
pub fn common_ac_ops<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> Vec<Cfg::O>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let eg = snap.egraph();
    let mut ops: Vec<Cfg::O> = Vec::new();
    for &(op, _) in snap.members(l).iter().chain(snap.members(r).iter()) {
        let kind = eg.ops().info(op).canon_class();
        if matches!(kind, ENodeKind::MSet | ENodeKind::Set) && !ops.contains(&op) {
            ops.push(op);
        }
    }
    ops.sort_unstable_by_key(|o| o.to_usize());
    ops
}
