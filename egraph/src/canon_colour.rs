// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A colour for every class and node that depends only on the e-graph's content
//! (`doc/goal-stable-extraction.md`, decisions 1 and 2).
//!
//! Node and class ids follow allocation order, which follows the order rules were
//! applied in, so two runs that build the same e-graph number it differently. The colour
//! is colour refinement over the class graph, the function `tools/apps/dump_canon.py`
//! computes:
//!
//! ```text
//! colour[0](c)   = H({ (label(m), arity(m), subsumed(m)) : m in members(c) })
//! colour[k+1](c) = H({ (label(m), kids(k, m), subsumed(m)) : m in members(c) })
//! kids(k, m)     = [(colour[k](child), 1)] in order       for plain and `a` operators
//!                  sorted (colour, count) pairs            for ac, aci, and comm
//! ```
//!
//! `label` is the operator name, or a literal's value. A multiset child is one entry with
//! its multiplicity, as the node stores it and the dump writes it: `arity` is the total
//! count, and an unordered node's pairs merge equal colours by summing their counts, so
//! `kids` is the multiset of child colours without writing a child once per occurrence.
//! The rounds stop when the partition the colours
//! induce stops changing. That partition is the coarsest stable one, so two classes share
//! a colour exactly when they are bisimilar. The members are the ones the dump writes:
//! every node but a congruent duplicate.
//!
//! The hash is two seeded runs of `rapidhash_v3`, whose output the crate guarantees
//! stable across versions; a golden-value test pins it.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::registry::OpKind;
use std::collections::BTreeMap;

/// A 128-bit content colour.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Colour(pub u128);

impl Colour {
    /// The colour as 32 lowercase hexadecimal digits, the spelling the dump writes.
    pub fn hex(self) -> String {
        format!("{:032x}", self.0)
    }
}

const SEED_HI: rapidhash::v3::RapidSecrets = rapidhash::v3::RapidSecrets::seed_cpp(0x5e3a_7c01);
const SEED_LO: rapidhash::v3::RapidSecrets = rapidhash::v3::RapidSecrets::seed_cpp(0x9d1f_44b2);

/// The colour of a byte string.
pub fn hash_bytes(bytes: &[u8]) -> Colour {
    let hi = rapidhash::v3::rapidhash_v3_seeded(bytes, &SEED_HI);
    let lo = rapidhash::v3::rapidhash_v3_seeded(bytes, &SEED_LO);
    Colour((u128::from(hi) << 64) | u128::from(lo))
}

/// Tags that keep the encodings of different kinds of signature apart.
const TAG_SHALLOW: u8 = 0;
const TAG_MEMBER: u8 = 1;
const TAG_CLASS: u8 = 2;
const TAG_NODE: u8 = 3;

fn push_len(buf: &mut Vec<u8>, n: usize) {
    // A length always fits u64 on the targets this crate builds for; saturate otherwise.
    buf.extend_from_slice(&u64::try_from(n).unwrap_or(u64::MAX).to_le_bytes());
}

fn push_colours(buf: &mut Vec<u8>, cs: &[Colour]) {
    push_len(buf, cs.len());
    for c in cs {
        buf.extend_from_slice(&c.0.to_le_bytes());
    }
}

/// A count as the colouring hashes it: a u128 when it fits, which a sum of u64
/// multiplicities over fewer than 2^64 entries always does, and exact otherwise. A value
/// has one encoding whichever form computed it (`push_count`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Count {
    Small(u128),
    Big(num_bigint::BigUint),
}

impl Count {
    fn of<M: MultiplicityLike>(m: M) -> Self {
        match m.to_u64() {
            Some(v) => Count::Small(u128::from(v)),
            // Through the canonical form: a count in [2^64, 2^128) is `Small` here as it
            // is when a sum reaches it, so it has one encoding.
            None => Count::from_big(m.to_biguint()),
        }
    }

    fn big(&self) -> num_bigint::BigUint {
        match self {
            Count::Small(v) => num_bigint::BigUint::from(*v),
            Count::Big(b) => b.clone(),
        }
    }

    fn add(&self, other: &Self) -> Self {
        if let (Count::Small(a), Count::Small(b)) = (self, other)
            && let Some(s) = a.checked_add(*b)
        {
            return Count::Small(s);
        }
        Count::from_big(self.big() + other.big())
    }

    /// The canonical form: `Small` whenever the value fits u128.
    fn from_big(n: num_bigint::BigUint) -> Self {
        match u128::try_from(&n) {
            Ok(v) => Count::Small(v),
            Err(_) => Count::Big(n),
        }
    }
}

/// A count's bytes: 16 little-endian bytes when it fits u128, else a marker, a length,
/// and its little-endian digits. The marker keeps the two forms apart.
fn push_count(buf: &mut Vec<u8>, c: &Count) {
    match c {
        Count::Small(v) => buf.extend_from_slice(&v.to_le_bytes()),
        Count::Big(b) => {
            buf.push(0xff);
            let bytes = b.to_bytes_le();
            push_len(buf, bytes.len());
            buf.extend_from_slice(&bytes);
        }
    }
}

/// `(colour, count)` pairs.
fn push_counted(buf: &mut Vec<u8>, cs: &[(Colour, Count)]) {
    push_len(buf, cs.len());
    for (c, m) in cs {
        buf.extend_from_slice(&c.0.to_le_bytes());
        push_count(buf, m);
    }
}

/// One member as the colouring reads it.
struct Member<G> {
    id: G,
    label: Colour,
    unordered: bool,
    subsumed: bool,
    /// Child class indices with their multiplicities, one entry per stored child.
    kids: Vec<(usize, Count)>,
}

/// The colouring of one e-graph: classes in id order of their representative (an
/// internal order only; nothing written depends on it).
pub struct Colouring<G> {
    /// Each class's union-find representative.
    pub classes: Vec<G>,
    /// Each class's members as the dump writes them, in id order.
    pub members: Vec<Vec<G>>,
    pub class_colour: Vec<Colour>,
    /// Each class's members' colours, aligned with `members`.
    pub node_colour: Vec<Vec<Colour>>,
    /// Refinement rounds run after round 0.
    pub rounds: usize,
    /// Whether the partition stopped changing within the bound. Always true in theory
    /// (the bound is the class count plus one); false would mean a defect, reported
    /// instead of looping.
    pub converged: bool,
    index: BTreeMap<G, usize>,
}

impl<G: Ord + Copy> Colouring<G> {
    /// The index of the class whose representative is `repr`.
    pub fn class_of(&self, repr: G) -> Option<usize> {
        self.index.get(&repr).copied()
    }

    /// Groups of more than one class sharing a colour: structurally symmetric classes.
    pub fn symmetric_groups(&self) -> usize {
        let mut count: BTreeMap<Colour, usize> = BTreeMap::new();
        for &c in &self.class_colour {
            *count.entry(c).or_insert(0) += 1;
        }
        count.values().filter(|&&n| n > 1).count()
    }
}

/// The partition a colouring induces, as each class's block number in first-seen order.
fn partition(col: &[Colour]) -> Vec<usize> {
    let mut seen: BTreeMap<Colour, usize> = BTreeMap::new();
    col.iter()
        .map(|c| {
            let next = seen.len();
            *seen.entry(*c).or_insert(next)
        })
        .collect()
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    /// The content colouring of the graph as it stands.
    pub fn canon_colours(&self) -> Colouring<Cfg::G> {
        let mut by_class: BTreeMap<Cfg::G, Vec<Cfg::G>> = BTreeMap::new();
        for id in self.node_ids() {
            if self.node_flags(id) & crate::node_types::FLAG_CONGRUENT_DUP != 0 {
                continue;
            }
            by_class.entry(self.class_repr(id)).or_default().push(id);
        }
        let classes: Vec<Cfg::G> = by_class.keys().copied().collect();
        let index: BTreeMap<Cfg::G, usize> =
            classes.iter().enumerate().map(|(i, &c)| (c, i)).collect();
        let mut members: Vec<Vec<Member<Cfg::G>>> = Vec::with_capacity(classes.len());
        for ids in by_class.values_mut() {
            ids.sort_by_key(|id| id.to_usize());
            let ms = ids
                .iter()
                .map(|&id| {
                    let label = match self.get_lit_val(id) {
                        Some(v) => v.to_string(),
                        None => self.node_op_name(id).to_string(),
                    };
                    let unordered = matches!(
                        self.ops().info(self.node_op(id)).kind,
                        OpKind::MSet { .. } | OpKind::Set { .. } | OpKind::Commutative { .. }
                    );
                    let mut kids = Vec::new();
                    self.for_each_child(id, |child, mult| {
                        // A child class the dump has no member for is skipped, as the
                        // dump skips it; the `FLAG_CONGRUENT_DUP` invariant keeps every
                        // class non-empty, so this does not happen.
                        if let Some(&k) = index.get(&self.class_repr(child)) {
                            kids.push((k, Count::of(mult)));
                        }
                    });
                    Member {
                        id,
                        label: hash_bytes(label.as_bytes()),
                        unordered,
                        subsumed: self.node_flags(id) & crate::node_types::FLAG_SUBSUMED != 0,
                        kids,
                    }
                })
                .collect();
            members.push(ms);
        }

        let mut buf: Vec<u8> = Vec::new();
        let mut sigs: Vec<Colour> = Vec::new();
        let class_hash = |sigs: &mut Vec<Colour>, buf: &mut Vec<u8>| {
            sigs.sort_unstable();
            buf.clear();
            buf.push(TAG_CLASS);
            push_colours(buf, sigs);
            hash_bytes(buf)
        };
        // Round 0: the shallow signature.
        let mut col: Vec<Colour> = members
            .iter()
            .map(|ms| {
                sigs.clear();
                for m in ms {
                    buf.clear();
                    buf.push(TAG_SHALLOW);
                    buf.extend_from_slice(&m.label.0.to_le_bytes());
                    let arity = m
                        .kids
                        .iter()
                        .fold(Count::Small(0), |acc, (_, c)| acc.add(c));
                    push_count(&mut buf, &arity);
                    buf.push(u8::from(m.subsumed));
                    sigs.push(hash_bytes(&buf));
                }
                class_hash(&mut sigs, &mut buf)
            })
            .collect();
        let member_sig = |m: &Member<Cfg::G>, col: &[Colour], buf: &mut Vec<u8>, tag: u8| {
            let mut kids: Vec<(Colour, Count)> =
                m.kids.iter().map(|(k, c)| (col[*k], c.clone())).collect();
            if m.unordered {
                // The multiset of child colours: equal colours merge, their counts summed.
                kids.sort_unstable_by_key(|(c, _)| *c);
                kids.dedup_by(|later, earlier| {
                    let same = later.0 == earlier.0;
                    if same {
                        earlier.1 = earlier.1.add(&later.1);
                    }
                    same
                });
            }
            buf.clear();
            buf.push(tag);
            buf.extend_from_slice(&m.label.0.to_le_bytes());
            push_counted(buf, &kids);
            buf.push(u8::from(m.subsumed));
            hash_bytes(buf)
        };
        // Each round before the fixpoint splits at least one block, so the partition is
        // stable within as many rounds as there are classes; one more confirms it.
        let bound = classes.len().saturating_add(1);
        let mut part = partition(&col);
        let mut rounds = 0usize;
        let mut converged = false;
        while rounds < bound {
            let next: Vec<Colour> = members
                .iter()
                .map(|ms| {
                    sigs.clear();
                    for m in ms {
                        sigs.push(member_sig(m, &col, &mut buf, TAG_MEMBER));
                    }
                    class_hash(&mut sigs, &mut buf)
                })
                .collect();
            rounds += 1;
            let next_part = partition(&next);
            col = next;
            if next_part == part {
                converged = true;
                break;
            }
            part = next_part;
        }
        // A node's colour: its class's colour and its own signature, so two members of
        // one class differ, and a member of another class with the same content differs.
        let node_colour: Vec<Vec<Colour>> = members
            .iter()
            .enumerate()
            .map(|(ci, ms)| {
                ms.iter()
                    .map(|m| {
                        let own = member_sig(m, &col, &mut buf, TAG_NODE);
                        buf.clear();
                        buf.push(TAG_NODE);
                        buf.extend_from_slice(&col[ci].0.to_le_bytes());
                        buf.extend_from_slice(&own.0.to_le_bytes());
                        hash_bytes(&buf)
                    })
                    .collect()
            })
            .collect();
        Colouring {
            members: members
                .iter()
                .map(|ms| ms.iter().map(|m| m.id).collect())
                .collect(),
            classes,
            class_colour: col,
            node_colour,
            rounds,
            converged,
            index,
        }
    }
}
