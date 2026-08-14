// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance of the verified `EClasses` aggregate: layout pins for the
//! swapped-in structure, and a reference-model differential over randomized
//! operation traces (allocation, directed and by-rank merges, use-lists,
//! find, mark/restore).
//!
//! There is no production-crate `EClasses` twin (the hand-rolled aggregate
//! lived in the e-graph and is replaced by the verified kernel), so the
//! oracle here is a transparent model: a naive union-find over `Vec<usize>`,
//! class membership as sorted vectors, use-lists as `Vec<Vec<usize>>`, and
//! mark/restore as whole-model snapshots. The differential checks the
//! RELATION the e-graph consumes — same-class equivalence, root/key
//! liveness, ring membership, use-list contents — not representative
//! identity, which is a policy choice (rank or parent count), asserted
//! separately where the API pins it (`merge_directed`).

use semi_persistent_containers_verus as verus;
use verus::eclasses::EClasses;
use verus::index_like::IndexLike;
use verus::opt::DenseId;
use verus::vec::ShrinkPolicy;

verus::define_id31! { pub struct CE / StoredCE, "e"; }
verus::define_id31! { pub struct CL / StoredCL, "l"; }
verus::define_id31! { pub struct CN / StoredCN, "n"; }

use semi_persistent_containers_verus::union_find::NoJust;
verus::define_id63! { pub struct CE64 / StoredCE64, "e64"; }
verus::define_id63! { pub struct CL64 / StoredCL64, "l64"; }
verus::define_id63! { pub struct CN64 / StoredCN64, "n64"; }
type EC = EClasses<CE, CL, CN, NoJust, true, false>;
type EC64 = EClasses<CE64, CL64, CN64, NoJust, true, false>;

// ---------------------------------------------------------------------------
// Layout pins (the numbers the swap was required to keep)
// ---------------------------------------------------------------------------

#[cfg(target_pointer_width = "64")]
#[test]
fn ring_cell_is_12_bytes_at_31_bit_ids() {
    assert_eq!(
        core::mem::size_of::<
            verus::circular_list::CircularNodeRepr<verus::Opt<<CE as DenseId>::Index>, CE>,
        >(),
        12,
        "e-class ring cell: next word (4) + BoolTagged key payload (8)"
    );
}

#[cfg(target_pointer_width = "64")]
#[test]
fn class_slot_is_12_bytes_at_31_bit_ids() {
    use verus::tagged::Tagged;
    assert_eq!(
        core::mem::size_of::<<verus::eclasses::ClassData<CL, CE> as Tagged>::Repr>(),
        12,
        "per-class slot: use-list word (4) + row number (4) + two flags"
    );
}

#[cfg(target_pointer_width = "64")]
#[test]
fn union_find_columns_are_bare_words() {
    // The verified union-find's parent column stores the id type itself
    // (4-byte word at 31-bit ids inside an InlineStore), the rank column a
    // BoolTagged u8. No hidden per-element bookkeeping beyond the store's
    // own capture bits.
    assert_eq!(core::mem::size_of::<CE>(), 4, "parent column element");
}

// ---------------------------------------------------------------------------
// Reference model
// ---------------------------------------------------------------------------

#[derive(Clone, Default)]
struct Model {
    parent: Vec<usize>,
    /// use-list contents per class, keyed by the AGGREGATE's repr key
    /// (usize form); merged into the survivor's on splice.
    uses: Vec<Vec<usize>>,
    /// node -> its class's live key while the node is canonical.
    key_of_root: std::collections::BTreeMap<usize, usize>,
}

impl Model {
    fn find(&self, x: usize) -> usize {
        let mut cur = x;
        while self.parent[cur] != cur {
            cur = self.parent[cur];
        }
        cur
    }
    fn add_singleton(&mut self, key: usize) {
        let id = self.parent.len();
        self.parent.push(id);
        if self.uses.len() <= key {
            self.uses.resize(key + 1, Vec::new());
        }
        self.uses[key].clear();
        self.key_of_root.insert(id, key);
    }
    fn class_members(&self, x: usize) -> Vec<usize> {
        let r = self.find(x);
        let mut m: Vec<usize> = (0..self.parent.len())
            .filter(|&y| self.find(y) == r)
            .collect();
        m.sort_unstable();
        m
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn ce(n: usize) -> CE {
    CE::try_new(n).expect("trace id in range")
}

fn ec_key(ec: &EC, node: CE) -> Option<usize> {
    ec.repr_id(node).map(|k| k.as_usize())
}

fn trace(seed: u64, steps: usize) {
    let mut ec = EC::new();
    let mut m = Model::default();
    let mut rng = Rng(seed | 1);
    let mut marks: Vec<(verus::eclasses::EClassesToken, Model)> = Vec::new();

    for step in 0..steps {
        let n = m.parent.len();
        match rng.next() % 10 {
            // allocate
            0..=2 => {
                let (id, key) = ec.try_add_singleton();
                assert_eq!(id.to_usize(), n);
                m.add_singleton(key.as_usize());
            }
            // merge (by rank)
            3..=4 if n >= 2 => {
                let a = rng.below(n);
                let b = rng.below(n);
                let (ca, cb) = (ce(a), ce(b));
                let same = m.find(a) == m.find(b);
                let r = ec.merge(ca, cb);
                assert_eq!(r.is_none(), same, "step {step}: merge None iff same class");
                if let Some(mi) = r {
                    // survivor and absorbed are the two roots.
                    let (ra, rb) = (m.find(a), m.find(b));
                    let s = mi.survivor.to_usize();
                    let ab = mi.absorbed.to_usize();
                    assert!(
                        (s == ra && ab == rb) || (s == rb && ab == ra),
                        "step {step}: merge endpoints are the prior roots"
                    );
                    // model: link absorbed under survivor; splice uses.
                    let abs_key = m.key_of_root.remove(&ab).expect("absorbed had a key");
                    m.parent[ab] = s;
                    // the aggregate's key survives on the survivor.
                    let s_key = *m.key_of_root.get(&s).expect("survivor keeps its key");
                    ec.splice_uses(
                        ec.use_list_id(ec.repr_id(mi.survivor).unwrap()),
                        mi.absorbed_uses,
                    );
                    let moved = std::mem::take(&mut m.uses[abs_key]);
                    m.uses[s_key].extend(moved);
                }
            }
            // directed merge: larger use-list must survive
            5 if n >= 2 => {
                let a = rng.below(n);
                let b = rng.below(n);
                if m.find(a) != m.find(b) {
                    let (ra, rb) = (m.find(a), m.find(b));
                    let ka = m.key_of_root[&ra];
                    let kb = m.key_of_root[&rb];
                    let (la, lb) = (m.uses[ka].len(), m.uses[kb].len());
                    let prefer_a = la >= lb;
                    let mi = ec
                        .merge_directed_with(ce(a), ce(b), prefer_a)
                        .expect("distinct classes merge");
                    let expect_s = if prefer_a { ra } else { rb };
                    assert_eq!(
                        mi.survivor.to_usize(),
                        expect_s,
                        "step {step}: directed survivor"
                    );
                    let ab = mi.absorbed.to_usize();
                    let abs_key = m.key_of_root.remove(&ab).unwrap();
                    m.parent[ab] = expect_s;
                    let s_key = m.key_of_root[&expect_s];
                    ec.splice_uses(
                        ec.use_list_id(ec.repr_id(mi.survivor).unwrap()),
                        mi.absorbed_uses,
                    );
                    let moved = std::mem::take(&mut m.uses[abs_key]);
                    m.uses[s_key].extend(moved);
                }
            }
            // add_use to a random live class
            6 if n >= 1 => {
                let x = rng.below(n);
                let parent_node = rng.below(n);
                let root = m.find(x);
                let key = m.key_of_root[&root];
                ec.add_use(ec.repr_id(ce(root)).unwrap(), ce(parent_node));
                m.uses[key].push(parent_node);
            }
            // mark
            7 => {
                marks.push((ec.mark(ShrinkPolicy::Never), m.clone()));
            }
            // restore the innermost outstanding mark
            8 if !marks.is_empty() => {
                let (tok, snap) = marks.pop().unwrap();
                ec.try_restore(tok).expect("token minted by this trace");
                m = snap;
            }
            // checks
            _ if n >= 1 => {
                let a = rng.below(n);
                let b = rng.below(n);
                let (ca, cb) = (ce(a), ce(b));
                assert_eq!(
                    ec.find_const(ca).to_usize() == ec.find_const(cb).to_usize(),
                    m.find(a) == m.find(b),
                    "step {step}: same-class relation"
                );
                // roots hold live keys; non-roots hold none.
                assert_eq!(
                    ec_key(&ec, ca).is_some(),
                    m.find(a) == a,
                    "step {step}: key presence iff root"
                );
                // ring membership matches the class.
                let mut ring: Vec<usize> = ec.iter_class(ca).map(|x: CE| x.to_usize()).collect();
                ring.sort_unstable();
                assert_eq!(ring, m.class_members(a), "step {step}: ring == class");
                // use-list contents (as multisets) match.
                let root = m.find(a);
                let key = m.key_of_root[&root];
                let mut got: Vec<usize> = ec
                    .iter_uses(ec.repr_id(ce(root)).unwrap())
                    .map(|x: CE| x.to_usize())
                    .collect();
                let mut want = m.uses[key].clone();
                got.sort_unstable();
                want.sort_unstable();
                assert_eq!(got, want, "step {step}: use-list contents");
                assert_eq!(
                    ec.use_list_len(ec.repr_id(ce(root)).unwrap()),
                    want.len(),
                    "step {step}: O(1) length agrees"
                );
            }
            _ => {}
        }
        assert_eq!(
            ec.len().as_usize(),
            m.parent.len(),
            "step {step}: node count"
        );
        assert_eq!(
            ec.num_classes().as_usize(),
            m.key_of_root.len(),
            "step {step}: class count"
        );
    }
}

#[test]
fn differential_short_traces() {
    for seed in 1..=32u64 {
        trace(seed, 200);
    }
}

#[test]
fn differential_long_trace() {
    trace(0xE61A55, 3000);
}

// ---------------------------------------------------------------------------
// 63-bit twin: the same relation checks over the wide id family
// ---------------------------------------------------------------------------

fn ce64(n: usize) -> CE64 {
    CE64::try_new(n).expect("trace id in range")
}

#[test]
fn bits63_smoke_relation() {
    let mut ec = EC64::new();
    let mut m = Model::default();
    for _ in 0..24 {
        let (id, key) = ec.try_add_singleton();
        assert_eq!(id.to_usize(), m.parent.len());
        m.add_singleton(key.as_usize());
    }
    for step in 0..24usize {
        let a = (step * 7) % 24;
        let b = (step * 11 + 3) % 24;
        let same = m.find(a) == m.find(b);
        let r = ec.merge(ce64(a), ce64(b));
        assert_eq!(r.is_none(), same, "63-bit step {step}");
        if let Some(mi) = r {
            let ab = mi.absorbed.to_usize();
            let s = mi.survivor.to_usize();
            m.key_of_root.remove(&ab).expect("absorbed had a key");
            m.parent[ab] = s;
        }
    }
    for a in 0..24usize {
        for b in 0..24usize {
            assert_eq!(
                ec.find_const(ce64(a)).to_usize() == ec.find_const(ce64(b)).to_usize(),
                m.find(a) == m.find(b),
                "63-bit relation ({a},{b})"
            );
        }
    }
}
