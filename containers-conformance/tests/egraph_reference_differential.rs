// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Differential coverage for the former production union-find and e-class
//! aggregate retained in `semi-persistent-containers`.

use proptest::prelude::*;
use semi_persistent_containers as reference;
use semi_persistent_containers_verus as verified;

reference::define_id31! { pub struct RefNode / StoredRefNode, "rn"; }
reference::define_id31! { pub struct RefList / StoredRefList, "rl"; }
reference::define_id31! { pub struct RefLink / StoredRefLink, "rk"; }
verified::define_id31! { pub struct VerNode / StoredVerNode, "vn"; }
verified::define_id31! { pub struct VerList / StoredVerList, "vl"; }
verified::define_id31! { pub struct VerLink / StoredVerLink, "vk"; }

type RefUf = reference::union_find::UnionFind<RefNode, reference::union_find::NoJust, true, false>;
type VerUf = verified::union_find::UnionFind<VerNode, verified::union_find::NoJust, true, false>;
type RefClasses = reference::eclasses::EClasses<
    RefNode,
    RefList,
    RefLink,
    reference::union_find::NoJust,
    true,
    false,
>;
type VerClasses = verified::eclasses::EClasses<
    VerNode,
    VerList,
    VerLink,
    verified::union_find::NoJust,
    true,
    false,
>;

fn rn(i: usize) -> RefNode {
    <RefNode as reference::DenseId>::from_usize(i)
}

fn vn(i: usize) -> VerNode {
    <VerNode as verified::DenseId>::try_new(i).expect("test id in range")
}

fn ref_index(i: <RefNode as reference::DenseId>::Index) -> usize {
    reference::IndexLike::as_usize(i)
}

fn ver_index(i: <VerNode as verified::DenseId>::Index) -> usize {
    verified::IndexLike::as_usize(i)
}

#[derive(Clone, Debug)]
enum UfOp {
    Add,
    Union {
        a: u8,
        b: u8,
        directed: bool,
        prefer_a: bool,
    },
    Mark,
    Restore,
}

fn uf_op() -> impl Strategy<Value = UfOp> {
    prop_oneof![
        4 => Just(UfOp::Add),
        8 => (any::<u8>(), any::<u8>(), any::<bool>(), any::<bool>())
            .prop_map(|(a, b, directed, prefer_a)| UfOp::Union {
                a,
                b,
                directed,
                prefer_a,
            }),
        1 => Just(UfOp::Mark),
        1 => Just(UfOp::Restore),
    ]
}

fn assert_uf_equal(reference: &RefUf, verified: &VerUf, n: usize) {
    assert_eq!(ref_index(reference.len()), n);
    assert_eq!(ver_index(verified.len()), n);
    for a in 0..n {
        assert_eq!(
            reference.find_const(rn(a)).to_usize(),
            verified.find_const(vn(a)).to_usize(),
            "representative differs for node {a}"
        );
        for b in 0..n {
            assert_eq!(
                reference.find_const(rn(a)) == reference.find_const(rn(b)),
                verified.find_const(vn(a)) == verified.find_const(vn(b)),
                "partition differs for ({a}, {b})"
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    #[test]
    fn retained_union_find_matches_verified(
        ops in prop::collection::vec(uf_op(), 1..96)
    ) {
        let mut r = RefUf::new();
        let mut v = VerUf::new();
        let mut marks = Vec::new();
        let mut n = 0usize;

        for op in ops {
            match op {
                UfOp::Add if n < 24 => {
                    r.make_set(rn(n));
                    v.make_set(vn(n));
                    n += 1;
                }
                UfOp::Union { a, b, directed, prefer_a } if n > 0 => {
                    let a = a as usize % n;
                    let b = b as usize % n;
                    let rr = if directed {
                        r.union_directed(rn(a), rn(b), prefer_a)
                    } else {
                        r.union(rn(a), rn(b))
                    };
                    let vr = if directed {
                        v.union_directed(vn(a), vn(b), prefer_a)
                    } else {
                        v.union(vn(a), vn(b))
                    };
                    prop_assert_eq!(rr.is_some(), vr.is_some());
                    if let (Some((rs, ra)), Some((vs, va))) = (rr, vr) {
                        prop_assert_eq!(rs.to_usize(), vs.to_usize());
                        prop_assert_eq!(ra.to_usize(), va.to_usize());
                    }
                }
                UfOp::Mark => {
                    marks.push((
                        r.mark(reference::ShrinkPolicy::Never),
                        v.try_mark(verified::ShrinkPolicy::Never).expect("tracked"),
                        n,
                    ));
                }
                UfOp::Restore if !marks.is_empty() => {
                    let (rt, vt, marked_n) = marks.pop().unwrap();
                    r.restore(rt);
                    v.try_restore(vt).expect("own innermost token");
                    n = marked_n;
                }
                _ => {}
            }
            assert_uf_equal(&r, &v, n);
        }
    }
}

#[test]
fn retained_union_find_reconstructs_the_same_proof_path() {
    type RefProofUf = reference::union_find::UnionFind<RefNode, u8, true, true>;
    type VerProofUf = verified::union_find::UnionFind<VerNode, u8, true, true>;

    let mut r = RefProofUf::new();
    let mut v = VerProofUf::new();
    for i in 0..5 {
        r.make_set(rn(i));
        v.make_set(vn(i));
    }

    r.union_justified(rn(0), rn(1), 11);
    v.union_justified(vn(0), vn(1), 11);
    r.union_justified_directed(rn(2), rn(1), 22, false);
    v.union_justified_directed(vn(2), vn(1), 22, false);

    let rt = r.mark(reference::ShrinkPolicy::Never);
    let vt = v.try_mark(verified::ShrinkPolicy::Never).expect("tracked");
    r.union_justified(rn(3), rn(2), 33);
    v.union_justified(vn(3), vn(2), 33);

    let mut rb = reference::union_find::ProofBuf::new();
    let mut vb = verified::union_find::ProofBuf::new();
    assert!(r.explain(rn(0), rn(3), &mut rb));
    assert!(v.explain(vn(0), vn(3), &mut vb));
    let r_path: Vec<_> = rb
        .steps
        .iter()
        .map(|(a, b, just)| (a.to_usize(), b.to_usize(), *just))
        .collect();
    let v_path: Vec<_> = vb
        .steps
        .iter()
        .map(|(a, b, just)| (a.to_usize(), b.to_usize(), *just))
        .collect();
    assert_eq!(r_path, v_path);

    r.restore(rt);
    v.try_restore(vt).expect("own token");
    rb.clear();
    vb.clear();
    assert!(!r.explain(rn(0), rn(3), &mut rb));
    assert!(!v.explain(vn(0), vn(3), &mut vb));
}

#[test]
fn directed_union_rank_saturates_without_changing_the_partition() {
    let mut r = RefUf::new();
    let mut v = VerUf::new();
    for i in 0..300 {
        r.make_set(rn(i));
        v.make_set(vn(i));
    }

    let mut r_root = rn(0);
    let mut v_root = vn(0);
    for i in 1..300 {
        r_root = r.union_directed(r_root, rn(i), false).unwrap().0;
        v_root = v.union_directed(v_root, vn(i), false).unwrap().0;
    }

    assert_uf_equal(&r, &v, 300);
}

#[derive(Clone, Debug)]
enum ClassOp {
    Add,
    AddUse { child: u8, parent: u8 },
    Merge { a: u8, b: u8, directed: bool },
    SetMinimum { class: u8, column: bool, node: u8 },
    SetAtomic { class: u8 },
    Mark,
    Restore,
}

fn class_op() -> impl Strategy<Value = ClassOp> {
    prop_oneof![
        4 => Just(ClassOp::Add),
        5 => (any::<u8>(), any::<u8>())
            .prop_map(|(child, parent)| ClassOp::AddUse { child, parent }),
        6 => (any::<u8>(), any::<u8>(), any::<bool>())
            .prop_map(|(a, b, directed)| ClassOp::Merge { a, b, directed }),
        3 => (any::<u8>(), any::<bool>(), any::<u8>())
            .prop_map(|(class, column, node)| ClassOp::SetMinimum { class, column, node }),
        1 => any::<u8>().prop_map(|class| ClassOp::SetAtomic { class }),
        1 => Just(ClassOp::Mark),
        1 => Just(ClassOp::Restore),
    ]
}

fn assert_classes_equal(reference: &RefClasses, verified: &VerClasses, n: usize) {
    assert_eq!(ref_index(reference.len()), n);
    assert_eq!(ver_index(verified.len()), n);
    assert_eq!(
        ref_index(reference.num_classes()),
        ver_index(verified.num_classes())
    );

    for i in 0..n {
        let rr = reference.find_const(rn(i));
        let vr = verified.find_const(vn(i));
        assert_eq!(rr.to_usize(), vr.to_usize(), "root differs for {i}");

        let rk = reference.repr_id(rr).expect("root has live class key");
        let vk = verified.repr_id(vr).expect("root has live class key");
        assert_eq!(ref_index(rk), ver_index(vk));
        assert_eq!(reference.atomic(rk), verified.atomic(vk));
        assert_eq!(reference.use_list_len(rk), verified.use_list_len(vk));

        for col in 0..2 {
            assert_eq!(
                reference.min_monomial(rk, col).map(|x| x.to_usize()),
                verified.min_monomial(vk, col).map(|x| x.to_usize())
            );
        }

        let mut rm: Vec<_> = reference.iter_class(rn(i)).map(|x| x.to_usize()).collect();
        let mut vm: Vec<_> = verified.iter_class(vn(i)).map(|x| x.to_usize()).collect();
        rm.sort_unstable();
        vm.sort_unstable();
        assert_eq!(rm, vm);

        let mut ru: Vec<_> = reference.iter_uses(rk).map(|x| x.to_usize()).collect();
        let mut vu: Vec<_> = verified.iter_uses(vk).map(|x| x.to_usize()).collect();
        ru.sort_unstable();
        vu.sort_unstable();
        assert_eq!(ru, vu);
    }
}

#[test]
fn retained_nested_restore_recaptures_a_post_mark_use_list() {
    let mut r = RefClasses::new();
    let mut v = VerClasses::new();
    r.set_min_width(2);
    v.set_min_width(2);

    r.add_singleton(rn(0));
    v.add_singleton(vn(0));
    let _outer_r = r.mark(reference::ShrinkPolicy::Never);
    let _outer_v = v.mark(verified::ShrinkPolicy::Never);

    r.add_use(r.repr_id(rn(0)).unwrap(), rn(0));
    v.add_use(v.repr_id(vn(0)).unwrap(), vn(0));
    r.add_singleton(rn(1));
    v.add_singleton(vn(1));
    r.add_use(r.repr_id(rn(1)).unwrap(), rn(0));
    v.add_use(v.repr_id(vn(1)).unwrap(), vn(0));

    let rm = r.merge(rn(1), rn(0)).unwrap();
    let vm = v.merge(vn(1), vn(0)).unwrap();
    let rr = r.repr_id(rm.survivor).unwrap();
    let vr = v.repr_id(vm.survivor).unwrap();
    r.splice_uses(r.use_list_id(rr), rm.absorbed_uses);
    v.splice_uses(v.use_list_id(vr), vm.absorbed_uses);
    assert_eq!(r.use_list_len(rr), 2);
    assert_eq!(v.use_list_len(vr), 2);

    let inner_r = r.mark(reference::ShrinkPolicy::Never);
    let inner_v = v.mark(verified::ShrinkPolicy::Never);
    r.add_use(rr, rn(0));
    v.add_use(vr, vn(0));
    assert_eq!(r.use_list_len(rr), 3);
    assert_eq!(v.use_list_len(vr), 3);

    r.restore(inner_r);
    v.restore(inner_v);
    let rr = r.repr_id(r.find_const(rn(0))).unwrap();
    let vr = v.repr_id(v.find_const(vn(0))).unwrap();
    assert_eq!(
        r.iter_uses(rr).count(),
        2,
        "retained list links must roll back"
    );
    assert_eq!(
        r.use_list_len(rr),
        2,
        "retained cached list length must roll back"
    );
    assert_eq!(v.iter_uses(vr).count(), 2);
    assert_eq!(v.use_list_len(vr), 2);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn retained_eclasses_match_verified(
        ops in prop::collection::vec(class_op(), 1..72)
    ) {
        let mut r = RefClasses::new();
        let mut v = VerClasses::new();
        r.set_min_width(2);
        v.set_min_width(2);
        let mut marks = Vec::new();
        let mut n = 0usize;

        for op in ops {
            match op {
                ClassOp::Add if n < 20 => {
                    let rk = r.add_singleton(rn(n));
                    let vk = v.add_singleton(vn(n));
                    prop_assert_eq!(ref_index(rk), ver_index(vk));
                    n += 1;
                }
                ClassOp::AddUse { child, parent } if n > 0 => {
                    let child = child as usize % n;
                    let parent = parent as usize % n;
                    let rr = r.find_const(rn(child));
                    let vr = v.find_const(vn(child));
                    r.add_use(r.repr_id(rr).unwrap(), rn(parent));
                    v.add_use(v.repr_id(vr).unwrap(), vn(parent));
                }
                ClassOp::Merge { a, b, directed } if n > 0 => {
                    let a = a as usize % n;
                    let b = b as usize % n;
                    let rm = if directed {
                        r.merge_directed(rn(a), rn(b))
                    } else {
                        r.merge(rn(a), rn(b))
                    };
                    let vm = if directed {
                        v.merge_directed(vn(a), vn(b))
                    } else {
                        v.merge(vn(a), vn(b))
                    };
                    prop_assert_eq!(rm.is_some(), vm.is_some());
                    if let (Some(rm), Some(vm)) = (rm, vm) {
                        prop_assert_eq!(rm.survivor.to_usize(), vm.survivor.to_usize());
                        prop_assert_eq!(rm.absorbed.to_usize(), vm.absorbed.to_usize());
                        prop_assert_eq!(
                            rm.absorbed_min_row.is_some(),
                            vm.absorbed_min_row.is_some()
                        );
                        for col in 0..2 {
                            prop_assert_eq!(
                                r.min_monomial_at_row(rm.absorbed_min_row, col)
                                    .map(|node| node.to_usize()),
                                v.min_monomial_at_row(vm.absorbed_min_row, col)
                                    .map(|node| node.to_usize())
                            );
                        }
                        prop_assert_eq!(rm.absorbed_atomic, vm.absorbed_atomic);
                        let rr = r.repr_id(rm.survivor).unwrap();
                        let vr = v.repr_id(vm.survivor).unwrap();
                        r.splice_uses(r.use_list_id(rr), rm.absorbed_uses);
                        v.splice_uses(v.use_list_id(vr), vm.absorbed_uses);
                    }
                }
                ClassOp::SetMinimum { class, column, node } if n > 0 => {
                    let class = class as usize % n;
                    let node = node as usize % n;
                    let rr = r.find_const(rn(class));
                    let vr = v.find_const(vn(class));
                    r.set_min_monomial(r.repr_id(rr).unwrap(), column as usize, rn(node));
                    v.set_min_monomial(v.repr_id(vr).unwrap(), column as usize, vn(node));
                }
                ClassOp::SetAtomic { class } if n > 0 => {
                    let class = class as usize % n;
                    let rr = r.find_const(rn(class));
                    let vr = v.find_const(vn(class));
                    r.set_atomic(r.repr_id(rr).unwrap());
                    v.set_atomic(v.repr_id(vr).unwrap());
                }
                ClassOp::Mark => {
                    marks.push((
                        r.mark(reference::ShrinkPolicy::Never),
                        v.mark(verified::ShrinkPolicy::Never),
                        n,
                    ));
                }
                ClassOp::Restore if !marks.is_empty() => {
                    let (rt, vt, marked_n) = marks.pop().unwrap();
                    r.restore(rt);
                    v.restore(vt);
                    n = marked_n;
                }
                _ => {}
            }
            assert_classes_equal(&r, &v, n);
        }
    }
}
