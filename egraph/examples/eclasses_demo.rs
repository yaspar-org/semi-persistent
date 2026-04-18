// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use semi_persistent_egraph::classes::EClasses;
use semi_persistent_egraph::id::{UseListId, UseNodeId};
use semi_persistent_egraph::{ENodeId, IdFactory, IndexLike};

fn main() {
    let mut ec = EClasses::<ENodeId, UseListId, UseNodeId, true, false>::new();
    let mut factory = IdFactory::<ENodeId>::new();

    let ids: Vec<ENodeId> = (0..50)
        .map(|_| {
            let id = factory.alloc();
            ec.add_singleton(id);
            id
        })
        .collect();

    // Merge into groups: {0..4}, {5..9}, {10..19}, {20..29}, {30..49}
    for i in 1..5 {
        ec.merge(ids[0], ids[i]);
    }
    for i in 6..10 {
        ec.merge(ids[5], ids[i]);
    }
    for i in 11..20 {
        ec.merge(ids[10], ids[i]);
    }
    for i in 21..30 {
        ec.merge(ids[20], ids[i]);
    }
    for i in 31..50 {
        ec.merge(ids[30], ids[i]);
    }

    println!("50 nodes, {} classes\n", ec.num_classes().as_usize());

    for &id in &ids {
        let class: Vec<_> = ec.iter_class(id).collect();
        let repr = ec.repr_id(id);
        if let Some(r) = repr {
            println!(
                "{id}: repr=s{r} class_size={} members={class:?}",
                class.len()
            );
        }
    }
}
