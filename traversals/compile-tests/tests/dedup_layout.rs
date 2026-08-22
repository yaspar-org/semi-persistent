// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use semi_persistent_traversals::rec_family;

rec_family! {
    family Layout => LayoutStore;
    enum Root { One(Node) }
    enum Node { Leaf(i64) }
}

#[test]
fn dedup_modes_have_the_same_inline_store_layout() {
    assert_eq!(
        std::mem::size_of::<LayoutStore<false>>(),
        std::mem::size_of::<LayoutStore<true>>()
    );
}
