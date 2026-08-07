// Layout parity assertions (fix 1 acceptance): the packed verus list types
// must match production's sizes exactly at equal id widths.
use semi_persistent_containers_verus as verus;

verus::define_id31! { pub struct VE / SVE, "e"; }
verus::define_id31! { pub struct VN / SVN, "n"; }

#[test]
fn node_size_matches_production() {
    // Production node for (u32-repr payload, u32 id): (u32, u32) = 8 bytes.
    // Verus node: payload VE (repr-transparent u32) + next_repr u32 = 8 bytes.
    assert_eq!(
        core::mem::size_of::<verus::list::ListNode<VE, VN>>(),
        8,
        "packed verus ListNode<31-bit payload, 31-bit id> must be 8 bytes"
    );
}

#[test]
fn head_size_matches_production() {
    // Production ListHead<N=u32>: head_repr u32 + tail_repr u32 + len u32 = 12.
    assert_eq!(
        core::mem::size_of::<verus::list::ListHead<VN>>(),
        12,
        "packed verus ListHead<31-bit id> must be 12 bytes"
    );
}

/// The e-class ring cell (the consumer swap, `egraph/src/classes.rs`).
///
/// This is the memory-parity claim for the swap: `classes.rs` no longer stores
/// its own `EClassEntry { next: T, repr_stored: <u32 as Tagged>::Repr }`, it
/// stores a `CircularList<Opt<T::Index>, T, TRACK>` cell. Both are 12 bytes and
/// compose the same way — a `BoolTagged<u32>` payload word pair (presence bit +
/// key) plus one niche-tagged id word (successor + capture bit in its spare MSB)
/// — so the ring costs the same per e-class after the swap as before it. The
/// cell is what multiplies by class count, and it is also what the diff log
/// records per captured write, so this equality is what keeps BOTH the live
/// footprint and the retained-history footprint at parity.
///
/// Asserted rather than argued because the composition is exactly the kind of
/// thing a later `Opt`/`Tagged` change could silently widen to 16.
#[test]
fn class_ring_cell_size_matches_production() {
    // Production's pre-swap cell, from the shared baseline module.
    use containers_conformance::prod_class_ring::EClassEntry;

    assert_eq!(
        core::mem::size_of::<EClassEntry>(),
        12,
        "harness check: production's pre-swap ring cell is 12 bytes at 31-bit ids"
    );
    assert_eq!(
        core::mem::size_of::<verus::circular_list::CircularListNode<verus::Opt<u32>, VN>>(),
        core::mem::size_of::<EClassEntry>(),
        "verus ring cell must match the hand-rolled cell the swap replaced"
    );
    // The *stored* form is what occupies the store's backing vector; the logical
    // node above is only ever a temporary. Both must be 12 for the claim to hold.
    assert_eq!(
        core::mem::size_of::<verus::circular_list::CircularNodeRepr<verus::Opt<u32>, VN>>(),
        core::mem::size_of::<EClassEntry>(),
        "verus ring cell's inline-stored repr must match production's cell"
    );
}
