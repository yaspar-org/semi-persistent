// Layout parity assertions: the packed Verus list types
// must match production's sizes exactly at equal id widths.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

verus::define_id31! { pub struct VE / SVE, "e"; }
verus::define_id31! { pub struct VN / SVN, "n"; }
verus::define_id31! { pub struct VK / SVK, "k"; }
verus::define_id63! { pub struct VN64 / SVN64, "n64"; }
verus::define_id63! { pub struct VK64 / SVK64, "k64"; }

// The production-side ids for the ring-cell parity check. Both id families, so the
// claim is checked at each `EGraphConfig::Index` width rather than only at `u32`.
prod::define_id31! { pub struct PN31 / SPN31, "p"; }
prod::define_id31! { pub struct PK31 / SPK31, "pk"; }
prod::define_id63! { pub struct PN63 / SPN63, "p64"; }
prod::define_id63! { pub struct PK63 / SPK63, "pk64"; }

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

/// The list header, at both id families.
///
/// Production's `ListHead` is `(head_repr, tail_repr, len)` where `len` is `N::Index` —
/// the node arena's own index type — rather than a fixed `u32`. This test is the witness
/// that following the id family there costs nothing, which is what made the widening
/// unconditional instead of a 63-bit-only concession:
///
/// * 31-bit `N`: two `u32` words plus a `u32` count = 12 bytes. Unchanged; the count was
///   already this wide.
/// * 63-bit `N`: two `u64` words plus a `u64` count = 24 bytes. A `u32` count would have
///   padded `(u64, u64, u32)` back up to 24 anyway, so the wider count lives in padding
///   that existed either way — and buys the removal of a hard 4-billion-element cap on a
///   single list at an id width whose arena has room for far more.
///
/// Both are asserted, because a single-width check is exactly what would let a future
/// `u32` count slip back in unnoticed: it is free at 31 bits and only wrong at 63.
/// Production's own in-crate counterpart is `head_is_two_words_plus_a_same_width_count`
/// (`containers/src/list.rs`), which can see the private type directly.
#[test]
fn head_size_matches_production() {
    assert_eq!(
        core::mem::size_of::<verus::list::ListHead<VN>>(),
        12,
        "packed verus ListHead<31-bit id> must be 12 bytes"
    );
    assert_eq!(
        core::mem::size_of::<verus::list::ListHead<VN64>>(),
        24,
        "packed verus ListHead<63-bit id> must be 24 bytes: two u64 words + a u64 count, \
         which is what `(u64, u64, u32)` already padded to"
    );

    // The *stored* form is what occupies the store's backing vector (the logical header is
    // only ever a temporary), so the claim has to hold of the repr too. `ListHeadRepr`'s
    // count parameter is written `<Id as DenseId>::Index`, never a literal word: hard-coding
    // it would let this test keep passing while asserting about a type the arena no longer
    // instantiates.
    assert_eq!(
        core::mem::size_of::<
            verus::list::ListHeadRepr<
                <VN as verus::tagged::Tagged>::Repr,
                <VN as verus::opt::DenseId>::Index,
            >,
        >(),
        12,
        "the inline-stored 31-bit header repr must match the header"
    );
    assert_eq!(
        core::mem::size_of::<
            verus::list::ListHeadRepr<
                <VN64 as verus::tagged::Tagged>::Repr,
                <VN64 as verus::opt::DenseId>::Index,
            >,
        >(),
        24,
        "the inline-stored 63-bit header repr must match the header"
    );
}

/// The e-class ring cell used by `egraph/src/classes.rs`.
///
/// The verified `CircularList<Opt<K>, T, TRACK>` cell and the retained
/// `EClassEntry` reference cell compose the same way: one niche-tagged class
/// key word plus one niche-tagged successor word. The
/// cell is what multiplies by class count, and it is also what the diff log
/// records per captured write, so equality covers both live and retained-history
/// footprint.
///
/// Asserted rather than argued because the composition is exactly the kind of
/// thing a later `Opt`/`Tagged` change could silently widen to 16.
///
/// Checked at **both** id families, not just 31-bit. `EGraphConfig::Index` is the
/// word every capacity-coupled id is pinned to (`egraph/src/config.rs`), precisely
/// so a wide e-graph gets wide arenas without overflow risk; a parity claim that
/// only holds at `u32` would not cover a `define_id63!` config, and the failure
/// mode there is silent memory growth, not a compile error. Both sides are generic
/// over the id, so both instantiations are just type arguments.
///
/// Both IDs store their configured-width `Tagged::Repr`, never a hard-coded
/// `u32`/`u64`: the cell follows its node and class-key families by
/// construction. Only the expected 31-bit size is literal; the 63-bit rows
/// compare against the retained cell.
#[test]
fn class_ring_cell_size_matches_production() {
    // Former production cell retained in the reference containers crate.
    use prod::eclasses::EClassEntry;

    // The verified cell at each id family, payload word derived from the id.
    type Cell31 = verus::circular_list::CircularListNode<verus::Opt<VK>, VN>;
    type Repr31 = verus::circular_list::CircularNodeRepr<verus::Opt<VK>, VN>;
    type Cell63 = verus::circular_list::CircularListNode<verus::Opt<VK64>, VN64>;
    type Repr63 = verus::circular_list::CircularNodeRepr<verus::Opt<VK64>, VN64>;

    // 31-bit family: one 4-byte successor word + one 4-byte optional-key word.
    assert_eq!(
        core::mem::size_of::<EClassEntry<PN31, PK31>>(),
        8,
        "reference ring cell is two words at 31-bit ids"
    );
    assert_eq!(
        core::mem::size_of::<Cell31>(),
        core::mem::size_of::<EClassEntry<PN31, PK31>>(),
        "verified ring cell must match the reference cell"
    );
    // The *stored* form is what occupies the store's backing vector; the logical
    // node above is only ever a temporary. Both must be 8 for the claim to hold.
    assert_eq!(
        core::mem::size_of::<Repr31>(),
        core::mem::size_of::<EClassEntry<PN31, PK31>>(),
        "verus ring cell's inline-stored repr must match production's cell"
    );

    // 63-bit family: the same composition one word wider. The absolute size is
    // asserted against the reference cell rather than a literal, so this remains
    // a cross-implementation equality rather than a second layout specification.
    assert_eq!(
        core::mem::size_of::<Cell63>(),
        core::mem::size_of::<EClassEntry<PN63, PK63>>(),
        "verus ring cell must match production's cell at 63-bit ids too"
    );
    assert_eq!(
        core::mem::size_of::<Repr63>(),
        core::mem::size_of::<EClassEntry<PN63, PK63>>(),
        "verus ring cell's stored repr must match production's cell at 63-bit ids"
    );
}
