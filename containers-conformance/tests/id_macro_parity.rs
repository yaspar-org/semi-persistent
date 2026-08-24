// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime and layout parity for the generated dense-ID families.

use proptest::prelude::*;
use semi_persistent_containers as plain;
use semi_persistent_containers_verus as verified;

plain::define_id7! { pub struct PlainId7 / StoredPlainId7, "p7_"; }
plain::define_id15! { pub struct PlainId15 / StoredPlainId15, "p15_"; }
plain::define_id31! { pub struct PlainId31 / StoredPlainId31, "p31_"; }
plain::define_id63! { pub struct PlainId63 / StoredPlainId63, "p63_"; }

verified::define_id7! { pub struct VerifiedId7 / StoredVerifiedId7, "v7_"; }
verified::define_id15! { pub struct VerifiedId15 / StoredVerifiedId15, "v15_"; }
verified::define_id31! { pub struct VerifiedId31 / StoredVerifiedId31, "v31_"; }
verified::define_id63! { pub struct VerifiedId63 / StoredVerifiedId63, "v63_"; }

macro_rules! assert_id_contract {
    ($containers:ident, $id:ty, $word:ty, $value:expr, $max:expr, $prefix:expr) => {{
        let value: usize = $value;
        let max: usize = $max;
        let id = <$id as $containers::DenseId>::try_new(value).expect("value is in range");

        assert_eq!(id.raw(), value as $word);
        assert_eq!(id.index(), value);
        assert_eq!(id.to_usize(), value);
        assert_eq!(<$id as $containers::DenseId>::to_usize(id), value);
        assert_eq!(<$id as $containers::DenseId>::to_index(id), value as $word);
        assert_eq!(<$id as $containers::IndexLike>::as_usize(id), value);
        assert_eq!(<$id as $containers::DenseId>::from_usize(value), id);
        assert_eq!(<$id>::new(value as $word), id);
        assert_eq!(<$id>::try_from(value as $word).unwrap(), id);
        assert!(<$id as $containers::DenseId>::bit_stealing());

        assert_eq!(
            <$id as $containers::IndexLike>::as_usize(<$id as $containers::IndexLike>::min()),
            0
        );
        assert_eq!(
            <$id as $containers::IndexLike>::as_usize(<$id as $containers::IndexLike>::max()),
            max
        );
        assert_eq!(<$id as $containers::DenseId>::try_new(max + 1), None);
        assert_eq!(
            <$id as $containers::IndexLike>::try_from_usize(max + 1),
            None
        );

        assert_eq!(core::mem::size_of::<$id>(), core::mem::size_of::<$word>());
        assert_eq!(core::mem::align_of::<$id>(), core::mem::align_of::<$word>());
        assert_eq!(
            core::mem::size_of::<<$id as $containers::Tagged>::Repr>(),
            core::mem::size_of::<$word>()
        );

        let mut repr: $word = <$id as $containers::Tagged>::into_repr(id);
        assert!(!<$id as $containers::Tagged>::tag(&repr));
        <$id as $containers::Tagged>::set_tag(&mut repr);
        assert!(<$id as $containers::Tagged>::tag(&repr));
        assert_eq!(<$id as $containers::Tagged>::from_repr(&repr), id);
        <$id as $containers::Tagged>::clear_tag(&mut repr);
        assert!(!<$id as $containers::Tagged>::tag(&repr));
        assert_eq!(<$id as $containers::Tagged>::from_repr(&repr), id);

        let mut opt = $containers::Opt::some(id);
        assert_eq!(opt.to_option(), Some(id));
        opt.set_none();
        assert!(opt.is_none());
        assert_eq!(opt.get_unchecked(), id);

        let pair = $containers::Pair { a: id, b: 17u16 };
        let mut pair_repr = <$containers::Pair<$id, u16> as $containers::Tagged>::into_repr(pair);
        assert!(!<$containers::Pair<$id, u16> as $containers::Tagged>::tag(
            &pair_repr
        ));
        <$containers::Pair<$id, u16> as $containers::Tagged>::set_tag(&mut pair_repr);
        assert!(<$containers::Pair<$id, u16> as $containers::Tagged>::tag(
            &pair_repr
        ));
        assert_eq!(
            <$containers::Pair<$id, u16> as $containers::Tagged>::from_repr(&pair_repr),
            pair
        );

        assert_eq!(format!("{id}"), format!("{}{value}", $prefix));
    }};
}

#[test]
fn all_widths_share_the_runtime_contract() {
    assert_id_contract!(plain, PlainId7, u8, 73, 0x7f, "p7_");
    assert_id_contract!(verified, VerifiedId7, u8, 73, 0x7f, "v7_");
    assert_id_contract!(plain, PlainId15, u16, 12_345, 0x7fff, "p15_");
    assert_id_contract!(verified, VerifiedId15, u16, 12_345, 0x7fff, "v15_");
    assert_id_contract!(plain, PlainId31, u32, 1_000_003, 0x7fff_ffff, "p31_");
    assert_id_contract!(verified, VerifiedId31, u32, 1_000_003, 0x7fff_ffff, "v31_");
    assert_id_contract!(
        plain,
        PlainId63,
        u64,
        4_294_967_311usize,
        0x7fff_ffff_ffff_ffffusize,
        "p63_"
    );
    assert_id_contract!(
        verified,
        VerifiedId63,
        u64,
        4_294_967_311usize,
        0x7fff_ffff_ffff_ffffusize,
        "v63_"
    );
}

#[test]
fn fallback_and_pair_representations_match_layout_and_behavior() {
    macro_rules! assert_fallback {
        ($word:ty, $value:expr) => {{
            assert_eq!(
                core::mem::size_of::<<$word as plain::Tagged>::Repr>(),
                core::mem::size_of::<<$word as verified::Tagged>::Repr>()
            );
            assert_eq!(
                core::mem::align_of::<<$word as plain::Tagged>::Repr>(),
                core::mem::align_of::<<$word as verified::Tagged>::Repr>()
            );

            let mut p = <$word as plain::Tagged>::into_repr($value);
            let mut v = <$word as verified::Tagged>::into_repr($value);
            <$word as plain::Tagged>::set_tag(&mut p);
            <$word as verified::Tagged>::set_tag(&mut v);
            assert_eq!(
                <$word as plain::Tagged>::tag(&p),
                <$word as verified::Tagged>::tag(&v)
            );
            assert_eq!(
                <$word as plain::Tagged>::from_repr(&p),
                <$word as verified::Tagged>::from_repr(&v)
            );
        }};
    }

    assert_fallback!(u8, 3u8);
    assert_fallback!(u16, 300u16);
    assert_fallback!(u32, 70_000u32);
    assert_fallback!(u64, 5_000_000_000u64);
    assert_fallback!(usize, 71usize);

    assert_eq!(
        core::mem::size_of::<<plain::Pair<PlainId31, u16> as plain::Tagged>::Repr>(),
        core::mem::size_of::<<verified::Pair<VerifiedId31, u16> as verified::Tagged>::Repr>()
    );
    assert_eq!(
        core::mem::align_of::<<plain::Pair<PlainId31, u16> as plain::Tagged>::Repr>(),
        core::mem::align_of::<<verified::Pair<VerifiedId31, u16> as verified::Tagged>::Repr>()
    );
}

macro_rules! assert_same_value_semantics {
    ($plain:ty, $verified:ty, $word:ty, $value:expr) => {{
        let value = $value as usize;
        let p = <$plain as plain::DenseId>::try_new(value).unwrap();
        let v = <$verified as verified::DenseId>::try_new(value).unwrap();
        assert_eq!(p.raw(), v.raw() as $word);
        assert_eq!(p.index(), v.index());

        let mut pr = <$plain as plain::Tagged>::into_repr(p);
        let mut vr = <$verified as verified::Tagged>::into_repr(v);
        <$plain as plain::Tagged>::set_tag(&mut pr);
        <$verified as verified::Tagged>::set_tag(&mut vr);
        assert_eq!(
            <$plain as plain::Tagged>::tag(&pr),
            <$verified as verified::Tagged>::tag(&vr)
        );
        assert_eq!(
            <$plain as plain::Tagged>::from_repr(&pr).index(),
            <$verified as verified::Tagged>::from_repr(&vr).index()
        );
    }};
}

proptest! {
    #[test]
    fn generated_ids_have_matching_value_and_tag_semantics(
        v7 in 0u8..=0x7f,
        v15 in 0u16..=0x7fff,
        v31 in 0u32..=0x7fff_ffff,
        v63 in 0u64..=0x7fff_ffff_ffff_ffff,
    ) {
        assert_same_value_semantics!(PlainId7, VerifiedId7, u8, v7);
        assert_same_value_semantics!(PlainId15, VerifiedId15, u16, v15);
        assert_same_value_semantics!(PlainId31, VerifiedId31, u32, v31);
        assert_same_value_semantics!(PlainId63, VerifiedId63, u64, v63);
    }
}
