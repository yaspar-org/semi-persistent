// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance criteria: the multiplicity width is a configuration parameter, and every
//! boundary it introduces is checked rather than truncated.
//!
//! `EGraphConfig::M` selects how an AC child's occurrence count is stored, on an axis
//! independent of the id width. Three things have to hold for that to be more than a
//! declaration:
//!
//! 1. a config with a *different* `M` actually instantiates the engine — nothing on the
//!    generic paths may hardcode `Multiplicity` (this file drives `ConfigM16` through
//!    build, canonicalize, rebuild, merge and extract);
//! 2. the width chosen is the width stored, and choosing it is not a hidden cost;
//! 3. every conversion from the `u64` surface width, and every summation, either
//!    succeeds exactly or fails loudly. The narrow config is what makes this testable:
//!    `u16` boundaries are reachable with a monomial a test can construct, where the
//!    equivalent `u32` case needs four billion children.
//!
//! The anti-unification search is parameterized on the same `M` (its cached `ActionPair`
//! counts and its structural-composition arithmetic), so the last two tests carry the
//! criteria across that boundary: AU instantiates and runs at the narrow width, and the
//! width bounds a single child's count without bounding what the search can *total*.

use semi_persistent_egraph::EGraphM16;
use semi_persistent_egraph::au::actions::ActionPair;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::terms::TermOp;
use semi_persistent_egraph::au::{AuIds31, AuIds64};
use semi_persistent_egraph::config::EGraphConfig;
use semi_persistent_egraph::extract::extract_best;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::multiplicity::{
    Multiplicity, Multiplicity16, Multiplicity64, MultiplicityLike,
};
use semi_persistent_egraph::node_store::MSetChild;
use semi_persistent_egraph::nodes::{Config64, ConfigM16, DefaultConfig};
use semi_persistent_egraph::registry::{Clamp, OpKind};

type EgM16 = EGraphM16<NiraLitVal, false, false>;

/// Each width stores in exactly its backing primitive — the parameter selects a
/// representation, it does not wrap one in a discriminant or an `Option`.
#[test]
fn each_width_is_its_backing_primitive() {
    assert_eq!(core::mem::size_of::<Multiplicity16>(), 2);
    assert_eq!(core::mem::size_of::<Multiplicity>(), 4);
    assert_eq!(core::mem::size_of::<Multiplicity64>(), 8);
}

/// An AC child pairs an id with a count, and the id's alignment sets the pair's stride —
/// so at 63-bit ids the pair is 16 bytes at *every* multiplicity width, and a 64-bit
/// multiplicity is free. That is why `Config64` takes the widest count available: leaving
/// it at 32 bits would keep a reachable ceiling in place for no storage saving, on a
/// config whose whole purpose is to remove capacity caps.
///
/// The 31-bit side records the counterpart fact: 16 and 32 bits pad to the same 8 bytes
/// there, so `ConfigM16` is a low-ceiling guard rather than a space optimization, and this
/// test is what would catch a claim otherwise.
#[test]
fn multiplicity_width_is_free_at_the_wide_id_width() {
    type E31 = <DefaultConfig as EGraphConfig>::G;
    type E63 = <Config64 as EGraphConfig>::G;
    let wide16 = core::mem::size_of::<MSetChild<E63, Multiplicity16>>();
    let wide64 = core::mem::size_of::<MSetChild<E63, Multiplicity64>>();
    assert_eq!(
        wide16, wide64,
        "at 8-byte ids every multiplicity width pads to the same stride, so the widest \
         count is free: 16-bit pair = {wide16}, 64-bit pair = {wide64}"
    );
    assert_eq!(
        core::mem::size_of::<<Config64 as EGraphConfig>::C>(),
        wide64,
        "Config64 must take the free width"
    );

    assert_eq!(
        core::mem::size_of::<MSetChild<E31, Multiplicity16>>(),
        core::mem::size_of::<MSetChild<E31, Multiplicity>>(),
        "at 4-byte ids a 16-bit count pads to the same stride as a 32-bit one"
    );
}

/// The multiplicity width does not follow the id width: `ConfigM16` pairs 4-byte ids with
/// a 2-byte count and `DefaultConfig` pairs the same ids with a 4-byte one, so the two
/// axes are demonstrably separable at a fixed `Index`. A change that quietly tied `M` to
/// `Index` — deriving one from the other, or reintroducing a hardcoded `Multiplicity` —
/// would collapse that pair.
#[test]
fn multiplicity_width_is_independent_of_id_width() {
    assert_eq!(
        core::mem::size_of::<<DefaultConfig as EGraphConfig>::G>(),
        4
    );
    assert_eq!(core::mem::size_of::<<Config64 as EGraphConfig>::G>(), 8);
    assert_eq!(core::mem::size_of::<<ConfigM16 as EGraphConfig>::G>(), 4);

    // Same id width, two different multiplicity widths — the axes are independent.
    assert_eq!(
        core::mem::size_of::<<DefaultConfig as EGraphConfig>::M>(),
        4
    );
    assert_eq!(core::mem::size_of::<<ConfigM16 as EGraphConfig>::M>(), 2);
    // And `Config64` differs from `DefaultConfig` on *both* axes at once: 8-byte ids with
    // an 8-byte count, chosen because that count is free at this id width (see
    // `multiplicity_width_is_free_at_the_wide_id_width`).
    assert_eq!(core::mem::size_of::<<Config64 as EGraphConfig>::M>(), 8);
}

/// Register a plain AC (`OpKind::MSet`, no clamp) op named `f` over one sort, plus `n`
/// distinct constants. Returns `(f, sort, constant ids)`.
fn ac_setup(
    eg: &mut EgM16,
    n: usize,
) -> (
    semi_persistent_egraph::OpId,
    Vec<semi_persistent_egraph::ENodeId>,
) {
    let s = eg.intern_sort("E");
    let f = eg.register_kind(
        "f",
        s,
        OpKind::MSet {
            arg_sort: s,
            clamp: Clamp::None,
            identity: None,
            cancellative: false,
        },
    );
    let mut ids = Vec::with_capacity(n);
    for i in 0..n {
        let op = eg.register_op0(&format!("c{i}"), s);
        ids.push(eg.add(op, &[]));
    }
    (f, ids)
}

/// The whole engine runs on the narrow config: build an AC node with a repeated child,
/// which exercises the coalescing increment, then rebuild and extract. Nothing on this
/// path may assume a 32-bit multiplicity.
#[test]
fn engine_runs_end_to_end_on_the_narrow_config() {
    let mut eg = EgM16::from_model(&NiraModel);
    let (f, c) = ac_setup(&mut eg, 2);
    // f(c0, c0, c1) canonicalizes to the monomial {c0:2, c1:1}.
    let node = eg.add(f, &[c[0], c[0], c[1]]);
    eg.rebuild();
    let term = extract_best(&eg, node).expect("the AC node must extract");
    let s = term.to_string();
    assert_eq!(
        s.matches("c0").count(),
        2,
        "multiplicity 2 must survive the narrow width and re-expand to two copies: {s}"
    );
    assert_eq!(s.matches("c1").count(), 1, "{s}");
}

/// Merging two classes recanonicalizes the monomials that mention them, coalescing the
/// merged summands — the rebuild-path increment, distinct from the build-path one above.
#[test]
fn merge_coalesces_multiplicities_on_the_narrow_config() {
    let mut eg = EgM16::from_model(&NiraModel);
    let (f, c) = ac_setup(&mut eg, 2);
    let node = eg.add(f, &[c[0], c[1]]);
    eg.rebuild();
    // c0 ≡ c1 turns {c0:1, c1:1} into {c0:2}.
    eg.merge(c[0], c[1]);
    eg.rebuild();
    let term = extract_best(&eg, node).expect("the AC node must extract after the merge");
    let s = term.to_string();
    let total = s.matches("c0").count() + s.matches("c1").count();
    assert_eq!(
        total, 2,
        "the two merged summands must coalesce to one summand of multiplicity 2: {s}"
    );
}

/// A count near the width's ceiling is stored exactly, not truncated. 65535 children is
/// the largest monomial a `u16` multiplicity can hold; the value one below it is stored
/// and read back unchanged.
#[test]
fn count_just_below_the_ceiling_round_trips() {
    let mut eg = EgM16::from_model(&NiraModel);
    let (f, c) = ac_setup(&mut eg, 1);
    let n = usize::from(u16::MAX) - 1;
    let children = vec![c[0]; n];
    let node = eg.add(f, &children);
    eg.rebuild();
    let mut seen = None;
    eg.for_each_child(node, |g, mult| {
        assert_eq!(g, eg.find_const(c[0]));
        seen = Some(mult);
    });
    assert_eq!(
        seen.map(|m| m.to_u64()),
        Some(n as u64),
        "a multiplicity one below the width's maximum must be stored exactly"
    );
}

/// Past the ceiling the engine panics with a diagnosable message instead of wrapping.
///
/// This is the case that used to be silent: `u16::MAX + 1` copies wrapped to a stored
/// multiplicity of **0**, which the canonical form declares impossible — and the
/// nilpotent/idempotent clamps drop zero entries, so the summand would have vanished and
/// the e-graph would assert an equality that does not hold. A panic naming the configured
/// width is the correct outcome: the configuration is too narrow for this e-graph, and
/// there is no error channel on the build path to report it through.
#[test]
#[should_panic(expected = "multiplicity width is too narrow")]
fn count_past_the_ceiling_panics_rather_than_wrapping() {
    let mut eg = EgM16::from_model(&NiraModel);
    let (f, c) = ac_setup(&mut eg, 1);
    let children = vec![c[0]; usize::from(u16::MAX) + 1];
    let _ = eg.add(f, &children);
}

/// The surface width is `u64` and narrowing from it is fallible in exactly the places it
/// has to be. These are the values that used to alias under an unchecked `as`: `2^32`
/// truncated to 0 (a multiplicity the representation forbids) and `2^32 + 1` to 1.
#[test]
fn surface_narrowing_is_checked_at_every_width() {
    assert_eq!(Multiplicity::try_from_u64(1 << 32), None);
    assert_eq!(Multiplicity::try_from_u64((1 << 32) + 1), None);
    assert_eq!(Multiplicity16::try_from_u64(1 << 16), None);
    assert_eq!(Multiplicity16::try_from_u64((1 << 16) + 1), None);
    // Widening is total, so a stored count always compares exactly against a surface
    // literal — which is why the match paths never need to narrow at all.
    for m in [
        Multiplicity16::ZERO,
        Multiplicity16::ONE,
        Multiplicity16::MAX,
    ] {
        assert_eq!(Multiplicity16::try_from_u64(m.to_u64()), Some(m));
    }
    assert_eq!(
        Multiplicity64::try_from_u64(u64::MAX),
        Some(Multiplicity64::MAX)
    );
}

/// The AU search's cached child-pair carries `M`, and doing so is free at every shipped
/// config — the same padding fact `multiplicity_width_is_free_at_the_wide_id_width`
/// records for AC children, restated for the AU-side stored pair.
///
/// This is the test that keeps the *justification* honest, not just the types: the reason
/// `ActionPair::count` is `Cfg::M` rather than a hardcoded `u32` is that a fixed `u32`
/// narrows a `Multiplicity64` count and so drops representable members, **not** that it
/// wastes space at `Multiplicity16`. It does not: 16 and 32 bits pad to the same pair.
#[test]
fn au_action_pair_costs_nothing_to_parameterize() {
    let narrow = core::mem::size_of::<ActionPair<AuIds31, Multiplicity16>>();
    let default = core::mem::size_of::<ActionPair<AuIds31, Multiplicity>>();
    assert_eq!(
        narrow, default,
        "at 4-byte class ids a 2-byte count pads to the same pair as a 4-byte one: \
         16-bit pair = {narrow}, 32-bit pair = {default}"
    );
    assert_eq!(
        core::mem::size_of::<ActionPair<AuIds64, Multiplicity16>>(),
        core::mem::size_of::<ActionPair<AuIds64, Multiplicity64>>(),
        "at 8-byte class ids every multiplicity width pads to the same pair"
    );
}

/// Build `f(c0^n, c1^n)` and `f(c0^n, c2^n)` on the narrow config, with `2n` past the
/// width's ceiling, and anti-unify them.
///
/// Two criteria at once.
///
/// *The engine instantiates.* AU generates, caches and composes actions whose counts are
/// `Cfg::M`; a hardcoded `Multiplicity` anywhere on those paths stops this compiling, and
/// exact-vs-UCT agreement says the two independent consumers of those counts (recursive
/// composition and the MCGS statistics arena) read them the same way.
///
/// *The width bounds a child, not a total.* `2n > u16::MAX` while each individual count is
/// `n < u16::MAX`, so a search that summed multiplicities at `Cfg::M` would either drop
/// this generalization or — the old failure — wrap the total and report a term with `2n mod
/// 2^16` children as a generalization of one with `2n`. The production AC path reads
/// monomials at the `u64` surface width and narrows once, in the transport feasibility
/// gate, so the correct total survives: the assertion is on the exact child count.
#[test]
fn au_totals_are_not_capped_by_the_narrow_multiplicity_width() {
    let mut eg = EgM16::from_model(&NiraModel);
    let (f, c) = ac_setup(&mut eg, 3);

    let n = 40_000usize;
    assert!(n < usize::from(u16::MAX), "each count must fit the width");
    assert!(2 * n > usize::from(u16::MAX), "the total must not");

    let mut left = vec![c[0]; n];
    left.extend(vec![c[1]; n]);
    let mut right = vec![c[0]; n];
    right.extend(vec![c[2]; n]);
    let l = eg.add(f, &left);
    let r = eg.add(f, &right);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).expect("snapshot on the narrow config");
    let exact = anti_unify(
        &snap,
        l,
        r,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .expect("exact AU on the narrow config");
    let uct = anti_unify(
        &snap,
        l,
        r,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 300,
            ..Default::default()
        },
    )
    .expect("UCT AU on the narrow config");

    assert_eq!(exact.completion, Completion::Exact);
    assert!(
        matches!(exact.root_op(), TermOp::EGraph(op) if *op == f),
        "the generalization must keep the AC operator, not degrade to a variable"
    );
    assert_eq!(
        exact.root_children().len(),
        2 * n,
        "the anti-unifier must have every one of the {} children both inputs have; a total \
         summed at the 16-bit width would wrap to {}",
        2 * n,
        (2 * n) % (usize::from(u16::MAX) + 1)
    );
    assert_eq!(
        uct.root_children().len(),
        exact.root_children().len(),
        "UCT must reach the same total as the exact oracle"
    );
    assert_eq!(uct.size, exact.size, "UCT must match the exact oracle");
}
