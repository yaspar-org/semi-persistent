# Congruence channel integration

`congruence_refine.rs` implements `Refine<F = Facts<W>>` for every `W: Word`,
including u128. It uses the existing verified Congruence implementation;
no Word migration or Congruence arithmetic changes are needed.

## Current protocol

`Channel` extends `Canonical`. Its exact meet produces field-wise valid
(`pre_wf`) records, and normalization preserves their concretization while
establishing `wf`. `Refine::to_channel` exports implied facts;
`Refine::refine` preserves the intersection with those facts and never grows
the component. `Product::reduce` already proves preservation for every fuel
and nesting depth. A product is not itself canonical.

The inherent `Congruence::refines(&other) -> bool` decides containment and
backs `Domain::leq`. It is distinct from `Refine::refine(&facts)`, which
returns `BotOr<Congruence<W>>` and participates in reduction.

The current record has only `u`. Congruence exports the interval from its
residue to its verified `max_member`. Refinement intersects that hull with
the record's interval: disjoint bounds yield bottom, singleton overlap uses
the existing exact Congruence meet with a constant, and other overlaps keep
the original congruence. All returned leaves retain their canonical form.
The two trait contracts prove export soundness, intersection preservation,
and no growth. These suffice for the existing product preservation theorem.

This is useful independently: products can propagate congruence bounds,
learn constants, detect bounds conflicts, and use the existing componentwise
unsigned add/sub/neg transfers. Tests exhaust all u8 constructor inputs for
exported hulls, check sampled refinements and reductions against every u8
value, exercise wrapping transfers, and cover high u128 values.

## Dependency on the congruence field

Grid clipping, `Facts.c`, `Facts::normalize`, and canonicality are owned by
Yuning and are unchanged here. General interval/grid emptiness is not detected
by this implementation. For example, `[8, 9]` and `4Z+3` have overlapping
hulls but an empty intersection; reduction through unsigned bounds alone
need not report bottom. Products must not be used as canonical e-class records.

Congruence-related transfers in `facts_ops.rs` require these public interfaces:

- A spec accessor and executable accessor for `c`, with well-formedness and
  the implication from record membership to congruence membership.
- A way to build a field-wise valid record from independently computed `u`
  and `c`, then normalize it to `BotOr<Facts<W>>` with exact preservation.
- An export constructor that embeds a congruence with sound unsigned bounds
  and returns a normalized record.

After those interfaces land, export `c` in `to_channel` and meet the incoming
`c` in `refine`. Extend the existing add/sub/neg fact transfers with the
verified Congruence operations and normalize the combined fields. Handle
normalization bottom according to the existing transfer return contracts;
do not assume independently sound fields form a nonempty record. Multiplication,
division, and comparisons need separately verified Congruence transfer support
before claiming additional precision; Congruence currently exposes unsigned
`Arith`, not those transfer traits.

Then add interval/grid conflict and precision regressions, including
`[8, 9]` with `4Z+3`, and rerun full pinned verification and runtime checks.
No temporary congruence encoding in the unsigned field is needed.
