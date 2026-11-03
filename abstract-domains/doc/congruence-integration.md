# Congruence channel integration

`congruence_refine.rs` implements `Refine<F = Facts<W>>` for every `W: Word`,
including u128, using the existing verified Congruence operations.

## Protocol and fact extraction

`Facts<W>` contains unsigned bounds `u` and congruence `c`; its concretization
is their intersection. `Channel` extends `Canonical`. Its exact meet produces
field-wise valid (`pre_wf`) records, and normalization preserves their
concretization while establishing `wf`. Use `meet_normalize` when a normalized
intersection is needed. `Facts::from_parts(u, c)` directly constructs that
normalized intersection and returns `BotOr::Bot` when it is empty.

Congruence's `to_channel` exports the interval from its residue to its verified
`max_member`, together with the congruence itself, through `Facts::from_parts`.
The exported record denotes exactly the source class; the trait contract
proves export soundness and well-formedness.

The inherent `Congruence::refines(&other) -> bool` decides containment and
backs `Domain::leq`. It is distinct from `Refine::refine(&facts)`, which
returns `BotOr<Congruence<W>>` and participates in reduction.

## Grid-aware refinement

`refine` first meets the source congruence with `f.congruence()`. Incompatible
grids return bottom. It then normalizes the merged grid against `f.interval()`
using `Facts::from_parts`: lower bounds round up, upper bounds round down,
and an empty intersection returns bottom. A single remaining value becomes a
constant congruence. A final meet with the merged grid establishes no growth
using the public contracts, without relying on normalization internals.

For example, `[8, 9]` intersected with `4Z+3` returns bottom, while `[5, 9]`
leaves only the constant `7`. The interval `[3, 10]` snaps to `[3, 7]`.
A Congruence leaf cannot retain arbitrary interval bounds: the normalized
channel carries those bounds to interval or Facts components during product
reduction. The leaf retains the merged class or learns a constant.

The refinement contract proves preservation of every common concrete value,
no growth, and well-formedness. `Product::reduce` preserves concretization
for every fuel and nesting depth. Positive fuel propagates normalized facts;
zero fuel leaves the original product unchanged, even if its components
jointly denote an empty set. A product is not itself canonical and must not
be used as a canonical e-class record.

## Regression coverage

`tests/congruence_refine.rs` checks all u8 constructor inputs for exported
hulls, congruence retention, and concrete membership. It exhausts every u8
interval for representative grids against enumerated concrete members,
checking bottom detection, singleton feedback, no growth, and snapped product
bounds. Additional tests cover incoming grid compatibility, two Congruence
leaves, nested products, reduction fuel, existing componentwise arithmetic,
and u128 boundary cases. Facts membership checks include both fields.

## Remaining arithmetic integration

A4 remains separate: `facts_ops.rs` add/sub/neg still compute only the interval
transfer. The public `Facts::congruence` and `Facts::from_parts` APIs are now
available for combining those results with verified Congruence transfers.
Normalization bottom must be handled according to the transfer return
contracts. Multiplication, division, comparisons, and other operations require
separate transfer support before claiming additional congruence precision.
