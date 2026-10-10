# Proof status and plan for the encoders

> **Moved on 2026-10-06.** This was `pb-verus/doc/proof-plan.md`. The crate is gone: its
> encoders are `egraph/src/extraction/{cnf,totalizer}.rs`, without the Verus `spec fn`s
> and the one verified lemma (`lemma_weighted_sum_add`) that `cnf.rs` carried, because the
> user chose to verify the encoders' actual properties in a Verus crate later rather than
> keep a specification layer that the exec code did not use
> (`doc/goal-one-crate.md`, decision 3). The plan below is what that work starts from.

This document records which claims about the encoders in this crate are
machine-checked, which are established by exhaustive testing, and what porting
the remainder into `verus!` requires. It is not a design document: the encoding
itself is specified in the module documentation of `src/gte.rs`.

## The property a consumer depends on

An optimizing extractor uses the encoder in one direction only. It asserts the
negation of an emitted indicator to bound a weighted sum, so the claim it rests
on is the contrapositive of the forward direction:

```text
a.cnf(emitted)  /\  !a.lit(indicator_for(t))  ==>  weighted_sum(a, ws) < t
```

The converse is deliberately false. Only the forward clause family is emitted,
so an indicator may be true under a model whose sum is below its threshold.
`src/gte.rs` states why, and `attained_sum` exists because of it: a caller
recovers the sum from the input literals rather than counting indicators.

## Verified now

| item | location | status |
| --- | --- | --- |
| `Lit`, complement, constant discrimination | `src/cnf.rs` | **verified** |
| `Assign::lit`, `clause`, `cnf` | `src/cnf.rs` | **verified** |
| `weighted_sum` specification | `src/cnf.rs` | **verified** |
| `lemma_weighted_sum_add`: splitting the input splits the sum | `src/cnf.rs` | **proved** |

`cargo verus verify` reports 6 verified, 0 errors. The lemma is the induction
step the merge proof needs: `merge` combines two subtrees, and its obligation
reduces to a claim about `weighted_sum` over a concatenation.

## Established by testing, not proof

The bound property above, for the GTE encoder. `tests/exhaustive.rs` enumerates
every assignment over the input literals and every extension to the auxiliary
variables the encoder allocated, then checks two things per instance:

- whenever a satisfying extension leaves the indicator for `t` false, the
  directly computed sum is below `t`;
- every input assignment has at least one satisfying extension, so the encoding
  excludes no selection.

The second check is the one that catches an over-constrained encoding, which
would make a reported optimum an artifact of the encoding rather than a property
of the problem. Instance sizes are capped at 5 inputs and 18 auxiliary variables
so the enumeration terminates.

## Next: porting the exec code into `verus!`

Three obligations, in dependency order.

**A leaf encodes its own sum.** For `weighted = [(l, w)]` the returned map is
`{0 -> True, w -> l}`. The obligation is that under every assignment,
`a.lit(map[s]) ==> weighted_sum(a, weighted) >= s` fails only in the intended
direction, and that `weighted_sum(a, weighted) >= s ==> a.lit(map[s])` holds for
both entries. Both follow by case analysis on `a.lit(l)`.

**`merge` preserves the property.** Given that `left` and `right` satisfy the
forward property for their own inputs, the emitted clauses give it for the
concatenation. The argument: let `S` be the sum over the concatenated inputs and
`S_L`, `S_R` its parts, so `S = S_L + S_R` by `lemma_weighted_sum_add`. The
induction hypothesis forces `left`'s indicator at `S_L` and `right`'s at `S_R`
true, the forward clause for that pair forces the output at `S`, and the
monotonicity chain carries it down to every achievable threshold at or below `S`.
The monotonicity step is why those clauses are not optional, and it is the part
of the argument most likely to need explicit sequence lemmas about the sorted
achievable set.

**`encode_tree` composes.** Structural induction on the balanced split, with the
concatenation identity supplying the arithmetic.

Two implementation changes the port needs. `BTreeMap` has no vstd model, so the
achievable-sum map becomes a sorted `Vec<(u64, Lit)>` with an explicit sortedness
invariant. And `ClauseSink` becomes a specified trait: `clause` needs a
postcondition relating the sink's accumulated clause sequence before and after
the call, since the theorem quantifies over the emitted set.

## Not planned

Proving the backward direction. The encoder does not emit the clauses that would
make it true, and no consumer in this repository reads an indicator as a fact.
Revisit only if a caller is added that needs `a.lit(indicator_for(t)) ==>
weighted_sum(a, ws) >= t`, which would require emitting the backward family and
roughly doubling the clause count.
