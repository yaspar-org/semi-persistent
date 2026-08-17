<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# The Dense-Span Multimap: a Build-Once Index, Refined to a Filter

This chapter describes `containers-verus/src/dense_span_map.rs`: what
`DenseSpanMap<V>` stores, the three properties its proofs establish, and which
proof-structure decisions the module made and why. It is not a status page:
`cargo verus verify` reports the current per-module tally, and CI asserts the
trust-surface counts.

Every container before this one is semi-persistent. This one is not, and that is
the first design decision to justify.

## 1. What it is, and why it has no `mark`/`restore`

`DenseSpanMap<V>` is a multimap from a dense key `k < num_keys` to a sequence of
values, stored in two flat vectors:

```rust
pool:  Vec<V>       // every value, grouped by key
spans: Vec<Span>    // spans[k] = { off, len }: key k occupies pool[off .. off+len]
```

It is built in one call from a `(key, value)` stream and is read-only afterwards.
The construction is the standard two-pass counting sort: pass 1 counts each key's
population and prefix-sums the counts into offsets, pass 2 walks the stream again
and writes each value at its key's running cursor.

It replaces the e-graph's per-round index families
(`egraph/doc/design/06-index.md`, `20-index-selectivity-and-delta-suffixes.md`
sections R2/R3), which are rebuilt from scratch each round. A rebuilt-per-round
structure has no state to roll back to, so `mark`/`restore` would add a frame
stack, a fork history, and a capture protocol that no caller ever exercises. The
container therefore carries none of them, and the semi-persistence proof
obligations that occupy chapters 03 through 08 do not arise here.

That is a scope decision, not a claim that semi-persistence would be slow.
Revisit it only if a workload is measured to restore an index family rather than
rebuild it.

## 2. The model

The ghost model is one value sequence per key:

```rust
spec fn view(&self) -> Seq<Seq<V>>
```

and the container keeps a ghost copy of the stream it was built from, so the
refinement remains stateable after `build` returns.

The specification-side vocabulary is five named spec functions: `is_key(k)`,
`is_below(k)`, `snd()`, and the two they compose into,

```rust
key_slice(stream, k) == stream.filter(is_key(k)).map_values(snd())
count_below(stream, k) == stream.filter(is_below(k)).len()
```

**Filter predicates are named spec functions, never inline closures.** Two
syntactically identical closures are two different spec terms. An invariant
carrying `filter(|p| p.0 == k)` and a lemma call site writing the same closure do
not match, and vstd's filter lemmas then apply to a term the invariant does not
hold. Naming them makes the terms identical by construction. This is the reason
`lemma_filter_take_len` can be handed the same predicate the pass-2 invariant
carries.

## 3. The three properties

**No wrong-slice reads.** `wf()` states that the spans tile the pool exactly:
the first span starts at 0, each span starts where the previous one ends, and the
last ends at `pool.len()`. Pairwise disjointness is not the invariant; it is the
derived `lemma_spans_disjoint`, proved from the tiling. `get(k)` returns a slice
equal to `view()[k]`.

**No invented and no dropped values.** `refines()` pins the pool against the
build stream: for every key, `view()[k] == key_slice(stream, k)`. This is a
sequence equality, not a multiset or length equality, so it constrains order as
well as content. A pass 2 that placed a key's values in the wrong relative order
would satisfy a count-based specification and fail this one. `build` establishes
it for every `k < num_keys`.

**Sortedness transfer.** `lemma_filter_sorted` proves that filtering preserves
sortedness under an arbitrary relation, over a bare `Seq<A>`;
`lemma_view_sorted` applies it to conclude that if the build stream is sorted by
some measure, every per-key slice is sorted by that measure. A caller that sorts
the stream once does not re-sort per key, and does not have to assume the
grouping preserved the order.

The composite-key helper flattens a two-dimensional key `(a, b)` with `b < bcount`
to `a * bcount + b`. `lemma_composite_key_injective` proves the flattening
injective on that domain, which is what makes a `DenseSpanMap` keyed by it
conflate-free. The exec form returns `None` both for `b >= bcount` and for a
product that leaves `usize`.

## 4. Proof structure

**Structural `wf()`, separate `refines()`.** `wf()` mentions only the span
tiling; the refinement to the stream is a second predicate. `get` needs the
tiling and nothing else, so it never loads the refinement's quantifier over
filtered sequences. This follows playbook section 4: an over-broad `requires`
drags unused quantifiers into every proof that mentions it.

**Single-variable disjointness clauses.** The tiling is four clauses, each
quantified over one variable. The idiomatic pairwise phrasing
(`forall|i, j| ... i != j ==> ranges disjoint`) is the shape playbook section 9
records at 223,553 ms in `list::splice_raw`, because a trigger set with two
disjoint bound-variable groups instantiates over every pair of matching terms.
The pairwise form was not tried here: the single-variable form was chosen from
that recorded measurement, so this module contributes no new data point on the
cost of the alternative.

**Bare-sequence lemmas.** Every lemma in the module takes plain `Seq` arguments
rather than `self` or the build loop's locals: `lemma_place_step` (the pass-2
placement step), `lemma_spans_disjoint`, `lemma_offsets_monotone`,
`lemma_filter_sorted`, and the `count_below` arithmetic. Same reason: proof cost
scales with what the solver can see, and these goals are cheap when nothing else
is in scope.

**Overflow reduces to one identity.** Every `usize` obligation in `build`
discharges through `offsets[k] == count_below(stream, k)`. A count of a
subsequence of the stream is bounded by `stream.len()`, which is a `usize`
because the stream is a slice, so the prefix-sum accumulator cannot overflow.
The step lemma `count_below(s, k+1) == count_below(s, k) + count_key(s, k)` is
what carries the accumulator from one key to the next.

The module verifies in 10.2 s with no `#[verifier::rlimit]` and no
`spinoff_prover`. Per playbook section 5, needing neither is the evidence that
the structure, not the budget, is doing the work.

### Two assumptions from the design sketch that the pinned vstd did not support

**`Vec::set` does not exist** in vstd `0.0.0-2026-08-02-0125`. Pass 2 writes
through `pool[pos] = val`, which routes to `vec_index_mut`, whose postcondition
is `final(vec)@ == old(vec)@.update(pos, val)`. That is the form
`lemma_place_step` is stated against.

**A custom filter-subset lemma was unnecessary.** The push case of
`lemma_filter_sorted` needs "every element of a filtered sequence came from the
sequence". vstd ships this as `Seq::lemma_filter_contains_rev`, so the planned
helper was dropped.

**Slices are carved with `split_at`, not `&pool[a..b]`.** `split_at` carries a
direct `subrange` postcondition. Range indexing on a `Vec` reaches vstd's
`Index` specification, whose postcondition is existential over `call_ensures`
(`std_specs/vec.rs`), and going through `as_slice()` first still lands on a
`call_ensures`-shaped obligation (`std_specs/slice.rs`). The range-index route
was not attempted, so whether it discharges is unmeasured; `split_at` was chosen
because its postcondition is the equality the proof needs.

## 5. Trust classification

The module adds **no `external_body` markers**: the default-build count is
unchanged at 27, and the `literal-types` count at 5. Nothing in it is trusted
beyond what the rest of the crate already trusts, which for this module is
vstd's `Vec` and slice specifications (trust ledger group A) and the `Ghost`
erasure. There are no `admit`s or `assume`s.

The public surface is total: no public exec function carries a `requires`
clause, so the partial-API allowlist does not grow. `build` is `pub(crate)`;
callers use `try_build`, which returns `IndexOutOfBounds` for a stream carrying
a key at or beyond `num_keys`. `get` and `key_len` are total with a documented
panic: two O(1) bound branches that are exactly what carving the slice needs.
For a `wf()` map neither branch is reachable, which is why the checks cost a
comparison rather than an O(num_keys) revalidation of the tiling.

## 6. What the runtime tests add

Verus erases `requires` and `ensures` under `cargo test`, so
`containers-conformance/tests/dense_span_map_differential.rs` exercises the
executable code the proofs never run. The reference model is a
`HashMap<usize, Vec<V>>` filled by walking the stream and pushing each value onto
its key's vector: no pool, no spans, no prefix sums, no cursors, so it cannot
reproduce an off-by-one in the counting sort because it does not count.

Nineteen tests cover randomized and key-skewed streams, keys with no entries,
duplicate values, interleaved keys, `u64` values, refusal of out-of-range keys,
and the composite-key helper's injectivity and two-dimensional round trip. One
check is worth naming: concatenating every key's slice in key order must equal
the stream stably sorted by key. That observes the tiling from outside the
proof, because an overlap duplicates a value and a gap loses one.

## 7. The recycled build path

A dense build writes the whole key space however few values its stream carries:
`num_keys` counts, `num_keys` offsets, `num_keys` cursors and `num_keys` spans.
`comparison/span-table-sparsity.md` measures what that costs the e-graph at
S = 1e6: 40.6 ms per round writing 77 MB of arrays for a 3.2 MB pool at 2 M keys,
and a delta install of 19.57 ms to make 23 values addressable. Section 4 of
`16-layered-span-map.md` carries the retraction of the cost claim that omitted
this term.

`build_in` is the second build path, over a caller-owned `SpanArena` that
survives the map built into it. The arena holds the span table, the occupancy
list and a generation stamp. A build bumps the generation and writes only the
keys its stream carries; a key left by an earlier build carries an older stamp
and reads as empty. `recycle` hands the arena back. Work is proportional to the
stream and the keys it occupies, not to the key space.

**The measured numbers are the prototype's, not this container's.** The
prototype in `egraph/src/span_proto.rs` measured the index build at 65.4 to
36.5 ms per round and the delta install at 19.57 to 0.010 ms, corpus
byte-identical. Whether the verified version reproduces them is a measurement
nobody has taken: it is not yet wired into the e-graph, and `replace_delta` still
builds its delta generation with the dense path, so the 19.6 ms install stands
until that changes.

**There is one build, not two.** `build` delegates to `build_in` with a fresh
arena. Keeping a separate dense path would have meant listing every key in the
occupancy list, including empty ones, and that breaks the argument in the next
paragraph.

**`wf()` moves the tiling onto the occupancy order.** It is the same
`spans_tile` predicate applied to `permute(spans, occ)`, the table read in
occupancy order, so `lemma_spans_monotone` and `lemma_spans_disjoint` apply
verbatim and no pairwise-quantified clause enters `wf()`. Injectivity of the
occupancy list is NOT a `wf()` clause: it is derived by `lemma_occ_injective`
from the tiling plus "an occupied span is non-empty", both single-variable,
because a repeated span would have to satisfy `S.off + S.len <= S.off`. That
derivation is available only because a listed key always carries at least one
value, which is why the dense path had to go.

`refines()` is unchanged. What changes is the order of keys within the pool:
extents are assigned in first-occurrence order rather than key order, which a
per-key filter does not constrain.

### Stamp width and exhaustion

The stamp is a `u64` and stamp 0 is reserved for a never-written entry, so a live
generation is always positive. On exhaustion the build re-stamps the whole table
to 0 and resets the generation to 1, O(num_keys) once every 2^64 builds. The
branch is written and proved rather than argued away, because "unreachable in
practice" is not a postcondition. It is also not runtime-tested: reaching it
takes 2^64 builds, so the conformance suite cannot drive it, and that is a
consequence of choosing `u64` over the prototype's `u32`.

A `{off, len, stamp}` triple at `usize`/`usize`/`u64` is 24 bytes against the
prototype's 12. The arena is resident where the dense build's arrays were
transient, so the resident steady state rises; section 7 of the sparsity document
asks for both peak and steady state to be measured on the largest corpus program
before the width is settled. That measurement has not been taken.

### What the proof structure cost

The first attempt put all three passes in one function and did not converge. The
passes are now three contracted functions verified in isolation, `count_pass`,
`extent_pass` and `place_pass`, composed by `build_in`.

Two diagnoses are worth recording. First, `permute` is a NAMED spec function and
is `#[verifier::opaque]`, with `lemma_permute_index` and `lemma_permute_len` as
the only way in. Written as an inline `map_values` closure it was re-elaborated
at every mention, including once per iteration inside a loop invariant, and
`place_pass` exceeded the solver budget; naming it and making it opaque removed
that. Second, `build_in` then failed at rlimit 30, 60 and 200 alike. Per playbook
section 1 a budget that does not help means a matching loop rather than slow
search, so the fix was to move the tiling conclusion into `place_pass`, where it
is proved against the loop invariant that already carries the pieces. `build_in`
now converges on the default budget with `spinoff_prover` and no `rlimit`
attribute.

Verus loops see only their invariant, not the enclosing function's
preconditions. Several obligations that looked like proof failures were facts
stated in a `requires` and never restated in the loop.


---
[← Table of Contents](00-table-of-contents.md)
