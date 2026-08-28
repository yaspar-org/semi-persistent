# Algebraic properties of AC operators: representation, canonization, and the per-op pool

The monomial order referenced throughout is defined in `ac-completion-spec.md` §3.1
(degree-lex: total size, then lexicographic from the largest class id down, Kapur's
deglex). This chapter is the durable record of how multiple AC/ACI symbols and their
semantic properties (identity, idempotent, nilpotent, cancelative, inverse) are
represented and canonized: the three independent axes, the canonization-not-completion
doctrine, the per-op min-monomial pool, and the surface property tags. Companions: the
completion algorithm chapter (`ac-congruence-completeness.md`) and the engine-level spec
with the Kapur-correspondence table (`ac-completion-spec.md`).

## Reference

The authoritative paper is the 2023 journal extension, not the FSCD 2021 conference version:

- Deepak Kapur, **"Modularity and Combination of Associative Commutative Congruence Closure
  Algorithms enriched with Semantic Properties"**, Logical Methods in Computer Science, Vol.
  19 Issue 1, 2023. DOI `10.46298/lmcs-19(1:19)2023`, arXiv `2111.04793` (v4, 13 Mar 2023),
  `https://lmcs.episciences.org/11073`. Published in the LMCS "Selected Papers of FSCD 2021"
  track.
- Predecessor: Deepak Kapur, "A Modular Associative Commutative (AC) Congruence Closure
  Algorithm", FSCD 2021, LIPIcs Vol. 195, DOI `10.4230/LIPIcs.FSCD.2021.15`.

Two results in the 2023 paper decide the shape of this design:

1. **Multiple AC symbols = the single-symbol loop run independently per symbol**, sharing only
   the constant set. There is no cross-symbol coupling beyond what union-find already provides:
   a constant with two normal forms (Kapur's one cross-symbol case) is, in an e-graph, just one
   e-class holding a node of each op, each reducing to the class via its own normal form. No
   fresh constant, no combination procedure.
2. **ACI is not a separate algorithm.** Idempotency is one of a family of *semantic properties*
   (idempotency, nilpotency, identity/unit, cancellativity, group) that enrich an AC symbol.
   Each property is a rule on the per-summand multiplicity in the monomial normal form. So ACI
   is "AC with multiplicities clamped to {0,1}", handled by parameterizing the one normalization
   step, not by forking the completion loop.

The paper deliberately avoids AC-compatible orderings, AC unification, and extension rules,
which matches our existing framing (the monomial degree-lex order is internal, not an AC-RPO).

## Three independent axes (do not conflate them)

A monomial is a map from summand class to a count. Three *independent* facts govern how a monomial
canonicalizes; an early draft folded them into one "clamp" column, which was wrong. Keep them
separate:

1. **Storage representation (MSet vs Set).** Either children are stored with an explicit count
   (**MSet**, `(G, Cfg::M)`) or as bare `G` with the count implicit at 1 (**Set**). This is the only
   axis the *routing/storage* layer cares about. A `Set` node is nothing but a space-optimized
   `MSet` node whose canonize rule guarantees every count is {0,1}, so the count need not be stored.
2. **Count clamp (none / idempotent / nilpotent).** How the normal form bounds a summand's count:
   none (ℕ, plain AC), idempotent (clamp to 1, `x∘x = x`), or nilpotent order-n (count mod n,
   `x∘x = e`; merge = symmetric difference at n=2). **This axis is NOT Set-only**: see
   "nilpotent must be MSet" below. It is an algebra property of the op, applied **inside canonization** (at build
   and on recanonicalize), not at completion time: the clamp establishes the stored normal form,
   so `xor(a,a) = e` holds with completion OFF (see "Canonization, not completion" below).
3. **Identity = a dropped unit element, orthogonal to both, on either representation.** A
   distinguished element `e` whose multiplicity is forced to 0 (removed) wherever it appears.
   Applies to MSet (`+` with `0`, `*` with `1`) **and** Set (`and` with `true`, `or` with `false`).
   It is *not* a count clamp; it is a separate optional field. Nilpotency *requires* an identity
   because the emptied monomial `{}` (`a⊕a`) must reduce to a real node, the unit.

### Storage partition and clamp are independent axes; nilpotent must be MSet

One could be tempted to store nilpotent ops in the Set partition: their normal-form
counts at order 2 are {0,1}, which "fit" a Set, and XOR reads like a set operation. **That
is unsound**, and the reason is the *canonize* step (run at build AND on `recanonize_node`
after a child merge). The Set partition is hardwired to exactly one canonize
rule, `sort; dedup` (`SetCanon`), which is the *idempotent* clamp. An op may live in the Set
partition only if `dedup` is its correct canonize rule. For nilpotent it is not: `xor(a, a)` must
reduce toward the unit `e`, but `dedup` collapses `{a,a} → {a} = a`, a **false equality**, and it
does so at build time, before completion runs. Dedup (presence) and parity (count mod 2) are
different rules; a single partition cannot serve both.

To compute `count mod n` you must first *hold* the count, and the only hash-consed place that holds
counts is the **MSet partition**. So the canonize-time representation for nilpotent is forced to be
MSet, even though the *values* in its normal form are {0,1} (n=2) and would "fit" a Set. The
principle:

> A `Set` node is a space-optimized `MSet` node: bare children, multiplicity implicit at 1. Storing
> into it is sound only if the op's canonize rule (build **and** recanonize) yields {0,1} counts
> from the current children slice alone. That holds for idempotent (`dedup`) and fails for nilpotent
> (`parity` needs the run-lengths dedup just threw away).

**Representation analysis: all combinations.** All ops here are AC (assoc + comm). *During-canon
repr* = the multiplicity domain that must be faithfully maintained (through recanonize) to stay
sound. *NF count domain* = the counts the normal form can contain. *Final storage* = the most
compact partition that can hold that normal form.

| algebra                         | canonize rule            | during-canon repr | NF counts   | final storage        |
|---------------------------------|--------------------------|-------------------|-------------|----------------------|
| AC (`+`, bag)                   | coalesce (sum counts)    | MSet (ℕ)          | ℕ (≥1)      | **MSet**             |
| AC + identity (`+`,`0`)         | coalesce + drop unit     | MSet (ℕ)          | ℕ, may empty| **MSet**             |
| AC + idempotent (`and`)         | dedup (presence)         | **Set** ({0,1})   | {0,1}       | **Set**              |
| AC + idem + identity            | dedup + drop unit        | **Set**           | {0,1}, empty| **Set**              |
| AC + nilpotent₂ + id (`xor`)    | parity (mod 2)           | **MSet** (needs run-length) | {0,1} | **MSet** (required for soundness, see above) |
| AC + nilpotentₙ + id (n>2)      | count mod n              | MSet ({0..n−1})   | {0..n−1}    | **MSet** (Set can't hold count 2) |
| AC + identity + inverse (group) | signed coalesce (ℤ): POSTPONED design; shipped: pair cancellation on ℕ counts | signed MSet (ℤ), not built | ℤ∖{0} | MSet (ℕ) + inverse-pair cancel |

Reading the table: the `xor` row is the mismatch. During-canon must be MSet for soundness under
recanonize, even though its NF values are {0,1}. Storing xor in the Set partition would need a
clamp-aware canonizer plus empty-var-node→unit and size-1→element handling *inside the store /
recanonize path*: hash-cons-core surgery for a constant-factor space win on xor-only nodes, and it
helps only n=2 (n>2 must be MSet regardless). **Decision: all nilpotent (every order) is stored in
the MSet partition.** The mod-n clamp is applied **inside `MSetCanon`** (`canonize` =
`update_multiset` then `clamp_multiset`), so the stored node is already `{0,…,n−1}`-valued: the
store never holds an unreduced count past a canonize, and nilpotent never routes through
`dedup` (the false-equality hazard above is structurally unreachable).

Consequently the clamp is a property of the op **regardless of partition**, and lives as a unified
field on both descriptors: `Idempotent → Set`; `None` / `Nilpotent{order}` → `MSet`.

### Canonization, not completion (the clamp/identity/degeneracy live in canonize)

The count clamp (nilpotent mod-n), the identity unit-drop, and the degenerate-arity collapse
(empty ⇒ the op's unit; single mult-1 summand ⇒ that summand's class) are the op's **canonical
normal form**, on the same footing as flatten/sort/coalesce and the idempotent `dedup`. They are
applied **inside canonization**, at build (`add`) and on `recanonize_node`, so they hold with AC
completion OFF. `xor(a,a) = e`, `and(a,a) = a`, `+(a,e) = a` are canonization facts, established the
moment the term is built (or when a child merge recanonicalizes it), never deferred to a completion
round. Mechanically: the clamp is a step inside `MSetCanon::canonize`; the clamp mode is fetched
from the op registry before canonizing (`recanonize_node` takes `&ops`, like `add`); and a
degenerate result is an *equality*, so it is emitted as a **merge** (build returns the existing
class id; recanonize records a collision-style merge): congruence, not the completion-layer
collapse (`FLAG_AC_COLLAPSED`, which is rule inter-reduction). Completion (`cc_round`) runs only
after `rebuild_congruence`, so every source node it reads is already canonical. The round still
clamps and normalizes generated reducts in the op's count domain, applies inverse-pair
cancellation where configured, and materializes them through `add`; that path can collapse an
empty or singleton reduct to its unit or element. The distinction is that completion does not
repair malformed stored source nodes: it preserves canonical form while deriving and
materializing new consequences.

The representation choice matters for memory: an MSet child is `(G, Cfg::M)` while a Set child
is a bare `G`. `Cfg::M` is independently configurable as a 16-, 32-, or 64-bit multiplicity
(`Multiplicity16`, `Multiplicity`, or `Multiplicity64`). Layout includes Rust alignment: for
the shipped 31-bit id configurations the 16- and 32-bit pairs are both 8 bytes and the 64-bit
pair is 16 bytes, versus 4 bytes for a Set child; the width tests pin these layouts. The
completion pool is unaffected either way because it stores node ids.

**In scope:** plain AC = MSet with no clamp, idempotent = Set (clamp Idempotent),
nilpotent = MSet with clamp Nilpotent, and identity on MSet or Set. Group is "shape-only"
at the descriptor level: the `:inverse` tag validates and stores, and the shipped
inference is inverse-PAIR cancellation (`x ∘ inv(x) = e`), not signed counts: the
signed-count representation sketched later in this chapter is a postponed design.

See the SMT-LIB operator survey at the end of this doc for which real operators land in each
representation.

### Clamps canonize; they do not replace Kapur §4's axiom critical pairs

One could hope the count clamp alone makes completion property-aware: after all, it
enforces the axiom `x∘x = x` (or `xⁿ = e`) inside every stored monomial. It does not
suffice. The clamp axis establishes each monomial's canonical form (it is the `can` of canonized
rewriting, Conchon–Contejean–Iguernelala Def. 4.1), but completion must ALSO superpose
every rule with the op's own axiom: for a rule `f(M) → f(N)`, idempotency requires the
pairs `(f(M), f(N ∪ {a}))` per `a ∈ M` (Kapur Lemma 4.1(ii)) and nilpotency order `n` the
pairs `(f(N ⊎ {a: n−m}), f((M − {a: m}) ⊎ {e}))` per summand (Lemma 4.2(ii)/4.5). These
are *cross-rule* consequences the within-monomial clamp cannot produce: e.g.
`or(a,b)=c ⟹ or(a,c)=c` and `xor(a,b)=c ⟹ xor(a,c)=b` are underivable without the axiom
pairs `cc_round` generates (spec §3 table row "per-rule axiom critical pairs"; fixtures
`aci_rule_axiom_cp.egg`, `nilpotent_rule_axiom_cp.egg`, `nilpotent3_rule_axiom_cp.egg`;
ground-truth checker `cc_axiom_cps_nonjoinable`, asserted under `CHECK_AC_BASIS`).
Identity needs no axiom pairs (Lemma 4.3), provided the unit-drop also runs on the
recanonize path (`CanonMode.unit` + the became-a-unit sweep in `rebuild_congruence`),
not just at build.

## Numbers for laws, ids for entities (why `order: u8`, why the unit is a node)

A recurring reading question: why is the nilpotent order a plain `u8` while the identity
and the inverse are ids? Because the pieces of an algebraic law have different natures,
and each is stored as what it IS:

- **The order `n` in `xⁿ = e` is arithmetic.** Its only use is as the modulus in the
  count clamp (`count % n`). No e-node denotes it (there is nothing in the graph to
  point AT), so a node-id type would be a category error. `u8` is the "orders are tiny"
  choice (xor = 2); the one known consequence is that encoding `bvadd(N)`'s additive
  torsion as nilpotency of order `2^N` needs `N < 8`, so widen to `u32` if bitvector
  modeling ever lands (a four-site mechanical change: the `Clamp` field, `MSetClamp`,
  the two clamp functions, the tag parser). The surface `Option<u8>` is only a parsing
  default: bare `:nilpotent` means order 2.
- **The identity `e` and the inverse operator ARE graph entities**, and they are stored
  as such: a resolved node id (`unit_node`) and op id (`inverse_op`) in egraph-side
  per-op maps with the same semi-persistence as the rest of the graph. They live off the
  `OpKind` descriptor because `OpKind<S>` is generic over sorts only and cannot carry a
  `Cfg::G`/`Cfg::O`. The descriptor also retains the parsed `UnitRef`, but registration
  immediately sort-checks and builds that ground term and records the resulting node.

## Type-width rationale (every numeric choice, and why it is sufficient)

The rule of thumb from the previous section (numbers for laws, ids
for entities) plus one more: every width is justified either by a HARD bound (checked or
structural) or by a PHYSICAL bound (memory exhausts first); no width relies on "probably
big enough" without an argument.

| Type | Width | Sufficiency argument |
|---|---|---|
| ids (`Cfg::G`/`Cfg::O`/`Cfg::S`) | **generic** via `EGraphConfig`: the engine never names a concrete id type (verified: zero hard-coded id uses in production code; tests bind a config, `literal.rs` has one overridable default param). `DefaultConfig`/`EGraph31` binds the 31-bit family (u32, bit 31 = capture flag); `EGraph63` binds 64-bit; `--id-bits` selects at runtime | for the 31-bit binding: ids are dense arena indices; 2³¹ nodes at ≥16 B/node ≥ 32 GB, so memory exhausts first, and the 63-bit binding covers that case. Width is a CONFIG choice, not an engine constant. |
| `RuleId`/`AxiomId` | 15-bit payload (u16, flag bit) | rules/axioms are program-declared; the encoding has 32,768 payload values, with maximum id 32,767. This is the tightest capacity in the system: fine for written programs, and the one to widen first if rule GENERATION ever lands. |
| `Cfg::M` / `Multiplicity16` | u16 | Optional compact count domain. Surface narrowing and every count-increasing operation are checked; values above 65,535 are rejected or panic instead of wrapping. With 31-bit ids the pair still pads to 8 bytes, so this width trades range rather than pair size. |
| `Cfg::M` / `Multiplicity` | u32 | Default count domain. Surface narrowing and count addition are checked in every build; overflow panics rather than becoming a wrong equality. |
| `Cfg::M` / `Multiplicity64` | u64 | Widest supported count domain. It accepts the full surface `u64` range, but sums can still overflow and panic. With 31-bit ids an MSet child is 16 bytes because of alignment. |
| `multiset_size` | u64 accumulator | Degree comparison sums multiplicities with `checked_add`; an unrepresentable total panics. This is an implementation limit, not a proof that every configured graph fits. |
| `Clamp::Nilpotent.order` | u8 | previous section; widen to u32 only for the postponed `bvadd` 2^N torsion encoding. |
| `GUARD_MAX_REWRITES` | usize = 1 000 000 | defensive implementation backstop, not a proved upper bound. Exhaustion panics in every build rather than returning a partial normal form. The paper termination argument applies only when all generated rules satisfy its orientation and representation hypotheses; that implementation correspondence remains a proof obligation. |
| `DEFAULT_COMPLETION_NODE_BUDGET` | usize = 50 000 | policy: resource bail (sound-but-incomplete, reported via `CompletionOutcome::AbortedGrowthLimit`); configurable per e-graph (`set_completion_node_budget`); limits and open work are in `../future/ac-completion-limitations.md`. |
| flatten cap `seed_children + 1 + 64·node_count` (saturating `usize`) | operational refusal bound, not a semantic theorem | The seed term permits legitimately wide inputs. Saturating arithmetic prevents the guard calculation itself from wrapping; the cap counts recursive splice expansions and output. Exhaustion panics in every build rather than returning a partial normal form. |

## Where the algebra lives: ENodeKind (routing) vs OpKind (algebra)

The codebase already separates the two concerns this raises, and the descriptor design uses that
split rather than inventing a side table.

- **`ENodeKind`** (`id.rs`) is the `#[repr(u8)]` storage/routing discriminant copied into node
  headers and the routing table. It is payload-free and stays that way. Its representation variants
  are renamed to the representation names (`AC → MSet`, `ACI → Set`); this is the only Set-vs-MSet
  fact the routing layer needs, and clamp/identity never touch it.
- **`OpKind`** (`registry.rs`, inside `OpInfo`) is the per-op algebra record, stored once per op in
  the registry `Map`, `Clone`-not-`Copy`, **not** copied into any hot structure. It already carries
  per-op static metadata (`arg_sort`, `dir`). The clamp and identity live here, co-located with the
  representation tag so they cannot desync:

  ```rust
  enum OpKind<S> {
      // ... Normal, Commutative, A, Lit unchanged ...
      MSet { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool },
      Set  { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool },
  }
  enum Clamp { None, Idempotent, Nilpotent { order: u8 } }  // unified, on BOTH variants
  // clamp and identity are representation-independent fields on both variants.
  ```

  Note: the resolved `:inverse` OPERATOR ID is deliberately NOT an `OpKind`
  field: `OpKind<S>` cannot carry an op id. Like the resolved identity node, it lives in
  an egraph-side per-op map (`inverse_op`, same semi-persistence as `unit_node`), consumed
  by inverse-PAIR cancellation (`x ∘ inv(x) = e`, at build and on completion normal
  forms). Full Abelian-group completion (§5.4 signed counts / Gaussian elimination) is
  postponed indefinitely: the signed-count sketch further down describes that postponed
  design, not the shipped mechanism.

  The clamp is a *unified* field on both variants (the independence argument above): partition is
  derived from the resolved clamp: `Idempotent → Set`; `None` / `Nilpotent → MSet`. The resolver
  is the single point that enforces the legal (clamp, partition) pairings; a `MSet { clamp:
  Idempotent }` or `Set { clamp: Nilpotent }` is never constructed. `OpInfo::canon_class` projects
  `OpKind` down to the bare `ENodeKind` for routing (`MSet { .. } → ENodeKind::MSet`, `Set { .. } →
  ENodeKind::Set`), and completion reads the clamp via `op_clamp` regardless of partition.

The algebra record is co-located with `OpKind`, avoiding a second op-to-algebra map that would
have to stay synchronized with the representation tag. This is a structural design rationale,
not a measured performance claim.

**In scope:** `OpKind::MSet { clamp: None }` (AC), `OpKind::Set { clamp: Idempotent }` (ACI),
`OpKind::MSet { clamp: Nilpotent }` (XOR), and identity on either. Group: the `:inverse`
tag is validated and consumed at pair-cancellation level; the signed-count
representation this section sketches is the POSTPONED full-group design, not shipped.

## Storage: one pool of node ids, fixed-width rows over a strongly-typed op array

### Entries are global node ids, never materialized sets/multisets

Each per-class min-monomial entry is a `Cfg::G` pointing at a real member node (an AC node for
an AC column, an ACI node for an ACI column). The monomial is recomputed on read by
dereferencing the id (`node_monomial_into` -> `mset_children` for MSet,
`set_children` for Set).
It is a merge-maintained **candidate**, not a verified exact minimum after arbitrary merge
cascades; the completion orientation guard filters candidates that no longer produce a
decreasing rule, and the optional basis diagnostic searches for non-minimal candidates.
Rationale:

- The id is the canonical handle: children are read through `find_const`, so multiplicities and
  membership are always live. A stored multiset would go stale the moment a child class merges
  and would need re-canonicalization anyway.
- Every stored candidate is a class-member node, and completion's materialized reducts are real
  nodes (`materialize` calls `eg.add`), so a node id suffices for the maintained candidate.
- `class_rhs_into` dereferences the candidate for the requested completion column. The pool can
  hold one such id per completion op per allocated class row.

### The column → op reference array (strongly typed `OpId`, no `u16` slots)

There is **one** pool. Each class's row is `nb_completion = nb_mset + nb_set` columns wide, one
column per registered MSet and Set op. `OpRegistry` persistently stores one `CompletionSlot`
per op with its kind and running MSet/Set ranks. `completion_column(op)` reads that table in
O(1). `completion_ops()` is an allocating derived view used by round-level callers; it returns
MSet ops followed by Set ops, preserving registration order within each segment:

```
completion_ops() -> Vec<Cfg::O> // e.g. [op_+, op_*, op_and, op_or]
//                                  column:  0      1      2       3
```

So `pool[row * width + i]` is the maintained monomial candidate for op
`completion_ops()[i]`. To find a node's own column, `completion_column` reads its persistent
`CompletionSlot`; it does not allocate or scan the op map. No separate public slot id is stored.

The op registry and its `CompletionSlot` table are marked and restored together, so op ids and
their ranks remain aligned. Column order can change if a new MSet op is inserted after Set ops;
the class layer therefore fixes row width and column meaning when the first completion row is
seeded and rejects a later width change at the next completion-node seed. The implementation
does not perform a `node_op` assertion on every pool access; column correctness follows from
the only writers mapping the node's op through `completion_column`, and is covered by registry,
pool, and completion tests rather than a machine-checked semantic invariant.

### Layout

```
EClasses {
    min_pool: ParallelStore<Opt<Cfg::G>, TRACK>, // flat, whole rows
    min_width: usize,
}
ClassData { use_list: L, min_row: Option<T::Index>, atomic: bool, size: T::Index }
```

`size` is the class's member-node count, kept in the node-id family's index type (the `min_row`
pattern): set to 1 at `add_singleton`, folded survivor += absorbed at `merge_with`. It feeds the
`--union-by size`/`sum` survivor policy.

Entries are `Opt<Cfg::G>`; absent means "this class holds no candidate for this op yet."
`min_row` stores a row number, not a byte or element offset, and is absent for a class that
holds no MSet/Set monomial.

A row mixes AC and ACI columns (`[ac_min_+, ac_min_*, aci_min_and, aci_min_or]`); they are all
`Opt<Cfg::G>` node ids, homogeneous storage. The per-column semantics (MSet counts vs Set
presence) is a read-time property looked up from `ops.info(completion_ops()[i]).kind`, not a
property of which pool the id lives in. So one pool keeps the per-kind clamp; it just resolves
the clamp from the op rather than from a pool identity. Every allocated row reserves all
completion columns, including absent cross-sort columns; the cost is therefore exactly
`nb_completion * size_of::<Opt<G>>()` per allocated row, not assumed negligible.

Rows are appended to a flat semi-persistent pool. Row width is fixed after the first row.

- **Lazy allocation.** The first time a class gains any AC/ACI monomial, append `nb_completion`
  absent entries to `min_pool` and store the row number in `min_row`.
- **Merge mutates the survivor row in place** (`min_pool.set(row * width + i, …)`), captured/restored
  by the semi-persistent `VecI`. The pool grows only on first-AC/ACI-monomial-per-class, never on
  merge, so it is bounded by `nb_completion × (classes holding any AC/ACI monomial)`.

### Row width vs. late op registration

A row's width is the completion-op count when the first completion node seeds the pool.
The normal surface workflow declares functions before building terms. Registration itself
does not inspect class rows, so a late completion-op declaration can succeed; when a node of
that op is subsequently created, `register_if_fresh` calls `set_min_width(new_count)`, which
rejects changing a nonempty pool's fixed width. There is no migrate-on-grow implementation.

### Fixed-width rows, not variable-width slices

A variable-width slice (listing only the `(op, node)` pairs a class actually holds) is sparser,
but merge would have to append a fresh unioned row and repoint the offset whenever the survivor
gains a new op, growing the pool per merge. With `nb_completion` tiny, fixed-width rows with
in-place merge are simpler and keep pool growth off the merge path. Use fixed-width.

### Access path

`OpRegistry::completion_column(op)` maps an op to `i`; callers then use
`EClasses::{min_monomial,set_min_monomial}(repr, i)`. The class layer computes
`row * min_width + i`, checks the column and live-key bounds, and lazily allocates a whole row
on the first write.

## Invariants that keep the pool sound

1. **A pool column is intended to hold only nodes of its owning op.** Fresh completion nodes
   are seeded through `completion_column(op)`, and merge folding compares the same column from
   two rows. The implementation has tests for this routing but no per-access assertion or
   machine-checked theorem connecting a stored node's op to the registry column.
2. **The monomial read is kind-correct.** MSet reads coalesced
   multiplicities (`mset_children`); Set reads deduplicated children with
   implicit multiplicity 1 (`set_children`). The column's op (hence kind) selects the
   semantics; `node_ref` confirms it.
3. **`monomial_cmp` compares within a column in the merge fold.** The fold is element-wise per
   column `i`: keep the `monomial_cmp`-smaller of `survivor[base+i]` and `absorbed[base+i]`,
   absent = +∞. Both operands are column `i`, hence the same op, hence the same kind: never a
   multiset against a set. The fixed column layout enforces this structurally; the comparison
   never crosses kinds.
4. **`atomic` stays a single per-class bool.** If a class is referenced as a child anywhere,
   `{class}` is a real atom usable in *any* op's monomials, so the flag short-circuits the
   per-op min regardless of kind. It is not per-op.
5. **Staleness is guarded.** A stored candidate may cease to be minimal under a merge cascade; the
   read-time orientation guard (design §9b axis-2) already makes that safe and is unchanged.

## How AC uses the pool

Storage reads and writes index by op through `completion_column`.

- **RHS read** (`class_rhs_into`): the empty monomial if the class is the op's identity
  class (Kapur's `f({}) = e`: the normative RHS definition is `ac-completion-spec.md` §1);
  else if `atomic` → `{class}`; else the stored candidate in the node op's column → emit that
  node's monomial. For a real rule, the `node` is itself a column-`i` node, so the slot is
  non-absent.
- **Merge fold** (`fold_min_monomial`): element-wise over the row (invariant 3), OR the `atomic`
  bool. `MergeInfo` carries the absorbed class's row number so the survivor can fold it.
- **Completion loop**: builds rules from all MSet and Set nodes. Each `Rule` carries its op,
  and superposition/normalization filter by
  op (`rj.op == rules[i].op`), so two ops produce two non-interacting rule sets sharing the
  constant pool. The cross-op `a+b = a*b` case is one e-class holding a `+`-node and a `*`-node,
  each reducing to the class via its own column; union-find records the equality (Kapur's
  shared-constant case, dissolved for free).

## How ACI uses the pool, and the one difference

ACI uses Set columns (one per idempotent op) with two localized differences:

1. **Set monomials.** ACI children are bare `G` with multiplicity always 1 (`nodes.set`). So an
   ACI node's monomial emits each class with count 1, and `monomial_cmp` over an ACI monomial is
   the degree-lex applied to the deduplicated element set (every count 1, so "size" is the
   number of distinct elements).
2. **Idempotent normalization.** The I axiom clamps every count to 1 after each rewrite step.
   The superposition arithmetic is the same shape (lcm = union, subtract, normalize); the AC
   primitives in `multiset.rs` provide `normalize_set_into`, which clamps counts to {0,1}
   after each rewrite.

Completion iterates both partitions, superposes same-op rules, normalizes reducts with the
op's clamp, merges differing normal forms, and collapses reducible rules. This is an
implementation correspondence with Kapur's property-enriched construction, not a verified
completeness theorem.

The clamp alone is insufficient. `cc_round` explicitly generates the per-rule idempotence
critical pairs from Kapur §4, such as `or(a,b)=c` implying `or(a,c)=c`; the nilpotent arm
likewise generates its semantic-axiom pairs. Focused fixtures and `cc_axiom_cps_nonjoinable`
exercise these generators.

## Semi-persistence

`min_pool` is a `ParallelStore` inside the shared `EClasses` aggregate. `EClasses::mark`
captures the representations, use-list arena, class-ring state, and pool token;
`restore` restores them together. The Verus aggregate proves its structural W1-W7
invariant, including whole-row pool layout and live-row bounds. That proof does not establish
the egraph-level semantic property that a candidate belongs to the op denoted by its column.

## Surface language: composable property tags

The surface declares algebra with **orthogonal basic tags** (`parser.rs` `AlgTag`, dispatched in
`sortcheck.rs`); `OpKind` and the set/mset representation are derived from the combination.
Properties that need a value take a ground argument.

```
:comm  :assoc  :assoc-left  :assoc-right
:idempotent  :nilpotent [n]  :identity <term>  :cancellative  :inverse <op>
```

Pre-combined tags would not compose: every new combination (nilpotent, identity, group) would
need its own tag. The pre-combined `:assoc-comm` / `:assoc-comm-idem` are therefore accepted
only as aliases that the parser expands into the basic tags (`:assoc :comm` and
`:assoc :comm :idempotent`).

```
(function +    (Int)  Int  :assoc :comm)                        ; AC, multiset
(function and  (Bool) Bool :assoc :comm :idempotent)            ; ACI, set (clamp to 1)
(function cat  (E)    E    :assoc-left)                         ; A-only sequence
(function xor  (Bool) Bool :assoc :comm :nilpotent :identity (false))  ; MSet, mod-2 clamp
(function +    (Int)  Int  :assoc :comm :identity 0)            ; AC + unit drop
```

### Derivation from tags

| tags                            | OpKind        | representation     | normal-form merge        |
|---------------------------------|---------------|--------------------|--------------------------|
| `:assoc-left`                   | A             | sequence           | flatten first-child spine |
| `:assoc-right`                  | A             | sequence           | flatten last-child spine |
| `:assoc`                        | A             | sequence           | flatten every same-op child |
| `:comm` (binary)                | C             | pair               | reorder                  |
| `:assoc :comm`                  | AC            | **multiset** (ℕ)   | union                    |
| `:assoc :comm :idempotent`      | ACI           | **set** ({0,1})    | union, clamp to 1        |
| `:assoc :comm :nilpotent`       | nilpotent     | **multiset** (mod-n clamp; see "nilpotent must be MSet") | symmetric difference (n=2) |
| + `:identity e` on any AC row   | (same)        | (same)             | additionally drop `e`    |

### Which properties take a parameter, and which are baked in

The rule: a property needs a parameter iff its reduction target names a term the engine cannot
derive structurally.

| property      | parameter                       | baked? | why                                                              |
|---------------|---------------------------------|--------|------------------------------------------------------------------|
| `:comm`       | none                            | yes    | structural (reorder children)                                    |
| `:assoc-left` / `:assoc-right` / `:assoc` | direction encoded by the tag | yes | flatten the selected spine during construction |
| `:idempotent` | none                            | yes    | reduces to the operand itself; clamp count to 1, no external term |
| `:identity`   | the unit term `e`               | no     | `e` is op-specific (`0` for `+`, `true` for `and`)               |
| `:nilpotent`  | the unit `e` (+ optional order n, default 2) | no | the emptied monomial `{}` must canonicalize to a real node = the unit |
| cancellative  | none                            | yes    | inference rule on equations, no element                          |
| group         | unit `e` + unary inverse op     | no     | the inverse operator and unit are op-specific                    |

So **idempotent and cancellative are fully bakeable**; **identity, nilpotent, and group must
declare the neutral element** (group also the inverse op). The structural reason idempotent needs
no unit but nilpotent does: idempotent clamping (count→1) keeps a non-empty monomial non-empty,
so it never reaches `{}`; nilpotent (count mod 2) can empty a monomial (`a⊕a → {}`), and `{}` must
equal a real node, the unit. That is also why `:nilpotent` requires `:identity` to be present.

Parameter syntax: a value-taking tag is followed by a **ground term of the op's return sort**:
`:identity 0` (literal) or `:identity (zero)` (nullary constant application), `:nilpotent` (order
2 default) or `:nilpotent 3`, `:inverse neg` (names the unary inverse op). This is not a
new literal syntax: the tag argument is an ordinary surface term, parsed by the existing term
grammar (`Term::Lit` / `Term::App`).

### Resolve free tags into a closed descriptor (the choke point)

Free composition at the surface, resolved **once at registration** into a closed, validated
descriptor that the rest of the engine matches on. Not a fixed menu of compound tags (does not
compose), and not on-the-fly re-derivation at each read site (re-introduces the late-validation /
recomputed-representation bugs the `completion_ops` array exists to remove). The resolver
(`sortcheck.rs`) is the single place that maps a tag set to the descriptor in `registry.rs`:

```rust
enum Clamp { None, Idempotent, Nilpotent { order: u8 } }  // count clamp in the normal form
enum OpKind<S> {
    // ... Normal, Commutative, A, Lit ...
    MSet { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool },
    Set  { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool },
}
```

The `MSet`/`Set` variant is derived from the clamp (`Idempotent` → `Set`; `None` / `Nilpotent` →
`MSet`: dedup would destroy the run-lengths the mod-n clamp needs, see "nilpotent must be MSet")
and chosen at resolution, so every downstream site is a single exhaustive match on `OpKind`,
never a re-derivation from tags. `OpKind` is stored on `OpInfo`. Invalid tag combinations are
rejected here and become unrepresentable downstream.

This lands on the existing structure with no new partition: `OpKind::MSet` routes to
`nodes.mset` (`(G, mult)` children), `OpKind::Set` to `nodes.set` (bare `G`). Plain AC and
nilpotent **share** the multiset partition (nilpotent needs true multiplicities before the mod-n
clamp) and differ only in the `Clamp` the canonicalizer/merge reads: `None` for plain AC,
mod-n for `Nilpotent`; idempotent is the one `Set` case (dedup IS its clamp).

### Validation at registration

The resolver (`sortcheck.rs`) rejects an invalid tag set at registration:

- `:assoc`, `:assoc-left`, and `:assoc-right` are mutually exclusive (repeating the same tag
  is harmless); directional folds cannot be combined with `:comm`, because that would silently
  strengthen them to full AC.
- `:idempotent` and `:nilpotent` are mutually exclusive (cannot clamp to 1 and reduce mod 2).
- `:idempotent` / `:nilpotent` require `:assoc :comm` (the monomial machinery is AC-based).
- `:nilpotent` requires `:identity` (it needs the unit to reduce to).
- `:inverse` requires `:identity` (an inverse cancels *to* the unit).
- `:idempotent` and `:inverse` are **mutually exclusive**: not merely unimplemented, but algebraically
  incoherent. See "Inverse is a group inverse, not a complement" below: an idempotent group is trivial,
  so an idempotent AC op has no non-trivial inverses. This rejects `and`/`or` + `:inverse` at the
  resolver (the intended `not`/complement is a *different* structure: model it as `xor`).
- `:idempotent` and `:cancellative` are mutually exclusive (a cancellative idempotent monoid
  collapses to the identity).
- `:cancellative` requires `:assoc :comm` (cancellativity is an inference rule on AC monomial
  equations; on an A-only, C-only, or plain operator the tag would be stored nowhere and
  silently ignored).
- `:identity e` must sort-check `e` to the op's return sort.

### The unit ground term is built at registration

`:identity e` uses the ordinary ground-term machinery:

- A literal unit (`0`, `true`, `#b0000`) lexes as `Term::Lit` (`parser.rs` `is_literal`),
  sort-checks through `LitValParser::parse(tok, sort)` (`literal.rs`) into a `LitVal`, and builds
  via `lit_op_for_sort(sort)` + `add_lit` (`interpret.rs`): the identical path every program
  literal already takes. Bitvector units need only an appropriate parser
  closure registered on the BV sort, which BV literals in programs require
  anyway; nothing identity-specific.
- A constructed unit (`(zero)`) is a `Term::App` over a previously declared nullary op, built by
  the ordinary term builder.

`register_op` first records a parsed `UnitRef` in `OpKind`, then sort-checks the identity term,
builds it immediately through `build_ground_cterm`, and stores the resulting node in the
egraph's `unit_node` map. Consequently any constructor or literal operator needed by the unit
must already be declared. Registration can add the unit node to the graph; the op registry,
unit map, and graph state participate in the normal mark/restore protocol.

### Inverse is a group inverse, not a complement (why `not` is not an `and`-inverse)

`:inverse` means a **group inverse**: a unary op `x⁻¹` with `x ∘ x⁻¹ = e`, where `e` is the
operator's own **identity**. The shipped implementation recognizes and cancels explicit
inverse pairs. A future full Abelian-group completion would lift coefficients to signed
integers; it is not implemented. Three points fix what this is and is not.

**1. It only exists for the multiset (non-idempotent) operators.** The clean cases:

| op  | identity `e` | inverse `x⁻¹` | `x ∘ x⁻¹` | signed count means | notes |
|-----|--------------|---------------|-----------|--------------------|-------|
| `+` | `0`          | `−x` (`neg`)  | `0` = `e` ✓ | integer coefficient | *the* group case; abelian group |
| `*` | `1`          | `1/x` (`recip`) | `1` = `e` ✓ | exponent           | **partial** (`0` has no inverse); `*` also has annihilator `0` (treat opaque); distribution is cross-op (a ring), out of scope |

The shipped pair-level rule can cancel `a + neg(a)` to the unit and can remove paired copies
from a larger monomial. It does not standardize arbitrary signed coefficients or derive all
Abelian-group consequences (for example, it is not the signed Gaussian/inter-reduction
procedure sketched by Kapur §5.4). The store always holds unsigned multiplicities and
`neg(a)` remains a real child node.

**2. Idempotent + inverse is incoherent, so it is rejected: this is why `not` is not an
`and`-inverse.** A tempting mistake is to read logical `not` as an `and`-inverse encoded by the sign
of a multiplicity on the `and` (Set) representation. It is not, for two independent reasons:

- *Wrong target.* An `and`-inverse would have to satisfy `x ∧ x⁻¹ = e_and = true`. But
  `x ∧ ¬x = false`, and `false` is the **annihilator** (zero) of `and`, not its identity `true`. So
  `¬x` does not cancel `x` to the unit; it is a complement, not an inverse.
- *No group to sign.* In any group an idempotent element is the identity
  (`x∘x = x ⟹ x = e`), so a genuinely idempotent operator has **no non-trivial inverses** at all.
  `and`/`or` are idempotent (that is the whole Set representation, counts clamped to {0,1}), hence
  carry no group structure to attach a signed multiplicity to. Boolean algebra under `and` is a
  bounded semilattice, not a group.

Therefore `:idempotent` + `:inverse` is rejected at the resolver (listed above), the same way
idempotent and nilpotent are mutually exclusive.

**3. Where logical negation actually lives: `xor`, already handled.** `not` *is* expressible in
this framework, over the **additive** Boolean operator rather than the multiplicative one:
`¬x = true ⊕ x`. In the Zhegalkin/GF(2) view `xor` is the additive group and `and` the
multiplicative monoid. And `xor` is exactly **nilpotent order 2**, which means every element is its
own additive inverse (`x ⊕ x = 0`), so xor's "inverse" is already covered by the shipped
nilpotent clamp, with no signing needed. Net: complementation is modeled as `xor` with the
constant `true` (available today), never as an inverse on `and`.

### Scope and compatibility

All property tags are wired end to end: `:identity` and `:nilpotent` run in canonization
AND completion; `:cancellative` drives the Kapur §5 cancel-closure; `:inverse` (which
implies cancelative) drives inverse-pair cancellation. Full Abelian-group completion
(§5.4 signed counts / Gaussian elimination) is postponed indefinitely. The pre-combined
aliases `:assoc-comm` / `:assoc-comm-idem` remain accepted for compatibility and expand
to the basic tags.

## SMT-LIB AC operator survey

All AC (associative *and* commutative) operators across the standard SMT-LIB theories, with the
representation the design above assigns if modeled with these tags. Operators that are A-only,
C-only, or neither are listed as exclusions per theory. The `repr` column drives child storage:
**set** = bare `G` children, **mset** = `(G, Cfg::M)` children.

### Core (Bool)

| op           | A | C | identity | idempotent | nilpotent | repr |
|--------------|---|---|----------|------------|-----------|------|
| `and` (∧)    | ✓ | ✓ | `true`   | ✓          | —         | set  |
| `or` (∨)     | ✓ | ✓ | `false`  | ✓          | —         | set  |
| `xor` (⊕)    | ✓ | ✓ | `false`  | —          | ✓         | mset (mod 2) |

Not AC: `not` (unary involution), `=>` (right-assoc, not comm), `=` / `distinct` (pairwise, not
an AC fold), `ite`.

### Ints / Reals

| op  | A | C | identity | idempotent | nilpotent | repr |
|-----|---|---|----------|------------|-----------|------|
| `+` | ✓ | ✓ | `0`      | —          | — (group via unary `-`) | mset (ℕ; signed ℤ if modeling the group) |
| `*` | ✓ | ✓ | `1`      | —          | —         | mset |

Not AC: `-` (binary), `/`, `div`, `mod`, `abs`, comparisons. `min`/`max` (where a logic provides
them): AC + idempotent → set.

### FixedSizeBitVectors

| op       | A | C | identity   | idempotent | nilpotent | repr |
|----------|---|---|------------|------------|-----------|------|
| `bvand`  | ✓ | ✓ | all-ones   | ✓          | —         | set  |
| `bvor`   | ✓ | ✓ | `0`        | ✓          | —         | set  |
| `bvxor`  | ✓ | ✓ | `0`        | —          | ✓         | mset (mod 2) |
| `bvxnor` | ✓ | ✓ | all-ones   | —          | ✓         | mset (mod 2) |
| `bvadd`  | ✓ | ✓ | `0`        | —          | —         | mset |
| `bvmul`  | ✓ | ✓ | `1`        | —          | —         | mset |

Not AC: `bvnand` / `bvnor` (not associative), `concat`, `bvsub`, shifts, `bvudiv`, `bvnot` /
`bvneg` (unary).

### Sets / Bags (CVC-style finite collections)

| op                     | A | C | identity   | idempotent | repr |
|------------------------|---|---|------------|------------|------|
| `set.union` (∪)        | ✓ | ✓ | ∅          | ✓          | set  |
| `set.inter` (∩)        | ✓ | ✓ | universe   | ✓          | set  |
| `bag.union_max`        | ✓ | ✓ | empty bag  | ✓ (max)    | set-like |
| `bag.inter_min`        | ✓ | ✓ | —          | ✓ (min)    | set-like |
| `bag.union_disjoint` (⊎) | ✓ | ✓ | empty bag | —         | mset (counts add) |

Not AC: `set.minus`, `bag.difference_*`. Bags are the one theory where multiset is the
*semantics*, not just an encoding: `bag.union_disjoint` genuinely needs counts.

### Strings / Sequences / Regex

| op                     | A | C | identity            | repr |
|------------------------|---|---|---------------------|------|
| `str.++` / `seq.++`    | ✓ | ✗ | `""`                | A-only (sequence; order matters, neither set nor mset) |
| `re.union`             | ✓ | ✓ | `re.none`           | set (idempotent) |
| `re.inter`             | ✓ | ✓ | `re.all`            | set (idempotent) |
| `re.++`                | ✓ | ✗ | `(str.to_re "")`    | A-only |

Concat-family is associative-only (the A operators), handled by flattening into a sequence, not
by AC monomials.

### Arrays, FloatingPoint

No AC operators. `select` / `store` are not AC. FP `fp.add` / `fp.mul` are commutative but **not
associative** (rounding), so they are not AC and get no completion.

### Summary

- **set** (bare `G`, {0,1} counts): `and`, `or`, `bvand`, `bvor`, `set.union`, `set.inter`,
  `bag.union_max`, `bag.inter_min`, `re.union`, `re.inter`, `min`, `max`: the idempotent
  (union-clamp) operators.
- **mset** (`(G, Cfg::M)`, configured unsigned counts): `+`, `*`, `bvadd`, `bvmul`,
  `bag.union_disjoint` (plain AC),
  **plus the nilpotent family** (`xor`, `xnor`, `bvxor`, `bvxnor`): stored MSet with the mod-n
  clamp (symmetric difference at n=2), see "nilpotent must be MSet".
- **signed mset** (ℤ counts): only if abelian groups are ever modeled (out of scope).

Implemented: set-idempotent (ACI: `and`, `or`, …), multiset (AC: `+`, `*`, …), and the
nilpotent family (MSet + mod-n clamp + declared unit). The signed-count group representation
remains out of scope (shipped group support is inverse-PAIR cancellation).
