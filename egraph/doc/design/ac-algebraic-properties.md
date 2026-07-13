# Algebraic properties of AC operators: representation, canonization, and the per-op pool

Design chapter (promoted 2026-07-10 from the retired implementation plan
`doc/future/multi-ac-aci-completion-plan.md`, now deleted; the staging/build-order sections live
in git history — the dated corrections inside predate the promotion and are kept verbatim).
The monomial order referenced throughout is defined in `ac-completion-spec.md` §3.1
(degree-lex: total size, then lexicographic from the largest class id down — Kapur's
deglex). This is the durable record of how multiple AC/ACI symbols and their
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
   (**MSet**, `(G, u32)`) or as bare `G` with the count implicit at 1 (**Set**). This is the only
   axis the *routing/storage* layer cares about. A `Set` node is nothing but a space-optimized
   `MSet` node whose canonize rule guarantees every count is {0,1}, so the count need not be stored.
2. **Count clamp (none / idempotent / nilpotent).** How the normal form bounds a summand's count:
   none (ℕ, plain AC), idempotent (clamp to 1, `x∘x = x`), or nilpotent order-n (count mod n,
   `x∘x = e`; merge = symmetric difference at n=2). **This axis is NOT Set-only** — see the
   correction below. It is an algebra property of the op, applied **inside canonization** (at build
   and on recanonicalize), not at completion time — the clamp establishes the stored normal form,
   so `xor(a,a) = e` holds with completion OFF (see "Canonization, not completion" below).
3. **Identity = a dropped unit element, orthogonal to both, on either representation.** A
   distinguished element `e` whose multiplicity is forced to 0 (removed) wherever it appears.
   Applies to MSet (`+` with `0`, `*` with `1`) **and** Set (`and` with `true`, `or` with `false`).
   It is *not* a count clamp; it is a separate optional field. Nilpotency *requires* an identity
   because the emptied monomial `{}` (`a⊕a`) must reduce to a real node, the unit.

### Correction (2026-07-01): storage partition and clamp are genuinely independent; nilpotent is MSet

An earlier version of this section claimed the clamp is "Set-only" and that **XOR is a Set**. That is
**wrong**, and building on it would be unsound. The reason is the *canonize* step (run at build AND
on `recanonize_node` after a child merge). The Set partition is hardwired to exactly one canonize
rule — `sort; dedup` (`SetCanon`) — which is the *idempotent* clamp. An op may live in the Set
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

**Representation analysis — all combinations.** All ops here are AC (assoc + comm). *During-canon
repr* = the multiplicity domain that must be faithfully maintained (through recanonize) to stay
sound. *NF count domain* = the counts the normal form can contain. *Final storage* = the most
compact partition that can hold that normal form.

| algebra                         | canonize rule            | during-canon repr | NF counts   | final storage        |
|---------------------------------|--------------------------|-------------------|-------------|----------------------|
| AC (`+`, bag)                   | coalesce (sum counts)    | MSet (ℕ)          | ℕ (≥1)      | **MSet**             |
| AC + identity (`+`,`0`)         | coalesce + drop unit     | MSet (ℕ)          | ℕ, may empty| **MSet**             |
| AC + idempotent (`and`)         | dedup (presence)         | **Set** ({0,1})   | {0,1}       | **Set**              |
| AC + idem + identity            | dedup + drop unit        | **Set**           | {0,1}, empty| **Set**              |
| AC + nilpotent₂ + id (`xor`)    | parity (mod 2)           | **MSet** (needs run-length) | {0,1} | **MSet** (required for soundness — the 2026-07-01 correction below) |
| AC + nilpotentₙ + id (n>2)      | count mod n              | MSet ({0..n−1})   | {0..n−1}    | **MSet** (Set can't hold count 2) |
| AC + identity + inverse (group) | signed coalesce (ℤ) — POSTPONED design; shipped: pair cancellation on ℕ counts | signed MSet (ℤ) — not built | ℤ∖{0} | MSet (ℕ) + inverse-pair cancel |

Reading the table: the `xor` row is the mismatch — during-canon must be MSet for soundness under
recanonize, even though its NF values are {0,1}. Storing xor in the Set partition would need a
clamp-aware canonizer plus empty-var-node→unit and size-1→element handling *inside the store /
recanonize path* — hash-cons-core surgery for a constant-factor space win on xor-only nodes, and it
helps only n=2 (n>2 must be MSet regardless). **Decision: all nilpotent (every order) is stored in
the MSet partition.** The mod-n clamp is applied **inside `MSetCanon`** (`canonize` =
`update_multiset` then `clamp_multiset`), so the stored node is already `{0,…,n−1}`-valued — the
store never holds an unreduced count past a canonize. This also immediately closes the earlier
unsoundness (nilpotent no longer routes through `dedup`).

Consequently the clamp is a property of the op **regardless of partition**, and lives as a unified
field on both descriptors: `Idempotent → Set`; `None` / `Nilpotent{order}` → `MSet`.

### Canonization, not completion (the clamp/identity/degeneracy live in canonize)

The count clamp (nilpotent mod-n), the identity unit-drop, and the degenerate-arity collapse
(empty ⇒ the op's unit; single mult-1 summand ⇒ that summand's class) are the op's **canonical
normal form**, on the same footing as flatten/sort/coalesce and the idempotent `dedup`. They are
applied **inside canonization** — at build (`add`) and on `recanonize_node` — so they hold with AC
completion OFF. `xor(a,a) = e`, `and(a,a) = a`, `+(a,e) = a` are canonization facts, established the
moment the term is built (or when a child merge recanonicalizes it), never deferred to a completion
round. Mechanically: the clamp is a step inside `MSetCanon::canonize`; the clamp mode is fetched
from the op registry before canonizing (`recanonize_node` takes `&ops`, like `add`); and a
degenerate result is an *equality*, so it is emitted as a **merge** (build returns the existing
class id; recanonize records a collision-style merge) — congruence, not the completion-layer
collapse (`FLAG_AC_COLLAPSED`, which is rule inter-reduction). Completion (`cc_round`) runs only
after `rebuild_congruence`, so every node it reads is already canonical; it therefore does *only*
superposition + inter-reduction, and needs no clamp/degeneracy handling of its own.

The representation choice matters for memory: an MSet child is `(G, u32)` (the multiplicity is
`u32`, see `multiplicity.rs` — *not* the 128-bit literal value, which is unrelated) versus a bare
`G` for a Set child. At 31-bit `G` that is 8 bytes vs 4, a ~2x per-child overhead the idempotent
(Set) ops should not pay. The completion *pool* is unaffected either way (it stores node ids); the
node child storage picks MSet vs Set from the op (the existing `nodes.mset`/`nodes.set` partitions).

**In scope to implement now:** plain AC = MSet with no clamp, idempotent = Set (clamp Idempotent),
nilpotent = MSet with clamp Nilpotent, and identity on MSet or Set. Group (inverse/signed) is
— see the 2026-07-10 note below: "shape-only" means the descriptor validates and stores the
tag, while the shipped inference is inverse-PAIR cancellation, not signed counts —
recorded so the descriptor has the right *shape* but is not built here.

See the SMT-LIB operator survey at the end of this doc for which real operators land in each
representation.

### Correction (2026-07-09): clamps canonize; they do not replace Kapur §4's axiom critical pairs

The clamp axis establishes each monomial's canonical form (it is the `can` of canonized
rewriting, Conchon–Contejean–Iguernelala Def. 4.1), but completion must ALSO superpose
every rule with the op's own axiom: for a rule `f(M) → f(N)`, idempotency requires the
pairs `(f(M), f(N ∪ {a}))` per `a ∈ M` (Kapur Lemma 4.1(ii)) and nilpotency order `n` the
pairs `(f(N ⊎ {a: n−m}), f((M − {a: m}) ⊎ {e}))` per summand (Lemma 4.2(ii)/4.5). These
are *cross-rule* consequences the within-monomial clamp cannot produce — e.g.
`or(a,b)=c ⟹ or(a,c)=c` and `xor(a,b)=c ⟹ xor(a,c)=b` were underivable before the axiom
pairs were added to `cc_round` (Kapur-conformance fix W3 (spec §3 table); fixtures `aci_rule_axiom_cp.egg`,
`nilpotent_rule_axiom_cp.egg`, `nilpotent3_rule_axiom_cp.egg`; ground-truth checker
`cc_axiom_cps_nonjoinable`, asserted under `CHECK_AC_BASIS`). Identity needs no axiom
pairs (Lemma 4.3) — provided the unit-drop also runs on the recanonize path, which is the
companion W2 fix (`CanonMode.unit` + the became-a-unit sweep).

## Numbers for laws, ids for entities (why `order: u8`, why the unit is a node)

A recurring reading question: why is the nilpotent order a plain `u8` while the identity
and the inverse are ids? Because the pieces of an algebraic law have different natures,
and each is stored as what it IS:

- **The order `n` in `xⁿ = e` is arithmetic.** Its only use is as the modulus in the
  count clamp (`count % n`). No e-node denotes it — there is nothing in the graph to
  point AT — so a node-id type would be a category error. `u8` is the "orders are tiny"
  choice (xor = 2); the one known consequence is that encoding `bvadd(N)`'s additive
  torsion as nilpotency of order `2^N` needs `N < 8`, so widen to `u32` if bitvector
  modeling ever lands (a four-site mechanical change: the `Clamp` field, `MSetClamp`,
  the two clamp functions, the tag parser). The surface `Option<u8>` is only a parsing
  default: bare `:nilpotent` means order 2.
- **The identity `e` and the inverse operator ARE graph entities**, and they are stored
  as such — a resolved node id (`unit_node`) and op id (`inverse_op`) in egraph-side
  per-op maps with the same semi-persistence as the rest of the graph. They live OFF the
  `OpKind` descriptor deliberately: `OpKind<S>` is generic over sorts only and cannot
  carry a `Cfg::G`/`Cfg::O`, which is also why the descriptor holds a *deferred*
  `UnitRef` (a term to resolve at registration) rather than a node.

## Type-width rationale (every numeric choice, and why it is sufficient)

Audited 2026-07-11. The rule of thumb from the previous section (numbers for laws, ids
for entities) plus one more: every width is justified either by a HARD bound (checked or
structural) or by a PHYSICAL bound (memory exhausts first); no width relies on "probably
big enough" without an argument.

| Type | Width | Sufficiency argument |
|---|---|---|
| ids (`Cfg::G`/`Cfg::O`/`Cfg::S`) | **generic** via `EGraphConfig` — the engine never names a concrete id type (verified: zero hard-coded id uses in production code; tests bind a config, `literal.rs` has one overridable default param). `DefaultConfig`/`EGraph31` binds the 31-bit family (u32, bit 31 = capture flag); `EGraph63` binds 64-bit; `--id-bits` selects at runtime | for the 31-bit binding: ids are dense arena indices; 2³¹ nodes at ≥16 B/node ≥ 32 GB — memory exhausts first, and the 63-bit binding is the escape hatch. Width is a CONFIG choice, not an engine constant. |
| `RuleId`/`AxiomId` | 15-bit (u16, flag bit) | rules/axioms are program-declared; 32 767 is the tightest ceiling in the system — fine for written programs, the one to widen first if rule GENERATION ever lands. |
| `Multiplicity` | u32 (also the stored `Cfg::M` in both id widths — no narrowing) | counts originate from a built child list (a count of k requires a k-element `add` call: 4 B/child ⇒ 2³² copies ≈ 16 GB in one call) and completion never inflates them: `normalize` hosts only shrink (admissible order), `lcm` takes max, the (C2) join adds two rule sizes, axiom/per-constant pairs add ≤ order. Debug builds panic on overflow; release wrap is physically unreachable. |
| `multiset_size` | u64 accumulator | worst case 2³¹ distinct summands × u32::MAX counts ≈ 2⁶³ — fits u64 exactly; u32/usize would not. |
| `Clamp::Nilpotent.order` | u8 | previous section; widen to u32 only for the postponed `bvadd` 2^N torsion encoding. |
| `GUARD_MAX_REWRITES` | usize = 1 000 000 | policy backstop, not a bound: termination is a theorem (admissible order), the cap only catches a mis-oriented rule and debug-asserts. |
| `DEFAULT_COMPLETION_NODE_BUDGET` | usize = 50 000 | policy: divergence bail (sound-but-incomplete, reported via `CompletionOutcome::AbortedGrowthLimit`); configurable per-egraph (`set_completion_node_budget`); granularity caveat in review-debt §1. |
| flatten cap `1 + 64·node_count` | usize | 64 × 2³¹ = 2³⁷ needs a 64-bit usize — fine on supported targets; would overflow on 32-bit (not a supported deployment). |

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
      MSet { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool }, // ℕ / mod-n
      Set  { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool }, // {0,1}
  }
  enum Clamp { None, Idempotent, Nilpotent { order: u8 } }  // unified, on BOTH variants
  // clamp and identity are representation-independent fields on both variants.
  ```

  Note (2026-07-10): the resolved `:inverse` OPERATOR ID is deliberately NOT an `OpKind`
  field — `OpKind<S>` cannot carry an op id. Like the resolved identity node, it lives in
  an egraph-side per-op map (`inverse_op`, same semi-persistence as `unit_node`), consumed
  by inverse-PAIR cancellation (`x ∘ inv(x) = e`, at build and on completion normal
  forms). Full Abelian-group completion (§5.4 signed counts / Gaussian elimination) is
  postponed indefinitely — the signed-count sketch further down describes that postponed
  design, not the shipped mechanism.

  The clamp is a *unified* field on both variants (the 2026-07-01 correction above): partition is
  derived from the resolved clamp — `Idempotent → Set`; `None` / `Nilpotent → MSet`. The resolver
  is the single point that enforces the legal (clamp, partition) pairings; a `MSet { clamp:
  Idempotent }` or `Set { clamp: Nilpotent }` is never constructed. `OpInfo::canon_class` projects
  `OpKind` down to the bare `ENodeKind` for routing (`MSet { .. } → ENodeKind::MSet`, `Set { .. } →
  ENodeKind::Set`), and completion reads the clamp via `op_clamp` regardless of partition.

A separate `Map<OpId, AcAlgebra>` was considered and rejected: it adds a second lookup and a second
source of truth that must stay in sync with the representation tag. `AcAlgebra` is a couple of enum
bytes plus an `Option<UnitRef>`, immutable after registration, so co-locating it on `OpKind` (the
existing per-op record, read by op id only where completion needs it) is strictly simpler.

**In scope now:** `OpKind::MSet { clamp: None }` (AC), `OpKind::Set { clamp: Idempotent }` (ACI),
`OpKind::MSet { clamp: Nilpotent }` (XOR), and identity on either. Group: the `:inverse`
tag is validated and consumed at pair-cancellation level (2026-07-10); the signed-count
representation this section sketches is the POSTPONED full-group design, not shipped.

## Storage: one pool of node ids, fixed-width rows over a strongly-typed op array

### Entries are global node ids, never materialized sets/multisets

Each per-class min-monomial entry is a `Cfg::G` pointing at a real member node (an AC node for
an AC column, an ACI node for an ACI column). The monomial is recomputed on read by
dereferencing the id (`node_monomial_into` → `ac_children` for AC, `aci_children` for ACI).
Rationale, identical to the single-op slot today (design §9a):

- The id is the canonical handle: children are read through `find_const`, so multiplicities and
  membership are always live. A stored multiset would go stale the moment a child class merges
  and would need re-canonicalization anyway.
- The minimum monomial is always *some member node's* monomial (the leximin representative is a
  class member), and completion's materialized reducts are real nodes (`materialize` calls
  `eg.add`). So no min is ever a synthetic multiset with no backing node; an id always suffices.
- It matches the shipped design exactly: today `min_monomial: T` is one node id and `class_rhs_into`
  dereferences it. The pool holds `nb_completion` such ids per class instead of one.

### The column → op reference array (strongly typed `OpId`, no `u16` slots)

There is **one** pool. Each class's row is `nb_completion = nb_ac + nb_aci` columns wide, one
column per registered AC and ACI op. Column meaning is given by a single reference array of
strongly-typed op ids, in registration order:

```
// Built once (in the registry, or on the egraph), len = nb_completion:
completion_ops: Vec<Cfg::O>     // e.g. [op_+, op_*, op_and, op_or]
//                                column:  0      1      2       3
```

So `pool[base + i]` is the ≫_f-least monomial node for op `completion_ops[i]`. To find a node's
own column, map its `OpId` → column `i` (store `i` on `OpInfo`, or reverse-scan the tiny
`completion_ops`). No integer slot id is stored anywhere; the only integer is the column
position `i`, used as `base + i` pool arithmetic.

The op registry is a `Map<String, OpInfo>` that only ever appends (`insert` + `log_len`); ops
are never renumbered, so `completion_ops` is stable for the life of the run: column `i` always
means the same op. **Kind is derived, not stored:** `ops.info(completion_ops[i]).kind` says AC
vs ACI. There is no separate kind tag and no second pool — the column already identifies the op,
and the op identifies the kind.

The foolproof check at every pool read/write:
`debug_assert!(node_op(pool[base + i]) == completion_ops[i])`. A `*`-node can never sit in the
`+` column without tripping it. This replaces any positional convention with a stored fact the
code verifies, against the strongly-typed array.

### Layout

```
EClasses {
    min_pool: VecI<Opt<Cfg::G>, usize, TRACK>,   // flat, rows of width nb_completion
}
ClassData { use_list: L, min_row: <off|absent>, atomic: bool }
```

Entries are `Opt<Cfg::G>` (niche-tagged absent, the `Opt<N>` form already used in
`containers/list.rs`), absent = "this class holds no monomial for this op yet". Not a raw `G`
with a magic sentinel. `min_row` is absent for a class that holds no AC/ACI monomial at all (the
majority — they get no row and cost nothing).

A row mixes AC and ACI columns (`[ac_min_+, ac_min_*, aci_min_and, aci_min_or]`); they are all
`Opt<Cfg::G>` node ids, homogeneous storage. The per-column *semantics* (AC multiset-ℕ vs ACI
set-{0,1}) is a read-time property looked up from `ops.info(completion_ops[i]).kind`, not a
property of which pool the id lives in. So one pool keeps the per-kind clamp; it just resolves
the clamp from the op rather than from a pool identity. The cross-kind absent columns (a
Bool-sorted class carrying empty `+`/`*` columns, say) are a few `Opt` slots per row in a row
that is only `nb_completion ≈ 2–4` wide — negligible, and only classes that hold *some* AC/ACI
monomial get a row at all.

This mirrors `VariableArityCache` (`caches.rs`): offsets into a flat semi-persistent pool,
append-on-allocate. Row width is fixed (`nb_completion`), so the span is just an offset.

- **Lazy allocation.** The first time a class gains any AC/ACI monomial, append `nb_completion`
  absent entries to `min_pool` and store the offset in `min_row`.
- **Merge mutates the survivor row in place** (`min_pool.set(base + i, …)`), captured/restored
  by the semi-persistent `VecI`. The pool grows only on first-AC/ACI-monomial-per-class, never on
  merge, so it is bounded by `nb_completion × (classes holding any AC/ACI monomial)`.

### Row width vs. late op registration

A row's width is `nb_completion` at allocation time. If a new AC/ACI op is registered *after*
some class already has a row, existing rows are too narrow. Two handlings:

- **Declare-before-build invariant (chosen).** Ops are declared up front (the `.egg` program
  declares all functions before building terms), so `nb_completion` is fixed before the first
  AC/ACI monomial appears. Assert it: once any AC/ACI node exists, registering a new AC/ACI op is
  rejected. Matches every existing fixture and the same declare-timing reason the current
  single-AC guard lives at point-of-use in `rebuild`.
- **Migrate-on-grow (fallback).** If `nb_completion` increases while rows exist, do a one-time
  pool rebuild widening every row. The pool is small and the event is rare. Adopt only if
  push/pop ever interleaves op declaration with term construction.

### Fixed-width rows, not variable-width slices

A variable-width slice (listing only the `(op, node)` pairs a class actually holds) is sparser,
but merge would have to append a fresh unioned row and repoint the offset whenever the survivor
gains a new op, growing the pool per merge. With `nb_completion` tiny, fixed-width rows with
in-place merge are simpler and keep pool growth off the merge path. Use fixed-width.

### The accessor everyone goes through

```
fn min_mono(&self, op: O, repr) -> Option<Cfg::G>
fn set_min_mono(&mut self, op: O, repr, node: Cfg::G)
```

`min_mono` maps `op` → its column `i` (via `OpInfo` or a scan of `completion_ops`), then reads
`min_pool[min_row + i]`. Single-op AC today is the `nb_completion == 1`, `i == 0` special case,
so the migration is mechanical: route the existing `min_monomial`/`set_min_monomial` calls through
`min_mono`/`set_min_mono` first with no behavior change, then widen the row and admit ACI ops.

## Invariants that keep the pool sound

1. **`min_pool[base + i]` holds only a node of op `completion_ops[i]`.** It is written only by
   `set_min_mono(op, …, node)` after mapping `op → i`, and
   `debug_assert!(node_op(pool[base + i]) == completion_ops[i])` confirms it on read and write. A
   `*`-node can never appear in the `+` column. The op is the column (the strongly-typed
   `completion_ops` array); the kind is `ops.info(completion_ops[i]).kind` — both derived facts,
   not positional convention.
2. **The monomial read is kind-correct.** AC coalesces multiplicities (`ac_children`); ACI
   dedups to multiplicity 1 (`aci_children`). The column's op (hence kind) selects the
   semantics; `node_ref` confirms it.
3. **`monomial_cmp` only ever compares within a column.** The merge fold is element-wise per
   column `i`: keep the `monomial_cmp`-smaller of `survivor[base+i]` and `absorbed[base+i]`,
   absent = +∞. Both operands are column `i`, hence the same op, hence the same kind — never a
   multiset against a set. The fixed column layout enforces this structurally; the comparison
   never crosses kinds.
4. **`atomic` stays a single per-class bool.** If a class is referenced as a child anywhere,
   `{class}` is a real atom usable in *any* op's monomials, so the flag short-circuits the
   per-op min regardless of kind. It is not per-op.
5. **Staleness handled as today.** A stored min may go stale under a merge cascade; the
   read-time orientation guard (design §9b axis-2) already makes that safe and is unchanged.

## How AC uses the pool

Nothing about the algorithm changes; only storage reads/writes index by op through the column
array.

- **RHS read** (`class_rhs_into`): the empty monomial if the class is the op's identity
  class (Kapur's `f({}) = e` — the normative RHS definition is `ac-completion-spec.md` §1);
  else if `atomic` → `{class}`; else `min_mono(node's op, repr)` (column `i`) → emit that
  node's monomial. For a real rule, the `node` is itself a column-`i` node, so the slot is
  non-absent.
- **Merge fold** (`fold_min_monomial`): element-wise over the row (invariant 3), OR the `atomic`
  bool. `MergeInfo` carries the absorbed class's row offset so the survivor can fold it.
- **Completion loop**: drop the `mset_op_count() <= 1` guard. Build rules from all AC nodes as
  today; each `Rule` already carries its op, and superposition/normalization already filter by
  op (`rj.op == rules[i].op`), so two ops produce two non-interacting rule sets sharing the
  constant pool. The cross-op `a+b = a*b` case is one e-class holding a `+`-node and a `*`-node,
  each reducing to the class via its own column; union-find records the equality (Kapur's
  shared-constant case, dissolved for free).

## How ACI uses the pool, and the one difference

ACI uses its own columns (one per ACI op) with two localized changes:

1. **Set monomials.** ACI children are bare `G` with multiplicity always 1 (`nodes.set`). So an
   ACI node's monomial emits each class with count 1, and `monomial_cmp` over an ACI monomial is
   the degree-lex applied to the deduplicated element set (every count 1 — so "size" is the
   number of distinct elements).
2. **Idempotent normalization.** The I axiom clamps every count to 1 after each rewrite step.
   The superposition arithmetic is the same shape (lcm = union, subtract, normalize); the AC
   primitives in `multiset.rs` (`multiset_union`/`multiset_lcm`/`normalize_ms`) gain an
   idempotent variant that clamps counts to {0,1}. This is the multiplicity-clamp parameter
   from the table above — one `clamp: fn` per completion-op, ℕ for AC and {0,1} for ACI.

Then completion runs over the ACI partition the same way it runs over AC: iterate `nodes.set`
as candidate rules, superpose same-op pairs, normalize reducts (set semantics), merge differing
normal forms, collapse reducible rules. Completeness is identical to AC because Kapur treats
idempotency as a property of the AC symbol, not a new procedure. `completion_node_ids()` (egraph.rs)
generalizes to a `completion_node_ids()` that walks both the `ac` and `aci` partitions and tags
each node with its `(op, kind)`.

Note ACI's idempotence critical pair (plan §0 item 2: `f(M ∪ {a})` vs `f(M)` for `a ∈ M`) is
subsumed by clamping in normalization: a reduct that repeats a summand normalizes to the
deduplicated set, which is exactly that critical pair's join. So no special pair-generation is
needed beyond running the standard loop with the idempotent clamp.

## Semi-persistence

`min_pool` is a `VecI`, marked/restored like `children` in `VariableArityCache` (the
`PoolCacheToken` pattern). `EClasses::mark/restore` gains the pool. In-place row mutation on
merge is first-write-wins captured per entry, so restore reverts row contents, and the
`SparseSet` revert restores each class's `min_row` offset. Pool and offset roll back together,
the same consistency the current single-slot design relies on.

## Surface language: composable property tags

Today the surface declares algebra with pre-combined tags that map one-to-one onto an `OpKind`
(`parser.rs` `AlgAttr`, dispatched in `sortcheck.rs`):

```
:comm  :assoc  :assoc-left  :assoc-right  :assoc-comm  :assoc-comm-idem
```

That does not compose: every new combination (nilpotent, identity, group) would need its own
pre-combined tag. Replace it with **orthogonal basic tags** and derive `OpKind` + the set/mset
representation from the combination. Properties that need a value take a ground argument.

```
(function +    (Int)  Int  :assoc :comm)                        ; AC, multiset
(function and  (Bool) Bool :assoc :comm :idempotent)            ; ACI, set (clamp to 1)
(function -    (Int)  Int  :assoc-left)                         ; A-only, unchanged
(function xor  (Bool) Bool :assoc :comm :nilpotent :identity (false))  ; MSet, mod-2 clamp
(function +    (Int)  Int  :assoc :comm :identity 0)            ; AC + unit drop
```

### Derivation from tags

| tags                            | OpKind        | representation     | normal-form merge        |
|---------------------------------|---------------|--------------------|--------------------------|
| `:assoc-left` / `-right` / `:assoc` | A         | sequence           | flatten                  |
| `:comm` (binary)                | C             | pair               | reorder                  |
| `:assoc :comm`                  | AC            | **multiset** (ℕ)   | union                    |
| `:assoc :comm :idempotent`      | ACI           | **set** ({0,1})    | union, clamp to 1        |
| `:assoc :comm :nilpotent`       | nilpotent     | **multiset** (mod-n clamp; the 2026-07-01 correction) | symmetric difference (n=2) |
| + `:identity e` on any AC row   | (same)        | (same)             | additionally drop `e`    |

### Which properties take a parameter, and which are baked in

The rule: a property needs a parameter iff its reduction target names a term the engine cannot
derive structurally.

| property      | parameter                       | baked? | why                                                              |
|---------------|---------------------------------|--------|------------------------------------------------------------------|
| `:comm`       | none                            | yes    | structural (reorder children)                                    |
| `:assoc`      | direction only (A-only)         | yes    | structural (flatten)                                             |
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

Parameter syntax: a value-taking tag is followed by a **ground term of the op's return sort** —
`:identity 0` (literal) or `:identity (zero)` (nullary constant application), `:nilpotent` (order
2 default) or `:nilpotent 3`, `:inverse neg` (names the unary inverse op). This is not a
new literal syntax: the tag argument is an ordinary surface term, parsed by the existing term
grammar (`Term::Lit` / `Term::App`).

### Resolve free tags into a closed descriptor (the choke point)

Free composition at the surface, but resolved **once at registration** into a closed, validated
descriptor that the rest of the engine matches on. Not a fixed menu of compound tags (does not
compose), and not on-the-fly re-derivation at each read site (re-introduces the late-validation /
recomputed-representation bugs the `completion_ops` array exists to remove). The resolver is the
single place that maps a tag set to:

```rust
enum AcRepr  { Multiset, Set }                              // child storage: (G, u32) vs bare G
enum AcClamp { None, Idempotent, Nilpotent { order: u8 } }  // count clamp in the normal form
struct AcAlgebra {
    repr: AcRepr,                  // a function of `clamp`, stored so dispatch is one match
    clamp: AcClamp,
    identity: Option<UnitRef>,     // resolved unit, required by Nilpotent, optional drop for AC
    // inverse: Option<Cfg::O>,    // future: group
}
```

`repr` is derived (`Idempotent` → `Set`; `None` / `Nilpotent` → `Multiset` — the 2026-07-01
correction: dedup would destroy the run-lengths the mod-n clamp needs), stored explicitly so
every downstream site is a single exhaustive match on `AcAlgebra`, never a re-derivation from
tags. `AcAlgebra` is stored on `OpInfo`. Invalid tag combinations are rejected here and become
unrepresentable downstream.

This lands on the existing structure with no new partition: `AcRepr::Multiset` routes to
`nodes.mset` (`(G, mult)` children), `AcRepr::Set` to `nodes.set` (bare `G`). Plain AC and
nilpotent **share** the multiset partition (nilpotent needs true multiplicities before the mod-n
clamp) and differ only in the `AcClamp` the canonicalizer/merge reads — none for plain AC,
mod-n for `Nilpotent`; idempotent is the one `Set` case (dedup IS its clamp).

### Validation at registration

- `:idempotent` and `:nilpotent` are mutually exclusive (cannot clamp to 1 and reduce mod 2).
- `:idempotent` / `:nilpotent` require `:assoc :comm` (the monomial machinery is AC-based).
- `:nilpotent` requires `:identity` (it needs the unit to reduce to).
- `:inverse` requires `:identity` (an inverse cancels *to* the unit).
- `:idempotent` and `:inverse` are **mutually exclusive** — not merely unimplemented, but algebraically
  incoherent. See "Inverse is a group inverse, not a complement" below: an idempotent group is trivial,
  so an idempotent AC op has no non-trivial inverses. This rejects `and`/`or` + `:inverse` at the
  resolver (the intended `not`/complement is a *different* structure — model it as `xor`).
- `:identity e` must sort-check `e` to the op's return sort.

### The unit is a deferred ground term, not a node built at registration

`:identity e` does not need new literal machinery and must **not** build a node during
registration. The unit is just a ground term, and every step that turns a ground term into a node
already exists; the only question is *when* to run it.

- A literal unit (`0`, `true`, `#b0000`) lexes as `Term::Lit` (`parser.rs` `is_literal`),
  sort-checks through `LitValParser::parse(tok, sort)` (`literal.rs`) into a `LitVal`, and builds
  via `lit_op_for_sort(sort)` + `add_lit` (`interpret.rs`) — the identical path every program
  literal already takes. Bitvector units need only a `parse_bv` registered on the BV sort, which
  BV literals in programs require anyway; nothing identity-specific.
- A constructed unit (`(zero)`) is a `Term::App` over a previously declared nullary op, built by
  the ordinary term builder.

Registration today is side-effect-free on the e-graph (`register_*` adds no nodes). Keep it that
way: store the unit on the descriptor as a **deferred** `UnitRef` (the parsed `CTerm`, or the
`LitVal` + sort for the literal case), sort-checked but **not** built. Materialize it to a
`Cfg::G` lazily on first completion use (or once, just before the first completion-enabled
`rebuild`), then cache the id. This avoids a forward reference that would build a node before the
graph is ready, sidesteps op-declaration ordering hazards (the unit's lit op / constructor only
needs to exist by materialization time, not registration time), and means the in-scope work
(which does not run nilpotent/identity completion) carries the resolved-but-unbuilt unit with
zero runtime cost.

Doing this now — parse `:identity <term>`, sort-check it, store the deferred `UnitRef` on the
descriptor — is the point of building the grammar and resolver up front: it fixes the surface and
the storage shape so adding nilpotent/identity completion later is materialize-and-clamp, not a
grammar or descriptor migration. That is the technical debt this avoids.

### Inverse is a group inverse, not a complement (why `not` is not an `and`-inverse)

`:inverse` means a **group inverse**: a unary op `x⁻¹` with `x ∘ x⁻¹ = e`, where `e` is the
operator's own **identity**. Under completion this lifts a summand's count to ℤ and cancels a
summand against its inverse (`a + (−a) → 0`). Three points fix what this is and is not.

**1. It only exists for the multiset (non-idempotent) operators.** The clean cases:

| op  | identity `e` | inverse `x⁻¹` | `x ∘ x⁻¹` | signed count means | notes |
|-----|--------------|---------------|-----------|--------------------|-------|
| `+` | `0`          | `−x` (`neg`)  | `0` = `e` ✓ | integer coefficient | *the* group case; abelian group |
| `*` | `1`          | `1/x` (`recip`) | `1` = `e` ✓ | exponent           | **partial** (`0` has no inverse); `*` also has annihilator `0` (treat opaque); distribution is cross-op (a ring), out of scope |

So `a + a + neg(a)` reads as `{a: +2, a: −1} = {a: +1} = a`, and `a + neg(a)` reads as `{} = 0`.
This is the same "store honest + unsigned, interpret at completion" shape as nilpotent (§ the
2026-07-01 correction): the node `neg(a)` is a real child; completion *recognizes* it as `−a` and
signs the count, the store never holds a negative multiplicity.

**2. Idempotent + inverse is incoherent, so it is rejected — this is why `not` is not an
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
own additive inverse (`x ⊕ x = 0`) — so xor's "inverse" is already covered by the nilpotent clamp
shipped in property 2, with no signing needed. Net: complementation is modeled as `xor` with the
constant `true` (available today), never as an inverse on `and`.

### Scope and compatibility — SUPERSEDED (2026-07-10): everything below is wired

*(Original staging text retained for the record.)* Current state: `:identity` and
`:nilpotent` are fully wired (canonization + completion, 2026-07-09 series);
`:cancellative` drives the Kapur §5 cancel-closure and `:inverse` (implying cancelative)
drives inverse-pair cancellation (2026-07-10); full Abelian-group completion is postponed
indefinitely. The aliases `:assoc-comm` / `:assoc-comm-idem` remain accepted. Original:
wire only `:assoc`+`:comm` and `:assoc`+`:comm`+`:idempotent` to actual completion now;
`:nilpotent`, `:identity`, `:inverse` parse, sort-check, validate, and store on the
descriptor but are recorded as not-yet-completed.

## SMT-LIB AC operator survey

All AC (associative *and* commutative) operators across the standard SMT-LIB theories, with the
representation the design above assigns. Operators that are A-only, C-only, or neither are listed
as exclusions per theory. The `repr` column drives child storage: **set** = bare `G` children,
**mset** = `(G, u32)` children.

### Core (Bool)

| op           | A | C | identity | idempotent | nilpotent | repr |
|--------------|---|---|----------|------------|-----------|------|
| `and` (∧)    | ✓ | ✓ | `true`   | ✓          | —         | set  |
| `or` (∨)     | ✓ | ✓ | `false`  | ✓          | —         | set  |
| `xor` (⊕)    | ✓ | ✓ | `false`  | —          | ✓         | set (sym-diff) |

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
| `bvxor`  | ✓ | ✓ | `0`        | —          | ✓         | set (sym-diff) |
| `bvxnor` | ✓ | ✓ | all-ones   | —          | ✓         | set (sym-diff) |
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
  `bag.union_max`, `bag.inter_min`, `re.union`, `re.inter`, `min`, `max` — the idempotent
  (union-clamp) operators.
- **mset** (`(G, u32)`, ℕ counts): `+`, `*`, `bvadd`, `bvmul`, `bag.union_disjoint` (plain AC),
  **plus the nilpotent family** (`xor`, `xnor`, `bvxor`, `bvxnor`) — stored MSet with the mod-n
  clamp (symmetric difference at n=2), per the 2026-07-01 correction.
- **signed mset** (ℤ counts): only if abelian groups are ever modeled (out of scope).

Implemented: set-idempotent (ACI: `and`, `or`, …), multiset (AC: `+`, `*`, …), and the
nilpotent family (MSet + mod-n clamp + declared unit). The signed-count group representation
remains out of scope (shipped group support is inverse-PAIR cancellation).
