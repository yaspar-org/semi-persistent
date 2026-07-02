# Multiple AC and ACI symbols: completion via a per-op min-monomial pool

Status: design converged, not yet implemented. This is the plan to lift the two standing
limitations recorded in
[ac-congruence-completeness-plan.md](ac-congruence-completeness-plan.md) §0 items 1 and 2:
completion supports a single AC symbol and runs no completion at all for ACI. Both are the
same storage upgrade plus, for ACI, one parameterized normalization step. Read the design doc
§9a (the `min_monomial`/`atomic` per-class slot) and §9b axis-1 (the storage options) first; this
plan picks option 3 and fills in the ACI specifics.

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

1. **Count domain = the storage representation (MSet vs Set).** Either counts are unbounded in ℕ
   (**MSet**, children stored as `(G, u32)`) or bounded to {0,1} (**Set**, children stored as bare
   `G`). This is the only axis the *routing/storage* layer cares about.
2. **Why a Set is a Set = the Set clamp (idempotent vs nilpotent).** A {0,1} bound arises two ways:
   idempotency (`x∘x = x`, clamp count to 1, merge = union-clamp) or nilpotency (`x∘x = e`, count
   mod 2, merge = symmetric difference). This axis exists **only for Set**; an MSet op by definition
   has no count clamp (that is what keeps its counts in ℕ). So "do we need a clamp over MSet?" — no,
   a count-clamped MSet *is* a Set.
3. **Identity = a dropped unit element, orthogonal to both, on either representation.** A
   distinguished element `e` whose multiplicity is forced to 0 (removed) wherever it appears.
   Applies to MSet (`+` with `0`, `*` with `1`) **and** Set (`and` with `true`, `or` with `false`).
   It is *not* a count clamp and *not* Set-only; it is a separate optional field.

| op family    | count domain | Set clamp        | identity      | example                    |
|--------------|--------------|------------------|---------------|----------------------------|
| plain AC     | ℕ  (MSet)    | —                | optional      | `+`, `*`                   |
| idempotent   | {0,1} (Set)  | Idempotent       | optional      | `and`, `or`: `a∘a → a`     |
| nilpotent    | {0,1} (Set)  | Nilpotent (mod n)| **required**  | `xor`: `a⊕a → e`           |
| group        | ℤ  (MSet±)   | — (signed)       | required + inv| abelian `(+,0,−)`          |

So XOR is a **Set**, not a multiset: symmetric difference maps two sets to a set directly and never
materializes count 2. "Add then clamp mod 2" and "symmetric difference" compute the same thing, but
the second stays in {0,1} at every step. The naïve expectation that XOR needs a multiset (to add
then reduce mod 2) is wrong for exactly this reason. Nilpotency *requires* an identity because the
emptied monomial `{}` (`a⊕a`) must canonicalize to a real node, the unit.

The representation choice matters for memory: an MSet child is `(G, u32)` (the multiplicity is
`u32`, see `multiplicity.rs` — *not* the 128-bit literal value, which is unrelated) versus a bare
`G` for a Set child. At 31-bit `G` that is 8 bytes vs 4, a ~2x per-child overhead the Set ops
should not pay. The completion *pool* is unaffected either way (it stores node ids); the node child
storage picks MSet vs Set from the op (the existing `nodes.mset`/`nodes.set` partitions, renamed to
representation names — see below).

**In scope to implement now:** plain AC = MSet with no identity, and idempotent = Set with no
identity. Nilpotent, identity, and group are recorded so the descriptor has the right *shape* (the
clamp is a Set-only axis, identity is a both-representations field); none of the three is built or
promised here.

See the SMT-LIB operator survey at the end of this doc for which real operators land in each
representation.

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
      MSet { arg_sort: S, identity: Option<UnitRef> },                   // ℕ counts; was AC
      Set  { arg_sort: S, clamp: SetClamp, identity: Option<UnitRef> },  // {0,1} counts; was ACI
  }
  enum SetClamp { Idempotent, Nilpotent { order: u8 } }   // Set-only: why counts are bounded
  // identity is a separate, representation-independent field on BOTH variants.
  ```

  `Set { clamp, .. }` literally cannot exist without a clamp and `MSet` cannot carry one, so the
  representation-vs-clamp consistency is a type invariant, not a cross-map rule. `OpInfo::canon_class`
  projects `OpKind` down to the bare `ENodeKind` for routing (e.g. `MSet { .. } → ENodeKind::MSet`).

A separate `Map<OpId, AcAlgebra>` was considered and rejected: it adds a second lookup and a second
source of truth that must stay in sync with the representation tag. `AcAlgebra` is a couple of enum
bytes plus an `Option<UnitRef>`, immutable after registration, so co-locating it on `OpKind` (the
existing per-op record, read by op id only where completion needs it) is strictly simpler.

**In scope now:** `OpKind::MSet { identity: None }` (AC) and `OpKind::Set { clamp: Idempotent,
identity: None }` (ACI). `SetClamp::Nilpotent`, non-`None` `identity`, and group are shape-only.

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

- **RHS read** (`class_rhs_into`): if `atomic` → `{class}`; else `min_mono(node's op, repr)`
  (column `i`) → emit that node's monomial. For a real rule, the `node` is itself a column-`i`
  node, so the slot is non-absent.
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
   the degree-lex with every count 1 (set comparison).
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

## Out of scope

- **Distributivity** (`*` over `+`): a user rewrite rule (Kapur §6, the Gröbner recasting), not
  AC-CC. Unchanged from today.
- **Identity, nilpotency, cancellativity, group**: further per-pool clamps/rules in the same
  shape (the multiplicity-clamp table). The pool design leaves room without structural change,
  but none is built or promised here. Only AC (ℕ) and ACI ({0,1}) are in scope.

## Build order (each step a self-contained clean build passing all tests)

1. **Surface tags + resolver + descriptor (done up front, to avoid migration debt).** Replace the
   pre-combined `AlgAttr` with composable basic tags (`:assoc`, `:comm`, `:idempotent`,
   `:nilpotent`, `:identity <term>`, plus `:assoc-left`/`-right`), keeping `:assoc-comm` /
   `:assoc-comm-idem` as aliases. Add the registration-time resolver `tags → AcAlgebra` with all
   validation, store `AcAlgebra` (including the deferred `UnitRef`) on `OpInfo`. Map
   `AcRepr::Set`/`Multiset` to the existing `OpKind`/partition. No completion behavior change:
   `{Multiset,None}` and `{Set,Idempotent}` resolve exactly to today's AC/ACI; nilpotent/identity
   resolve, store, and report not-yet-completed. Parse-and-resolve tests for every tag combination
   (including the rejected ones) and the deferred-unit storage.
2. **Registry completion array.** Build `completion_ops: Vec<Cfg::O>` (AC then ACI ops in
   registration order), store each AC/ACI op's column on `OpInfo` (or map by scanning), add
   `aci_op_count()` and a unified completion-op iterator over AC ∪ ACI. Add the
   declare-before-build assert (reject a new AC/ACI op once a node of that kind exists). No
   behavior change to completion yet.
3. **Storage refactor at `nb_completion == 1`.** Add `min_pool`, change `ClassData` to `min_row`
   (drop `min_monomial: T`), route existing single-op reads/writes through `min_mono`/`set_min_mono`.
   Pure refactor: all tests green, no new behavior. This isolates the risky storage change from
   new behavior.
4. **Multi-AC.** Widen the row to all AC ops; generalize `fold_min_monomial`, `class_rhs_into`, and
   the completion loop to per-column reads; remove the single-AC guard (and its two guard tests).
   Add a multi-AC test (`+` and `*` with a shared constant, e.g. assert `a+b = a*b` and check it
   does not corrupt either op's completion). Extend the `ac_vs_rules` harness to two ops.
5. **ACI completion.** Admit ACI ops into `completion_ops` (their columns in the same row); add
   the idempotent-clamp normalization variant in `multiset.rs`; make `completion_node_ids()`
   walk the ACI partition; run the round over ACI ops with the set monomial reads and the {0,1}
   clamp (selected per column from the op's `AcAlgebra.clamp`). Add `and`/`or` completion tests
   (including the idempotence join `a∘a∘b = a∘b` and a multi-ACI case, since two ACI ops are
   currently allowed but un-completed).

Steps mirror the bisectable-commit discipline from the merged AC-completion PR: each commit
builds clean and passes the full suite, with step 3 the storage change carrying no behavior delta
so a bisect can pinpoint a regression to either storage or the per-op generalization. Step 1 is
pure surface/resolver plumbing with no completion change, landed first so the grammar and
descriptor never need a later migration.

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
(function xor  (Bool) Bool :assoc :comm :nilpotent :identity (false))  ; set (mod 2) [future]
(function +    (Int)  Int  :assoc :comm :identity 0)            ; AC + unit drop [future]
```

### Derivation from tags

| tags                            | OpKind        | representation     | normal-form merge        |
|---------------------------------|---------------|--------------------|--------------------------|
| `:assoc-left` / `-right` / `:assoc` | A         | sequence           | flatten                  |
| `:comm` (binary)                | C             | pair               | reorder                  |
| `:assoc :comm`                  | AC            | **multiset** (ℕ)   | union                    |
| `:assoc :comm :idempotent`      | ACI           | **set** ({0,1})    | union, clamp to 1        |
| `:assoc :comm :nilpotent`       | set-nilpotent | **set** ({0,1})    | symmetric difference     |
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
2 default) or `:nilpotent 3`, `:inverse neg` (names the unary inverse op, future). This is not a
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

`repr` is derived (`Idempotent` | `Nilpotent` → `Set`; `None` → `Multiset`), stored explicitly so
every downstream site is a single exhaustive match on `AcAlgebra`, never a re-derivation from
tags. `AcAlgebra` is stored on `OpInfo`. Invalid tag combinations are rejected here and become
unrepresentable downstream.

This lands on the existing structure with no new partition: `AcRepr::Multiset` routes to
`nodes.mset` (`(G, mult)` children), `AcRepr::Set` to `nodes.set` (bare `G`). Idempotent and
nilpotent **share** the set partition (both have {0,1} normal-form counts) and differ only in the
`AcClamp` the canonicalizer/merge reads — dedup for `Idempotent`, pair-cancel for `Nilpotent`.

### Validation at registration

- `:idempotent` and `:nilpotent` are mutually exclusive (cannot clamp to 1 and reduce mod 2).
- `:idempotent` / `:nilpotent` require `:assoc :comm` (the monomial machinery is AC-based).
- `:nilpotent` requires `:identity` (it needs the unit to reduce to).
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

### Scope and compatibility

Wire only `:assoc`+`:comm` (→ `AcAlgebra { Multiset, None }`, AC) and
`:assoc`+`:comm`+`:idempotent` (→ `{ Set, Idempotent }`, ACI) to actual completion now.
`:nilpotent`, `:identity`, `:inverse` parse, sort-check, validate, and store on the descriptor
(including the deferred `UnitRef`) but are recorded as not-yet-completed (the same posture as
today's "ACI canonicalizes but is not completed" gap). Keep `:assoc-comm` and `:assoc-comm-idem`
as accepted aliases that expand to the basic-tag combinations before resolution, so existing
`.egg` fixtures do not break.

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

- **set** (bare `G`, {0,1} counts): `and`, `or`, `xor`, `xnor`, `bvand`, `bvor`, `bvxor`,
  `bvxnor`, `set.union`, `set.inter`, `bag.union_max`, `bag.inter_min`, `re.union`, `re.inter`,
  `min`, `max`. The majority of AC operators, in two merge flavors — union-clamp (idempotent) and
  symmetric-difference (nilpotent).
- **mset** (`(G, u32)`, ℕ counts): `+`, `*`, `bvadd`, `bvmul`, `bag.union_disjoint`. The minority.
- **signed mset** (ℤ counts): only if abelian groups are ever modeled (out of scope).

In scope to implement: set-idempotent (ACI: `and`, `or`, …) and multiset (AC: `+`, `*`, …). The
set-nilpotent family (`xor`, bitwise) is future work on the same machinery with a
symmetric-difference merge and a declared unit.
