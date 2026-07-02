# Multi-operator AC/ACI (+ semantic properties): detailed task plan

Executable task breakdown for the design in
[multi-ac-aci-completion-plan.md](multi-ac-aci-completion-plan.md). That doc is the *what and
why* (the three axes, the pool, the resolver, the SMT survey, the Kapur 2023 reference); this
doc is the *how*: ordered, checkable subtasks with concrete signatures, per-file change lists,
test lists, and per-step acceptance criteria.

Read the design doc and the naming convention (design §0a-bis: representation = `mset`/`set`,
completion procedure = `cc`, theory/matcher = `AC`) first. This plan uses those names.

## Scope and staging

Four facets, planned in dependency order. Each facet is several commits; every commit builds
clean and passes the full suite (the discipline from the merged AC-CC PR).

- **Facet A — surface syntax + property resolver.** Composable tags for every property; the
  `tags → AcAlgebra` resolver + descriptor on `OpInfo`. All properties parse/validate/store.
- **Facet B — canonization rules.** Build-time clamps (idempotent, nilpotent, identity) as a
  generalization of the existing `flatten_ac_children`; the representation split (MSet vs Set).
- **Facet C — multi-operator CC loop.** Per-op `min_monomial` pool; drive completion over MSet
  *and* Set partitions; per-op superposition (mostly present, `rj.op` filter already exists).
- **Facet D — implementation sequencing.** The concrete commit order that threads A→B→C so each
  lands green, with the wired-vs-shape-only cut per property.

Implementation depth per property (design decision, "everything all facets"):

| property   | surface (A) | canon (B)      | CC loop (C)        | wired end-to-end? |
|------------|-------------|----------------|--------------------|-------------------|
| AC (MSet)  | yes         | MSetCanon      | yes                | **yes, now**      |
| ACI (Set)  | yes         | SetCanon       | yes                | **yes, now**      |
| identity   | yes         | unit-drop      | (transparent)      | yes               |
| nilpotent  | yes         | XOR/mod-n canon| Set-nilpotent merge| yes               |
| group      | yes         | signed MSet    | signed superpose   | yes (largest)     |
| cancellative | yes       | (none)         | equation inference | yes               |

"Everything" here means all facets are *planned in detail*; D sequences them so AC+ACI land
first and the rest follow on the same machinery.

---

## Facet A — surface syntax + property resolver

### A0. Structural findings this facet rests on

- `AlgAttr` (`ast.rs`) is currently a closed enum of pre-combined tags (`Comm`, `Assoc`,
  `AssocComm`, `AssocCommIdem`, …), parsed by `parse_alg_attr` (`parser.rs`), dispatched to
  `register_c/register_a/register_mset/register_set` in `sortcheck.rs::register_op_with_attr`
  (the `attr` match). It does not compose.
- `OpKind` (`registry.rs`) already carries per-op data (`arg_sort`, `dir`) and is `Clone`, one
  record per op in the registry `Map`, not copied into hot structures. `OpInfo::canon_class`
  projects it to the bare `ENodeKind` for routing.
- Registration is currently side-effect-free on the e-graph. The unit term for
  identity/nilpotent must therefore be stored **deferred** (parsed+sort-checked, not built).

### A1. Composable tag parsing

**Files:** `parser.rs`, `ast.rs`.

- Replace the single `Option<AlgAttr>` on `Command::Function` (and datatype variants) with a
  parsed **tag set**: a `Vec<AlgTag>` (or a small bitflags-like struct) collected by looping
  `parse_alg_attr` until no tag matches, instead of taking one.
- New `AlgTag` enum: `Comm`, `Assoc`, `AssocLeft`, `AssocRight`, `Idempotent`, `Nilpotent(Option<u8>)`,
  `Identity(Term)`, `Inverse(String)`. Value-taking tags parse a following argument:
  `:nilpotent` optionally an integer order (default 2), `:identity` a ground `Term` (reuses the
  existing term parser — not new literal syntax), `:inverse` an op name (`ident`).
- Keep `:assoc-comm` and `:assoc-comm-idem` as **aliases** that expand to `{Assoc, Comm}` /
  `{Assoc, Comm, Idempotent}` before resolution.

**Tests (parser):** each tag parses; multiple tags compose; alias expansion; `:identity 0`,
`:identity (zero)`, `:nilpotent`, `:nilpotent 3`, `:inverse neg` parse their arguments; trailing
`)` still consumed.

**Acceptance:** parsing a function decl yields the raw tag set; no resolution/validation yet.

### A2. The `AcAlgebra` descriptor + resolver

**Files:** `registry.rs` (descriptor + `OpKind` fields), `sortcheck.rs` (resolver + call).

Descriptor (design §"Where the algebra lives"; **as shipped** — the clamp was unified onto both
variants by the 2026-07-01 correction, so it no longer lives only on `Set`):

```rust
enum Clamp   { None, Idempotent, Nilpotent { order: u8 } }   // unified, on BOTH MSet and Set
enum UnitRef { Lit { token }, Ctor { term } }                // deferred, built at registration
// (a standalone AcAlgebra struct was not needed — the fields live directly on OpKind.)
```

`OpKind` carries the fields on its AC-bearing variants (co-located, so representation and clamp
cannot desync — design rationale):

```rust
MSet { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool }, // None / Nilpotent
Set  { arg_sort: S, clamp: Clamp, identity: Option<UnitRef>, cancellative: bool }, // Idempotent
```

Resolver `register_op(tags, ...) -> Result<O, SortError>` (in `sortcheck.rs`):

- `{Assoc, Comm}` alone → `MSet { clamp: None }`.
- `+ Idempotent` → `Set { clamp: Idempotent }`.
- `+ Nilpotent(n)` → `MSet { clamp: Nilpotent { order: n.unwrap_or(2) } }` — **MSet, not Set**
  (keeps true multiplicities for the completion-time mod-n reduction; see property 2 above).
- `Assoc` alone (no `Comm`) → existing `A` kind (direction from AssocLeft/Right); `Comm` alone
  (binary) → existing `C`. Neither idempotent nor identity applies to A/C — reject if present.
- `Identity(term)` → sort-check `term` to `ret_sort`, build to a real node, store on the egraph's
  `unit_node` map. Attaches to MSet or Set.
- `Inverse(name)` → resolve op id; requires `Identity` present.

**Validation (reject at registration):**
- `Idempotent` and `Nilpotent` mutually exclusive.
- `Idempotent`/`Nilpotent` require `Assoc + Comm`.
- `Nilpotent` requires `Identity` (emptied monomial must canonicalize to the unit).
- `Inverse` requires `Identity`.
- `Identity term` must sort-check to the op's return sort.
- Redeclaring a property twice, or conflicting directions, is an error.

**Tests (resolver):** every valid combination maps to the expected `AcAlgebra`; every rejected
combination returns the specific error; `canon_class` projects `MSet→ENodeKind::MSet`,
`Set→ENodeKind::Set`; deferred `UnitRef` stored, not built (assert no node minted at register).

**Acceptance:** all existing `.egg` fixtures still parse+resolve (aliases); no completion
behavior change (`MSet{identity:None,...}` ≡ today's AC, `Set{Idempotent,identity:None}` ≡ ACI).

### A3. Deferred-unit materialization hook

**Files:** `egraph.rs` (a `materialize_units` step), `interpret.rs`.

- Add `fn ensure_units_built(&mut self)` that, for every op whose `AcAlgebra.identity` is a
  deferred `UnitRef`, builds the node once (via `lit_op_for_sort`+`add_lit` for `Lit`, or the
  term builder for `Ctor`) and caches the resulting `Cfg::G` on a side map `op → unit node`.
- Call it once at the top of the first completion-enabled `rebuild` (before `cc_round`), so
  registration stays side-effect-free and the unit's lit-op/ctor only needs to exist by then.

**Tests:** unit built lazily and cached; building is idempotent across rounds; rolls back under
push/pop (or is rebuilt after restore).

**Acceptance:** an op with `:identity 0` has its unit node resolvable at completion time; no node
minted before first completion `rebuild`.

---

## Facet B — canonization rules

### B0. Structural finding

`VarCanon::canonize` (`canon.rs`) is a **static trait**, dispatched by `ENodeKind` in
`recanonize_node::<Canon>` (`node_store.rs`), with no per-op parameters. So identity (needs the
unit) and nilpotent (needs order + unit) **cannot be pure `VarCanon` impls** keyed only on
`ENodeKind`. Two options; the plan picks build-time clamping to match precedent:

- **(chosen) Build-time clamp**, generalizing `flatten_ac_children` (`egraph.rs`, already called
  from `add` for MSet). The `add` path already has the op and can read `AcAlgebra`. Apply
  identity-drop and nilpotent-reduce there and in the completion `materialize` path.
- (rejected) Thread `AcAlgebra` into a dynamic `canonize` signature — larger churn to the
  `VarCanon`/`recanonize_node` surface, and recanonicalization only substitutes atoms (it never
  changes multiplicities), so the clamp belongs at build/materialize, not recanon.

Note the recanon-flatten vacuity lemma (design §6c) extends: a stored Set/MSet child is always
atomic, so recanon never re-introduces a clampable monomial; the clamp is a build-time concern.

### B1. Representation canonicalizers (mostly present)

**Files:** `canon.rs`.

- `MSetCanon` (find + sort + sum mults) and `SetCanon` (find + sort + dedup) already exist and
  are correct for AC and ACI. No change for those two.
- Idempotency is *already* `SetCanon`'s dedup: `a∘a∘b → a∘b`. So plain ACI needs no new
  canonicalizer. **Acceptance:** confirm with a test that `SetCanon` yields the idempotent normal
  form (dedup) — already covered by existing ACI canon tests.

### B2. Nilpotent canonicalization (XOR / mod-n)

**Files:** `egraph.rs` (build path), `multiset.rs` (a set-nilpotent primitive), `canon.rs` (if a
dedicated Set-nilpotent canonicalizer is cleaner than a build-time pass).

- Nilpotent (order 2) canonical form: children stored as a **set** (bare `G`), but the reduction
  is *symmetric difference*, not dedup — a child appearing an even number of times cancels to
  absent, odd stays once. For general order n: count mod n, drop count-0.
- Build-time: when `add`ing a `Set{Nilpotent{n}}` node, after find+sort, fold runs of equal `G`
  by `count mod n` and drop zeros. If the result is empty, the node **is** the unit (return the
  deferred/materialized unit node instead of an empty AC node).
- The completion merge for nilpotent is symmetric difference (design: "add then clamp mod 2" ≡
  sym-diff, stays in {0,1}). Add `set_symmetric_difference` / `mod_n_reduce` to `multiset.rs`
  operating on bare-`G` slices.

**Tests:** `a⊕a → {}` (→ unit); `a⊕a⊕b → b`; order-3 `a⊕a⊕a → {}`, `a⊕a → a:2`; empty result maps
to the unit node; sym-diff of two sets.

**Acceptance:** a `:nilpotent :identity` op canonicalizes XOR terms to the parity normal form and
the empty monomial to the declared unit.

### B3. Identity (unit drop)

**Files:** `egraph.rs` (build path).

- When `add`ing any AC-bearing node whose `AcAlgebra.identity` is set, drop the unit `G` from the
  child list before storing (multiplicity forced to 0). Applies to MSet and Set alike.
- Interacts with B2: for nilpotent, unit-drop and parity-reduce compose (drop the unit, then the
  empty result *is* the unit — consistent).
- Requires the unit node id (from A3's `ensure_units_built`), so unit-drop is active only once
  units are materialized (first completion rebuild). Before that, a unit child is harmless (it is
  just another atom); document that identity-drop is a completion-time normalization.

**Tests:** `+(a, 0) → +(a)` i.e. `{a}`; `*(a, 1) → {a}`; `and(a, true) → {a}`; unit-only term
`+(0) →` the unit/class; identity + idempotent compose; identity + nilpotent compose.

**Acceptance:** declared-unit ops drop the unit in canonical form during canonization (build and
recanonize), so the reduction holds with completion off.

### B4. Group (signed multiset)

**Files:** `multiset.rs` (signed counts), `egraph.rs` (build + inverse handling), `canon.rs`.

- Group counts are in ℤ: a summand and its inverse cancel. Representation is MSet with a **signed**
  multiplicity, or (encoding) keep `u32` mult but track sign via the inverse op wrapping.
- Canonicalization: `a + b + (−a) → b`. Needs the inverse op (`AcAlgebra.inverse`) to recognize
  `neg(x)` as the inverse of `x` and cancel. This is the largest change: multiplicity type or an
  inverse-aware fold.
- Decision to record: whether to widen `Multiplicity` to signed, or represent inverses as tagged
  children. Prefer inverse-as-tagged-child (no `Multiplicity` type change, localized to the group
  fold) unless measurement says otherwise.

**Tests:** `a + (−a) → {}` (→ unit `0`); `a + b + (−a) → b`; double negation `−(−a) → a`.

**Acceptance:** an abelian-group op cancels inverses to the unit. (Largest, last; see D.)

---

## Facet C — multi-operator CC loop

### C0. Structural finding

The completion round (`cc_round`, `egraph.rs`) **already** filters superposition/normalization by
op (`rj.op == rules[i].op`, the per-op `nf_rules` filter). Two things are single-op today:

1. `completion_node_ids` iterates only the `nodes.mset` partition (Set/ACI nodes never enter
   completion).
2. `min_monomial` is a single per-class slot (`ClassData.min_monomial`), holding one op's least
   monomial; `rebuild` asserts `mset_op_count() <= 1`.

### C1. Per-op `min_monomial` pool

**Files:** `classes.rs` (pool + `ClassData` change), `egraph.rs` (`fold_min_monomial`,
`class_rhs_into`, `min_monomial` reads), `registry.rs` (`completion_ops` array).

- Add `completion_ops: Vec<Cfg::O>` to the registry (or egraph): AC then ACI ops in registration
  order, with each op's column index stored on `OpInfo` (design "column → op reference array").
  Declare-before-build assert: reject a new AC/ACI op once a node of that kind exists.
- Add `min_pool: VecI<Opt<Cfg::G>, usize, TRACK>` to `EClasses`, fixed-width rows of
  `nb_completion = nb_mset + nb_set` columns. `ClassData.min_monomial: T` → `min_row: <off|absent>`.
  Accessor `min_monomial(op, repr)` / `set_min_monomial(op, repr, node)` maps op→column→pool slot.
- `fold_min_monomial` becomes element-wise per column (keep the `monomial_cmp`-smaller per op).
- `debug_assert!(node_op(pool[off+i]) == completion_ops[i])` on every pool read/write.
- Semi-persistence: mark/restore `min_pool` (PoolCacheToken pattern); rows roll back with offsets.

**Milestone C1a — pure refactor at `nb_completion == 1`:** land the pool with one column, routing
existing single-op reads through the accessor. No behavior change, all tests green. (Isolates the
storage change from the multi-op generalization for bisect.)

**Tests:** pool len/rollback; row fold keeps per-op minima independent; `nb_completion==1` matches
the old single-slot behavior exactly (differential against pre-refactor on the AC egg suite).

**Acceptance:** completion with one AC op behaves identically; the guard `mset_op_count()<=1` still
holds (removed in C2).

### C2. Multi-MSet superposition

**Files:** `egraph.rs` (`cc_round`, remove the guard), tests.

- Remove `assert!(mset_op_count() <= 1)`. The per-op `rj.op` filter already keeps two MSet ops'
  rule sets non-interacting; the pool (C1) now stores each op's minimum separately.
- Cross-op shared constant (`a+b = a*b`): one class holds a `+`-node and a `*`-node, each reducing
  to the class via its own pool column; union-find records the equality (Kapur's shared-constant
  case, dissolved for free).

**Tests:** `+` and `*` with a shared constant; assert `a+b=a*b` does not corrupt either op's
completion; a superposition in `+` and one in `*` both fire; `ac_vs_rules` harness extended to two
MSet ops.

**Acceptance:** two MSet ops complete correctly and independently.

### C3. Set-partition completion (ACI + nilpotent)

**Files:** `egraph.rs` (`completion_node_ids` walks `nodes.set` too; `multiset_of` reads set
children with count 1; the merge uses the Set clamp from `AcAlgebra`), `multiset.rs` (set-union
and set-symmetric-difference normal-form ops), tests.

- `completion_node_ids` iterates `nodes.mset` **and** `nodes.set`, tagging each with `(op, repr)`.
- Reducts/normalization pick the per-op clamp: MSet → ℕ multiset ops; Set-idempotent → union then
  clamp-to-1; Set-nilpotent → symmetric difference. Selected from `ops.info(op).kind`'s `AcAlgebra`.
- The ACI idempotence critical pair (`f(M∪{a})` vs `f(M)`) is *subsumed* by the clamp: a repeated
  summand normalizes to the deduped set, which is the join. No special pair generation.

**Tests:** ACI completion (`and`/`or`): the idempotence join `a∘a∘b = a∘b`; a genuine ACI
superposition; multi-ACI (two Set ops); nilpotent completion (`xor`): `a⊕a=e`, a XOR superposition.

**Acceptance:** ACI and nilpotent ops complete; a multi-ACI graph (currently allowed but
un-completed) now completes.

### C4. Identity / group in the loop

**Files:** `egraph.rs`, `multiset.rs`.

- Identity: transparent to the loop once B3 drops units at build/materialize — the monomials the
  loop sees never contain the unit. Verify no special loop handling needed.
- Group: superposition over signed monomials (B4); the reducts carry signed counts / inverse
  children; the merge cancels. Cancellative: an equation-level inference (subtract a shared summand
  from both sides), applied when two rules share a common addend — a new step in the round, not a
  per-term clamp.

**Tests:** identity op completes (unit invisible to superposition); group op derives an
inverse-cancellation equality; cancellative derives `a=b` from `a+c=b+c`.

**Acceptance:** all six property families complete; the round selects behavior per op from
`AcAlgebra`.

---

## Facet D — implementation sequencing (the commit order)

**Status (feature/ac-multi-op):** steps 1–4 below **DONE**, plus ACI completion. Landed as six
commits: OpKind widening (clamp/identity/cancellative); composable tags + resolver; registry
`completion_ops` array; per-op min-monomial pool (`ClassData.min_row: Option<usize>` +
`min_pool: VecP<Opt<T>>`); multiple-MSet completion (guard dropped); ACI (Set) completion
(`normalize_set`/`clamp_idempotent`, round walks both partitions, `rules` sorted by node id).
**Remaining: steps 5–7** below — identity (deferred `UnitRef` build + unit drop), nilpotent
(symmetric-difference normalize), group. All three already parse/validate/store; only the
completion normalization is unbuilt. Nilpotent Set ops are currently skipped in rule-building
(sound-but-uncompleted). See memory `multi-ac-aci-implementation` for the sweep-baseline caveat.

Each numbered item is one green commit. A→B→C interleave so AC+ACI land first, the rest follow.

1. **A1+A2 surface+resolver, no behavior change.** Composable tags, `AcAlgebra`, resolver,
   `OpKind` field additions; aliases keep fixtures green. `MSet{None}`/`Set{Idempotent,None}`
   resolve to today's AC/ACI. (Facet A, minus deferred-unit build.)
2. **C1a pool refactor at `nb_completion==1`.** Storage change only, differential-tested against
   pre-refactor. No new behavior.
3. **C1+C2 multi-MSet.** `completion_ops` array, per-op pool columns, remove the single-AC guard,
   multi-`+`/`*` tests, `ac_vs_rules` two-op extension.
4. **C3 Set-partition completion (ACI).** Drive the round over `nodes.set` with the idempotent
   clamp; `and`/`or` completion tests, multi-ACI.
5. **A3 deferred-unit build + B3 identity.** `ensure_units_built`; unit-drop at build/materialize;
   `+ with 0`, `and with true` tests.
6. **B2+C3-nilpotent.** Set-nilpotent canonicalization + symmetric-difference merge; `xor` tests.
7. **B4+C4 group + cancellative.** Signed/inverse fold; group + cancellative completion tests.
   Largest and last; may split further.

Steps 1–4 deliver the originally-requested multiple AC + ACI. Steps 5–7 deliver the remaining
Kapur 2023 semantic properties on the same machinery, and can stop/pause after any step (each is a
self-contained, tested capability).

## Remaining-work recap (what's left, in priority order)

Everything below is *parsed, sort-checked, and stored* already (the resolver in `sortcheck.rs`
builds the full `OpKind` descriptor; `:identity`/`:nilpotent`/`:cancellative`/`:inverse` all
validate). Only the completion-time *normalization* for each property is unbuilt, so each is a
localized addition to the round, not new surface or storage.

### 1. Identity — the neutral element (`:identity e`). NEXT.

`x ∘ e = x`: the unit `e` drops from every monomial (`a+0 → a`, `and(x, true) → x`). Applies to
both MSet and Set. Lowest risk, self-contained, and a **prerequisite for nilpotent** (the emptied
monomial must materialize to the unit).

- **Deferred-unit build (`ensure_units_built`).** The unit is stored as a `UnitRef` (parsed term,
  not built) so registration stays side-effect-free. Materialize it to a `Cfg::G` lazily, once,
  before the first completion-enabled round; cache `op → unit node` on the egraph. Literal units
  (`0`, `true`) go through `LitValParser` + `lit_op_for_sort` + `add_lit`; a constructed unit
  (`(zero)`) through the term builder.
- **Unit drop** in **canonization** (`add` and `recanonize_node`): when an op has an identity,
  remove the unit class from the child multiset so the stored node is in normal form. Keys on the
  resolved unit-node id, so it fires once the unit is materialized at registration. (Originally
  planned as a completion-time monomial-read normalization; moved into canonization with the
  nilpotent clamp — see property 2 and the design doc "Canonization, not completion" — so
  `+(a, e) = a` holds with completion OFF.)
- Tests: `+ with 0`, `* with 1`, `and with true`, `or with false`; identity composes with
  idempotent; unit-only term reduces to the unit/class.

### 2. Nilpotent — pairs cancel to the unit (`:nilpotent`, XOR). AFTER identity. ✅ DONE

`x ∘ x = e` (order 2; general order-n = count mod n). Was flagged **highest-risk of the three**;
the risk was the representation (below), which is now resolved.

- Semantics (order 2): a summand's contribution is its **count mod 2** — even copies cancel to
  the unit, odd copies leave one. `a⊕a = e`; `a⊕a⊕a = a`; `a⊕a⊕a⊕a = e`; `a⊕a⊕b = b`. Contrast
  idempotent, where any positive count → 1 (`a∘a∘a∘a = a`, never the unit) — this is why
  nilpotent needs `:identity` and idempotent does not. General order-n = count mod n (order 2 =
  XOR/bvxor is the only case in SMT-LIB, but the code takes any order).
- **Representation decision (2026-07-01): nilpotent is stored in the MSet partition, NOT Set.**
  The blocker was that a nilpotent op resolving to `OpKind::Set` builds through `SetCanon`, whose
  `dedup` is the *idempotent* clamp: it collapses `xor(a,a) → {a} = a` at build time (a false
  equality), before completion runs, and again on `recanonize_node`. Parity (count mod n) cannot
  be recovered once dedup throws the multiplicity away. Analysis (see the design doc's
  "Representation analysis — all combinations" table): to compute count-mod-n you must *hold* the
  count, and the only hash-consed place that holds counts is the MSet partition. So:
  - **Storage partition and count clamp are independent axes.** The clamp is now a unified
    `Clamp { None, Idempotent, Nilpotent { order } }` on BOTH `OpKind::MSet` and `OpKind::Set`
    (replacing the Set-only `SetClamp`). Partition is derived: `Idempotent → Set`; `None` /
    `Nilpotent → MSet`. The resolver enforces the pairing.
  - The mod-n clamp is applied **inside canonization** (`MSetCanon::canonize` = `update_multiset`
    then `clamp_multiset`), at build (`add`) AND on `recanonize_node`, so the stored node is
    already reduced: `xor(a,a) = e` holds with completion OFF. The clamp mode is fetched from the
    op registry before canonizing (`recanonize_node` takes `&ops`, like `add`). This also closes
    the old unsoundness — nilpotent no longer dedups at build.
  - Degenerate arity (empty ⇒ unit, size-1 mult-1 ⇒ that class) is a **canonization equality**,
    emitted as a merge: build returns the existing class id; recanonize's `degeneracy_merge`
    records a collision-style merge. It is congruence, NOT completion collapse. `normalize_nilpotent`
    (multiset.rs) re-clamps after each rewrite step and the superposition reduct clamps mod n (so
    completion's *derived* monomials stay reduced), but completion no longer applies the clamp or
    the empty/size-1 handling to stored nodes — canonization already did. See the design doc
    "Canonization, not completion".
  - This also handles order n>2 uniformly (Set's {0,1} could not hold count 2), and the "clamp is
    Set-only / XOR is a Set" claims in the design doc were corrected.
- Tests: `nilpotent_xor.egg` (`a⊕a=e`, `a⊕a⊕a=a`, `a⊕a⊕a⊕a=e`, `a⊕a⊕b=b`, empty→unit, both even
  cases coincide), `nilpotent_xor_superposition.egg` (shared-child superposition through the
  unit), `nilpotent_no_dedup.egg` (`xor(a,a) ≠ a`, an `EXPECT: check-failed` soundness guard),
  `canonize_clamp_no_cc.egg` (clamp/identity/degeneracy hold with completion OFF, both the build
  and recanonize paths), plus `multiset.rs` unit tests for `clamp_nilpotent` / `normalize_nilpotent`
  and `canon.rs` unit tests for the in-canonize clamp. CHECK_AC_BASIS where completion is on. The
  rule-building skip was removed.

### 3. Group — signed counts + inverse (`:inverse`, abelian group). LATER, largest.

AC + identity + inverses: `x ∘ x⁻¹ = e`. Monomial counts lift to ℤ; a summand and its inverse
cancel. Needs: (a) the deferred `inverse` op stored on `OpKind` — currently **not stored** because
`OpKind<S>` lacks the op-id type; widen or store the inverse op *name* then resolve; (b) signed
multiplicity (or inverse-as-tagged-child) in the monomial + an inverse-aware fold; (c) the round's
group reduct/normalize. May split further. Cancellativity (`x∘z=y∘z ⟹ x=y`) is an adjacent
equation-level inference (subtract a shared summand), not a per-term clamp.

### S3b — incremental completion driver (deferred, performance, not a gate).

Today `rules` is rebuilt from scratch each `cc_round` (a fresh `Vec`, re-scanned from
`completion_node_ids`, sorted by node id, dropped at round end — so there is **no** cross-round
structure to maintain, and the per-round sort is one-shot, off the hot path). S3b replaces the
"rebuild-and-re-superpose the whole rule set every round" batch with a persistent worklist: a node
enters when materialized or its class changes; draining it runs its chores for that node only.
*That* rewrite is where a persistent, incrementally-maintained rule structure (or a
`HashMap<node, index>` for the partner lookup) would earn its place — not the current round-local
sort. **Risk:** changes the driver, can reintroduce divergence/non-termination; keep the §4a/§4b/§5b
differential tests as the oracle and the 50k growth backstop on. Performance, not correctness.

### On-by-default decision (blocked on scoping).

Completion is **opt-in** (`set_cc`), and stays that way until a scoping mechanism lands, because it
diverges on dense graphs — now reachable via ACI too (the `investigate_completion_sweep` caveat:
its stress graph registers both `add` and `and`, so ACI completion enlarges/diverges those runs;
the harness is `#[ignore]` and no CI-gated test enables completion on them). The decision recorded
in [ac-completion-performance.md](ac-completion-performance.md): the lever for on-by-default is
**scoping** — a growth guard / on-demand / degree bound so completion never pays `O(crit × rules)`
on an exploding basis — not inner-loop tuning (measured dead ends) and not the S3b driver alone.
Until a scoping guard exists, completion remains off by default; flipping it on is gated on that,
not on finishing properties 1–3.

## Cross-cutting acceptance (every step)

- Clean `cargo build --all-targets`, `cargo fmt --check`, `cargo clippy --all-targets`.
- Full `cargo test --lib` + egg suite green.
- No new stale-name drift (the MSet/Set/cc/AC discipline, design §0a-bis).
- Soundness unchanged: an unsupported or mis-declared case is rejected at registration or derives
  fewer equalities, never a wrong one (design §14: only "same e-class" is a trustworthy verdict).
- Where a step bounds coverage (e.g. group deferred), the limitation is recorded in
  [ac-congruence-completeness-plan.md](ac-congruence-completeness-plan.md) §0, not left implicit.
