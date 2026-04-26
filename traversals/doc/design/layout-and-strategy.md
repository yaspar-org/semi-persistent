# Choosing a layout, memo strategy, and dedup mode

This doc records the decision matrix and benchmark evidence for the three
orthogonal choices a user of this crate makes:

1. **Layout**: `Arena<Lang<usize, usize>>` (single-arena coproduct) vs
   `LangStore` (partitioned per-sort arenas, via `partition!`)
2. **Memo strategy**: `Dense` (default) vs `Sparse` vs `memo::None`
3. **Dedup**: plain push vs hash-consing (`new_dedup`)

Numbers below come from `traversals/benches/fold_bench.rs`, balanced binary
`Add(Lit)` trees at depths 10 / 14 / 18 (2K / 32K / 524K nodes).

---

## Layout: partitioned vs single-arena

**Use partitioned (`partition!`) unless you have a reason not to.**

### Fold throughput

| Depth | Nodes | single_arena | partitioned_dense |
|-------|------:|-------------:|------------------:|
| 10 | 2,047 | 173 M/s | **189 M/s** (+9%) |
| 14 | 32,767 | 163 M/s | **188 M/s** (+15%) |
| 18 | 524,287 | 164 M/s | **186 M/s** (+13%) |

Partitioned fold is 9–15% faster across all sizes. The gap is stable, pointing
to a per-node constant factor, not a cache or asymptotic effect. Two causes:

1. **No runtime sort dispatch.** Single-arena folds call `node.dispatch(|stmt| …, |expr| …)`
   on every visit, which compiles to a tag check on the `Lang::Stmt*` vs
   `Lang::Expr*` discriminant. Partitioned folds route each sort through a
   separate stack variant at codegen time — the branch is resolved statically.
2. **Smaller per-node payloads.** `Lang<i64, i64>` is sized to its largest
   variant. `ExprNodeMapped<i64>` and `StmtNodeMapped<i64>` are sized per sort,
   so memo cells are smaller on the hot path.

### Build throughput is layout-independent

| Depth | single_plain | partitioned_plain |
|-------|-------------:|------------------:|
| 10 | 371 M/s | 370 M/s |
| 14 | 431 M/s | 424 M/s |
| 18 | 274 M/s | 270 M/s |

`push_expr` / `push_stmt` cost the same as the untyped `push` — the type-level
sort dispatch is entirely compile-time. Plain push is essentially `Vec::push`
in both layouts.

### Ergonomics

Beyond performance, partitioned layouts offer:

- **Typed IDs per sort** (`StmtId`, `ExprId`) — sort confusion is a compile
  error, not a runtime `TryInto` failure.
- **Separate rules per sort** in `rewrite`, `prefold`, `rewrite_down`,
  `transform` — no `_ => {}` catch-all, no `.into()` coercions.
- **Multi-sorted fold is the default.** Each sort has its own algebra; the
  traversal handles cross-sort dispatch automatically.

### When to use single-arena

- The AST has exactly one sort and you want the full canonical set of free
  functions (`refold`, `refold_with_history`, `unfold`, `unfold_short`,
  `postunfold`) plus `ArenaView` memo strategy selection without going
  through a generated Store type.
- You need coproduct tricks (uniform `Functor<R>` impls across sorts,
  `TryFrom` between sort subsets) that the partitioned layout doesn't expose.
- You're doing a one-off script where saving ten lines of `partition!` matters
  more than 11% fold throughput.

### API convention: one closure per sort

Every partitioned scheme takes **one algebra (or rule) closure per sort, in
declaration order**. Given

```rust
partition! {
    family Lang => LangStore;
    enum Stmt { /* … */ }
    enum Expr { /* … */ }
}
```

the signatures are:

| Scheme | Closures per sort | Signature per sort |
|--------|-------------------|--------------------|
| `fold` | 1 | `Fn(SortNodeMapped<A_stmt, A_expr, …>) -> A_sort` |
| `fold_short` | 1 | `Fn(SortNodeMapped<A_stmt, A_expr, …>) -> Result<A_sort, A_sort>` |
| `fold_with_history` | 1 | `Fn(SortNodeMapped<Ann<A_stmt>, Ann<A_expr>, …>) -> A_sort` |
| `fold_with_aux` | 2 (aux + main) | aux: `Fn(Mapped<B>) -> B_sort`, main: `Fn(Mapped<(A,B)>) -> A_sort` |
| `fold_with_original` | 1 | `Fn(&SortNode, SortNodeMapped<A, …>) -> A_sort` |
| `fold_pair` | 2 (A + B algebras) | `Fn(Mapped<(A,B)>) -> A_sort` and `-> B_sort` |
| `prefold` | 2 (pre + alg) | pre: `Fn(SortNode) -> SortNode`, alg: same as `fold` |
| `rewrite` | 1 | `Fn(SortNode, &mut Store) -> SortId` |
| `rewrite_down` | 1 | `Fn(SortNode) -> SortNode` |
| `transform` | 1 | `Fn(SortNode) -> SortNode` |
| `fold_all` | 1 | same as `fold`, returns a per-sort `Cache` |

With N sorts, a single-closure-per-sort scheme takes N closures. With two
sorts (Stmt, Expr), `fold` takes two closures; `fold_pair` takes four.

**Return types are sort-tagged.** `fold` returns `<Store>FoldResult<A_stmt,
A_expr, …>` — an enum with one variant per sort. Unwrap with
`.unwrap_<sort>()` when the root sort is known, or match on it.

**Each sort can return a different type.** `A_stmt` and `A_expr` are
independent generic parameters. The type inference chapter has `A_stmt =
TyStmt` (an environment transformer) and `A_expr = TyExpr` (a type query);
the bytecode compiler chapter has both `A_stmt = A_expr = Vec<Op>`.

**Mapped enums only mention sorts they reference.** If `Stmt` never contains
an `Expr`, `StmtNodeMapped` is generic only in `A_stmt`. The macro tracks
child references to keep generic parameter lists minimal.

---

## Memo strategy: Dense vs Sparse vs None

### Fold throughput

| Depth | partitioned_dense | partitioned_sparse |
|-------|------------------:|-------------------:|
| 10 | 189 M/s | 60 M/s |
| 14 | 188 M/s | 64 M/s |
| 18 | 186 M/s | 61 M/s |

**Sparse is ~3× slower than dense when folding the whole store.** Sparse
pays a hash per lookup and insertion, with no compensating memory win because
every node is touched anyway.

### When to use which

| Strategy | Allocation | Best for |
|----------|-----------|----------|
| `Dense` (default) | `O(store_size)` | Folding most or all of a store. DAG sharing where nodes are hit multiple times. |
| `Sparse` | `O(reachable_subtree)` | Folding a small focused subtree inside a large store. Avoids `Vec<Option<A>>` of millions of unused slots. |
| `memo::None` | same as `Dense` but skips dedup checks | Pure trees (no shared subtrees). Shaves a branch per node. **Incorrect on DAGs** — will recompute shared subtrees. |

Use `store.with_strategy::<Sparse>().fold(…)` to switch. The scheme API is
identical; only the internal table shape changes.

### Sparse wins when the reachable set is a small fraction of the store

If you're folding a 1K-node subtree inside a 1M-node store, Dense allocates
a `Vec<Option<A>>` with 1M cells and visits 1K. Sparse allocates a hashmap
and grows to ~1K entries. The current benchmark intentionally probes the
opposite regime (full-store fold) to show sparse's worst case.

---

## Dedup: plain push vs hash-consing

### Build throughput

| Depth | Nodes | single_plain | single_dedup | partitioned_plain | partitioned_dedup |
|-------|------:|-------------:|-------------:|------------------:|------------------:|
| 10 | 2,047 | 371 M/s | 153 M/s (2.4×) | 370 M/s | 140 M/s (2.6×) |
| 14 | 32,767 | 431 M/s | 157 M/s (2.8×) | 424 M/s | 146 M/s (2.9×) |
| 18 | 524,287 | 274 M/s | 157 M/s (1.7×) | 270 M/s | 144 M/s (1.9×) |

**Dedup is 2–3× slower than plain push.** You pay a hash + hashmap probe
per node. The slowdown is consistent across layouts and sizes.

### But the memory savings can be enormous

For the benchmark input (balanced Add tree with every leaf `Lit(1)`):

- Depth 18 unique nodes without dedup: **524,287**
- Depth 18 unique nodes with dedup: **19** (one `Lit(1)` + one `Add` per depth level)

That's a 27,000× memory reduction. Any downstream fold over the deduped
store hits each unique node once and completes in microseconds.

### When to use dedup

- **Use dedup** when the AST has (or is expected to develop) structural
  sharing: e-graphs, canonicalization, compiler IRs, memoized computation
  graphs.
- **Skip dedup** for one-shot parses / translations where you build, fold
  once, and throw away.
- **Dedup interacts correctly with `mark`/`restore`.** On restore, dedup
  entries pointing past the mark are pruned so stale ids are never returned.

---

## Decision flowchart

```
Single sort only?
├── yes → use Arena<N> with RecFunctor, skip partition!
└── no → use partition! (faster folds, typed IDs, better ergonomics)

Folding entire tree / DAG?
├── yes → use Dense (default)
└── no  → folding small subtree in large store → use Sparse

Structural redundancy in the AST (repeated subterms)?
├── yes → use new_dedup() — 2-3x slower build, potentially 1000x+ memory savings
└── no  → use new()

Pure tree, no shared subtrees, need every last % of fold speed?
└── add .with_strategy::<memo::None>() on top of the above
```

---

## Source

All numbers reproducible via:

```bash
cargo bench -p semi-persistent-traversals --bench fold_bench
```

Benchmark source: [`traversals/benches/fold_bench.rs`](../../benches/fold_bench.rs).

Hardware: results will vary. Relative ratios (11% layout gap, 3× sparse
overhead on full folds, 2.5× dedup overhead) have been consistent across
runs.
