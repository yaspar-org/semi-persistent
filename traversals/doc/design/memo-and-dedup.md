# Choosing a memo strategy and dedup mode

This doc records the decision matrix and benchmark evidence for the two
orthogonal runtime choices a user of `rec_family!` makes:

1. **Memo strategy**: `Dense` (default) vs `Sparse` vs `memo::None`
2. **Dedup**: plain push vs hash-consing (`new_dedup`)

Numbers come from `traversals/benches/fold_bench.rs`, balanced binary
`Add(Lit)` trees at depths 10 / 14 / 18 (2K / 32K / 524K nodes).

---

## Memo strategy: Dense vs Sparse vs None

### Fold throughput (whole-tree fold)

| Depth | dense | sparse | none |
|-------|------:|-------:|-----:|
| 10 | **189 M/s** | 60 M/s | close to dense |
| 14 | **188 M/s** | 64 M/s | close to dense |
| 18 | **186 M/s** | 61 M/s | close to dense |

**Sparse is ~3× slower than dense when folding the whole store.** Sparse
pays a hash per lookup and insertion, with no compensating memory win
because every node is touched anyway.

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

| Depth | Nodes | plain | dedup |
|-------|------:|------:|------:|
| 10 | 2,047 | **370 M/s** | 140 M/s (2.6×) |
| 14 | 32,767 | **424 M/s** | 146 M/s (2.9×) |
| 18 | 524,287 | **270 M/s** | 144 M/s (1.9×) |

**Dedup is 2–3× slower than plain push.** You pay a hash + hashmap probe
per node. The slowdown is consistent across all sizes.

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

## API convention: one closure per sort

Every scheme takes **one algebra (or rule) closure per sort, in
declaration order**. Given

```rust
rec_family! {
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

## Decision flowchart

```
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

Hardware: results will vary. Relative ratios (3× sparse overhead on
full folds, 2.5× dedup overhead) have been consistent across runs.
