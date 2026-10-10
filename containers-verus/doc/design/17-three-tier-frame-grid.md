# The Three-Tier Frame Grid

This chapter is the visual proof model for Trail, Hot, and Cold history. It is
normative for frame-reconstruction arguments: vector indices run horizontally,
frame age runs vertically, and every frame owns an independent `saved_len`.
Adjacent saved lengths are not monotone; restoration may grow or shrink the live
vector.

## 1. The complete stack

The newest frame is nearest the live vector. The oldest retained frame is at the
bottom. Physical tier order is Cold | Hot | Trail.

```text
                                          VECTOR INDEX j →
frame / tier      saved_len    0    1    2    3    4    5    6    7
                             ───────────────────────────────────────
CURRENT LIVE          4      v₀   v₁   v₂   v₃    ·    ·    ·    ·
                                  ↑ newer layer
F₅ / Trail            6       C    C    I    I    C    C    ·    ·
                             ───────── frame delimiter ─────────────
F₄ / Trail            3       C    I    C    ·    ·    ·    ·    ·
                             ═════════ Trail / Hot ═════════════════
F₃ / Hot              7       C    I    C    C    C    C    C    ·
                             ───────── frame delimiter ─────────────
F₂ / Hot              4       I    C    I    C    ·    ·    ·    ·
                             ═════════ Hot / Cold ══════════════════
F₁ / Cold             8       C    C    C    I    C    C    C    C
                             ───────── frame delimiter ─────────────
F₀ / Cold             5       I    C    C    C    C    ·    ·    ·
                                  OLDEST RETAINED FRAME

C = physically covered; I = inherited from the newer layer;
· = outside this row's saved/live domain.
```

The cells marked `I` require equality to the newer snapshot's cell (or the
current live cell for F₅). Each `C` stores this frame's snapshot value, using
the oldest chronological entry in a Trail column. Captures from distinct
frames need not have equal values. This is an index-domain diagram: it does
not prescribe the physical order of Hot entries in memory.

The mandatory coverage where a frame extends beyond its newer layer is:

- F₅: columns 4 and 5, because the live length is 4;
- F₃: columns 3 through 6, because F₄'s saved length is 3;
- F₁: columns 4 through 7, because F₂'s saved length is 4.

The illustrated Cold runs are `[0, 3)` and `[4, 8)` for F₁, and `[1, 5)`
for F₀. Trail cells may contain several entries stacked vertically; section 4
shows their replay order.

Empty frames retain a delimiter and `saved_len` even when they contain no
physical entries. The delimiter is logical token identity and must survive
conversion.

### Physical authority

The proofs read the frame grid from the tier pools and nothing else: the
`hot_value_pool`, the `trail_value_pool` and the Cold runs are the physical
authority for what a frame captured, and every capture extent, every
reconstruction and every restore is justified from them. The former inert compatibility `diff_log` field and its proof scaffolding
were removed in `47722b0`; no shadow runtime log remains. Each Trail, Hot and
Cold frame owns its own `saved_len`; nothing relates a frame's saved length to
its neighbours' (§2), and a Hot frame's payload count is bounded by that
saved length while an undeduplicated Trail frame's is not, because duplicate
writes stack vertically (§8). Persistent Hot frames are unique but unordered;
sorting happens only as a transient local step inside the Hot-to-Cold
translation (§4).

## 2. Saved lengths zigzag

Each frame records the exact live length at its mark:

```text
frame:       F₀   F₁   F₂   F₃   F₄   F₅   live
saved_len:    5    8    4    7    3    6      4
               ↗    ↘    ↗    ↘    ↗    ↘
```

No proof may assume `saved_len(f) <= saved_len(f + 1)` or the reverse. The only
valid relation is pointwise coverage against `layer_above_at(f)`, which is
`snapshot[f + 1]` for an inner frame and the current view for the newest frame.

## 3. The per-cell inductive rule

For every frame `f` and every `j < saved_len(f)`:

```text
                         cell (f, j)
                              │
                ┌─────────────┴─────────────┐
                │                           │
          covered by frame            not covered
                │                           │
      frame stores snapshot[f][j]     j < layer_above(f).len
                                            &&
                                      layer_above(f)[j]
                                         == snapshot[f][j]
```

The specification is:

```text
j < saved_len(f)
    ==>
    covered(f, j)
        ? stored_value(f, j) == snapshot[f][j]
        : j < layer_above(f).len
          && layer_above(f)[j] == snapshot[f][j]
```

This is `frame_cell_inv` for Trail/Hot ranges and the equivalent uncovered-cell
clause in `cold_reconstructs`.

### A frame larger than its layer above

```text
frame f saved_len = 7:       0  1  2  3  4  5  6
layer above length = 4:      ✓  ✓  ✓  ✓  ×  ×  ×
required physical coverage:             C  C  C
```

Columns 4..6 cannot be inherited. The frame must physically cover them:

```text
snapshot[f]        [a  b  c  d  e  f  g]
layer_above(f)     [a  b  c  d]
frame captures                 [e  f  g]
```

### A frame smaller than its layer above

```text
frame f saved_len = 3:       0  1  2
layer above length = 7:      0  1  2  3  4  5  6
```

Frame `f` says nothing about columns 3..6. They belong only to newer state and
vanish when restoring `f`.

## 4. Three representations of one logical frame

Suppose one live cell evolves as `A → B → C → D` after a mark.

```text
TRAIL                           HOT                     COLD
chronological writes           first old value         first old value
                                                        packed into a run

newest   ┌─────┐
         │  C  │  replay 1st
         ├─────┤
         │  B  │  replay 2nd      ┌─────┐              ┌───────────────┐
oldest   │  A  │  replay last     │  A  │              │ ... A ...     │
         └─────┘                   └─────┘              └───────────────┘
             │                         │                         │
             └─────────────── all restore A ────────────────────┘
```

Trail records `A, B, C`; reverse chronological replay applies `C`, then `B`,
then `A`. Hot stores only the first old value `A`. Persistent Hot frames are
unique but need not be sorted. Cold stores the same unique values grouped into
contiguous runs.

Trail→Hot deduplication first collapses every Trail column to its oldest value.
Hot→Cold then sorts the selected unique Hot frame **in place as a transient
translation step**. The sort is a permutation, so it preserves at-most-one entry
per index and the frame's index→value abstraction. Run construction consumes the
sorted order; sortedness is not a persistent `hot_repr_ok` invariant and must not
be required of ordinary Hot writes or restores. The representation-refinement
target is:

```text
base = resize_preserving_prefix(layer_above(f), saved_len(f))

reverse_replay(base, trail_frame)
    == apply(base, hot_frame)
    == apply(base, cold_frame)
    == snapshot[f]
```

The equations require the frame's coverage invariant. Any cells introduced
when extending `base` are physically covered, so their initial filler values
do not affect the result. Inherited cells retain the newer layer's values.

## 5. Restore order across tiers

To restore Hot frame `F₂` from the complete stack:

```text
CURRENT
   │
   ▼
resize once to saved_len(F₂) = 4, preserving the live prefix
   │
   ▼
replay F₅ Trail entries newest → oldest
   │
   ▼
replay F₄ Trail entries newest → oldest
   │
   ▼
apply F₃ Hot unique captures
   │
   ▼
apply F₂ Hot unique captures
   │
   ▼
snapshot[F₂] (length remains 4)
```

All replay writes are restricted to the fixed target-length window. Intermediate
rows need agree with their snapshots only within both that window and their own
saved domain; they need not materialize each intermediate snapshot in full.
When the target is longer than the initial live row, the coverage invariant
ensures the appropriate frames overwrite every newly introduced filler cell.

After replay, remove the target and newer frames. Preserve exactly the older
physical and canonical history prefixes, then rebuild capture state for the
surviving top frame. Clearing the entire canonical history is valid only for
restore to frame zero.

For an older Cold target, continue with direct Cold run copies. Trail order is
load-bearing because one column may contain multiple entries. Order within one
Hot or Cold frame is irrelevant because each index appears at most once.

### Connecting the induction to execution

Freeze the original container locally with `let ghost pre = *self`. Replay may
change the live buffer, but all frame lemmas continue to read `pre`, whose
invariant is still available. No second persistent frame history is needed:
`frame_saved_value` reads the existing pools and headers.

The diagram shows logical frame steps. Trail and Hot execution still use one
batched range per tier. `lemma_overlay_split` connects that range to the frame
induction, and `lemma_pair_tier_suffix_cell` follows inherited cells until it
finds a winning capture or reaches the original live row. Cold's checked run
composition feeds `lemma_physical_frame_step`; its reverse frame loop carries
the intersection with the fixed target window.

`reconstruct_target_checked` composes resize, capture preparation, and these
physical tier paths. Its contract establishes the target contents and preserves
all history fields. Final well-formedness is a separate obligation: truncate
history, retain the canonical prefix, promote a survivor when needed, and
rebuild capture state. Verification of reconstruction alone does not discharge
those later operations or the representation-conversion proofs.

## 6. Push and regrowth

Suppose the live vector is shorter than the newest frame's saved length:

```text
newest frame saved_len = 6

snapshot:  [a  b  c  d  e  f]
live:      [a  b  c]
captures:           [d  e  f]
                     3  4  5
```

Pushing at index 3 is regrowth, not a new transient cell:

```text
before push:
live:      [a  b  c]
capture:            d

after push(x):
live:      [a  b  c  x]
```

The frame captured `d` when index 3 was popped. Push therefore does not append
history. It restores the capture bit at index 3, keeps `d` authoritative, and a
later restore overwrites `x` with `d`.

The reusable induction lemma is a horizontal live-row extension:

```text
old live row: [  preserved prefix  ]
new live row: [  preserved prefix  ][new cells]

captured column   → independent of the live row
uncovered column  → already inside the preserved old prefix
```

In source this is `lemma_frame_inv_range_grow_layer`. It applies unchanged to
the authoritative Hot range and the canonical ghost `full_trail` range.

## 7. Proof obligations induced by the grid

The grid suggests the following reusable lemma families:

1. **Horizontal extension:** grow the live row while preserving its old prefix.
2. **Horizontal contraction:** before removing a saved column, ensure that the
   frame covers it; surviving uncovered columns remain in the retained prefix.
3. **Vertical frame locality:** changing the newest frame does not affect older
   frame ranges whose layer is a fixed snapshot.
4. **Frame delimiter preservation:** conversion may change representation but
   must preserve frame count, order, empty frames, and per-frame `saved_len`.
5. **Trail column fold:** reverse chronological entries in one `(frame,index)`
   column reduce to its oldest value.
6. **Trail-to-Hot refinement:** deduplication selects that same oldest value.
7. **Hot-to-Cold refinement:** sorted runs preserve the unique `(index,value)`
   map and therefore every covered column.
8. **Tier-partition depth:** Cold count + Hot count + Trail count equals logical
   snapshot depth; each segment maps its own saved lengths to the corresponding
   snapshots.

These lemmas avoid global length-order assumptions and align proof structure
with the actual physical layout.

## 8. Frame-size bounds from column geometry

The horizontal saved domain also yields representation-specific size theorems.
For frame `f`, every stored Hot or Cold payload names a column strictly below
`saved_len(f)`. Hot uniqueness and Cold run disjointness allow at most one
payload per column:

```text
hot_entry_count(f) <= saved_len(f) < I::max_nat()
cold_value_count(f) <= saved_len(f) < I::max_nat()
cold_run_count(f) <= cold_value_count(f)
```

Visually, Hot and Cold may occupy columns but cannot stack entries vertically:

```text
index:       0    1    2    3    4    5
Hot:        [A]       [C]            [F]     at most one box per column
Cold runs:  [A]       [C]            [F]     three singleton runs
             <--------- saved_len --------->
```

Trail has no analogous payload bound because repeated writes stack vertically
inside a column:

```text
index:       0    1    2
newest:          [D]
                  [C]
                  [B]
oldest:          [A]                       arbitrarily many writes at index 1
```

Trail-to-Hot `dedupe_first` establishes the bound. It maps every nonempty Trail
column to exactly its oldest recorded value, removes all newer duplicates, and
therefore produces at most one entry for each index below `saved_len(f)`:

```text
W = Trail write count        // may exceed saved_len
U = deduplicated index count // U <= saved_len
R = Cold run count           // R <= U
```

The formal proof should factor this into four named lemmas:

1. `stratum_unique` plus the per-entry index bound implies
   `hot_entry_count <= saved_len`;
2. Trail deduplication produces `stratum_unique`, preserves the first old value
   of every touched column, and implies `dedup_len <= saved_len`;
3. transient in-place sorting of a unique Hot frame preserves
   `stratum_unique` and the complete index→value frame abstraction; sortedness
   is only a local translation fact;
4. run formation over that transient sorted order produces disjoint Cold runs,
   preserves the same unique column map, and implies both
   `cold_value_count <= saved_len` and `cold_run_count <= cold_value_count`.

No proof may apply the Hot/Cold bound directly to an undeduplicated Trail frame.
That distinction is also the geometric basis of the adaptive ratios `W/U` and
`U/R`.

## 9. Rollover: when a frame changes representation

Sections 4 to 8 say what the three representations of a frame are and why they
restore the same snapshot. This section says when a frame moves from one to the
next. The code is `src/tier_policy.rs` and the rollover functions of `src/vec.rs`.

### Ingress and closed frames

The writable frame, the newest one, is the ingress frame. Its representation is
fixed by the store. A store that appends every write (`TrailStore`) has Trail
ingress; a store that dedupes on first capture (`InlineStore`, whose
`unique_capture` is true) has Hot ingress, so its frames never pass through
Trail. The ingress frame is never converted: every limit below applies to closed
frames only, and a limit of zero still leaves the ingress frame alone.

### What a mark does

A mark seals the ingress frame, opens a new one, and then applies a
`RolloverPolicy`:

| Policy | Effect |
| --- | --- |
| `Defer` | converts nothing; the mark is one header push |
| `ApplyConfigured` (default) | applies the vector's configured limits, below |
| `ForceClosed { trail_to_hot, hot_to_cold }` | converts every closed frame on the chosen edges |

When both edges run, Trail to Hot runs before Hot to Cold, so a frame can cascade
from Trail to Cold in one mark.

### Configured limits

A vector carries a `TierPolicy`: one `TierLimit` for closed Trail frames, one for
closed Hot frames, and a `ReclaimPolicy` for Cold pools.

| Limit | Frames converted |
| --- | --- |
| `Unbounded` | none, automatically |
| `Frames(n)` | all but the newest `n` closed frames |
| `Entries(n)` | all but the newest closed suffix whose entries fit `n` |
| `Bytes(n)` | all but the newest closed suffix whose entries times the entry size fit `n` |
| `Adaptive` | on Trail: closed frames from the oldest, each while its writes are at least twice its unique slots, stopping at the first that is not; on Hot: none automatically |

A bounded limit keeps the newest closed suffix and converts the older prefix, so
recently closed frames stay in the cheaper-to-restore representation. Trail to
Hot is `dedupe_first` (§8): a hash set over the frame's writes, linear in them.
Hot to Cold sorts the unique frame in place and forms runs (§4), so it costs a
sort of the frame's unique entries.

The constructors choose a policy from the store. A Hot-ingress store gets
`trail: Frames(0), hot: Unbounded`, which is `TierPolicy::fully_buffered_unique()`
(the default): closed frames stay Hot until something compresses them. A
Trail-ingress store gets `trail: Unbounded, hot: Unbounded`, which converts
nothing by limit. Four named profiles exist:

| Profile | Trail | Hot | Use |
| --- | --- | --- | --- |
| `smt()` | `Unbounded` | `Unbounded` | frequent backtracking: append-only formation, no conversion |
| `adaptive()` | `Adaptive` | `Unbounded` | duplicate-heavy frames dedupe; unique frames wait for explicit compression |
| `restore_optimized()` | `Frames(0)` | `Frames(0)` | every closed frame goes to Cold |
| `fully_buffered_unique()` | `Frames(0)` | `Unbounded` | the default for Hot ingress |

`set_tier_policy` replaces a vector's policy for future marks (`apply_tier_policy`
enforces it at once), and `tier_stats` reports the frames and entries in each
tier.

### The legacy batch cadence

Before the tier limits existed, a vector converted history in batches. That
cadence survives as `hot_buffer`, and the constructor sets it to eight frames
for every store except a Hot-ingress store with no compression mode. When it is
set, it takes precedence over the limits: once more than eight frames have
closed, every closed ingress frame migrates (Trail to Hot, then Hot to Cold).
`TrailStore`, and so the e-graph's `TrailFirst` policy, therefore rolls its
closed frames over in batches of eight by default. A vector built with an
explicit `TierPolicy`, or given one by `set_tier_policy`, has no batch cadence:
the limits alone decide.

### Explicit passes

A caller can also convert history directly:

- `flush_trail` dedupes every closed Trail frame;
- `compress_hot` run-compresses every closed Hot frame;
- `apply_tier_policy` enforces both configured limits now;
- `apply_adaptive(AdaptiveInput)` runs one deterministic budgeted pass and
  returns an `AdaptiveReport`.

The adaptive pass takes a byte budget for closed history
(`max_closed_history_bytes`) and two exact ratios. It does nothing when the
closed history already fits the budget. Otherwise it dedupes closed Trail frames
from the oldest, while the budget is exceeded and each frame's writes per unique
slot meet `min_writes_per_unique`. It then recomputes the occupancy and moves
closed Hot frames to Cold from the oldest, while the budget is still exceeded,
each frame's unique entries per run meet `min_uniques_per_run`, and its Cold form
is no larger than its Hot form. The first frame that does not qualify stops its
stage. The budget counts logical occupancy only (closed headers and payloads
times their element size), not capacity, allocator state, or time. The ratios
compare by cross multiplication, so the decision does not depend on floating
point. Capacity is reclaimed once, after both stages, so a cascade does not
shrink a pool and then regrow it. `try_push_frame_adaptive` is a deferred mark
followed by one such pass.

### Why the e-graph's two policies differ

The e-graph chooses its stores through `EGraphConfig::Policy` (chapter 18).
Equality saturation writes the same slots many times between marks, so
`HotFirst`'s deduplicating ingress pays: one saved word per touched slot per
frame, at the cost of a lookup per write. SMT search marks and backtracks often
with few writes per frame, so `TrailFirst`'s append-only ingress pays: no lookup
per write, and duplicates are kept until rollover dedupes them. Restoring a frame
replays its Trail entries in reverse or applies its Hot or Cold entries once
(§5); a deduplicated frame restores in time proportional to its unique slots, a
Trail frame in time proportional to its writes.
