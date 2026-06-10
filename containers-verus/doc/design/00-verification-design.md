# Verified Semi-Persistent Vector — Design & Proof Notes

This is the master design document for `containers-verus`, the Verus port of
the production semi-persistent vector in `../containers`. It captures the data
layout, the bit-stealing storage abstraction, the mark/restore/fork machinery,
the verification invariants, and exactly how each operation establishes or
maintains them — so the proof architecture doesn't have to be rediscovered.

Companion docs:
- `restore-regrow-alternatives.md` — Default vs Clone-scan vs force-record for
  the pop/regrow value problem (and why Default was chosen).

Status snapshot (HEAD `1f979ae`, 142 verified, 0 errors, no admits/assumes):
the full vector — push, pop (transient-only), set, get, mark, restore — is
proved at arbitrary nesting depth. Faithful pop (pop into the marked region)
and fork-history/branch-cut safety are in progress / not started. See the
"What's proved vs pending" section at the end.

---

## 1. What problem this solves

Backtracking search (e-graphs, SAT, constraint propagation, game trees) needs
to snapshot mutable state and roll back. A naive clone-per-snapshot is O(n).
The semi-persistent vector gives **O(1) mark** and **O(k) restore** (k =
mutations since the mark) via a *diff log*: record the old value before each
first overwrite, replay in reverse to undo.

The headline correctness theorem we prove:

> After `restore(token)`, `view() == snapshots[token.frame_idx]`, where
> `snapshots[k]` is the deep copy of `view()` at the moment frame `k` was
> marked. Holds at arbitrary mark-nesting depth.

`view(): Seq<T>` is the abstract, user-visible contents. `snapshots` is a
**ghost** stack — it exists only in the proof, never at runtime; the whole
point is that the data structure reconstructs it from the diff log without
storing it.

---

## 2. Layered module architecture

```
L0  tagged.rs / index_like.rs   trait specs: niche/bijection axioms
L1  diff_store.rs               DiffStore trait — the capture-protocol contract
L2  parallel_store.rs           ParallelStore<T,I>  (T: Copy)         impl + proofs
    inline_store.rs             InlineStore<T,I>    (T: Tagged)       impl + proofs
L3  frame.rs                    Frame<I> { saved_len: I, diff_start: usize }
L4  vec.rs                      Vec<T,I,S,TRACK> — proofs over the trait specs
```

`Vec`'s proof talks only to the `DiffStore` *contract*, so it is parametric in
storage. Two backends satisfy that contract; swapping them is invisible to the
`Vec` proof.

---

## 3. Bit-stealing: the `Tagged` trait and the two storage layouts

### The idea

Pool-allocated ids (e-nodes, etc.) are dense small integers. A 32-bit id only
needs 31 bits to address 2 billion entries; the MSB is a free **tag bit**. The
semi-persistent vector needs a per-slot "captured since last mark?" flag —
exactly one bit. For id types, that bit lives *inside* the id at zero memory
cost.

### `Tagged` (L0, `tagged.rs`)

```
trait Tagged: Copy {
    type Repr: Copy;
    spec fn value_of(r: Repr) -> Self;   // the clean value in r
    spec fn tag_of(r: Repr) -> bool;     // the tag bit in r
    spec fn repr_wf(r: Repr) -> bool;    // niche predicate
    proof fn lemma_repr_extensional(...) // two wf reprs w/ equal (value,tag) are equal
    fn into_repr / from_repr / tag / set_tag / clear_tag   // exec, contracted
}
```

The **niche obligation** (`repr_wf` + `lemma_repr_extensional`) is what makes a
bit-stealing impl sound: it forces the encoding to be injective so the stolen
bit doesn't waste state space. The `BoolPair<T>` fallback impl sets
`repr_wf := true` (no niche; pays an extra word). A real `DenseId<31>` over
`u32` would set the MSB and discharge the niche proof. The key consequence:
`set_tag`/`clear_tag` preserve `value_of` — flipping the capture flag never
disturbs the abstract value, which is why `view()` is invariant under
capture-bit edits.

### `IndexLike` (L0, `index_like.rs`)

Bijection between an exec index type and `nat`: `as_nat`, `max_nat`,
`min_spec`/`max_spec`, ordering, with injectivity + boundedness lemmas. Keeps
diff entries `(T, I)` compact (a narrow `I` = smaller log). `u64` index is
gated to 64-bit hosts so `as_usize` can't truncate.

### The two `DiffStore` backends (L2)

|                | `InlineStore<T: Tagged>`        | `ParallelStore<T: Copy>`      |
|----------------|---------------------------------|-------------------------------|
| storage        | `Vec<T::Repr>`                  | `Vec<T>` + `Vec<bool>`        |
| capture flag   | inline, in each `T::Repr`'s tag | separate parallel bool vector |
| memory         | 0 extra bytes / slot            | 1 bit (here: 1 bool) / slot   |
| `data()` spec  | `value_of` mapped over reprs    | the `Vec<T>` directly         |
| `captured()`   | `tag_of` mapped over reprs      | the parallel bool vector      |

(The verus `ParallelStore` uses `Vec<bool>` rather than production's packed
`Vec<u64>` bitset — same observable behavior, simpler proof; the bitset is a
non-observable optimization to revisit.)

Both prove `data().len() == captured().len()` (`lemma_wf_captured_len`) and
that capture-bit edits leave `data()` unchanged.

---

## 4. The DiffStore capture-protocol contract (L1)

Ghost views: `data(): Seq<T>`, `captured(): Seq<bool>`, `wf(): bool`. Methods
(contracts in terms of the `@` views of exec slice/Vec args):

- `push / pop / get / set_raw / truncate` — raw data ops; `set_raw` preserves
  the capture flag at the written slot.
- `prepare_mark(saved_len, prev_diffs)` — clear `captured[0..saved_len]` so the
  new frame can capture fresh.
- `capture(i, saved_len, diff_log)` — **first-write-wins**: if
  `i < saved_len && !captured[i]`, append `(data[i], i)` to the log and set
  `captured[i]`; else no-op. The postcondition spells this out so an impl
  cannot vacuously satisfy it.
- `force_capture(i, saved_len, diff_log)` — *unconditional* capture (production
  uses it for pop). Bounded-log designs avoid it (see §8).
- `restore_entry(idx, old, target_saved_len)` — the replay step. Drops
  `idx >= target_saved_len`; pushes if `idx == data.len()` (regrow); else
  overwrites. **Everything is gated by the TARGET's saved_len.**
- `finish_restore(surviving_diffs, saved_len)` — rebuild `captured` from the
  surviving (post-restore) top stratum.
- `mark_captured(i)` / `resize_default(len)` — added for faithful pop (§8):
  set one flag; truncate-or-grow-with-`T::default()`.

---

## 5. Vec layout (L4)

```
struct Vec<T, I, S, const TRACK: bool> {
    store: S,                      // the DiffStore backend
    diff_log: std::vec::Vec<(T,I)>,// (old_value, index) entries, all frames
    frames:   std::vec::Vec<Frame<I>>,
    active_saved_len: I,           // cached saved_len of the top frame
    snapshots: Ghost<Seq<Seq<T>>>, // GHOST: deep copy per frame
}
Frame<I> { saved_len: I, diff_start: usize }
```

- `view() == store.data()`.
- The diff log is **stratified**: frame `k` owns the slice
  `[frames[k].diff_start, stratum_end(k))`, where `stratum_end(k)` is
  `frames[k+1].diff_start` (inner) or `diff_log.len()` (top). Each capture
  while frame `k` is active lands in stratum `k`.
- `Frame.saved_len: I` (not `u32`) — fixes a production bug where a `u32`
  field silently truncated past 4 G slots for `I = u64`. `diff_start: usize`
  indexes the log.

#### 2D picture: stratification (nested marks)

One flat `diff_log`, partitioned by `diff_start` into per-frame strata. Each
frame's `frame_inv_range` runs over its own stratum, with `layer_above` =
the next-deeper snapshot (or the view, for the top frame):

```
                       diff_log positions →
        0    1    2    3    4    5    6    7
      ┌────┬────┬────┬────┬────┬────┬────┬────┐
      │ d0   d1 │ d2 │ d3   d4   d5 │ d6   d7 │
      └────┴────┴────┴────┴────┴────┴────┴────┘
        └ stratum 0 ┘└ str 1 ┘└─── stratum 2 (top) ───┘
   frame:   0          1            2
 diff_start 0          2            5         (n = 8)

 layer_above(0) = snapshots[1]    overlay stratum 0 onto snap[1] ⇒ snap[0]
 layer_above(1) = snapshots[2]    overlay stratum 1 onto snap[2] ⇒ snap[1]
 layer_above(2) = view()          overlay stratum 2 onto view   ⇒ snap[2]
```

`restore(target)` replays `diff_log[diff_start_target .. n]` — i.e. the union
of strata `target..top` — in reverse. The central lemma proves this equals
`snapshots[target]` by composing the per-stratum overlays top-down.

---

## 6. The invariant: `wf` = `wf_for_snap` + bridge

### `wf_for_snap()` — snapshot-reconstruction core

Structural:
1. `store.wf()`.
2. `snapshots.len() == frames.len()` (parallel stacks).
3. `frames.len()==0 ⟹ diff_log empty`.
4. `frames[0].diff_start == 0`; `frames[top].diff_start <= diff_log.len()`.
5. `frames[top].saved_len <= view.len()` — "view is full". **(This and the
   saved_len-monotone clause are the two that faithful pop must relax — see
   §8.)**
6. `diff_start` monotone; `saved_len` monotone; `snapshots[k].len() ==
   frames[k].saved_len`.
7. **Per frame `k`** (the heart): `frame_inv_range(layer_above(k), diff_log,
   lo_k, hi_k, snapshots[k], saved_len_k)`, where `layer_above(k)` is
   `snapshots[k+1]` (inner) or `view()` (top).

### `wf()` adds the capture-flag bridge

8. `active_saved_len` caches `frames[top].saved_len`.
9. `store.captured().len() == view.len()`.
10. **Bridge**: for `j < min(active_saved_len, view.len())`,
    `store.captured()[j] ⟺ j ∈ top stratum`. Ties the runtime per-slot flag to
    the ghost diff log so `set`/`pop` can reason about `capture`'s
    first-write-wins branch. Restricted to *present* cells; popped cells'
    captured-ness lives only in the diff log.

`wf` was split into `wf_for_snap` + bridge precisely because `resize_default`
(restore's regrow) preserves `wf_for_snap` but breaks the bridge — so the
reconstruction lemmas run on `wf_for_snap`.

### `frame_cell_inv` — the per-cell declarative invariant (the key idea)

`frame_inv_range`'s heart is a `forall j < saved_len . frame_cell_inv(...)`:

```
frame_cell_inv(above, diffs, lo, hi, snap, j) :=
    if  no entry in stratum [lo,hi) hits j (UNCAPTURED):
            j < above.len()  &&  above[j] == snap[j]
    else (CAPTURED):
            some entry (old, j) in [lo,hi) has old == snap[j]
```

Read declaratively (the formulation the user pushed for, much easier to
maintain than an operational "replay" spec):

> Each marked cell's snapshot value lives in **exactly one** of two places:
> if untouched since mark, in the **view** itself (and the cell is still
> present); if overwritten/popped, in the **diff log**.

The **coverage** consequence — the linchpin for pop — is the contrapositive of
the uncaptured arm: `j ≥ above.len() ⟹ captured`. I.e. *every cell that has
left the layer-above (was popped) must have a diff entry*. There is no third
state: a cell can't be both absent from the view and absent from the log.

#### 2D picture: one frame's invariant

Columns = vector index `j`; the diff-log row holds this stratum's entries
(at most one per column — first-write-wins); the bottom rows are the live
`view` and the ghost `snap` we must be able to rebuild.

```
            j=0    j=1    j=2    j=3    j=4
 stratum  │      │      │(C,2) │      │(E,4) │   captured columns: 2, 4
          └──────┴──────┴──────┴──────┴──────┘
 view  =  [  A      B      x      D      y  ]    x,y = scribbles written since mark
 snap  =  [  A      B      C      D      E  ]    (target; ghost)
             ↑u     ↑u     ↑cap   ↑u     ↑cap     u = uncaptured, cap = captured
```

Reading each column — this *is* `frame_cell_inv`:

| col | captured? | where `snap[j]` lives                       | arm        |
|-----|-----------|---------------------------------------------|------------|
| 0 A | no        | `view[0]` (== snap, untouched)              | uncaptured |
| 1 B | no        | `view[1]`                                   | uncaptured |
| 2 C | yes       | diff entry `(C,2)`  (view holds scribble x) | captured   |
| 3 D | no        | `view[3]`                                   | uncaptured |
| 4 E | yes       | diff entry `(E,4)`  (view holds scribble y) | captured   |

Restore = overlay the diff row back onto the view: write each `(old,j)` at
column `j`. Uncaptured columns already equal `snap`; captured columns get
their `old` back. Result == `snap`. The **lowest-position** entry per column
wins (it is applied outermost), which matters once a column has more than one
entry (see §8).

Plus stratum-local structural facts: entries in stratum k have `idx <
saved_len_k`, and indices are **unique within a stratum** (first-write-wins).
Across strata the same index may recur (different marked-time values).

### Trigger engineering note

`frame_cell_inv` is a *named* spec fn (not an inlined if-then-else) so
`frame_inv_range`'s `forall j` has a clean `#[trigger] frame_cell_inv(...)`
that Verus re-assembles reliably. `lemma_frame_inv_arm_at` instantiates it at
one cell; `lemma_frame_cell_inv_local` transfers it across a diff-log change
that preserves `[lo,hi)`. This pattern (proved-forall == goal-forall via
function-application trigger) was the fix for a multi-session reassembly
blocker.

---

## 7. How each operation maintains the invariant

`view()`, `len`, `is_empty`, `get` — read-only; trivially preserve `wf`.

**`push(v)`** — `store.push(v)`. diff_log/frames/snapshots unchanged; only the
view grows by one at the end. Inner frames' `frame_inv_range` references
snapshots (unchanged). The top frame's layer is the view: its `frame_cell_inv`
transfers per-cell because the view's `[0, old_len)` prefix is preserved and
the new cell is past every `saved_len`. (`lemma_saved_len_le_view_from`.)

**`set(i, v)`** under an active frame — `capture(i, active, diff_log)` then
`set_raw(i, v)`. Per-cell proof, split on `j == i`:
- `j ≠ i`: view[j] and captured-status unchanged ⇒ both arms inherited.
- `j == i`: now captured. If `capture` appended, the new entry holds
  `old_view[i]`, which equals `snap[i]` *because* i was uncaptured ⇒ the old
  uncaptured arm gave `view[i] == snap[i]`. If i was already captured, the
  existing entry still holds `snap[i]`.
  The **bridge** is what tells the proof whether i was already captured
  (`store.captured()[i]`), matching `capture`'s first-write-wins branch.
Uniqueness preserved: i was absent from the stratum iff we append.

**`pop()`** (transient-only, current) — `store.pop()`. Precondition
`active_saved_len < view.len()`: only pop a cell *above* every frame's marked
region, so no frame_inv cell is affected and no capture is needed. Bridge:
pop drops the last captured flag (index ≥ active), leaving `[0, active)`
unchanged. (Faithful pop lifts this — §8.)

**`mark()`** — `prepare_mark`, push `snapshots.push(view)`, push
`Frame { saved_len: view.len(), diff_start: diff_log.len() }`, set
`active_saved_len`. The new top frame's stratum is **empty**, so its
`frame_cell_inv` is all-uncaptured: `view[j] == snap[j]` reduces to
`view[j] == view[j]`. The previously-top frame's layer flips from `view` to
the new `snapshots[top]` (== the view at mark time), so its `frame_inv_range`
transfers. Establishes the bridge trivially (prepare_mark cleared the flags;
empty stratum ⇒ captured_in_range false everywhere).

**`restore(token)`** — truncate to `saved_len_target`, then a loop replaying
`diff_log[diff_start_target .. n]` in reverse via `restore_entry`. The
`overlay` spec models the loop: lower-index entries are applied outermost, so
the **lowest-position entry per cell wins**. The central lemma
`lemma_snap_eq_overlay` proves `overlay(view, diffs, diff_start_target, n) ==
snapshots[target]` on `[0, saved_len_target)`, by downward induction over
frames (each stratum overlaid onto the layer above). Then truncate +
`finish_restore` rebuild the bridge for the new top frame; snapshots/frames
truncated to `target`.

---

## 8. Faithful pop (in progress) — the hard part, and what we learned

Production allows **popping into the marked region** (popping a cell with
`index < saved_len`). On restore, that pop "becomes a push": the regrown slot
needs a real `T`. Three ways to supply it (see `restore-regrow-alternatives.md`):

- **C. force-record (production)**: pop logs *unconditionally*. Correct, but a
  `push/pop` loop on one index grows the log without bound — a latent **DoS**.
- **A. Default + resize (CHOSEN)**: pop uses *conditional* capture (bounded
  log); restore `resize_default`s the view back up with `T::default()` fillers,
  which the replay overwrites. Needs `T: Default`. O(k) restore.
- **B. Clone-scan**: no Default, but index-keyed regrow → 2×/log-factor restore.

Default-filler **soundness**: a fabricated default is *never observable*. Every
filler sits in a popped cell, which coverage guarantees is captured, so the
replay overwrites it. This is *entailed by the headline theorem* `view() ==
snapshots[k]` — a filler surviving would make `view() != snapshot`. Hence
`T::default()`'s value is never constrained.

#### 2D picture: pop into the marked region, then restore

`saved_len = 5`, `snap = [A,B,C,D,E]`. We `set(2,X)` (captures C), then pop
twice into the marked region. Conditional capture logs a popped cell **only
if not already captured**:

```
 step          stratum (diff entries)        view            note
 ----          ----------------------        ----            ----
 mark(5)       (none)                        [A B C D E]
 set(2,X)      (C,2)                          [A B X D E]    capture C
 pop()  j=4    (C,2)(E,4)                      [A B X D]      j=4 uncaptured → log E
 pop()  j=3    (C,2)(E,4)(D,3)                 [A B X]        j=3 uncaptured → log D
```

Now `view.len() = 3 < saved_len = 5`. The **gap** `[3,5)` is exactly the
popped region, and coverage holds — every gap column has a diff:

```
            j=0   j=1   j=2   j=3   j=4
 stratum  │     │     │(C,2)│(D,3)│(E,4)│
          └─────┴─────┴─────┴─────┴─────┘
 view  =  [ A     B     X ]  ╎     ╎       present: [0,3);  gap [3,5)
 snap  =  [ A     B     C     D     E ]    (target, len 5)
            ↑u    ↑u    ↑cap  ↑cap  ↑cap    j≥view.len() ⇒ MUST be captured
```

restore (Default approach), all clamped to `saved_len = 5`:

```
 resize_default(5):  [ A  B  X  d  d ]        d = T::default() fillers in the gap
 replay diffs onto it (lowest-position wins):
      (E,4): col 4 < 5  → overwrite → [ A B X d E ]
      (D,3): col 3 < 5  → overwrite → [ A B X D E ]
      (C,2): col 2 < 5  → overwrite → [ A B C D E ]   == snap  ✓
```

The fillers `d` are overwritten because columns 3,4 are captured (coverage);
they are never observed. Two diffs per column never arises here because
conditional capture skips already-captured columns — keeping the log ≤
`saved_len`. If we then `mark()` while short, the new frame records
`saved_len = 3 < 5`: **saved_lens go non-monotone** (why §8 must drop that
clause). And note every diff above is `< saved_len = 5`; a deeper frame's
diff at column ≥ 5 would simply be **dropped** by `restore_entry` (target-
clamped), so the view never needs to exceed the target's saved_len.

### What faithful pop requires (the invariant relaxations)

1. **Drop `wf` clause "frames[top].saved_len <= view.len()"** (clause 5):
   after popping into the marked region the view is *shorter* than saved_len.
   `frame_cell_inv`'s coverage arm already handles the popped cells. The
   dependent lemmas (`lemma_saved_len_le_view`, `lemma_snap_eq_overlay`) take
   "view is full" as an explicit hypothesis that **restore re-establishes via
   `resize_default`** before reconstructing.

2. **Drop `wf` clause "saved_len monotone"** — `mark` after a deep pop pushes a
   frame whose `saved_len < ` the previous frame's (it marks the current short
   view). So saved_lens are **not monotone**, and `lemma_saved_len_le_active`
   ("top is the longest") is **false**. Replacement is per-frame **coverage**,
   already in `frame_cell_inv`: uncaptured `j ⟹ j < saved_{k+1}`; contrapositive
   `j ∈ [saved_{k+1}, saved_k) ⟹ captured in stratum k`. So the central
   lemma's inductive step, for cells beyond the layer-above's length, uses the
   *captured* arm (frame k's own diff) instead of the layer. No new clause
   needed — use coverage, stop using monotonicity.

3. **restore is TARGET-bounded — no resize-to-max.** Production's
   `restore_entry` early-returns on `idx >= target_saved_len`: **out-of-range
   diffs are simply dropped.** So restore truncates/regrows to *exactly*
   `saved_len_target`, and any diff (from any replayed stratum) with `idx >=
   saved_len_target` is a no-op. The view never needs to reach `max(saved_len)`.
   Consequence for the proof: the central lemma should be stated **flat and
   target-clamped** — `overlay(base_of_len_target, diffs, diff_start_target, n,
   target_saved_len)` with the `saved_len` parameter = target's, which makes
   over-range entries vanish — rather than reconstructing each intermediate
   `snapshots[k]` fully on `[0, saved_k)`. The current layered lemma
   over-reconstructs intermediates (needs `saved_k <= view.len()` for inner k),
   which is the spurious requirement to remove.
   The **committed** `overlay` spec is currently **overwrite-only** (two-way:
   `idx < prev.len()` → update, else skip) and takes **no `saved_len`
   parameter** — it matches the no-regrow restore that the transient-only pop
   needs. Faithful pop must extend it to the three-way form
   `idx >= saved_len` skip / `idx < prev.len()` overwrite / `idx == prev.len()`
   push (regrow), adding the `saved_len` (= target) parameter so over-range
   entries vanish. (A three-way `overlay` was prototyped in a reverted draft;
   it is *not* in the committed code.)

4. **`push` must `mark_captured`** a cell re-entering the marked region (after
   pop then push, `old_len < active_saved_len`): the pop already captured
   `snap[i]`, so the fresh slot inherits the captured flag. Without this, a
   later `set` re-captures and the log grows unbounded (defeats first-write-wins
   *and* the bound). This is what keeps faithful pop's log ≤ saved_len.

### Coverage — the one lemma, and its lifecycle

With conditional capture (no force-record), we are back to **at most one diff
per cell per stratum** (uniqueness). The *only* new obligation faithful pop
adds is **coverage**, which is just the contrapositive of `frame_cell_inv`'s
uncaptured arm:

> **Coverage (per frame k):** every cell `j` with `layer_above_k.len() ≤ j <
> saved_len_k` is **captured** in stratum k. I.e. any marked cell no longer
> present in the layer above (it was popped) has a diff entry — the entry that
> will overwrite the padded default during restore.

Plus **uniqueness**: within a stratum each index appears at most once
(first-write-wins). These two are the whole proof. Crucially, **nothing about
`T::default()`'s value is ever needed** — coverage guarantees every padded
default is overwritten, so defaults are transient placeholders, never observed.

Lifecycle — how each op handles coverage + uniqueness (top frame's
`layer_above` is the live `view`; the gap is `[view.len(), saved_len)`):

| op | coverage | uniqueness |
|----|----------|------------|
| **mark** | *establishes*: `saved_len := view.len()`, so the gap is **empty** — no popped cells yet, nothing to cover. | *establishes*: new stratum is empty. |
| **set(i,v)** | *maintains*: view length unchanged ⇒ gap unchanged; `i < view.len()` is below the gap. | *maintains*: `capture` is first-write-wins → `i` appears ≤ once. |
| **pop()** | *maintains*: removing cell `i` grows the gap to include `i`; `pop` calls `capture(i)` first, so `i` becomes captured (or already was) — holding `snap[i]` because the old uncaptured arm gave `view[i]==snap[i]`. | *maintains*: **conditional** capture (not force-record) → still ≤ 1 entry for `i`. |
| **push(v)** | cell leaves the gap (present again); n/a. | *maintains*: if re-entering a marked index (`old_len < saved_len`), `mark_captured(old_len)` keeps the flag set so a later `set` won't append a 2nd entry. |
| **restore(t)** | *uses*: pad/chop to `saved_target`; the padded cells are exactly the gap, which coverage says are all captured ⇒ each padded default is overwritten by its diff (lowest-position-in-range wins = the target's value). | *uses*: lowest-position-in-`[diff_start_target,n)` entry per cell is unambiguous (≤1 per stratum), and it is the target's own (or a fallen-through deeper stratum's) value. |

This is the "either it's already snapshotted, or we record a diff" intuition,
formalized: `pop` is the only op that opens a gap, and it pays for each gapped
cell with a capture. See `flat-central-lemma-design.md` for the lemma that
turns coverage into the `view() == snapshots[target]` reconstruction.

### Done vs pending for faithful pop

- Done & committed: store methods `mark_captured`/`resize_default`;
  `frame_cell_inv` coverage refactor; `wf_for_snap` split; bridge restricted to
  present cells; reconstruction lemmas on `wf_for_snap`.
- Pending: drop the two wf clauses; restate the central lemma flat/
  target-clamped; restore body (resize to target_saved_len + replay); `push`
  mark_captured; `pop` conditional-capture into the marked region. These were
  prototyped (the pop body largely proved) but reverted to keep the tree green
  while the central-lemma restatement is designed.

---

## 9. Fork history / branch-cut safety

Mark/restore alone is not memory-safe against **stale tokens**. The frame
index in a token can be reused: restore past a mark, then mark again — the new
frame reuses the old index, but it is a *different* logical snapshot on a *new
timeline*. A token from the abandoned timeline must be rejected, or restoring
with it would roll back to a frame that no longer means what the token thinks.
Production solves this with two mechanisms; the verus model does **not yet**
have either (this is milestone **M5**, after push/pop).

### 9.1 Container identity (M5a — straightforward)

```
ContainerId(u32)                    // from a global atomic counter
VecToken { …, container_id }        // every token records its origin Vec
```

`restore` asserts `token.container_id == self.id`. Rejects using one vec's
token on a *different* vec. Property to prove: a token validated against a Vec
was minted by that Vec. Modeled with a ghost unique id per Vec; cheap.

### 9.2 Fork history (M5b — the real branch-cut theorem)

Production state (`token.rs`):

```
VecToken { branch_id: u32, depth: u32, frame_index: u32, container_id }
ForkHistory {
    current_branch_id: u32,
    origins: Vec<ForkOrigin { parent_branch_id: u32, fork_depth: u32 }>,
}
```

Lifecycle:

- **`mark()`** stamps the token with `branch_id = forks.current_branch()` and
  `depth = frames.len()` (the depth *before* the push — so a token's `depth`
  equals its own frame index, i.e. how many frames sit below it).
- **`restore(token)`** rolls back to `token.frame_index`, then calls
  `forks.fork(token, …)`: it **starts a new branch** — pushes
  `ForkOrigin { parent_branch_id = token.branch_id, fork_depth = token.depth }`
  and sets `current_branch_id = origins.len()` (a fresh, never-reused id). The
  fork records *which branch we forked from* and *at what depth*.
- **`is_valid(token, current_depth)`** (the gate `restore` checks):
  ```
  if token.branch_id == current_branch_id:        // same branch
      return token.depth <= current_depth
  branch = current_branch_id
  while branch != token.branch_id:
      if branch == 0: return false                // token's branch unreachable
      origin = origins[branch - 1]
      if origin.parent_branch_id == token.branch_id:
          return token.depth <= origin.fork_depth  // token must be at/below the cut
      branch = origin.parent_branch_id             // climb toward the root
  return token.depth <= current_depth
  ```

In words: walk from the current branch up its chain of parents. A token is
valid iff its branch lies on that ancestor path **and** its depth is within the
part of that branch that has *not* been cut off by a later fork.

### Branch tree — 2D picture

Each `restore` snips the current timeline at some depth and grows a new branch
from there. Branches form a tree; `origins[b-1]` is branch `b`'s parent edge,
labelled with the `fork_depth` (how deep the parent was when branch `b` budded).

```
 depth
   3            t_old ✗            ← token at depth 3 on branch 0
   2        ┌───┘                    (cut: branch 1 forked from branch 0 at depth 1)
   1     ●──┴───────●  fork_depth=1
   0  ───┴───branch0─┴───branch1(current)───
          branch 0           branch 1

 is_valid checks, current = branch 1:
   token{branch=1, depth≤current}      → valid   (same branch, in range)
   token{branch=0, depth≤fork_depth=1} → valid   (ancestor, at/below the cut)
   token{branch=0, depth=3 > 1}        → INVALID  (t_old: on the abandoned
                                                    future, above the cut)
```

So after `restore` cuts branch 0 at depth 1 and we work on branch 1, any
branch-0 token deeper than 1 (a snapshot from the discarded future) is
rejected; branch-0 tokens at depth ≤ 1 (genuine ancestors of the current
state) stay valid. That is **branch-cut safety**.

### Properties to prove (M5b)

Model `ForkHistory` as a ghost **fork tree** (each branch a node, edge to
parent labelled with `fork_depth`). Then prove `is_valid(token)` is exactly:

> `token.branch_id` is `current_branch_id` or one of its ancestors, **and**
> `token.depth` is within the live (un-cut) prefix of that branch — i.e.
> `≤ current_depth` on the current branch, or `≤ fork_depth` of the child edge
> on the path down to the current branch.

Soundness consequence to connect to the snapshot theorem: **if `is_valid(token)`
then `token.frame_index` still denotes the same logical snapshot it did at
mark time** — so the existing `restore` correctness theorem (`view() ==
snapshots[token.frame_idx]`) composes with validity to give "restore with a
*valid* token reproduces the snapshot that token was minted for", even across
intervening restores/re-marks. The `is_valid` walk terminates because it climbs
strictly toward the root (`parent_branch_id < branch` by construction, since
parents are older); that termination + the path characterization are the two
core lemmas.

Effort: comparable to the M4 nested-restore proof. Scheduled after push/pop.

---

## 10. What's proved vs pending (summary)

Proved, no admits/assumes, arbitrary nesting depth:
- push, set, get, mark, restore, and **transient** pop, with the headline
  `view() == snapshots[token.frame_idx]` restore theorem.
- Both storage backends satisfy the DiffStore contract.
- Production `Frame.saved_len` u32→I truncation bug fixed (and mirrored).

Pending:
- Faithful pop (pop into the marked region) — §8. Design fully understood;
  central-lemma restatement (flat/target-clamped) + invariant relaxations
  remain.
- Fork history / branch-cut safety — §9, not started.
- `TRACK = false` observational-equivalence theorem.
- Other containers (AppendOnlyVec, Map, SparseSet, BPlusTreeSet, ListArena).

### Verus tactics worth remembering
- When all `wf` sub-conjuncts verify under `--expand-errors` but the aggregate
  `self.wf()` fails: add `#[verifier::spinoff_prover]` + `#[verifier::rlimit]`
  — it's solver budget, not a soundness gap.
- Factor per-cell invariants into named spec fns for stable `forall` triggers.
- One milestone per commit; always leave the tree verifying; never commit a
  broken half-migration.
