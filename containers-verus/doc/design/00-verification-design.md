# Master Verification Design — Semi-Persistent Containers

[Table of Contents](00-table-of-contents.md)


This is the master design document for `containers-verus`, the Verus port of
the production semi-persistent vector in `../containers`. It explains the
theorems we prove and why they are the right ones, then the data layout,
storage abstraction, and invariants that make those theorems provable. Read
§0 first; the rest is the machinery behind it. See the
[table of contents](00-table-of-contents.md) for companion documents.

The whole vector — `push`, `pop` (including into a marked region), `set`,
`get`, `mark`, `restore` — is verified at arbitrary mark-nesting depth, along
with fork-history / branch-cut safety, with **no `admit`s or `assume`s**. Run
`./verify-all.sh` from the package root for the current per-module count.

---

## 0. The theorems we prove, and why they are the right ones

A semi-persistent vector is a mutable vector that can be *snapshotted* in O(1)
(`mark`) and *rolled back* to a snapshot in O(k) (`restore`, k = mutations
since the mark), without ever copying the vector. The entire reason it is hard
— and worth verifying — is that it achieves rollback **without storing the
snapshots**: it keeps only a *diff log* of overwritten values and replays it
backwards. So the central question a proof must answer is:

> Does replaying the diff log actually reconstruct the snapshot — exactly, at
> any nesting depth, after any interleaving of pushes, sets, and pops?

That question decomposes into four theorems. Each one rules out a specific way
the data structure could silently corrupt state; together they give end-to-end
correctness. They are stated informally here and precisely in the sections
that follow.

### Theorem 1 — Reconstruction (the headline)

> After `restore(token)`, `view() == snapshots[token.frame_idx]`.

`view(): Seq<T>` is the user-visible contents. `snapshots[k]` is the contents
at the moment frame `k` was marked — a **ghost** sequence that exists only in
the proof. This is the right top-level statement because it is exactly the
user's mental model ("restore puts back what was there at mark time") and
because it pins down the value of *every* cell, leaving no room for an
off-by-one or a stale entry to hide. Crucially `snapshots` is ghost: the
theorem asserts the structure can *recompute* the snapshot from the diff log,
which is the entire performance claim. If we stored the snapshots, the theorem
would be trivial and the data structure pointless.

*Why not a weaker statement?* "restore restores the length" or "restore
restores cell 0" would both pass while corrupting other cells. Full sequence
equality is the weakest statement that is also airtight.

### Theorem 2 — The diff log is a faithful, bounded encoding

Reconstruction is only meaningful if the diff log itself is well-formed. Two
sub-properties, both captured by the `wf` invariant (§6):

- **Coverage**: every cell that has *left* the live view (was popped out of a
  marked region) has a diff entry recording its marked value. The
  contrapositive — "no diff ⟹ still present and unchanged" — is what guarantees
  replay can find every value it needs. Without coverage, restore could be
  asked to resurrect a cell whose value was never recorded.
- **Uniqueness / first-write-wins**: each cell is captured *at most once per
  frame*. This is what bounds the log to O(saved_len) per frame (not unbounded
  — see the DoS discussion in §8 and `restore-regrow-alternatives.md`) and
  what makes "the entry for cell j" well-defined.

These are the right auxiliary theorems because reconstruction is *false*
without them: they are precisely the gap between "we have some log" and "the
log determines the snapshot."

### Theorem 3 — The runtime capture flag faithfully mirrors the ghost log

The structure carries one bit per cell (`captured()`) telling `set`/`pop`
whether this cell has already been logged in the current frame — that is how
first-write-wins is enforced at runtime. The **bridge** theorem says this bit
is never out of sync with the ghost diff log:

> `captured()[j]` is set ⟺ cell `j` has an entry in the current (top) frame's
> stratum of the diff log.

This is the right theorem because the runtime bit and the ghost log are two
representations of the same fact, and *every* operation's correctness depends
on them agreeing — a desynchronized flag would either double-log (breaking the
bound) or skip a needed capture (breaking coverage). The bridge is what lets
the imperative code trust a single bit instead of scanning the log.

### Theorem 4 — Token validity: only honest tokens restore (branch-cut safety)

`mark` hands out a token; `restore` consumes one. A token names a frame, but
frame indices are reused after rollback, so a *stale* token from an abandoned
branch of the search could name a frame that no longer means what the token
thinks. The fork-history theorem characterizes exactly which tokens are valid:

> A token is valid ⟺ its branch is on the current path of the fork tree and
> its depth is within that branch's live (un-cut) prefix.

This is the right theorem because it is the precise boundary between "restoring
to a genuine ancestor of the current state" (safe, reproduces that ancestor)
and "restoring to a discarded future" (must be rejected). It is what makes the
snapshot theorem *composable across backtracking*: with a valid token,
Theorem 1's guarantee survives intervening restores and re-marks.

### How they compose

`mark` establishes Theorems 2–3 for a fresh empty frame. `set`, `push`, and
`pop` each *maintain* coverage, uniqueness, and the bridge as they mutate.
`restore` *uses* coverage + uniqueness to prove the diff replay reconstructs
the snapshot (Theorem 1), re-establishes the bridge for the frame it lands in,
and records a fork-tree cut so Theorem 4 keeps rejecting now-stale tokens. The
rest of this document builds the machinery — the storage abstraction (§3–4),
the `wf` invariant that carries Theorems 2–3 (§6), the per-operation
maintenance proofs (§7–8), and the fork tree for Theorem 4 (§9) — and shows,
operation by operation, that the four theorems hold.

A fifth, orthogonal guarantee — when no marks are live the structure behaves as
a plain `std::Vec` with zero tracking overhead — is the `TRACK=false` story
(§7); it matters for the "you don't pay for what you don't use" claim but is
not part of the reconstruction argument.

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

## 8. Faithful pop — the hard part, and how it was proved

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

### How faithful pop landed

The pieces, in the order they were built (each kept the tree green): the store
methods `mark_captured`/`resize_default`; the `frame_cell_inv` coverage
refactor and the `wf_for_snap` split; the **flat, target-clamped central
lemma** (§3 of `flat-central-lemma-design.md`) that reconstructs one cell at a
time and so needs no `saved_len` monotonicity; dropping the two now-false `wf`
clauses; the `restore` body (resize to the target's `saved_len`, then replay);
`push`'s `mark_captured` on re-entry; and `pop`'s conditional capture into the
marked region. The chronological account, including the reverted attempts, is
in [the proof attempts log](proof-attempts-log.md).

---

## 9. Fork history / branch-cut safety

> **Authoritative formal statement: [`m5-fork-history-design.md`](m5-fork-history-design.md) §0.6** —
> precise definitions of the fork tree, how a cut is recorded, "on the current
> path", the per-branch depth bound, and the branch-safety theorem. This
> section is the informal overview; where the prose below uses loose words
> ("timeline", etc.) the §0.6 definitions govern.

Mark/restore alone is not memory-safe against **stale tokens** (Theorem 4 of
§0). The frame index in a token can be reused: restore past a mark, then mark
again — the new frame reuses the old index, but it denotes a *different*
logical snapshot. A token naming the rolled-back position must be rejected, or
restoring with it would roll back to a frame that no longer means what the
token records. Two mechanisms together close this, both verified and wired into
`Vec`: a per-container identity (§9.1) and the fork-history branch-cut theorem
(§9.2).

### 9.1 Container identity

```
ContainerId(u32)                    // from a global atomic counter
VecToken { …, container_id }        // every token records its origin Vec
```

`restore` asserts `token.container_id == self.id`. Rejects using one vec's
token on a *different* vec. Property to prove: a token validated against a Vec
was minted by that Vec. Modeled with a ghost unique id per Vec; cheap.

### 9.2 Fork history — the branch-cut theorem

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

### The characterization (proved)

`ForkHistory` is modeled as a ghost **fork tree** (each branch a node, edge to
parent labelled with `fork_depth`). `lemma_fork_valid_characterization` proves
`is_valid(token)` is exactly:

> `token.branch_id` is `current_branch_id` or one of its ancestors, **and**
> `token.depth` is within the live (un-cut) prefix of that branch — i.e.
> `≤ current_depth` on the current branch, or `≤ fork_depth` of the child edge
> on the path down to the current branch.

This is what connects Theorem 4 back to Theorem 1: **if `is_valid(token)` then
`token.frame_index` still denotes the same logical snapshot it did at mark
time**, so the reconstruction theorem (`view() == snapshots[token.frame_idx]`)
composes with validity to give "restore with a *valid* token reproduces the
snapshot that token was minted for", even across intervening restores and
re-marks. The walk terminates because it descends strictly toward the root
(`parent_branch_id < branch` by construction — `fh_wf`); that termination plus
the path characterization are the two core lemmas, both discharged in
`fork_history.rs`.

---

## 10. What is verified

Everything below is proved with no `admit`s or `assume`s, at arbitrary
mark-nesting depth. Run `./verify-all.sh` for the live per-module count.

**The four core theorems of §0** — reconstruction, diff-log faithfulness
(coverage + uniqueness), the runtime↔ghost capture bridge, and token validity
(branch-cut safety) — hold for the full vector API: `push`, `set`, `get`,
`mark`, `restore`, and **faithful `pop`** (popping into a marked region, the
hard case). The branch-safety theorem is `lemma_fork_valid_characterization`,
wired into `Vec` via `VecToken { branch_id, depth, container_id }`, a `restore`
that requires `is_token_valid_spec`, and the `forks.fork(...)` cut.

Also verified: both storage backends (`InlineStore`, `ParallelStore`) satisfy
the `DiffStore` contract; the `TRACK=false` guarantee (an unmarked vector is
observably a plain `std::Vec` with zero tracking overhead); and full
production API parity (`with_store`/`new`, `depth`, `is_valid_token`,
`VecView`/`VecViewIter`, `ShrinkPolicy` + `mark`, byte-accounting).

The verification also **found and fixed a real production bug**: a silent
`u32` truncation in `Frame.saved_len` (corrected in both trees).

**Container family.** The same four-theorem template is reused for the
containers built on `Vec`: `AppendOnlyVec`, `Map`, `SparseSet` (refined to a
ghost set + index pool), and `ListArena` (chain semantics + acyclicity). See
their modules and the [table of contents](00-table-of-contents.md).

**Deliberate divergences from production** (documented, not gaps): `T: Copy +
Default` instead of `T: Clone` (`Copy ⊂ Clone` suffices for the e-graph
domain; `Default` enables the DoS-free bounded-capture pop — see
`restore-regrow-alternatives.md`); `as_slice` omitted (a backend-specific fast
path outside the persistence contract).

**Remaining work**: `ListArena` `append`/`splice` (need acyclicity decoupled
from arena index — see the proof-attempts log); the generalized multi-size
`BPlusTreeSet`.

### Verus tactics worth remembering
- When all `wf` sub-conjuncts verify under `--expand-errors` but the aggregate
  `self.wf()` fails: add `#[verifier::spinoff_prover]` + `#[verifier::rlimit]`
  — it's solver budget, not a soundness gap.
- Factor per-cell invariants into named spec fns for stable `forall` triggers.
- One milestone per commit; always leave the tree verifying; never commit a
  broken half-migration.
