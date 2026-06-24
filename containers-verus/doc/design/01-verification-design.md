# A Verified Library of Semi-Persistent Containers

*Master design document for `containers-verus`: the Verus port of the
production [`semi-persistent-containers`](../../../containers) crate.*

[Table of Contents](00-table-of-contents.md)

## 1. Overview

The crate verifies a core semi-persistent data structure in depth and then reuses
it to implement other semi-persistent data structures.

**The semi-persistent vector.** A vector supporting `mark()` and
`restore(token)`. Its externally-observable specification is a stack of deep
copies: `mark` deep-copies the current contents onto the stack, `restore(token)`
pops back to the marked level, discarding the entries above it. The
implementation does not store those copies; it keeps a **sparse negative diff**:
the first write to a cell after a mark logs that cell's old value, and later
writes to the same cell do not create diff entries. `restore` truncates the log
to the mark and replays the recorded values in reverse. Memory is proportional 
to the number of modified cells since the mark, and `restore` runs in time
proportional to the diff. No deep copy is materialized: a marked state is the
current contents minus the diffs recorded since. 
(`mark` is not unconditionally O(1), it resets per-cell capture state, sublinear
with the packed bitset and O(diff-size) for the inline backend, but never a deep
copy; the design objective is the memory bound.)

The diff representation can diverge from the deep-copy specification through a
faulty replay (a dropped entry, a wrong replay order, a cell restored from the
wrong mark), so the central theorem is their equivalence. The vector carries a
**ghost field** `snapshots`: the stack of deep copies, defined in ghost code
(erased before compilation, so the compiled vector retains only the sparse diff).
It is the specification of what each mark must preserve, and the theorem states that
the diff engine reproduces it:

> after `restore(token)`, `view() == snapshots[token.frame_idx]`

This holds per cell, at arbitrary mark-nesting depth, under any interleaving of `push`,
`set`, and `pop`. A companion result constrains which tokens `restore` accepts:
each `mark` opens a branch in a fork history, each `restore` cuts the branches it
discards, and a token naming a discarded state is rejected.

**The container family.** The verified vector is also used as a **backtrackable arena
allocator**: a pool of integer-indexed slots that inherits semi-persistence from
the underlying vector. On it the crate builds and proves a family of further
containers: an append-only vector, a hash map, a sparse set (a bijection refining
to a ghost set plus an index pool), an intrusive linked-list arena
(`prepend`/`append`/`splice`), a circular class-list (O(1) ring merge by pointer
swap), and a B+tree set. These are all the core data structures needed to build
a semi-persistent e-graph data structure. Several are internally **aliased** and
**cyclic**: they connect nodes by integer index rather than Rust reference, which
bypasses ownership and borrow checking, leaving Verus verification as the sole
correctness guarantee. They are verified in an explicit **dynamic-frames** style:
a ghost field names each structure as sets of unique arena ids, and aliasing,
separation, and shape are proved as predicates over those ids
([§10](#10-why-these-proofs-arenas-integers-as-pointers-and-explicit-aliasing),
[Chapter 9](09-arena-aliasing-dynamic-frames.md)).

The whole development carries no `admit`s or `assume`s; run `./verify-all.sh` for
the per-module tally. ("No `admit`s/`assume`s" does not mean nothing is trusted:
the trust boundary is 7 `external_body` items, enumerated and justified in
[Chapter 2](02-trust-boundary.md). Read it to know exactly what is guaranteed.)

The rest of this document is the machinery: the layered architecture (§2), the
capture-bit storage abstraction and its two backends (§3–4), the vector's layout
(§5), the well-formedness invariant (§6), the operation maintenance proofs
including pop into a marked region (§7–8), fork-history soundness (§9), the
arena-container proof style (§10), and a summary of what is verified (§11).

---

## 2. Layered module architecture

```
L0  tagged.rs / index_like.rs   trait specs: niche / bijection axioms
    dense_id.rs                 DenseId31 — one type, both IndexLike + Tagged
L1  diff_store.rs               DiffStore trait — the capture-protocol contract
L2  capture_bits.rs             CaptureBits — packed Vec<u64> bit-vector
    parallel_store.rs           ParallelStore<T,I> (T: Copy)   over CaptureBits
    inline_store.rs             InlineStore<T,I>   (T: Tagged)  over T::Repr
L3  frame.rs                    Frame<I> { saved_len: I, diff_start: usize }
L4  vec.rs                      Vec<T,I,S,TRACK> — proofs over the trait specs
```

`Vec`'s proof talks only to the `DiffStore` *contract*, so it is parametric in
storage. Two backends satisfy that contract; and §3–4 are about *where each puts
the one capture bit per cell*, the choice the rest of the proof is blind to.

---

## 3. The capture bit and its two modes of storage

### One bit per cell

The diff log turns on a single question, asked of a cell on every mutation: *has
this cell already been captured since the last mark?* If it has, the mutation is
a re-write: the log already holds the cell's mark-time value, so nothing is
recorded. If not, this is the first write since the mark, and the old value must
be logged before it is lost. First-write-wins, and with it the entire memory
argument, rests on answering that question correctly for every cell.

The answer is one bit of state per cell: *captured* or not. The vector must hold
`view.len()` such bits; `mark` clears them, the first write to a cell sets its
bit, every mutation reads one. *Where those bits live* is the subject of this
section. The reconstruction theorem never mentions them, so the choice is
invisible to diff replay correctness; but it decides the memory footprint and the
cache cost of a mutation. So the choice hides behind a trait, the vector is proved
once against the abstraction (§4–8), and two concrete backends are supplied: one
that stores the bit inline with the value (by wrapping the value in a tuple, or 
by stealing a bit from a niche in the type), and one that stores the bit in a
parallel bitvector.

### `Tagged`: carving the bit out of the value

The most cache-friendly place for a cell's capture bit is *inside the cell*.
A vector of pool-allocated identifiers never uses the full width of its storage
word: a 32-bit id can still address two billion entries in 31 bits while leaving
the top bit usable as a niche. Spending that idle bit on the capture flag costs
no memory and keeps the flag on the same cache line as its value, so a mutation
touches one word rather than chasing a second allocation. The design turns on the
distinction between a word's *storage* width and its *used* width: a `DenseId31`
stores 32 bits but uses only the low 31 for its value, reserving the 32nd as a
control bit.

Carving a control bit out of a value's word is exactly the bit-twiddling that
silently corrupts data when a mask is wrong, so the `Tagged` trait makes the
nich carving soundness a actual proof obligation. A `Tagged` type names a
representation `Repr` (the stored word) and three ghost projections: `value_of(r)`
(the clean value, control bit masked away), `tag_of(r)` (the control bit), and
`repr_wf(r)` (the *niche predicate*: which reprs are in the image of the
encoding). The exec surface is `into_repr`/`from_repr`/`tag`/`set_tag`/`clear_tag`,
each contracted against those projections. Two obligations make the encoding
sound, exactly the ones a wrong mask would break:

- **Tag edits do not disturb the value.** `set_tag`/`clear_tag` preserve
  `value_of` (and `repr_wf`). This lets the vector flip a cell's capture flag at
  will: `data()` is `value_of` read across the cells, invariant under tag edits,
  so `view()` is invariant under capture-flag edits. Without it, marking a cell
  could change the cell.
- **The encoding is injective: the niche axiom.** `lemma_repr_extensional`: two
  well-formed reprs with equal `value_of` and equal `tag_of` are equal. The value
  and the tag together pin down the whole word, so the stolen bit wastes no state
  space and `from_repr` inverts `into_repr`.

A type with no spare bit uses the fallback `BoolTagged<T>`, which stores the tag
in a separate `bool` field; it steals nothing, so `repr_wf` is `true` everywhere
and the niche axiom is vacuous. The impl that makes the obligations *bite* is
`DenseId31`, below.

### `DiffStore`: the protocol that consults the bit

The vector never touches a `Tagged` repr or a capture bit directly. It speaks to
a backend through the `DiffStore` trait, which owns the data sequence and the
capture flags and exposes them as two ghost views, `data(): Seq<T>` and
`captured(): Seq<bool>`, tied by `wf()` to equal length. `DiffStore` is the
capture *protocol* (full contract in §4); it is the seam that makes the two ways
of storing the capture bit two implementations of one trait, neither visible to
the reconstruction theorem.

### `IndexLike` and `DenseId31`: the bit packed inline

`InlineStore<T: Tagged>` is the zero-overhead backend: a single `Vec<T::Repr>`
where each cell *is* a tagged word, its capture bit in the stolen niche. `data()`
is `value_of` across the reprs, `captured()` is `tag_of` across them, both read
from the same physical vector, and `wf()` asks every stored repr be `repr_wf`.
The capture protocol becomes pure bit manipulation, leaving `value_of` (hence
`data()`) untouched by the tag-edit obligation.

`DenseId31` (in `dense_id.rs`) ties the two trait layers together: it is *both*
`Tagged` (stored with the flag packed inline) and `IndexLike` (indexes a vector),
one type in both roles as production's `define_id31!` ids are. It is a `u32`
whose top bit is reserved: a type invariant pins a clean id below `2^31`, the
`Repr` is the bare `u32` with the MSB carrying the tag. The niche axiom is a
genuine bit-vector theorem (*two words agreeing on their low 31 bits and their
MSB are equal*), discharged by Verus's solver against a real stolen bit, not the
fallback's vacuous `repr_wf := true`. On the `IndexLike` side `as_nat` is the
identity on the clean value (injectivity immediate); the `[0, 2^31)` bound comes
from the type invariant, read via `lemma_as_nat_bounded(tracked self)`; the
tracked receiver is what lets a Verus type invariant be consulted in the proof,
and is what lets one `u32`-backed type carry both a tight index bound and an
inline niche. The witness `lemma_dense_id31_indexes_and_stores_itself` discharges
`InlineStore<DenseId31, DenseId31>`, the same id type indexing the store and
stored in it.

### `ParallelStore` and `CaptureBits`: the packed-bitset fallback

When the stored type has no spare bit, the flags move into a side structure.
`ParallelStore<T: Copy>` holds the data in a plain `Vec<T>` and the flags in a
parallel bit-vector; `wf()` keeps the two the same length. It asks nothing of `T`
beyond `Copy`, at the cost of one bit per cell plus the cache jump from a value to
its flag in a separate allocation, exactly what `InlineStore` avoids.

The flags use the same packed form as production: `CaptureBits` (in
`capture_bits.rs`) is a `Vec<u64>`, bit `i` in word `i/64` at position `i%64`,
under a ghost `Seq<bool>` view, eight times denser than a `Vec<bool>`. Each op
(`get`/`set`/`push`/`pop`/`truncate`) is proved to refine the ghost-sequence op,
the per-bit reasoning by the bit-vector solver (the delicate case being `set`,
which must leave every *other* bit's view unchanged). Because `CaptureBits` *is* a
`Seq<bool>` through its view, the packing is verified in isolation and is
invisible above.

Both backends discharge `lemma_wf_captured_len` and the value-invariance of
capture-bit edits, so the vector cannot tell them apart.

---

## 4. The DiffStore capture-protocol contract (L1)

Ghost views: `data(): Seq<T>`, `captured(): Seq<bool>`, `wf(): bool`. Methods:

- `push / pop / get / set_raw / truncate`: raw data ops; `set_raw` preserves the
  capture flag at the written slot.
- `prepare_mark(saved_len, prev_diffs)`: clear `captured[0..saved_len]` so the
  new frame captures fresh.
- `capture(i, saved_len, diff_log)`: **first-write-wins**: if
  `i < saved_len && !captured[i]`, append `(data[i], i)` and set `captured[i]`;
  else no-op (the postcondition spells this out so an impl can't satisfy it
  vacuously).
- `force_capture(i, saved_len, diff_log)`: *unconditional* capture (production
  uses it for pop). Bounded-log designs avoid it (§8).
- `restore_entry(idx, old, target_saved_len)`: the replay step. Drops
  `idx >= target_saved_len`; pushes if `idx == data.len()` (regrow); else
  overwrites. **Everything gated by the TARGET's saved_len.**
- `finish_restore(surviving_diffs, saved_len)`: rebuild `captured` from the
  surviving top stratum.
- `mark_captured(i)` / `resize_default(len)`: for pop into the marked region
  (§8): set one flag; truncate-or-grow-with-`T::default()`.

---

## 5. Vec layout (L4)

```
struct Vec<T, I, S, const TRACK: bool> {
    store: S,                        // the DiffStore backend
    diff_log: std::vec::Vec<(T,I)>,  // (old_value, index) entries, all frames
    frames:   std::vec::Vec<Frame<I>>,
    active_saved_len: I,             // cached saved_len of the top frame
    snapshots: Ghost<Seq<Seq<T>>>,   // GHOST: deep copy per frame
}
Frame<I> { saved_len: I, diff_start: usize }
```

- `view() == store.data()`.
- The diff log is **stratified**: frame `k` owns the slice
  `[frames[k].diff_start, stratum_end(k))`, where `stratum_end(k)` is
  `frames[k+1].diff_start` (inner) or `diff_log.len()` (top). Each capture while
  frame `k` is active lands in stratum `k`.
- `Frame.saved_len: I` (not `u32`): a `u32` field silently truncated past 4 G
  slots for `I = u64`; this corrected a real production bug. `diff_start: usize`
  indexes the log.

#### 2D picture: stratification (nested marks)

One flat `diff_log`, partitioned by `diff_start` into per-frame strata. Each
frame's `frame_inv_range` runs over its own stratum, with `layer_above` = the
next-deeper snapshot (or the view, for the top frame):

```
                       diff_log positions →
        0    1    2    3    4    5    6    7
      ┌────┬────┬────┬────┬────┬────┬────┬────┐
      │ d0   d1 │ d2 │ d3   d4   d5 │ d6   d7 │ ......
      └────┴────┴────┴────┴────┴────┴────┴────┘
        └ stratum 0 ┘└ str 1 ┘└─── stratum 2 (top) ───┘
   frame:   0          1            2
 diff_start 0          2            5         (n = 8)

 layer_above(0) = snapshots[1]    overlay stratum 0 onto snap[1] ⇒ snap[0]
 layer_above(1) = snapshots[2]    overlay stratum 1 onto snap[2] ⇒ snap[1]
 layer_above(2) = view()          overlay stratum 2 onto view   ⇒ snap[2]
```

`restore(target)` replays `diff_log[diff_start_target .. n]`, the union of strata
`target..top`, in reverse. The central lemma proves this equals
`snapshots[target]` by composing the per-stratum overlays top-down.

---

## 6. The invariant: `wf` = `wf_for_snap` + bridge

### `wf_for_snap()`: snapshot-reconstruction core

1. `store.wf()`.
2. `snapshots.len() == frames.len()` (parallel stacks).
3. `frames.len()==0 ⟹ diff_log empty`.
4. `frames[0].diff_start == 0`; `frames[top].diff_start <= diff_log.len()`.
5. `frames[top].saved_len <= view.len()`: "view is full". **(This and the
   saved_len-monotone clause are the two that pop into the marked region relaxes,
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

`wf` is split into `wf_for_snap` + bridge precisely because `resize_default`
(restore's regrow) preserves `wf_for_snap` but breaks the bridge; so the
reconstruction lemmas run on `wf_for_snap`.

### `frame_cell_inv`: the per-cell declarative invariant (the key idea)

`frame_inv_range`'s heart is a `forall j < saved_len . frame_cell_inv(...)`:

```
frame_cell_inv(above, diffs, lo, hi, snap, j) :=
    if  no entry in stratum [lo,hi) hits j (UNCAPTURED):
            j < above.len()  &&  above[j] == snap[j]
    else (CAPTURED):
            some entry (old, j) in [lo,hi) has old == snap[j]
```

Read declaratively:

> Each marked cell's snapshot value lives in **exactly one** of two places: if
> untouched since mark, in the **view** itself (and the cell is still present);
> if overwritten/popped, in the **diff log**.

The **coverage** consequence, the linchpin for pop, is the contrapositive of
the uncaptured case: `j ≥ above.len() ⟹ captured`. Every cell that has left the
layer-above (was popped) must have a diff entry. There is no third state: a cell
can't be both absent from the view and absent from the log.

#### 2D picture: one frame's invariant

Columns = vector index `j`; the diff-log row holds this stratum's entries (at most
one per column: first-write-wins); the bottom rows are the live `view` and the
ghost `snap` we must rebuild.

```
            j=0    j=1    j=2    j=3    j=4
 stratum  │      │      │(C,2) │      │(E,4) │   captured columns: 2, 4
          └──────┴──────┴──────┴──────┴──────┘
 view  =  [  A      B      x      D      y  ]    x,y = scribbles written since mark
 snap  =  [  A      B      C      D      E  ]    (target; ghost)
             ↑u     ↑u     ↑cap   ↑u     ↑cap     u = uncaptured, cap = captured
```

| col | captured? | where `snap[j]` lives                       | case       |
|-----|-----------|---------------------------------------------|------------|
| 0 A | no        | `view[0]` (== snap, untouched)              | uncaptured |
| 1 B | no        | `view[1]`                                   | uncaptured |
| 2 C | yes       | diff entry `(C,2)`  (view holds scribble x) | captured   |
| 3 D | no        | `view[3]`                                   | uncaptured |
| 4 E | yes       | diff entry `(E,4)`  (view holds scribble y) | captured   |

Restore = overlay the diff row back onto the view: write each `(old,j)` at column
`j`. Uncaptured columns already equal `snap`; captured columns get their `old`
back. Result == `snap`. The **lowest-position** entry per column wins (applied
outermost), which matters once a column has more than one entry (§8).

Plus stratum-local structural facts: entries in stratum k have `idx <
saved_len_k`, and indices are **unique within a stratum** (first-write-wins).
Across strata the same index may recur.

`frame_cell_inv` is a *named* spec fn (not an inlined if-then-else) so
`frame_inv_range`'s `forall j` has a clean `#[trigger]` Verus re-assembles
reliably, the fix for a multi-session reassembly blocker.

---

## 7. How each operation maintains the invariant

`view()`, `len`, `is_empty`, `get`: read-only; trivially preserve `wf`.

**`push(v)`**: `store.push(v)`. diff_log/frames/snapshots unchanged; the view
grows by one at the end. Inner frames reference snapshots (unchanged). The top
frame's layer is the view: its `frame_cell_inv` transfers per-cell because the
`[0, old_len)` prefix is preserved and the new cell is past every `saved_len`.

**`set(i, v)`** under an active frame: `capture(i, active, diff_log)` then
`set_raw(i, v)`. Per-cell, split on `j == i`:
- `j ≠ i`: view[j] and captured-status unchanged ⇒ both cases inherited.
- `j == i`: now captured. If `capture` appended, the new entry holds
  `old_view[i]`, which equals `snap[i]` because i was uncaptured. If i was already
  captured, the existing entry still holds `snap[i]`. The **bridge** tells the
  proof which (`store.captured()[i]`), matching first-write-wins.

**`pop()`** (transient-only, current default): `store.pop()`. Precondition
`active_saved_len < view.len()`: only pop a cell *above* every frame's marked
region, so no frame_inv cell is affected. (Pop into the marked region lifts this,
§8.)

**`mark()`**: `prepare_mark`, push `snapshots.push(view)` and
`Frame { saved_len: view.len(), diff_start: diff_log.len() }`, set
`active_saved_len`. The new top stratum is **empty**, so its `frame_cell_inv` is
all-uncaptured (`view[j] == snap[j]` is `view[j] == view[j]`). The previously-top
frame's layer flips from `view` to `snapshots[top]` (the view at mark time).

**`restore(token)`**: truncate to `saved_len_target`, then replay
`diff_log[diff_start_target .. n]` in reverse via `restore_entry`. The `overlay`
spec models the loop: lower-index entries applied outermost, so the
**lowest-position entry per cell wins**. The central lemma proves
`overlay(view, diffs, diff_start_target, n) == snapshots[target]` on
`[0, saved_len_target)` by downward induction over frames. Then truncate +
`finish_restore` rebuild the bridge; snapshots/frames truncated to `target`.

---

## 8. Pop into a marked region: the hard part

Production allows **popping a cell with `index < saved_len`**. On restore that pop
"becomes a push": the regrown slot needs a real `T`. The crate supplies it with
**Default + resize** (option A of [Chapter 6](06-restore-regrow-alternatives.md)):
pop uses *conditional* capture (keeping the log bounded), and restore
`resize_default`s the view back up with `T::default()` fillers that the replay
overwrites. This needs `T: Default` and keeps restore O(k). The two rejected
alternatives are production's *force-record* (pop logs unconditionally; correct
but a `push/pop` loop grows the log without bound, a latent DoS) and a Clone-scan
regrow (no Default, but a log-factor slower restore).

**Why the fillers are sound: they are never observable.** Every filler sits in a
popped cell, which coverage guarantees is captured, so the replay overwrites it.
This is *entailed by the headline theorem* `view() == snapshots[k]`; a surviving
filler would make `view() != snapshot`. So `T::default()`'s value is never
constrained.

#### 2D picture: pop into the marked region, then restore

`saved_len = 5`, `snap = [A,B,C,D,E]`. `set(2,X)` captures C, then pop twice into
the marked region (conditional capture logs a popped cell only if not already
captured):

```
 step          stratum (diff entries)        view            note
 mark(5)       (none)                        [A B C D E]
 set(2,X)      (C,2)                         [A B X D E]    capture C
 pop()  j=4    (C,2)(E,4)                    [A B X D]      j=4 uncaptured → log E
 pop()  j=3    (C,2)(E,4)(D,3)               [A B X]        j=3 uncaptured → log D
```

Now `view.len() = 3 < saved_len = 5`. The **gap** `[3,5)` is the popped region,
and coverage holds, every gap column has a diff:

```
            j=0   j=1   j=2   j=3   j=4
 stratum  │     │     │(C,2)│(D,3)│(E,4)│
          └─────┴─────┴─────┴─────┴─────┘
 view  =  [ A     B     X ]  ╎     ╎      present: [0,3);  gap [3,5)
 snap  =  [ A     B     C    D     E ]    (target, len 5)
            ↑u    ↑u    ↑cap  ↑cap  ↑cap   j≥view.len() ⇒ MUST be captured
```

restore, clamped to `saved_len = 5`:

```
 resize_default(5):  [ A  B  X  d  d ]        d = T::default() fillers in the gap
 replay (lowest-position wins):
      (E,4): col 4 < 5 → [ A B X d E ]
      (D,3): col 3 < 5 → [ A B X D E ]
      (C,2): col 2 < 5 → [ A B C D E ]   == snap  ✓
```

### The two invariant relaxations, and the one new obligation

Pop into the marked region relaxes two `wf` clauses and adds one fact:

1. **Drop "frames[top].saved_len <= view.len()"** (clause 5): after popping into
   the marked region the view is *shorter* than saved_len. The dependent lemmas
   take "view is full" as an explicit hypothesis that **restore re-establishes via
   `resize_default`** before reconstructing.
2. **Drop "saved_len monotone"**: `mark` after a deep pop records the current
   short view, so saved_lens are not monotone. The replacement is per-frame
   **coverage** (already in `frame_cell_inv`): for cells beyond the layer-above's
   length, the central lemma's inductive step uses the *captured* case (frame k's
   own diff) instead of the layer. No new clause: use coverage, stop using
   monotonicity.
3. **`push` must `mark_captured`** a cell re-entering the marked region (after pop
   then push, `old_len < active_saved_len`): the pop already captured `snap[i]`,
   so the fresh slot inherits the captured flag, or a later `set` would re-capture
   and grow the log unbounded.

Plus the target-clamping that makes it all bounded: `restore_entry` drops any
`idx >= target_saved_len`, so restore regrows to *exactly* the target's saved_len
and over-range diffs from deeper strata simply vanish; the view never needs to
reach `max(saved_len)`. The reconstruction lemma is correspondingly stated **flat
and target-clamped** ([Chapter 5](05-flat-central-lemma.md)), reconstructing one
cell at a time, which is what lets it need no `saved_len` monotonicity.

**Coverage and uniqueness are the whole proof.** Coverage: every cell `j` with
`layer_above_k.len() ≤ j < saved_len_k` is captured in stratum k. Uniqueness:
within a stratum each index appears at most once. Nothing about `T::default()`'s
value is ever needed. How each op handles them (top frame's `layer_above` is the
live `view`; the gap is `[view.len(), saved_len)`):

| op | coverage | uniqueness |
|----|----------|------------|
| **mark** | establishes: `saved_len := view.len()`, gap empty | establishes: new stratum empty |
| **set(i,v)** | maintains: view length unchanged; `i` below the gap | maintains: first-write-wins → `i` ≤ once |
| **pop()** | maintains: removing `i` grows the gap; `pop` captures `i` first (holding `snap[i]`) | maintains: conditional capture → still ≤ 1 entry |
| **push(v)** | cell leaves the gap; n/a | maintains: re-entry calls `mark_captured` so a later `set` won't append again |
| **restore(t)** | uses: padded cells are exactly the gap, all captured ⇒ each filler overwritten | uses: lowest-position-in-range entry per cell is unambiguous |

---

## 9. Fork history / branch-cut safety

> **Authoritative formal statement: [`03-fork-history.md`](03-fork-history.md)**:
> the fork tree, how a cut is recorded, "on the current path", the per-branch
> depth bound, and the branch-safety theorem (§3). This section is the informal
> overview.

Mark/restore alone is not safe against **stale tokens**. A token's frame index
can be reused: restore past a mark, then mark again, the new frame reuses the old
index but denotes a *different* logical snapshot. A token naming the rolled-back
position must be rejected. Two mechanisms close this, both verified and wired into
`Vec`:

### 9.1 Container identity

```
ContainerId(u32)                    // from a global atomic counter
VecToken { …, container_id }        // every token records its origin Vec
```

`restore` asserts `token.container_id == self.id`, rejecting one vec's token on a
different vec. Modeled with a ghost unique id per Vec.

### 9.2 Fork history: the branch-cut theorem

```
VecToken { branch_id: u32, depth: u32, frame_index: u32, container_id }
ForkHistory {
    current_branch_id: u32,
    origins: Vec<ForkOrigin { parent_branch_id: u32, fork_depth: u32 }>,
}
```

- **`mark()`** stamps `branch_id = forks.current_branch()` and
  `depth = frames.len()` (the depth before the push: a token's `depth` equals its
  own frame index).
- **`restore(token)`** rolls back to `token.frame_index`, then `forks.fork(...)`
  starts a new branch: pushes
  `ForkOrigin { parent_branch_id = token.branch_id, fork_depth = token.depth }`
  and sets `current_branch_id = origins.len()` (a fresh, never-reused id).
- **`is_valid(token, current_depth)`** walks from the current branch up its chain
  of parents; a token is valid iff its branch lies on that ancestor path **and**
  its depth is within the part of that branch not cut off by a later fork.

#### Branch tree: 2D picture

Each `restore` snips the current timeline at some depth and grows a new branch.
`origins[b-1]` is branch `b`'s parent edge, labelled with the `fork_depth`.

```
 depth
   3            t_old ✗            ← token at depth 3 on branch 0
   2        ┌───┘                    (cut: branch 1 forked from branch 0 at depth 1)
   1     ●──┴───────●  fork_depth=1
   0  ───┴───branch0─┴───branch1(current)───
          branch 0           branch 1

 is_valid, current = branch 1:
   token{branch=1, depth≤current}      → valid   (same branch, in range)
   token{branch=0, depth≤fork_depth=1} → valid   (ancestor, at/below the cut)
   token{branch=0, depth=3 > 1}        → INVALID  (abandoned future, above the cut)
```

After `restore` cuts branch 0 at depth 1, any branch-0 token deeper than 1 (a
snapshot from the discarded future) is rejected; branch-0 tokens at depth ≤ 1
(genuine ancestors) stay valid. That is **branch-cut safety**.

`lemma_fork_valid_characterization` proves `is_valid(token)` equals exactly "its
branch is the current branch or an ancestor, and its depth is within that
branch's live prefix." This is what connects validity back to reconstruction: a
*valid* token's `frame_index` still denotes the same logical snapshot it did at
mark time, so `view() == snapshots[token.frame_idx]` composes with validity to
give "restore with a valid token reproduces the snapshot it was minted for," even
across intervening restores and re-marks. The walk terminates because it descends
strictly toward the root (`parent_branch_id < branch` by `fh_wf`); termination
plus the path characterization are the two core lemmas, in `fork_history.rs`.

---

## 10. Why these proofs: arenas, integers-as-pointers, and explicit aliasing

The containers built on the vector, the sparse set, the linked-list arena, the
circular class lists, the B+tree, are where the real reason to verify shows up.

Every one is **arena-allocated**: its objects live in a backing vector and are
named by **integer index**, not by a Rust reference. Those indices *are* the
pointers: a list node holds its successor's index, a class ring is a cycle of
`next` indices, a sparse set's three vectors point at each other by position.
This is a performance choice (one contiguous allocation, `Copy` ids on the hot
path, no per-object heap traffic, trivial semi-persistent snapshotting), but it
has a sharp consequence: **integers-as-pointers bypasses Rust's ownership and
borrow checking entirely.** Two fields may hold the same index, the structures
are freely *aliased*, and an index may point back into a structure that points
at it, so the arenas hold genuinely **cyclic** object graphs, which `&mut` forbids.
Going through indices sidesteps that, and gives up all compiler help for the
discipline that keeps the structure well-formed. **Verus is the only guarantee
left.**

The proof style is **explicit dynamic frames**, transposed from heap references to
arena indices. Each structure carries a **ghost field** describing its footprint
as *unique integer ids*: the node ids on a list, the id-set a sparse set
represents, the ids in each class ring. Well-formedness is stated over those ids:
structural shape (the exec `head`/`next`/`tail` pointers trace exactly the ghost
sequence), **aliasing** (which ids may coincide), and **separation** (which id
sets must be disjoint: a sparse set's live region and free pool partition
`[0, cap)`; distinct lists own disjoint nodes; the class rings partition the
arena). The only constraint on an individual index is that it is **in range**,
deliberately no "points at a smaller index" ordering, which would be a false
invariant unable to express `append` (linking an old node forward to a fresh
larger index) or `splice`; the structural facts come from the ghost model.
Operations *frame* their effect: they specify exactly which ids may change and
prove every id outside that frame is untouched.

The payoff is the guarantees the borrow checker can no longer give, as theorems:
the list arena's `prepend`/`append`/`splice` each refine the obvious sequence
operation while preserving disjointness of all other lists; the circular class
list's O(1) `splice`-by-pointer-swap merges two rings into one whose node set is
their union, unconditionally; the sparse set is a genuine bijection between its
dense and sparse halves. [Chapter 9](09-arena-aliasing-dynamic-frames.md)
develops the dynamic-frames connection and the frame/anti-frame mechanics in full;
the B+tree, the one recursive case, is [Chapter 10](10-bplus-tree.md).

## 11. What is verified

Everything below is proved with no `admit`s or `assume`s, at arbitrary
mark-nesting depth. Run `./verify-all.sh` for the live per-module count. For the
dual, what is taken on trust (the 7 `external_body` items), see
[Chapter 2](02-trust-boundary.md).

**The vector.** Reconstruction, diff-log faithfulness (coverage + uniqueness), the
runtime↔ghost capture bridge, and token validity (branch-cut safety) hold for the
full API: `push`, `set`, `get`, `mark`, `restore`, and `pop` into a marked region.
Both backends (`InlineStore`, `ParallelStore`) satisfy the `DiffStore` contract;
the bit-stealing layer is exercised by `DenseId31` (both `IndexLike` and `Tagged`
on one `u32`, niche-injectivity discharged by the bit-vector solver), and
`ParallelStore`'s flags use the packed `CaptureBits`. The `TRACK=false` guarantee
(an unmarked vector is observably a plain `std::Vec`) and full production API
parity hold. The verification also **found and fixed a real production bug**: a
silent `u32` truncation in `Frame.saved_len`.

**The container family.** All verified: `AppendOnlyVec`, `Map`, `SparseSet`
(refined to a ghost set + index pool), `ListArena` (chain semantics + acyclicity,
incl. `append`/`splice`), `CircularList` (O(1) ring merge), and `BPlusTreeSet`
(insert with split propagation: total; sound in-order traversal and seek; the
arena provably never overflows; `mark`/`restore`; insert-only,
[Chapter 10](10-bplus-tree.md)).

**Deliberate divergences** (documented, not gaps): `T: Copy + Default` instead of
`T: Clone` (`Copy ⊂ Clone` suffices for the e-graph domain; `Default` enables the
DoS-free bounded-capture pop, [Chapter 6](06-restore-regrow-alternatives.md));
`as_slice` omitted (a backend-specific fast path outside the persistence
contract). The full method-by-method coverage vs. production is the
[parity audit](../future/parity-audit-and-plan.md).
