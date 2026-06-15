# A Verified Library of Semi-Persistent Containers

*Master design document for `containers-verus` — the Verus port of the
production [`semi-persistent-containers`](../../../containers) crate.*

[Table of Contents](00-table-of-contents.md)

## Abstract

This crate verifies one data structure in depth and then puts it to a second
use. **Act one**: a *semi-persistent vector* — cheap snapshots (`mark`) and
rollback (`restore`) whose cost is proportional to the mutations since the
snapshot, never to the whole state. The decisive saving is *memory*: it never
stores its snapshots, recording only a *sparse negative diff* (the old value of
each cell, captured the first time the cell changes within a marked region) and
reconstructing a snapshot by replaying that diff in reverse. Our central result
is that this reconstruction is *exact* — we model the intended states as full
snapshots in ghost code and prove each is recovered from the sparse diff, at
arbitrary nesting depth and after any interleaving of pushes, sets, and pops —
and that the discipline governing *which* snapshots may be restored is sound: a
`mark` opens a branch in a fork history, a `restore` cuts the branches it
discards, and any attempt to restore a discarded snapshot is rejected.

**Act two**: that verified vector is, in its second role, a *backtrackable arena
allocator*, and inside it we build and prove correct a family of further
containers — an append-only vector, a hash map, a sparse set (a bijection
refining to a ghost set plus an index pool), an intrusive linked-list arena
(`prepend`/`append`/`splice`), and a circular class-list (O(1) ring merge by
pointer swap). Several are internally **aliased** and even **cyclic**: they
connect their nodes by integer index into the arena rather than by a Rust
reference, which is the only way to express them — `&mut`'s uniqueness rule
forbids exactly that aliasing and cyclicity — and which deliberately bypasses
Rust's ownership and borrow checking, leaving **Verus as the sole
well-formedness guarantee**. We discharge it in an explicit **dynamic-frames**
style: a ghost field names each structure as sets of unique arena ids, and
aliasing, separation, and shape are proved as explicit predicates over those ids
(§10, [Chapter 9](09-arena-aliasing-dynamic-frames.md)). The whole development
carries no `admit`s or `assume`s; run `./verify-all.sh` from the package root
for the current per-module tally.

## 1. Introduction

This document has two halves, and it is worth stating the arc before the
machinery, because the second half is the *reason* for the first. We verify a
single semi-persistent vector — a vector with cheap, nestable snapshot/rollback
— and prove its reconstruction exact and its backtracking discipline sound.
Then we change how we *think* about that vector: a semi-persistent vector of
cells is, equivalently, a **backtrackable arena allocator** — a pool of
integer-indexed slots in which whole data structures can be built, and which can
be snapshotted and rolled back wholesale for free, because the underlying vector
already can be. On top of it we implement a family of containers — an
append-only vector, a hash map, a sparse set, an intrusive linked-list arena, a
circular class-list — several of which are internally *aliased* and *cyclic*,
since they wire their nodes together by arena index rather than by Rust
reference. Those structures are where the non-trivial well-formedness lives, and
where the compiler stops helping; the second half of this document (§10 and
[Chapter 9](09-arena-aliasing-dynamic-frames.md)) is how we verify them. The
first half — the rest of this introduction and §2–§9 — earns the foundation
that makes the second possible.

Backtracking search — equality saturation, SAT, constraint propagation,
game-tree exploration — repeatedly snapshots a mutable state, explores forward,
and rolls back. Doing this by cloning the whole state at each snapshot costs
O(n) time *and* O(n) memory per snapshot, and with many nested snapshots the
memory dominates. A *semi-persistent* structure removes the memory blow-up: a
snapshot stores only the cells that subsequently change, so its footprint is
the size of the diff rather than the size of the state, and rollback runs in
proportion to that diff. (Snapshotting is not unconditionally O(1) in time —
`mark` resets per-cell capture state, which is sublinear with a packed
capture bitfield and O(diff-size) for the inline backend, but never a full
copy; see §3. The robust, design-defining win is the memory.) The price of
the asymmetry is that the structure must reconstruct old states on demand, and
the reconstruction logic is exactly where a subtle off-by-one or a dropped
update silently corrupts the search. That is what makes the structure worth
verifying, and it is the foundation we verify first because so much is built
on it.

The mechanism is a *diff log*. Mutating a cell for the first time since the
last mark records the cell's old value as a negative diff `(old, index)`;
subsequent writes to the same cell in the same mark add nothing. To restore,
the structure truncates the log back to the mark and replays the recorded
values in reverse, undoing each first-write and so returning every touched cell
to what it held at mark time. Untouched cells were never logged because they
never changed. The log is therefore *sparse* (only first-writes) and *negative*
(it stores what to undo, not the current state), and a snapshot is never
materialized — it lives only implicitly in "current contents, minus the diffs."

The proof's task is to show that this implicit representation is faithful. We
give the vector a ghost field `snapshots`: a stack of full sequences, where
`snapshots[k]` is the entire contents at the instant frame `k` was marked.
These full snapshots exist only in the proof — they are the *specification* of
what each mark ought to preserve, deliberately redundant with the sparse diff
that the running code actually keeps. The headline theorem is that the two
agree on rollback:

> After `restore(token)`, `view() == snapshots[token.frame_idx]`.

Here `view(): Seq<T>` is the user-visible contents and `snapshots[k]` is the
ghost full copy at mark time. Because `snapshots` is ghost, the theorem says
something strong: the data structure can *recompute* a full snapshot from the
sparse negative diff, exactly, for every cell. Proving it for one mark is
routine; the difficulty is that marks nest arbitrarily and mutations interleave
freely — a cell may be untouched under one mark, overwritten under a deeper
one, popped out of the live region under a third — and the reconstruction must
still land each cell's value from precisely the right mark. We discharge this
by partitioning the diff log into per-frame *strata* and proving a single
declarative per-cell invariant (§6): each marked cell's snapshot value lives in
exactly one place — in the live contents if untouched, or in the diff log if
overwritten or popped — with no third possibility. Replaying the strata in the
right order overlays those values back, reconstructing the snapshot (§7–8).

A second concern is which snapshots a caller is even allowed to restore. A
token names a frame, but rolling back and marking again reuses frame indices,
so a token left over from a discarded line of exploration could name a frame
that no longer means what the token's holder thinks. Restoring it would silently
jump to an unrelated state. We make the discipline explicit and prove it sound:
the structure maintains a *fork history* in which each `mark` opens a branch and
each `restore` records a cut that abandons the branches above the restore point.
A token is valid exactly when its branch still lies on the current path of this
history and its depth falls within that branch's un-cut prefix; we prove that
`restore`'s validity check accepts precisely those tokens and rejects every
token naming a discarded snapshot (§9). With this, the reconstruction guarantee
composes across backtracking: a *valid* token always reproduces the snapshot it
was minted for, even across intervening restores and re-marks.

One more result closes out act one: when no mark is live the vector must impose
no cost, and we prove it reduces observably to a plain `std::Vec` with an empty
diff log (the `TRACK = false` story, §7) — so the unmarked allocator is exactly
an ordinary arena, and snapshotting is genuinely pay-as-you-go.

That completes the foundation. The vector's ghost-model / sparse-representation /
reconstruction template then *recurs* in the act-two containers — but with a
twist that is the real subject of the second half: because those containers are
index-addressed, they are freely aliased and cyclic, so their well-formedness
(and the separation between the structures sharing an arena) has to be specified
and proved explicitly, in the dynamic-frames style of §10 and
[Chapter 9](09-arena-aliasing-dynamic-frames.md). The summary of exactly what is
verified, across both acts, is §11.

The rest of this document is the machinery behind these results: the layered
module architecture (§2), the bit-stealing storage abstraction and its two
backends (§3–4), the vector's memory layout (§5), the well-formedness invariant
that carries the per-cell discipline and the runtime/ghost agreement (§6), the
operation-by-operation maintenance proofs including the subtle case of popping
into a marked region (§7–8), the fork-history soundness argument (§9), why the
arena-allocated container family needs verifying at all and how its aliasing and
separation are specified (§10), and a summary of what is verified (§11).

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
storage. Two backends satisfy that contract — and §3–4 are about *where each
puts the one capture bit per cell*, the choice that the rest of the proof is
deliberately blind to.

---

## 3. The capture bit, and where to keep it

### One bit per cell

The diff log of §1 turns on a single question, asked of a cell on every
mutation: *has this cell already been captured since the last mark?* If it has,
the mutation is a re-write — the log already holds the cell's mark-time value,
so nothing is recorded. If it has not, this is the first write since the mark,
and the old value must be logged before it is lost. First-write-wins, and with
it the entire memory argument, rests on answering that question correctly for
every cell.

The answer is one bit of state per cell — *captured* or not. The vector holds
`view.len()` such bits; `mark` clears them, the first write to a cell sets its
bit, and every mutation reads one. *Where those bits live* is the subject of
this section. The reconstruction theorem never mentions them, so the choice is
invisible to correctness — but it decides the structure's memory footprint and
the cache cost of a mutation, the two things a semi-persistent vector is built
to economize. We therefore hide the choice behind a trait, prove the vector
once against the abstraction (§4–8), and supply two concrete backends.

### `Tagged`: carving the bit out of the value

The cache-friendly place to keep a cell's capture bit is *inside the cell*. A
vector of pool-allocated identifiers — e-node ids, class ids — never uses the
full width of its storage word: a 32-bit id addresses two billion entries in 31
bits and leaves the top bit idle. Spending that idle bit on the capture flag
costs no memory, and it keeps the flag on the same cache line as the value it
describes, so a mutation touches one word rather than chasing a second
allocation. The distinction the design turns on is between a word's *storage*
width and its *used* width: a `DenseId31` stores 32 bits but uses only the low
31 for its value, reserving the 32nd as a control bit.

Carving a control bit out of a value's word is precisely the bit-twiddling that
silently corrupts data when a mask is wrong, so the `Tagged` trait makes the
carving a contract and its soundness a proof obligation. A `Tagged` type names
a representation `Repr` (the stored word) and three ghost projections of it:
`value_of(r)`, the clean value carried in `r` with the control bit masked away;
`tag_of(r)`, the control bit; and `repr_wf(r)`, the *niche predicate* — which
reprs are in the image of the encoding. The exec surface is the five obvious
operations, `into_repr`/`from_repr`/`tag`/`set_tag`/`clear_tag`, each contracted
against those projections. Two obligations make the encoding sound, and they
are exactly the ones a wrong mask would break:

- **Tag edits do not disturb the value.** `set_tag` and `clear_tag` preserve
  `value_of` (and `repr_wf`). This is what lets the vector flip a cell's capture
  flag at will: `data()` is `value_of` read across the cells, and `value_of` is
  invariant under tag edits, so `view()` is invariant under capture-flag edits.
  Without this, marking a cell could change the cell.

- **The encoding is injective — the niche axiom.** `lemma_repr_extensional`:
  two well-formed reprs with equal `value_of` and equal `tag_of` are equal.
  This certifies that the stolen bit is genuinely free: the value and the tag
  together pin down the whole word, so the bit wastes no state space and
  `from_repr` inverts `into_repr`.

A type that has no bit to spare uses the fallback `BoolPair<T>`, which stores
the tag in a separate `bool` field beside the value. It steals nothing, so
`repr_wf` is `true` everywhere and the niche axiom is vacuous — it pays a word
of padding to remain usable. The impl that makes the obligations *bite* is
`DenseId31`, below.

### `DiffStore`: the protocol that consults the bit

The vector never touches a `Tagged` repr or a capture bit directly. It speaks
to a storage backend through the `DiffStore` trait, which owns the data
sequence and the capture flags together and exposes them as two ghost views,
`data(): Seq<T>` and `captured(): Seq<bool>`, tied by `wf()` to equal length.
`DiffStore` is the capture *protocol* — `prepare_mark` clears the flags for a
new frame, `capture` performs the first-write-wins test-and-log, `restore_entry`
replays one diff, and so on. Its full contract is §4. What matters here is that
`DiffStore` is the seam: the vector's proof depends only on this trait, so the
two ways of storing the capture bit are two implementations of it, and neither
is visible to the reconstruction theorem.

### `IndexLike` and `DenseId31`: the bit packed inline

`InlineStore<T: Tagged>` is the zero-overhead backend. It stores a single
`Vec<T::Repr>`: each cell *is* a tagged word, its capture bit living in the
word's stolen niche. `data()` is `value_of` mapped across the reprs and
`captured()` is `tag_of` mapped across them — so the two ghost views are read
out of the same physical vector, and `wf()` additionally asks that every stored
repr be `repr_wf`. The capture protocol becomes pure bit manipulation:
`set_tag` on a cell to mark it captured, `clear_tag` across a prefix in
`prepare_mark`, all leaving `value_of` — hence `data()` — untouched by the
tag-edit obligation above.

`DenseId31` (in `dense_id.rs`) is the concrete identifier that makes this real,
and it ties the two trait layers together: it is *both* `Tagged` (so it can be
stored with the flag packed inline) and `IndexLike` (so it can index a vector),
one type filling both roles exactly as production's `define_id31!` ids do. It
is a `u32` whose top bit is reserved: a type invariant pins a *clean* id below
`2^31`, and its `Repr` is the bare `u32` with the MSB carrying the tag.
`value_of` masks the low 31 bits, `tag_of` tests the MSB, `set_tag` ORs it in
and `clear_tag` ANDs it out. On the `Tagged` side the niche axiom is no
formality but a genuine theorem about 32-bit words — *if two words agree on
their low 31 bits and on their MSB then they are equal* — discharged by Verus's
bit-vector solver, which also checks that masking preserves the value and that a
clean id round-trips through `into_repr`; all proved against a real stolen bit
rather than the fallback's vacuous `repr_wf := true`. On the `IndexLike` side
`as_nat` is the identity on the clean value, so injectivity is immediate, and
the `[0, 2^31)` bound — which primitive index types get structurally — comes
from the type invariant.

That last point is where `IndexLike` earns a small design choice. Its bound
obligation, `lemma_as_nat_bounded`, must hold for *every* value of the type,
and a `u32`-backed id has 2³² bit patterns of which only the clean half are
legal — so the proof has to *consult* the `2^31` type invariant. A Verus type
invariant is readable only through `use_type_invariant`, which needs a tracked
or exec receiver, so the obligation is declared `lemma_as_nat_bounded(tracked
self)`. Primitive impls, whose bound is structural, ignore the receiver and
keep an empty body; `DenseId31` uses it to pull `raw < 2^31` into the proof.
That single receiver-mode choice is what lets one `u32`-backed type carry both
a tight `2^31` index bound and an inline niche, instead of splitting the index
and value roles across two types. The end-to-end witness
`lemma_dense_id31_indexes_and_stores_itself` (in `dense_id.rs`) discharges
`InlineStore<DenseId31, DenseId31>`'s well-formedness — the same id type
indexing the store and stored in it, capture bit packed inline.

### `ParallelStore` and `CaptureBits`: the packed-bitset fallback

When the stored type has no spare bit, the capture flags move out of the value
and into a side structure. `ParallelStore<T: Copy>` holds the data in a plain
`Vec<T>` and the flags in a parallel bit-vector, so `set_raw` writes only the
data while the capture protocol writes only the flags; `wf()` keeps the two the
same length. This is the general backend — it asks nothing of `T` beyond `Copy`
— and the cost is one bit per cell plus the cache jump from a value to its flag
in a separate allocation, which is exactly what `InlineStore` avoids and why
the inline layout is preferred for id-typed vectors.

The flags themselves use the same packed representation as production:
`CaptureBits` (in `capture_bits.rs`) is a `Vec<u64>` carrying one bit per cell —
bit `i` in word `i / 64` at position `i % 64` — under a ghost `Seq<bool>` view.
A naive `Vec<bool>` would spend a whole byte per flag; the packed form is eight
times denser. Each operation (`get`, `set`, `push`, `pop`, `truncate`) is
proved to refine the corresponding operation on the ghost sequence, the
per-bit reasoning again discharged by the bit-vector solver — the delicate case
being `set`, which must leave every *other* bit's view value unchanged. Because
`CaptureBits` *is* a `Seq<bool>` through its view, `ParallelStore`'s
`captured()` spec and every proof over it are exactly what a `Vec<bool>` backing
would give: the packing is verified in isolation and is invisible above.

Both backends discharge `lemma_wf_captured_len` (the views stay equal length)
and the value-invariance of capture-bit edits, so the vector cannot tell them
apart.

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
- `mark_captured(i)` / `resize_default(len)` — added for pop into the marked region (§8):
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
   saved_len-monotone clause are the two that pop into the marked region must relax — see
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
the uncaptured case: `j ≥ above.len() ⟹ captured`. I.e. *every cell that has
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

| col | captured? | where `snap[j]` lives                       | case        |
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
- `j ≠ i`: view[j] and captured-status unchanged ⇒ both cases inherited.
- `j == i`: now captured. If `capture` appended, the new entry holds
  `old_view[i]`, which equals `snap[i]` *because* i was uncaptured ⇒ the old
  uncaptured case gave `view[i] == snap[i]`. If i was already captured, the
  existing entry still holds `snap[i]`.
  The **bridge** is what tells the proof whether i was already captured
  (`store.captured()[i]`), matching `capture`'s first-write-wins branch.
Uniqueness preserved: i was absent from the stratum iff we append.

**`pop()`** (transient-only, current) — `store.pop()`. Precondition
`active_saved_len < view.len()`: only pop a cell *above* every frame's marked
region, so no frame_inv cell is affected and no capture is needed. Bridge:
pop drops the last captured flag (index ≥ active), leaving `[0, active)`
unchanged. (Pop into the marked region lifts this — §8.)

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

## 8. Pop into a marked region — the hard part, and how it was proved

Production allows **popping into the marked region** (popping a cell with
`index < saved_len`). On restore, that pop "becomes a push": the regrown slot
needs a real `T`. Three ways to supply it (see `05-restore-regrow-alternatives.md`):

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

### What pop-into-the-marked-region requires (the invariant relaxations)

1. **Drop `wf` clause "frames[top].saved_len <= view.len()"** (clause 5):
   after popping into the marked region the view is *shorter* than saved_len.
   `frame_cell_inv`'s coverage case already handles the popped cells. The
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
   *captured* case (frame k's own diff) instead of the layer. No new clause
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
   needs. Pop into the marked region must extend it to the three-way form
   `idx >= saved_len` skip / `idx < prev.len()` overwrite / `idx == prev.len()`
   push (regrow), adding the `saved_len` (= target) parameter so over-range
   entries vanish. (A three-way `overlay` was prototyped in a reverted draft;
   it is *not* in the committed code.)

4. **`push` must `mark_captured`** a cell re-entering the marked region (after
   pop then push, `old_len < active_saved_len`): the pop already captured
   `snap[i]`, so the fresh slot inherits the captured flag. Without this, a
   later `set` re-captures and the log grows unbounded (defeats first-write-wins
   *and* the bound). This is what keeps the marked-region pop's log ≤ saved_len.

### Coverage — the one lemma, and its lifecycle

With conditional capture (no force-record), we are back to **at most one diff
per cell per stratum** (uniqueness). The *only* new obligation pop into the marked region
adds is **coverage**, which is just the contrapositive of `frame_cell_inv`'s
uncaptured case:

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
| **pop()** | *maintains*: removing cell `i` grows the gap to include `i`; `pop` calls `capture(i)` first, so `i` becomes captured (or already was) — holding `snap[i]` because the old uncaptured case gave `view[i]==snap[i]`. | *maintains*: **conditional** capture (not force-record) → still ≤ 1 entry for `i`. |
| **push(v)** | cell leaves the gap (present again); n/a. | *maintains*: if re-entering a marked index (`old_len < saved_len`), `mark_captured(old_len)` keeps the flag set so a later `set` won't append a 2nd entry. |
| **restore(t)** | *uses*: pad/chop to `saved_target`; the padded cells are exactly the gap, which coverage says are all captured ⇒ each padded default is overwritten by its diff (lowest-position-in-range wins = the target's value). | *uses*: lowest-position-in-`[diff_start_target,n)` entry per cell is unambiguous (≤1 per stratum), and it is the target's own (or a fallen-through deeper stratum's) value. |

This is the "either it's already snapshotted, or we record a diff" intuition,
formalized: `pop` is the only op that opens a gap, and it pays for each gapped
cell with a capture. See `04-flat-central-lemma.md` for the lemma that
turns coverage into the `view() == snapshots[target]` reconstruction.

### How pop-into-the-marked-region landed

The pieces, in the order they were built (each kept the tree green): the store
methods `mark_captured`/`resize_default`; the `frame_cell_inv` coverage
refactor and the `wf_for_snap` split; the **flat, target-clamped central
lemma** (§3 of `04-flat-central-lemma.md`) that reconstructs one cell at a
time and so needs no `saved_len` monotonicity; dropping the two now-false `wf`
clauses; the `restore` body (resize to the target's `saved_len`, then replay);
`push`'s `mark_captured` on re-entry; and `pop`'s conditional capture into the
marked region. The chronological account, including the reverted attempts, is
in [the proof attempts log](08-proof-attempts-log.md).

---

## 9. Fork history / branch-cut safety

> **Authoritative formal statement: [`02-fork-history.md`](02-fork-history.md) §0.6** —
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

## 10. Why these proofs: arenas, integers-as-pointers, and explicit aliasing

The vector's reconstruction theorem is delicate, but the containers built on it
— the sparse set, the linked-list arena, the circular class lists — are where
the *real* reason to verify shows up, and it is worth stating plainly because it
governs the whole design.

Every one of these structures is **arena-allocated**: its objects live in a
backing vector and are named by their **integer index**, not by a Rust
reference. Those indices *are* the pointers — a list node holds the index of its
successor, a use-list holds the indices of the e-nodes that reference a class, a
sparse set's three vectors point at each other by position. This is a
deliberate performance choice (one contiguous allocation, `Copy` ids on the hot
path, no per-object heap traffic, trivial semi-persistent snapshotting), but it
has a sharp consequence: **using integers as pointers bypasses Rust's ownership
and borrow checking entirely.** Two fields may hold the same index — the
structures are freely *internally aliased* — and an index may point back into a
structure that already points at it, so the arenas contain genuinely **cyclic**
object graphs (a circular class list is literally a cycle of `next` indices).
Rust's type system forbids exactly this aliasing and cyclicity for `&mut`
references; we sidestep it by going through indices, and in doing so we **give up
all compiler help** for the very discipline that keeps the structure
well-formed. There is no borrow checker watching that a freed slot is not still
referenced, that a list stays acyclic, that the sparse/dense cross-pointers
remain inverse. **Verus is the only guarantee left.**

The proof style is essentially **explicit dynamic frames**, transposed from heap
references to arena indices. Each structure carries a **ghost field** that
describes its mathematical footprint as *unique integer ids* within the arena —
the sequence of node ids on a list, the id-set a sparse set represents, the ids
in each class ring. Well-formedness is then stated over those ids: structural
shape (the executable `head`/`next`/`tail` pointers trace exactly the ghost
sequence; a class ring's `next` is the cyclic successor of its ghost ring),
**aliasing** (which ids may coincide), and **separation** (which id sets must be
disjoint — e.g. a sparse set's live region and its free pool partition
`[0, cap)`; distinct lists own disjoint node sets; the class rings partition the
node arena). Notably, the only constraint placed on an individual `next`/`head`
index is that it is **in range** — there is deliberately no "points at a smaller
index" ordering discipline; that would have been a false invariant, unable to
express `append` (which links an old node forward to a freshly-allocated larger
index) or `splice`, and the structural facts come instead from the ghost model.
Operations are contracted to *frame* their effect: they specify exactly which
ids' contents may change and prove every id outside that frame is untouched —
the index analogue of "modifies this footprint, nothing else." Aliasing and
separation that the Rust compiler would normally enforce structurally become
**explicit formal properties** discharged by the verifier.

The payoff is that we get back, as theorems, precisely the guarantees the
borrow checker can no longer give us — and more. The intrusive list arena's
`prepend`/`append`/`splice` are each proved to refine the obvious sequence
operation while **preserving disjointness** of all other lists (splice provably
concatenates two disjoint lists and empties the source); the circular class
list's O(1) `splice`-by-pointer-swap is proved to **merge two rings into one**
whose node set is their union, with the ring partition preserved — unconditionally,
no "the cycle eventually closes" side assumption; the sparse set is proved to be
a genuine **bijection** between its dense and sparse halves, refining to a ghost
set plus an index pool with the two provably partitioning the arena. None of
these come from Rust — they come from stating the id footprints and their
separation explicitly and proving the operations respect them. This is the
deeper sense in which the vector's correctness "underwrites" the rest (§1): not
only does mark/restore compose, but the *aliased, cyclic, index-addressed*
structures layered on top are sound exactly because their footprints and
separations are verified, where no other tool in the Rust stack was ever going
to check them. The method-layer companion [Chapter 9](09-arena-aliasing-dynamic-frames.md)
develops the dynamic-frames connection and the frame/anti-frame proof mechanics
in full.

## 11. What is verified

Everything below is proved with no `admit`s or `assume`s, at arbitrary
mark-nesting depth. Run `./verify-all.sh` for the live per-module count.

**The four core theorems of §0** — reconstruction, diff-log faithfulness
(coverage + uniqueness), the runtime↔ghost capture bridge, and token validity
(branch-cut safety) — hold for the full vector API: `push`, `set`, `get`,
`mark`, `restore`, and **`pop` into a marked region** (the
hard case). The branch-safety theorem is `lemma_fork_valid_characterization`,
wired into `Vec` via `VecToken { branch_id, depth, container_id }`, a `restore`
that requires `is_token_valid_spec`, and the `forks.fork(...)` cut.

Also verified: both storage backends (`InlineStore`, `ParallelStore`) satisfy
the `DiffStore` contract; the bit-stealing layer is exercised by a *real*
niche-packing identifier, `DenseId31`, which is *both* `IndexLike` and `Tagged`
on one `u32` (it indexes a vector and is stored in one, capture bit in the
stolen MSB; niche-injectivity discharged by the bit-vector solver, not left
vacuous as in the `BoolPair` fallback — and the witness
`InlineStore<DenseId31, DenseId31>` is proved well-formed), and
`ParallelStore`'s flags use a packed `CaptureBits` (`Vec<u64>`, one bit per
cell, proved to refine a ghost `Seq<bool>`); the
`TRACK=false` guarantee (an unmarked vector is observably a plain `std::Vec`
with zero tracking overhead); and full production API parity (`with_store`/
`new`, `depth`, `is_valid_token`, `VecView`/`VecViewIter`, `ShrinkPolicy` +
`mark`, byte-accounting).

The verification also **found and fixed a real production bug**: a silent
`u32` truncation in `Frame.saved_len` (corrected in both trees).

**Container family.** The same four-theorem template is reused for the
containers built on `Vec`: `AppendOnlyVec`, `Map`, `SparseSet` (refined to a
ghost set + index pool), and `ListArena` (chain semantics + acyclicity). See
their modules and the [table of contents](00-table-of-contents.md).

**Deliberate divergences from production** (documented, not gaps): `T: Copy +
Default` instead of `T: Clone` (`Copy ⊂ Clone` suffices for the e-graph
domain; `Default` enables the DoS-free bounded-capture pop — see
`05-restore-regrow-alternatives.md`); `as_slice` omitted (a backend-specific fast
path outside the persistence contract).

**Remaining work**: the generalized multi-size `BPlusTreeSet` (the largest
single target). (`ListArena` `append`/`splice` and the circular class list are
now verified — see §10 and [Chapter 9](09-arena-aliasing-dynamic-frames.md).)

### Verus tactics worth remembering
- When all `wf` sub-conjuncts verify under `--expand-errors` but the aggregate
  `self.wf()` fails: add `#[verifier::spinoff_prover]` + `#[verifier::rlimit]`
  — it's solver budget, not a soundness gap.
- Factor per-cell invariants into named spec fns for stable `forall` triggers.
- One milestone per commit; always leave the tree verifying; never commit a
  broken half-migration.
