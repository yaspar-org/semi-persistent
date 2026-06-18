# Chapter 2 — Semi-Persistent Vectors

[← Ch 1: Dense IDs and Tagged](01-dense-ids-and-tagged.md) · [Table of Contents](00-table-of-contents.md) · [Ch 3: AppendOnlyVec →](03-append-only-vec.md)


## High-Level Idea

Many search algorithms need backtracking: explore a branch, then undo
everything and try a different branch. E-graph equality saturation,
SAT solving, constraint propagation, and game-tree search all share
this pattern. Backtracking requires snapshotting the entire mutable
state and restoring it later.

A naive clone-on-snapshot is O(n) in both time and memory per mark —
and with many nested snapshots the memory is what hurts. The
semi-persistent vector takes a different approach: it records negative
diffs into a stack. On `mark()`, the vector stores its current length
and starts logging negative diffs in a frame of its private diff
stack. On each mutation, before overwriting a slot, it pushes the old
value into the negative diff stack. On `restore()`, it replays the log
in reverse to restore captured values, then truncates back to the
saved length.

The decisive win is **memory**: a snapshot costs only the cells that
subsequently change (the sparse diff), never a full copy, so deeply
nested marks stay cheap. `restore()` is O(k), where k is the number of
mutations since `mark()`. `mark()` is *not* unconditionally O(1) in
time — it must reset the per-slot capture flags for the new frame — but
it is always sublinear in that work, never a copy: `InlineStore` clears
only the flags the parent frame actually captured (O(k)), and
`ParallelStore` zeroes a packed `u64` capture bitfield (O(n/64)). Make
the capture bitfield small relative to the data and `mark()` approaches
O(1); regardless, the memory footprint is the real, design-defining
advantage.

The tricky part is the first-write-wins protocol: each slot of the Vec
must be logged at most once per frame (logging the same slot twice wastes
space and the second log entry is useless because only the original value
matters). This requires a per-slot "already captured" flag, which is
exactly the tag bit from Chapter 1. For `DenseId` types stored in
`InlineStore`, the capture flag is the MSB, costing zero extra memory.

### Token Safety

A `mark()` returns an opaque `VecToken`. The caller hands this token
back to `restore()` to undo. But tokens can go stale: if you restore
past a mark and then mark again, you're on a new timeline, and old
tokens from the abandoned future must be rejected. The engine detects
this with two mechanisms:

- `ContainerId` is a globally unique id per `Vec` instance (from an
  atomic counter). Every token records which container it came from.
  `restore()` checks the token's container id matches, preventing
  cross-container bugs (e.g., using one container's token on a different
  container).

- `ForkHistory` is a field in each vector that tracks branch history
  defined by `mark()/restore()` invocations. Each token records a
  `branch_id` and `depth` within that branch. When you restore past
  a mark and re-mark, a new branch is created with a new `branch_id`,
  and the fork point is recorded. On `restore()`, the history is walked
  to verify the token belongs to the current branch or a direct ancestor;
  tokens from terminated sibling branches cause panics.

```rust
pub struct VecToken {
    branch_id: u32,
    depth: u32,
    frame_index: u32,
    container_id: ContainerId,
}
```

## Type Parameters

The vector is parameterized by two type-level concerns and one
compile-time flag:

```rust
pub struct Vec<T, I: IndexLike, S: DiffStore<T, I, TRACK>, const TRACK: bool>
```

`T` is the element type. When stored in an `InlineStore`, `T` must
implement `Tagged` so the capture bit can be packed into each slot's
representation. When stored in a `ParallelStore`, `T` only needs
`Clone` (the capture bits live in a separate `BitSet`).

`I: IndexLike` is the index type. It must admit a bijection to
`[0, N)` for some N determined by its bit width. Concretely,
`IndexLike` requires `to_usize` and `from_usize` conversions, plus
an associated `MAX` constant that bounds the addressable range. The
diff log stores `(I, T)` pairs, so a narrow index type (e.g., `u16`)
keeps diff entries compact.

`DiffStore<T, I, TRACK>` is the storage backend trait, parameterized
by both `T` and `I`. It defines the capture protocol (`capture`,
`prepare_mark`, `restore_entry`) and the raw data access (`get`,
`set_raw`, `push`, `truncate`). `InlineStore` and `ParallelStore`
are the two implementations.

The key unification: `DenseId` implements both `Tagged` and
`IndexLike`. A dense id can be stored in an `InlineStore` (using its
MSB as the capture flag) and simultaneously used as the index type
for a different vector. This is why a single
`VecI<MyId, MyId::Index, TRACK>` can serve as a parent-pointer array:
the elements are id values with zero-cost capture tracking, indexed
by the same id type.

Two convenience aliases capture the common cases:

```rust
type VecI<T: Tagged, I, TRACK> = Vec<T, I, InlineStore<T, I, TRACK>, TRACK>;
type VecP<T: Clone, I, TRACK>  = Vec<T, I, ParallelStore<T, I, TRACK>, TRACK>;
```

## API

| Operation | Cost | Description |
|-----------|------|-------------|
| `push(val)` | O(1) amortized | Append element (marks re-entered captured slots) |
| `pop()` | O(1) | Remove last element (captures it first-write-wins if below `saved_len`) |
| `get(i)` | O(1) | Read element at index |
| `view().set(i, val)` | O(1) | Write element (with capture) |
| `len()` | O(1) | Current length |
| `mark()` → `VecToken` | sublinear; O(parent diff) inline / O(n/64) parallel | Snapshot — clears per-slot capture flags, never copies. Memory cost is only the diff. |
| `restore(token)` | O(k + regrow) | Undo all mutations since mark (k = mutations). Requires `T: Default`. |

## The Diff-Log Protocol

### Mark

```
mark():
    push Frame { saved_len: current len, diff_start: diff_log.len() }
    store.prepare_mark(saved_len, &diff_log[prev_frame..])
```

On `InlineStore`, `prepare_mark` clears all tag bits in slots
`[0..saved_len]` so that subsequent mutations can be detected.

### Mutate

```
view().set(i, new_val):
    store.capture(i, saved_len, &mut diff_log)
    store.set_raw(i, new_val)
```

`capture` on `InlineStore`: if `i < saved_len` and tag bit is clear,
log `(old_value, i)` to diff_log and set the tag bit. If tag is
already set, the slot was already captured, so it skips. This ensures each
slot is logged at most once per frame.

`pop()` is a mutation too: if the popped slot sits below `saved_len`, it
goes through the **same first-write-wins `capture`** before removing the
element. It must *not* use an unconditional record — a `loop { pop(); push() }`
on a marked index would otherwise log an entry per iteration and grow the
diff log without bound (a memory-exhaustion DoS). With conditional capture
the log holds at most one entry per index per frame, so it is bounded by
`saved_len`.

`push(val)` appends to the store. New elements above `saved_len` need no
capture — truncation on restore removes them. But when `push` *re-enters* a
slot below `saved_len` that was popped after already being captured this
frame, it calls `store.mark_captured(i)` to keep that slot's capture bit set.
Without this, a later `set` on the re-entered slot would log a second entry
for it, defeating first-write-wins and re-opening the unbounded-log hole.

### Restore

```
restore(token):                       // requires T: Default
    frame = frames[token.frame_idx]
    store.resize_default(frame.saved_len)   // regrow popped region first
    for (old_val, idx) in diff_log[frame.diff_start..].rev():
        store.restore_entry(idx, &old_val, frame.saved_len)
    store.finish_restore(&diff_log[frame.diff_start..], frame.saved_len)
    diff_log.truncate(frame.diff_start)
    frames.truncate(token.frame_idx)
```

`restore` first resizes the store back to exactly `saved_len`: it truncates
any elements pushed above the mark *and* regrows any region that was popped
below it, filling the grown slots with `T::default()`. It then replays the
diff log in reverse, overwriting each modified slot with its marked value.

Regrowing *before* the replay is what makes the replay a pure overwrite.
Because `pop` now captures conditionally (first-write-wins) rather than
logging every popped cell, the log no longer contains an entry for every
slot in the popped region — so the old "regrow by pushing during replay"
scheme would leave gaps. `resize_default` restores contiguity up front; the
replay then overwrites every regrown cell with its captured value.

**Why the fillers are safe.** The `T::default()` fillers `resize_default`
writes are provably never observed: every regrown cell is below `saved_len`
and was captured this frame, so the backward replay overwrites it with its
diff value. The filler therefore may be any in-domain value — which is why
`restore` only requires `T: Default`, and why a degenerate default (an
all-zero node, an empty list head) is fine. For bit-stealing `Tagged` types
the filler is routed through `into_repr`, which re-clears the stolen niche
bit, so a `Default` impl introduces no new niche obligation. This is the one
reason `restore` carries a `T: Default` bound; every other operation does
not.

## Nested Marks

Marks can be nested. Each `mark()` pushes a new `Frame`. `restore()`
pops back to the specified frame, undoing all intermediate frames.

```
mark()  → token_A (saved_len=10)
  push, push, set(3, x)     // diff_log: [(old_3, 3)]
  mark()  → token_B (saved_len=12)
    set(5, y)                // diff_log: [(old_3, 3), (old_5, 5)]
  restore(token_B)           // undo set(5,y), truncate to 12
restore(token_A)             // undo set(3,x), truncate to 10
```

## `InlineStore` — Zero-Overhead Tracking

```rust
pub struct InlineStore<T: Tagged, I: IndexLike, const TRACK: bool> {
    data: std::vec::Vec<T::Repr>,
}
```

The tag bit lives inside each `T::Repr`. For `DenseId` types, this is
the MSB of the `u32`, costing zero extra memory.

| Operation | Tag behavior |
|-----------|-------------|
| `push(val)` | Store `val.into_repr()` (tag=0) |
| `set_raw(i, val)` | Overwrite repr at `i` |
| `capture(i, ..)` | If `!tag(data[i])`: log old value, `set_tag(data[i])` |
| `mark_captured(i)` | `set_tag(data[i])` (mark re-entered slot captured, no log) |
| `prepare_mark(..)` | Clear all tags in `[0..saved_len]` |
| `restore_entry(i, old)` | `data[i] = old.into_repr()` |
| `resize_default(len)` | Truncate or regrow to `len`, filling with `T::default().into_repr()` |
| `get(i)` | `T::from_repr(&data[i])` (strips tag) |

## `ParallelStore` — For Non-Taggable Types

```rust
pub struct ParallelStore<T: Clone, I: IndexLike, const TRACK: bool> {
    data: std::vec::Vec<T>,
    bits: BitSet,
}
```

Same protocol, but the capture flag is a separate bit in `BitSet`.
Used for types like `(MyId, u32)` that don't implement `Tagged`.

## `View` — Mutable Accessor

`View` wraps `&mut Vec` and provides `get`/`set` with automatic
capture tracking, preventing accidental calls to `set_raw` without
capture:

## Token Validation

See "Token Safety" above for the full design. In summary:

- `ContainerId` prevents cross-container token use.
- `ForkHistory` prevents stale-branch token use.
- Both checks happen at the start of `restore()` and panic on
  violation; these are always programmer errors, never recoverable.

## `ShrinkPolicy` — Capacity Reclamation

Rust's `Vec::truncate` reduces `len` but preserves `capacity`. After
restoring from a large exploratory branch, the store's internal
arrays may have far more capacity than needed. Capacity ratchets
across branches, converging to the maximum branch size ever explored.

The original design principle: shrinking happens at mark time (before
the frame push), not at restore time. The rationale is that never
shrinking during restore avoids costly reallocations in tight
exploratory loops; the vec naturally "learns" the right capacity.
Shrinking is part of the maintenance phase inside `mark()`, alongside
resize and compaction — semantics-preserving transformations
that are not captured in the diff frames.

```rust
pub enum ShrinkPolicy {
    Never,
    IfOverallocated { factor: usize, headroom: usize },
}
```

With `IfOverallocated { factor, headroom }`, if
`capacity > factor * len`, the backing storage shrinks to
`headroom * len`. The same check is applied to the diff log.

`Never` is best for tight search loops with similar-sized branches.
`IfOverallocated` is for top-level marks after major search resets
where the previous branch was much larger than the next one will be.

All `mark()` methods across the container hierarchy accept a
`ShrinkPolicy`. All `restore()` methods take no policy — they just
undo. Applications typically store the policy as a configurable field
and propagate it through their top-level `mark()` to all
sub-containers.

---
[← Ch 1: Dense IDs and Tagged](01-dense-ids-and-tagged.md) · [Table of Contents](00-table-of-contents.md) · [Ch 3: AppendOnlyVec →](03-append-only-vec.md)
