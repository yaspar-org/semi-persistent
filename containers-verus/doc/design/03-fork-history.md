# Fork History / Branch-Cut Safety

Branch-cut safety is the second correctness property of the semi-persistent
containers (the first is the reconstruction theorem of Chapter 1). It governs
*which tokens `restore` will accept*: a token naming a state that has been
discarded by an intervening `restore` must be rejected. Fork history is the
data structure that decides this. It is orthogonal to the reconstruction
mechanism: it adds a precondition to `restore`, it does not change how `restore`
rebuilds the contents.

## 1. The data structure

A token carries four fields:

```
VecToken { branch_id: u32, depth: u32, frame_index: u32, container_id: ContainerId }
```

`mark` stamps `branch_id == forks.current_branch()`, and
`depth == frame_index == frames.len()`. `depth` and `frame_index` are numerically
equal at creation but feed two different parts of the contract (§5).

`ContainerId(u32)` is an unforgeable per-instance identity drawn from a
process-global atomic counter; `restore` asserts `token.container_id == self.id`
so a token from one container cannot be replayed into another.

Fork history itself is a forest stored as an append-only origin list:

```
ForkHistory { current_branch_id: u32, origins: Vec<ForkOrigin> }
ForkOrigin  { parent_branch_id: u32, fork_depth: u32 }
```

Branch `0` is the root. For `b >= 1`, `origins[b-1]` defines branch `b`'s parent
edge: `parent(b) := origins[b-1].parent_branch_id`, labeled with
`fork_depth(b) := origins[b-1].fork_depth`.

`mark` does not touch `forks`; it only reads `current_branch()` and the depth
into the token. A cut is recorded by `restore`, at its end, via `fork(p, d)`,
which performs exactly:

```
origins.push({ parent_branch_id: p, fork_depth: d });
current_branch_id := origins.len();   // the new branch id
```

So restoring branch `p` at depth `d` appends one origin entry and moves onto a
fresh child branch. The entry records the fact *branch `p` was restored at depth
`d` and a new branch diverged from it there*: along any path through the new
branch, `p` is retained only up to depth `d`.

## 2. Validity: the `is_valid` walk

```
is_valid(token, current_depth):
    if token.branch_id == current_branch_id { return token.depth <= current_depth }
    branch = current_branch_id
    while branch != token.branch_id {
        if branch == 0 { return false }
        origin = origins[branch - 1]
        if origin.parent_branch_id == token.branch_id {
            return token.depth <= origin.fork_depth
        }
        branch = origin.parent_branch_id
    }
    return token.depth <= current_depth
```

**Termination.** Each step sets `branch = origin.parent_branch_id`. The walk
terminates because `parent(b) < b` for every `b >= 1`: after a fork the new
branch id is `origins.len()` and its parent was a branch valid at the time,
hence strictly smaller. So the parent id strictly decreases toward `0`. This is
the well-formedness invariant `fh_wf` carried on `ForkHistory`; it gives the
spec walk its `decreases`.

## 3. The branch-safety theorem

Define the **current path** as the node sequence `current_branch_id`,
`parent(current_branch_id)`, `parent²(…)`, …, `0` (finite by `parent(b) < b`). A
branch `q` *is on the current path* iff it occurs in this sequence. For `q` on
the path, its **depth bound** is:

- `bound(q) := current_depth` if `q == current_branch_id` (the live frontier);
- `bound(q) := fork_depth(c)` if `q` is a strict ancestor, where `c` is `q`'s
  unique on-path child (the depth at which `q` was cut on the way to the current
  branch). The path is linear, so `c` is unique.

> **Theorem.** `is_valid(token, current_depth) = true` iff `token.branch_id` is
> on the current path and `token.depth <= bound(token.branch_id)`.

Contrapositive (when a token is rejected): a token is invalid iff either
(i) its branch is not on the current path (it lies in a subtree diverged away
from; the walk reaches branch `0`); or (ii) its branch is on the path but
`token.depth > bound(token.branch_id)` (it names a position past where that
branch was cut, or beyond the live frontier).

Note the asymmetry: a token on a *cut* branch `p` is not automatically invalid.
It is valid iff `token.depth <= fork_depth(c)` for `p`'s on-path child `c`. Cut
branches retain their at-or-below-the-cut tokens, which name genuine ancestors
of the current state.

## 4. Two layers and what is proved

- **Exec `ForkHistory`** is a faithful port of production:
  `current_branch_id: u32`, `origins: Vec<ForkOrigin>`, with the production
  bodies for `new`/`current_branch`/`fork`/`is_valid`. Ids and depths are
  concrete `u32` (§5), no ghost-`nat` projection.
- **Spec `fork_valid`** is a pure recursive `spec fn` over `(origins,
  current_branch, current_depth, token_branch, token_depth)` defining the walk
  declaratively, `decreases branch` (kept total with an explicit `parent >=
  branch` guard that `fh_wf` makes unreachable).

Proved in `fork_history.rs`:

1. **Refinement.** The exec `is_valid` while-loop computes exactly
   `fork_valid(...)`.
2. **Branch-safety theorem (§3).** `lemma_fork_valid_characterization` proves
   `fork_valid == reaches(current, tb) && td <= walk_bound(current, cd, tb)`
   for all cases (current branch, strict ancestors at any depth, off-path
   rejection), by induction on `branch` under `fh_wf` (which discharges the
   `parent >= branch` dead guards so the three recursions align). `reaches` and
   `walk_bound` are the spec fns realizing "on the current path" and "the
   branch's depth bound". `lemma_branch_cut` and
   `lemma_fork_valid_current_branch` remain as convenient specializations.
3. **`fh_wf` maintenance.** `new` establishes it; `fork` maintains it.

Wiring into `Vec`: `forks: ForkHistory` and `id: ContainerId` fields;
`VecToken` carries the four fields; `mark` stamps them; `restore` asserts
`is_valid_token` and calls `forks.fork(token, frames.len())` at the end; `wf`
carries `fh_wf`. Because `fork` mutates only the `ForkHistory` field, the
reconstruction proof of Chapter 1 is untouched. The exec
`is_valid_token(t) -> bool` is the container-identity check AND `forks.is_valid(...)`.

## 5. Design decisions

**Ids and depths are concrete `u32`, not ghost `nat`.** Production uses `u32`,
and the bit-stealing id types are u31-effective (`define_id31!`: `u32` word, MSB
is the capture tag, `MAX_RAW = 0x7FFF_FFFF`). The model reasons on machine
integers directly; the walk arithmetic is simple `<` comparisons, so `nat`
would buy nothing for the SMT solver. A `u32` branch-id overflow at 4 G forks is
bounded in `fork`'s precondition (`origins.len() + 1 <= u32::MAX`) rather than
ghosted away, mirroring the `saved_len` treatment elsewhere.

`origins` grows by one entry per `restore` and is never reclaimed, so
`origins.len()` is the *lifetime* restore count and this `u32` ceiling is the
binding mark/restore limit (~4.29e9, versus `depth`/`frame_index`, which fall
back on restore and so only cap concurrent nesting). A verified caller proves
the bound; for an unverified one, `restore` carries a runtime guard
(`check_precondition`, [Ch. 2 §2.5](02-trust-boundary.md)) that traps rather
than letting the `as u32` cast silently wrap. The headroom is queryable at
runtime: `restores_remaining()` returns `u32::MAX - origins.len()` (saturating),
so a caller can check before it runs out.

**`depth` and `frame_index` stay separate, with no equating wf clause.** They
are numerically equal at `mark` time but feed different axes of the contract:
`frame_index` is the frame-stack slot the reconstruction mechanism rolls back
to; `depth` is what `is_valid` compares against `current_depth`/`fork_depth`.
Merging them would couple the reconstruction-index requirement to the validity
predicate. Keeping `frame_index < frames.len()` (a structural precondition) and
validity (a separate precondition) independent is what keeps the reconstruction
theorem orthogonal to fork history.

**`ContainerId` is modeled minimally.** The current encoding is `external_body`
with a `spec id(): nat` and an exec `eq` reflecting id equality. The container
check is not on the correctness-critical path (it only rejects cross-container
misuse, a caller error), so genuine end-to-end distinctness is not proved. It
*could* be: a `tracked` monotone ghost counter threaded as the "next id" source
(advanced on each `new`, ensuring `fresh_id` exceeds all prior) expresses a
static integer generator in Verus without a global mutable static. That upgrade
is available if cross-container distinctness is ever wanted as a proved rather
than trusted property. See [Chapter 2](02-trust-boundary.md) for the trust
boundary `ContainerId` sits in.

---
[← Table of Contents](00-table-of-contents.md)
