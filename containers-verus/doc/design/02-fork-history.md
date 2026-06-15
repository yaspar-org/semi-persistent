# M5 — Fork history / branch-cut safety (design)

Status: DESIGN, for review. This milestone adds the remaining part of the
production token contract: `restore` requires (as a precondition) that the
token is *valid* — its branch is on the current path of the fork tree and its
depth is within that branch's recorded bound — and that it originates from the
same container.

## 0. What the production code actually does (re-read 2026-06-10)

`containers/src/token.rs` + `containers/src/vec.rs`:

- `VecToken { branch_id: u32, depth: u32, frame_index: u32, container_id }`.
  In `mark`, `depth == frame_index == frames.len()` and `branch_id ==
  forks.current_branch()`. (depth and frame_index are equal at creation; they
  are separate fields but the code never makes them diverge — `frame_index`
  indexes the frame stack, `depth` is what `is_valid` compares.)
- `ContainerId(u32)` from a process-global `AtomicU32` counter — unforgeable
  per-instance identity. `restore` asserts `token.container_id == self.id`.
- `ForkHistory { current_branch_id: u32, origins: Vec<ForkOrigin> }`,
  `ForkOrigin { parent_branch_id: u32, fork_depth: u32 }`. Branch 0 is the
  root; branch `b ≥ 1` is `origins[b-1]` with parent `parent_branch_id` forked
  at `fork_depth`.
- `mark` does NOT touch `forks` (token just snapshots `current_branch()` and
  the depth).
- `restore(token)`:
  1. assert same container;
  2. assert `forks.is_valid(token, frames.len())`;
  3. assert `target_index < frames.len()`;
  4. (the M1–M4 reconstruction we already proved);
  5. **`forks.fork(&token, frames.len())`** — push a new origin
     `(token.branch_id, token.depth)` and set `current_branch_id =
     origins.len()`. This records the cut (see §0.6).
- `is_valid(token, current_depth)`:
  ```
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
  This is the operational definition; §0.6 states the declarative
  characterization it is intended to compute.

## 0.6. Definitions and the branch-safety theorem (precise)

**Fork tree.** `ForkHistory = { current_branch_id: u32, origins: Vec<ForkOrigin> }`.
The branches are the node ids `0, 1, …, origins.len()`; node `0` is the root.
For `b ≥ 1`, `origins[b-1] = { parent_branch_id, fork_depth }` defines branch
`b`'s parent edge: `parent(b) := origins[b-1].parent_branch_id`, labeled with
`fork_depth(b) := origins[b-1].fork_depth`. Invariant `fh_wf`:
`parent(b) < b` for all `1 ≤ b ≤ origins.len()`, and `current_branch_id ≤
origins.len()`.

**How a cut is recorded.** `fork(p, d)` performs exactly:
`origins.push({ parent_branch_id: p, fork_depth: d })` (creating a new branch
`b_new = origins.len()` with `parent(b_new) = p`, `fork_depth(b_new) = d`),
then `current_branch_id := b_new`. Thus a cut is recorded as **one appended
origin entry**. The entry on branch `c` with `parent(c) = p`, `fork_depth(c) =
d` records the fact: *branch `p` was restored at depth `d` and branch `c`
diverged from it there* — so along the path toward `c`, branch `p` is retained
only up to depth `d`.

**On the current path.** Define the current path as the node sequence
`current_branch_id, parent(current_branch_id), parent²(…), …, 0` (finite and
terminating because `parent(b) < b`). A branch `q` *is on the current path* iff
it occurs in this sequence (i.e. `q == current_branch_id` or `q` is a strict
ancestor of `current_branch_id`). Being on the current path is a NECESSARY,
not sufficient, condition for a token on `q` to be valid.

**Depth bound of a path branch.** For `q` on the current path:
- if `q == current_branch_id`, `bound(q) := current_depth` (the live frontier;
  `q` is the live branch, not a cut one);
- if `q` is a strict ancestor, the path is linear so `q` has a unique child `c`
  on it (the node with `parent(c) = q`); `bound(q) := fork_depth(c)` — the
  depth at which `q` was cut on the way to the current branch.

**Branch-safety theorem.** `is_valid(token, current_depth) = true` **iff**
`token.branch_id` is on the current path **and** `token.depth ≤
bound(token.branch_id)`.

Contrapositive (when a token is REJECTED): `token` is invalid iff EITHER
(i) `token.branch_id` is not on the current path — it lies in a subtree that
was diverged away from (`is_valid`'s walk reaches branch `0`); OR
(ii) its branch is on the path but `token.depth > bound(token.branch_id)` — it
names a frame on a prefix that was rolled back past (a strictly-deeper position
on a cut branch, or beyond the live frontier of the current branch).

Note the asymmetry your phrasing should avoid: a token on a *cut* branch `p` is
NOT automatically invalid — it is valid iff `token.depth ≤ fork_depth(c)` for
`p`'s on-path child `c`. Cut branches retain their at-or-below-the-cut tokens
(those name genuine ancestors of the current state).

### Why the walk terminates
Each step sets `branch = origin.parent_branch_id`. Production does NOT prove
`parent_branch_id < branch`, but it is an invariant of how `fork` builds
origins: `current_branch_id` after a fork is `origins.len()`, and the parent is
`token.branch_id` which was a *valid* branch at the time, hence `< origins.len()`
at that point, hence `<` the new branch id. So **`origins[b-1].parent_branch_id
< b`** for all `b ≥ 1` — the parent id strictly decreases, so the walk strictly
descends toward 0 and terminates. This is the key well-formedness invariant we
must carry on `ForkHistory` to give the spec walk a `decreases`.

## 0.5. Architecture: validity is a separate precondition, orthogonal to restore

The most important framing correction (per review 2026-06-10): **fork history
defines token *validity*; it does not touch the restore *mechanism*.** These
are two layers that meet only at `restore`'s entry, never inside the
reconstruction proof:

- **Mechanism (M1–M4, DONE).** `restore` is keyed on `token.frame_index` (the
  stack slot to roll back to). Its correctness theorem —
  `view() == snapshots[frame_index]` — and its structural precondition
  (`frame_index < frames.len()`) are UNCHANGED by M5. We do **not** try to
  discharge that precondition *from* validity; it stays its own requirement.
- **Validity (M5).** `is_valid(token)` is the §0.6 predicate over the fork
  history. It is evaluated as a precondition of `restore` and is otherwise
  independent of the snapshot machinery.

So M5 adds this predicate + its `assert`, plus the `forks.fork(...)` call at
the *end* of restore (which mutates only the `ForkHistory` field, not the
store/diff_log/frames). It does NOT change the reconstruction theorem. There is
therefore **no "validity ⇒ in-range" obligation** — that was a mis-coupling.
`frame_index < frames.len()` remains an independent structural precondition;
validity is a separate precondition.

### `depth` and `frame_index` are DIFFERENT quantities (not to be merged)

They are numerically equal at `mark` time (`mark` stamps both `= frames.len()`)
but they are used by different parts of the contract:

- **`frame_index`** — consumed by the reconstruction mechanism: the frame-stack
  index `restore` rolls back to (`target_index`, used to index `frames`).
- **`depth`** — consumed by `is_valid`: compared against `current_depth` /
  `fork_depth` per §0.6 to decide validity.

Keeping them as one field would couple the reconstruction-index requirement to
the validity predicate. **Decision: keep both, with NO `depth == frame_index`
wf clause** — they are independent fields; the only relation is that `mark`
sets them equal, which neither part of the proof needs to exploit.

## 1. Two layers + the refinement (mirrors M3b's spec/exec split)

- **Exec `ForkHistory`** — faithful port of production: `current_branch_id:
  u32`, `origins: Vec<ForkOrigin>` (each `{ parent_branch_id: u32, fork_depth:
  u32 }`). Methods `new/current_branch/fork/is_valid` with the production
  bodies. IDs and depths are **concrete machine integers** (`u32`), matching
  production and the bit-stealing id story (`define_id31!` gives a u31-effective
  id in a u32 word with the MSB as the capture tag) — see §4(a). No ghost-`nat`
  projection; we reason on `u32`/`as nat` directly where needed.
- **Spec `fork_valid`** — a pure recursive `spec fn` over `(origins,
  current_branch, current_depth, token_branch, token_depth)` that defines the
  walk declaratively, with `decreases branch` (sound by the parent-decreasing
  invariant; the spec is kept total with an explicit `parent >= branch` guard).
  The exec `is_valid` while-loop is proved to compute exactly `fork_valid(...)`.
  **[DONE — `fork_history.rs`.]**
- **Well-formedness `fh_wf`**: `forall b: 1 ≤ b ≤ origins.len() ==>
  origins[b-1].parent_branch_id < b` AND `current_branch_id ≤ origins.len()`.
  `new` establishes it; `fork` maintains it. **[DONE.]**

We do NOT need the heavier "ForkTree with per-node saved_view + current_path"
the stub mentioned: snapshot reconstruction is the M1–M4 theorem keyed on
`frame_index`. The fork history only governs *which tokens are still valid*.
`fork_valid` is the whole ghost story; the "current path" is implicitly the
ancestor chain of `current_branch_id`.

## 2. What M5 proves

1. **Refinement** (DONE): `ForkHistory::is_valid(t_branch, t_depth, d)` returns
   `fork_valid(origins@, current_branch_id, d, t_branch, t_depth)`. Pure over
   `ForkHistory`; no vec.rs.
2. **Branch-safety theorem** (§0.6) — `fork_valid` equals the declarative
   predicate "`token.branch_id` is reachable from `current_branch_id` AND
   `token.depth ≤ walk_bound(token.branch_id)`". Pure over `ForkHistory`.
   **PROVED** — `lemma_fork_valid_characterization` (via
   `lemma_fork_walk_characterization`, induction on `branch` under `fh_wf`).
   `reaches`/`walk_bound` are the spec fns realizing "on the current path" and
   "the branch's depth bound".
3. **`mark`/`restore`/`fork` maintain `fh_wf`**, and `restore` calls
   `forks.fork(token, frames.len())` after reconstruction (records the cut).
   The only vec.rs wiring; `fork` mutates only the `ForkHistory` field, so the
   M1–M4 reconstruction proof is unchanged.
4. **`is_valid_token(t)` exec method** = container check (§4c) AND
   `forks.is_valid(...)`. `restore` requires it as a precondition, alongside —
   not in place of — its own `frame_index < frames.len()` precondition (§0.5).

### 2.1. Proof status (all DONE)

- Refinement (item 1): `is_valid` while-loop == `fork_valid`.
- `new`/`fork` maintain `fh_wf`.
- GENERAL branch-safety theorem (item 2, §0.6): `lemma_fork_valid_characterization`
  proves `fork_valid == reaches(current, tb) && td ≤ walk_bound(current, cd, tb)`
  for ALL cases — current branch, strict ancestors (parent, grandparent, …),
  and off-path rejection (`reaches` false ⇒ invalid). Proved by induction on
  `branch` under `fh_wf` (which kills the `parent ≥ branch` dead guards so the
  three recursions align).
- `lemma_branch_cut` (single-cut instance) and `lemma_fork_valid_current_branch`
  (current-branch case) remain as convenient specializations.

## 3. Build order (each commit green)

1. **`ContainerId`** — concrete id wrapper. **[DONE — see §4c.]**
2. **`ForkHistory` + `fork_valid` + refinement lemma**. **[DONE.]**
3. **Branch-safety theorem**: `reaches`/`walk_bound` spec fns +
   `lemma_fork_valid_characterization` proving `fork_valid ⟺ reaches(tb) &&
   td ≤ walk_bound(tb)` (§0.6). Pure over `ForkHistory`, no vec.rs. **[DONE.]**
4. **Wire into `Vec`**: add `forks: ForkHistory` + `id: ContainerId` fields,
   extend `VecToken` with `branch_id`/`depth`/`container_id` (real `u32`/
   `ContainerId`), `mark` stamps them, `restore` `assert`s `is_valid_token` and
   calls `forks.fork(...)` at the end, `wf` carries `fh_wf`. Restore's
   reconstruction contract is unchanged. (REVIEW; small additive diff.)

## 4. Decisions (resolved in review 2026-06-10)

- (a) **IDs/depths are concrete `u32`, not ghost `nat`.** Production uses `u32`;
  the bit-stealing id types are u31-effective (`define_id31!`: `u32` word, MSB =
  capture tag, `MAX_RAW = 0x7FFF_FFFF`). The model reasons on machine integers
  directly. (`nat` would only be worth it if it materially eased SMT — it does
  not here; the walk arithmetic is simple `<` comparisons.) A `u32` branch-id
  overflow at 4 G forks is the same unreachable edge as elsewhere; bound it in
  `fork`'s precondition (`origins.len() + 1 <= u32::MAX`) rather than ghosting
  it away, mirroring the M1 `saved_len` treatment.
- (b) **`depth` and `frame_index` stay SEPARATE fields, no equating wf clause.**
  See §0.5 — they are different concepts (validity axis vs mechanism axis).
- (c) **`ContainerId` check is trivial; keep it minimal but DO model the
  generator faithfully.** A static integer generator IS expressible in Verus:
  a `tracked` ghost monotone counter (a `Tracked<...>` resource threaded as the
  "next id" source, advanced on each `new()`, with `ensures fresh_id > all
  prior`) gives genuine distinctness — no global mutable static needed; the
  monotone ghost token is passed/owned like any linear resource. Since the
  container check is not on the correctness-critical path (it only rejects
  cross-container misuse, a caller error), we keep the *current* lean encoding
  (`external_body` + `id(): nat`, exec `eq` reflecting id equality) for now and
  note the tracked-counter upgrade as available if we later want end-to-end
  distinctness as a *proved* (not assumed) property.

---
[← Table of Contents](00-table-of-contents.md)
