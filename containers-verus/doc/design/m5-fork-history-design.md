# M5 — Fork history / branch-cut safety (design)

Status: DESIGN, for review. Tree is green at HEAD (`d66526d`, 142 verified).
This milestone adds the last piece of the production token contract: a token
is only valid to `restore` if it lies on the **current branch path** of the
fork tree (not an "abandoned future"), and only on the **same container**.

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
     origins.len()`. This is the branch cut: everything that was "above" the
     restore target is now an abandoned future.
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
  In words: walk from the current branch up the parent chain. The token is
  valid iff its branch is an ancestor-or-equal of the current branch AND its
  depth is within the live prefix of that branch — `≤ current_depth` if the
  token is on the current branch, else `≤ fork_depth` of the fork that leaves
  the token's branch toward the current head.

### Why the walk terminates
Each step sets `branch = origin.parent_branch_id`. Production does NOT prove
`parent_branch_id < branch`, but it is an invariant of how `fork` builds
origins: `current_branch_id` after a fork is `origins.len()`, and the parent is
`token.branch_id` which was a *valid* branch at the time, hence `< origins.len()`
at that point, hence `<` the new branch id. So **`origins[b-1].parent_branch_id
< b`** for all `b ≥ 1` — the parent id strictly decreases, so the walk strictly
descends toward 0 and terminates. This is the key well-formedness invariant we
must carry on `ForkHistory` to give the spec walk a `decreases`.

## 1. Two layers + the refinement (mirrors M3b's spec/exec split)

- **Exec `ForkHistory`** — faithful port of production: `current_branch_id:
  u32` (model as `nat` ghost-projected, like `IndexLike`, or just `u32` with
  `as_nat`), `origins: Vec<ForkOrigin>`. Methods `new/current_branch/fork/
  is_valid` with the production bodies.
- **Spec `fork_valid`** — a pure recursive `spec fn` over `(origins,
  current_branch, current_depth, token_branch, token_depth)` that defines the
  walk declaratively, with `decreases branch` (sound by the parent-decreasing
  invariant). The exec `is_valid` while-loop is proved to compute exactly
  `fork_valid(...)`.
- **Well-formedness `fh_wf`**: `forall b: 1 ≤ b ≤ origins.len() ==>
  origins[b-1].parent_branch_id < b` AND `current_branch_id ≤ origins.len()`.
  `new` establishes it (empty origins, branch 0); `fork` maintains it (new
  parent is an existing valid branch id, new current is origins.len()).

The stub doc mentions a heavier "ForkTree with per-node saved_view +
current_path". We DON'T need saved_view in the tree: the snapshot
reconstruction is already the M1–M4 theorem keyed on `frame_index`. The fork
tree only governs *which frame_index values are still restorable*. So the
lean model is: `fork_valid` is the whole ghost story; the "current path" is
implicitly the ancestor chain of `current_branch_id`, and
`current_path.contains(node)` ⟺ `fork_valid(... that node ...)`.

## 2. The safety theorem (what M5 proves)

1. **Refinement**: `ForkHistory::is_valid(t, d)` (exec, while-loop) returns
   `fork_valid(origins@, current_branch_id, d, t.branch_id, t.depth)`
   (spec). Pure, self-contained — provable now, touches nothing in vec.rs.
2. **Container safety**: `ContainerId` equality is unforgeable — two distinct
   `Vec::new()` calls get distinct ids (ghost `id: nat`, `external_body`
   constructor axiomatized fresh). So `t.container_id == self.id ==> t was
   minted by self`.
3. **Validity ⇒ in-range**: if `is_valid_token(t)` then
   `t.frame_index < frames.len()` (so the M4 `restore` precondition
   `token.frame_idx < frames@.len()` is *discharged* by validity, not assumed).
   This is the bridge that lets `restore`'s public contract require only
   `is_valid_token(t)` instead of the raw in-range condition.
4. **End-to-end**: `restore(t)` with `is_valid_token(t)` ensures
   `view() == snapshots[t.frame_index]` (the M4 theorem) AND re-establishes
   `fh_wf` after the `fork` call.

Step 1+2 are the self-contained, design-stable core. Steps 3–4 rewire vec.rs's
token surface (currently `VecToken { frame_idx }`) and the mark/restore
contracts — higher risk, done after the core + this review.

## 3. Build order (each commit green)

1. **`ContainerId`** — `external_body` struct wrapping the runtime id + ghost
   `id: nat`; `new()` ensures a fresh ghost id (`spec fn` distinctness via an
   uninterpreted "next id" the axiom advances). Standalone; no design freedom.
2. **`ForkHistory` + `fork_valid` + refinement lemma** — the data types,
   `fh_wf`, the spec walk with `decreases`, and the exec `is_valid` ⟺
   `fork_valid` proof. Standalone (own module); doesn't touch vec.rs.
3. **Token surface**: extend `VecToken` with `branch_id`/`depth`/`container_id`
   (ghost or real), thread `ForkHistory` + `ContainerId` into `Vec`, update
   `mark` to stamp them and `restore` to call `fork`. Re-prove `wf` carries
   `fh_wf`. (Touches vec.rs — REVIEW GATE before starting.)
4. **`is_valid_token` exec method + validity⇒in-range** + restore's public
   contract switched to require validity. End-to-end safety theorem.

## 4. Open questions for review

- (a) Model `branch_id`/`depth` as `u32` (real, with `as_nat`) or as ghost
  `nat` carried alongside a real `u32`? Production uses `u32`; a `u32` overflow
  at 4 G forks is a real (if unreachable) edge — mirror the M1 `saved_len`
  fix and bound it, or treat ids as unbounded ghost `nat` and keep `u32` only
  in exec? **Lean: `nat` ghost + `u32` exec with `as_nat`, like `IndexLike`.**
- (b) Do we fold `depth == frame_index` into one field in the verus model
  (production keeps two but never diverges them), or keep both for fidelity?
  **Lean: keep both, with a wf clause `token.depth == token.frame_index` so
  the validity⇒in-range bridge can use `depth` and reconstruction can use
  `frame_index`.**
- (c) `ContainerId` freshness axiom shape — a global ghost counter is awkward
  in Verus (no mutable statics in spec). **Lean: `new()` is `external_body`
  returning a value whose ghost `id` is `>` any previously handed out, modeled
  by an uninterpreted monotone source; for the cross-container check we only
  need *distinctness*, which `external_body` + an `ensures self.id == <fresh>`
  with an opaque fresh-ness predicate provides.** Needs care; flagged.
