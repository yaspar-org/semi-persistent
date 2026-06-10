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

## 0.5. Architecture: validity is a SEPARATE GATE, orthogonal to restore

The most important framing correction (per review 2026-06-10): **fork history
defines token *validity*; it does not touch the restore *mechanism*.** These
are two layers that meet only at `restore`'s entry, never inside the
reconstruction proof:

- **Mechanism (M1–M4, DONE).** `restore` is keyed on `token.frame_index` (the
  stack slot to roll back to). Its correctness theorem —
  `view() == snapshots[frame_index]` — and its structural precondition
  (`frame_index < frames.len()`) are UNCHANGED by M5. We do **not** try to
  discharge that precondition *from* validity; it stays its own requirement.
- **Validity (M5).** `is_valid(token)` is a predicate over the fork history
  answering "is this token's branch/depth on the live, un-cut timeline". It is
  computed and checked at `restore`'s entry (a `bool` the caller/contract
  gates on) and is otherwise independent of the snapshot machinery.

So M5 adds an orthogonal predicate + its `assert`, plus the `forks.fork(...)`
bookkeeping call at the *end* of restore (which only mutates `ForkHistory`, not
the store/diff_log/frames). It does NOT re-shape the reconstruction theorem.
There is therefore **no "validity ⇒ in-range" obligation** — that was a
mis-coupling. frame_index-in-range remains a structural precondition; validity
is a parallel guarantee.

### `depth` and `frame_index` are DIFFERENT concepts (not to be merged)

They are numerically equal at `mark` time (`mark` stamps both `= frames.len()`)
but they answer different questions and live in different layers:

- **`frame_index`** — the *mechanism* coordinate: which frame-stack slot
  `restore` rolls back to (`target_index`, used to index `frames`).
- **`depth`** — the *validity* coordinate: the token's position along its
  branch's timeline, compared against `current_depth` / `fork_depth` in
  `is_valid`. It is what tells an *abandoned-future* token (deeper than the
  cut) apart from a genuine ancestor.

Keeping them as one field would conflate the mechanism axis with the validity
axis. **Decision: keep both, with NO `depth == frame_index` wf clause** — they
are independent fields; the only relation is that `mark` happens to set them
equal, which we don't need to exploit (and shouldn't, to keep the layers clean).

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
  **[DONE — `fork_history.rs`, 7 verified.]**
- **Well-formedness `fh_wf`**: `forall b: 1 ≤ b ≤ origins.len() ==>
  origins[b-1].parent_branch_id < b` AND `current_branch_id ≤ origins.len()`.
  `new` establishes it; `fork` maintains it. **[DONE.]**

We do NOT need the heavier "ForkTree with per-node saved_view + current_path"
the stub mentioned: snapshot reconstruction is the M1–M4 theorem keyed on
`frame_index`. The fork history only governs *which tokens are still valid*.
`fork_valid` is the whole ghost story; the "current path" is implicitly the
ancestor chain of `current_branch_id`.

## 2. The safety theorem (what M5 proves)

1. **Refinement** (DONE): `ForkHistory::is_valid(t_branch, t_depth, d)` returns
   `fork_valid(origins@, current_branch_id, d, t_branch, t_depth)`. Pure,
   self-contained, touches nothing in vec.rs.
2. **Branch-cut characterization**: `fork_valid` is exactly "token's branch is
   an ancestor-or-equal of the current branch, and its depth is within that
   branch's live (un-cut) prefix". A path-level lemma over the fork tree —
   the real content of branch-cut safety. Pure over `ForkHistory`.
3. **`mark`/`restore`/`fork` maintain `fh_wf`**, and `restore` calls
   `forks.fork(token, frames.len())` at the END (after reconstruction), cutting
   the branch. This is the only vec.rs wiring; `fork` mutates only the
   `ForkHistory` field, so the M1–M4 reconstruction proof is untouched.
4. **`is_valid_token(t)` exec method** = container check (cheap, see §4c) AND
   `forks.is_valid(...)`, exposed so callers gate `restore` on it. `restore`'s
   contract keeps its own `frame_index < frames.len()` structural precondition
   (validity is parallel, NOT a substitute — see §0.5).

Steps 1 (+ the data types) are DONE and self-contained. Step 2 is a pure
fork-history lemma (no vec.rs). Steps 3–4 wire `ForkHistory` into `Vec` and
extend `VecToken` — REVIEW GATE, but now a *small additive* change (a new field
+ a gate + a tail call), not a reshape of restore.

## 3. Build order (each commit green)

1. **`ContainerId`** — concrete id wrapper. **[DONE — see §4c for the
   modeling.]**
2. **`ForkHistory` + `fork_valid` + refinement lemma**. **[DONE.]**
3. **Branch-cut characterization lemma** (§2.2) — pure over `ForkHistory`,
   no vec.rs. The mathematical heart of M5.
4. **Wire into `Vec`**: add `forks: ForkHistory` + `id: ContainerId` fields,
   extend `VecToken` with `branch_id`/`depth`/`container_id` (real `u32`/
   `ContainerId`), `mark` stamps them, `restore` `assert`s `is_valid_token` and
   calls `forks.fork(...)` at the end, `wf` carries `fh_wf`. Restore's
   reconstruction contract is unchanged. (REVIEW GATE; small additive diff.)

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
