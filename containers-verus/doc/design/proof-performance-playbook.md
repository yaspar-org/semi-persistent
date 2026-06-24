# Proof-Performance Playbook: Diagnosing Slow, Hanging, or Flaky Proofs

*A field guide for maintaining and extending this crate's Verus proofs. When a
proof hangs, diverges, or flakes, these are the concrete recipes we converged on:
what the symptom means and what actually unblocks it. Companion to the
[Proof Attempts Log](proof-attempts-log.md) (the chronological narrative) and
the [Trust Boundary](02-trust-boundary.md) (what is `external_body` and why).
Verus `0.2026.04.12.f1166c4`.*

[Design Table of Contents](00-table-of-contents.md)

The recurring theme: when a proof *fails*, Verus says little, so you diagnose
from indirect signals. The order below is roughly "cheapest check first."

## 1. A hang at low CPU is a matching loop, not slow search

Check a process monitor. One fully-pegged core (~100% of a core) = z3 is
searching hard; bump `rlimit` or simplify the goal. **Low total CPU** (e.g.
~2.5% across many cores) with a long wall-clock = a **quantifier matching loop**:
z3 is generating instantiations faster than it makes progress. More `rlimit`
makes this *worse*, not better. Stop raising the budget and go fix triggers /
hypotheses (§4, §6). This is exactly how `circular_list::lemma_splice_covers` was
diagnosed; it hung 15+ minutes at ~2.5% CPU.

## 2. Isolate, then bisect by function

- `verus src/lib.rs --crate-type=lib --verify-only-module M --verify-function '*name'`
  verifies a single function. Note: `--verify-function` requires
  `--verify-only-module`, **not** `--verify-module` (the latter errors with a
  message telling you so).
- A whole module hanging is usually **one** pathological function. Isolate each in
  parallel under a per-function `gtimeout`; the one that times out alone is the
  culprit. (For `circular_list`, 21 of 22 functions verified in isolation; one did
  not: that one was the whole problem.)
- **Read the results line, not the shell exit code.** `--verify-function` exits
  nonzero even on success (partial-verification status); trust
  `verification results:: N verified, 0 errors`, and beware reading a pipe's exit
  code (grep's) instead of verus's.

## 3. Distinguish the four failure modes

`postcondition not satisfied` / `assertion failed` covers four different
situations with different fixes. Check in this order:

1. **Nonlinear arithmetic**: any `*` between non-constants (or even `*0` / `*1`
   with a *symbolic* factor) that Verus won't attempt automatically. Wrap the
   step and feed it the facts it needs:
   `assert(a*(b+c) == a*b + a*c) by (nonlinear_arith);` (use `requires` inside the
   `by` to hand it antecedents). We needed this for every `lmin * …` step in the
   B+tree node-count bound (the arena-capacity proof).
2. **Definition not unfolding (fuel)**: a recursive spec fn
   (`forest_node_count`, `chain_keys`, …) that must compute on a small literal.
   Hand-unfold: `assert(s.drop_first() =~= seq![...]); assert(f(s) == ...);` step
   by step, or `reveal_with_fuel`.
3. **Over-broad hypothesis**: the expensive, non-obvious one. See §4.
4. **Genuinely over budget**: only after ruling out 1–3, raise `rlimit` (and
   treat needing a big one as a smell, §5).

## 4. Over-broad `requires` is the usual blowup cause

If a proof drags in a heavyweight invariant it does not actually use (classically
`requires self.wf()` when the body needs a single clause), the unused conjuncts'
quantifiers, especially nested `forall` over sequence indexing, e-match
combinatorially and the proof blows up or hangs.

**Weaken the precondition to exactly what the body uses.** Weakening a `requires`
is always caller-safe: any caller that proved the stronger precondition still
satisfies the weaker one. Concretely, `lemma_splice_covers` required `pre.wf()`
but used only `pre.model_covers()`; the dropped `model_disjoint` clause was a
quad-nested `forall|c1,p1,c2,p2| m[c1][p1]==m[c2][p2]`. Weakening took it from a
240-second timeout to **25 ms**. Audit `requires` by hand: for each clause, ask
"does the body actually need this?"

## 5. Treat large `rlimit` as debt; prefer structure over budget

`#[verifier::rlimit(800)] + #[verifier::spinoff_prover]` is a red flag, not a
solution: a proof that marginal passes on a lucky z3 seed and **flakes later**.
This actually happened here: `lemma_splice_covers` was committed green, then
stopped converging weeks later from seed nondeterminism alone, same source and
binary.

Prefer, in order: weaken hypotheses (§4) → add explicit trigger annotations (§6)
→ split the lemma → factor a sub-lemma the prover uses as a black box. Reach for a
big `rlimit` only when the proof is genuinely large *and* stable, and after a fix
prove it converges at a **low** rlimit: a pass at `rlimit(50)` is robust; a pass
at `rlimit(800)` is borrowed time. `spinoff_prover` legitimately isolates a heavy
proof into its own solver instance, but it does not make a matching loop converge.

> **Footgun:** a per-function `#[verifier::rlimit(N)]` **silently overrides** the
> `--rlimit` CLI flag. A "starve it to see if it fails fast" experiment via
> `--rlimit 5` is a no-op if the function carries an attribute; you're still at
> `N`. To probe the budget, edit the attribute, not the flag.

## 6. Trigger notes: make the chosen trigger explicit

`cargo verus verify` (without `--triggers-mode silent`) emits "low confidence:
automatically chose trigger" notes. They are advisory, not errors, and are a
*syntactic* judgment (multiple candidate triggers existed) rather than a
performance one; the flagged function is often not the actual hot spot.

To silence a note **and** pin the choice for stability, annotate the quantifier
with the trigger Verus reported: `#[trigger]` on the chosen subexpression for a
single trigger, or `#![trigger e1, e2]` / multiple `#![trigger ...]` clauses for a
multi-trigger set. Match exactly what the note printed; a single `#[trigger]`
where Verus wanted a *set* can change solver behavior. `#![auto]` confirms the
auto-choice with zero risk if an explicit pick destabilizes the proof. To suppress
the notes wholesale during iteration, pass `--triggers-mode silent` (what
`verify-all.sh` does, which is also why a proof can look "clean" under one
invocation and noisy under another).

## 7. Cast / target-width facts are usually provable

Casts (`x as usize`, `n as u32`) are often *provable*, not inherently
`external_body`: widening and guarded-narrowing primitive casts verify directly;
`u64 <-> usize` is the value-identity on a 64-bit host, discharged via a crate-wide
`global size_of usize == 8;` pin plus `vstd::layout::unsigned_int_max_values()`
(giving `usize::MAX == u64::MAX`). The `global` is **declared once per crate**; a
second declaration errors with "can only be set once per crate" (it lives in
`bplus_layout.rs`; `index_like.rs` reuses it). Pair such casts with a
`#[cfg(target_pointer_width = "64")]` gate so the host assumption is explicit. This
is how the crate took its trust surface from 16 `external_body` items down to 6;
see [Trust Boundary §3](02-trust-boundary.md).

## 8. Process & commit hygiene that paid off

- **One milestone per commit; never commit a broken half-migration.** Always leave
  `verify-all.sh` green.
- **Measure blast radius before committing to an approach.** For a risky spec
  change (e.g. strengthening a `wf` clause), add it and immediately see *which*
  functions break; Verus's failure set is your bi-abduction oracle. We used this
  to scope the B+tree's `arena.len() == node_count` `wf`-clause addition before
  threading it through the insert recursion.
- **Property-test the executable code against a plain-`std` oracle.** `requires` /
  `ensures` are erased under `cargo test`, so proptests catch exec-path mistakes
  the proof never sees, and they are the only runtime guard on trusted
  (`external_body`) bodies the proof cannot reach (see
  `tests/external_body_contract_fuzz.rs`).

---
[← Table of Contents](00-table-of-contents.md)
