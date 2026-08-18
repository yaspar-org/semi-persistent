# Proof-Performance Playbook: Diagnosing Slow, Hanging, or Flaky Proofs

*A field guide for maintaining and extending this crate's Verus proofs. When a
proof hangs, diverges, or flakes, these are the concrete recipes we converged on:
what the symptom means and what actually unblocks it. Companion to the
[Proof Attempts Log](proof-attempts-log.md) (the chronological narrative) and
the [Trust Boundary](02-trust-boundary.md) (what is `external_body` and why).
Verus `0.2026.08.02.b677dd5`, z3 4.16.0.*

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

> **Trap:** a per-function `#[verifier::rlimit(N)]` **silently overrides** the
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
where Verus wanted a *set* can change solver behavior. `#![auto]` records the
auto-choice explicitly, but it is **not** risk-free: it accepts whatever Verus
picked, and Verus sometimes picks the quantifier's *conclusion* (see §9). To
suppress the notes wholesale during iteration, pass `--triggers-mode silent`, which
is also why a proof can look "clean" under one invocation and noisy under another.

Also note the *absence* of a note means nothing about cost. The most expensive
quantifier we ever hit (§9, 223 s in one function) was selected **silently**, with
full confidence and no diagnostic at all. Low-confidence notes are about syntactic
ambiguity, not expense; `capture_bits` carries four of them and verifies in 76 ms.

## 7. Cast / target-width facts are usually provable

Casts (`x as usize`, `n as u32`) are often *provable*, not inherently
`external_body`: widening and guarded-narrowing primitive casts verify directly;
`u64 <-> usize` is the value-identity on a 64-bit host, discharged via a crate-wide
`global size_of usize == 8;` pin plus `vstd::layout::unsigned_int_max_values()`
(giving `usize::MAX == u64::MAX`). The `global` is **declared once per crate**; a
second declaration errors with "can only be set once per crate" (it lives in
`bplus_layout.rs`; `index_like.rs` reuses it). Pair such casts with a
`#[cfg(target_pointer_width = "64")]` gate so the host assumption is explicit. This
is how the crate keeps its cast-related trust surface small; the current
default-build `external_body` total is pinned in
[Trust Boundary §3](02-trust-boundary.md) and by the CI gate.

## 8. Process & commit hygiene that paid off

- **One milestone per commit; never commit a broken half-migration.** Always leave
  `cargo verus verify` green.
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

## 9. Quadratic triggers: two independent matches in one trigger set

The single most expensive pathology in this crate. A trigger set containing two
terms whose **bound variables are disjoint** lets the solver instantiate over
every *pair* of matching terms: cost quadratic in the term set, and the term set
is everything in scope.

The canonical instance is the arena disjointness invariant, which is idiomatic
and looks innocent:

```rust
forall|l1: int, p1: int, l2: int, p2: int|
    0 <= l1 < m.len() && 0 <= p1 < m[l1].len()
        && 0 <= l2 < m.len() && 0 <= p2 < m[l2].len()
        && (#[trigger] m[l1][p1]) == (#[trigger] m[l2][p2])
            ==> l1 == l2 && p1 == p2
```

Proved **inline in an exec body**, where both pre- and post-state `wf()` plus every
exec local are in scope, `list::splice_raw` measured **223,553 ms / 1.56 B rlimit /
26.5 M instantiations**: 94% of the whole crate's verification cost, in one
function, hidden behind an `rlimit(800)`.

The fix is not a trigger annotation (there is no better trigger: the shape is
inherently pairwise). It is to **move the goal somewhere nothing else is in
scope**: a lemma over the bare `Seq<Seq<usize>>`, requiring only the old
disjointness rather than a `wf()`:

```
splice_raw       223,553 ms -> 17,543 ms   1.56B -> 75.9M rlimit
the lemma alone       11 ms,  140,854 rlimit
whole crate           3m54s -> 26s
```

**The 11 ms is the lesson.** The goal was nearly free all along; the 223 seconds
were e-matching against irrelevant context, not proof work. Whenever a proof is
expensive, ask what the solver can *see*, not just what it must prove.

Recipes:
- Grep for the shape: a `forall` with 4+ bound variables whose `#[trigger]`s are
  two nested accesses with disjoint variable sets. We found 11 sites this way; all
  were in `list` / `circular_list`, and the three sitting inline in exec bodies
  were the ones worth fixing (`lemma_splice_disjoint`,
  `lemma_insert_fresh_disjoint`).
- Cost scales with the *ambient* context, not the goal. The same quantifier costs
  48 ms in `circular_list::add_singleton` (one fresh ring in scope) and 223 s in
  `splice_raw`. Do not assume every instance needs extracting; measure first.
- A related, cheaper pathology: `#![auto]` picking the quantifier's **conclusion**
  as trigger, so the axiom re-fires on facts it just derived. In
  `abstract-domains::div::lsh_or_tb_sound` that was 14,635 instantiations, 80% of
  the module's total; naming the *hypotheses* instead
  (`#![trigger self.has(r), b.has(bv)]`) cut the module 18,154 -> 3,262
  instantiations and 3690 -> 2089 ms.

## 10. Closed ground terms: skip the solver with `by(compute_only)`

If an `assert` is a closed term over concrete values (no free variables, no
quantifiers), Verus can *evaluate* it in its interpreter instead of asking z3 to
prove it. `abstract-domains::nats` had a ladder of `exp(n) == 2^n` lemmas built
from iterated `cons`, each proved by unfolding chains with
`reveal_with_fuel(lshi, 33)` and a hand-rolled `rlimit(10000)`. Replaced by

```rust
pub proof fn exp_128() ensures exp(128) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000 {
    assert(exp(128) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat) by(compute_only);
}
```

`exp_128` went **27,452,387 rlimit -> 2** (989 ms -> 0 ms) and the module 5370 ms
-> 157 ms (34x), deleting the fuel chains and the `rlimit` attribute with it. Check
for this before writing any unfolding ladder over concrete constants.

Note `by(nonlinear_arith)` is *not* a speed tool and is irrelevant to bit-blasted
(`by(bit_vector)`) goals; upstream used it to stop a divergence, not to gain speed.
