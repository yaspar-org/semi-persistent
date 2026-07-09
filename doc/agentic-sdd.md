# The Agentic SDD Harness

*Companion documentation for the `.claude/` directory: an agentic, spec-driven
development and verification system for this repository. The operational
reference is [`.claude/README.md`](../.claude/README.md); this chapter explains
the system's purpose, its organizing principles, its catalogs, and its
calibration discipline for readers of the project documentation.*

## 1. Purpose

The harness (named `sdd`, for spec-driven development) structures how LLM
agents produce and verify code in this repository. It addresses a specific
weakness: an LLM has broad knowledge but no rigor; it will assert that a
property holds without evidence, weaken a specification to make a proof close,
or report a solver timeout as a refutation. Verification tools (z3, Verus,
property-based testing, fuzzers) have the opposite profile: rigor without
knowledge. The harness composes the two so that agents propose and tools
decide. No property is considered established unless an oracle produced the
evidence, and every claim is traceable from the stakeholder requirement to the
oracle output that discharged it.

The process covers the activities of a conventional development lifecycle
(requirements capture, architecture, detailed design, verification planning,
implementation, verification, qualification), but it is not organized as a
phase sequence. The activities are reachable in any order, on demand, driven
by the current intent and by feedback from the tools (section 4). The target
language is Rust, verified with Verus; the Rust-specific knowledge (idioms,
what the borrow checker guarantees for free versus what needs a Verus proof,
the arena style for aliased and cyclic structures) lives under
`.claude/languages/rust/`.

## 2. Organization

The harness is built on the three extensibility primitives of Claude Code,
with a strict division of responsibilities:

| Primitive | Location | Responsibility |
|---|---|---|
| Subagents | `.claude/agents/*.md` (17) | judgment: each engineering role is one agent with its own prompt, tool allowlist, and output ownership |
| Skills | `.claude/skills/*/SKILL.md` (20) | knowledge: reusable methods and reference material, loaded by agents on demand |
| Workflows | `.claude/workflows/*.js` (10) | control flow: deterministic scripts that spawn agents, route on their structured results, and enforce budgets |

The rule that assigns a responsibility to a primitive: anything requiring
judgment is an agent; anything that is reusable method knowledge is a skill;
anything that counts, routes, or enforces an invariant is deterministic script
code. In particular, the plan of a multi-step process lives in workflow
variables, not in any agent's context; an agent can fail or be replaced
without the process losing its position.

## 3. Organizing principles

Twelve principles govern the design (stated fully in the `principles` skill).
The ones a reader needs in order to follow the rest of this chapter:

1. **Role reification.** Each role (elicitation, architecture, design,
   planning, implementation, verification, qualification, and their advisors)
   is a distinct agent. One agent doing everything reduces to generic LLM
   coding with no checkable role boundaries.
2. **Neuro-symbolic composition.** At every step the agent proposes and an
   oracle decides. A verification claim without a tool run behind it is
   rejected at the gate.
3. **Context hygiene.** Verifiers and reviewers run in fresh contexts and
   receive only the artifact under review, the contracts it must satisfy, and
   oracle outputs; never the producer's reasoning trace. In Claude Code a new
   subagent invocation is a fresh context by construction.
4. **Reviewers do not edit.** A reviewer that edits the artifact it reviews
   becomes a producer and then defends its own edits; reviewers return reports
   and verdicts only.
5. **Property provenance.** Every verifiable property is tagged CP
   (stakeholder-owned) or DP (design-induced). Provenance decides who may
   change a property and how a falsification is routed: a falsified CP is a
   stakeholder decision; a falsified DP is an engineering revision.
6. **Artifact ownership.** Every document has exactly one owning agent; the
   exceptions are three append-only shared logs (design rationale, proof
   attempts, traceability). Ownership makes staleness attributable.
7. **Two evidence chains.** A descending chain refines intent into code
   (spec, architecture, design, plans, implementation); an ascending chain of
   oracle outputs, verification reports, and gate verdicts attests each step.
   A delivery is complete only when both chains are closed.

## 4. The artifact graph and reactive dispatch

The document set of an iteration (specification, architecture, design,
property registry, verification plan, task plan, code, verification record;
see the `document-set` skill for the full placement table) forms a dependency
graph. Each node has one owner, a set of upstream nodes, and a gate: a fresh
verifier instance that checks the node against its upstream contracts using
the oracles assigned by the verification plan. The `artifact-graph` skill is
the canonical statement of the graph; the reactive workflows carry a
JavaScript projection of it.

Freshness is defined recursively. A node is fresh if and only if it exists,
its gate verdict is `pass`, the verdict's recorded input hashes still match
the current content of the node and of its upstream nodes, and every upstream
node is itself fresh. The hash record is written by the verifier next to each
verdict (`gates/<gate>.inputs`, one SHA-256 line per input file); a verdict
without its hash record is treated as unverified, since it cannot demonstrate
what it was issued against.

Three consequences give the process its reactive character:

1. **Any entry point.** An intervention may target any node (revise the
   specification, rework the architecture, patch one function). The
   `status` workflow computes the freshness of every node deterministically
   and returns the minimal repair plan in topological order; the `advance`
   workflow brings a single node up to date by running its producer, then its
   gate, with a bounded retry budget.
2. **One invariant.** A gate never issues `pass` against stale upstream
   inputs; asked to, it escalates and names the stale inputs. Any edit is
   permitted at any time, but a passing verdict can only be minted on fresh
   inputs, so a fully passing graph is a proof of coherence and a stale
   region is precisely delimited.
3. **Lazy invalidation.** Editing a node does not trigger re-derivation of
   the nodes that depend on it. Staleness is computed from the hashes when
   next queried; repair happens when an intent requires the affected nodes.
   The scope of re-verification is bounded by the intervention's perimeter,
   using the same non-regression frame that the brownfield path establishes:
   properties outside the perimeter are frozen and checked to still hold,
   which is what makes narrow re-verification sound.

Gate verdicts are structured as one of five outcome shapes, because the kinds
of failure route differently: `pass` (advance), `refuted` (a counterexample
exists; escalate only if it falsifies a stakeholder property and is confirmed
reachable, otherwise retry), `negated` (the negation was proved, which is
stronger than a counterexample), `stall` (no progress: solver `unknown`,
timeout, or an unproven inductive step; never reported as a refutation), and
`escalate` (a decision exceeds the agents' authority). Tool feedback re-enters
the dispatch as a new intent: for example, a reachable top-level refutation
targets the specification; a stall from a failed inductive step targets
invariant strengthening; a divergence between a formal specification and the
code is surfaced as a possible code defect, never silently re-documented.

## 5. Agents catalog

| Agent | Role |
|---|---|
| `elicitation` | world model, assumptions, formal specification (SMT-LIB twin plus controlled-English requirements) |
| `gap-analysis` | abductive detection of specification gaps (advisor to elicitation) |
| `architect` | candidate architectures, coupling metrics, interface contracts |
| `algorithm-expert` | algorithm and data-structure feasibility (advisor to the architect) |
| `robustness-analysis` | sensitivity analysis of commitments (writes the sensitivity report) |
| `designer` | language-level realization and the property registry |
| `task-planner` | task decomposition with dependency graph and property coverage |
| `verification-planner` | oracle assignment per property (the verification plan) |
| `implementer` | code, tests, and Verus contracts |
| `verifier` | gate execution: runs the assigned oracles, issues the outcome-shape verdict and the input-hash record |
| `failure-diagnosis` | classification of failures by layer (fresh context) |
| `critic` | adversarial review of drafts before a gate; reports findings with severity and confidence, applies no edits |
| `qualification` | final sign-off, verification record, iteration synthesis (including open decisions and out-of-scope observations) |
| `maintenance` | supersession annotations on outdated artifacts |
| `spec-extraction` | brownfield reconstruction of the as-is specification and the non-regression frame |
| `bug-hunter` | SMT-backed differential bug search |
| `doc-sync` | post-development reconciliation of documentation with code |

## 6. Skills catalog

Foundations: `principles` (the twelve principles and property provenance),
`artifact-graph` (the dependency graph, freshness rules, hash convention),
`document-set` (document placement and ownership), `feedback-protocol`
(verdict semantics and loop discipline for producers).

Requirements: `requirements-format` (precision requirements, the
controlled-English logic surfaces, the SMT-LIB twin),
`abductive-requirement-refinement` (from user story to interface-grounded
acceptance criteria), `theory-building` (world model, assumptions, rationale
log, sensitivity).

Verification methods: `property-taxonomy` (sixteen property categories with
provenance and difficulty tags), `oracle-ladder` (difficulty to verification
method), `bi-abduction-local` and `bi-abduction-global` (per-function and
inter-procedural contract inference for Verus), `bi-abduction-arena`
(dynamic-frames verification of arena-allocated, integer-indexed, internally
aliased structures), `smt-bug-finding` (differential SMT search with
confirmation on the real system), `proof-slop-check` (inventory and
classification of proof escape hatches: `assume`, `admit`, `external_body`,
vacuous preconditions, contentless postconditions, assertion-free tests).

Dynamic analysis: `runtime-contract-instrumentation` (properties as executable
checks and monitors), `trace-logging` (structured execution traces),
`invariant-inference` (likely invariants mined from traces, then proved or
rejected).

Architecture and maintenance: `architecture-design` (partitioning and coupling
metrics), `language-profiles` (router to the Rust and Verus profile under
`.claude/languages/rust/`), `drift-detection` (classification of documentation
and specification drift against code).

## 7. Workflows catalog

The lifecycle stages, each returning a structured envelope and advancing only
on a passing status: `capture-greenfield` (world model, specification,
preliminary blueprint), `capture-brownfield` (as-is specification,
non-regression frame, change perimeter), `design-plan` (committed
architecture, detailed design, verification plan, task plan), `execute` (task
implementation to convergence, with formal proof and bug mining on flagged
tasks), `finalize` (qualification, documentation reconciliation, commit
proposal; it never rewrites git history or pushes).

Sub-workflows called by `execute`: `verify-bi-abduction` (compositional
contract verification, local then global) and `mine-bugs` (fan-out
differential bug search with adversarial confirmation).

The reactive layer: `status` (the freshness sweep and repair plan), `advance`
(bring one node up to date), and `calibrate` (the probe suite of section 8).

## 8. Calibration

The harness is prompt-based, and its rules are tuned against the observed
behavior of a specific model generation, not against timeless properties of
language models. `.claude/CALIBRATION.md` records that tuning explicitly so
that a model change is a deliberate recalibration rather than silent drift.
It contains:

1. **The assumption statement.** Which model generation the prompts were
   tuned against and the behavioral traits assumed (near-literal instruction
   following; under-use of optional capabilities unless triggers are
   explicit; literal compliance with filtering instructions, which silently
   suppresses findings; a bias toward closing a task, which under proof
   pressure becomes routing around hard obligations).
2. **The rule ledger.** Each hard rule in the prompts, the failure mode it
   defends against, and the condition under which it could be relaxed. Rules
   that are structural rather than behavioral (context hygiene, reviewer
   non-editing, anti-weakening) are marked as permanent.
3. **The probe suite.** `.claude/probes/` holds fixture scenarios with known
   expected outcome shapes; each fixture contains a complete, canned oracle
   transcript and forbids live tool runs, so it tests how the agent
   interprets oracle output rather than whether the tools work. The
   `calibrate` workflow replays the fixtures against the live verifier and
   scores the structured verdicts deterministically; the expected answers
   live only in the scorer. Current probes: a solver `unknown` must be
   reported as `stall`, not `refuted`; a counterexample to induction with an
   unconfirmed pre-state must be reported as `stall`; a contract weaker than
   the stakeholder property it claims to discharge must be caught even when
   the weakened obligation verifies.
4. **The procedure and the log.** On any model change: run the probe suite,
   review per-gate retry rates and verdict distributions from the run
   evidence, update the ledger, and record a dated entry. Prompt edits
   motivated by calibration cite the probe or telemetry that justified them.

In the artifact graph the calibration is a node upstream of everything: a
model change invalidates it, and verdicts issued under a stale calibration
are treated as provisional.

## 9. Relation to this repository

The harness definitions live at the repository root (`.claude/`) and apply to
sessions started anywhere in the repository. The natural first applications
are the crates that already carry the corresponding document sets:
`containers-verus` (whose `doc/design/` chapters, proof-attempts log, and
arena verification style directly instantiate the `document-set` and
`bi-abduction-arena` skills) and future verified extensions of `containers`,
`egraph`, and `abstract-domains`. The verifier and implementer agents invoke
the real toolchain (z3, Verus via the crate's verification script, cargo,
proptest); a missing tool fails the corresponding oracle call rather than
being simulated. Run evidence is written under `runs/<run-id>/` and is
ephemeral; everything durable is distilled into the target crate's `doc/`
subdirectories as described in the `document-set` skill.
