<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E12: worklist fixpoint in `extract_best` (C3)

**Closed without implementing.** The experiment's own gate was "measure pass
counts first; if typical ≤ 3, close". Measured: **2 on every workload**, up to
depth 400.

## The proposal

`extract_best` rescans all *n* nodes on every pass until no cost improves, which
is O(n x passes). C3 proposed a worklist instead: seed it with leaf and literal
nodes, and on each cost improvement push that class's parents using the existing
`by_child_pos` / `by_contains` indexes. That turns the cost into O(edges).

## The measurement

`egraph/examples/extractprobe.rs` replays the fixpoint and counts passes:

| workload | classes | passes | scan visits | term nodes |
|---|---|---|---|---|
| `tree20`   |  41 | 2 |  82 |      41 |
| `tree200`  | 401 | 2 | 802 |     401 |
| `dag12`    |  13 | 2 |  26 |   8 191 |
| `dag16`    |  17 | 2 |  34 | 131 071 |
| `wide32`   |  95 | 2 | 190 |      65 |
| `wide128`  | 383 | 2 | 766 |     257 |

Two everywhere: one pass to propagate costs, one to observe that nothing
changed. Even `tree400`, a 401-deep left chain, converges in two.

## Why two, and not depth-many

The scan runs `i` in `0..n`, and ids are allocated in construction order, so a
node's children almost always have lower ids than the node itself. A single
forward pass therefore costs children before parents and propagates the whole
chain in one sweep. The second pass is the termination check. Depth does not enter
into it. What would is a graph whose ids run counter to its dependency order,
which construction through `add` does not produce, since a node cannot be built
before its children exist. Merging can reorder representatives, but a
representative is one of the merged ids, so it cannot get ahead of the whole
chain.

This also means the theoretical worst case (O(n) passes) needs an id order that
`add` cannot generate.

## Verdict

The worklist would replace `2n` scan visits with an edge traversal plus queue
push/pop and a per-class "in queue" flag. At two passes there is nothing left to
recover (the scan *is* the propagation) and the queue maintenance would be new
cost. Rejected on the measurement, not on judgement.

Worth revisiting only if a workload appears whose pass count is not 2. The
`extractprobe` output above is the check to re-run; it prints the count directly.

## Reproduce

```bash
cd egraph
cargo run --release --example extractprobe
```
