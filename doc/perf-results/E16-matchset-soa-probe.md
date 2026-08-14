<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E16 — MatchSet (flat SoA) from the consumer's side — **postponed**

**Verdict: postponed. The flat store wins population by 10.5-14.3% but LOSES
the apply-pattern read by 1.5% at 1k matches and 10% at 16k; the combined
round trip favors it by ~6.5%, entirely from the producer side. That does
not justify rewiring `apply` while match storage is no measured bottleneck
(E2 already removed its allocation cost). Revisit if a workload is measured
to carry large per-query match sets where population dominates, or if a
column-order consumer (batched RHS instantiation over one variable at a
time) becomes real — that access pattern is the one this layout is shaped
for and the probe did not exercise it.**

The hypothesis was that `MatchSet` — the stride-packed flat storage that has
sat unused beside `MatchPool` since A2 — would pay off on the CONSUMER side:
`apply` reads every binding of every match, and one flat array per variable
kind should stream better than per-match slots of nine vectors each.

`benches/matchset_bench.rs`: both stores kept warm (`clear`, not drop;
`MatchSet` gained the `clear` it lacked), populated from the same pre-built
envs (4 node vars, 2 mults, one 10-element multiset rest), then read in
apply order — per match, every node and mult binding plus the rest-slice
walk, XOR/add sink.

| benchmark | MatchPool | MatchSet | set vs pool |
|---|---|---|---|
| 1024/populate | 14.24 µs | 12.75 µs | −10.5% |
| 1024/consume | 7.28 µs | 7.39 µs | +1.5% |
| 16384/populate | 235.0 µs | 201.3 µs | −14.3% |
| 16384/consume | 106.3 µs | 117.1 µs | +10.2% |

The population win is mechanical: one strided `extend` per field kind
against `clone_from` across nine vectors per slot. The consume LOSS at 16k
is the interesting half: the apply pattern is row-order, and a warm pool's
per-slot vectors keep each match's bindings and rest slice in a few small,
repeatedly-reused heap blocks, while the flat store walks strided spans
across a megabyte-scale shared pool. Row-order consumers do not want this
layout; column-order ones would, and none exists today.

Cross-arm caveat: pool and set are separate bench ids in one binary, so the
second-arm placement effect (11-layout-parity.md) applies to the absolute
gap; the sign of the 16k consume loss is well outside it, the 1.5% one is
not.
