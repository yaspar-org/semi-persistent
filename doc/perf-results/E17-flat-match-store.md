<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E17: MatchPool stores its matches in the flat MatchSet: **accepted**

**Verdict: accepted, on every workload that emits matches: plain7 −14.6% /
−7.8%, ac10 −13.8% / −12.6%, ac6 −10.7% / −9.7% against the post-E15
baseline. ac10/naive allocations fall 64% (373 499 → 136 096, 1.36 → 0.49
per step) and peak live bytes fall 64% (39.2 MB → 14.2 MB). The
completion-only workloads (+1.0 to +1.6%, zero matches) are placement
movement, not mechanism. Workspace 1334/0, clippy 0.**

## The attribution that reopened E16

E16 postponed the flat store because the apply-order READ was slower and
nothing showed match storage mattered. The per-workload attribution run
changed that: counters showed every remaining step-proportional allocation
class was `MatchPool`'s fresh-slot arm (`slots.push(env.clone())`) firing
exactly the pool's high-water per workload: 76 320 slots on ac10/naive,
20 505 on plain7/naive, each slot allocating ~5 vectors. `clone_from`
recycling only pays off at steady state; a saturation whose rounds grow
monotonically pushes past the high-water again and again, so the "one-time"
population cost is the dominant remaining allocator. Population is
precisely the side E16 measured the flat store winning by 10.5-14.3%.

## The change

`MatchPool` keeps its name, its API role, and its E14 loan buffers, but
stores matches in a `MatchSet` (which gains the `lit_vals` column it
lacked, `empty()`, and `reshape`, adopting a query's strides while keeping
every flat allocation, so one warm store serves differently-shaped rules
across a saturation). `run_query_into` reshapes instead of clearing.

The apply loop reads rows in place: a `MatchView` trait (reads of every
variable kind plus the two scalar writes RHS comprehensions perform, and
`clear`) is implemented by the in-progress `Match` and by `MatchRow`, and
`apply_action`/`eval`/`eval_arg` are generic over it. On the owned `Match`,
`clear` restores the panic-on-read guard; the flat store holds no unbound
state, so a row's `clear` leaves the stale value, equivalent for every
compiled action sequence, which sets a comprehension variable before each
read.

E16's read regression (+10% at 16k in isolation) is visible nowhere in the
end-to-end numbers: each match is read once against pushes that no longer
allocate, and the population win plus the removed allocator traffic
dominate on every match-emitting workload.

## Numbers

`saturate_bench` vs baseline `post-e15` (stash/baseline/pop, exact):

| benchmark | change |
|---|---|
| plain7/naive | −14.6% |
| plain7/semi | −7.8% |
| ac6/naive | −10.7% |
| ac6/semi | −9.7% |
| ac10/naive | −13.8% |
| ac10/semi | −12.6% |
| accompl32 / accompl64 | +1.6% / +1.0% (zero matches; placement) |

allocprobe: ac10/naive 136 096 allocations (0.49/step), peak 14.2 MB;
plain7/semi 9 299 (0.08/step), peak 0.93 MB. Node counts identical on every
workload; 917 e-graph tests and the full workspace pass unchanged.

Cumulative since the verified-aggregate swap (E15 + E17): ac10/naive
52.0 → 44.3 ms on top of E15's −21.5%, roughly −34% end to end on the
heaviest AC workload, and plain rewrite workloads double-digit down with
peak memory roughly a third of where the day started.
