# Domain registry status

`registry.rs` is the dynamic boundary between the e-graph and the statically
typed abstract domains. The carrier/value layer, core dispatch, and transfer
calls live in `verus!`: `Value::wf` carries the invariant of the selected
domain, `top` and `join` have concretization contracts, and `meet`, `reduce`,
constants, forward transfer, and backward `ite` dispatch only to verified
typed operations after checking those invariants.

The acceptance suite in `tests/registry.rs` checks the dynamic cases that the
typed contracts cannot enumerate in one sort: all registered names, carrier
widths, masked records, constants, malformed byte entries, `ite` refinement,
SMT-LIB zero-divisor behavior, and seeded exhaustive `u8` transfer coverage.

## Explicitly deferred boundary work

`encode` and `decode` remain ordinary Rust. Their implementation relies on
native `to_le_bytes`, `from_le_bytes`, and slice conversions, which the pinned
Verus standard-library model does not specify. The round-trip and outward
rounding properties are covered by the registry acceptance tests. They must
move under verified contracts when the byte-conversion specifications are
available; no `external_body`, `assume`, or `admit` was added.

Indexed casts (`extract`, `zero_extend`, and `sign_extend`) are rejected by
`op` until the surface API carries their indices. This prevents an output at
the wrong bit width. Their transfers, together with unimplemented domain
fields, remain conservative registry stubs: forward transfer returns the
correctly typed `Top` and backward transfer retains its operands. The
registry task assigns those precision improvements to the later domain and
surface-integration work.
