import SemperProofs.Fidelity.Index
import SemperProofs.Fidelity.Subsume
import SemperProofs.Fidelity.ByOpPolicy
import SemperProofs.Fidelity.Normalize
import SemperProofs.Fidelity.Recanon
import SemperProofs.Fidelity.NormalizeSat
import SemperProofs.Fidelity.Sound

/-!
# Fidelity rows closed against the engine

The ledger `fidelity-ledger.md` lists, per engine behavior, how the Lean
model relates to the Rust code. The files here close the rows where the
model assumed more than the engine does:

* `Index`: the index is a filter on the store by the three skip predicates
  of `index.rs:521-537`; the join theorems restated (`matches_index_iff`).
* `Subsume`: saturation with `:subsume` runs, consequences read on the store
  (`saturation_complete_store`).
* `ByOpPolicy`: the `ByOp` placement policy as a parameter
  (`policy_candidates_eq`).
* `Normalize`, `NormalizeSat`: right-hand sides present as `add`'s normal
  forms (`DenN`, `fired_after_actions_N`, `saturation_complete_N`,
  `den_misses_single`).
* `Recanon`: recanonicalization as the laws apply it (`StorePersistN`: a
  unit drop, a count clamp or a degenerate arity at rebuild), under which
  n-ary right-hand sides need not persist (`denN_persist_fails`); the
  saturation theorems route the rules that build them naive after such a
  round.
* `Sound`: what the actions build denotes the right-hand side in every model
  (`denN_sound`, `firedN_sound`, `union_recorded_sound`).
-/
