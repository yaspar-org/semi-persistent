#!/bin/bash
# Per-module Verus driver. Mirrors abstract-domains/verify-all.sh.
set +e

if command -v timeout >/dev/null 2>&1; then
  TIMEOUT=timeout
elif command -v gtimeout >/dev/null 2>&1; then
  TIMEOUT=gtimeout
else
  TIMEOUT=""
fi

# `hasher_spec` names `foldhash` (the production hasher `Map` is specified
# against), so `verus src/lib.rs` has to be told where that crate's artifacts
# are — cargo normally supplies `--extern`, and without it every module fails at
# resolution with "unresolved module or unlinked crate `foldhash`", which reads
# like a proof failure but is a link-path failure. Build the lib first so the
# artifacts exist, then point Verus at the newest `rlib` (cargo also emits
# `.rmeta`-only entries for check builds, which Verus cannot use).
DEPS=$(cd "$(dirname "$0")/.." && pwd)/target/release/deps
cargo build --release -p semi-persistent-containers-verus --lib >/dev/null 2>&1
FOLDHASH=$(ls -t "$DEPS"/libfoldhash-*.rlib 2>/dev/null | head -1)
if [ -z "$FOLDHASH" ]; then
  echo "no libfoldhash-*.rlib under $DEPS — run 'cargo build --release' first" >&2
  exit 1
fi
EXTERNS=(--extern "foldhash=$FOLDHASH" -L "dependency=$DEPS")

run_verus() {
  if [ -n "$TIMEOUT" ]; then
    $TIMEOUT 600 verus --trace "$@" "${EXTERNS[@]}"
  else
    verus --trace "$@" "${EXTERNS[@]}"
  fi
}

FAIL=0
# Modules are added here as their bodies land. Empty `verus! {}` blocks are
# erased by the macro and become invisible to `--verify-module`, so listing a
# stub-only module here would fail.
for mod in guard tagged index_like dense_id diff_store capture_bits parallel_store inline_store frame opt container_id fork_history vec append_only_vec map sparse_set list circular_list bplus bplus_layout bplus_search bplus_tree sorted_vec_cursor id_factory id_macros::id_witnesses::StoredWitnessId7 id_macros::id_witnesses::StoredWitnessId15 id_macros::id_witnesses::StoredWitnessId31 id_macros::id_witnesses::StoredWitnessId63 id_macros::ids::StoredSparseSetId id_macros::ids::StoredUseListId id_macros::ids::StoredUseNodeId; do
  printf "%-20s " "$mod:"
  output=$(run_verus src/lib.rs --crate-type=lib --verify-module "$mod" 2>&1)
  status=$?
  result=$(echo "$output" | grep "verification results" | head -1)
  if [ $status -eq 124 ]; then
    echo "TIMEOUT"
    FAIL=1
  elif [ -z "$result" ]; then
    echo "ERROR (exit $status)"
    echo "$output" | tail -20
    FAIL=1
  elif echo "$result" | grep -q "0 errors"; then
    echo "$result"
  else
    echo "FAIL: $result"
    echo "--- full output for $mod ---"
    echo "$output"
    echo "--- end output for $mod ---"
    FAIL=1
  fi
done
exit $FAIL
