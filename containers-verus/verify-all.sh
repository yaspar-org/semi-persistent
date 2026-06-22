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

run_verus() {
  if [ -n "$TIMEOUT" ]; then
    $TIMEOUT 600 verus --trace "$@"
  else
    verus --trace "$@"
  fi
}

FAIL=0
# Modules are added here as their bodies land. Empty `verus! {}` blocks are
# erased by the macro and become invisible to `--verify-module`, so listing a
# stub-only module here would fail.
for mod in tagged index_like dense_id diff_store capture_bits parallel_store inline_store frame opt container_id fork_history vec append_only_vec map sparse_set list circular_list bplus bplus_layout bplus_search bplus_tree; do
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
