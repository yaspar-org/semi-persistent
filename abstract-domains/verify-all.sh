#!/bin/bash
set +e
# Find a timeout command (GNU `timeout` is named `gtimeout` on macOS via coreutils).
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
for mod in nats tnum anum bools tbit chopped exec_tnum div unum domains::d8 domains::d16 domains::d32 domains::d64; do
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
    echo "--- re-running $mod with --expand-errors ---"
    run_verus src/lib.rs --crate-type=lib --verify-module "$mod" --expand-errors 2>&1
    echo "--- end expand-errors for $mod ---"
    FAIL=1
  fi
done
exit $FAIL
