#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
# Gates on the Lean development, run after `lake build` from the project root:
#   1. no declaration uses `sorry` (checked in the sources and in the build log);
#   2. every `#print axioms` in the *Check.lean files reports only the standard
#      axioms propext, Classical.choice and Quot.sound, and every Check file
#      reports at least one declaration.
# Exit status is non-zero on the first failing gate; the offending lines are printed.
set -euo pipefail
cd "$(dirname "$0")/.."

allowed='propext|Classical\.choice|Quot\.sound'
fail=0

echo "gate 1: no sorry"
hits=$(grep -rn --include='*.lean' -E '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' SemperProofs \
  | grep -vE ':[0-9]+:[[:space:]]*(--|/-)' || true)
if [ -n "$hits" ]; then
  echo "::error::sorry in the sources:"
  echo "$hits"
  fail=1
fi
log=$(lake build 2>&1) || { echo "$log"; echo "::error::lake build failed"; exit 1; }
if echo "$log" | grep -q "declaration uses 'sorry'"; then
  echo "::error::lake build reports a declaration using sorry:"
  echo "$log" | grep "declaration uses 'sorry'"
  fail=1
fi

echo "gate 2: standard axioms only"
checks=$(find SemperProofs -name '*Check.lean' | sort)
if [ -z "$checks" ]; then
  echo "::error::no *Check.lean file found"
  exit 1
fi
for f in $checks; do
  out=$(lake env lean "$f" 2>&1) || { echo "$out"; echo "::error::$f failed to elaborate"; fail=1; continue; }
  lines=$(echo "$out" | grep "depends on axioms" || true)
  n=$(echo "$lines" | grep -c "depends on axioms" || true)
  if [ "$n" -eq 0 ]; then
    echo "::error::$f prints no axiom report"
    fail=1
    continue
  fi
  bad=$(echo "$lines" | sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' \
    | grep -vE "^($allowed)$" || true)
  if [ -n "$bad" ]; then
    echo "::error::$f depends on non-standard axioms:"
    echo "$lines" | grep -E "$(echo "$bad" | paste -sd'|' -)"
    fail=1
  else
    echo "  $f: $n declarations, standard axioms only"
  fi
done
exit $fail
