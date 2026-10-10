#!/bin/sh
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
# Each program must pass with the declarative n-ary rules and fail without them.
# The rules are the collection rules of ../mltl_nary_decl.egg, inserted before
# the program's first `let`, after its declarations.
# Usage: egraph/tests/mltl/rules/tests/run_nary_decl_checks.sh PATH_TO_semi-persistent
# Scratch files go under $WORK, or the current directory, never /tmp.
set -u
B="$1"; here=$(dirname "$0"); status=0
scratch=$(mktemp -d "${WORK:-.}/nary_decl.XXXXXX"); rules="$scratch/rules.egg"; prog="$scratch/prog.egg"
sed -n '/^; --- n-ary collection rules/,$p' "$here/../mltl_nary_decl.egg" > "$rules"
for f in "$here"/nary_check_*.egg; do
  awk -v R="$rules" '/^\(let / && !done {while ((getline l < R) > 0) print l; done=1} {print}' "$f" > "$prog"
  on=$("$B" "$prog" --types machine >/dev/null 2>&1 && echo pass || echo fail)
  off=$("$B" "$f" --types machine >/dev/null 2>&1 && echo pass || echo fail)
  echo "$(basename "$f"): with rules $on, without rules $off"
  [ "$on" = pass ] && [ "$off" = fail ] || status=1
done
rm -rf "$scratch"
exit $status
