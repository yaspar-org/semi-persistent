#!/bin/sh
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
# Each program must pass with the n-ary driver and fail without it.
# Usage: egraph/tests/mltl/rules/tests/run_nary_checks.sh PATH_TO_mltl_nary
set -u
B="$1"; here=$(dirname "$0"); status=0
for f in "$here"/nary_check_*.egg; do
  on=$("$B" "$f" >/dev/null 2>&1 && echo pass || echo fail)
  off=$(MLTL_NARY=none "$B" "$f" >/dev/null 2>&1 && echo pass || echo fail)
  echo "$(basename "$f"): with rules $on, without rules $off"
  [ "$on" = pass ] && [ "$off" = fail ] || status=1
done
exit $status
