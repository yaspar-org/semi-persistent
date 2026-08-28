#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Build the user-facing book and check the things `mdbook build` does not fail
# on. mdBook exits 0 when an `{{#include}}` names a missing file (it logs ERROR
# and renders the literal directive into the page) and says nothing at all when
# an include names a missing anchor. Both would ship a broken page, so this
# script owns those checks.

set -euo pipefail

book_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$book_dir/../.." && pwd)"
out="$book_dir/book"
log="$(mktemp)"
trap 'rm -f "$log"' EXIT

if ! command -v mdbook >/dev/null 2>&1; then
    printf 'error: mdbook is not on PATH (cargo install mdbook)\n' >&2
    exit 1
fi

failed=0
fail() { printf 'error: %s\n' "$1" >&2; failed=1; }

# ---------------------------------------------------------------- build

printf '==> mdbook build\n'
if ! mdbook build "$book_dir" 2>&1 | tee "$log"; then
    fail 'mdbook build exited non-zero'
fi

# A broken include is an ERROR line and a zero exit status, so grep for it.
if grep -q 'ERROR' "$log"; then
    grep 'ERROR' "$log" >&2
    fail 'mdbook logged ERROR (usually a missing {{#include}} target)'
fi

# ------------------------------------------------- unexpanded directives

printf '==> checking for unexpanded preprocessor directives\n'
if leftover="$(grep -rl '{{#' "$out" --include='*.html' 2>/dev/null)"; then
    printf '%s\n' "$leftover" >&2
    fail 'rendered HTML still contains {{# ... }}'
fi

# ------------------------------------------------------- include targets

# Every `{{#include path}}` and `{{#include path:anchor}}` in the sources must
# name a file that exists, and an anchor form must name an anchor that exists.
# The anchor case is the silent one: mdBook renders nothing and reports nothing.
printf '==> checking {{#include}} targets and anchors\n'
while IFS= read -r directive; do
    src_file="${directive%%$'\t'*}"
    spec="${directive#*$'\t'}"
    target="$book_dir/$(dirname "${src_file#"$book_dir/"}")/${spec%%:*}"
    if [[ ! -f "$target" ]]; then
        fail "$src_file includes ${spec%%:*}, which does not exist"
        continue
    fi
    if [[ "$spec" == *:* ]]; then
        anchor="${spec#*:}"
        # Line ranges are numeric; only named anchors need the ANCHOR check.
        if [[ ! "$anchor" =~ ^[0-9:]*$ ]] \
            && ! grep -q "ANCHOR:[[:space:]]*$anchor\b" "$target"; then
            fail "$src_file includes anchor '$anchor', absent from $target"
        fi
    fi
done < <(
    grep -rHo '{{#include [^}]*}}' "$book_dir/src" --include='*.md' \
        | sed -e 's/:{{#include /\t/' -e 's/}}$//' -e 's/[[:space:]]*$//' || true
)

# ------------------------------------------------------- repository links

# Chapters link to source files by their GitHub blob/tree URL. Those 404 unless
# the path is tracked, and a path that merely exists locally is exactly the case
# a local build would otherwise pass. Ask git, not the filesystem.
printf '==> checking repository links\n'
while IFS= read -r path; do
    [[ -n "$path" ]] || continue
    if ! git -C "$root" ls-files --error-unmatch -- "$path" >/dev/null 2>&1 \
        && ! git -C "$root" ls-files -- "$path" | read -r _; then
        fail "the book links to $path, which is not tracked by git"
    fi
done < <(
    grep -rho 'blob/main/[a-zA-Z0-9_./-]*\|tree/main/[a-zA-Z0-9_./-]*' \
        "$book_dir/src" --include='*.md' \
        | sed -e 's|blob/main/||' -e 's|tree/main/||' -e 's|)$||' \
        | sort -u || true
)

# ----------------------------------------------------------------- done

if (( failed )); then
    printf 'book build FAILED\n' >&2
    exit 1
fi
printf 'book build ok -> %s\n' "$out"
