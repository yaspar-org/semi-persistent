#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "$root"

failed=0
while IFS=$'\t' read -r package manifest license; do
    package_dir="$(dirname "$manifest")"

    if [[ "$license" != "Apache-2.0" ]]; then
        printf 'error: %s declares license %q, expected Apache-2.0\n' \
            "$package" "$license" >&2
        failed=1
    fi

    for document in LICENSE CODE_OF_CONDUCT.md CONTRIBUTING.md SECURITY.md; do
        package_document="$package_dir/$document"
        if [[ ! -f "$package_document" ]]; then
            printf 'error: %s is missing %s\n' "$package" "$document" >&2
            failed=1
        elif ! cmp -s "$document" "$package_document"; then
            printf 'error: %s has a non-canonical %s\n' "$package" "$document" >&2
            failed=1
        fi
    done
done < <(
    cargo metadata --locked --no-deps --format-version 1 |
        jq -r '.packages[] | [.name, .manifest_path, (.license // "")] | @tsv'
)

for pattern in '*.rs' '*.py' '*.sh'; do
    while IFS= read -r source; do
        header="$(head -n 5 "$source")"
        if ! grep -Fq \
            'Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.' \
            <<<"$header"; then
            printf 'error: %s is missing the copyright header\n' "$source" >&2
            failed=1
        fi
        if ! grep -Fq 'SPDX-License-Identifier: Apache-2.0' <<<"$header"; then
            printf 'error: %s is missing the SPDX header\n' "$source" >&2
            failed=1
        fi
    done < <(git ls-files "$pattern")
done

exit "$failed"
