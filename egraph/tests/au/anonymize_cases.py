#!/usr/bin/env python3
"""Anonymize AU fixture records deterministically.

Input: JSON array. Each record must contain `symbols` (the variable names to anonymize)
and may contain nested strings/lists/dicts. Symbol assignment is per record, ordered by
first token occurrence in the record's `term1`, `term2`, `expression`, and `expected*`
fields, then by the remaining `symbols` list. The same source symbol always maps to the
same vN within the record; maps never cross record boundaries.

The output omits `symbols` and never records the source→anonymous map.
"""
from __future__ import annotations

import argparse
import copy
import json
import re
import sys
from pathlib import Path
from typing import Any

TOKEN = re.compile(r"(?<![A-Za-z0-9_])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_])")
PRIMARY_TEXT_KEYS = ("declarations", "term1", "term2", "expression")


def _strings(value: Any):
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from _strings(item)
    elif isinstance(value, dict):
        for key in value:  # JSON insertion order is part of the fixture format.
            yield from _strings(value[key])


def stable_symbol_map(record: dict[str, Any]) -> dict[str, str]:
    symbols = list(dict.fromkeys(record.get("symbols", [])))
    symbol_set = set(symbols)
    ordered: list[str] = []
    text_keys = list(PRIMARY_TEXT_KEYS)
    text_keys.extend(
        key for key in record
        if key.startswith("expected") and key not in text_keys
    )
    for key in text_keys:
        if key not in record:
            continue
        for text in _strings(record[key]):
            for match in TOKEN.finditer(text):
                name = match.group(1)
                if name in symbol_set and name not in ordered:
                    ordered.append(name)
    ordered.extend(name for name in symbols if name not in ordered)
    return {name: f"v{i}" for i, name in enumerate(ordered, 1)}


def _replace(value: Any, mapping: dict[str, str]) -> Any:
    if isinstance(value, str):
        return TOKEN.sub(lambda m: mapping.get(m.group(1), m.group(1)), value)
    if isinstance(value, list):
        return [_replace(item, mapping) for item in value]
    if isinstance(value, dict):
        return {key: _replace(item, mapping) for key, item in value.items()}
    return value


def anonymize_record(record: dict[str, Any]) -> dict[str, Any]:
    mapping = stable_symbol_map(record)
    result = _replace(copy.deepcopy(record), mapping)
    result.pop("symbols", None)
    result["variables"] = [mapping[name] for name in mapping]
    return result


def anonymize(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [anonymize_record(record) for record in records]


def self_test() -> None:
    records = [
        {
            "id": "example_1",
            "symbols": ["left_name", "right_name", "unused_name"],
            "term1": "(+ left_name right_name)",
            "term2": "(+ right_name left_name)",
            "expected": "(pair left_name right_name)",
        },
        {
            "id": "example_2",
            "symbols": ["right_name", "left_name"],
            "term1": "left_name",
            "term2": "right_name",
        },
        {
            "id": "example_3",
            "symbols": ["later_name", "first_name"],
            "expected_left": "first_name later_name",
        },
    ]
    out = anonymize(records)
    assert out[0]["term1"] == "(+ v1 v2)"
    assert out[0]["term2"] == "(+ v2 v1)"
    assert out[0]["expected"] == "(pair v1 v2)"
    assert out[0]["variables"] == ["v1", "v2", "v3"]
    # Mapping is independent per record and follows first textual occurrence.
    assert out[1]["term1"] == "v1"
    assert out[1]["term2"] == "v2"
    assert out[1]["variables"] == ["v1", "v2"]
    # Every expected* field participates in first-occurrence ordering.
    assert out[2]["expected_left"] == "v1 v2"
    assert out[2]["variables"] == ["v1", "v2"]
    # Deterministic byte-for-byte.
    assert json.dumps(out, sort_keys=True) == json.dumps(anonymize(records), sort_keys=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", nargs="?", type=Path)
    ap.add_argument("output", nargs="?", type=Path)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        print("ok")
        return 0
    if args.input is None or args.output is None:
        ap.error("input and output are required unless --self-test is used")
    records = json.loads(args.input.read_text())
    if not isinstance(records, list) or not all(isinstance(x, dict) for x in records):
        raise ValueError("input must be a JSON array of objects")
    args.output.write_text(json.dumps(anonymize(records), indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
