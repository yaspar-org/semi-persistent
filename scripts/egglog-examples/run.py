#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Validate the finite egglog example corpus; this is not a timing harness."""

import argparse
from collections import Counter
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
REVISION = "593df10e1465904e8b7a3dc85d8ef3976842b509"
MODES = ("naive", "semi-naive")
ARMS = {("egglog", "original"), ("egglog", "encoded"), ("ours", "encoded")}


def digest(path):
    sha = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            sha.update(chunk)
    return sha.hexdigest()


def checked_path(root, relative, expected_hash):
    path = (root / relative).resolve()
    if Path(relative).is_absolute() or not path.is_relative_to(root.resolve()):
        raise ValueError(f"path outside corpus: {relative}")
    if not path.is_file() or digest(path) != expected_hash:
        raise ValueError(f"missing file or SHA-256 mismatch: {relative}")
    return path


def validate_oracles(program):
    for field in ("stdout_contains", "stderr_contains"):
        value = program.get(field, [])
        if not isinstance(value, list) or not all(
            isinstance(text, str) and text for text in value
        ):
            raise ValueError(f"{field} must be a list of nonempty strings")
    if program["expected"] != "pass" and not program.get("stderr_contains"):
        raise ValueError("failure needs a diagnostic oracle")


def load_examples(root=ROOT):
    examples = []
    seen_ids, seen_sources = set(), set()
    for manifest in sorted((root / "manifests").glob("*.json")):
        data = json.loads(manifest.read_text())
        if data["upstream_revision"] != REVISION:
            raise ValueError(f"unexpected source revision: {manifest.name}")
        for example in data["examples"]:
            key = f"{data['group']}/{example['id']}"
            if not re.fullmatch(r"[a-z0-9_-]+/[a-z0-9_-]+", key):
                raise ValueError(f"invalid example id: {key}")
            source = example["source"]
            if key in seen_ids or source["path"] in seen_sources:
                raise ValueError(f"duplicate example/source: {key}")
            seen_ids.add(key)
            seen_sources.add(source["path"])
            checked_path(root, source["vendored_path"], source["sha256"])
            expected_url = (
                f"https://github.com/egraphs-good/egglog/blob/{REVISION}/{source['path']}"
            )
            if source["url"] != expected_url:
                raise ValueError(f"source URL does not match pin: {key}")
            if example["classification"] != "finite-example":
                raise ValueError(f"unexpected scope: {key}")
            if not example["adaptations"] or not example["limitations"]:
                raise ValueError(f"missing scope notes: {key}")
            case_ids = set()
            source_cases = 0
            for case in example["cases"]:
                if case["id"] in case_ids or not re.fullmatch(
                    r"[a-zA-Z0-9_-]+", case["id"]
                ):
                    raise ValueError(f"duplicate/invalid case: {key}/{case['id']}")
                case_ids.add(case["id"])
                if case["kind"] not in {"source", "validation", "control"}:
                    raise ValueError(f"unknown case kind: {key}/{case['id']}")
                source_cases += case["kind"] == "source"
                arms = set()
                for program in case["programs"]:
                    arm = (program["engine"], program["arm"])
                    if arm not in ARMS or arm in arms:
                        raise ValueError(f"invalid/duplicate arm: {key}/{case['id']}")
                    arms.add(arm)
                    checked_path(root, program["path"], program["sha256"])
                    expected = program["expected"]
                    if expected not in {"pass", "check_failure", "runtime_failure"}:
                        raise ValueError(f"unknown expectation: {expected}")
                    validate_oracles(program)
                    if case["kind"] == "source" and expected != "pass":
                        raise ValueError(f"source arm must succeed: {key}")
                if case["kind"] == "source" and arms != ARMS:
                    raise ValueError(f"source needs all three arms: {key}")
            if source_cases != 1:
                raise ValueError(f"expected one source case: {key}")
            examples.append(dict(example, group=data["group"], key=key))
    if not examples:
        raise ValueError("no manifests found")
    return examples


def command(binary, program, mode):
    flags = (
        ["--types", "machine", "--use-" + mode]
        if program["engine"] == "ours"
        else (["--naive"] if mode == "naive" else [])
    )
    return [str(binary), *flags, program["path"]]


def stop_process(process):
    """Kill/reap our child and its process group, including on interruption."""
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        elif process.poll() is None:
            process.kill()
    except ProcessLookupError:
        pass
    finally:
        process.wait()


def execute(argv, cwd, stdout_path, stderr_path, timeout, output_limit):
    started = time.monotonic()
    stop = None
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(
            argv, cwd=cwd, stdout=stdout, stderr=stderr,
            start_new_session=os.name == "posix",
        )
        try:
            while process.poll() is None:
                if time.monotonic() - started >= timeout:
                    stop = "timeout"
                    break
                if stdout_path.stat().st_size + stderr_path.stat().st_size > output_limit:
                    stop = "output_limit"
                    break
                time.sleep(0.02)
        finally:
            stop_process(process)
    if stdout_path.stat().st_size + stderr_path.stat().st_size > output_limit:
        stop = "output_limit"
    return {
        "returncode": process.returncode,
        "stop": stop,
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def assess(program, execution, stdout, stderr):
    """A timeout, crash or unrelated parser error cannot pass a negative control."""
    if execution["stop"]:
        return execution["stop"]
    code = execution["returncode"]
    if code < 0:
        return f"terminated by signal {-code}"
    expected_code = 0 if program["expected"] == "pass" else 1
    if code != expected_code:
        return f"expected exit {expected_code}, got {code}"
    for field, text in (("stdout_contains", stdout), ("stderr_contains", stderr)):
        for required in program.get(field, []):
            if required not in text:
                return f"missing {field} fragment: {required!r}"
    return None


def find_binary(value):
    found = shutil.which(value)
    path = Path(found or value).resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise ValueError(f"executable not found: {value}")
    return path


def terminate(signum, _frame):
    # Raising rather than exiting immediately preserves the cleanup/finally blocks.
    raise SystemExit(128 + signum)


def main():
    signal.signal(signal.SIGTERM, terminate)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify manifests/hashes only")
    parser.add_argument("--ours", default=str(ROOT.parents[1] / "target/release/semi-persistent"))
    parser.add_argument("--egglog", help="optional pinned egglog binary; enables all three arms")
    parser.add_argument("--group", action="append", help="select a group (repeatable)")
    parser.add_argument("--example", action="append", help="select group/id (repeatable)")
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--timeout", type=float, default=30.0, help="wall seconds per process")
    parser.add_argument("--output-limit-mib", type=float, default=8.0)
    parser.add_argument("--output", type=Path, help="new directory for results and logs")
    args = parser.parse_args()
    try:
        examples = load_examples()
        total = len(examples)
        for selected, available, label in (
            (args.group, {e["group"] for e in examples}, "group"),
            (args.example, {e["key"] for e in examples}, "example"),
        ):
            if selected and set(selected) - available:
                raise ValueError(f"unknown {label}: {sorted(set(selected) - available)}")
        examples = [
            e for e in examples
            if (not args.group or e["group"] in args.group)
            and (not args.example or e["key"] in args.example)
        ]
        if not examples:
            raise ValueError("selection contains no examples")
        print(f"Verified {total} example manifests and file hashes; selected {len(examples)}.")
        if args.check:
            return 0
        if not args.output:
            raise ValueError("--output must name a new results directory")
        if not all(
            math.isfinite(v) and v > 0 for v in (args.timeout, args.output_limit_mib)
        ):
            raise ValueError("resource limits must be finite and positive")
        binaries = {"ours": find_binary(args.ours)}
        if args.egglog:
            binaries["egglog"] = find_binary(args.egglog)
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
        results = {
            "schema_version": 1,
            "egglog_source_revision": REVISION,
            "runner_sha256": digest(Path(__file__)),
            "binaries": {
                engine: {"name": path.name, "sha256": digest(path)}
                for engine, path in binaries.items()
            },
            "manifests": {
                p.name: digest(p) for p in sorted((ROOT / "manifests").glob("*.json"))
            },
            "selected_examples": [e["key"] for e in examples],
            "modes": MODES,
            "timeout_seconds": args.timeout,
            "output_limit_mib": args.output_limit_mib,
            "note": "Validation only. Elapsed times are watchdog diagnostics, not benchmarks.",
            "planned_processes": sum(
                len(MODES)
                for e in examples for c in e["cases"] for p in c["programs"]
                if p["engine"] in binaries and (not args.source_only or c["kind"] == "source")
            ),
            "complete": False,
            "runs": [],
        }
        report = output / "results.json"
        try:
            for example in examples:
                count_before = len(results["runs"])
                for case in example["cases"]:
                    if args.source_only and case["kind"] != "source":
                        continue
                    for program in case["programs"]:
                        if program["engine"] not in binaries:
                            continue
                        for mode in MODES:
                            # Each mode is a separate invocation. Detect edits between runs.
                            checked_path(ROOT, program["path"], program["sha256"])
                            binary = binaries[program["engine"]]
                            if digest(binary) != results["binaries"][program["engine"]]["sha256"]:
                                raise ValueError(f"binary changed during run: {binary.name}")
                            key = (
                                f"{example['key']}/{case['id']}/"
                                f"{program['engine']}-{program['arm']}-{mode}"
                            )
                            log_base = output / key
                            log_base.parent.mkdir(parents=True, exist_ok=True)
                            stdout_path = log_base.with_suffix(".stdout")
                            stderr_path = log_base.with_suffix(".stderr")
                            execution = execute(
                                command(binary, program, mode),
                                ROOT, stdout_path, stderr_path, args.timeout,
                                args.output_limit_mib * 1024 * 1024,
                            )
                            # Never read unbounded child output into the parent.
                            limit = int(args.output_limit_mib * 1024 * 1024) + 1
                            with stdout_path.open("rb") as stream:
                                stdout = stream.read(limit).decode(errors="replace")
                            with stderr_path.open("rb") as stream:
                                stderr = stream.read(limit).decode(errors="replace")
                            failure = assess(program, execution, stdout, stderr)
                            results["runs"].append({
                                "id": key, "example": example["key"], "case": case["id"],
                                "kind": case["kind"], "engine": program["engine"],
                                "arm": program["arm"], "mode": mode,
                                "program": program["path"], "sha256": program["sha256"],
                                "expected": program["expected"], **execution,
                                "ok": failure is None, "failure": failure,
                                "stdout": str(stdout_path.relative_to(output)),
                                "stderr": str(stderr_path.relative_to(output)),
                            })
                            if failure:
                                print(f"FAIL {key}: {failure}", flush=True)
                new = results["runs"][count_before:]
                print(
                    f"{example['key']}: {sum(r['ok'] for r in new)}/{len(new)} "
                    "expected outcomes", flush=True,
                )
            results["complete"] = True
        finally:
            results["summary"] = {
                "processes": len(results["runs"]),
                "matched_expectations": sum(r["ok"] for r in results["runs"]),
                "expected_outcomes": dict(Counter(r["expected"] for r in results["runs"])),
            }
            report.write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results["summary"], sort_keys=True))
        return int(not results["complete"] or any(not r["ok"] for r in results["runs"]))
    except (OSError, ValueError, KeyError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("Interrupted; completed results retained.", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
