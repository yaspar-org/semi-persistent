#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Cross-engine process-level benchmark comparison against egglog.

The runner keeps two tables:

* ``<label>-samples.csv`` contains every timed invocation.
* ``<label>-results.csv`` contains one aggregate row per configuration.

``<label>-provenance.json`` binds those rows to exact binary SHA-256 hashes,
source snapshots, normalized commands, non-identifying machine metadata, and
the complete protocol.
"""

import argparse
import csv
import datetime
import glob
import hashlib
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
MANIFEST = os.path.join(ROOT, "egraph", "benches", "corpus.toml")
OUR_PROGRAMS = os.path.join(ROOT, "egraph", "tests", "egg", "bench")
THEIR_PROGRAMS = os.path.join(HERE, "programs")

SAMPLE_FIELDS = [
    "label",
    "benchmark",
    "engine",
    "encoding",
    "sample",
    "ms",
    "nodes",
    "classes",
    "iterations",
    "stats_status",
    "stats_source",
]
RESULT_FIELDS = [
    "label",
    "benchmark",
    "engine",
    "encoding",
    "samples",
    "ms",
    "min_ms",
    "max_ms",
    "mean_ms",
    "stdev_ms",
    "nodes",
    "classes",
    "iterations",
    "stats_status",
]


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def run_text(cmd, cwd=None):
    return subprocess.run(
        cmd, cwd=cwd, capture_output=True, text=True, check=True
    ).stdout.strip()


def load_manifest(path):
    """Load TOML, with a small fallback for Python before 3.11."""
    try:
        import tomllib

        with open(path, "rb") as f:
            return tomllib.load(f)
    except ImportError:
        pass

    data, table = {}, None
    with open(path, encoding="utf-8") as source:
        for raw in source:
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            if line.startswith("[") and line.endswith("]"):
                table = line[1:-1]
                node = data
                for part in table.split("."):
                    node = node.setdefault(part, {})
                continue
            key, _, value = line.partition("=")
            key, value = key.strip(), value.strip()
            if value.startswith("["):
                parsed = [
                    v.strip().strip('"') for v in value[1:-1].split(",") if v.strip()
                ]
            else:
                parsed = value.strip('"')
            node = data
            for part in table.split("."):
                node = node[part]
            node[key] = parsed
    return data


def install_egglog(rev, repo, into):
    src = os.path.join(into, "egglog")
    print(f"cloning {repo} into {src}", flush=True)
    subprocess.run(["git", "clone", "--quiet", repo, src], check=True)
    subprocess.run(["git", "-C", src, "checkout", "--quiet", rev], check=True)
    head = run_text(["git", "-C", src, "rev-parse", "HEAD"])
    print(f"building egglog at {head[:12]} (release)", flush=True)
    subprocess.run(["cargo", "build", "--release", "--quiet"], cwd=src, check=True)
    binary = os.path.join(src, "target", "release", "egglog")
    require_executable(binary)
    return binary, head, src


def verify_pinned(binary, rev):
    """Verify the checkout behind a reused egglog binary."""
    src = os.path.abspath(os.path.join(os.path.dirname(binary), "..", ".."))
    try:
        head = run_text(["git", "-C", src, "rev-parse", "HEAD"])
    except subprocess.CalledProcessError:
        sys.exit(f"{src} is not a git checkout; cannot verify the pinned revision")
    if not head.startswith(rev) and not rev.startswith(head[: len(rev)]):
        sys.exit(f"{src} is at {head[:12]}, manifest pins {rev}; refusing to record")
    return head, src


def build_ours():
    print("building our engine (release)", flush=True)
    subprocess.run(
        ["cargo", "build", "--release", "-p", "semi-persistent-egraph"],
        cwd=ROOT,
        check=True,
    )
    binary = os.path.join(ROOT, "target", "release", "semi-persistent")
    require_executable(binary)
    return binary


def require_executable(path):
    if not os.path.isfile(path):
        sys.exit(f"binary is missing: {path}")
    if not os.access(path, os.X_OK):
        sys.exit(f"binary is not executable: {path}")


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def command_version(cmd):
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired) as error:
        return f"unavailable: {error}"
    text = (proc.stdout or proc.stderr).strip()
    return text.splitlines()[0] if text else f"exit {proc.returncode}, no output"


def git_metadata(root):
    head = run_text(["git", "-C", root, "rev-parse", "HEAD"])
    diff = subprocess.run(
        ["git", "-C", root, "diff", "--binary", "--no-ext-diff", "HEAD"],
        capture_output=True,
        check=True,
    ).stdout
    return {
        "revision": head,
        "tracked_diff_sha256": hashlib.sha256(diff).hexdigest(),
    }


def binary_metadata(path, relation, source):
    stat = os.stat(path)
    return {
        "sha256": sha256_file(path),
        "size_bytes": stat.st_size,
        "source_relation": relation,
        "source": source,
    }


def normalize_command(cmd, ours, egglog, egglog_source, source_root=ROOT):
    """Retain a reproducible command shape without recording local paths."""
    exact = {
        os.path.realpath(ours): "<ours>",
        os.path.realpath(egglog): "<egglog>",
    }
    roots = (
        (os.path.realpath(source_root), "<source>"),
        (os.path.realpath(egglog_source), "<egglog-source>"),
    )
    normalized = []
    for arg in cmd:
        if not os.path.isabs(arg):
            normalized.append(arg)
            continue
        path = os.path.realpath(arg)
        if path in exact:
            normalized.append(exact[path])
            continue
        for root, alias in roots:
            if path.startswith(root + os.sep):
                relative = os.path.relpath(path, root).replace(os.sep, "/")
                normalized.append(f"{alias}/{relative}")
                break
        else:
            normalized.append(f"<absolute>/{os.path.basename(path)}")
    return normalized


NODES = re.compile(r"\bnodes?\b[^0-9]*([0-9]+)", re.I)
CLASSES = re.compile(r"\bclasses?\b[^0-9]*([0-9]+)", re.I)
ITERS = re.compile(r"\biterations?\b[^0-9]*([0-9]+)", re.I)
TOTAL = re.compile(r"^total[^0-9]*([0-9]+)", re.I | re.M)
EGGLOG_SIZE_ROW = re.compile(r"^\s*\(*[^()\s]+\s+([0-9]+)\)+\s*$")


def scrape_text(text):
    def one(pattern):
        match = pattern.search(text)
        return int(match.group(1)) if match else None

    nodes = one(NODES)
    if nodes is None:
        totals = TOTAL.findall(text)
        nodes = int(totals[-1]) if totals else None
    if nodes is None:
        # egglog's normal-mode `(print-stats)` starts with an s-expression
        # containing one `(function cardinality)` row per table. Its JSON
        # report contains timing/iteration data but not these cardinalities.
        # Some programs also print an `Overall statistics:` section and some
        # (for example acgen) print only the cardinality expression.
        prefix = text.split("Overall statistics:", 1)[0]
        rows = [
            int(match.group(1))
            for line in prefix.splitlines()
            if (match := EGGLOG_SIZE_ROW.match(line))
        ]
        nodes = sum(rows) if rows else None
    return {"nodes": nodes, "classes": one(CLASSES), "iterations": one(ITERS)}


def normalize_key(key):
    return re.sub(r"[^a-z0-9]", "", str(key).lower())


JSON_KEYS = {
    "nodes": {"nodes", "nodecount", "numnodes", "egraphnodes", "totalnodes"},
    "classes": {
        "classes",
        "classcount",
        "numclasses",
        "eclasses",
        "eclasscount",
    },
    "iterations": {
        "iterations",
        "iteration",
        "numiterations",
        "iters",
        "numiters",
    },
}


def collect_json_metrics(value, found):
    if isinstance(value, dict):
        for key, child in value.items():
            normalized = normalize_key(key)
            if normalized == "iterations" and isinstance(child, list):
                found["iterations"].append(len(child))
            for metric, aliases in JSON_KEYS.items():
                if normalized in aliases and isinstance(child, (int, float)):
                    found[metric].append(int(child))
            collect_json_metrics(child, found)
    elif isinstance(value, list):
        for child in value:
            collect_json_metrics(child, found)


def read_stats(run_dir, stdout, stderr):
    """Read generated JSON and text output without silently inventing metrics."""
    metrics = scrape_text(f"{stdout}\n{stderr}")
    sources = ["text"] if any(v is not None for v in metrics.values()) else []

    for path in sorted(glob.glob(os.path.join(run_dir, "*.stats.json"))):
        try:
            with open(path, encoding="utf-8") as source:
                value = json.load(source)
        except (OSError, json.JSONDecodeError) as error:
            sys.exit(f"cannot parse stats file {path}: {error}")
        found = {metric: [] for metric in JSON_KEYS}
        collect_json_metrics(value, found)
        for metric, values in found.items():
            if values:
                metrics[metric] = values[-1]
        sources.append(os.path.basename(path))

    missing = [name for name, value in metrics.items() if value is None]
    status = "complete" if not missing else "missing:" + ",".join(missing)
    return metrics, status, "+".join(sources) if sources else "unavailable"


def metrics_status(metrics):
    missing = [name for name, value in metrics.items() if value is None]
    return "complete" if not missing else "missing:" + ",".join(missing)


def remove_old_stats(run_dir):
    for path in glob.glob(os.path.join(run_dir, "*.stats.json")):
        os.unlink(path)


def run_checked(cmd, run_dir):
    remove_old_stats(run_dir)
    proc = subprocess.run(cmd, cwd=run_dir, capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit(
            f"command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"{proc.stdout}\n{proc.stderr}"
        )
    return proc


def time_run(
    cmd,
    runs,
    warmups,
    run_dir,
    require_stats,
    required_metrics,
    stats_probe_cmd=None,
):
    """Return every timed sample and its independently parsed statistics."""
    for _ in range(warmups):
        run_checked(cmd, run_dir)

    samples = []
    for sample_index in range(1, runs + 1):
        start = time.perf_counter_ns()
        proc = run_checked(cmd, run_dir)
        elapsed_ms = (time.perf_counter_ns() - start) / 1_000_000
        metrics, status, source = read_stats(run_dir, proc.stdout, proc.stderr)
        samples.append(
            {
                "sample": sample_index,
                "ms": elapsed_ms,
                **metrics,
                "stats_status": status,
                "stats_source": source,
            }
        )

    if stats_probe_cmd is not None:
        probe = run_checked(stats_probe_cmd, run_dir)
        probe_metrics, _, probe_source = read_stats(
            run_dir, probe.stdout, probe.stderr
        )
        for sample in samples:
            filled = []
            for metric, value in probe_metrics.items():
                if sample[metric] is None and value is not None:
                    sample[metric] = value
                    filled.append(metric)
            if filled:
                sample["stats_source"] += (
                    f"+untimed-probe[{','.join(filled)}]:{probe_source}"
                )
            sample["stats_status"] = metrics_status(sample)

    if require_stats:
        for sample in samples:
            missing = [
                metric for metric in required_metrics if sample[metric] is None
            ]
            if missing:
                sys.exit(
                    f"required statistics unavailable for {' '.join(cmd)}: "
                    f"missing:{','.join(missing)} "
                    f"(sources: {sample['stats_source']})"
                )
    return samples


def stable_metric(samples, metric):
    values = [sample[metric] for sample in samples]
    if any(value is None for value in values):
        return None
    return values[0] if all(value == values[0] for value in values) else None


def aggregate(label, benchmark, engine, encoding, samples):
    times = [sample["ms"] for sample in samples]
    statuses = sorted({sample["stats_status"] for sample in samples})
    metrics_stable = all(stable_metric(samples, metric) is not None for metric in JSON_KEYS)
    if len(statuses) == 1 and metrics_stable:
        stats_status = statuses[0]
    else:
        varying = [
            metric for metric in JSON_KEYS if stable_metric(samples, metric) is None
        ]
        stats_status = "varies-or-missing:" + ",".join(varying)
    return {
        "label": label,
        "benchmark": benchmark,
        "engine": engine,
        "encoding": encoding,
        "samples": len(samples),
        "ms": round(statistics.median(times), 3),
        "min_ms": round(min(times), 3),
        "max_ms": round(max(times), 3),
        "mean_ms": round(statistics.mean(times), 3),
        "stdev_ms": round(statistics.stdev(times), 3) if len(times) > 1 else 0.0,
        "nodes": stable_metric(samples, "nodes"),
        "classes": stable_metric(samples, "classes"),
        "iterations": stable_metric(samples, "iterations"),
        "stats_status": stats_status,
    }


def append_configuration(
    sample_rows,
    result_rows,
    label,
    benchmark,
    engine,
    encoding,
    samples,
):
    retained_samples = [
        {
            key: round(value, 3) if key == "ms" else value
            for key, value in sample.items()
        }
        for sample in samples
    ]
    for sample in retained_samples:
        sample_rows.append(
            {
                "label": label,
                "benchmark": benchmark,
                "engine": engine,
                "encoding": encoding,
                **sample,
            }
        )
    result_rows.append(
        aggregate(label, benchmark, engine, encoding, retained_samples)
    )


def write_csv(path, fields, rows):
    with open(path, "w", newline="", encoding="utf-8") as destination:
        writer = csv.DictWriter(
            destination, fieldnames=fields, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def report(rows, skipped):
    by = {}
    for row in rows:
        by.setdefault(row["benchmark"], {})[row["encoding"]] = row["ms"]
    encodings = sorted({row["encoding"] for row in rows if row["engine"] == "ours"})
    print(f"\n{'benchmark':22} {'egglog':>9} " + " ".join(f"{e:>14}" for e in encodings))
    ratios = {encoding: [] for encoding in encodings}
    for name in sorted(by):
        base = by[name].get("egglog")
        cells = []
        for encoding in encodings:
            ours = by[name].get(encoding)
            if base and ours:
                ratios[encoding].append(base / ours)
                cells.append(f"{ours:9.1f} ({base / ours:4.2f}x)")
            else:
                cells.append(" " * 14)
        print(f"{name:22} {base:9.1f} " + " ".join(cells))

    print("\ngeometric mean of egglog/ours (above 1 means we are faster):")
    for encoding in encodings:
        values = ratios[encoding]
        if values:
            print(
                f"  {encoding:16} {statistics.geometric_mean(values):5.2f}"
                f"  (n = {len(values)})"
            )
    if skipped:
        print("\nnot compared:")
        for name, entry in sorted(skipped.items()):
            print(f"  {name:22} {entry.get('blocked', 'no egglog counterpart')}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--label", default="compare")
    parser.add_argument("--runs", type=int, default=10)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--benchmark", action="append", default=None)
    parser.add_argument("--ours", default=None, help="skip building; use this binary")
    parser.add_argument(
        "--keep-egglog",
        default=None,
        help="reuse an egglog checkout instead of cloning; must be at the pinned rev",
    )
    parser.add_argument(
        "--require-stats",
        action="store_true",
        help=(
            "fail if engine-supported metrics cannot be parsed "
            "(egglog: nodes/iterations; ours: nodes/classes/iterations)"
        ),
    )
    parser.add_argument(
        "--out", default=os.path.join(ROOT, "doc", "benchmarks", "records")
    )
    args = parser.parse_args()
    if args.runs < 1 or args.warmups < 0:
        parser.error("--runs must be >= 1 and --warmups must be >= 0")

    started_at = utc_now()
    started_monotonic = time.monotonic()
    load_average_start = (
        list(os.getloadavg()) if hasattr(os, "getloadavg") else None
    )
    manifest = load_manifest(MANIFEST)
    pin = manifest["egglog"]
    entries = manifest["benchmarks"]
    subset = {
        name: entry
        for name, entry in entries.items()
        if entry.get("egglog") and not entry.get("blocked")
    }
    skipped = {name: entry for name, entry in entries.items() if name not in subset}
    if args.benchmark:
        selected = set(args.benchmark)
        subset = {name: entry for name, entry in subset.items() if name in selected}
        if not subset:
            sys.exit("no comparable benchmark matched --benchmark")

    ours_built = args.ours is None
    ours = os.path.abspath(args.ours) if args.ours else build_ours()
    require_executable(ours)
    ours_source = git_metadata(ROOT)

    temp_checkout = None
    if args.keep_egglog:
        egglog = os.path.join(
            os.path.abspath(args.keep_egglog), "target", "release", "egglog"
        )
        require_executable(egglog)
        egglog_head, egglog_src = verify_pinned(egglog, pin["rev"])
    else:
        temp_checkout = tempfile.mkdtemp(prefix="egglog-compare-")
        egglog, egglog_head, egglog_src = install_egglog(
            pin["rev"], pin["repo"], temp_checkout
        )
    egglog_source = git_metadata(egglog_src)

    binaries = {
        "ours": binary_metadata(
            ours,
            "built by this runner from the recorded source snapshot"
            if ours_built
            else "provided via --ours; source identity is the binary hash",
            ours_source,
        ),
        "egglog": binary_metadata(
            egglog,
            "built from/reused at the manifest-pinned checkout",
            egglog_source,
        ),
    }

    sample_rows = []
    result_rows = []
    commands = {}
    run_root = tempfile.mkdtemp(prefix=f"egglog-{args.label}-runs-")
    try:
        for name in sorted(subset):
            entry = subset[name]
            their_file = os.path.join(THEIR_PROGRAMS, entry["egglog"])
            config_dir = os.path.join(run_root, name, "egglog")
            os.makedirs(config_dir)
            cmd = [egglog, "-j", "1", "--mode", "no-messages", their_file]
            commands[f"{name}/egglog"] = normalize_command(
                cmd, ours, egglog, egglog_src
            )
            stats_probe_cmd = [egglog, "-j", "1", their_file]
            commands[f"{name}/egglog-stats-probe-untimed"] = normalize_command(
                stats_probe_cmd, ours, egglog, egglog_src
            )
            samples = time_run(
                cmd,
                args.runs,
                args.warmups,
                config_dir,
                args.require_stats,
                ("nodes", "iterations"),
                stats_probe_cmd,
            )
            append_configuration(
                sample_rows,
                result_rows,
                args.label,
                name,
                "egglog",
                "egglog",
                samples,
            )
            median = result_rows[-1]["ms"]
            print(
                f"{name:22} egglog          {median:9.1f} ms "
                f"[{result_rows[-1]['stats_status']}]",
                flush=True,
            )

            for encoding in entry["encodings"]:
                our_file = os.path.join(OUR_PROGRAMS, f"{name}.{encoding}.egg")
                if not os.path.exists(our_file):
                    sys.exit(
                        f"{name}: manifest lists {encoding} but {our_file} is missing"
                    )
                for strategy, flag in (
                    ("naive", "--use-naive"),
                    ("semi", "--use-semi-naive"),
                ):
                    encoded = f"{encoding}-{strategy}"
                    config_dir = os.path.join(run_root, name, encoded)
                    os.makedirs(config_dir)
                    cmd = [ours, our_file, "--types", entry["types"], flag]
                    commands[f"{name}/{encoded}"] = normalize_command(
                        cmd, ours, egglog, egglog_src
                    )
                    samples = time_run(
                        cmd,
                        args.runs,
                        args.warmups,
                        config_dir,
                        args.require_stats,
                        ("nodes", "classes", "iterations"),
                    )
                    append_configuration(
                        sample_rows,
                        result_rows,
                        args.label,
                        name,
                        "ours",
                        encoded,
                        samples,
                    )
                    median = result_rows[-1]["ms"]
                    print(
                        f"{name:22} {encoded:15} {median:9.1f} ms "
                        f"[{result_rows[-1]['stats_status']}]",
                        flush=True,
                    )
    finally:
        shutil.rmtree(run_root, ignore_errors=True)
        if temp_checkout:
            shutil.rmtree(temp_checkout, ignore_errors=True)

    os.makedirs(args.out, exist_ok=True)
    samples_path = os.path.join(args.out, f"{args.label}-samples.csv")
    results_path = os.path.join(args.out, f"{args.label}-results.csv")
    provenance_path = os.path.join(args.out, f"{args.label}-provenance.json")
    write_csv(samples_path, SAMPLE_FIELDS, sample_rows)
    write_csv(results_path, RESULT_FIELDS, result_rows)

    provenance = {
        "schema": "semi-persistent-benchmark-provenance-v3",
        "label": args.label,
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started_monotonic, 3),
        "protocol": {
            "runs": args.runs,
            "warmups": args.warmups,
            "timing": "process wall clock via time.perf_counter_ns",
            "egglog_threads": 1,
            "require_stats": args.require_stats,
            "required_statistics": {
                "egglog": ["nodes", "iterations"],
                "ours": ["nodes", "classes", "iterations"],
            },
            "statistics_note": (
                "egglog 7b1adf2 does not report e-class counts; one normal-mode "
                "stats probe per benchmark is excluded from timings"
            ),
            "raw_samples_file": os.path.basename(samples_path),
            "aggregate_file": os.path.basename(results_path),
        },
        "machine": {
            "platform": platform.platform(),
            "system": platform.system(),
            "release": platform.release(),
            "version": platform.version(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "cpu_count": os.cpu_count(),
            "load_average_start": load_average_start,
        },
        "tools": {
            "python": sys.version,
            "rustc": command_version(["rustc", "--version", "--verbose"]),
            "cargo": command_version(["cargo", "--version"]),
        },
        "binaries": binaries,
        "egglog_pin": pin,
        "benchmarks": sorted(subset),
        "skipped": {
            name: entry.get("blocked", "no egglog counterpart")
            for name, entry in skipped.items()
        },
        "commands": commands,
    }
    with open(provenance_path, "w", encoding="utf-8") as destination:
        json.dump(provenance, destination, indent=2)
        destination.write("\n")

    report(result_rows, skipped)
    print(
        f"\nwrote {samples_path}\nwrote {results_path}\nwrote {provenance_path}"
    )


if __name__ == "__main__":
    main()
