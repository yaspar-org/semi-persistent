#!/usr/bin/env python3
"""Process-level timing harness for the add-ac width-scaling sweep.

Runs every (n, config) pair 1 warmup + 5 timed runs, records wall time per run, and
collects node and iteration counts from the engines' own machine-readable statistics.
Writes addac-sweep.csv next to this script.

A configuration that cannot reach its goal within the budget is recorded as DNF at that
n, with its one demonstration run's wall time kept and its iteration column set to DNF.

Usage:
    python3 run-addac-sweep.py [--runs 5] [--warmups 1] [--timeout 180]
        [--ours PATH] [--egglog PATH] [-n 7 -n 9 ...]
"""

import argparse
import csv
import json
import os
import re
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))

WIDTHS = [7, 9, 11, 13, 15, 17, 20]


def configs(ours, egglog, n):
    """(config name, argv, stats file, flavour) for each configuration at width n."""
    yield ("egglog",
           [egglog, "-j", "1", "--mode", "no-messages", f"addac-n{n}.egglog.egg"],
           f"addac-n{n}.egglog.stats.json", "egglog")
    for enc in ("rules", "native"):
        yield (f"ours-{enc}",
               [ours, f"addac-n{n}.{enc}.egg", "--types", "machine"],
               f"addac-n{n}.{enc}.stats.json", "ours")


def probe(argv, timeout):
    """(wall ms, ok) for the one bounded run that decides completion or DNF.

    This is the only run that passes `timeout=`.  CPython implements a bounded wait by
    polling with an exponentially backing-off sleep, which snaps short processes to the
    polling boundaries: measured against it, every configuration reports a wall time
    from the sequence 6, 12, 24, 48 ms and the growth signal disappears.  The timed runs
    below use a blocking wait instead, so they are not quantized.
    """
    t0 = time.perf_counter()
    try:
        p = subprocess.run(argv, cwd=HERE, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=timeout)
    except subprocess.TimeoutExpired:
        return ((time.perf_counter() - t0) * 1000.0, False)
    return ((time.perf_counter() - t0) * 1000.0, p.returncode == 0)


def timed(argv):
    """Wall ms for one run, waiting on the child with a blocking wait."""
    t0 = time.perf_counter()
    subprocess.run(argv, cwd=HERE, stdout=subprocess.DEVNULL,
                   stderr=subprocess.DEVNULL)
    return (time.perf_counter() - t0) * 1000.0


def read_stats(path, flavour):
    """(nodes, iterations) from the engine's stats file; nodes is None for egglog."""
    full = os.path.join(HERE, path)
    if not os.path.exists(full):
        return (None, None)
    with open(full) as fh:
        d = json.load(fh)
    if flavour == "ours":
        return (d["nodes"], d["iterations"])
    return (None, len(d.get("iterations", [])))


def egglog_nodes(egglog, n, timeout):
    """Total node count from egglog's own (print-size), summed over functions."""
    try:
        p = subprocess.run([egglog, "-j", "1", f"addac-n{n}.egglog.egg"], cwd=HERE,
                           stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    total = 0
    for line in p.stdout.splitlines():
        m = re.match(r"^\s*\(?\(([A-Za-z_][A-Za-z0-9_]*) (\d+)\)\)?\s*$", line)
        if m:
            total += int(m.group(2))
    return total or None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--warmups", type=int, default=1)
    ap.add_argument("--timeout", type=float, default=180.0)
    ap.add_argument("--ours", default=os.path.join(HERE, "..", "target", "release",
                                                   "semi-persistent"))
    ap.add_argument("--egglog", default=os.path.expanduser("~/tools/egglog/target/release/egglog"))
    ap.add_argument("-n", dest="widths", type=int, action="append")
    args = ap.parse_args()

    rows = []
    ours = os.path.abspath(args.ours)
    for n in (args.widths or WIDTHS):
        for name, argv, stats_path, flavour in configs(ours, args.egglog, n):
            ms, ok = probe(argv, args.timeout)          # warmup doubles as the check
            if not ok:
                # DNF: keep the one demonstration run and move on.
                rows.append({"n": n, "config": name, "run": 1,
                             "wall_ms": f"{ms:.3f}", "nodes": "", "iterations": "DNF"})
                print(f"n={n:2d} {name:12s} DNF after {ms:9.1f} ms", flush=True)
                continue
            for _ in range(args.warmups - 1):
                timed(argv)
            walls = [timed(argv) for _ in range(args.runs)]
            nodes, iters = read_stats(stats_path, flavour)
            if flavour == "egglog":
                nodes = egglog_nodes(args.egglog, n, args.timeout)
            for i, w in enumerate(walls, 1):
                rows.append({"n": n, "config": name, "run": i, "wall_ms": f"{w:.3f}",
                             "nodes": nodes if nodes is not None else "",
                             "iterations": iters if iters is not None else ""})
            print(f"n={n:2d} {name:12s} median {statistics.median(walls):9.1f} ms  "
                  f"nodes {nodes}  iters {iters}", flush=True)

    out = os.path.join(HERE, "addac-sweep.csv")
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["n", "config", "run", "wall_ms", "nodes",
                                           "iterations"])
        w.writeheader()
        w.writerows(rows)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
