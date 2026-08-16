#!/usr/bin/env python3
"""Time the E6 semi-persistence programs on both engines.

Writes one CSV row per timed run to semi-persistence.csv and prints the derived
cost-per-cycle tables. Follows comparison/methodology.md section 2: process-level
wall clock, warmups discarded, no subprocess timeout on timed runs (it quantizes
millisecond measurements). One divergence from that section, registered there:
the reported statistic is the minimum of the timed runs, not the median (see EST).

    python3 run-semipersistence.py
    python3 run-semipersistence.py --runs 3 --warmups 1
    python3 run-semipersistence.py --terms 880 --terms 2650
"""

import argparse
import csv
import os
import subprocess
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OURS = os.path.join(HERE, "..", "..", "target", "release", "semi-persistent")
DEFAULT_EGGLOG = "/tmp/egglog/target/release/egglog"

SIZES = [880, 2_650, 8_900, 27_000, 100_000]
VARIANTS = ["base", "empty", "cycles", "norun", "rerun", "rerunnorun"]
CYCLES = {"cycles": 20, "empty": 200, "norun": 200}

# Derived per-cycle costs are differences of two large wall times, so they take
# the MINIMUM of the timed runs rather than the median: background load on this
# machine is additive noise, and a median of either term leaks that noise into a
# difference that is a fraction of it. Registered as a divergence from
# methodology.md section 2; the CSV keeps every run so a median can be recomputed.
EST = min


def configs(ours, egglog):
    return [
        ("egglog", "egglog", lambda p: [egglog, "-j", "1", "--mode", "no-messages", p]),
        ("ours-naive", "native", lambda p: [ours, p, "--types", "machine"]),
        (
            "ours-semi",
            "native",
            lambda p: [ours, p, "--types", "machine", "--use-semi-naive"],
        ),
    ]


def timed(cmd):
    t0 = time.perf_counter()
    r = subprocess.run(cmd, capture_output=True)
    dt = (time.perf_counter() - t0) * 1000.0
    if r.returncode != 0:
        raise SystemExit(
            f"FAILED {' '.join(cmd)}\n{r.stdout.decode()[-2000:]}\n{r.stderr.decode()[-2000:]}"
        )
    return dt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ours", default=DEFAULT_OURS)
    ap.add_argument("--egglog", default=DEFAULT_EGGLOG)
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--warmups", type=int, default=1)
    ap.add_argument("--terms", type=int, action="append")
    ap.add_argument("--out", default=os.path.join(HERE, "semi-persistence.csv"))
    ap.add_argument("--calc-only", action="store_true")
    args = ap.parse_args()

    sizes = [] if args.calc_only else (args.terms or SIZES)
    rows = []
    med = {}
    for terms in sizes:
        for name, syntax, argv in configs(args.ours, args.egglog):
            for variant in VARIANTS:
                prog = os.path.join(HERE, f"sp-t{terms}.{variant}.{syntax}.egg")
                if not os.path.exists(prog):
                    raise SystemExit(f"missing {prog}; run gen-semipersistence.py")
                # Large instances get fewer timed runs; the CSV records how many.
                runs = args.runs if terms < 100_000 else max(3, args.runs - 2)
                for _ in range(args.warmups):
                    timed(argv(prog))
                vals = [timed(argv(prog)) for _ in range(runs)]
                for i, v in enumerate(vals):
                    rows.append(
                        {
                            "config": name,
                            "terms": terms,
                            "variant": variant,
                            "run": i,
                            "wall_ms": round(v, 3),
                        }
                    )
                med[(name, terms, variant)] = EST(vals)
                print(f"{name:11s} t={terms:<7d} {variant:11s} {med[(name, terms, variant)]:9.1f} ms")

    # Macro exhibit: calc.egg, four push/run/check/pop blocks, timed as cumulative
    # prefixes because process-level wall clock cannot see inside a program.
    calc_runs = max(args.runs, 10)
    for name, syntax, argv in configs(args.ours, args.egglog):
        for k in range(5):
            prog = os.path.join(HERE, f"calc.{syntax}-p{k}.egg")
            for _ in range(args.warmups):
                timed(argv(prog))
            vals = [timed(argv(prog)) for _ in range(calc_runs)]
            for i, v in enumerate(vals):
                rows.append(
                    {"config": name, "terms": 0, "variant": f"calc-p{k}", "run": i, "wall_ms": round(v, 3)}
                )
            med[(name, 0, f"calc-p{k}")] = EST(vals)

    with open(args.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["config", "terms", "variant", "run", "wall_ms"])
        w.writeheader()
        w.writerows(rows)

    def cost(name, terms, variant):
        return (med[(name, terms, variant)] - med[(name, terms, "base")]) / CYCLES[variant]

    print("\ncalc.egg, cumulative prefix minima (ms) and per-block deltas")
    print("config       " + "".join(f"{'p' + str(k):>10s}" for k in range(5)))
    for n, _, _ in configs("", ""):
        print(f"{n:13s}" + "".join(f"{med[(n, 0, f'calc-p{k}')]:10.2f}" for k in range(5)))
    print("config       " + "".join(f"{'blk' + str(k):>10s}" for k in range(1, 5)))
    for n, _, _ in configs("", ""):
        print(
            f"{n:13s}"
            + "".join(
                f"{med[(n, 0, f'calc-p{k}')] - med[(n, 0, f'calc-p{k - 1}')]:10.2f}"
                for k in range(1, 5)
            )
        )

    if not sizes:
        return

    print("\ncost per cycle (ms), full cycle [push; 10 terms; 2 unions; run 1; check; pop]")
    print("terms    " + "".join(f"{n:>14s}" for n, _, _ in configs("", "")))
    for terms in sizes:
        print(f"{terms:<9d}" + "".join(f"{cost(n, terms, 'cycles'):14.2f}" for n, _, _ in configs("", "")))

    print("\ncost per cycle (ms), bare [push; pop]")
    print("terms    " + "".join(f"{n:>14s}" for n, _, _ in configs("", "")))
    for terms in sizes:
        print(f"{terms:<9d}" + "".join(f"{cost(n, terms, 'empty'):14.2f}" for n, _, _ in configs("", "")))

    print("\ncost per cycle (ms), no-run cycle [push; 10 terms; 2 unions; check; pop]")
    print("terms    " + "".join(f"{n:>14s}" for n, _, _ in configs("", "")))
    for terms in sizes:
        print(f"{terms:<9d}" + "".join(f"{cost(n, terms, 'norun'):14.2f}" for n, _, _ in configs("", "")))

    print("\nours only: restore vs re-run from scratch (ms per cycle)")
    print("terms      restore  rerun    ratio | restore-nr rerun-nr ratio")
    for terms in sizes:
        r = cost("ours-naive", terms, "cycles")
        rr = med[("ours-naive", terms, "rerun")]
        rn = cost("ours-naive", terms, "norun")
        rrn = med[("ours-naive", terms, "rerunnorun")]
        print(
            f"{terms:<9d} {r:8.2f} {rr:8.2f} {rr / r:6.1f}x | {rn:10.2f} {rrn:8.2f} {rrn / rn:6.1f}x"
        )


if __name__ == "__main__":
    main()
