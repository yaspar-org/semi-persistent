#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import statistics
import unittest

from compare import (
    append_configuration,
    collect_json_metrics,
    normalize_command,
    scrape_text,
)


class StatsParsingTests(unittest.TestCase):
    def test_egglog_table_cardinalities_are_summed(self):
        text = """((Add 4)
 (Mul 3)
 (Num 3)
 (Var 1))
Overall statistics:
Rule example: search and apply 0.000s, num matches 2
"""
        self.assertEqual(scrape_text(text)["nodes"], 11)

    def test_egglog_table_without_overall_statistics_is_summed(self):
        text = """((Add 173052)
 (N 11))
"""
        self.assertEqual(scrape_text(text)["nodes"], 173063)

    def test_egglog_iteration_array_is_counted(self):
        found = {
            "nodes": [],
            "classes": [],
            "iterations": [],
        }
        collect_json_metrics({"iterations": [{}, {}, {}]}, found)
        self.assertEqual(found["iterations"], [3])


class ProvenanceTests(unittest.TestCase):
    def test_commands_use_release_safe_path_aliases(self):
        source = "/tmp/private/source"
        egglog_source = "/tmp/private/egglog"
        ours = f"{source}/target/release/semi-persistent"
        egglog = f"{egglog_source}/target/release/egglog"
        command = [
            ours,
            f"{source}/egraph/tests/egg/bench/calc.rules.egg",
            "--types",
            "machine",
        ]

        self.assertEqual(
            normalize_command(command, ours, egglog, egglog_source, source),
            [
                "<ours>",
                "<source>/egraph/tests/egg/bench/calc.rules.egg",
                "--types",
                "machine",
            ],
        )

    def test_unrelated_absolute_path_is_reduced_to_basename(self):
        normalized = normalize_command(
            ["/home/example/tool"],
            "/tmp/source/ours",
            "/tmp/egglog/egglog",
            "/tmp/egglog",
        )
        self.assertEqual(normalized, ["<absolute>/tool"])


class RetentionTests(unittest.TestCase):
    def test_aggregates_are_reproducible_from_retained_sample_precision(self):
        samples = [
            {
                "sample": index,
                "ms": elapsed,
                "nodes": 7,
                "classes": 3,
                "iterations": 2,
                "stats_status": "complete",
                "stats_source": "fixture",
            }
            for index, elapsed in enumerate(
                [1.0004, 1.0004, 1.0014], start=1
            )
        ]
        sample_rows = []
        result_rows = []

        append_configuration(
            sample_rows,
            result_rows,
            "fixture",
            "bench",
            "ours",
            "rules-naive",
            samples,
        )

        retained = [row["ms"] for row in sample_rows]
        self.assertEqual(retained, [1.0, 1.0, 1.001])
        self.assertEqual(
            result_rows[0]["mean_ms"],
            round(statistics.mean(retained), 3),
        )


if __name__ == "__main__":
    unittest.main()
