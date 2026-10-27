# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Harness regressions: failure classification, resource limits and provenance."""

import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

SPEC = importlib.util.spec_from_file_location("runner", Path(__file__).with_name("run.py"))
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class RunnerTests(unittest.TestCase):
    def test_negative_control_requires_its_diagnostic(self):
        program = {"expected": "check_failure", "stderr_contains": ["check failed"]}
        execution = {"stop": None, "returncode": 1}
        self.assertIsNone(runner.assess(program, execution, "", "error: check failed"))
        self.assertIsNotNone(runner.assess(program, execution, "", "parse error"))
        self.assertIsNotNone(runner.assess(program, dict(execution, returncode=0), "", ""))
        self.assertIsNotNone(runner.assess(program, dict(execution, returncode=-9), "", "check failed"))
        self.assertIsNotNone(runner.assess(program, dict(execution, returncode=101), "", "check failed"))
        self.assertIsNotNone(runner.assess(program, dict(execution, stop="timeout"), "", "check failed"))

    def test_success_requires_output_oracle(self):
        program = {"expected": "pass", "stdout_contains": ["(Cheap)"]}
        execution = {"stop": None, "returncode": 0}
        self.assertIsNone(runner.assess(program, execution, "(Cheap)\n", ""))
        self.assertIsNotNone(runner.assess(program, execution, "(Expensive)\n", ""))

    def test_string_oracle_is_not_a_list_of_characters(self):
        program = {"expected": "check_failure", "stderr_contains": "check failed"}
        with self.assertRaisesRegex(ValueError, "list of nonempty strings"):
            runner.validate_oracles(program)
        with self.assertRaisesRegex(ValueError, "diagnostic oracle"):
            runner.validate_oracles({"expected": "check_failure"})

    def test_paths_and_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture = root / "test.egg"
            fixture.write_text("(check (= 1 1))")
            sha = runner.digest(fixture)
            self.assertEqual(runner.checked_path(root, "test.egg", sha), fixture.resolve())
            with self.assertRaises(ValueError):
                runner.checked_path(root, "../escape.egg", sha)
            fixture.write_text("changed")
            with self.assertRaises(ValueError):
                runner.checked_path(root, "test.egg", sha)

    def execute(self, source, timeout=2, output_limit=8192):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            return runner.execute(
                [sys.executable, "-c", source], root, root / "stdout",
                root / "stderr", timeout, output_limit,
            )

    def test_timeout_is_not_expected_failure(self):
        result = self.execute("import time; time.sleep(30)", timeout=0.1)
        self.assertEqual(result["stop"], "timeout")
        self.assertNotEqual(result["returncode"], 0)
        self.assertLess(result["elapsed_seconds"], 3)

    def test_output_limit_also_checked_after_exit(self):
        result = self.execute("print('x' * 20000)")
        self.assertEqual(result["stop"], "output_limit")

    @unittest.skipUnless(os.name == "posix", "process-group cleanup is POSIX-specific")
    def test_sigterm_reaps_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pid_file = root / "child.pid"
            child = (
                "import os,time; from pathlib import Path; "
                f"Path({str(pid_file)!r}).write_text(str(os.getpid())); time.sleep(30)"
            )
            parent = (
                "import run,signal,sys; from pathlib import Path; "
                "signal.signal(signal.SIGTERM,run.terminate); "
                f"p=Path({str(root)!r}); "
                f"run.execute([sys.executable,'-c',{child!r}],p,p/'out',p/'err',30,8192)"
            )
            process = subprocess.Popen(
                [sys.executable, "-B", "-c", parent], cwd=runner.ROOT,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
            child_pid = None
            try:
                deadline = time.monotonic() + 5
                while time.monotonic() < deadline:
                    if pid_file.exists() and pid_file.read_text():
                        child_pid = int(pid_file.read_text())
                        break
                    time.sleep(0.01)
                self.assertIsNotNone(child_pid, "child never started")
                process.terminate()
                self.assertEqual(process.wait(timeout=5), 128 + signal.SIGTERM)
                with self.assertRaises(ProcessLookupError):
                    os.kill(child_pid, 0)
            finally:
                if child_pid:
                    try:
                        os.killpg(child_pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                if process.poll() is None:
                    process.kill()
                process.wait()

    def test_both_engine_modes(self):
        program = {"engine": "ours", "path": "example.egg"}
        self.assertEqual(
            runner.command("ours", program, "semi-naive"),
            ["ours", "--types", "machine", "--use-semi-naive", "example.egg"],
        )
        program["engine"] = "egglog"
        self.assertEqual(runner.command("egglog", program, "naive"), ["egglog", "--naive", "example.egg"])
        self.assertEqual(runner.command("egglog", program, "semi-naive"), ["egglog", "example.egg"])

    def test_corpus_has_33_distinct_sources(self):
        examples = runner.load_examples()
        self.assertEqual(len(examples), 33)
        self.assertEqual(len({e["source"]["path"] for e in examples}), 33)


if __name__ == "__main__":
    unittest.main()
