#!/usr/bin/env python3.12
"""score/pnr/lec.py, the reference-against-routed equivalence job (a tool only: not a validity condition, not pinned),
offline on the stored negative control of 2026-11-13 (tests/pnr/fixtures/README.txt, lec/):

  - the log reader: the eight stored kepler-formal logs (4 unchanged netlists IDENTICAL, 4 changed ones DIFFERENT),
    an empty log and logs cut off before the verdict (NO VERDICT), and contradictory or partial texts;
  - the configuration: the flow's own configuration of each run with three lines changed reproduces the eight
    configurations the control ran, byte for byte; in a job directory the reference is the bound netlist file;
  - the container command (by digest, the bound netlist and the run read-only).

    python3.12 tests/pnr/test_lec.py
"""

import os
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "score", "pnr"))
import lec  # noqa: E402
import pnr  # noqa: E402
import run_job  # noqa: E402

FIX = os.path.join(HERE, "fixtures", "lec")
CASES = {"add": ("add_3f31f3f29548", "add_16ead89fd77f"), "sorter": ("sorter_616d75ed0732", "sorter_cd7ff7079121")}


def read(*rel):
    with open(os.path.join(FIX, *rel), encoding="utf-8") as fh:
        return fh.read()


def jobs():
    for task, (pos, pert) in CASES.items():
        for case, nick in (("positive", pos), ("perturbed", pert)):
            for ref in ("A", "B"):
                yield task, case, ref, pos, nick, f"lec_{task}_{case}_ref{ref}"


class VerdictTest(unittest.TestCase):
    def test_the_eight_stored_logs(self):
        seen = {lec.IDENTICAL: 0, lec.DIFFERENT: 0}
        for _task, case, _ref, _pos, _nick, job in jobs():
            with self.subTest(job=job):
                v = lec.verdict(read("logs", job + "_lec_check.log"))
                self.assertEqual(v, lec.IDENTICAL if case == "positive" else lec.DIFFERENT)
                seen[v] += 1
        self.assertEqual(seen, {lec.IDENTICAL: 4, lec.DIFFERENT: 4})

    def test_no_verdict(self):
        pos = read("logs", "lec_add_positive_refB_lec_check.log")
        pert = read("logs", "lec_add_perturbed_refB_lec_check.log")
        cut_pos = pos[:pos.index("Circuits are IDENTICAL")]
        cut_pert = pert[:pert.index("Circuits are DIFFERENT")]
        for name, text in (("empty", ""), ("cut before IDENTICAL", cut_pos), ("cut before DIFFERENT", cut_pert),
                           ("cut in the middle", pos[:len(pos) // 2]), ("both verdicts", pos + pert),
                           ("IDENTICAL with a difference found", pos + "\nFound difference for PO: 1\n"),
                           ("a difference without the final line", "Found difference for PO: 5\n"),
                           ("DIFFERENT without a difference found", "Circuits are DIFFERENT\n")):
            with self.subTest(name):
                self.assertEqual(lec.verdict(text), lec.NO_VERDICT)

    def test_the_command_reads_the_log(self):
        for name, want in (("lec_add_positive_refB_lec_check.log", 0), ("lec_add_perturbed_refB_lec_check.log", 1)):
            self.assertEqual(lec.main(["verdict", os.path.join(FIX, "logs", name)]), want)
        with tempfile.NamedTemporaryFile("w", suffix=".log", delete=False) as fh:
            fh.write("")
        self.addCleanup(os.remove, fh.name)
        self.assertEqual(lec.main(["verdict", fh.name]), 3)
        self.assertEqual(lec.main(["verdict", os.path.join(FIX, "no-such.log")]), 2)


class ConfigTest(unittest.TestCase):
    def test_the_control_s_eight_configurations(self):
        """config() over each run's own flow configuration gives the control's file: the reference first (A: the
        unchanged run's 1_synth_lec.v, B: the bound netlist file), the run's 6_final_lec.v second, its own log."""
        for task, case, ref, pos, nick, job in jobs():
            with self.subTest(job=job):
                reference = (f"/srv/run/results/asap7/{pos}/min_s1/1_synth_lec.v" if ref == "A"
                             else f"/srv/designs/{pos}.v")
                got = lec.config(read("flow", nick + ".yml"), reference,
                                 f"/srv/run/results/asap7/{nick}/min_s1/6_final_lec.v",
                                 f"/work/out/{job}_lec_check.log")
                self.assertEqual(got, read("cfg", job + ".yml"))
                flow = read("flow", nick + ".yml").splitlines()
                self.assertEqual(sum(a != b for a, b in zip(flow, got.splitlines())), 3)
                self.assertEqual(len(flow), len(got.splitlines()))

    def test_a_config_not_of_the_flow_s_shape_is_refused(self):
        flow = read("flow", "add_3f31f3f29548.yml")
        for bad in (flow.replace("input_paths:", "inputs:"), flow.replace("log_file:", "log:"),
                    flow + "log_file: /x\n",
                    flow.replace("input_paths:\n", "input_paths:\n  - /extra.v\n")):
            with self.subTest(bad=bad[:40]), self.assertRaises(ValueError):
                lec.config(bad, "/a", "/b", "/c")

    def test_in_a_job_directory(self):
        tmp = tempfile.mkdtemp(prefix="pnrlec-")
        self.addCleanup(shutil.rmtree, tmp, ignore_errors=True)
        job = "add_3f31f3f29548__min_s1"
        obj = pnr.work_dirs(tmp, job)["objects"]
        os.makedirs(obj)
        shutil.copyfile(os.path.join(FIX, "flow", "add_3f31f3f29548.yml"), os.path.join(obj, "6_final_lec_test.yml"))
        with self.assertRaises(ValueError):                                  # no configuration yet
            lec.run_command(tmp, job, pnr.load_pins())
        path = lec.write_config(tmp, job)
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        self.assertIn("input_paths:\n  - /work/designs/add_3f31f3f29548.v\n"
                      "  - /work/run/results/asap7/add_3f31f3f29548/min_s1/6_final_lec.v\n", text)
        self.assertIn(f"log_file: /work/lec/{job}_lec_check.log\n", text)
        with self.assertRaises(ValueError):                                  # no bound netlist file
            lec.run_command(tmp, job, pnr.load_pins())
        os.makedirs(os.path.join(tmp, "designs"))
        with open(os.path.join(tmp, "designs", "add_3f31f3f29548.v"), "w"):
            pass
        pins = pnr.load_pins()
        cmd = lec.run_command(tmp, job, pins)
        mounts = {inside: ro for _h, inside, ro in run_job._mounts_of(cmd)}
        self.assertEqual(mounts, {"/work/designs": True, "/work/run": True, "/work/lec": False, "/tmp": False})
        self.assertIn(pnr.image_ref(pins), cmd)
        self.assertEqual(cmd[cmd.index("--network") + 1], "none")
        self.assertIn(f"kepler-formal --config /work/lec/{job}.yml", cmd[-1])
        self.assertEqual(lec.main(["run", tmp, job, "--dry-run"]), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
