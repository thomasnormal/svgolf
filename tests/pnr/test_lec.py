#!/usr/bin/env python3.12
"""score/pnr/lec.py, the reference-against-routed equivalence check (a step of every routed run and a validity
condition since 2026-11-13: score/pnr/pins.json `validity_rule`), offline on the stored negative control of 2026-11-13
(tests/pnr/fixtures/README.txt, lec/ and negctl/):

  - the log reader: the eight stored kepler-formal logs (4 unchanged netlists IDENTICAL, 4 changed ones DIFFERENT),
    an empty log and logs cut off before the verdict (NO VERDICT), and contradictory or partial texts;
  - the configuration: the flow's own configuration of each run with three lines changed reproduces the eight
    configurations the control ran, byte for byte; in a job directory the reference is the bound netlist file;
  - the container command (by digest, the bound netlist and the run read-only), and `run_job.py run`'s dry run naming
    the check after the flow;
  - THE NEGATIVE CONTROL AS A RULE: the two changed netlists' runs passed the flow's own check (their stored logs say
    IDENTICAL), and their reference-against-routed logs say DIFFERENT; filed as the par design's scoring run, the
    rule refuses them (`asap7pnr_file_problems`, `asap7pnr_status` "failed"), while the unchanged runs' records pass.

    python3.12 tests/pnr/test_lec.py
"""

import json
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

sys.path.insert(0, os.path.join(SVGOLF, "leaderboard"))
import collect  # noqa: E402
import leaderboard as lb  # noqa: E402

FIX = os.path.join(HERE, "fixtures", "lec")
NEG = os.path.join(HERE, "fixtures", "negctl")
# the sha256 of the changed sorter run's routed 6_final_lec.v (2026-11-13; the file is not a fixture, 92 kB); the
# changed add run's is (fixtures/negctl/run/results/...)
SORTER_PERTURBED_ROUTED = "af7f12c5f4874b4803db37e068344060975211a5ec2ea0f73b9753e5f293ae79"
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


class RecordTest(unittest.TestCase):
    def test_the_record_of_a_job_directory(self):
        tmp = tempfile.mkdtemp(prefix="pnrlec-")
        self.addCleanup(shutil.rmtree, tmp, ignore_errors=True)
        job = "add_3f31f3f29548__min_s1"
        self.assertIsNone(lec.record(tmp, job))                              # not run: no log, no configuration
        obj = pnr.work_dirs(tmp, job)["objects"]
        os.makedirs(obj)
        shutil.copyfile(os.path.join(FIX, "flow", "add_3f31f3f29548.yml"), os.path.join(obj, "6_final_lec_test.yml"))
        cfg = lec.write_config(tmp, job)
        self.assertIsNone(lec.record(tmp, job))                              # configured, not run
        shutil.copyfile(os.path.join(FIX, "logs", "lec_add_positive_refB_lec_check.log"),
                        os.path.join(tmp, "lec", job + "_lec_check.log"))
        rec = lec.record(tmp, job)
        self.assertEqual(rec, {"verdict": lec.IDENTICAL, "config_sha256": pnr.sha256_file(cfg),
                               "log_sha256": pnr.sha256_file(os.path.join(FIX, "logs", "lec_add_positive_refB_lec_check.log")),
                               "reference_sha256": None, "routed_lec_sha256": None})
        self.assertTrue(lb.pnr_lec_reference_problems(rec, "0" * 64))         # a hash missing: never a valid record
        self.assertEqual(lec.main(["record", tmp, job]), 0)
        self.assertEqual(lec.main(["record", tmp, "add_3f31f3f29548__min_s2"]), 2)

    def test_the_runner_names_the_check_after_the_flow(self):
        import contextlib
        import io
        job_dir = os.path.join(HERE, "fixtures", "example_job")
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            self.assertEqual(run_job.main(["run", job_dir, "_example_38596d52847c__min_s1", "--dry-run"]), 0)
        self.assertIn("then, when the flow exits 0, the reference-against-routed check", buf.getvalue())


class NegativeControlRuleTest(unittest.TestCase):
    """The negative control of 2026-11-13 as the rule's test: one gate changed in add's and sorter's par design, each
    changed netlist placed and routed under the pins. The flow's own check passed both (it compares the routed netlist
    with the run's own input); the reference-against-routed check, the bound netlist against each run's routed
    netlist, said DIFFERENT. The tree's rule refuses a run with that record, whatever else the run shows."""

    def record(self, task, case):
        pos, pert = CASES[task]
        nick = pos if case == "positive" else pert
        job = f"lec_{task}_{case}_refB"
        if task == "add":
            ref = pnr.sha256_file(os.path.join(NEG, "designs", f"{pos}.v"))
        else:
            ref = next(e for e in lb.load_asap7pnr("sorter")["designs"] if e["netlist_sha256"].startswith(pos[7:]))[
                "netlist_sha256"]
        routed = os.path.join(NEG, "run", "results", "asap7", nick, "min_s1", "6_final_lec.v")
        return {"verdict": lec.verdict(read("logs", job + "_lec_check.log")),
                "log_sha256": pnr.sha256_file(os.path.join(FIX, "logs", job + "_lec_check.log")),
                "config_sha256": pnr.sha256_file(os.path.join(FIX, "cfg", job + ".yml")), "reference_sha256": ref,
                "routed_lec_sha256": pnr.sha256_file(routed) if os.path.isfile(routed) else (
                    SORTER_PERTURBED_ROUTED if case == "perturbed" else "0" * 64)}

    def test_the_flow_s_check_passed_the_changed_netlists(self):
        for task, (_pos, pert) in CASES.items():
            with self.subTest(task=task):
                logs = os.path.join(NEG, "run", "logs", "asap7", pert, "min_s1")
                self.assertEqual(collect.lec_verdicts(logs), ["6_final:IDENTICAL"])
        bound = read_neg("designs", "add_3f31f3f29548.v")
        routed = read_neg("run", "results", "asap7", "add_16ead89fd77f", "min_s1", "6_final_lec.v")
        self.assertIn("XOR2xp5_ASAP7_75t_R _178_ (.A(_131_), .B(_133_), .Y(_26_));", bound)
        self.assertIn("XNOR2xp5_ASAP7_75t_R _178_ (.A(_131_),", routed)          # the changed gate, routed

    def test_the_rule_refuses_them(self):
        pins = lb.asap7pnr_identity()
        for task, (pos, _pert) in CASES.items():
            table = lb.load_asap7pnr(task)
            a7 = lb.load_asap7(task)
            entry = next(e for e in table["designs"] if e["netlist_sha256"].startswith(pos[len(task) + 1:]))
            for case in ("positive", "perturbed"):
                with self.subTest(task=task, case=case):
                    rec = self.record(task, case)
                    self.assertEqual(rec["reference_sha256"], entry["netlist_sha256"])     # the bound netlist
                    t = json.loads(json.dumps(table))
                    e = lb.asap7pnr_entry(t, entry["sv_sha256"])
                    e["runs"][0]["lec_reference"] = rec
                    problems = lb.asap7pnr_file_problems(t, task)
                    status, why, _ = lb.asap7pnr_status(t, a7, entry["sv_sha256"], task=lb.load_task(lb.DEFAULT_TASKS,
                                                                                                        task), pins=pins)
                    if case == "positive":
                        self.assertEqual((problems, status), ([], "bound"))
                    else:
                        self.assertEqual(rec["verdict"], lec.DIFFERENT)
                        self.assertTrue(any("reference-against-routed check's IDENTICAL" in p for p in problems),
                                        problems)
                        self.assertEqual(status, "failed")
                        self.assertIn("its verdict is DIFFERENT", why)


def read_neg(*rel):
    with open(os.path.join(NEG, *rel), encoding="utf-8") as fh:
        return fh.read()


if __name__ == "__main__":
    unittest.main(verbosity=2)
