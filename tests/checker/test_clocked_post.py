#!/usr/bin/env python3.12
"""The clocked score and post-synthesis check (PLAN4 Gate 2 steps 3 to 5), without Lean: check.py
`--unproved` with a FAKE Lean (test_clocked.py's) and the REAL score, postsynth and ppa stages
(Yosys, Verilator, the built `svgolf-eval --trace`, the pinned sky130 liberty):

  * the counter fixture (seq-family) passes; its ranked score is sky130 area and cycles x period;
    two runs give byte-identical score and ppa objects;
  * the matmul G1 reference (tx-family, at the small point N=2, W=4, AccW=8 of a copy of the task)
    passes at its latency, with back-to-back transactions in the log;
  * every negative fails at its stage: tests/seq_tx/*.sv (first line `// expect: <message>`) and a
    declared latency below the design's at `postsynth`; the counter's initial-block, async-reset,
    two-clock and initializer attacks at `source`;
  * the sorter reference (stream-family, at N=3, W=4 of a copy of the task) passes at its latency 2N,
    back to back; its mutants (`STREAM_NEGATIVES`: an output one cycle early, a wrong order, a dropped
    duplicate, out_valid x after reset, out_valid 1 before the first start) and the reference at a
    declared latency 2N - 1 fail at `postsynth`, each with its own message.

    python3.12 tests/checker/test_clocked_post.py
"""
import json
import os
import re
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from test_clocked import COUNTER, CNT_SV, MATMUL_SV, SVGOLF, FakeLean, checkpy  # noqa: E402

SEQ_TX = os.path.join(SVGOLF, "tests", "seq_tx")
SORTER_SV = os.path.join(SVGOLF, "tasks", "sorter", "reference", "sorter_ins.sv")
# (what, old, new: the reference's text, a regex when `old` is compiled; the message it fails with)
STREAM_NEGATIVES = [
    ("an output one cycle early (out_data unregistered: the next cycle's value)",
     "    out_data  <= data[0 +: W];\n    if (rst) out_valid <= 1'b0;\n  end\n",
     "    if (rst) out_valid <= 1'b0;\n  end\n  assign out_data = data[0 +: W];\n",
     "the emitted values are not the task's: output"),
    ("a wrong order (every input pushes: input order)", re.compile(r"in_data > data\[\((k\+1|N-1)\)\*W \+: W\]"),
     "1'b1", "the emitted values are not the task's: output"),
    ("a dropped duplicate (a value equal to the last output is not shown)", "out_valid <= tok[0];",
     "out_valid <= tok[0] & ~(out_valid & (out_data == data[0 +: W]));", "2 values emitted, want 3"),
    ("out_valid x after reset (the cells' tokens are not reset)", "        tok[k] <= 1'b0;\n", "",
     "ls-sv: out_valid is x/z in a cared position"),
    ("out_valid 1 before the first start (the tokens reset to 1)", "        tok[k] <= 1'b0;\n",
     "        tok[k] <= 1'b1;\n", "out_valid is 1 at cycle 1, before the first start"),
]


def matmul_small():
    """A temporary copy of tasks/matmul (task.json, oracle.py) scored and checked at N=2, W=4, AccW=8."""
    d = tempfile.mkdtemp(prefix="svgolf-txsmall-")
    shutil.copy(os.path.join(SVGOLF, "tasks", "matmul", "oracle.py"), d)
    with open(os.path.join(SVGOLF, "tasks", "matmul", "task.json")) as fh:
        t = json.load(fh)
    t.update(name="tx_matmul_small", probe_points=["N=1,W=1,AccW=1", "N=2,W=4,AccW=8"],
             scoring={"params": {"N": 2, "W": 4, "AccW": 8}}, postsynth={"seeds": 3, "txns": 24})
    with open(os.path.join(d, "task.json"), "w") as fh:
        json.dump(t, fh)
    return d


def sorter_small():
    """A temporary copy of tasks/sorter (task.json, oracle.py) scored and checked at N=3, W=4."""
    d = tempfile.mkdtemp(prefix="svgolf-streamsmall-")
    shutil.copy(os.path.join(SVGOLF, "tasks", "sorter", "oracle.py"), d)
    with open(os.path.join(SVGOLF, "tasks", "sorter", "task.json")) as fh:
        t = json.load(fh)
    t.update(name="stream_sorter_small", probe_points=["N=2,W=4", "N=3,W=4"],
             scoring={"params": {"N": 3, "W": 4}}, postsynth={"seeds": 3, "txns": 24})
    with open(os.path.join(d, "task.json"), "w") as fh:
        json.dump(t, fh)
    return d


class ClockedPost(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.small, cls.sorter = matmul_small(), sorter_small()

    @classmethod
    def tearDownClass(cls):
        for d in (cls.small, cls.sorter):
            shutil.rmtree(d, ignore_errors=True)

    def check(self, task_dir, sv, **kw):
        stage = tempfile.mkdtemp(prefix="svgolf-clockedpost-")
        self.addCleanup(shutil.rmtree, stage, ignore_errors=True)
        orig, checkpy.Lean = checkpy.Lean, FakeLean
        try:
            return checkpy.check(task_dir, sv, None, stage, [], do_score=True, build_trusted=False,
                                 unproved=True, postsynth_mode="full", **kw)
        finally:
            checkpy.Lean = orig

    def test_the_counter_passes_and_scores_twice_the_same(self):
        a, b = self.check(COUNTER, CNT_SV), self.check(COUNTER, CNT_SV)
        self.assertEqual(a["stage"], "unproved", a["errors"])
        s = a["score"]
        self.assertEqual((s["cycles"], s["ranked"], s["ffs"]), (1, ["area_um2", "time_ps"], 8))
        self.assertEqual(s["time_ps"], s["period_ps"])
        self.assertEqual(s["area_um2"], a["ppa"]["area_um2_sky130"])
        sres = a["stages"]["score"]
        self.assertTrue(sres["abc"]["version"] and sres["script_sha256"] and sres["ge_table_sha256"])
        (pt,) = a["stages"]["postsynth"]["points"]
        self.assertEqual((pt["mismatches"], len(pt["seeds"])), (0, 3))
        self.assertTrue(all(x["cycles"] > 300 and not x["late"] for x in pt["seeds"]))
        for key in ("score", "ppa"):
            self.assertEqual(json.dumps(a[key], sort_keys=True), json.dumps(b[key], sort_keys=True))

    def test_the_matmul_reference_passes_back_to_back(self):
        res = self.check(self.small, MATMUL_SV, latency=2)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        self.assertEqual((res["score"]["cycles"], res["score"]["time_ps"]),
                         (2, 2 * res["score"]["period_ps"]))
        for seed in res["stages"]["postsynth"]["points"][0]["seeds"]:
            log = seed["transactions"]
            self.assertEqual(len(log), 24)
            self.assertTrue(all(t["latency"] == 2 and t["samples"] >= 1 for t in log))
            self.assertTrue(any(u["start"] == t["first_done"] + 1 for t, u in zip(log, log[1:])))

    def test_each_negative_fails_at_its_stage(self):
        cases = [(self.small, MATMUL_SV, 1, "postsynth", "within the declared latency 1")]
        for f in sorted(os.listdir(SEQ_TX)):
            with open(os.path.join(SEQ_TX, f)) as fh:
                want = fh.readline().split("// expect:")[1].strip()
            cases.append((self.small, os.path.join(SEQ_TX, f), 2, "postsynth", want))
        for f, want in (("initial", "initial"), ("async_reset", "a second event"),
                        ("two_clocks", "clk"), ("init_decl", "initializer")):
            cases.append((COUNTER, os.path.join(COUNTER, "attacks", f + ".sv"), None, "source", want))
        for task_dir, sv, lat, stage, want in cases:
            with self.subTest(sv=os.path.basename(sv), latency=lat):
                res = self.check(task_dir, sv, latency=lat)
                self.assertEqual(res["stage"], stage, res["errors"])
                self.assertIn(want, res["errors"][0])


    def test_the_sorter_reference_passes_back_to_back(self):
        res = self.check(self.sorter, SORTER_SV, latency=6)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        self.assertEqual((res["score"]["cycles"], res["score"]["time_ps"]), (6, 6 * res["score"]["period_ps"]))
        (pt,) = res["stages"]["postsynth"]["points"]
        self.assertEqual((pt["kind"], pt["mismatches"], len(pt["seeds"])), ("stream-family", 0, 3))
        for seed in pt["seeds"]:
            log = seed["transactions"]
            self.assertEqual(len(log), 24)
            self.assertTrue(all(t["outputs"] == 3 and t["latency"] == 6 for t in log), log)
            self.assertTrue(any(u["start"] == t["last_output"] + 1 for t, u in zip(log, log[1:])))

    def test_each_stream_negative_fails_at_postsynth(self):
        with open(SORTER_SV) as fh:
            ref = fh.read()
        work = tempfile.mkdtemp(prefix="svgolf-streamneg-")
        self.addCleanup(shutil.rmtree, work, ignore_errors=True)
        cases = [("the reference at a declared latency 2N - 1", SORTER_SV, 5, "beyond the declared latency 5")]
        for k, (what, old, new, want) in enumerate(STREAM_NEGATIVES):
            text, n = old.subn(new, ref) if isinstance(old, re.Pattern) else (ref.replace(old, new), ref.count(old))
            self.assertGreaterEqual(n, 1, what)
            sv = os.path.join(work, f"neg{k}.sv")
            with open(sv, "w") as fh:
                fh.write(text)
            cases.append((what, sv, 6, want))
        for what, sv, lat, want in cases:
            with self.subTest(what):
                res = self.check(self.sorter, sv, latency=lat)
                self.assertEqual(res["stage"], "postsynth", res["errors"])
                report = res["stages"]["postsynth"]["points"][-1].get("report") or []
                self.assertIn(want, res["errors"][0] + json.dumps(report))


if __name__ == "__main__":
    unittest.main(verbosity=1)
