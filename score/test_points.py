#!/usr/bin/env python3.12
"""Tests of the several-points measurement (score/points.py, score/points.json, score/measured/<task>.json).

    python3.12 score/test_points.py

Most tests read committed files only (no Yosys, no liberty): the points file names each task's scored point, the plan
covers every design of score/tests/ppa/designs.json, and the committed data EQUALS THE GOLDENS BIT FOR BIT at the scored
point (expected_ppa.json for the designs of designs.json, tests/expected.json's GE and clocked columns), carries
tests/expected.json's GE columns at every other point it has them, and is current (design files, sky130 identity, pinned
flow). One test re-measures a point that is not the scored one through the pinned flow and compares it with the
committed row; it needs the pinned liberty, Yosys and pyslang and is skipped without them.
"""

import contextlib
import copy
import hashlib
import io
import json
import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import points  # noqa: E402


def load(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


CONFIG = load(points.CONFIG)
TASKS = sorted(CONFIG["tasks"])


def data(task):
    return load(points.data_path(task))


def have_flow():
    try:
        import ppa
        import pyslang  # noqa: F401
        import score
    except ImportError:
        return False
    return shutil.which(score.yosys_bin()) is not None and os.path.isfile(ppa.find_liberty(None, ppa.Pins()))


class ConfigTest(unittest.TestCase):
    def test_every_scored_point_is_one_of_the_task_s_points(self):
        """points.json is untrusted, task.json trusted: the scored point (task.json scoring.params) must be listed."""
        for t in TASKS:
            with self.subTest(task=t):
                task = load(os.path.join(SVGOLF, "tasks", t, "task.json"))
                order = list(task["scoring"]["params"])
                keys = [points.point_key(p["params"], order) for p in CONFIG["tasks"][t]["points"]]
                self.assertIn(points.point_key(task["scoring"]["params"], order), keys)

    def test_the_points_of_the_decision(self):
        """The points the site offers (the lead's decision of 11/05): add 8..64, mul and clmul 4..32, matmul (2,8,32) and
        (4,8,32), the sorter 4, 8, 16 at W = 8, fdivp bfloat16, binary16, binary32, aes_sbox its one size."""
        want = {"add": ["N=8", "N=16", "N=32", "N=64"], "mul": ["N=4", "N=8", "N=16", "N=32"],
                "clmul": ["N=4", "N=8", "N=16", "N=32"], "aes_sbox": ["default"],
                "fdivp": ["W=8,P=8", "W=5,P=11", "W=8,P=24"], "matmul": ["N=2,W=8,AccW=32", "N=4,W=8,AccW=32"],
                "sorter": ["N=4,W=8", "N=8,W=8", "N=16,W=8"]}
        plans = points.full_plan(CONFIG)
        self.assertEqual({t: [p["key"] for p in plans[t]["points"]] for t in plans}, want)
        self.assertEqual([p["label"] for p in plans["fdivp"]["points"]], ["bfloat16", "binary16", "binary32"])

    def test_the_plan_covers_designs_json_and_the_site_s_designs(self):
        """Every design of designs.json (the sky130 goldens) is in the plan at its point, and so is every reference of
        task.json and every baseline of tests/expected.json (at its banlist_points when it has them: a fixed size)."""
        plans = points.full_plan(CONFIG)
        for g in load(points.DESIGNS)["designs"]:
            p = plans[g["task"]]
            self.assertTrue(any(d["src"] == g["src"] and p["scored"] in d["points"] for d in p["designs"]), g["name"])
        exp = load(points.EXPECTED)["tasks"]
        for t, p in plans.items():
            task = load(os.path.join(SVGOLF, "tasks", t, "task.json"))
            ids = {d["id"]: d for d in p["designs"]}
            for ref in task["references"]:
                self.assertIn("reference/" + os.path.splitext(os.path.basename(ref["sv"]))[0], ids)
            for stem, b in exp[t]["baselines"].items():
                d = ids[f"baseline/{stem}"]
                self.assertEqual(d["points"], [k for k in [q["key"] for q in p["points"]]
                                               if "banlist_points" not in b or k in b["banlist_points"]])

    def test_a_bad_config_is_refused(self):
        exp = load(points.EXPECTED)
        bad = copy.deepcopy(CONFIG["tasks"]["add"])
        bad["points"] = [q for q in bad["points"] if q["params"]["N"] != 16]
        with self.assertRaisesRegex(points.PlanError, "the scored point N=16"):
            points.task_plan("add", bad, expected=exp)
        bad = copy.deepcopy(CONFIG["tasks"]["add"])
        bad["skip"] = [{"design": "add_n", "point": "N=16", "reason": "x"}]
        with self.assertRaisesRegex(points.PlanError, "never skipped"):
            points.task_plan("add", bad, expected=exp)
        bad = copy.deepcopy(CONFIG["tasks"]["fdivp"])
        bad["points"].append({"params": {"W": 8}})
        with self.assertRaisesRegex(points.PlanError, "every parameter"):
            points.task_plan("fdivp", bad, expected=exp)
        bad = copy.deepcopy(CONFIG["tasks"]["mul"])
        bad.setdefault("families", {})["x"] = ["no_such_baseline"]
        with self.assertRaisesRegex(points.PlanError, "not a baseline"):
            points.task_plan("mul", bad, expected=exp)

    def test_every_baseline_is_proved_in_the_plan_and_the_data(self):
        """Decided 2026-11-12: every design the site shows has a kernel-checked proof. A baseline names its proof
        (tests/expected.json `lean`), the plan carries it, the data marks it `proved` with that file, and a baseline
        without one, or whose proof file is not there, is a plan error."""
        plans = points.full_plan(CONFIG)
        for t, p in plans.items():
            for d in p["designs"]:
                if d["kind"] == "baseline":
                    self.assertTrue(os.path.isfile(os.path.join(SVGOLF, d["lean"])), d["lean"])
            for e in data(t)["designs"]:
                if e["kind"] == "baseline":
                    self.assertIs(e.get("proved"), True, (t, e["id"]))
                    self.assertTrue(os.path.isfile(os.path.join(SVGOLF, e["lean"])), (t, e["lean"]))
        exp = load(points.EXPECTED)
        for change, why in ((lambda b: b.pop("lean"), "names no proof"),
                            (lambda b: b.update(lean="baselines/no_such_proof.lean"), "is not there")):
            bad = copy.deepcopy(exp)
            change(bad["tasks"]["add"]["baselines"]["add_n_sklansky"])
            with self.assertRaisesRegex(points.PlanError, why):
                points.task_plan("add", CONFIG["tasks"]["add"], expected=bad)


class LatencyTest(unittest.TestCase):
    def test_the_reference_latency_functions(self):
        """The clocked references' `def lat` lines, evaluated in task.json's parameter order, agree with their
        `-- svgolf-latency:` headers at the scored point."""
        for t, stem, want in (("matmul", "matmul_g1", {(2, 8, 32): 2, (4, 8, 32): 4}),
                              ("sorter", "sorter_ins", {(4, 8): 8, (8, 8): 16, (16, 8): 32})):
            task = load(os.path.join(SVGOLF, "tasks", t, "task.json"))
            order = list(task["scoring"]["params"])
            with open(os.path.join(SVGOLF, "tasks", t, "reference", stem + ".lean"), encoding="utf-8") as fh:
                text = fh.read()
            line, at = points.latency_of(text, order)
            self.assertTrue(line.startswith("def lat"), line)
            for vals, n in want.items():
                self.assertEqual(at(dict(zip(order, vals))), n)
            self.assertEqual(points.declared_latency(text), at(task["scoring"]["params"]))

    def test_the_evaluator_is_lean_s_nat_and_nothing_more(self):
        env = {"N": 5, "W": 3}
        self.assertEqual(points.eval_nat("2 * N + 1", env), 11)
        self.assertEqual(points.eval_nat("(N + W) * 2", env), 16)
        self.assertEqual(points.eval_nat("W - N", env), 0)              # Nat subtraction truncates
        self.assertEqual(points.eval_nat("N / 2", env), 2)
        self.assertEqual(points.eval_nat("N / 0", env), 0)
        for bad in ("N ^ 2", "foo N", "Nat.log2 N", "N +", "(N", "clog2", "N clog2", "clog2 +"):
            self.assertIsNone(points.eval_nat(bad, env), bad)
        # the library's clog2 (LeanModels/Sv/Param.lean: if n ≤ 1 then 0 else (n - 1).log2 + 1, its #guards' values),
        # applied tighter than any operator, as Lean's application binds
        self.assertEqual([points.clog2(n) for n in (0, 1, 2, 3, 4, 5, 8, 9, 16, 17)], [0, 0, 1, 2, 2, 3, 3, 4, 4, 5])
        self.assertEqual(points.eval_nat("N * N + clog2 N + 2", {"N": 4}), 20)
        self.assertEqual(points.eval_nat("clog2 N + 1", {"N": 16}), 5)
        self.assertEqual(points.eval_nat("clog2 (N + 3) * 2", {"N": 5}), 6)
        # a proof that defines its own clog2 is not read as the library's
        self.assertEqual(points.latency_of("def clog2 (n : Nat) : Nat := n\ndef lat (N : Nat) : Nat := clog2 N\n",
                                           ["N"]), (None, None))
        line, at = points.latency_of("def lat (N : Nat) (W : Nat) : Nat := N * W\n", ["N", "W"])
        self.assertEqual(at({"N": 3, "W": 4}), 12)
        self.assertEqual(points.latency_of("def lat (N : Nat) : Nat := if N = 0 then 1 else N\n", ["N"])[1]({"N": 2}),
                         None)


class DataTest(unittest.TestCase):
    def test_the_committed_data_is_consistent_and_current(self):
        """`points.py check`: every task's data matches its plan (points, designs and their files), every (design,
        point) is measured or dropped with a reason, the scored point never dropped, under the current sky130 identity
        and pinned flow, and the goldens agree (below)."""
        self.assertEqual(points.check(CONFIG), [])

    def test_the_scored_point_equals_the_goldens_bit_for_bit(self):
        """THE GOLDEN RULE: at the scored point the measured numbers ARE the goldens. Read here independently of
        points.check: expected_ppa.json for every design of designs.json (area in 1e-4 um^2, delay, cells, the GE
        columns and every hash), tests/expected.json for every reference and baseline (the GE columns at every point
        it scores, and a clocked task's area, period, cycles and time at the scored point)."""
        gold = load(points.EXPECTED_PPA)
        seen = 0
        for g in load(points.DESIGNS)["designs"]:
            d = data(g["task"])
            row = next(e for e in d["designs"] if e["src"] == g["src"])["at"][d["scored"]]
            want = gold["designs"][g["name"]]
            got = {"area_e4um2": row["area_e4um2"], "delay_ps": row["delay_ps"], "cells": row["cells"],
                   "area_ge": row["area_ge"], "depth": row["depth"], "gates": row["num_gates"],
                   "unit_depth": row["unit_depth"], "netlist_sha256": row["netlist_sha256"],
                   "repaired_sha256": row["repaired_sha256"], "rtlil_sha256": row["rtlil_sha256"]}
            self.assertEqual(got, want, g["name"])
            self.assertEqual(row["time_ps"], row["delay_ps"])
            self.assertEqual(row["area_um2"], row["area_e4um2"] / 10000)
            seen += 1
        self.assertEqual(seen, len(load(points.DESIGNS)["designs"]))
        exp = load(points.EXPECTED)["tasks"]
        compared = clocked = 0
        for t in TASKS:
            d = data(t)
            for e in d["designs"]:
                if e["kind"] == "record":
                    continue
                for key, s in ((exp[t].get(e["kind"] + "s") or {}).get(e["name"], {}).get("scores") or {}).items():
                    if key not in e["at"]:
                        continue
                    row = e["at"][key]
                    self.assertEqual((row["area_mge"], row["depth"], row["num_gates"], row["gates"]),
                                     (s["area_mge"], s["depth"], s["num_gates"], s["gates"]), f"{t} {e['id']} {key}")
                    compared += 1
                    if key == d["scored"] and "period_ps" in s:
                        self.assertEqual((row["area_um2"], row["period_ps"], row["cycles"], row["time_ps"], row["ffs"]),
                                         (s["area_um2"], s["period_ps"], s["cycles"], s["time_ps"], s["ffs"]))
                        clocked += 1
        self.assertGreater(compared, 60)
        self.assertEqual(clocked, 2)                 # matmul_g1, sorter_ins

    def test_records_measured_are_never_the_reference_player_s(self):
        for t in TASKS:
            for e in data(t)["designs"]:
                if e["kind"] == "record":
                    self.assertNotEqual(e["name"], points.REFERENCE_PLAYER)
        with open(os.path.join(SVGOLF, "site", "config.json"), encoding="utf-8") as fh:
            self.assertEqual(json.load(fh)["reference_player"], points.REFERENCE_PLAYER)

    def test_the_data_is_canonical_text(self):
        """The committed files are exactly what `measure` writes (sorted keys, one format), so a re-measurement that
        changes nothing changes no byte."""
        for t in TASKS:
            with open(points.data_path(t), encoding="utf-8") as fh:
                text = fh.read()
            self.assertEqual(text, points.data_text(json.loads(text)), t)
            self.assertNotIn("seconds", text)            # no wall time in the data

    def test_drops_are_said(self):
        """A dropped (design, point) carries its reason; the one pinned in points.json is the one dropped, and its
        reason names the time limit the task has now (task.json `time_limit_s`; 300 s since 2026-11-06, re-measured
        2026-11-12: the reason named the 120 s of before)."""
        dropped = {(t, e["id"], k): why for t in TASKS for e in data(t)["designs"]
                   for k, why in (e.get("dropped") or {}).items()}
        self.assertEqual(sorted(dropped), [("fdivp", "reference/fdivp_newton", "W=8,P=24")])
        for (t, _, _), why in dropped.items():
            with open(os.path.join(SVGOLF, "tasks", t, "task.json"), encoding="utf-8") as fh:
                limit = json.load(fh)["time_limit_s"]
            self.assertIn(f"time limit ({limit} s)", why)


class RecordsFlagTest(unittest.TestCase):
    def test_records_join_the_plan_with_the_flag_only(self):
        """`--records` adds a player's record (never the reference player's, never a design file the task already
        has); without the flag the plan is the references and baselines."""
        exp = load(points.EXPECTED)
        with open(os.path.join(SVGOLF, "tests", "add", "baselines", "add_n_sklansky.sv"), "rb") as fh:
            known = hashlib.sha256(fh.read()).hexdigest()
        recs = [{"task": "add", "player": "golfer", "record_hash": "a" * 64, "files": {"sv": {"sha256": "f" * 64}}},
                {"task": "add", "player": points.REFERENCE_PLAYER, "record_hash": "b" * 64,
                 "files": {"sv": {"sha256": "e" * 64}}},
                {"task": "add", "player": "copycat", "record_hash": "c" * 64, "files": {"sv": {"sha256": known}}},
                {"task": "mul", "player": "golfer", "record_hash": "d" * 64, "files": {"sv": {"sha256": "1" * 64}}}]
        with_ = points.task_plan("add", CONFIG["tasks"]["add"], expected=exp, records=recs)
        without = points.task_plan("add", CONFIG["tasks"]["add"], expected=exp)
        rec = [d for d in with_["designs"] if d["kind"] == "record"]
        self.assertEqual([(d["id"], d["name"], d["src"]) for d in rec],
                         [("a" * 64, "golfer", f"leaderboard/data/add/{'a' * 64}.sv")])
        self.assertEqual(rec[0]["points"], [p["key"] for p in with_["points"]])
        self.assertFalse(any(d["kind"] == "record" for d in without["designs"]))


@unittest.skipUnless(have_flow(), "needs the pinned liberty, Yosys and pyslang")
class RemeasureTest(unittest.TestCase):
    def test_a_point_that_is_not_the_scored_one_remeasures_bit_for_bit(self):
        """The pinned flow on the Sklansky adder at N = 32 (not the scored point, so no golden backs it) gives the
        committed row exactly: the data is reproducible, not only correct where a golden says so."""
        plan = points.full_plan(CONFIG, ["add"])["add"]
        d = next(x for x in plan["designs"] if x["id"] == "baseline/add_n_sklansky")
        point = next(p for p in plan["points"] if p["key"] == "N=32")
        res, why, _ = points.run_ppa(plan, d, point, plan["limit"])
        self.assertIsNone(why)
        row = points.row_of(res, plan, point, None)
        committed = next(e for e in data("add")["designs"] if e["id"] == d["id"])["at"]["N=32"]
        self.assertEqual(row, committed)

    def test_a_timeout_drops_the_point_and_kills_the_flow(self):
        """A run past its limit is stopped (its process group killed) and reported as the time-limit drop."""
        plan = points.full_plan(CONFIG, ["add"])["add"]
        d = next(x for x in plan["designs"] if x["id"] == "reference/add_n")
        point = next(p for p in plan["points"] if p["key"] == "N=64")
        res, why, secs = points.run_ppa(plan, d, point, 0.05)
        self.assertIsNone(res)
        self.assertIn("did not finish within the task's time limit", why)
        self.assertLess(secs, 30)

    def test_measure_writes_the_committed_bytes(self):
        """`measure --task clmul --out DIR` (the cheapest task: clmul_n and three proved baselines at four points) writes
        the committed file byte for byte."""
        with tempfile.TemporaryDirectory() as tmp:
            with contextlib.redirect_stderr(io.StringIO()):
                rc = points.main(["measure", "--task", "clmul", "--out", tmp, "--records"])
            self.assertEqual(rc, 0)
            with open(os.path.join(tmp, "clmul.json"), encoding="utf-8") as a, \
                    open(points.data_path("clmul"), encoding="utf-8") as b:
                self.assertEqual(a.read(), b.read())


if __name__ == "__main__":
    unittest.main()
