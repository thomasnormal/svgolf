#!/usr/bin/env python3
"""Tests for leaderboard/sizes.py (`leaderboard.py sizes`: the records' designs at other sizes, measured, not ranked).
No Lean, no Yosys: the files are synthetic, built the way `sizes --write` builds them, and every check of the offline
checker is met by a PLANTED fault (a column, a hash, the arithmetic, a missing or extra size or design, the scoring-size
control against the records and the ASAP7 view, the form, the pins). The configuration reader (the sizes of
leaderboard/sizes.json against the tasks' ranges) and the run watchdog (time and memory limits over a process tree whose
child sits in a session of its own, as score.py's sandboxed Yosys does) are tested too.

    python3.12 tests/leaderboard/test_sizes.py
"""
import argparse
import contextlib
import copy
import io
import json
import os
import sys
import tempfile
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(SVGOLF, "leaderboard"))
import leaderboard as lb  # noqa: E402
import sizes  # noqa: E402

sizes.LB = lb

COMB = {"name": "toy", "kind": "comb-family", "top": "toy",
        "parameters": [{"name": "N", "range": "1 <= N < 2^31"}], "scoring": {"params": {"N": 16}}}
COMB_CFG = {"sizes": [{"params": {"N": 8}}, {"params": {"N": 16}}, {"params": {"N": 32}}],
            "series": [{"param": "N", "label": "N", "fixed": {}}], "why": "test"}
SEQ = {"name": "toyseq", "kind": "tx-family", "top": "toyseq",
       "parameters": [{"name": "N", "range": "1 <= N, N*W < 2^31"}, {"name": "W", "range": "1 <= W, N*W < 2^31"}],
       "scoring": {"params": {"N": 8, "W": 8}}}
SEQ_CFG = {"sizes": [{"params": {"N": 4, "W": 8}}, {"params": {"N": 8, "W": 8}}, {"params": {"N": 8, "W": 16}}],
           "series": [{"param": "N", "label": "N (W = 8)", "fixed": {"W": 8}},
                      {"param": "W", "label": "W (N = 8)", "fixed": {"N": 8}}], "why": "test"}
SEQ_LEAN = "-- svgolf-latency: 16\nimport X\n\ndef lat (N _W : Nat) : Nat := 2 * N\n"
NOW = {"flow": {"flow": "comb", "yosys": "Yosys 0.53", "canon_script_sha256": "c" * 64, "script_sha256": "d" * 64,
                "ge_table_sha256": "e" * 64},
       "sky130": {"ppa_version": "sky130_a0_v3", "ppa_pins_sha256": "f" * 64, "liberty_sha256": "a" * 64,
                  "input_drive": "sky130_fd_sc_hd__buf_8"},
       "asap7": {"ppa_version": "asap7_a0_v1", "ppa_pins_sha256": "b" * 64, "liberty_sha256": "9" * 64,
                 "input_drive": "BUFx8_ASAP7_75t_R"},
       "limits": {"timeout_s": 900, "memory_gb": 6}, "ppa_script_sha256": "8" * 64}


def h(c):
    return c * 64


def row(area_e4, delay, *, cycles=None, net="4", flops=None):
    t = delay * (cycles or 1)
    a5 = area_e4 // 60
    return {"status": "measured", "area_e4um2": area_e4, "area_um2": area_e4 / 10_000, "delay_ps": delay,
            "cycles": cycles, "time_ps": t, "area_x_time": area_e4 * t, "cells": 83, "buffers": 0, "unit_depth": 33,
            "area_mge": 1000, "depth": 5, "num_gates": 10, "flops": flops, "netlist_sha256": h(net),
            "repaired_sha256": h("5"), "rtlil_sha256": h("3"), "seconds": 0.5,
            "asap7": {"status": "measured", "area_e5um2": a5, "area_um2": a5 / 100_000, "delay_ps": delay // 5,
                      "time_ps": (delay // 5) * (cycles or 1), "area_x_time": a5 * (delay // 5) * (cycles or 1),
                      "cells": 84, "buffers": 0, "repaired_sha256": h("6")}}


def record(task, rhash, sv, scored_row, *, player="p1", clocked=False):
    r = scored_row
    rec = {"record_hash": rhash, "task": task["name"], "player": player,
           "files": {"sv": {"sha256": sv, "name": f"{player}.sv"}},
           "score": {"scoring_point": dict(task["scoring"]["params"]), "area_mge": r["area_mge"], "depth": r["depth"],
                     "num_gates": r["num_gates"], "rtlil_sha256": r["rtlil_sha256"]},
           "ppa": {"available": True, "area_e4um2_sky130": r["area_e4um2"], "area_um2_sky130": r["area_um2"],
                   "delay_ps_sky130": r["delay_ps"], "cells_sky130": r["cells"], "unit_depth": r["unit_depth"],
                   "netlist_sha256": r["netlist_sha256"],
                   "repair": {"buffers": r["buffers"], "netlist_sha256": r["repaired_sha256"]}}}
    if clocked:
        rec["score"].update(area_um2=r["area_um2"], period_ps=r["delay_ps"], cycles=r["cycles"], time_ps=r["time_ps"],
                            ffs=r["flops"])
    return rec


def a7_table(task, entries):
    return {"scoring_point": dict(task["scoring"]["params"]), "identity": dict(NOW["asap7"]), "flow": dict(NOW["flow"]),
            "designs": entries}


def a7_entry(sv, r):
    a = r["asap7"]
    return {"sv_sha256": sv, "area_e5um2": a["area_e5um2"], "delay_ps": a["delay_ps"], "time_ps": a["time_ps"],
            "cells": a["cells"], "buffers": a["buffers"], "repaired_sha256": a["repaired_sha256"],
            "netlist_sha256": r["netlist_sha256"]}


class Fixture:
    """A consistent task: its sizes, its records, the file `sizes --write` would write, the ASAP7 table."""

    def __init__(self, clocked=False):
        self.task = SEQ if clocked else COMB
        self.clocked = clocked
        cfg = SEQ_CFG if clocked else COMB_CFG
        self.sizes, self.series, self.scored = sizes.task_sizes(self.task, cfg)
        if clocked:
            self.rows = {h("1"): {s["key"]: row(50_000 * s["params"]["N"] * s["params"]["W"] // 8, 2000 + s["params"]["W"],
                                                cycles=2 * s["params"]["N"], net=str(i), flops=10 * s["params"]["N"])
                                  for i, s in enumerate(self.sizes)}}
        else:
            self.rows = {h("1"): {s["key"]: row(300_000 * s["params"]["N"], 160 * s["params"]["N"], net=str(i))
                                  for i, s in enumerate(self.sizes)},
                         h("2"): {s["key"]: row(400_000 * s["params"]["N"], 100 * s["params"]["N"], net=str(i + 4))
                                  for i, s in enumerate(self.sizes)}}
        self.records = [record(self.task, h(c), sv, self.rows[sv][self.scored], player=f"p{c}", clocked=clocked)
                        for c, sv in zip("ab", sorted(self.rows))]
        self.par = {h("1")}
        self.designs = sizes.plan_designs(self.task, self.records, self.par, lean_text=lambda rec: SEQ_LEAN)
        self.a7 = a7_table(self.task, [a7_entry(sv, self.rows[sv][self.scored]) for sv in sorted(self.rows)])
        flow = dict(NOW["flow"], flow="seq" if clocked else "comb")
        self.now = dict(NOW, flow=flow)
        self.a7["flow"] = flow
        self.data = sizes.file_data(self.task, self.sizes, self.series, self.scored, self.designs, self.now,
                                    copy.deepcopy(self.rows))

    def check(self, data=None, *, now=None, a7="same", text=None):
        data = self.data if data is None else data
        return sizes.check_data(data, self.task, self.sizes, self.series, self.scored, self.designs,
                                now or self.now, a7_table=self.a7 if a7 == "same" else a7, a7_identity=NOW["asap7"],
                                text=text)


class CleanFiles(unittest.TestCase):
    def test_comb_clean(self):
        fx = Fixture()
        self.assertEqual(fx.check(text=sizes.data_text(fx.data)), ([], []))

    def test_clocked_clean(self):
        fx = Fixture(clocked=True)
        self.assertEqual(fx.check(), ([], []))
        d = fx.data["designs"][0]
        self.assertEqual(d["latency"], "def lat (N _W : Nat) : Nat := 2 * N")
        self.assertEqual(d["at"]["N=4,W=8"]["cycles"], 8)

    def test_file_form(self):
        fx = Fixture()
        self.assertEqual([d["sv_sha256"] for d in fx.data["designs"]], sorted(fx.rows))
        self.assertEqual(fx.data["designs"][0]["par"], True)
        self.assertEqual(fx.data["designs"][1]["par"], False)
        self.assertEqual([s["key"] for s in fx.data["sizes"]], ["N=8", "N=16", "N=32"])
        self.assertEqual(fx.data["series"][0]["keys"], ["N=8", "N=16", "N=32"])
        self.assertTrue(fx.data["_comment"].startswith("GENERATED"))
        text = sizes.data_text(fx.data)
        self.assertEqual(text, sizes.data_text(json.loads(text)))


class PlantedFaults(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()
        self.data = copy.deepcopy(self.fx.data)
        self.d0 = self.data["designs"][0]

    def fails(self, **kw):
        f, _ = self.fx.check(self.data, **kw)
        return f

    def assertFails(self, needle, **kw):
        f = self.fails(**kw)
        self.assertTrue(any(needle in x for x in f), f"no failure naming {needle!r} in {f}")

    def test_control_area(self):
        e = self.d0["at"]["N=16"]
        e["area_e4um2"] += 1
        e["area_um2"] = e["area_e4um2"] / 10_000
        e["area_x_time"] = e["area_e4um2"] * e["time_ps"]
        self.assertFails("(the scoring size): area_e4um2")

    def test_control_delay(self):
        e = self.d0["at"]["N=16"]
        e["delay_ps"] += 7
        e["time_ps"] = e["delay_ps"]
        e["area_x_time"] = e["area_e4um2"] * e["time_ps"]
        f = self.fails()
        self.assertTrue(any("(the scoring size): delay_ps" in x for x in f), f)
        self.assertTrue(any("area_x_time" in x and "product" in x for x in f), f)

    def test_control_netlist_hash(self):
        self.d0["at"]["N=16"]["netlist_sha256"] = h("7")
        f = self.fails()
        self.assertTrue(any("(the scoring size): netlist_sha256" in x for x in f), f)
        self.assertTrue(any("ASAP7 view's entry weighs another netlist" in x for x in f), f)

    def test_control_ge_and_rtlil(self):
        self.d0["at"]["N=16"]["area_mge"] += 1
        self.d0["at"]["N=16"]["rtlil_sha256"] = h("0")
        f = self.fails()
        self.assertTrue(any("area_mge" in x for x in f) and any("rtlil_sha256" in x for x in f), f)

    def test_control_asap7(self):
        a = self.d0["at"]["N=16"]["asap7"]
        a["area_e5um2"] += 1
        a["area_um2"] = a["area_e5um2"] / 100_000
        a["area_x_time"] = a["area_e5um2"] * a["time_ps"]
        self.assertFails("ASAP7 area_e5um2")

    def test_asap7_view_stale_is_not_compared(self):
        a = self.d0["at"]["N=16"]["asap7"]
        a["area_e5um2"] += 1
        a["area_um2"] = a["area_e5um2"] / 100_000
        a["area_x_time"] = a["area_e5um2"] * a["time_ps"]
        other = copy.deepcopy(self.fx.a7)
        other["scoring_point"] = {"N": 8}
        self.assertEqual(self.fails(a7=other), [])
        self.assertEqual(self.fails(a7=None), [])

    def test_other_size_is_not_a_control(self):
        e = self.d0["at"]["N=32"]
        e["area_e4um2"] += 1
        e["area_um2"] = e["area_e4um2"] / 10_000
        e["area_x_time"] = e["area_e4um2"] * e["time_ps"]
        self.assertEqual(self.fails(), [])

    def test_arithmetic_time(self):
        self.d0["at"]["N=32"]["time_ps"] += 1
        self.assertFails("is not the delay")

    def test_arithmetic_product(self):
        self.d0["at"]["N=8"]["area_x_time"] += 1
        self.assertFails("area_x_time is not area_e4um2 x time_ps")

    def test_arithmetic_area_um2(self):
        self.d0["at"]["N=8"]["area_um2"] += 0.01
        self.assertFails("area_um2")

    def test_asap7_arithmetic(self):
        self.d0["at"]["N=8"]["asap7"]["time_ps"] += 1
        self.assertFails("asap7: time_ps")

    def test_missing_size(self):
        del self.d0["at"]["N=32"]
        self.assertFails("missing")

    def test_extra_size(self):
        self.d0["at"]["N=64"] = copy.deepcopy(self.d0["at"]["N=32"])
        self.assertFails("extra")

    def test_scoring_size_not_measured(self):
        self.d0["at"]["N=16"] = {"status": "not measured", "why": "limit", "reason": "x", "seconds": 900.0}
        f = self.fails()
        self.assertTrue(any("never left unmeasured" in x for x in f), f)
        self.assertTrue(any("not measured at the scoring size" in x for x in f), f)

    def test_not_measured_well_formed(self):
        self.d0["at"]["N=32"] = {"status": "not measured", "why": "limit", "reason": "the limit", "seconds": 900.0}
        self.assertEqual(self.fails(), [])
        self.d0["at"]["N=32"]["why"] = "slow"
        self.assertFails("a not-measured size is exactly")

    def test_bad_status(self):
        self.d0["at"]["N=8"]["status"] = "estimated"
        self.assertFails("status must be")

    def test_extra_column(self):
        self.d0["at"]["N=8"]["estimate"] = 1
        self.assertFails("keys must be exactly")

    def test_missing_design(self):
        del self.data["designs"][1]
        self.assertFails("no sizes for the design")

    def test_extra_design(self):
        extra = copy.deepcopy(self.data["designs"][1])
        extra["sv_sha256"] = h("9")
        self.data["designs"].append(extra)
        self.assertFails("which is no record's design file now")

    def test_design_order(self):
        self.data["designs"].reverse()
        self.assertFails("sv_sha256 order")

    def test_par_flag(self):
        self.d0["par"] = False
        self.assertFails("par differ")

    def test_records_list(self):
        self.d0["records"][0]["player"] = "someone"
        self.assertFails("records differ")

    def test_sizes_differ_from_config(self):
        self.data["sizes"] = self.data["sizes"][1:]
        self.assertFails("the sizes differ")

    def test_series_differ(self):
        self.data["series"][0]["keys"] = self.data["series"][0]["keys"][:2]
        self.assertFails("the series differ")

    def test_scoring_point(self):
        self.data["scored"] = "N=8"
        self.assertFails("the scoring point differs")

    def test_schema(self):
        self.data["schema"] = "svgolf-sizes/0"
        self.assertFails("schema")

    def test_top_keys(self):
        del self.data["pins"]
        self.assertFails("top-level keys")

    def test_form(self):
        text = json.dumps(self.data, indent=2, sort_keys=True) + "\n"
        f, _ = self.fx.check(self.data, text=text)
        self.assertTrue(any("deterministic form" in x for x in f), f)

    def test_stale_pins_are_a_note(self):
        e = self.d0["at"]["N=16"]
        e["area_e4um2"] += 1                    # a control fault the stale file is not held to
        e["area_um2"] = e["area_e4um2"] / 10_000
        e["area_x_time"] = e["area_e4um2"] * e["time_ps"]
        for key, change in (("sky130", {"ppa_pins_sha256": h("0")}), ("asap7", {"ppa_version": "asap7_a0_v2"}),
                            ("limits", {"timeout_s": 1800}), ("flow", {"script_sha256": h("0")})):
            now = copy.deepcopy(self.fx.now)
            now[key].update(change)
            f, notes = self.fx.check(self.data, now=now)
            self.assertEqual(f, [], key)
            self.assertTrue(notes and key in notes[0], (key, notes))

    def test_flow_without_yosys_is_not_stale(self):
        now = copy.deepcopy(self.fx.now)
        now["flow"]["yosys"] = None             # Yosys not runnable where the check runs
        self.assertEqual(self.fx.check(self.data, now=now), ([], []))

    def test_ppa_script_is_recorded_not_compared(self):
        now = copy.deepcopy(self.fx.now)
        now["ppa_script_sha256"] = h("0")
        self.assertEqual(self.fx.check(self.data, now=now), ([], []))


class ClockedFaults(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture(clocked=True)
        self.data = copy.deepcopy(self.fx.data)
        self.d0 = self.data["designs"][0]

    def fails(self):
        return self.fx.check(self.data)[0]

    def test_cycles_not_the_latency(self):
        e = self.d0["at"]["N=4,W=8"]
        e["cycles"] = 9
        e["time_ps"] = 9 * e["delay_ps"]
        e["area_x_time"] = e["area_e4um2"] * e["time_ps"]
        f = self.fails()
        self.assertTrue(any("latency at this size is 8" in x for x in f), f)

    def test_time_not_cycles_x_period(self):
        self.d0["at"]["N=8,W=16"]["time_ps"] += 1
        f = self.fails()
        self.assertTrue(any("is not cycles x period" in x for x in f), f)

    def test_control_cycles(self):
        e = self.d0["at"]["N=8,W=8"]
        rec = self.fx.designs[self.d0["sv_sha256"]]["records_full"][0]
        rec2 = copy.deepcopy(rec)
        rec2["score"]["cycles"] = 15
        rec2["score"]["time_ps"] = 15 * rec2["score"]["period_ps"]
        self.fx.designs[self.d0["sv_sha256"]]["records_full"] = [rec2]
        try:
            f = self.fails()
        finally:
            self.fx.designs[self.d0["sv_sha256"]]["records_full"] = [rec]
        self.assertTrue(any("(the scoring size): cycles 16" in x for x in f), f)
        self.assertEqual(e["cycles"], 16)

    def test_control_flops(self):
        self.d0["at"]["N=8,W=8"]["flops"] += 1
        f = self.fails()
        self.assertTrue(any("(the scoring size): flops" in x for x in f), f)

    def test_comb_columns_on_a_clocked_task(self):
        self.d0["at"]["N=4,W=8"]["cycles"] = None
        f = self.fails()
        self.assertTrue(any("positive integer cycles" in x for x in f), f)

    def test_latency_line(self):
        self.d0["latency"] = "def lat (N _W : Nat) : Nat := N"
        f = self.fails()
        self.assertTrue(any("latency differ" in x for x in f), f)


class Plan(unittest.TestCase):
    def test_range(self):
        t = {"name": "t", "parameters": [{"name": "N", "range": "1 <= N, N*N < 2^31"}]}
        self.assertEqual(sizes.range_problems(t, {"N": 46340}), [])
        self.assertEqual(sizes.range_problems(t, {"N": 46341}), ["1 <= N, N*N < 2^31"])
        self.assertEqual(sizes.range_problems(t, {"N": 0}), ["1 <= N, N*N < 2^31"])
        f = {"name": "f", "parameters": [{"name": "W", "range": "2 <= W, W + P + 1 < 2^31"},
                                         {"name": "P", "range": "2 <= P, W + P + 1 < 2^31"}]}
        self.assertEqual(sizes.range_problems(f, {"W": 5, "P": 11}), [])
        self.assertEqual(len(sizes.range_problems(f, {"W": 1, "P": 11})), 1)
        with self.assertRaises(sizes.PlanError):
            sizes.range_problems({"name": "x", "parameters": [{"name": "N", "range": "__import__('os')"}]}, {"N": 1})
        with self.assertRaises(sizes.PlanError):
            sizes.range_problems({"name": "x", "parameters": [{"name": "N", "range": "1 <= M"}]}, {"N": 1})

    def test_size_outside_range(self):
        cfg = copy.deepcopy(COMB_CFG)
        cfg["sizes"].append({"params": {"N": 2 ** 31}})
        with self.assertRaisesRegex(sizes.PlanError, "outside the task's range"):
            sizes.task_sizes(COMB, cfg)

    def test_scoring_point_required(self):
        cfg = copy.deepcopy(COMB_CFG)
        cfg["sizes"] = [s for s in cfg["sizes"] if s["params"]["N"] != 16]
        cfg["sizes"].append({"params": {"N": 64}})
        with self.assertRaisesRegex(sizes.PlanError, "scoring point"):
            sizes.task_sizes(COMB, cfg)

    def test_size_on_no_series(self):
        cfg = copy.deepcopy(SEQ_CFG)
        cfg["sizes"].append({"params": {"N": 4, "W": 4}})
        with self.assertRaisesRegex(sizes.PlanError, "lie on a series"):
            sizes.task_sizes(SEQ, cfg)

    def test_series_order(self):
        s, series, scored = sizes.task_sizes(SEQ, SEQ_CFG)
        self.assertEqual(scored, "N=8,W=8")
        self.assertEqual([x["keys"] for x in series], [["N=4,W=8", "N=8,W=8"], ["N=8,W=8", "N=8,W=16"]])

    def test_parameterless_task(self):
        with self.assertRaisesRegex(sizes.PlanError, "no parameter"):
            sizes.task_sizes({"name": "s", "kind": "comb-fixed", "scoring": {"params": {}}},
                             {"sizes": [{"params": {}}], "series": []})

    def test_committed_config(self):
        """leaderboard/sizes.json is well formed against the tree's tasks (every size inside its task's range)."""
        config = sizes.load_json(sizes.CONFIG)
        tasks = {n: lb.load_task(lb.DEFAULT_TASKS, n) for n in lb.all_task_names(lb.DEFAULT_TASKS)}
        self.assertEqual(sizes.config_problems(config, tasks), [])
        bad = copy.deepcopy(config)
        bad["left_out"]["add"] = "x"
        self.assertTrue(any("both measured and left out" in p for p in sizes.config_problems(bad, tasks)))
        bad = copy.deepcopy(config)
        del bad["left_out"]["aes_sbox"]
        self.assertTrue(any("aes_sbox" in p for p in sizes.config_problems(bad, tasks)))

    def test_records_of_another_point_left_out(self):
        fx = Fixture()
        recs = copy.deepcopy(fx.records)
        recs[1]["score"]["scoring_point"] = {"N": 8}
        designs = sizes.plan_designs(COMB, recs, set())
        self.assertEqual(sorted(designs), [h("1")])

    def test_two_records_one_file(self):
        fx = Fixture()
        recs = copy.deepcopy(fx.records)
        recs[1]["files"]["sv"]["sha256"] = recs[0]["files"]["sv"]["sha256"]
        designs = sizes.plan_designs(COMB, recs, set())
        self.assertEqual([r["record_hash"] for r in designs[h("1")]["records"]], [h("a"), h("b")])

    def test_cycles(self):
        fx = Fixture(clocked=True)
        d = fx.designs[h("1")]
        self.assertEqual(sizes.cycles_at(SEQ, d, {"N": 32, "W": 8}), 64)
        self.assertEqual(sizes.cycles_at({"kind": "react-family"}, d, {"N": 32}), 1)
        self.assertIsNone(sizes.cycles_at(COMB, d, {"N": 32}))

    def test_a_latency_that_does_not_evaluate_fails_loudly(self):
        """A `def lat` the reader does not evaluate at a size is a loud failure of the task (PlanError), never a crash
        and never a guess; the library's `clog2` is read as LeanModels/Sv/Param.lean defines it (two matmul records'
        latencies use it: `clog2 N + 1`, `N * N + clog2 N + 2`)."""
        fx = Fixture(clocked=True)
        d = dict(fx.designs[h("1")], lat=lambda params: None, latency="def lat (N _W : Nat) : Nat := N ^ 2")
        with self.assertRaises(sizes.PlanError) as e:
            sizes.cycles_at(SEQ, d, {"N": 32, "W": 8})
        self.assertIn("does not evaluate", str(e.exception))
        for text, want in (("def lat (N _W : Nat) : Nat := N * N + clog2 N + 2", [3, 7, 20, 30, 262]),
                           ("def lat (N _W : Nat) : Nat := clog2 N + 1", [1, 2, 3, 4, 5])):
            designs = sizes.plan_designs(SEQ, fx.records, set(), lean_text=lambda r: text + "\n")
            (d,) = designs.values()
            self.assertEqual((d["latency"], [sizes.cycles_at(SEQ, d, {"N": n, "W": 8}) for n in (1, 2, 4, 5, 16)]),
                             (text, want))


class WriteAndResume(unittest.TestCase):
    """`sizes --write` with the runs replaced by the fixture's rows (no Yosys): it measures only what a file under the
    same pins lacks, everything under other pins, and keeps nothing of a design whose scoring size differs from its
    records (the control), failing the task."""

    def setUp(self):
        self.fx = Fixture()
        self.dir = tempfile.TemporaryDirectory()
        self.args = argparse.Namespace(tasks_dir=lb.DEFAULT_TASKS, data_dir=lb.DEFAULT_DATA, sizes_dir=self.dir.name,
                                       asap7_dir=self.dir.name, size=None, design=None, jobs=2, timings=None,
                                       task=["toy"], sizes_config=None, write=True)
        self.config = {"tasks": {"toy": COMB_CFG}, "limits": dict(NOW["limits"])}
        self.calls = []

    def tearDown(self):
        self.dir.cleanup()

    def patches(self, rows=None, now=None):
        rows = rows or self.fx.rows

        def fake_measure(task, design, size, cycles, pins, limits, env=None, log=None):
            self.calls.append((design["sv_sha256"], size["key"]))
            return copy.deepcopy(rows[design["sv_sha256"]][size["key"]])
        st = contextlib.ExitStack()
        st.enter_context(mock.patch.object(sizes, "_context", return_value=(self.config, {"toy": COMB},
                                                                             self.fx.records)))
        st.enter_context(mock.patch.object(sizes, "task_plan", return_value=(self.fx.sizes, self.fx.series,
                                                                             self.fx.scored, self.fx.designs)))
        st.enter_context(mock.patch.object(sizes, "pins_now", return_value=now or self.fx.now))
        st.enter_context(mock.patch.object(sizes, "measure_one", side_effect=fake_measure))
        st.enter_context(mock.patch.object(sizes, "liberty_problems", return_value=[]))
        st.enter_context(contextlib.redirect_stderr(io.StringIO()))
        return st

    def path(self):
        return os.path.join(self.dir.name, "toy.json")

    def test_write_then_resume(self):
        with self.patches():
            self.assertEqual(sizes.cmd_write(self.args), 0)
        self.assertEqual(len(self.calls), 6)
        self.assertEqual(sorted(self.calls[:2]), [(h("1"), "N=16"), (h("2"), "N=16")])   # the scoring sizes first
        with open(self.path()) as fh:
            text = fh.read()
        self.assertEqual(text, sizes.data_text(self.fx.data))
        data = json.loads(text)
        del data["designs"][1]["at"]["N=32"]
        with open(self.path(), "w") as fh:
            fh.write(sizes.data_text(data))
        self.calls.clear()
        with self.patches():
            self.assertEqual(sizes.cmd_write(self.args), 0)
        self.assertEqual(self.calls, [(h("2"), "N=32")])
        with open(self.path()) as fh:
            self.assertEqual(fh.read(), sizes.data_text(self.fx.data))

    def test_other_pins_measure_everything(self):
        with self.patches():
            sizes.cmd_write(self.args)
        self.calls.clear()
        now = copy.deepcopy(self.fx.now)
        now["limits"]["timeout_s"] = 1800
        with self.patches(now=now):
            self.assertEqual(sizes.cmd_write(self.args), 0)
        self.assertEqual(len(self.calls), 6)

    def test_control_failure_keeps_nothing(self):
        rows = copy.deepcopy(self.fx.rows)
        bad = rows[h("2")]["N=16"]
        bad["area_e4um2"] += 1
        bad["area_um2"] = bad["area_e4um2"] / 10_000
        bad["area_x_time"] = bad["area_e4um2"] * bad["time_ps"]
        with self.patches(rows=rows):
            self.assertEqual(sizes.cmd_write(self.args), 1)
        self.assertEqual(sorted(self.calls), [(h("1"), "N=16"), (h("2"), "N=16")])   # nothing after the control
        with open(self.path()) as fh:
            data = json.load(fh)
        self.assertEqual(data["designs"][1]["at"], {})
        f, _ = self.fx.check(data)
        self.assertTrue(any("missing" in x for x in f), f)

    def test_no_liberty_measures_nothing(self):
        with self.patches():
            with mock.patch.object(sizes, "liberty_problems", return_value=["sky130: liberty not found"]):
                with self.assertRaisesRegex(sizes.PlanError, "cannot weigh here"):
                    sizes.cmd_write(self.args)
        self.assertEqual(self.calls, [])
        self.assertFalse(os.path.exists(self.path()))

    def test_narrowed_run(self):
        self.args.size = ["N=32"]
        self.args.design = [h("b")[:12]]                 # a record hash prefix names its design file
        with self.patches():
            self.assertEqual(sizes.cmd_write(self.args), 0)
        self.assertEqual(self.calls, [(h("2"), "N=32")])


class Watchdog(unittest.TestCase):
    """The limits hold over the whole process tree, a child in a session of its own included (score.py runs Yosys
    through check/sandbox, which starts it with start_new_session)."""

    def script(self, d, name, text):
        p = os.path.join(d, name)
        with open(p, "w") as fh:
            fh.write(text)
        return p

    def test_time_limit_kills_the_tree(self):
        with tempfile.TemporaryDirectory() as d:
            marker = os.path.join(d, "alive")
            child = self.script(d, "child.py", f"import time\ntime.sleep(3)\nopen({marker!r}, 'w').write('x')\n")
            parent = self.script(d, "parent.py", "import subprocess, sys\n"
                                 f"subprocess.run([sys.executable, {child!r}], start_new_session=True)\n")
            r = sizes.run_limited([sys.executable, parent], 1, 1 << 34)
            self.assertEqual(r["limit"], "time")
            import time
            time.sleep(3.5)
            self.assertFalse(os.path.exists(marker), "the child in its own session outlived the limit")

    def test_memory_limit_counts_the_tree(self):
        with tempfile.TemporaryDirectory() as d:
            hog = self.script(d, "hog.py", "import time\na = bytearray(300 * 1024 * 1024)\n"
                              "for i in range(0, len(a), 4096):\n    a[i] = 1\ntime.sleep(20)\n")
            parent = self.script(d, "parent.py", "import subprocess, sys\n"
                                 f"subprocess.run([sys.executable, {hog!r}], start_new_session=True)\n")
            r = sizes.run_limited([sys.executable, parent], 60, 150 * 1024 * 1024)
            self.assertEqual(r["limit"], "memory")
            self.assertLess(r["seconds"], 30)

    def test_normal_run(self):
        r = sizes.run_limited([sys.executable, "-c", "import sys; print('out'); print('err', file=sys.stderr); "
                               "sys.exit(3)"], 30, 1 << 34)
        self.assertEqual((r["rc"], r["out"], r["err"], r["limit"]), (3, "out\n", "err\n", None))


if __name__ == "__main__":
    unittest.main()
