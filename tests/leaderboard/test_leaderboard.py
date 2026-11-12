#!/usr/bin/env python3
"""Tests for leaderboard/leaderboard.py. No Lean, no Yosys run, no network: the
check results are synthetic (same shape as check.py's JSON) and the `add` path
that runs check.py is exercised against a FAKE check.py script.

    python3 tests/leaderboard/test_leaderboard.py          # run
    UPDATE_GOLDEN=1 python3 tests/leaderboard/test_leaderboard.py   # rewrite the golden file

Covers: record round trip, record_hash canonicality and a pinned hash, tamper
detection (record, stored .sv and .lean), refusal of rejected submissions, the
ranked board (decided 2026-11-05: area x time, the sky130 A0' area times the
time, is the one ranked number, equal products share a rank and are listed as
the site lists them; the Pareto layer, GE and depth are extra columns; a record
without sky130 columns, or of another PPA identity or input drive, is not
ranked; a clocked record's time is cycles x period), the Pareto frontier, an
exploration view (dominance, ties, determinism, agreement with score.py's),
layers, the depth budget ranking, staleness (flow / scoring point), the
Markdown golden file, `assisted_by` handling, Lean line counting, the task.json
`leaderboard` field, the CLI end to end, the committed records' integrity, and
the post-synthesis MODE (WP-C2: `add` and `verify --full` run check.py with
`--postsynth full`; a light result is refused unless `add --postsynth light`
asks for a light record, which is marked `light` in the record, `add`'s output
and the boards; a record with no `postsynth.mode` reads as full), and the sky130
PPA columns (WP-X3: `add` and `verify --full` run check.py with `--ppa require`; WP-X4 adds the sub-object `ppa.mapped`,
flow A1', tested below by PpaMappedRecordTest, PpaMappedAxesTest and the CLI tests; the
record carries check.py's `ppa` object as an OPTIONAL key, additive like `postsynth.mode`:
a record without it stays valid, hashes as before and verifies as before; the opt-in
`pareto --axes` view; the default output is unchanged).
"""
import contextlib
import copy
import importlib.util
import io
import json
import os
import random
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(SVGOLF, "leaderboard"))
sys.path.insert(0, os.path.join(SVGOLF, "score"))
import leaderboard as lb  # noqa: E402
import score  # noqa: E402  (the cross-check of the Pareto filter, and the flows' files)

GOLDEN = os.path.join(HERE, "golden_board.md")

SV_TEXT = b"module toy_top #(parameter N = 1) (input [N-1:0] a, output [N-1:0] y);\n  assign y = a;\nendmodule\n"
LEAN_TEXT = b"""import Submission.Design
import LeanModels.Sv.CombView
/-! Doc comment
  with a nested /- block -/ comment. -/
namespace Submission
-- a line comment
theorem solution : Goal := by   -- trailing comment
  sv_structure
  omega

end Submission
"""
SV_SHA = lb.sha256_bytes(SV_TEXT)
CANON_SHA = "c" * 64
# the reason check.py's `incomplete_reasons` gives for a light post-synthesis check
LIGHT_REASON = ("the post-synthesis check ran LIGHT (a subset of the vectors, for local feedback); leaderboard.py add "
                "runs the full check itself, so there is no need to rerun with --postsynth full first (only a stored "
                "result for add --from-check must come from a full run)")

with open(os.path.join(SVGOLF, "score", "ge.json")) as _fh:
    GE = {k: round(v * 1000) for k, v in json.load(_fh).items() if not k.startswith("_")}
REAL_FLOW = lb.current_flow()
FLOW = {"yosys": REAL_FLOW["yosys"] or "Yosys test", "canon_script_sha256": REAL_FLOW["canon_script_sha256"],
        "script_sha256": REAL_FLOW["script_sha256"], "ge_table_sha256": REAL_FLOW["ge_table_sha256"]}
# a fixed flow for the golden file (independent of the checkout's scripts)
GOLD_FLOW = {"yosys": "Yosys 0.53", "canon_script_sha256": "1" * 64, "script_sha256": "2" * 64,
             "ge_table_sha256": "3" * 64}
ENV = {"svgolf_revision": "abc123", "lean_toolchain": "leanprover/lean4:v4.33.0-rc1",
       "files": {"check.py": "4" * 64, "score/score.py": "5" * 64}}


def toy_task(**kw):
    t = {"name": "toy", "title": "A toy task", "top": "toy_top", "status": "ready",
         "scoring": {"params": {"N": 16}, "depth_budget": None},
         "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"]}
    t.update(kw)
    return t


GOLD_GE = {"AND": 1333, "XOR": 2000}      # fixed weights for the pinned hash and the golden file


def fake_result(task="toy", sv_sha=SV_SHA, gates=None, depth=10, flow=None, point=None, ge=None,
                mode=None):
    """A check.py result of an accepted submission (the fields the leaderboard
    reads; the shape of a real result, see tests/mul/results/check.json). With
    no `mode` its postsynth stage has none, like a result of a checker from
    before the light mode (it reads as full); `mode` "full" / "light" adds the
    fields a current checker writes (`mode`, `full_vectors`)."""
    gates = dict(gates or {"AND": 10})
    flow = flow or FLOW
    mge = sum((ge or GE)[g] * n for g, n in gates.items())
    res = {
        "accepted": True, "errors": [], "stage": "done", "task": task,
        "score": {"area_ge": round(mge / 1000, 3), "area_mge": mge, "depth": depth,
                  "gates": gates, "num_gates": sum(gates.values()),
                  "params": dict(point or {"N": 16})},
        "stages": {
            "source": {"sha256": sv_sha, "canonical_sha256": CANON_SHA, "findings": []},
            "imports": {"imports": ["Submission.Design", "LeanModels.Sv.CombView"], "rejected": []},
            "extract": {"extractor_sha256": "e" * 64, "lean_surfaces": "0123abcd+dirty"},
            "trusted": {"exit": 0, "seconds": 1.0},
            "solution": {"exit": 0, "seconds": 8.41, "cpu_seconds": 9.1, "time_limit_s": 600,
                         "time_limit_counts": "cpu", "wall_limit_s": 3000},
            "integrity": {"changed": [], "changed_by_end": [], "files": 5},
            "comparator": {"exit": 0, "result": {
                "accepted": True, "axioms": ["propext", "Quot.sound", "Classical.choice"]}},
            "leanchecker": {"exit": 0, "seconds": 1.0},
            "score": {"gated": True, "top": "toy_top", "yosys_version": flow["yosys"],
                      "canon_script_sha256": flow["canon_script_sha256"],
                      "script_sha256": flow["script_sha256"],
                      "ge_table_sha256": flow["ge_table_sha256"], "rtlil_sha256": "d" * 64},
            "postsynth": {"point": "N=16", "vectors": 500, "mismatches": 0, "salted": False,
                          "seed": "5" * 64, "verilator": "Verilator 5.042 2025-11-02 rev X"},
        },
    }
    res["complete"] = True
    if mode is not None:
        ps = res["stages"]["postsynth"]
        ps.update(mode=mode, full_vectors=500)
        if mode == "light":
            ps["vectors"] = 120
            res["complete"] = False
            res["incomplete"] = [LIGHT_REASON]
    return res


BUF8 = "sky130_fd_sc_hd__buf_8"     # the pins' default input drive (sky130_a0_v3), the drive of a task that names none
BUF1 = "sky130_fd_sc_hd__buf_1"


def fake_ppa(res=None, area_e4=4604416, delay_ps=2487, constants=False, **over):
    """A numeric `ppa` object (what check.py's `ppa` stage writes) consistent with the score of `res`:
    unit depth = the scorer's depth, cells = its gate count (+1 for a priced tie cell); its `setup` names the
    default input drive, as sky130_a0_v3 writes it for a task that names none."""
    res = res or fake_result()
    n = res["score"]["num_gates"] + (1 if constants else 0)
    hist = {"nand2_1": n - 1, "inv_1": 1} if n > 1 else {"nand2_1": n}
    block = {"available": True, "ppa_version": "sky130_a0_v1", "area_um2_sky130": area_e4 / 10000,
             "area_e4um2_sky130": area_e4, "delay_ps_sky130": delay_ps,
             "unit_depth": res["score"]["depth"], "cells_sky130": n, "cell_hist_sky130": hist,
             "constants": constants, "critical": {"output": "y[0]", "edge": "r", "cells": 3},
             "setup": {"pi_slew_ps": 50, "input_drive": BUF8, "po_load_ff": 10, "wires": "none",
                       "tables": "no extrapolation"},
             "liberty_file": "sky130_fd_sc_hd__tt_025C_1v80.lib", "liberty_sha256": "a" * 64,
             "ppa_pins_sha256": "b" * 64, "ppa_script_sha256": "c" * 64, "netlist_sha256": "d" * 64}
    block.update(over)
    return block


def fake_mapped(area_e4=4404224, delay_ps=6313, cells=4, **over):
    """A `ppa.mapped` object (flow A1', what check.py's `ppa` stage writes beside A0''s columns), well-formed and reading the
    canonical RTLIL `fake_result` scores ("d" * 64)."""
    hist = {"maj3_1": cells - 1, "inv_1": 1} if cells > 1 else {"maj3_1": cells}
    m = {"available": True, "ppa_mapped_version": "sky130_a1_v1", "area_um2_sky130_mapped_v1": area_e4 / 10000,
         "area_e4um2_sky130_mapped_v1": area_e4, "mapped_delay_sky130_v1": delay_ps, "mapped_cells_sky130_v1": cells,
         "mapped_cell_hist_sky130_v1": hist, "mapped_levels_sky130_v1": 2, "mapped_buffers_sky130_v1": 0,
         "mapped_inverters_sky130_v1": 1 if cells > 1 else 0, "constants": False,
         "critical": {"output": "y[0]", "edge": "f", "cells": 2},
         "setup": {"pi_slew_ps": 50, "po_load_ff": 10, "wires": "none"},
         "equivalence": {"vectors": 2048, "seed": "svgolf-ppa-mapped/1"},
         "liberty_file": "sky130_fd_sc_hd__tt_025C_1v80.lib", "liberty_sha256": "a" * 64, "ppa_pins_sha256": "b" * 64,
         "ppa_mapped_pins_sha256": "e" * 64, "ppa_mapped_script_sha256": "f" * 64, "ppa_script_sha256": "c" * 64,
         "yosys_version": "Yosys test", "abc_version": "ABC test", "rtlil_sha256": "d" * 64, "netlist_sha256": "9" * 64}
    m.update(over)
    return m


def with_ppa(res, mode="require", **kw):
    """`res` with check.py's `ppa` key and `stages.ppa`, as `check.py --ppa <mode>` writes them."""
    mapped = kw.pop("mapped", None)
    res["ppa"] = fake_ppa(res, **kw)
    res["stages"]["ppa"] = {"mode": mode, "seconds": 0.5}
    if mapped is not None:
        res["ppa"]["mapped"] = (fake_mapped(**mapped) if isinstance(mapped, dict) and mapped.get("available") is not False
                                else mapped)
    return res


with open(os.path.join(SVGOLF, "score", "ge_seq.json")) as _fh:
    GE_SEQ = {k: round(v * 1000) for k, v in json.load(_fh).items() if not k.startswith("_")}
REAL_SEQ_FLOW = lb.current_flow(SVGOLF, "seq")
# the clocked flow (svgolf_seq.ys, ge_seq.json) in the form `FLOW` has, for the synthetic clocked results
SEQ = {"flow": "seq", "yosys": FLOW["yosys"], "canon_script_sha256": REAL_SEQ_FLOW["canon_script_sha256"],
       "script_sha256": REAL_SEQ_FLOW["script_sha256"], "ge_table_sha256": REAL_SEQ_FLOW["ge_table_sha256"]}


def clocked_task(**kw):
    """A synthetic tx-family task (scoring point N = 16): its post-synthesis points N = 2 and N = 16, 2 seeds each."""
    t = toy_task(kind="tx-family", clock="clk", postsynth={"points": [{"N": 2}, {"N": 16}], "seeds": 2})
    t.update(kw)
    return t


def fake_clocked_result(task=None, *, area_e4=90000, period=1000, latency=None, gates=None, mode="full"):
    """A check.py result of an accepted CLOCKED submission (check.py `score_clocked`): scored by the clocked flow, the
    clocked score (area_um2, period_ps, cycles = the declared latency or 1, time_ps), the `ppa` block it is held to,
    and `stages.postsynth.points`: every point of `task` (`clocked_points`), each with every seed, as
    check/postsynth.py `run_clocked` writes them (timings and transaction logs included, which a record drops)."""
    task = task or clocked_task()
    gates = dict(gates or {"AND": 5, "DFF_P": 1})
    res = with_ppa(fake_result(task=task["name"], gates=gates, flow=SEQ, ge=GE_SEQ, point=lb.scoring_point(task)),
                   area_e4=area_e4, delay_ps=period)
    res["stages"]["score"]["flow"] = "seq"
    cycles = latency or 1
    if latency is not None:
        res["latency"] = latency
    res["score"].update(area_um2=area_e4 / 10000, period_ps=period, cycles=cycles, time_ps=cycles * period,
                        ffs=gates.get("DFF_P", 0), ranked=["area_um2", "time_ps"])
    pts = []
    for k, q in enumerate(lb.clocked_points(task)):
        pts.append({"kind": task["kind"], "point": lb.point_text(q), "mode": mode, "mismatches": 0,
                    "netlist_sha256": res["ppa"]["netlist_sha256"] if q == lb.scoring_point(task) else str(k + 1) * 64,
                    "envelope_sha256": "7" * 64, "oracle_sha256": "8" * 64, "fuel": 100000, "latency": latency,
                    "verilator": "Verilator 5.042 2025-11-02 rev X", "seconds": 1.5, "t_netlist_build_s": 0.5,
                    "seeds": [{"seed": s, "reset_cycles": 1, "cycles": 300 + s, "late": False, "t_netlist_run_s": 0.1,
                               "t_lssv_s": 0.2, "transactions": [{"tag": "t", "start": 1 + 3 * j} for j in range(24)]}
                              for s in range(lb.clocked_seeds(task))]})
    res["stages"]["postsynth"] = {"points": pts, "netlist_sha256": res["ppa"]["netlist_sha256"]}
    if mode == "light":
        res["complete"] = False
        res["incomplete"] = [LIGHT_REASON]
    return res


# The arbiter's accepted check result (tests/leaderboard/clocked_arbiter/: check.py --postsynth full --ppa require on
# the reference rr_mask, kind react-family, the run's task.json and design; check.json's `_fixture` says what was
# changed: the run's temporary paths only)
ARBITER = os.path.join(HERE, "clocked_arbiter")
# A stand-in proof: a check result does not bind the .lean (leaderboard/README.md, "Commands"), and the record's proof
# facts are not what these tests are about
ARB_LEAN = (b"import Submission.Design\nimport SvGolf.React\n\nnamespace Submission\n"
            b"theorem solution : Goal := by\n  exact rr_mask_satisfies\n\nend Submission\n")


def arbiter_fixture():
    """(task.json, check result, design bytes) of the arbiter fixture, fresh copies."""
    with open(os.path.join(ARBITER, "task.json")) as fh:
        task = json.load(fh)
    with open(os.path.join(ARBITER, "check.json")) as fh:
        res = json.load(fh)
    with open(os.path.join(ARBITER, "rr_mask.sv"), "rb") as fh:
        sv = fh.read()
    return task, res, sv


def arbiter_flow():
    """The flow the arbiter's result was scored under (its clocked flow), as `current_flow` gives one."""
    s = arbiter_fixture()[1]["stages"]["score"]
    return {"flow": "seq", "yosys": s["yosys_version"], "canon_script_sha256": s["canon_script_sha256"],
            "script_sha256": s["script_sha256"], "ge_table_sha256": s["ge_table_sha256"]}


def arbiter_record(res=None, *, task=None, player=lb.REFERENCE_PLAYER, postsynth="full", date="2026-11-07"):
    """The record `add` makes of the arbiter's result (or of `res`, a changed copy of it)."""
    t, r, sv = arbiter_fixture()
    return lb.build_record(task or t, res or r, player=player, assisted_by=["Claude (Anthropic)"],
                           notes="reference solution", submitted_at=date, sv_name="/x/rr_mask.sv", sv_bytes=sv,
                           lean_name="/x/rr_mask.lean", lean_bytes=ARB_LEAN, environment=ENV, postsynth=postsynth)


def make_record(task=None, player="alice", assisted=(), date="2026-10-29", notes="", sv=SV_TEXT,
                lean=LEAN_TEXT, res=None, postsynth="full", sky=None, **kw):
    """A record of `res` (default: `fake_result(**kw)`). `sky` = (area_e4um2, delay_ps): the result's `ppa` block, the
    ranked sky130 score (absent: a record without the columns, which the boards do not rank)."""
    task = task or toy_task()
    res = res or fake_result(sv_sha=lb.sha256_bytes(sv), **kw)
    if sky is not None:
        res = with_ppa(copy.deepcopy(res), area_e4=sky[0], delay_ps=sky[1])
    return lb.build_record(task, res, player=player, assisted_by=list(assisted), notes=notes,
                           submitted_at=date, sv_name="/x/toy.sv", sv_bytes=sv,
                           lean_name="/x/toy.lean", lean_bytes=lean, environment=ENV,
                           postsynth=postsynth)


def quiet(fn, *a, **kw):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = fn(*a, **kw)
    return rc, out.getvalue(), err.getvalue()


class Tmp(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="svgolf-lbtest-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.data = os.path.join(self.tmp, "data")

    def store(self, rec, sv=SV_TEXT, lean=LEAN_TEXT):
        return lb.store_record(self.data, rec, sv, lean)


class RecordTest(Tmp):
    def test_fields_and_validity(self):
        rec = make_record(player="alice", assisted=["Claude (Anthropic)"], notes=" a note ")
        self.assertEqual(lb.validate_record(rec), [])
        self.assertEqual(rec["schema"], lb.SCHEMA)
        self.assertEqual((rec["task"], rec["player"], rec["notes"]), ("toy", "alice", "a note"))
        self.assertEqual(rec["assisted_by"], ["Claude (Anthropic)"])
        self.assertEqual(rec["files"]["sv"], {"name": "toy.sv", "sha256": SV_SHA})
        self.assertEqual(rec["files"]["lean"]["sha256"], lb.sha256_bytes(LEAN_TEXT))
        self.assertEqual(rec["canonical_sha256"], CANON_SHA)
        s = rec["score"]
        self.assertEqual((s["area_mge"], s["area_ge"], s["depth"], s["num_gates"]),
                         (13330, 13.33, 10, 10))
        self.assertEqual(s["scoring_point"], {"N": 16})
        self.assertEqual(s["gates"], {"AND": 10})
        c = rec["checker"]
        self.assertEqual((c["svgolf_revision"], c["lean_surfaces_revision"], c["lean_toolchain"]),
                         ("abc123", "0123abcd+dirty", "leanprover/lean4:v4.33.0-rc1"))
        self.assertEqual(c["yosys"], FLOW["yosys"])
        self.assertTrue(c["verilator"].startswith("Verilator 5"))
        self.assertEqual(c["files"], ENV["files"])
        p = rec["proof"]
        self.assertEqual(p["axioms"], ["Classical.choice", "Quot.sound", "propext"])
        self.assertEqual(p["build_seconds"], 8.41)
        self.assertEqual(p["lines"], 7)
        self.assertTrue(p["uses_comb_view"])
        self.assertFalse(p["uses_comb_eq"])
        self.assertEqual(p["tactics"], ["omega", "sv_structure"])
        self.assertEqual(rec["postsynth"]["mismatches"], 0)

    def test_record_hash_is_canonical(self):
        rec = make_record()
        self.assertEqual(rec["record_hash"], lb.compute_record_hash(rec))
        shuffled = {k: rec[k] for k in sorted(rec, reverse=True)}
        shuffled["score"] = {k: rec["score"][k] for k in sorted(rec["score"], reverse=True)}
        self.assertEqual(lb.compute_record_hash(shuffled), rec["record_hash"])
        # the hash does not cover itself, but covers everything else
        for path, new in ((("player",), "bob"), (("score", "depth"), 11),
                          (("notes",), "x"), (("assisted_by",), ["tool"]),
                          (("checker", "yosys"), "Yosys 9")):
            other = copy.deepcopy(rec)
            d = other
            for k in path[:-1]:
                d = d[k]
            d[path[-1]] = new
            self.assertNotEqual(lb.compute_record_hash(other), rec["record_hash"], path)

    def test_record_hash_pinned(self):
        """The canonical JSON is part of the format: this hash changes only if
        the schema or the canonicalization does (then bump SCHEMA)."""
        rec = make_record(player="pin", assisted=["tool a", "tool b"], notes="pinned",
                          date="2026-01-02", res=fake_result(flow=GOLD_FLOW, ge=GOLD_GE))
        self.assertEqual(rec["record_hash"], PINNED_HASH)

    def test_pure_no_clock(self):
        a, b = make_record(), make_record()
        self.assertEqual(a, b)
        with self.assertRaises(lb.Refused):
            make_record(date=None)    # no default date inside the pure function
        with self.assertRaises(lb.Refused):
            make_record(date="2026-13-40")
        with self.assertRaises(lb.Refused):
            make_record(date="yesterday")
        self.assertEqual(make_record(date="2026-10-29T12:30:00Z")["submitted_at"],
                         "2026-10-29T12:30:00Z")

    def test_round_trip(self):
        rec = make_record()
        path = self.store(rec)
        self.assertEqual(os.path.basename(path), rec["record_hash"] + ".json")
        self.assertEqual(os.path.dirname(path), os.path.join(self.data, "toy"))
        loaded = lb.load_records(self.data, "toy")
        self.assertEqual([(p, r, e) for p, r, e in loaded], [(path, rec, None)])
        self.assertEqual(lb.load_records(self.data), loaded)
        base = path[:-5]
        with open(base + ".sv", "rb") as fh:
            self.assertEqual(fh.read(), SV_TEXT)
        with open(base + ".lean", "rb") as fh:
            self.assertEqual(fh.read(), LEAN_TEXT)
        res = lb.verify_record(path, loaded[0][1], toy_task())
        self.assertEqual((res.status, res.fails), ("ok", []))
        with self.assertRaises(lb.Refused):      # never overwrites
            self.store(rec)

    def test_validate_rejects_malformed(self):
        rec = make_record()
        for mutate, frag in (
                (lambda r: r.pop("score"), "missing keys"),
                (lambda r: r.update(extra=1), "unknown keys"),
                (lambda r: r.update(schema="v0"), "schema"),
                (lambda r: r["score"].update(area_ge=1.0), "area_ge"),
                (lambda r: r["score"].update(num_gates=3), "num_gates"),
                (lambda r: r["files"]["sv"].update(sha256="xyz"), "files.sv"),
                (lambda r: r.update(player="no spaces allowed"), "player"),
                (lambda r: r["proof"].update(axioms=["b", "a"]), "axioms"),
                (lambda r: r["postsynth"].update(mismatches=2), "postsynth")):
            bad = copy.deepcopy(rec)
            mutate(bad)
            problems = lb.validate_record(bad)
            self.assertTrue(any(frag in p for p in problems), (frag, problems))
        self.assertIn("not a JSON object", lb.validate_record([])[0])


# Changed once, deliberately, by WP-C2 (10/30): `postsynth` gained `mode` and `full_vectors`
# (additive: a record without them stays valid and reads as a full check; SCHEMA unchanged).
PINNED_HASH = "bacee7ff43e63b54b73d7492b1c95e76042fea1e11a70b6cb73eb468002100d4"


class TamperTest(Tmp):
    def setUp(self):
        super().setUp()
        self.rec = make_record()
        self.path = self.store(self.rec)
        self.base = self.path[:-5]

    def verify(self, **kw):
        with open(self.path) as fh:
            rec = json.load(fh)
        return lb.verify_record(self.path, rec, toy_task(), **kw)

    def write_rec(self, rec):
        with open(self.path, "w") as fh:
            json.dump(rec, fh)

    def assertFails(self, frag, **kw):
        r = self.verify(**kw)
        self.assertEqual(r.status, "FAIL")
        self.assertTrue(any(frag in f for f in r.fails), r.fails)

    def test_untouched_is_ok(self):
        self.assertEqual(self.verify().status, "ok")

    def test_edit_record_score(self):
        rec = copy.deepcopy(self.rec)
        rec["score"]["depth"] = 1
        self.write_rec(rec)
        self.assertFails("record_hash does not match")

    def test_edit_record_and_rehash_but_not_rename(self):
        rec = copy.deepcopy(self.rec)
        rec["player"] = "mallory"
        rec["record_hash"] = lb.compute_record_hash(rec)
        self.write_rec(rec)
        self.assertFails("file name")

    def test_edit_sv(self):
        with open(self.base + ".sv", "ab") as fh:
            fh.write(b"// edited\n")
        self.assertFails("stored sv file")

    def test_edit_lean(self):
        with open(self.base + ".lean", "ab") as fh:
            fh.write(b"-- edited\n")
        self.assertFails("stored lean file")

    def test_missing_files(self):
        os.remove(self.base + ".sv")
        self.assertFails("missing")

    def test_garbage_json_is_reported(self):
        with open(self.path, "w") as fh:
            fh.write("{ not json")
        (loaded,) = lb.load_records(self.data, "toy")
        self.assertIsNone(loaded[1])
        self.assertIn("Expecting", loaded[2])

    def test_arithmetic_checked_against_ge_table(self):
        """Gate counts edited AND the hash recomputed AND the file renamed: the
        offline arithmetic still disagrees with area_mge."""
        rec = copy.deepcopy(self.rec)
        rec["score"]["gates"] = {"AND": 9}
        rec["score"]["num_gates"] = 9
        rec["record_hash"] = lb.compute_record_hash(rec)
        new = os.path.join(self.data, "toy", rec["record_hash"])
        for ext in (".sv", ".lean"):
            shutil.copy(self.base + ext, new + ext)
        with open(new + ".json", "w") as fh:
            json.dump(rec, fh)
        r = lb.verify_record(new + ".json", rec, toy_task())
        self.assertTrue(any("sum of the gate weights" in f for f in r.fails), r.fails)

    def test_forged_consistent_record_is_caught_by_rescore(self):
        """The documented limit of the offline level: a fully re-hashed forgery
        passes it; the rescore (and a re-check) is what catches it."""
        rec = copy.deepcopy(self.rec)
        rec["score"]["depth"] = 1
        rec["record_hash"] = lb.compute_record_hash(rec)
        new = os.path.join(self.data, "toy", rec["record_hash"])
        for ext in (".sv", ".lean"):
            shutil.copy(self.base + ext, new + ext)
        with open(new + ".json", "w") as fh:
            json.dump(rec, fh)
        self.assertEqual(lb.verify_record(new + ".json", rec, toy_task()).status, "ok")
        honest = {"area_mge": 13330, "depth": 10, "gates": {"AND": 10}, "num_gates": 10,
                  "rtlil_sha256": "d" * 64, "sources": [{"canonical_sha256": CANON_SHA}]}
        r = lb.verify_record(new + ".json", rec, toy_task(), flow=FLOW, rescore=lambda sv: honest)
        self.assertEqual(r.status, "FAIL")
        self.assertTrue(any("depth: recorded 1, rescored 10" in f for f in r.fails), r.fails)

    def test_disallowed_axiom_fails(self):
        task = toy_task(allowed_axioms=["propext"])
        r = lb.verify_record(self.path, self.rec, task)
        self.assertTrue(any("axioms outside" in f for f in r.fails), r.fails)

    def test_intact_tripwire_on_the_boards(self):
        rec = copy.deepcopy(self.rec)
        rec["score"]["depth"] = 1
        self.write_rec(rec)
        warned = []
        good = lb.good_records(lb.load_records(self.data), warn=warned.append)
        self.assertEqual(good, [])
        self.assertEqual(len(warned), 1)


class VerifyLevelsTest(Tmp):
    """`rescore` / `recheck` are injected: no Yosys or Lean here."""

    def setUp(self):
        super().setUp()
        self.rec = make_record()
        self.path = self.store(self.rec)
        self.honest_score = {"area_mge": 13330, "depth": 10, "gates": {"AND": 10},
                             "num_gates": 10, "rtlil_sha256": "d" * 64,
                             "sources": [{"canonical_sha256": CANON_SHA}]}

    def check_result(self, **kw):
        res = fake_result(**kw)
        return res

    def test_rescore_ok_and_mismatch(self):
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=FLOW,
                             rescore=lambda sv: self.honest_score)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("rescored: same score", r.notes)
        worse = dict(self.honest_score, area_mge=14000)
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=FLOW, rescore=lambda sv: worse)
        self.assertEqual(r.status, "FAIL")
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=FLOW,
                             rescore=lambda sv: dict(self.honest_score,
                                                     sources=[{"canonical_sha256": "0" * 64}]))
        self.assertTrue(any("canonical text" in f for f in r.fails))

        def boom(sv):
            raise RuntimeError("yosys failed")
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=FLOW, rescore=boom)
        self.assertTrue(any("rescore failed" in f for f in r.fails))

    def test_stale_flow_is_not_a_failure_and_skips_rescore(self):
        other = dict(FLOW, script_sha256="9" * 64)
        called = []
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=other,
                             rescore=lambda sv: called.append(sv))
        self.assertEqual(r.status, "stale")
        self.assertEqual(r.fails, [])
        self.assertEqual(called, [])
        self.assertTrue(any("script_sha256" in s for s in r.stale))

    def test_recheck(self):
        ok = fake_result()
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=FLOW,
                             recheck=lambda sv, lean: ok)
        self.assertEqual((r.status, r.fails), ("ok", []))
        rejected = dict(ok, accepted=False, stage="solution", errors=["does not compile"])
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=FLOW,
                             recheck=lambda sv, lean: rejected)
        self.assertTrue(any("no longer accepts" in f for f in r.fails))
        slower = fake_result(depth=11)
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=FLOW,
                             recheck=lambda sv, lean: slower)
        self.assertTrue(any("depth recorded 10, now 11" in f for f in r.fails), r.fails)
        r = lb.verify_record(self.path, self.rec, toy_task(), flow=dict(FLOW, script_sha256="9" * 64),
                             recheck=lambda sv, lean: slower)
        self.assertEqual((r.status, r.fails), ("stale", []))

    def test_checker_drift_is_a_note(self):
        r = lb.verify_record(self.path, self.rec, toy_task(), current_files={"check.py": "0" * 64,
                                                                              "score/score.py": "5" * 64})
        self.assertEqual(r.status, "ok")
        self.assertTrue(any("check.py" in n for n in r.notes))

    def test_offpoint_is_stale(self):
        task = toy_task(scoring={"params": {"N": 32}, "depth_budget": None})
        r = lb.verify_record(self.path, self.rec, task)
        self.assertEqual(r.status, "stale")


class AcceptanceTest(Tmp):
    def refusals(self, mutate, task=None, sv=SV_TEXT):
        res = fake_result()
        mutate(res)
        with self.assertRaises(lb.Refused) as cm:
            lb.build_record(task or toy_task(), res, player="alice", assisted_by=[], notes="",
                            submitted_at="2026-10-29", sv_name="a.sv", sv_bytes=sv,
                            lean_name="a.lean", lean_bytes=LEAN_TEXT, environment=ENV)
        return " | ".join(cm.exception.problems)

    def test_each_rejection_is_refused(self):
        def s(res, *path_and_value):
            *path, value = path_and_value
            d = res
            for k in path[:-1]:
                d = d[k]
            d[path[-1]] = value
        cases = [
            (lambda r: s(r, "accepted", False), "did not accept"),
            (lambda r: s(r, "stage", "comparator"), "not `done`"),
            (lambda r: s(r, "errors", ["boom"]), "reports errors"),
            (lambda r: s(r, "task", "other"), "task 'other'"),
            (lambda r: s(r, "stages", "source", "sha256", "0" * 64), "not about this .sv"),
            (lambda r: s(r, "stages", "source", "findings", ["`ifdef"]), "source gate"),
            (lambda r: r.pop("score"), "no score"),
            (lambda r: s(r, "score", "params", {"N": 8}), "scoring point"),
            (lambda r: s(r, "stages", "score", "gated", False), "not gated"),
            (lambda r: r["stages"].pop("postsynth"), "post-synthesis"),
            (lambda r: s(r, "stages", "postsynth", "mismatches", 3), "post-synthesis"),
            (lambda r: s(r, "stages", "comparator", "result", "axioms", ["propext", "evil"]),
             "axioms outside"),
            (lambda r: r["stages"].pop("comparator"), "comparator"),
            (lambda r: s(r, "stages", "solution", "exit", 1), "solution stage"),
            (lambda r: s(r, "stages", "integrity", "changed", ["x"]), "integrity"),
            (lambda r: s(r, "stages", "leanchecker", "exit", 1), "leanchecker"),
        ]
        for mutate, frag in cases:
            self.assertIn(frag, self.refusals(mutate), frag)

    def test_depth_budget_is_a_refusal(self):
        task = toy_task(scoring={"params": {"N": 16}, "depth_budget": 5})
        self.assertIn("exceeds the task's depth budget 5", self.refusals(lambda r: None, task))

    def test_human_fields_refused_together(self):
        with self.assertRaises(lb.Refused) as cm:
            lb.build_record(toy_task(), fake_result(), player="bad player!", assisted_by="claude",
                            notes="x" * 5000, submitted_at="soon", sv_name="a.sv",
                            sv_bytes=SV_TEXT, lean_name="a.lean", lean_bytes=LEAN_TEXT,
                            environment=ENV)
        text = " | ".join(cm.exception.problems)
        for frag in ("player handle", "assisted_by must be a list", "notes", "submitted_at"):
            self.assertIn(frag, text)

    def test_add_refuses_rejected_submission_and_writes_nothing(self):
        env = CliEnv(self)
        res = fake_result()
        res["accepted"], res["stage"], res["errors"] = False, "solution", ["does not compile"]
        rc, out, err = env.add("alice", from_check=env.write_result(res))
        self.assertEqual(rc, 1)
        self.assertIn("REFUSED", err)
        self.assertIn("did not accept", err)
        self.assertFalse(os.path.exists(env.data))

    def test_acceptance_needs_the_trusted_build_and_the_tasks_own_limit(self):
        """The board's own kernel check (the universal-correctness audit, F7): a result made with
        `--no-trusted-build` (no `stages.trusted`), under another `--time-limit`, stopped at a limit, or marked
        INCOMPLETE by check.py cannot enter a record."""
        def problems(change):
            res = fake_result()
            change(res)
            return " | ".join(lb.acceptance_problems(res, toy_task(), SV_SHA))
        self.assertEqual(problems(lambda r: None), "")
        self.assertIn("--no-trusted-build", problems(lambda r: r["stages"].pop("trusted")))
        self.assertIn("--no-trusted-build", problems(lambda r: r["stages"]["trusted"].update(exit=1)))
        self.assertIn("not the task's 600 CPU s", problems(lambda r: r["stages"]["solution"].update(time_limit_s=20)))
        self.assertIn("not the task's", problems(lambda r: r["stages"]["solution"].pop("time_limit_s")))
        self.assertIn("over the task's 600 s limit",
                      problems(lambda r: r["stages"]["solution"].update(cpu_seconds=600.5)))
        self.assertIn("stopped at its cpu limit", problems(lambda r: r["stages"]["solution"].update(stopped_by="cpu")))
        self.assertIn("INCOMPLETE: --no-score",
                      problems(lambda r: r.update(complete=False, incomplete=["--no-score: no score"])))
        self.assertIn("INCOMPLETE", problems(lambda r: r.update(complete=False)))

    def test_the_boards_own_data_directory_takes_only_its_own_sandboxed_check(self):
        """F7: `add --from-check` and `add --sandbox off` are refused for the board's own data directory
        (leaderboard/data, here a temporary one standing in for it) and stay available for a `--data-dir`
        trial; a live `add` there needs a check that ran in the OS sandbox (`sandbox.active`)."""
        env = CliEnv(self)
        sv_sha = lb.sha256_bytes(SV_TEXT + b"// alice\n")       # what CliEnv.files writes
        res = env.write_result(fake_result(sv_sha=sv_sha))
        with mock.patch.object(lb, "DEFAULT_DATA", env.data):
            rc, out, err = env.add("alice", from_check=res)
            self.assertEqual(rc, 1)
            self.assertIn("--from-check records a stored check.py result", err)
            rc, out, err = env.add("alice", extra=("--sandbox", "off"))
            self.assertEqual(rc, 1)
            self.assertIn("--sandbox off", err)
            self.assertFalse(os.path.exists(env.data))
            with mock.patch.dict(os.environ, {"FAKE_SANDBOX": "inactive"}):
                rc, out, err = env.add("alice", extra=("--sandbox", "auto"))
            self.assertEqual(rc, 1)
            self.assertIn("did not run in the OS sandbox", err)
            self.assertFalse(os.path.exists(env.data))
            rc, out, err = env.add("alice")                      # the default: `--sandbox require`, active
            self.assertEqual(rc, 0, err)
        # elsewhere (a trial) both stay available
        rc, out, err = env.add("bob", from_check=env.write_result(fake_result(sv_sha=lb.sha256_bytes(
            SV_TEXT + b"// bob\n"))))
        self.assertEqual(rc, 0, err)
        rc, out, err = env.add("carol", extra=("--sandbox", "off"))
        self.assertEqual(rc, 0, err)

    def test_from_check_bound_to_the_file(self):
        env = CliEnv(self)
        res = fake_result(sv_sha="0" * 64)      # a result about some other design
        rc, out, err = env.add("alice", from_check=env.write_result(res))
        self.assertEqual(rc, 1)
        self.assertIn("not about this .sv", err)



class PostsynthModeTest(Tmp):
    """WP-C2: the post-synthesis mode in results, records, `add`, `verify` and the boards."""

    def light_refusal(self, res, postsynth="full"):
        with self.assertRaises(lb.Refused) as cm:
            lb.build_record(toy_task(), res, player="alice", assisted_by=[], notes="",
                            submitted_at="2026-10-29", sv_name="a.sv", sv_bytes=SV_TEXT,
                            lean_name="a.lean", lean_bytes=LEAN_TEXT, environment=ENV,
                            postsynth=postsynth)
        return " | ".join(cm.exception.problems)

    def test_a_result_with_no_mode_is_a_full_check(self):
        ps = make_record()["postsynth"]
        self.assertEqual((ps["mode"], ps["full_vectors"], ps["vectors"]), ("full", 500, 500))
        self.assertEqual(lb.record_mode({}), "full")
        self.assertEqual(lb.validate_record(make_record()), [])

    def test_full_and_light_records(self):
        full = make_record(res=fake_result(mode="full"))
        self.assertEqual((full["postsynth"]["mode"], full["postsynth"]["vectors"],
                          full["postsynth"]["full_vectors"]), ("full", 500, 500))
        light = make_record(res=fake_result(mode="light"), postsynth="light")
        self.assertEqual((light["postsynth"]["mode"], light["postsynth"]["vectors"],
                          light["postsynth"]["full_vectors"]), ("light", 120, 500))
        self.assertEqual(lb.validate_record(light), [])
        self.assertNotEqual(light["record_hash"], full["record_hash"])
        # a full result is fine for a record that would have accepted a light one
        self.assertEqual(make_record(res=fake_result(mode="full"),
                                     postsynth="light")["postsynth"]["mode"], "full")

    def test_a_light_result_is_refused_for_an_official_record(self):
        msg = self.light_refusal(fake_result(mode="light"))
        self.assertIn("LIGHT mode", msg)
        self.assertIn("--postsynth full", msg)
        self.assertIn("add --postsynth light", msg)

    def test_bad_modes_are_refused(self):
        self.assertIn("neither 'light' nor 'full'", self.light_refusal(fake_result(mode="medium"),
                                                                       "light"))
        self.assertIn("postsynth 'medium' is neither", self.light_refusal(fake_result(mode="full"),
                                                                           "medium"))

    def test_validate_record_mode(self):
        rec = make_record(res=fake_result(mode="light"), postsynth="light")
        bad = copy.deepcopy(rec)
        bad["postsynth"]["mode"] = "medium"
        self.assertTrue(any("postsynth.mode" in p for p in lb.validate_record(bad)))
        bad = copy.deepcopy(rec)
        bad["postsynth"]["full_vectors"] = -1
        self.assertTrue(any("full_vectors" in p for p in lb.validate_record(bad)))
        legacy = copy.deepcopy(rec)
        del legacy["postsynth"]["mode"], legacy["postsynth"]["full_vectors"]
        self.assertEqual(lb.validate_record(legacy), [])      # the committed records' shape

    def test_boards_mark_light_records(self):
        task = toy_task()
        full = make_record(task, "fulla", res=fake_result(mode="full", gates={"AND": 12}), sky=(120000, 900))
        light = make_record(task, "lighta", res=fake_result(mode="light", gates={"AND": 10}),
                            postsynth="light", sky=(100000, 900))
        board = lb.build_board(task, [full, light], flow=FLOW)
        # a light check is incomplete: the record is listed, marked, and NEVER ranked (even with the better score)
        by = {r["player"]: r["postsynth"] for r in board["frontier"] + board["dominated"]}
        self.assertEqual(by, {"fulla": "full"})
        (un,) = board["unranked"]
        self.assertEqual((un["player"], un["postsynth"]), ("lighta", "light"))
        self.assertIn("LIGHT", un["reason"])
        self.assertIn("never ranks", un["reason"])
        md = lb.render_markdown(board)
        self.assertIn(f"`{light['record_hash'][:12]}` light |", md)
        self.assertNotIn(f"`{full['record_hash'][:12]}` light", md)
        self.assertIn(lb.LIGHT_NOTE, md)
        self.assertIn("never ranks", lb.render_pareto_text(board))
        only_full = lb.render_markdown(lb.build_board(task, [full], flow=FLOW))
        self.assertNotIn("light", only_full)

    def test_verify_notes_a_light_record(self):
        rec = make_record(res=fake_result(mode="light"), postsynth="light")
        self.store(rec)
        r = lb.verify_record(lb.record_paths(self.data, "toy", rec["record_hash"])[0], rec,
                             toy_task(), flow=FLOW)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertTrue(any("LIGHT mode" in n for n in r.notes), r.notes)


class ParetoTest(unittest.TestCase):
    """The frontier over the ranked pair (sky130 area `area_e4um2`, time `time_ps`). A row carries the same two
    numbers as `area_mge` and `depth` too, so that score.py's (area, depth) `--pareto` can cross-check the filter;
    BoardTest.test_the_board_ranks_sky130_not_ge shows the board reading the sky130 pair, not those."""
    @staticmethod
    def row(area, time, player="p", date="2026-10-29", h=None):
        return {"area_e4um2": area, "time_ps": time, "cycles": None, "period_ps": None,
                "area_mge": area, "depth": time, "player": player, "submitted_at": date,
                "record_hash": h or f"{area:08d}{time:04d}{player}".ljust(64, "0"),
                "assisted_by": [], "proof_lines": 1}

    def test_dominance_and_ties(self):
        rows = [self.row(100, 10, "a"), self.row(90, 12, "b"), self.row(110, 8, "c"),
                self.row(95, 12, "d"), self.row(100, 10, "e"), self.row(120, 8, "f"),
                self.row(90, 12, "g")]
        front = lb.pareto(rows)
        self.assertEqual([(r["area_e4um2"], r["time_ps"], r["player"]) for r in front],
                         [(90, 12, "b"), (90, 12, "g"), (100, 10, "a"), (100, 10, "e"),
                          (110, 8, "c")])
        layers = lb.pareto_layers(rows)
        self.assertEqual([[(r["area_e4um2"], r["time_ps"]) for r in layer] for layer in layers],
                         [[(90, 12), (90, 12), (100, 10), (100, 10), (110, 8)],
                          [(95, 12), (120, 8)]])
        self.assertTrue(lb.dominates(self.row(90, 12), self.row(90, 13)))
        self.assertTrue(lb.dominates(self.row(90, 12), self.row(91, 12)))
        self.assertFalse(lb.dominates(self.row(90, 12), self.row(90, 12)))
        self.assertFalse(lb.dominates(self.row(90, 13), self.row(91, 12)))

    def test_same_area_different_depth(self):
        front = lb.pareto([self.row(100, 12, "slow"), self.row(100, 10, "fast")])
        self.assertEqual([r["player"] for r in front], ["fast"])

    def test_empty_and_single(self):
        self.assertEqual(lb.pareto([]), [])
        self.assertEqual(lb.pareto_layers([]), [])
        r = self.row(5, 5)
        self.assertEqual(lb.pareto([r]), [r])

    def test_deterministic_under_permutation(self):
        rng = random.Random(7)
        rows = [self.row(rng.randint(1, 8) * 10, rng.randint(1, 6), f"p{i}",
                         f"2026-10-{rng.randint(1, 28):02d}") for i in range(40)]
        want = [r["record_hash"] for r in lb.pareto(rows)]
        want_layers = [[r["record_hash"] for r in layer] for layer in lb.pareto_layers(rows)]
        for _ in range(10):
            rng.shuffle(rows)
            self.assertEqual([r["record_hash"] for r in lb.pareto(rows)], want)
            self.assertEqual([[r["record_hash"] for r in layer] for layer in lb.pareto_layers(rows)],
                             want_layers)

    def test_agrees_with_score_py(self):
        """The frontier is score.py's `--pareto`, as a set (this one orders ties
        and breaks nothing else)."""
        rng = random.Random(11)
        for _ in range(20):
            rows = [self.row(rng.randint(1, 6), rng.randint(1, 6), f"p{i}") for i in range(15)]
            mine = {r["record_hash"] for r in lb.pareto(rows)}
            theirs = {r["record_hash"] for r in score.pareto(rows)}
            self.assertEqual(mine, theirs)

    def test_layers_partition_and_each_layer_is_a_frontier(self):
        rng = random.Random(3)
        rows = [self.row(rng.randint(1, 9), rng.randint(1, 9), f"p{i}") for i in range(30)]
        layers = lb.pareto_layers(rows)
        self.assertEqual(sorted(r["record_hash"] for layer in layers for r in layer),
                         sorted(r["record_hash"] for r in rows))
        rest = list(rows)
        for layer in layers:
            self.assertEqual({r["record_hash"] for r in lb.pareto(rest)},
                             {r["record_hash"] for r in layer})
            gone = {r["record_hash"] for r in layer}
            rest = [r for r in rest if r["record_hash"] not in gone]

    def test_earlier_date_listed_first_among_equals(self):
        rows = [self.row(100, 10, "late", "2026-11-02"), self.row(100, 10, "early", "2026-10-30")]
        self.assertEqual([r["player"] for r in lb.pareto(rows)], ["early", "late"])


class BoardTest(unittest.TestCase):
    """The default board: ranked by area x time, the sky130 A0' area times the time. `recs` gives each record a sky130
    score in the order of its GE score (area = ANDs x 1 um^2, time = depth x 100 ps); test_the_board_ranks_sky130_not_ge
    pulls the two apart, test_the_board_ranks_area_x_time_not_the_pareto_layer the product and the frontier."""
    def recs(self, task, specs):
        out = []
        for player, ands, depth, date in specs:
            out.append(make_record(task, player, date=date, gates={"AND": ands}, depth=depth,
                                   sky=(ands * 10000, depth * 100)))
        return out

    def test_effective_depth_budget(self):
        self.assertIsNone(lb.effective_depth_budget(toy_task()))
        self.assertEqual(lb.effective_depth_budget(toy_task(leaderboard={"depth_budget": 40})), 40)
        hard = toy_task(scoring={"params": {"N": 16}, "depth_budget": 30})
        self.assertEqual(lb.effective_depth_budget(hard), 30)
        both = toy_task(scoring={"params": {"N": 16}, "depth_budget": 30},
                        leaderboard={"depth_budget": 20})
        self.assertEqual(lb.effective_depth_budget(both), 20)
        both = toy_task(scoring={"params": {"N": 16}, "depth_budget": 30},
                        leaderboard={"depth_budget": 50})
        self.assertEqual(lb.effective_depth_budget(both), 30)
        self.assertIsNone(lb.effective_depth_budget(toy_task(leaderboard={"depth_budget": None})))

    def test_no_budget_by_default(self):
        task = toy_task()
        board = lb.build_board(task, self.recs(task, [("a", 10, 20, "2026-10-29")]), flow=FLOW)
        self.assertIsNone(board["depth_budget"])
        self.assertIsNone(board["budget_ranking"])
        md = lb.render_markdown(board)
        self.assertIn("Depth budget: none.", md)
        self.assertNotIn("Best area under", md)

    def test_budget_ranking(self):
        task = toy_task(leaderboard={"depth_budget": 20})
        specs = [("a", 100, 20, "2026-10-01"), ("b", 90, 25, "2026-10-02"),   # b is over budget
                 ("c", 110, 18, "2026-10-03"), ("d", 100, 20, "2026-10-04"),  # d ties a
                 ("e", 105, 19, "2026-10-05"), ("f", 130, 18, "2026-10-06")]  # f dominated
        board = lb.build_board(task, self.recs(task, specs), flow=FLOW)
        self.assertEqual(board["depth_budget"], 20)
        br = board["budget_ranking"]
        # by area x time (area = ANDs um^2, time = depth x 100 ps): c 110 x 1800 < e 105 x 1900 < a = d 100 x 2000
        # < f 130 x 1800, ties sharing a rank; b (90 x 2500) is over the budget
        self.assertEqual([(r["player"], r["rank"], r["over_budget"]) for r in br],
                         [("c", 1, False), ("e", 2, False), ("a", 3, False), ("d", 3, False),
                          ("f", 5, False), ("b", None, True)])
        # the board itself ranks every entry by area x time, the budget only flags; the layer is exploration
        self.assertEqual([(r["player"], r["rank"], r["layer"], r["over_budget"]) for r in board["ranking"]],
                         [("c", 1, 1, False), ("e", 2, 1, False), ("a", 3, 1, False), ("d", 3, 1, False),
                          ("b", 5, 1, True), ("f", 6, 2, False)])
        # the frontier is independent of the budget: b is on it, flagged
        front = {r["player"]: r["over_budget"] for r in board["frontier"]}
        self.assertEqual(front, {"b": True, "a": False, "e": False, "c": False, "d": False})
        self.assertEqual([r["player"] for r in board["dominated"]], ["f"])

    def test_hard_budget_flags_old_records(self):
        """A record made before the task got a (hard) budget is listed, flagged."""
        old = toy_task()
        recs = self.recs(old, [("a", 100, 40, "2026-10-01"), ("b", 120, 30, "2026-10-02")])
        task = toy_task(scoring={"params": {"N": 16}, "depth_budget": 35})
        board = lb.build_board(task, recs, flow=FLOW)
        self.assertEqual([(r["player"], r["rank"]) for r in board["budget_ranking"]],
                         [("b", 1), ("a", None)])

    def test_stale_flow_and_offpoint_are_not_ranked(self):
        task = toy_task()
        fresh = make_record(task, "fresh", gates={"AND": 10}, sky=(100000, 1000))
        stale = make_record(task, "stale", res=fake_result(gates={"AND": 5}, depth=1,
                                                           flow=dict(FLOW, script_sha256="9" * 64)), sky=(50000, 100))
        off = make_record(task, "off", res=fake_result(gates={"AND": 5}, depth=1), sky=(50000, 100))
        off["score"]["scoring_point"] = {"N": 8}      # e.g. the task's point moved since
        off["record_hash"] = lb.compute_record_hash(off)
        board = lb.build_board(task, [fresh, stale, off], flow=FLOW)
        self.assertEqual([r["player"] for r in board["frontier"]], ["fresh"])
        self.assertEqual(sorted((r["player"], r["reason"].split(" (")[0].split(",")[0])
                                for r in board["unranked"]),
                         [("off", "scored at {'N': 8}"), ("stale", "checked under another flow")])
        # with no flow given (--all-flows) the stale one is ranked (the off-point one never is)
        board = lb.build_board(task, [fresh, stale, off], flow=None)
        self.assertEqual([r["player"] for r in board["frontier"]], ["stale"])

    def test_the_board_ranks_sky130_not_ge(self):
        """Decided 11/03: sky130 A0' ranks (area um^2, time ps); GE and depth are extra columns. `ge` is the better GE
        score and the worse sky130 one; `old` has the best GE score and no sky130 columns at all."""
        task = toy_task()
        ge = make_record(task, "ge", gates={"AND": 5}, depth=5, sky=(90000, 900))
        sky = make_record(task, "sky", gates={"AND": 9}, depth=9, sky=(80000, 800))
        old = make_record(task, "old", gates={"AND": 1}, depth=1)
        board = lb.build_board(task, [ge, sky, old], flow=FLOW)
        self.assertEqual(board["ranked_axes"], ["area_um2_sky130", "time_ps"])
        self.assertEqual([(r["player"], r["layer"]) for r in board["frontier"] + board["dominated"]],
                         [("sky", 1), ("ge", 2)])
        self.assertEqual([(r["rank"], r["player"], r["exact"]) for r in board["ranking"]],
                         [(1, "sky", 80000 * 800), (2, "ge", 90000 * 900)])
        (un,) = board["unranked"]
        self.assertEqual(un["player"], "old")
        self.assertIn("no sky130 columns (a record made before them): not ranked until it is backfilled", un["reason"])
        # --all-flows ranks every flow, but never a record without the columns
        self.assertEqual([r["player"] for r in lb.build_board(task, [ge, sky, old], flow=None)["unranked"]], ["old"])
        md = lb.render_markdown(board)
        self.assertIn("| # | player | assisted by | area x time (um2*ns) | area (um^2) | time (ps) | layer | area (GE) | "
                      "depth |", md)
        self.assertIn("| 1 | sky | none | 6.40 | 8.0000 | 800 | 1 | 11.997 | 9 |", md)
        self.assertIn("| old | - | - | 1.333 | 1 |", md)
        text = lb.render_pareto_text(board)
        self.assertIn("Pareto frontier of (sky130 area, time) at N=16 (1 of 2 ranked records)", text)
        self.assertIn("not ranked (1):", text)
        # a design the pinned flow could not weigh is not ranked either, with the reason
        res = fake_result(gates={"AND": 2}, depth=2)
        res["ppa"], res["stages"]["ppa"] = {"available": False, "reason": "no cell"}, {"mode": "require"}
        unw = make_record(task, "unw", res=res)
        (un,) = lb.build_board(task, [unw], flow=FLOW)["unranked"]
        self.assertIn("the sky130 columns were not computed: no cell", un["reason"])

    def test_the_board_ranks_area_x_time_not_the_pareto_layer(self):
        """Decided 2026-11-05: area x time is the one ranked number. `w` is dominated by `y` (layer 2) and still ranks
        above `x`, which is on the frontier; the `#` column is the rank, the layer an exploration column."""
        task = toy_task()
        x = make_record(task, "x", gates={"AND": 3}, sky=(100000, 1000))     # 10 um^2 x 1000 ps = 10 um2*ns
        y = make_record(task, "y", gates={"AND": 4}, sky=(1000000, 50))      # 100 um^2 x 50 ps = 5
        w = make_record(task, "w", gates={"AND": 5}, sky=(1010000, 60))      # 101 um^2 x 60 ps = 6.06, dominated by y
        board = lb.build_board(task, [x, y, w], flow=FLOW)
        self.assertEqual([(r["rank"], r["player"], r["layer"]) for r in board["ranking"]],
                         [(1, "y", 1), (2, "w", 2), (3, "x", 1)])
        self.assertEqual([r["player"] for r in board["frontier"]], ["x", "y"])      # exploration: area order
        self.assertEqual([r["player"] for r in board["dominated"]], ["w"])
        md = lb.render_markdown(board)
        rows = [ln for ln in md.splitlines() if ln.startswith("| ") and not ln.startswith("| #")]
        self.assertEqual([ln.split(" | ")[:2] for ln in rows], [["| 1", "y"], ["| 2", "w"], ["| 3", "x"]])
        self.assertIn("| 2 | w | none | 6.06 | 101.0000 | 60 | 2 |", md)
        text = lb.render_pareto_text(board)
        self.assertIn("(2 of 3 ranked records), exploration: the board ranks area x time", text)
        self.assertRegex(text, r"\n  3 +10\.00 +10\.0000 +1000 .* x ")
        self.assertRegex(text, r"\n  1 +5\.00 +100\.0000 +50 .* y ")

    def test_equal_area_x_time_shares_a_rank_and_breaks_ties_as_the_site(self):
        """Equal products share a rank (1, 1, 3) and are listed as the site lists them (site/build.py `score_key`): the
        smaller area in GE first, then the smaller depth, then the earlier date, then the record hash."""
        task = toy_task()
        big = make_record(task, "big", gates={"AND": 9}, depth=3, sky=(200000, 1000))        # 20 x 1000 = 20
        small = make_record(task, "small", gates={"AND": 2}, depth=9, sky=(400000, 500), date="2026-11-03")  # 40 x 500
        late = make_record(task, "late", gates={"AND": 2}, depth=9, sky=(100000, 2000), date="2026-11-02")
        early = make_record(task, "early", gates={"AND": 2}, depth=9, sky=(100000, 2000), date="2026-10-30")
        shallow = make_record(task, "shallow", gates={"AND": 2}, depth=4, sky=(1000000, 200))
        worse = make_record(task, "worse", gates={"AND": 1}, depth=1, sky=(200001, 1000))
        board = lb.build_board(task, [worse, late, big, early, small, shallow], flow=FLOW)
        self.assertEqual([(r["rank"], r["player"]) for r in board["ranking"]],
                         [(1, "shallow"), (1, "early"), (1, "late"), (1, "small"), (1, "big"), (6, "worse")])
        self.assertEqual(len({r["exact"] for r in board["ranking"][:5]}), 1)

    def test_identity_and_input_drive_decide_comparability(self):
        """Columns of another ppa_version/liberty/pins than the current ones, or weighed under another input drive than
        the task's, are not ranked with the current ones (when `identity` / `input_drive` are given: the CLI gives
        them unless --all-flows)."""
        task = toy_task()
        cur = {"ppa_version": "sky130_a0_v1", "liberty_sha256": "a" * 64, "ppa_pins_sha256": "b" * 64}
        a = make_record(task, "a", gates={"AND": 5}, sky=(90000, 900))
        res = with_ppa(fake_result(gates={"AND": 4}), area_e4=10000, delay_ps=100, ppa_version="sky130_a0_v0")
        old_version = make_record(task, "v0", res=res)
        res = with_ppa(fake_result(gates={"AND": 3}), area_e4=10000, delay_ps=100)
        res["ppa"]["setup"]["input_drive"] = BUF1
        buf1 = make_record(task, "buf1", res=res)
        board = lb.build_board(task, [a, old_version, buf1], flow=FLOW, identity=cur, input_drive=BUF8)
        self.assertEqual([r["player"] for r in board["frontier"]], ["a"])
        why = {r["player"]: r["reason"] for r in board["unranked"]}
        self.assertIn("sky130 columns computed under another version (ppa_version differ)", why["v0"])
        self.assertIn("another input drive (sky130_fd_sc_hd__buf_1; the task's input drive is now "
                      "sky130_fd_sc_hd__buf_8)", why["buf1"])
        self.assertIn(f"Input drive: `{BUF8}`.", lb.render_markdown(board))
        board = lb.build_board(task, [a, old_version, buf1], flow=FLOW)     # nothing given: all three ranked
        self.assertEqual(board["unranked"], [])

    def test_a_clocked_record_ranks_by_cycles_times_period(self):
        """A clocked record's time is check.py's clocked `time_ps` = cycles x the register-to-register period (the
        `ppa` block's `delay_ps_sky130`), never the period alone; validate_record holds the three together. Since the
        clocked record format (decided 2026-11-07) a clocked record is the record of a clocked task, so the board is a
        tx-family task's (a one-cycle record with the longer period beats the four-cycle one), and a combinational
        record on it is not ranked."""
        task = clocked_task()
        slow = make_record(task, "clk4", res=fake_clocked_result(task, period=1000, latency=4))   # 4 cycles x 1000 ps
        fast = make_record(task, "clk1", res=fake_clocked_result(task, period=3000, latency=1))   # 1 cycle x 3000 ps
        comb = make_record(toy_task(), "comb", gates={"AND": 5}, sky=(90000, 3000))
        self.assertEqual(lb.validate_record(slow), [])
        self.assertEqual(lb.ranked_columns(slow), {"area_e4um2": 90000, "time_ps": 4000, "cycles": 4, "period_ps": 1000})
        board = lb.build_board(task, [slow, fast, comb], flow=SEQ)
        self.assertEqual([r["player"] for r in board["frontier"]], ["clk1"])
        self.assertEqual([r["player"] for r in board["dominated"]], ["clk4"])
        self.assertEqual([(r["player"], r["reason"]) for r in board["unranked"]],
                         [("comb", "scored under the comb flow, and a tx-family task is scored under the seq flow "
                                   "(svgolf_seq.ys, ge_seq.json)")])
        self.assertIn("| 4000 (4 x 1000) |", lb.render_markdown(board))
        for k, v, why in (("time_ps", 3000, "is not cycles x period_ps"), ("period_ps", 999, "is not ppa.delay_ps"),
                          ("area_um2", 8.0, "is not ppa.area_um2_sky130"), ("cycles", 0, "positive integer")):
            bad = copy.deepcopy(slow)
            bad["score"][k] = v
            self.assertTrue(any(why in p for p in lb.validate_record(bad)), (k, lb.validate_record(bad)))
        bad = copy.deepcopy(slow)
        del bad["score"]["cycles"]
        self.assertTrue(any("a clocked score has all of" in p for p in lb.validate_record(bad)))
        bad = copy.deepcopy(slow)
        del bad["ppa"]
        self.assertTrue(any("needs its numeric `ppa` block" in p for p in lb.validate_record(bad)))

    def test_other_tasks_records_ignored(self):
        task = toy_task()
        rec = make_record(toy_task(name="other"), "x", res=fake_result(task="other"))
        self.assertEqual(lb.build_board(task, [rec], flow=FLOW)["frontier"], [])

    def test_assisted_by_handling(self):
        self.assertEqual(lb.normalize_assisted_by(None), [])
        self.assertEqual(lb.normalize_assisted_by([]), [])
        self.assertEqual(lb.normalize_assisted_by(["  Claude  (Anthropic) ", "", "Claude (Anthropic)",
                                                   "a proof assistant"]),
                         ["Claude (Anthropic)", "a proof assistant"])
        for bad in ("Claude", [1], ["a\nb"], ["x" * 500], ["t"] * 0 + [str(i) for i in range(40)]):
            with self.assertRaises(lb.Refused):
                lb.normalize_assisted_by(bad)
        task = toy_task()
        recs = self.recs(task, [("a", 10, 20, "2026-10-01"), ("b", 9, 25, "2026-10-02")])
        recs[1] = make_record(task, "b", assisted=["Claude | the `best`"], gates={"AND": 9},
                              depth=25, date="2026-10-02", sky=(90000, 2500))
        both = lb.build_board(task, recs, flow=FLOW)
        self.assertEqual([r["player"] for r in both["frontier"]], ["b", "a"])
        only = lb.build_board(task, recs, flow=FLOW, unassisted=True)
        self.assertEqual([r["player"] for r in only["frontier"]], ["a"])
        self.assertTrue(only["unassisted_only"])
        md = lb.render_markdown(both)
        self.assertIn(r"Claude \| the \`best\`", md)      # table-safe
        self.assertNotIn("Claude | the", md)

    def test_markdown_golden(self):
        task = toy_task(leaderboard={"depth_budget": 20})
        specs = [("alice", 10, 20, "2026-10-01", ()), ("bob", 9, 25, "2026-10-02", ("Claude (Anthropic)",)),
                 ("carol", 12, 18, "2026-10-03", ("Claude (Anthropic)", "a proof assistant")),
                 ("dave", 11, 21, "2026-10-04", ()), ("erin", 10, 20, "2026-10-05", ()),
                 ("fay", 7, 30, "2026-10-06", ("a | b",))]
        # the sky130 score follows the GE one here (area 50 x milli-GE in 1e-4 um^2, time 120 ps per level)
        recs = [make_record(task, p, assisted=a, date=d, gates={"AND": n, "XOR": 2}, depth=dp,
                            res=fake_result(gates={"AND": n, "XOR": 2}, depth=dp, flow=GOLD_FLOW,
                                            ge=GOLD_GE), sky=((1333 * n + 4000) * 50, dp * 120))
                for p, n, dp, d, a in specs]
        stale = make_record(task, "gina", res=fake_result(
            gates={"AND": 1}, depth=1, flow=dict(GOLD_FLOW, script_sha256="8" * 64), ge=GOLD_GE),
            sky=(66650, 120))
        nocols = make_record(task, "hal", res=fake_result(gates={"AND": 2}, depth=2, flow=GOLD_FLOW, ge=GOLD_GE))
        board = lb.build_board(task, recs + [stale, nocols], flow=GOLD_FLOW)
        text = lb.render_export([board, lb.build_board(toy_task(name="empty", title=""), [],
                                                       flow=GOLD_FLOW)])
        if os.environ.get("UPDATE_GOLDEN"):
            with open(GOLDEN, "w") as fh:
                fh.write(text)
        with open(GOLDEN) as fh:
            self.assertEqual(text, fh.read())


class LeanFactsTest(unittest.TestCase):
    def test_code_lines(self):
        self.assertEqual(lb.lean_code_lines(""), 0)
        self.assertEqual(lb.lean_code_lines("\n\n  \n"), 0)
        self.assertEqual(lb.lean_code_lines(LEAN_TEXT.decode()), 7)
        text = '\n'.join([
            "import A",                           # 1
            "/- block",                           # (comment)
            "   /- nested -/ still comment",     # (comment)
            "-/ def x := 1",                      # 2: code after the closing
            "/-- doc -/",                         # (comment)
            "theorem t : True := by",             # 3
            '  have : "--not a comment" = "--not a comment" := rfl',   # 4
            "  trivial -- comment",               # 5
            "-- only comment",
            "  -- indented comment",
            "def c := '\"'",                      # 6: a char literal holding a quote
            "def d := \"a /- not a block\"",      # 7
            "def e' := x'",                       # 8: primes in names
        ])
        self.assertEqual(lb.lean_code_lines(text), 8)

    def test_imports_and_tactics(self):
        text = ("import Submission.Design\nimport LeanModels.Sv.CombEqTactic\n"
                "/- import Fake.Commented -/\nimport  SvGolf.Comb\n\nnamespace S\n"
                "theorem x : True := by\n  sv_equations\n  simp\n  decide +kernel\n"
                "  -- bv_decide mentioned in a comment only\n  have h := foo.omega_lt\n")
        self.assertEqual(lb.lean_imports(text),
                         ["Submission.Design", "LeanModels.Sv.CombEqTactic", "SvGolf.Comb"])
        self.assertEqual(lb.lean_tactics(text), ["decide", "simp", "sv_equations"])

    def test_comb_flags(self):
        res = fake_result()
        res["stages"]["imports"]["imports"] = ["Submission.Design", "LeanModels.Sv.CombEqTactic"]
        rec = make_record(res=res)
        self.assertFalse(rec["proof"]["uses_comb_view"])
        self.assertTrue(rec["proof"]["uses_comb_eq"])
        res["stages"]["imports"]["imports"] = ["Submission.Design", "LeanModels.Sv.Comb2"]
        rec = make_record(res=res)
        self.assertFalse(rec["proof"]["uses_comb_view"] or rec["proof"]["uses_comb_eq"])


class TaskFieldTest(unittest.TestCase):
    def test_field_validation(self):
        self.assertEqual(lb.task_leaderboard_problems(toy_task()), [])
        self.assertEqual(lb.task_leaderboard_problems(toy_task(leaderboard={"depth_budget": 12})), [])
        self.assertEqual(lb.task_leaderboard_problems(
            toy_task(leaderboard={"depth_budget": None, "_comment": "x"})), [])
        for bad in ({"depth_budget": 0}, {"depth_budget": "7"}, {"depth_budget": True},
                    {"depth_budget": 2.5}, {"budget": 3}, [1]):
            self.assertTrue(lb.task_leaderboard_problems(toy_task(leaderboard=bad)), bad)

    def test_real_tasks_are_valid(self):
        for t in lb.all_task_names(lb.DEFAULT_TASKS):
            task = lb.load_task(lb.DEFAULT_TASKS, t)      # raises on a bad `leaderboard`
            self.assertIsInstance(lb.scoring_point(task), dict)
            b = lb.effective_depth_budget(task)
            self.assertTrue(b is None or isinstance(b, int))


class CliEnv:
    """A temporary tasks dir with one synthetic task, a data dir and a FAKE
    check.py that prints a canned result for the .sv it is given."""

    def __init__(self, case):
        self.case = case
        self.tmp = case.tmp
        self.tasks = os.path.join(self.tmp, "tasks")
        self.data = os.path.join(self.tmp, "data")
        os.makedirs(os.path.join(self.tasks, "toy"))
        with open(os.path.join(self.tasks, "toy", "task.json"), "w") as fh:
            json.dump(toy_task(leaderboard={"depth_budget": 22}), fh)
        self.fake = os.path.join(self.tmp, "fake_check.py")
        with open(self.fake, "w") as fh:
            fh.write(FAKE_CHECK.replace("@TEMPLATE@", json.dumps(fake_result()))
                     .replace("@IDENT@", json.dumps(lb.ppa_identity() or {})))
        self.n = 0

    def write_result(self, res):
        p = os.path.join(self.tmp, f"result{self.n}.json")
        self.n += 1
        with open(p, "w") as fh:
            json.dump(res, fh)
        return p

    def files(self, tag):
        sv = os.path.join(self.tmp, f"{tag}.sv")
        lean = os.path.join(self.tmp, f"{tag}.lean")
        with open(sv, "wb") as fh:
            fh.write(SV_TEXT + f"// {tag}\n".encode())
        with open(lean, "wb") as fh:
            fh.write(LEAN_TEXT)
        return sv, lean

    def run(self, *argv):
        return quiet(lb.main, list(argv[:1]) + ["--data-dir", self.data, "--tasks-dir", self.tasks,
                                                 "--check-py", self.fake] + list(argv[1:]))

    def add(self, player, *, tag=None, assisted=(), from_check=None, date="2026-10-29", extra=()):
        sv, lean = self.files(tag or player)
        argv = ["add", "--task", "toy", "--player", player, "--sv", sv, "--lean", lean,
                "--date", date] + list(extra)
        for a in assisted:
            argv += ["--assisted-by", a]
        if from_check:
            argv += ["--from-check", from_check]
        return self.run(*argv)


FAKE_CHECK = '''import hashlib, json, os, sys
res = json.loads(r"""@TEMPLATE@""")
mode = os.environ.get("FAKE_MODE", "accept")
sv = open(sys.argv[2], "rb").read()
res["stages"]["source"]["sha256"] = hashlib.sha256(sv).hexdigest()
if os.environ.get("FAKE_ARGV_LOG"):
    with open(os.environ["FAKE_ARGV_LOG"], "a") as fh:
        fh.write(" ".join(sys.argv[3:]) + "\\n")
if "--postsynth" in sys.argv:     # a current check.py writes the mode it ran in
    ps = res["stages"]["postsynth"]
    ps["mode"] = sys.argv[sys.argv.index("--postsynth") + 1]
    ps["full_vectors"] = 500
    if ps["mode"] == "light":
        ps["vectors"] = 120
        res["complete"] = False
        res["incomplete"] = ["the post-synthesis check ran LIGHT (a subset of the vectors, for local feedback); "
                             "leaderboard.py add runs the full check itself, so there is no need to rerun with "
                             "--postsynth full first (only a stored result for add --from-check must come from a "
                             "full run)"]
if "--sandbox" in sys.argv and sys.argv[sys.argv.index("--sandbox") + 1] != "off":
    res["sandbox"] = {"mode": sys.argv[sys.argv.index("--sandbox") + 1], "mechanism": "fake",
                      "active": os.environ.get("FAKE_SANDBOX", "active") == "active"}
if "FAKE_GATES" in os.environ:
    g = json.loads(os.environ["FAKE_GATES"])
    res["score"]["gates"], res["score"]["num_gates"] = g, sum(g.values())
    res["score"]["area_mge"] = int(os.environ["FAKE_MGE"])
    res["score"]["area_ge"] = round(res["score"]["area_mge"] / 1000, 3)
if "FAKE_DEPTH" in os.environ:
    res["score"]["depth"] = int(os.environ["FAKE_DEPTH"])
if "--ppa" in sys.argv and os.environ.get("FAKE_PPA", "weighed") != "none":
    pm = sys.argv[sys.argv.index("--ppa") + 1]       # a current check.py writes `ppa` unless --ppa off
    res["stages"]["ppa"] = {"mode": pm, "seconds": 0.5}
    if os.environ.get("FAKE_PPA") == "unavailable":
        res["ppa"] = {"available": False, "reason": "liberty not found: /x/y.lib"}
    else:
        n, d = res["score"]["num_gates"], res["score"]["depth"]
        res["ppa"] = {"available": True, "ppa_version": "sky130_a0_v1", "area_um2_sky130": 460.4416,
                      "area_e4um2_sky130": 4604416, "delay_ps_sky130": 2487, "unit_depth": d,
                      "cells_sky130": n, "cell_hist_sky130": {"nand2_1": n}, "constants": False,
                      "liberty_sha256": "a" * 64, "ppa_pins_sha256": "b" * 64,
                      "ppa_script_sha256": "c" * 64, "netlist_sha256": "d" * 64}
        if os.environ.get("FAKE_SKY") == "current":    # columns a board ranks: the current identity, the
            res["ppa"].update(json.loads(r"""@IDENT@"""))   # default drive, area and time after the score
            res["ppa"]["setup"] = {"pi_slew_ps": 50, "input_drive": "sky130_fd_sc_hd__buf_8", "po_load_ff": 10}
            res["ppa"]["area_e4um2_sky130"] = res["score"]["area_mge"] * 30
            res["ppa"]["area_um2_sky130"] = res["ppa"]["area_e4um2_sky130"] / 10000
            res["ppa"]["delay_ps_sky130"] = d * 100
        if os.environ.get("FAKE_MAPPED") == "unavailable":
            res["ppa"]["mapped"] = {"available": False, "reason": "the mapping run failed: x"}
        elif os.environ.get("FAKE_MAPPED"):
            res["ppa"]["mapped"] = json.loads(os.environ["FAKE_MAPPED"])
if mode == "reject":
    res.update(accepted=False, stage="solution", errors=["the proof does not compile"])
    print(json.dumps(res)); sys.exit(1)
if mode == "infra":
    print(json.dumps({"accepted": False, "stage": "infrastructure", "errors": ["lake missing"]}))
    sys.exit(2)
print(json.dumps(res))
'''


class CliTest(Tmp):
    def fake(self, gates, depth):
        os.environ["FAKE_GATES"] = json.dumps(gates)
        os.environ["FAKE_MGE"] = str(sum(GE[g] * n for g, n in gates.items()))
        os.environ["FAKE_DEPTH"] = str(depth)

    def tearDown(self):
        for k in ("FAKE_GATES", "FAKE_MGE", "FAKE_DEPTH", "FAKE_MODE", "FAKE_ARGV_LOG", "FAKE_PPA", "FAKE_MAPPED",
                  "FAKE_SKY"):
            os.environ.pop(k, None)

    def test_end_to_end(self):
        env = CliEnv(self)
        os.environ["FAKE_SKY"] = "current"      # sky130 columns the board ranks (area 30 x milli-GE, 100 ps per level)
        self.fake({"AND": 100}, 20)
        rc, out, err = env.add("alice")
        self.assertEqual(rc, 0, err)
        self.assertIn("added toy/", out)
        self.assertIn("alice, 399.9000 um^2, 2000 ps (133.300 GE, depth 20)", out)
        self.fake({"AND": 90}, 25)
        self.assertEqual(env.add("bob", assisted=["Claude (Anthropic)", "a proof assistant"])[0], 0)
        self.fake({"AND": 120}, 30)
        self.assertEqual(env.add("carol")[0], 0)
        self.assertEqual(sorted(os.listdir(env.data)), ["toy"])
        self.assertEqual(len(os.listdir(os.path.join(env.data, "toy"))), 9)   # 3 x (json sv lean)

        rc, out, _ = env.run("pareto", "--task", "toy")
        self.assertEqual(rc, 0)
        self.assertIn("2 of 3 ranked records", out)
        self.assertIn("alice", out)
        self.assertIn("bob", out)
        self.assertNotIn("carol", out)
        self.assertIn("exploration: the board ranks area x time", out)
        rc, out, _ = env.run("pareto", "--task", "toy", "--format", "json")
        js = json.loads(out)
        self.assertEqual([(r["player"], r["rank"]) for r in js["frontier"]], [("bob", 2), ("alice", 1)])
        self.assertEqual((js["view"], js["ranked_by"]), ("exploration", "area_x_time"))
        rc, out, _ = env.run("pareto", "--task", "toy", "--unassisted")
        self.assertEqual(rc, 0)
        self.assertIn("1 of 2 ranked records", out)

        rc, md, _ = env.run("board", "--task", "toy")
        self.assertEqual(rc, 0)
        self.assertIn("Depth budget: depth <= 22", md)
        self.assertIn("Best area x time under the depth budget", md)
        self.assertIn("over budget", md)         # bob: depth 25 > 22
        rc, js, _ = env.run("board", "--task", "toy", "--format", "json")
        board = json.loads(js)
        self.assertEqual(board["depth_budget"], 22)
        self.assertEqual(board["ranked_by"], "area_x_time")
        # by area x time (alice 399.9 um^2 x 2000 ps < bob 359.91 x 2500 < carol), the Pareto layer beside it
        self.assertEqual([(r["rank"], r["player"], r["layer"], r["exact"]) for r in board["ranking"]],
                         [(1, "alice", 1, 3999000 * 2000), (2, "bob", 1, 3599100 * 2500), (3, "carol", 2, 4798800 * 3000)])
        self.assertIn("| 1 | alice | none | 799.80 | 399.9000 | 2000 | 1 |", md)
        self.assertEqual([r["player"] for r in board["budget_ranking"]], ["alice", "bob", "carol"])
        self.assertEqual([r["player"] for r in board["budget_ranking"] if r["rank"] is not None],
                         ["alice"])

        out_md = os.path.join(self.tmp, "all.md")
        rc, out, _ = env.run("export", "--out", out_md)
        self.assertEqual(rc, 0)
        with open(out_md) as fh:
            text = fh.read()
        self.assertIn("# svGolf leaderboard", text)
        self.assertIn("## `toy`", text)

        rc, out, err = env.run("verify", "--offline")
        self.assertEqual(rc, 0, out + err)
        self.assertIn("3 records, 0 failed", out)

        # tamper with one stored design: verify fails, exit 1, and the board skips it
        victim = sorted(f for f in os.listdir(os.path.join(env.data, "toy")) if f.endswith(".sv"))[0]
        with open(os.path.join(env.data, "toy", victim), "a") as fh:
            fh.write("// edit\n")
        rc, out, _ = env.run("verify", "--offline", "--task", "toy")
        self.assertEqual(rc, 1)
        self.assertIn("[FAIL]", out)
        self.assertIn("1 failed", out)

    def test_record_carries_the_real_checker_identity(self):
        env = CliEnv(self)
        self.assertEqual(env.add("alice")[0], 0)
        (_, rec, _), = lb.load_records(env.data, "toy")
        c = rec["checker"]
        self.assertEqual(c["files"], lb.checker_file_hashes())
        self.assertIn("check.py", c["files"])
        with open(os.path.join(SVGOLF, "lean-toolchain")) as fh:
            self.assertEqual(c["lean_toolchain"], fh.read().strip())
        self.assertTrue(c["svgolf_revision"] is None or len(c["svgolf_revision"].split("+")[0]) == 40)
        self.assertEqual(c["lean_surfaces_revision"], "0123abcd+dirty")    # from the check result

    def test_checker_changing_during_the_check_is_refused(self):
        env = CliEnv(self)
        calls = []

        def drifting(svgolf=lb.SVGOLF, task=None):
            calls.append(1)
            return {"svgolf_revision": "r", "lean_toolchain": "t",
                    "files": {"check.py": str(len(calls)) * 64}}
        with mock.patch.object(lb, "collect_environment", drifting):
            rc, out, err = env.add("alice")
        self.assertEqual(rc, 1)
        self.assertIn("checker or statement files changed while the check ran (check.py)", err)
        self.assertFalse(os.path.exists(env.data))

    def test_a_statement_changing_during_the_check_is_refused(self):
        """A record names the statement it was checked under (2026-11-07): a statement file that changes while the
        check runs is refused like a checker file."""
        env = CliEnv(self)
        calls = []

        def drifting(svgolf=lb.SVGOLF, task=None):
            calls.append(1)
            return {"svgolf_revision": "r", "lean_toolchain": "t", "files": {"check.py": "4" * 64},
                    "statement": {"tasks/toy/Spec.lean": str(len(calls)) * 64}}
        with mock.patch.object(lb, "collect_environment", drifting):
            rc, out, err = env.add("alice")
        self.assertEqual(rc, 1)
        self.assertIn("checker or statement files changed while the check ran (tasks/toy/Spec.lean)", err)
        self.assertFalse(os.path.exists(env.data))

    def test_require_clean(self):
        env = CliEnv(self)
        sv, lean = env.files("clean")
        rc, out, err = env.run("add", "--task", "toy", "--player", "clean", "--sv", sv, "--lean",
                               lean, "--date", "2026-10-29", "--require-clean")
        self.assertEqual(rc, 1)           # the fake result's lean-surfaces revision is +dirty
        self.assertIn("--require-clean", err)
        self.assertFalse(os.path.exists(env.data))

    def test_default_date_comes_from_the_cli_clock(self):
        env = CliEnv(self)
        sv, lean = env.files("dated")
        rc, out, err = env.run("add", "--task", "toy", "--player", "dated", "--sv", sv, "--lean",
                               lean)
        self.assertEqual(rc, 0, err)
        (_, rec, _), = lb.load_records(env.data, "toy")
        self.assertRegex(rec["submitted_at"], r"^\d{4}-\d{2}-\d{2}$")

    def test_rejected_and_infrastructure_and_duplicate(self):
        env = CliEnv(self)
        os.environ["FAKE_MODE"] = "reject"
        rc, out, err = env.add("alice")
        self.assertEqual(rc, 1)
        self.assertIn("REFUSED", err)
        self.assertFalse(os.path.exists(env.data))
        os.environ["FAKE_MODE"] = "infra"
        rc, out, err = env.add("alice")
        self.assertEqual(rc, 2)
        self.assertIn("infrastructure", err)
        self.assertFalse(os.path.exists(env.data))
        os.environ["FAKE_MODE"] = "accept"
        self.assertEqual(env.add("alice")[0], 0)
        os.environ["FAKE_MODE"] = "infra"        # if check.py ran, this would be exit status 2
        rc, out, err = env.add("alice")          # the same player, the same files
        self.assertEqual(rc, 1)
        self.assertIn("already recorded", err)
        sv, lean = env.files("alice")
        rc, out, err = env.run("add", "--task", "toy", "--player", "bad handle", "--sv", sv,
                               "--lean", lean, "--date", "2026-10-29")
        self.assertEqual(rc, 1)                  # malformed fields fail before check.py runs
        self.assertIn("player handle", err)
        os.environ["FAKE_MODE"] = "accept"
        self.assertEqual(env.add("alice2", tag="alice")[0], 0)   # another player: fine

    def test_verify_reports_junk_files(self):
        env = CliEnv(self)
        os.makedirs(os.path.join(env.data, "toy"))
        for name, text in (("a.json", "[1]"), ("b.json", "{ nope")):
            with open(os.path.join(env.data, "toy", name), "w") as fh:
                fh.write(text)
        rc, out, _ = env.run("verify", "--offline")
        self.assertEqual(rc, 1)
        self.assertIn("not a JSON object", out)
        self.assertIn("2 records, 2 failed", out)
        rc, out, _ = env.run("board", "--task", "toy")
        self.assertEqual(rc, 0)
        self.assertIn("No ranked records.", out)

    def test_unknown_task_and_bad_handle(self):
        env = CliEnv(self)
        sv, lean = env.files("x")
        rc, _, err = env.run("add", "--task", "nope", "--player", "a", "--sv", sv, "--lean", lean)
        self.assertEqual(rc, 2)
        rc, _, err = env.run("add", "--task", "toy", "--player", "has space", "--sv", sv,
                             "--lean", lean, "--date", "2026-10-29")
        self.assertEqual(rc, 1)
        self.assertIn("player handle", err)
        rc, _, err = env.run("pareto", "--task", "nope")
        self.assertEqual(rc, 2)

    def test_empty_board(self):
        env = CliEnv(self)
        rc, out, _ = env.run("board", "--task", "toy")
        self.assertEqual(rc, 0)
        self.assertIn("No ranked records.", out)
        rc, out, _ = env.run("verify")
        self.assertEqual((rc, out.strip()), (0, "no records"))


class PostsynthModeCliTest(Tmp):
    """`add` / `verify --full` run check.py with `--postsynth` (a fake check.py that logs
    its arguments and writes the mode it was given, like the real one)."""

    def setUp(self):
        super().setUp()
        self.env = CliEnv(self)
        self.log = os.path.join(self.tmp, "argv.log")
        os.environ["FAKE_ARGV_LOG"] = self.log

    def tearDown(self):
        os.environ.pop("FAKE_ARGV_LOG", None)
        os.environ.pop("FAKE_SKY", None)

    def argv_log(self):
        with open(self.log) as fh:
            return [ln.strip() for ln in fh if ln.strip()]

    def records(self):
        return [r for _, r, _ in lb.load_records(self.env.data, "toy")]

    def test_add_and_verify_full_run_check_py_with_the_sandbox_required(self):
        """WP-S: an official record is made with the OS sandbox or not at all: `--sandbox require` by default,
        overridable (`--sandbox off`) only by an explicit option."""
        rc, out, err = self.env.add("alice")
        self.assertEqual(rc, 0, err)
        line = self.argv_log()[-1].split()
        self.assertEqual(line[line.index("--sandbox") + 1], "require")
        rc, out, err = self.env.add("bob", extra=("--sandbox", "off"))
        self.assertEqual(rc, 0, err)
        line = self.argv_log()[-1].split()
        self.assertEqual(line[line.index("--sandbox") + 1], "off")

    def test_add_runs_check_py_in_full_mode_by_default(self):
        rc, out, err = self.env.add("alice")
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.argv_log()[-1].split()[-2:], ["--postsynth", "full"])
        (rec,) = self.records()
        self.assertEqual(rec["postsynth"]["mode"], "full")
        self.assertIn("full mode", out)
        self.assertNotIn("LIGHT", out)

    def test_add_postsynth_light_is_an_explicit_marked_record(self):
        os.environ["FAKE_SKY"] = "current"      # columns the board ranks
        sv, lean = self.env.files("lighty")
        rc, out, err = self.env.run("add", "--task", "toy", "--player", "lighty", "--sv", sv,
                                    "--lean", lean, "--date", "2026-10-29", "--postsynth", "light")
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.argv_log()[-1].split()[-2:], ["--postsynth", "light"])
        (rec,) = self.records()
        self.assertEqual((rec["postsynth"]["mode"], rec["postsynth"]["vectors"],
                          rec["postsynth"]["full_vectors"]), ("light", 120, 500))
        self.assertIn("LIGHT mode (120 of 500 vectors)", out)
        rc, md, _ = self.env.run("board", "--task", "toy")
        self.assertIn(" light |", md)
        rc, js, _ = self.env.run("board", "--task", "toy", "--format", "json")
        board = json.loads(js)
        self.assertEqual(board["frontier"], [])                 # a light record never ranks
        self.assertEqual(board["unranked"][0]["postsynth"], "light")

    def test_from_check_light_needs_the_light_flag(self):
        sv_sha = lb.sha256_bytes(SV_TEXT + b"// alice\n")       # what CliEnv.files writes
        res = self.env.write_result(fake_result(mode="light", sv_sha=sv_sha))
        rc, out, err = self.env.add("alice", from_check=res)
        self.assertEqual(rc, 1)
        self.assertIn("LIGHT mode", err)
        self.assertFalse(os.path.exists(self.env.data))
        sv, lean = self.env.files("alice")
        rc, out, err = self.env.run("add", "--task", "toy", "--player", "alice", "--sv", sv,
                                    "--lean", lean, "--date", "2026-10-29", "--from-check", res,
                                    "--postsynth", "light")
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.records()[0]["postsynth"]["mode"], "light")

    def test_verify_full_rechecks_in_full_mode(self):
        sv, lean = self.env.files("lighty")
        self.assertEqual(self.env.run("add", "--task", "toy", "--player", "lighty", "--sv", sv,
                                      "--lean", lean, "--date", "2026-10-29", "--postsynth",
                                      "light")[0], 0)
        open(self.log, "w").close()
        rc, out, err = self.env.run("verify", "--full")
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(self.argv_log()[-1].split()[-2:], ["--postsynth", "full"])
        self.assertIn("LIGHT mode", out)
        self.assertIn("rechecked: accepted", out)

    def test_seed_references_and_default_are_full(self):
        self.assertEqual(self.env.add("bob")[0], 0)
        self.assertTrue(all(ln.endswith("--postsynth full") for ln in self.argv_log()))

    def test_the_reference_handle_is_seed_references_own(self):
        """Decided 2026-11-12: `add` refuses the proved references' handle for any record (before any check runs);
        `seed-references`, the maintainers' path, records the task's listed references under it."""
        rc, _, err = self.env.add(lb.REFERENCE_PLAYER)
        self.assertEqual(rc, 1)
        self.assertIn(lb.RESERVED_HANDLE, err)
        self.assertFalse(os.path.exists(self.log))                  # check.py never ran
        self.assertEqual(self.records(), [])
        ref = os.path.join(self.env.tasks, "toy", "reference")
        os.makedirs(ref)
        sv, lean = self.env.files("ref_n")
        shutil.copy(sv, os.path.join(ref, "ref_n.sv"))
        shutil.copy(lean, os.path.join(ref, "ref_n.lean"))
        with open(os.path.join(self.env.tasks, "toy", "task.json"), "w") as fh:
            json.dump(toy_task(leaderboard={"depth_budget": 22},
                               references=[{"sv": "reference/ref_n.sv", "lean": "reference/ref_n.lean"}]), fh)
        rc, out, err = self.env.run("seed-references", "--task", "toy")
        self.assertEqual(rc, 0, out + err)
        self.assertEqual([r["player"] for r in self.records()], [lb.REFERENCE_PLAYER])


class PpaRecordTest(Tmp):
    """The `ppa` key of a record (WP-X3): optional, additive, validated, hashed, verified."""

    def rec_with(self, **kw):
        res = with_ppa(fake_result(), **kw)
        return make_record(res=res), res

    def test_a_record_without_the_key_is_unchanged(self):
        rec = make_record()
        self.assertNotIn("ppa", rec)
        self.assertEqual(lb.validate_record(rec), [])
        self.assertEqual(rec["record_hash"], lb.compute_record_hash(rec))
        # the pinned hash of test_record_hash_pinned is the same one: the key adds nothing when absent
        pinned = make_record(player="pin", assisted=["tool a", "tool b"], notes="pinned", date="2026-01-02",
                             res=fake_result(flow=GOLD_FLOW, ge=GOLD_GE))
        self.assertEqual(pinned["record_hash"], PINNED_HASH)

    def test_the_block_is_copied_validated_and_hashed(self):
        rec, res = self.rec_with()
        self.assertEqual(rec["ppa"], res["ppa"])
        self.assertIsNot(rec["ppa"], res["ppa"])
        self.assertEqual(lb.validate_record(rec), [])
        self.assertEqual(rec["schema"], lb.SCHEMA)                       # additive: the schema string is unchanged
        plain = make_record()
        self.assertNotEqual(rec["record_hash"], plain["record_hash"])    # the key is covered by the hash
        rec["ppa"]["delay_ps_sky130"] += 1
        self.assertNotEqual(lb.compute_record_hash(rec), rec["record_hash"])

    def test_malformed_blocks_are_refused(self):
        rec, _ = self.rec_with()
        for mutate, frag in (
                (lambda b: b.update(area_um2_sky130=1.0), "area_um2_sky130 is not"),
                (lambda b: b.update(cells_sky130=3), "sum of ppa.cell_hist_sky130"),
                (lambda b: b.update(delay_ps_sky130=1.5), "delay_ps_sky130 must be a non-negative integer"),
                (lambda b: b.update(netlist_sha256="xyz"), "netlist_sha256"),
                (lambda b: b.update(constants="yes"), "constants"),
                (lambda b: b.update(available="maybe"), "available"),
                (lambda b: b.update(unit_depth=9, cell_hist_sky130=b["cell_hist_sky130"]), "unit_depth 9 is not score.depth"),
                (lambda b: b.update(constants=True), "tie cell")):
            bad = copy.deepcopy(rec)
            mutate(bad["ppa"])
            problems = lb.validate_record(bad)
            self.assertTrue(any(frag in p for p in problems), (frag, problems))
        for blk in ({"available": False}, {"available": False, "reason": ""},
                    {"available": False, "reason": "x", "extra": 1}, "nope", None):
            bad = copy.deepcopy(rec)
            bad["ppa"] = blk
            self.assertTrue(lb.validate_record(bad), blk)

    def test_tie_cell_arithmetic(self):
        rec, _ = self.rec_with(constants=True)
        self.assertEqual(rec["ppa"]["cells_sky130"], rec["score"]["num_gates"] + 1)
        self.assertEqual(lb.validate_record(rec), [])

    def test_buffering_repair_arithmetic(self):
        """sky130_a0_v2 (buffering only): cells = the scored gates + the repair's buffers + its tie cells, exactly."""
        g = fake_result()["score"]["num_gates"]
        rep = {"method": "buffer_trees_v1", "cells_before": g, "buffers": 2, "tie_cells": 2, "nets_buffered": 1,
               "rounds": 2, "netlist_sha256": "e" * 64}
        rec, _ = self.rec_with(constants=True, repair=rep, cells_sky130=g + 4,
                               cell_hist_sky130={"nand2_1": g, "buf_2": 2, "conb_1": 2})
        self.assertEqual(lb.validate_record(rec), [])
        with self.assertRaises(lb.Refused) as cm:              # a block whose cells are not that sum is not recorded
            self.rec_with(constants=True, repair=dict(rep, buffers=3), cells_sky130=g + 4,
                          cell_hist_sky130={"nand2_1": g, "buf_2": 2, "conb_1": 2})
        self.assertIn("is not repair.cells_before + buffers + tie_cells", str(cm.exception))

    def test_unavailable_block_is_recorded_only_from_a_require_run(self):
        res = fake_result()
        res["ppa"] = {"available": False, "reason": "the netlist has cells outside the A0' table"}
        res["stages"]["ppa"] = {"mode": "require", "seconds": 0.1}
        rec = make_record(res=res)                    # a design the pinned flow cannot weigh: recorded, with the reason
        self.assertEqual(rec["ppa"], res["ppa"])
        self.assertEqual(lb.validate_record(rec), [])
        res["stages"]["ppa"]["mode"] = "auto"         # under auto it may merely be a missing liberty
        with self.assertRaises(lb.Refused) as cm:
            make_record(res=res)
        self.assertIn("official record needs `check.py --ppa require`", str(cm.exception))

    def test_a_result_with_no_ppa_key_gives_a_record_without_it(self):
        res = fake_result()                           # `--ppa off`, or a checker from before the columns
        self.assertNotIn("ppa", make_record(res=res))

    def test_a_malformed_ppa_in_the_result_is_refused(self):
        res = with_ppa(fake_result())
        res["ppa"]["cells_sky130"] = 99
        with self.assertRaises(lb.Refused) as cm:
            make_record(res=res)
        self.assertIn("`ppa` object is malformed", str(cm.exception))

    def test_offline_verify_checks_the_block_against_the_record(self):
        rec, _ = self.rec_with()
        path = lb.store_record(self.data if hasattr(self, "data") else self.tmp, rec, SV_TEXT, LEAN_TEXT)
        r = lb.verify_record(path, rec, toy_task())
        self.assertEqual((r.status, r.fails), ("ok", []))

    def test_recheck_under_another_flow_does_not_compare_the_columns(self):
        """A record checked under another Yosys/flow: the netlist, its area and its hash legitimately differ, and
        `verify --full` says STALE (as for the score), never FAIL on the PPA columns. The same flow still compares."""
        rec, res = self.rec_with()
        path = lb.store_record(self.data, rec, SV_TEXT, LEAN_TEXT)
        other_flow = dict(FLOW, yosys="Yosys 9.99 (another build)")
        moved = with_ppa(fake_result(), area_e4=4699999, netlist_sha256="9" * 64)
        r = lb.verify_record(path, rec, toy_task(), flow=other_flow, recheck=lambda sv, lean: moved)
        self.assertEqual((r.status, r.fails), ("stale", []))
        self.assertTrue(any("yosys" in x for x in r.stale), r.stale)
        self.assertIn("recheck: ppa columns not compared (the flow has changed)", r.notes)
        # the same record under the SAME flow is compared strictly: the moved area is a failure
        r = lb.verify_record(path, rec, toy_task(), flow=FLOW, recheck=lambda sv, lean: moved)
        self.assertEqual(r.status, "FAIL")
        self.assertTrue(any("ppa.area_e4um2_sky130 recorded 4604416, now 4699999" in f for f in r.fails), r.fails)
        # a record without columns gets no PPA note in the other-flow case either
        plain = make_record()
        pp = lb.store_record(os.path.join(self.tmp, "plain2"), plain, SV_TEXT, LEAN_TEXT)
        r = lb.verify_record(pp, plain, toy_task(), flow=other_flow, recheck=lambda sv, lean: moved)
        self.assertFalse(any("ppa" in n for n in r.notes), r.notes)

    def test_rescore_and_recheck_compare_the_columns_exactly(self):
        rec, res = self.rec_with()
        path = lb.store_record(self.data, rec, SV_TEXT, LEAN_TEXT)
        honest = {"area_mge": 13330, "depth": 10, "gates": {"AND": 10}, "num_gates": 10, "rtlil_sha256": "d" * 64,
                  "sources": [{"canonical_sha256": CANON_SHA}], "ppa": dict(res["ppa"])}

        def verify(**kw):
            return lb.verify_record(path, rec, toy_task(), flow=FLOW, **kw)

        r = verify(rescore=lambda sv: honest)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("ppa columns reproduced", r.notes)
        slower = dict(honest, ppa=dict(res["ppa"], delay_ps_sky130=9999))
        r = verify(rescore=lambda sv: slower)
        self.assertTrue(any("ppa.delay_ps_sky130 recorded 2487, now 9999" in f for f in r.fails), r.fails)
        # no liberty on the verifying machine: the rescore does not fail, it says so
        nolib = dict(honest, ppa={"available": False, "reason": "liberty not found: /x"})
        r = verify(rescore=lambda sv: nolib)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertTrue(any("not re-weighed" in n for n in r.notes), r.notes)
        # a weighing under another ppa_version is a note, not a failure (the number is no longer comparable)
        newer = dict(honest, ppa=dict(res["ppa"], ppa_version="sky130_a0_v2", delay_ps_sky130=1))
        r = verify(rescore=lambda sv: newer)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertTrue(any("not compared" in n for n in r.notes), r.notes)
        # --full: the recheck runs `--ppa require`, so a missing or unavailable weighing is a failure
        ok = with_ppa(fake_result())
        r = verify(recheck=lambda sv, lean: ok)
        self.assertEqual((r.status, r.fails), ("ok", []))
        r = verify(recheck=lambda sv, lean: fake_result())
        self.assertTrue(any("ppa columns recorded, not weighed now" in f for f in r.fails), r.fails)
        gone = with_ppa(fake_result())
        gone["ppa"] = {"available": False, "reason": "x"}
        r = verify(recheck=lambda sv, lean: gone)
        self.assertTrue(any("not weighed now: x" in f for f in r.fails), r.fails)
        # a record without columns is not compared with anything, whatever the fresh weighing says
        plain = make_record()
        pp = lb.store_record(os.path.join(self.tmp, "plain"), plain, SV_TEXT, LEAN_TEXT)
        r = lb.verify_record(pp, plain, toy_task(), flow=FLOW, rescore=lambda sv: slower, recheck=lambda sv, l: ok)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertFalse(any("ppa" in n for n in r.notes), r.notes)


class PpaMappedRecordTest(Tmp):
    """The sub-object `ppa.mapped` of a record (WP-X4, flow A1'): optional inside `ppa`, validated, hashed, compared by
    `verify` under its own identity, never mixed with A0''s columns."""

    def rec_with(self, **mapped):
        res = with_ppa(fake_result(), mapped=mapped)
        return make_record(res=res), res

    def test_the_sub_object_is_copied_validated_and_hashed(self):
        rec, res = self.rec_with()
        self.assertEqual(rec["ppa"]["mapped"], res["ppa"]["mapped"])
        self.assertIsNot(rec["ppa"]["mapped"], res["ppa"]["mapped"])
        self.assertEqual(lb.validate_record(rec), [])
        self.assertEqual(rec["schema"], lb.SCHEMA)                       # additive: the schema string is unchanged
        plain = make_record(res=with_ppa(fake_result()))                 # a record with A0' columns only stays valid
        self.assertNotIn("mapped", plain["ppa"])
        self.assertEqual(lb.validate_record(plain), [])
        self.assertNotEqual(rec["record_hash"], plain["record_hash"])
        rec["ppa"]["mapped"]["mapped_delay_sky130_v1"] += 1
        self.assertNotEqual(lb.compute_record_hash(rec), rec["record_hash"])

    def test_the_a0_columns_keep_their_names_and_the_mapped_ones_have_their_own(self):
        rec, _ = self.rec_with()
        self.assertEqual(rec["ppa"]["area_um2_sky130"], 460.4416)
        self.assertEqual(rec["ppa"]["mapped"]["area_um2_sky130_mapped_v1"], 440.4224)
        self.assertNotIn("area_um2_sky130", rec["ppa"]["mapped"])
        self.assertNotIn("area_um2_sky130_mapped_v1", {k: 1 for k in rec["ppa"] if k != "mapped"})

    def test_malformed_mapped_objects_are_refused(self):
        for mutate, frag in (
                (lambda m: m.update(area_um2_sky130_mapped_v1=1.0), "area_um2_sky130_mapped_v1 is not"),
                (lambda m: m.update(mapped_cells_sky130_v1=9), "is not the sum of mapped_cell_hist_sky130_v1"),
                (lambda m: m.update(mapped_delay_sky130_v1=1.5), "mapped_delay_sky130_v1 must be a non-negative integer"),
                (lambda m: m.update(mapped_buffers_sky130_v1=3), "buffer and inverter counts"),
                (lambda m: m.update(netlist_sha256="nope"), "netlist_sha256 must be a sha256"),
                (lambda m: m.update(ppa_mapped_version=""), "ppa_mapped_version must be a non-empty text"),
                (lambda m: m.update(equivalence={"vectors": 0, "seed": "x"}), "equivalence must record"),
                (lambda m: m.update(constants="no"), "constants must be a boolean"),
                (lambda m: m.update(rtlil_sha256="1" * 64), "ppa.mapped.rtlil_sha256 is not the canonical RTLIL"),
                (lambda m: m.update(available="yes"), "ppa.mapped.available must be true or false"),
                (lambda m: m.clear(), "ppa.mapped.available must be true or false")):
            rec, _ = self.rec_with()
            mutate(rec["ppa"]["mapped"])
            bad = lb.validate_record(rec)
            self.assertTrue(any(frag in b for b in bad), (frag, bad))
        # an unavailable mapped object is exactly {available: false, reason}
        rec, _ = self.rec_with()
        rec["ppa"]["mapped"] = {"available": False, "reason": "the mapping run failed: x"}
        self.assertEqual(lb.validate_record(rec), [])
        for bad in ({"available": False}, {"available": False, "reason": ""}, {"available": False, "reason": "x", "area": 1}):
            rec["ppa"]["mapped"] = bad
            self.assertTrue(lb.validate_record(rec), bad)
        # ... and an unavailable `ppa` cannot carry one
        rec["ppa"] = {"available": False, "reason": "x", "mapped": fake_mapped()}
        self.assertTrue(lb.validate_record(rec))
        # a malformed mapped object is a refused submission, like a malformed ppa
        res = with_ppa(fake_result(), mapped={"mapped_cells_sky130_v1": 9})
        with self.assertRaises(lb.Refused) as cm:
            make_record(res=res)
        self.assertIn("`ppa` object is malformed", str(cm.exception))

    def test_a_mapped_object_of_a_design_the_flow_could_not_map_is_recorded_as_it_is(self):
        res = with_ppa(fake_result(), mapped={"available": False, "reason": "the mapping run failed: x"})
        self.assertEqual(res["ppa"]["mapped"], {"available": False, "reason": "the mapping run failed: x"})
        rec = make_record(res=res)
        self.assertEqual(rec["ppa"]["mapped"], {"available": False, "reason": "the mapping run failed: x"})
        self.assertEqual(lb.validate_record(rec), [])

    def test_rescore_and_recheck_compare_the_mapped_columns_under_their_own_identity(self):
        rec, res = self.rec_with()
        path = lb.store_record(self.data, rec, SV_TEXT, LEAN_TEXT)
        honest = {"area_mge": 13330, "depth": 10, "gates": {"AND": 10}, "num_gates": 10, "rtlil_sha256": "d" * 64,
                  "sources": [{"canonical_sha256": CANON_SHA}], "ppa": copy.deepcopy(res["ppa"])}

        def verify(**kw):
            return lb.verify_record(path, rec, toy_task(), flow=FLOW, **kw)

        def mutated(**over):
            got = copy.deepcopy(honest)
            got["ppa"]["mapped"].update(over)
            return got

        r = verify(rescore=lambda sv: honest)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("ppa columns reproduced", r.notes)
        self.assertIn("ppa.mapped columns reproduced", r.notes)
        slower = mutated(mapped_delay_sky130_v1=9999)
        r = verify(rescore=lambda sv: slower)
        self.assertTrue(any("ppa.mapped.mapped_delay_sky130_v1 recorded 6313, now 9999" in f for f in r.fails), r.fails)
        self.assertFalse(any(f.startswith("rescore: ppa.delay") for f in r.fails), r.fails)      # A0' unaffected
        moved = mutated(netlist_sha256="8" * 64, mapped_cell_hist_sky130_v1={"maj3_1": 4})
        r = verify(rescore=lambda sv: moved)
        self.assertTrue(any("ppa.mapped.netlist_sha256" in f for f in r.fails), r.fails)
        self.assertTrue(any("ppa.mapped.mapped_cell_hist_sky130_v1" in f for f in r.fails), r.fails)
        # a mapping under another script, version, pins, or tool build is a note, not a failure
        for over in ({"ppa_mapped_version": "sky130_a1_v2"}, {"ppa_mapped_script_sha256": "1" * 64},
                     {"ppa_mapped_pins_sha256": "2" * 64}, {"yosys_version": "Yosys other"}, {"abc_version": "ABC other"}):
            r = verify(rescore=lambda sv, o=over: mutated(mapped_delay_sky130_v1=1, **o))
            self.assertEqual((r.status, r.fails), ("ok", []), over)
            self.assertTrue(any("ppa.mapped columns not compared" in n for n in r.notes), (over, r.notes))
        # no mapping on the verifying machine (rescore): a note; --full (recheck, `--ppa require`): a failure
        gone = copy.deepcopy(honest)
        gone["ppa"]["mapped"] = {"available": False, "reason": "the mapping run failed: x"}
        r = verify(rescore=lambda sv: gone)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertTrue(any("ppa.mapped columns not re-weighed (the mapping run failed: x)" in n for n in r.notes), r.notes)
        full_ok = with_ppa(fake_result(), mapped={})
        r = verify(recheck=lambda sv, lean: full_ok)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("ppa.mapped columns reproduced", r.notes)
        full_gone = with_ppa(fake_result(), mapped={"available": False, "reason": "boom"})
        r = verify(recheck=lambda sv, lean: full_gone)
        self.assertTrue(any("ppa.mapped columns recorded, not mapped now: boom" in f for f in r.fails), r.fails)
        no_key = with_ppa(fake_result())               # a checker from before WP-X4
        r = verify(recheck=lambda sv, lean: no_key)
        self.assertTrue(any("not mapped now: no `mapped` in the result" in f for f in r.fails), r.fails)
        # a record whose design the flow could not map, or made before the sub-object, is not compared on it
        unmapped_rec = make_record(res=with_ppa(fake_result(), mapped={"available": False, "reason": "x"}))
        pu = lb.store_record(os.path.join(self.tmp, "unmapped"), unmapped_rec, SV_TEXT, LEAN_TEXT)
        r = lb.verify_record(pu, unmapped_rec, toy_task(), flow=FLOW, recheck=lambda sv, lean: full_ok)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertFalse(any("mapped" in n for n in r.notes), r.notes)
        old = make_record(res=with_ppa(fake_result()))
        po = lb.store_record(os.path.join(self.tmp, "premapped"), old, SV_TEXT, LEAN_TEXT)
        r = lb.verify_record(po, old, toy_task(), flow=FLOW, rescore=lambda sv: honest, recheck=lambda sv, lean: full_ok)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertFalse(any("mapped" in n for n in r.notes), r.notes)

    def test_a_rescore_maps_only_for_a_record_that_has_mapped_columns(self):
        """`run_rescore` runs ppa.py (one Yosys run for the score, one more for flow A1''s mapping): `--no-mapped` unless asked."""
        fake = os.path.join(self.tmp, "fake_ppa.py")
        log = os.path.join(self.tmp, "argv.txt")
        with open(fake, "w") as fh:
            fh.write("import json, sys\nopen(%r, 'a').write(' '.join(sys.argv[1:]) + '\\n')\n"
                     "print(json.dumps({'score': {'area_mge': 1, 'depth': 1}, 'ppa': {'ppa_version': 'v'}}))\n" % log)
        out = lb.run_rescore("d.sv", "tdir", ppa_py=fake, mapped=False)
        self.assertEqual(out["ppa"], {"ppa_version": "v", "available": True})
        lb.run_rescore("d.sv", "tdir", ppa_py=fake)
        with open(log) as fh:
            self.assertEqual(fh.read().splitlines(), ["d.sv --task tdir --no-mapped", "d.sv --task tdir"])

    def test_the_checker_files_include_the_mapped_flow(self):
        for f in ("score/ppa_mapped.ys", "score/ppa_mapped_pins.json"):
            self.assertIn(f, lb.CHECKER_FILES)
            self.assertTrue(os.path.isfile(os.path.join(lb.SVGOLF, f)), f)


class PpaAxesTest(Tmp):
    """`pareto --axes`: the opt-in n-D view over chosen axes; the default is unchanged."""
    AX = ["area_um2_sky130", "delay_ps_sky130"]

    def rec(self, player, area_e4, delay, gates=10, depth=10, date="2026-10-29", ppa=True, **kw):
        res = fake_result(gates={"AND": gates}, depth=depth, flow=FLOW)
        if ppa:
            with_ppa(res, area_e4=area_e4, delay_ps=delay, **kw)
        return make_record(player=player, res=res, date=date)

    def view(self, recs, axes=None, **kw):
        return lb.build_axes_view(toy_task(), recs, axes or self.AX, **kw)

    def test_parse_axes(self):
        self.assertEqual(lb.parse_axes("area_um2_sky130, delay_ps_sky130"), self.AX)
        for bad in ("", "nonsense", "depth,depth", "area_ge"):
            with self.assertRaises(lb.Refused):
                lb.parse_axes(bad)

    def test_two_axes_frontier_dominance_and_ties(self):
        a = self.rec("a", 4000000, 3000)        # small and slow
        b = self.rec("b", 6000000, 2000)        # large and fast
        c = self.rec("c", 7000000, 2500)        # dominated by b
        d = self.rec("d", 4000000, 3000)        # ties a: kept, not dominated
        e = self.rec("e", 3999999, 3000)        # beats a and d on area, ties on delay: dominates them
        v = self.view([a, b, c, d])
        self.assertEqual([r["player"] for r in v["frontier"]], ["a", "d", "b"])
        self.assertEqual([r["player"] for r in v["dominated"]], ["c"])
        v = self.view([a, b, c, d, e])
        self.assertEqual([r["player"] for r in v["frontier"]], ["e", "b"])
        self.assertEqual([r["player"] for r in v["dominated"]], ["a", "d", "c"])

    def test_three_axes_and_deterministic_under_permutation(self):
        recs = [self.rec("a", 4000000, 3000, depth=10), self.rec("b", 4000000, 3000, depth=9),
                self.rec("c", 5000000, 2000, depth=12), self.rec("d", 4500000, 3500, depth=12)]
        axes = ["area_um2_sky130", "delay_ps_sky130", "depth"]
        ref = self.view(recs, axes)
        self.assertEqual([r["player"] for r in ref["frontier"]], ["b", "c"])      # a loses to b, d to b
        rnd = random.Random(7)
        for _ in range(8):
            shuffled = recs[:]
            rnd.shuffle(shuffled)
            self.assertEqual(self.view(shuffled, axes), ref)

    def test_records_without_the_columns_are_listed_not_ranked(self):
        old = self.rec("old", 0, 0, ppa=False)
        bad = make_record(player="unw", res=dict(fake_result(flow=FLOW), ppa={"available": False, "reason": "no cell"},
                                                  stages=dict(fake_result(flow=FLOW)["stages"],
                                                              ppa={"mode": "require", "seconds": 0})))
        good = self.rec("good", 4000000, 3000)
        v = self.view([old, bad, good])
        self.assertEqual([r["player"] for r in v["frontier"]], ["good"])
        why = {r["player"]: r["reason"] for r in v["not_shown"]}
        self.assertIn("before them", why["old"])
        self.assertIn("no cell", why["unw"])

    def test_columns_of_another_version_are_not_ranked_against_the_current_ones(self):
        cur = {"ppa_version": "sky130_a0_v1", "liberty_sha256": "a" * 64, "ppa_pins_sha256": "b" * 64}
        a = self.rec("a", 4000000, 3000)
        b = self.rec("b", 3000000, 2000, ppa_version="sky130_a0_v0")
        v = self.view([a, b], identity=cur)
        self.assertEqual([r["player"] for r in v["frontier"]], ["a"])
        self.assertIn("ppa_version", v["not_shown"][0]["reason"])
        self.assertEqual([r["player"] for r in self.view([a, b], identity=None)["frontier"]], ["b"])

    def test_the_ranked_axes_give_the_default_frontier(self):
        """The default board is the frontier over RANKED_AXES (`--axes area_um2_sky130,time_ps`); `--axes area_mge,depth`
        is the GE frontier, an extra view, over every record (the GE columns need no sky130 weighing)."""
        recs = [self.rec("a", 4000000, 3000, gates=10, depth=20), self.rec("b", 4000000, 2000, gates=12, depth=10),
                self.rec("c", 3000000, 3500, gates=14, depth=25), self.rec("old", 0, 0, ppa=False, gates=9, depth=30)]
        default = lb.build_board(toy_task(), recs, flow=FLOW)
        v = self.view(recs, list(lb.RANKED_AXES))
        self.assertEqual([r["record_hash"] for r in v["frontier"]], [r["record_hash"] for r in default["frontier"]])
        self.assertEqual([r["player"] for r in default["frontier"]], ["c", "b"])
        self.assertEqual([r["player"] for r in v["not_shown"]], ["old"])
        self.assertEqual([r["player"] for r in default["unranked"]], ["old"])
        self.assertEqual([r["player"] for r in self.view(recs, ["area_mge", "depth"])["frontier"]], ["old", "a", "b"])

    def test_the_time_axis_is_the_delay_of_a_combinational_record(self):
        a = self.rec("a", 4000000, 3000)
        self.assertEqual(lb.axis_values(a, ["time_ps", "delay_ps_sky130"]), {"time_ps": 3000, "delay_ps_sky130": 3000})
        self.assertIsNone(lb.axis_values(self.rec("old", 0, 0, ppa=False), ["time_ps"]))
        self.assertEqual(lb.parse_axes("area_um2_sky130,time_ps"), list(lb.RANKED_AXES))

    def test_text_rendering(self):
        a = self.rec("a", 4604416, 2487)
        b = self.rec("b", 6000000, 2000)
        text = lb.render_axes_text(self.view([a, b]))
        self.assertIn("Pareto frontier over (area_um2_sky130, delay_ps_sky130) at N=16 (2 of 2 records", text)
        self.assertIn("460.4416", text)
        self.assertIn("600.0000", text)
        self.assertIn("2487", text)


class PpaInputDriveTest(Tmp):
    """sky130_a0_v3's input drive is a TASK field (task.json `input_drive`, default the pins' buf_8), outside the pins file
    and so outside PPA_IDENTITY. `verify` compares a record's `ppa.setup` with what the task's configuration gives now, and
    the drive is part of PPA comparability: a record under another drive is stale and not ranked, never FAILed as if wrong,
    and a record that claims a drive its numbers were not weighed under cannot pass as reproduced. The records are the
    review's (11/04), rebuilt from tests/leaderboard/drive_records.json on the add record of 10-29 (no sky130 columns;
    kept under tests/leaderboard/drive_base/, leaderboard/data's was re-seeded under sky130_a0_v3)."""

    with open(os.path.join(HERE, "drive_records.json"), encoding="utf-8") as _fh:
        FIX = json.load(_fh)

    def setUp(self):
        super().setUp()
        base = os.path.join(HERE, self.FIX["base_record"])
        with open(base + ".json", encoding="utf-8") as fh:
            self.base = json.load(fh)
        with open(base + ".sv", "rb") as fh:
            self.sv = fh.read()
        with open(base + ".lean", "rb") as fh:
            self.lean = fh.read()
        self.task8 = lb.load_task(lb.DEFAULT_TASKS, "add")
        self.assertNotIn("input_drive", self.task8)                # the add task names none: the pins' default, buf_8
        self.task1 = dict(self.task8, input_drive=BUF1)            # the same task after it chose buf_1
        b8 = self.FIX["blocks"]["buf_8"]
        self.ident = {k: b8[k] for k in lb.PPA_IDENTITY}            # the blocks' own (sky130_a0_v3) identity

    def block(self, which, **setup):
        b = copy.deepcopy(self.FIX["blocks"][which])
        b["setup"].update(setup)
        return b

    def rec(self, block, ident=None):
        rec = copy.deepcopy(self.base)
        rec["ppa"] = block
        if ident:
            rec["ppa"].update(ident)
        rec["record_hash"] = lb.compute_record_hash(rec)
        return rec

    def records(self, ident=None):
        """The review's three records: honest under buf_8, buf_8 numbers claiming buf_1, honest under buf_1."""
        return {"honest_buf8": self.rec(self.block("buf_8"), ident),
                "claims_buf1": self.rec(self.block("buf_8", input_drive=BUF1), ident),
                "honest_buf1": self.rec(self.block("buf_1"), ident)}

    def setup_of(self, task):
        return {"pi_slew_ps": 50, "po_load_ff": 10, "input_drive": task.get("input_drive", BUF8)}

    def verify(self, rec, task, fresh=None, offline=False):
        """verify_record as `cmd_verify` runs it; `fresh` (a block): the rescore's weighing of the stored design under the
        task's drive now (score.py's part unchanged)."""
        self.n = getattr(self, "n", 0) + 1
        path = lb.store_record(os.path.join(self.tmp, f"v{self.n}"), rec, self.sv, self.lean)
        rescore = None
        if not offline:
            sc = rec["score"]
            got = {"area_mge": sc["area_mge"], "depth": sc["depth"], "gates": sc["gates"], "num_gates": sc["num_gates"],
                   "rtlil_sha256": sc["rtlil_sha256"], "sources": [{"canonical_sha256": rec["canonical_sha256"]}],
                   "ppa": fresh}
            rescore = lambda sv: got                                   # noqa: E731
        return lb.verify_record(path, rec, task, rescore=rescore, ppa_identity=self.ident,
                                ppa_setup=self.setup_of(task))

    def test_the_rebuilt_records_are_the_reviews(self):
        for name, rec in self.records().items():
            self.assertEqual(rec["record_hash"], self.FIX["record_hash"][name], name)
            self.assertEqual(lb.validate_record(rec), [], name)
        self.assertEqual(self.FIX["blocks"]["buf_8"]["setup"]["input_drive"], BUF8)
        self.assertEqual(self.FIX["blocks"]["buf_1"]["setup"]["input_drive"], BUF1)
        self.assertNotEqual(self.FIX["blocks"]["buf_8"]["delay_ps_sky130"], self.FIX["blocks"]["buf_1"]["delay_ps_sky130"])

    def test_the_setup_now_is_the_task_s_drive_else_the_pins_default(self):
        now = lb.ppa_setup_now(self.task8)
        self.assertEqual(now, {"pi_slew_ps": 50, "po_load_ff": 10, "input_drive": BUF8})
        self.assertEqual(lb.ppa_setup_now(self.task1)["input_drive"], BUF1)
        absent = os.path.join(self.tmp, "absent.json")
        self.assertEqual(lb.ppa_setup_now(self.task8, pins_path=absent), {})      # nothing known: nothing compared
        self.assertEqual(lb.ppa_setup_now(self.task1, pins_path=absent), {"input_drive": BUF1})

    def test_a_record_claiming_a_drive_its_numbers_were_not_weighed_under_never_passes(self):
        """The first attack: buf_8's numbers labelled buf_1 (hash recomputed) passed `verify` with "ppa columns reproduced"."""
        rec = self.records()["claims_buf1"]
        b8 = self.block("buf_8")
        r = self.verify(rec, self.task8, offline=True)
        self.assertEqual((r.status, r.fails), ("stale", []))
        self.assertTrue(any("another input drive (sky130_fd_sc_hd__buf_1; the task's input drive is now "
                            "sky130_fd_sc_hd__buf_8)" in s for s in r.stale), r.stale)
        r = self.verify(rec, self.task8, fresh=b8)                    # the rescore weighs under the task's buf_8
        self.assertEqual(r.status, "stale")
        self.assertNotIn("ppa columns reproduced", r.notes)
        # where the task's drive IS the claimed one, the rescore weighs under it and the numbers are not buf_1's: FAIL
        r = self.verify(rec, self.task1, fresh=self.block("buf_1"))
        self.assertEqual(r.status, "FAIL")
        self.assertTrue(any("rescore: ppa.delay_ps_sky130 recorded 2590, now 2602" in f for f in r.fails), r.fails)
        # and in the view it is never ranked with the task's records
        v = lb.build_axes_view(self.task8, [rec, self.records()["honest_buf8"]], ["area_um2_sky130", "delay_ps_sky130"],
                               identity=self.ident, input_drive=BUF8)
        self.assertEqual([r["record_hash"] for r in v["frontier"]], [self.FIX["record_hash"]["honest_buf8"]])
        self.assertEqual([r["record_hash"] for r in v["not_shown"]], [rec["record_hash"]])

    def test_records_under_another_drive_are_stale_and_not_ranked_never_failed(self):
        """The second attack: the task changed its drive; the board ranked old and new records together and `verify` FAILed
        the old ones."""
        recs = self.records()
        old, new = recs["honest_buf1"], recs["honest_buf8"]
        ax = ["area_um2_sky130", "delay_ps_sky130"]
        # under the task's buf_8: the buf_1 record is not shown (it used to sit among the dominated), with the reason
        v = lb.build_axes_view(self.task8, [old, new], ax, identity=self.ident, input_drive=BUF8)
        self.assertEqual([r["record_hash"] for r in v["frontier"]], [new["record_hash"]])
        self.assertEqual(v["dominated"], [])
        self.assertEqual(v["input_drive"], BUF8)
        (hid,) = v["not_shown"]
        self.assertEqual(hid["record_hash"], old["record_hash"])
        self.assertIn("another input drive (sky130_fd_sc_hd__buf_1; the task's input drive is now sky130_fd_sc_hd__buf_8)",
                      hid["reason"])
        # the task back on buf_1: the other way round
        v = lb.build_axes_view(self.task1, [old, new], ax, identity=self.ident, input_drive=BUF1)
        self.assertEqual([r["record_hash"] for r in v["frontier"]], [old["record_hash"]])
        self.assertEqual([r["record_hash"] for r in v["not_shown"]], [new["record_hash"]])
        # not compared (--all-flows): both shown, as before
        v = lb.build_axes_view(self.task8, [old, new], ax)
        self.assertEqual(len(v["frontier"]) + len(v["dominated"]), 2)
        # the GE axes do not read the sky130 columns: the drive hides nothing there
        self.assertEqual(lb.build_axes_view(self.task8, [old], ["area_mge", "depth"], identity=self.ident,
                                            input_drive=BUF8)["not_shown"], [])
        # verify: the old record is STALE, offline and on a rescore (which weighs under the task's buf_8 now)
        for kw in ({"offline": True}, {"fresh": self.block("buf_8")}):
            r = self.verify(old, self.task8, **kw)
            self.assertEqual((r.status, r.fails), ("stale", []), kw)
            self.assertNotIn("ppa columns reproduced", r.notes)
        r = self.verify(old, self.task8, fresh=self.block("buf_8"))
        self.assertTrue(any("rescore: ppa columns not compared: recorded under the input drive sky130_fd_sc_hd__buf_1, "
                            "weighed now under sky130_fd_sc_hd__buf_8" in n for n in r.notes), r.notes)
        # ... and reproduced exactly under its own drive; the new record likewise under the task's
        r = self.verify(old, self.task1, fresh=self.block("buf_1"))
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("ppa columns reproduced", r.notes)
        r = self.verify(new, self.task8, fresh=self.block("buf_8"))
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("ppa columns reproduced", r.notes)
        # without verify_record's own comparison (no ppa_setup), the rescore still marks the drive change stale
        path = lb.store_record(os.path.join(self.tmp, "bare"), old, self.sv, self.lean)
        sc = old["score"]
        got = {"area_mge": sc["area_mge"], "depth": sc["depth"], "gates": sc["gates"], "num_gates": sc["num_gates"],
               "rtlil_sha256": sc["rtlil_sha256"], "sources": [{"canonical_sha256": old["canonical_sha256"]}],
               "ppa": self.block("buf_8")}
        r = lb.verify_record(path, old, self.task8, rescore=lambda sv: got)
        self.assertEqual((r.status, r.fails), ("stale", []))

    def test_the_rest_of_the_setup_is_compared_too(self):
        # a slew or output load the pins file the block names cannot have given: FAIL, offline already
        for k, v in (("pi_slew_ps", 40), ("po_load_ff", 20)):
            r = self.verify(self.rec(self.block("buf_8", **{k: v})), self.task8, offline=True)
            self.assertEqual(r.status, "FAIL", k)
            self.assertTrue(any(f"ppa.setup.{k} is {v}, but the pins file" in f for f in r.fails), r.fails)
        # any other setup difference from the fresh weighing: FAIL on the rescore (`setup` is in PPA_COMPARED)
        self.assertIn("setup", lb.PPA_COMPARED)
        r = self.verify(self.rec(self.block("buf_8", tables="extrapolated")), self.task8, fresh=self.block("buf_8"))
        self.assertEqual(r.status, "FAIL")
        self.assertTrue(any(f.startswith("rescore: ppa.setup recorded") for f in r.fails), r.fails)
        # a block of the current identity that names no drive is not comparable with the task's records
        nodrive = self.block("buf_8")
        del nodrive["setup"]["input_drive"]
        r = self.verify(self.rec(nodrive), self.task8, offline=True)
        self.assertEqual(r.status, "stale")
        self.assertTrue(any("another input drive (none named;" in s for s in r.stale), r.stale)

    def test_a_record_of_another_ppa_version_is_not_looked_at_for_its_drive(self):
        """A block of another identity is not comparable anyway (the rescore says so in a note, as before)."""
        rec = self.rec(self.block("buf_1"), ident={"ppa_version": "sky130_a0_v2", "ppa_pins_sha256": "1" * 64})
        r = self.verify(rec, self.task8, offline=True)
        self.assertEqual((r.status, r.fails, r.stale), ("ok", [], []))
        r = self.verify(rec, self.task8, fresh=self.block("buf_8"))
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertTrue(any("recorded under another ppa_version, ppa_pins_sha256" in n for n in r.notes), r.notes)

    def test_verify_and_pareto_cli(self):
        """`verify --offline` and `pareto --axes` read the task's drive themselves (task.json, else the pins' default)."""
        ident = lb.ppa_identity()                       # the CLI compares with the CURRENT identity: give the blocks it
        tasks = os.path.join(self.tmp, "tasks")
        os.makedirs(os.path.join(tasks, "add"))

        def put_task(task):
            with open(os.path.join(tasks, "add", "task.json"), "w") as fh:
                json.dump(task, fh)

        data = os.path.join(self.tmp, "data")
        recs = self.records(ident)
        for rec in recs.values():
            lb.store_record(data, rec, self.sv, self.lean)

        def run(*argv):
            return quiet(lb.main, list(argv[:1]) + ["--data-dir", data, "--tasks-dir", tasks] + list(argv[1:]))
        # (the task without its statement module: the review's records name none, and this test is about the drive)
        put_task({k: v for k, v in self.task8.items() if k != "statement"})
        rc, out, err = run("verify", "--offline")
        self.assertEqual(rc, 0, out + err)
        self.assertIn("3 records, 0 failed, 2 stale", out)
        lines = {ln.split(":")[0]: ln for ln in out.splitlines() if ln.startswith("[")}
        self.assertTrue(lines[f"[ok] add/{recs['honest_buf8']['record_hash'][:12]}"])
        for name in ("claims_buf1", "honest_buf1"):
            self.assertIn(f"[stale] add/{recs[name]['record_hash'][:12]}", lines)
        rc, out, err = run("pareto", "--task", "add", "--axes", "area_um2_sky130,delay_ps_sky130")
        self.assertEqual(rc, 0, err)
        self.assertIn("(1 of 1 records that carry the axes)", out)
        self.assertEqual(out.count("another input drive (sky130_fd_sc_hd__buf_1; the task's input drive is now "
                                   "sky130_fd_sc_hd__buf_8)"), 2)
        rc, out, err = run("pareto", "--task", "add", "--axes", "area_um2_sky130,delay_ps_sky130", "--all-flows")
        self.assertIn("records that carry the axes)", out)
        self.assertNotIn("not shown", out)
        put_task({k: v for k, v in self.task1.items() if k != "statement"})   # the task chooses buf_1: the buf_8 record is stale
        rc, out, err = run("verify", "--offline")
        self.assertEqual(rc, 0, out + err)
        self.assertIn("3 records, 0 failed, 1 stale", out)
        self.assertIn(f"[stale] add/{recs['honest_buf8']['record_hash'][:12]}", out)


class PpaMappedAxesTest(Tmp):
    """`pareto --axes` over the mapped columns (flow A1'): opt-in, exact integers, with its own identity."""
    AX = ["area_um2_sky130_mapped_v1", "mapped_delay_sky130_v1"]

    def rec(self, player, area_e4, delay, mapped=True, a0=(4604416, 2487), **kw):
        res = fake_result(flow=FLOW)
        with_ppa(res, area_e4=a0[0], delay_ps=a0[1],
                 mapped=(dict(area_e4=area_e4, delay_ps=delay, **kw) if mapped is True else mapped))
        return make_record(player=player, res=res)

    def view(self, recs, axes=None, **kw):
        return lb.build_axes_view(toy_task(), recs, axes or self.AX, **kw)

    def test_parse_axes_knows_the_mapped_columns_and_keeps_the_old_ones(self):
        self.assertEqual(lb.parse_axes(", ".join(self.AX)), self.AX)
        self.assertEqual(lb.parse_axes("mapped_cells_sky130_v1,mapped_levels_sky130_v1,area_um2_sky130"),
                         ["mapped_cells_sky130_v1", "mapped_levels_sky130_v1", "area_um2_sky130"])
        self.assertEqual(lb.AXES["area_um2_sky130"], ("ppa", "area_e4um2_sky130", lb._fmt_e4))     # A0''s axes as before
        self.assertEqual(lb.AXES["delay_ps_sky130"], ("ppa", "delay_ps_sky130", str))

    def test_the_frontier_is_over_the_mapped_columns_not_a0s(self):
        a = self.rec("a", 4000000, 3000, a0=(9000000, 9000))          # best mapped area, worst A0'
        b = self.rec("b", 6000000, 2000, a0=(4000000, 1000))
        c = self.rec("c", 7000000, 2500, a0=(1000000, 100))           # dominated on the mapped columns, best in A0'
        v = self.view([a, b, c])
        self.assertEqual([r["player"] for r in v["frontier"]], ["a", "b"])
        self.assertEqual([r["player"] for r in v["dominated"]], ["c"])
        self.assertEqual(v["frontier"][0]["values"], {"area_e4um2_sky130_mapped_v1": 4000000, "mapped_delay_sky130_v1": 3000})
        self.assertEqual(v["axis_fields"], {"area_um2_sky130_mapped_v1": "area_e4um2_sky130_mapped_v1",
                                            "mapped_delay_sky130_v1": "mapped_delay_sky130_v1"})
        # the A0' view of the same records is another frontier
        w = lb.build_axes_view(toy_task(), [a, b, c], ["area_um2_sky130", "delay_ps_sky130"])
        self.assertEqual([r["player"] for r in w["frontier"]], ["c"])
        # mixed axes (A0' area against mapped delay) are allowed: each axis is read from its own flow
        m = lb.build_axes_view(toy_task(), [a, b, c], ["area_um2_sky130", "mapped_delay_sky130_v1"])
        self.assertEqual([r["player"] for r in m["frontier"]], ["c", "b"])          # (1.0M, 2500) and (4.0M, 2000); a loses to b

    def test_records_without_the_mapped_columns_are_listed_with_the_reason(self):
        none = self.rec("none", 0, 0, mapped=None)
        gone = self.rec("gone", 0, 0, mapped={"available": False, "reason": "the mapping run failed: x"})
        good = self.rec("good", 4000000, 3000)
        v = self.view([none, gone, good])
        self.assertEqual([r["player"] for r in v["frontier"]], ["good"])
        why = {r["player"]: r["reason"] for r in v["not_shown"]}
        self.assertIn("no mapped (A1') columns", why["none"])
        self.assertIn("the mapped (A1') columns were not computed: the mapping run failed: x", why["gone"])
        # the A0' axes still show all three: the mapping is an annex
        w = lb.build_axes_view(toy_task(), [none, gone, good], ["area_um2_sky130", "delay_ps_sky130"])
        self.assertEqual(len(w["frontier"]) + len(w["dominated"]), 3)

    def test_mapped_columns_of_another_version_script_or_pins_are_not_ranked_against_the_current_ones(self):
        cur = {"ppa_mapped_version": "sky130_a1_v1", "liberty_sha256": "a" * 64, "ppa_mapped_pins_sha256": "e" * 64,
               "ppa_mapped_script_sha256": "f" * 64}
        a = self.rec("a", 4000000, 3000)
        for over, key in (({"ppa_mapped_version": "sky130_a1_v0"}, "ppa_mapped_version"),
                          ({"ppa_mapped_script_sha256": "1" * 64}, "ppa_mapped_script_sha256"),
                          ({"ppa_mapped_pins_sha256": "2" * 64}, "ppa_mapped_pins_sha256"),
                          ({"liberty_sha256": "3" * 64}, "liberty_sha256")):
            b = self.rec("b", 3000000, 2000, **over)
            v = self.view([a, b], mapped_identity=cur)
            self.assertEqual([r["player"] for r in v["frontier"]], ["a"], over)
            self.assertIn("mapped (A1') columns computed under another version", v["not_shown"][0]["reason"])
            self.assertIn(key, v["not_shown"][0]["reason"])
            self.assertEqual([r["player"] for r in self.view([a, b], mapped_identity=None)["frontier"]], ["b"])
        # an A0' identity says nothing about the mapped columns
        self.assertEqual(len(self.view([a], identity={"ppa_version": "other", "liberty_sha256": "a" * 64,
                                                      "ppa_pins_sha256": "b" * 64})["frontier"]), 1)
        self.assertIsNone(self.view([a], mapped_identity=cur, axes=["area_um2_sky130"])["ppa_mapped_identity"])
        self.assertEqual(self.view([a], mapped_identity=cur)["ppa_mapped_identity"], cur)

    def test_the_current_mapped_identity_is_read_from_the_pins_and_the_script(self):
        ident = lb.ppa_mapped_identity()
        self.assertEqual(set(ident), set(lb.PPA_MAPPED_IDENTITY))
        with open(lb.PPA_MAPPED_PINS, "rb") as fh:
            self.assertEqual(ident["ppa_mapped_pins_sha256"], lb.sha256_bytes(fh.read()))
        with open(lb.PPA_MAPPED_SCRIPT, "rb") as fh:
            self.assertEqual(ident["ppa_mapped_script_sha256"], lb.sha256_bytes(fh.read()))
        self.assertIsNone(lb.ppa_mapped_identity(pins_path=os.path.join(self.tmp, "absent.json")))

    def test_text_rendering(self):
        text = lb.render_axes_text(self.view([self.rec("a", 4404224, 6313), self.rec("b", 6000000, 2000)]))
        self.assertIn("Pareto frontier over (area_um2_sky130_mapped_v1, mapped_delay_sky130_v1) at N=16 (2 of 2 records", text)
        self.assertIn("440.4224", text)
        self.assertIn("6313", text)


class PpaCliTest(Tmp):
    """`add` / `verify` / `pareto --axes` through the CLI, with the fake check.py."""

    def setUp(self):
        super().setUp()
        self.env = CliEnv(self)
        self.log = os.path.join(self.tmp, "argv.log")
        os.environ["FAKE_ARGV_LOG"] = self.log

    def tearDown(self):
        for k in ("FAKE_ARGV_LOG", "FAKE_PPA", "FAKE_MODE", "FAKE_MAPPED"):
            os.environ.pop(k, None)

    def argv_log(self):
        with open(self.log) as fh:
            return [ln.strip() for ln in fh if ln.strip()]

    def records(self):
        return [r for _, r, _ in lb.load_records(self.env.data, "toy")]

    def test_add_runs_check_py_with_ppa_require_and_records_the_block(self):
        rc, out, err = self.env.add("alice")
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.argv_log()[-1].split()[-4:], ["--ppa", "require", "--postsynth", "full"])
        (rec,) = self.records()
        self.assertEqual(rec["ppa"]["area_e4um2_sky130"], 4604416)
        self.assertEqual(rec["schema"], "svgolf-leaderboard-record/1")
        self.assertIn("the ranked sky130 score (A0', sky130_a0_v1): 460.4416 um^2, 2487 ps", out)

    def test_a_light_record_still_asks_for_the_columns(self):
        sv, lean = self.env.files("lighty")
        rc, out, err = self.env.run("add", "--task", "toy", "--player", "lighty", "--sv", sv, "--lean", lean,
                                    "--date", "2026-10-29", "--postsynth", "light")
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.argv_log()[-1].split()[-4:], ["--ppa", "require", "--postsynth", "light"])

    def test_add_records_and_prints_the_mapped_columns_and_verify_full_reproduces_them(self):
        os.environ["FAKE_MAPPED"] = json.dumps(fake_mapped(cells=10))
        rc, out, err = self.env.add("alice")
        self.assertEqual(rc, 0, err)
        (rec,) = self.records()
        self.assertEqual(rec["ppa"]["mapped"]["area_e4um2_sky130_mapped_v1"], 4404224)
        self.assertEqual(rec["ppa"]["area_e4um2_sky130"], 4604416)                       # A0' beside it, unchanged
        self.assertIn("sky130 mapped columns (A1', real abc -liberty; extra and unranked): 440.4224 um^2, 6313 ps, 10 cells "
                      "(sky130_a1_v1)", out)
        self.assertEqual(self.env.run("verify", "--offline")[0], 0)
        rc, out, err = self.env.run("verify", "--full")
        self.assertEqual(rc, 0, out + err)
        self.assertIn("ppa.mapped columns reproduced", out)

    def test_add_says_so_when_the_design_could_not_be_mapped(self):
        os.environ["FAKE_MAPPED"] = "unavailable"
        rc, out, err = self.env.add("alice")
        self.assertEqual(rc, 0, err)
        (rec,) = self.records()
        self.assertEqual(rec["ppa"]["mapped"], {"available": False, "reason": "the mapping run failed: x"})
        self.assertIn("NOTE: the sky130 mapped (A1') columns were not computed: the mapping run failed: x", out)

    def test_pareto_axes_over_the_mapped_columns_cli(self):
        ident = lb.ppa_mapped_identity()
        self.assertEqual(set(ident), set(lb.PPA_MAPPED_IDENTITY))
        for player, area, delay in (("alice", 4000000, 3000), ("bob", 6000000, 2000), ("carol", 7000000, 2500)):
            sv_sha = lb.sha256_bytes(SV_TEXT + f"// {player}\n".encode())
            res = with_ppa(fake_result(sv_sha=sv_sha), mapped=dict(area_e4=area, delay_ps=delay, **ident))
            self.assertEqual(self.env.add(player, from_check=self.env.write_result(res))[0], 0)
        self.assertEqual(self.env.add("old", from_check=self.env.write_result(
            with_ppa(fake_result(sv_sha=lb.sha256_bytes(SV_TEXT + b"// old\n")))))[0], 0)       # A0' columns, no mapped
        rc, out, err = self.env.run("pareto", "--task", "toy", "--axes", "area_um2_sky130_mapped_v1,mapped_delay_sky130_v1")
        self.assertEqual(rc, 0, err)
        self.assertIn("Pareto frontier over (area_um2_sky130_mapped_v1, mapped_delay_sky130_v1)", out)
        self.assertIn("(2 of 3 records that carry the axes)", out)
        self.assertIn("old: no mapped (A1') columns", out)
        rc, js, _ = self.env.run("pareto", "--task", "toy", "--axes", "area_um2_sky130_mapped_v1,mapped_delay_sky130_v1",
                                 "--format", "json")
        view = json.loads(js)
        self.assertEqual([r["player"] for r in view["frontier"]], ["alice", "bob"])
        self.assertEqual(view["ppa_mapped_identity"], ident)
        # the A0' axes see all four records (the mapped sub-object is an annex)
        rc, out, err = self.env.run("pareto", "--task", "toy", "--axes", "area_um2_sky130,delay_ps_sky130", "--all-flows")
        self.assertIn("of 4 records that carry the axes", out)
        # without --axes: the ranked board, whose A0' identity is the current one (the fake's dummy hashes are not)
        self.assertIn("(0 of 0 ranked records)", self.env.run("pareto", "--task", "toy")[1])

    def test_verify_full_runs_check_py_with_ppa_require(self):
        self.assertEqual(self.env.add("alice")[0], 0)
        open(self.log, "w").close()
        rc, out, err = self.env.run("verify", "--full")
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(self.argv_log()[-1].split()[-4:], ["--ppa", "require", "--postsynth", "full"])
        self.assertIn("ppa columns reproduced", out)

    def test_verify_full_of_a_record_made_before_the_columns_does_not_need_the_liberty(self):
        os.environ["FAKE_PPA"] = "none"                # a checker from before the columns: no `ppa` in the result
        self.assertEqual(self.env.add("old")[0], 0)
        self.assertNotIn("ppa", self.records()[0])
        os.environ.pop("FAKE_PPA")
        open(self.log, "w").close()
        rc, out, err = self.env.run("verify", "--full")
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(self.argv_log()[-1].split()[-4:], ["--ppa", "off", "--postsynth", "full"])
        self.assertFalse(any("ppa" in ln for ln in out.splitlines() if ln.startswith("[")), out)

    def test_an_absent_liberty_is_an_infrastructure_error_never_a_record(self):
        os.environ["FAKE_MODE"] = "infra"          # what `check.py --ppa require` answers with no liberty (exit 2)
        rc, out, err = self.env.add("alice")
        self.assertEqual(rc, 2)
        self.assertIn("infrastructure", err)
        self.assertFalse(os.path.exists(self.env.data))

    def test_from_check_with_an_auto_run_that_found_no_liberty_is_refused(self):
        sv_sha = lb.sha256_bytes(SV_TEXT + b"// alice\n")
        res = fake_result(sv_sha=sv_sha)
        res["ppa"] = {"available": False, "reason": "liberty not found: /x"}
        res["stages"]["ppa"] = {"mode": "auto", "seconds": 0.0}
        rc, out, err = self.env.add("alice", from_check=self.env.write_result(res))
        self.assertEqual(rc, 1)
        self.assertIn("--ppa require", err)
        # a stored result without the key (an old checker, or --ppa off) is a record without the columns
        rc, out, err = self.env.add("alice", from_check=self.env.write_result(fake_result(sv_sha=sv_sha)))
        self.assertEqual(rc, 0, err)
        self.assertNotIn("ppa", self.records()[0])
        # ... and `add` says so, instead of printing an official-looking line with nothing on it
        self.assertIn("NOTE: this record carries no sky130 columns", out)
        self.assertIn("--ppa off", out)
        self.assertIn("NOT RANKED until it is backfilled", out)

    def test_pareto_axes_cli(self):
        ident = lb.ppa_identity()                   # the columns of the CURRENT version (pins file + pinned liberty)
        self.assertEqual(set(ident), set(lb.PPA_IDENTITY))
        for player, area, delay in (("alice", 4000000, 3000), ("bob", 6000000, 2000), ("carol", 7000000, 2500)):
            sv_sha = lb.sha256_bytes(SV_TEXT + f"// {player}\n".encode())
            res = with_ppa(fake_result(sv_sha=sv_sha), area_e4=area, delay_ps=delay, **ident)
            self.assertEqual(self.env.add(player, from_check=self.env.write_result(res))[0], 0)
        self.assertEqual(self.env.add("old", from_check=self.env.write_result(
            fake_result(sv_sha=lb.sha256_bytes(SV_TEXT + b"// old\n"))))[0], 0)
        rc, out, err = self.env.run("pareto", "--task", "toy", "--axes", "area_um2_sky130,delay_ps_sky130")
        self.assertEqual(rc, 0, err)
        self.assertIn("Pareto frontier over (area_um2_sky130, delay_ps_sky130)", out)
        self.assertIn("(2 of 3 records that carry the axes)", out)
        self.assertIn("alice", out)
        self.assertIn("bob", out)
        self.assertIn("not shown (1)", out)
        self.assertIn("no PPA columns", out)
        self.assertNotIn("carol", out.split("not shown")[0])
        rc, js, _ = self.env.run("pareto", "--task", "toy", "--axes", "area_um2_sky130,delay_ps_sky130",
                                 "--format", "json")
        view = json.loads(js)
        self.assertEqual([r["player"] for r in view["frontier"]], ["alice", "bob"])
        # each value is named after the record field it came from, so the unit is in the name (1e-4 um^2)
        self.assertEqual(view["frontier"][0]["values"], {"area_e4um2_sky130": 4000000, "delay_ps_sky130": 3000})
        self.assertEqual(view["axis_fields"], {"area_um2_sky130": "area_e4um2_sky130",
                                               "delay_ps_sky130": "delay_ps_sky130"})
        self.assertNotIn("area_um2_sky130", view["frontier"][0]["values"])
        # columns computed under another version of the pins / liberty are not ranked (--all-flows ranks everything)
        os.environ["FAKE_PPA"] = "weighed"
        self.assertEqual(self.env.add("dave")[0], 0)          # the fake check.py's own (dummy-hash) identity
        rc, out, err = self.env.run("pareto", "--task", "toy", "--axes", "area_um2_sky130,delay_ps_sky130")
        self.assertIn("dave: PPA columns computed under another version", out)
        rc, out, err = self.env.run("pareto", "--task", "toy", "--axes", "area_um2_sky130,delay_ps_sky130",
                                    "--all-flows")
        self.assertIn("dave", out.split("not shown")[0])
        rc, out, err = self.env.run("pareto", "--task", "toy", "--axes", "nonsense")
        self.assertEqual(rc, 2)
        self.assertIn("unknown axes", err)
        # without --axes: the ranked board, (sky130 area, time) under the current identity, the same frontier
        rc, plain, _ = self.env.run("pareto", "--task", "toy")
        self.assertEqual(rc, 0)
        self.assertIn("Pareto frontier of (sky130 area, time) at N=16 (2 of 3 ranked records)", plain)
        self.assertIn("dave: sky130 columns computed under another version", plain)
        self.assertIn("old: no sky130 columns", plain)
        self.assertNotIn("carol", plain.split("not ranked")[0])


class ParTest(Tmp):
    """PAR (item 12 of the 11/05 newcomer study): the board shows the best proved reference by area x time, the ONE
    ranked number (leaderboard/combined.py), from the reference player's records that rank on it."""
    REF = lb.REFERENCE_PLAYER

    def rec(self, player, tag, area_e4, delay, **kw):
        return make_record(player=player, sv=SV_TEXT + f"// {tag}\n".encode(), sky=(area_e4, delay), **kw)

    @staticmethod
    def listed(*recs):
        """`names` (reference_names' shape) listing these records' designs, in this order, as task.json would."""
        return {r["files"]["sv"]["sha256"]: (i, f"ref{i}") for i, r in enumerate(recs)}

    def test_the_best_area_times_time_of_the_reference_player(self):
        task = toy_task()
        small = self.rec(self.REF, "small", 1000000, 3000)      # the smaller area: 3.0e9
        fast = self.rec(self.REF, "fast", 1200000, 2000)        # the smaller product: 2.4e9
        player = self.rec("alice", "alice", 500000, 1000)       # better still, but an entry, not par
        par = lb.par_of(task, [small, fast, player], flow=FLOW, names=self.listed(small, fast))
        self.assertEqual((par["record_hash"], par["exact"]), (fast["record_hash"], 1200000 * 2000))
        self.assertAlmostEqual(par["um2ns"], 240.0)
        self.assertEqual(par["name"], "ref1")                    # the stem task.json lists
        self.assertIsNone(lb.par_of(task, [player], flow=FLOW, names=self.listed(player)))

    def test_par_comes_only_from_a_listed_reference(self):
        """Decided 2026-11-12: a record of the reference player whose design task.json does not list is never par,
        however it scores; without the listing there is no par."""
        task = toy_task()
        listed = self.rec(self.REF, "listed", 1000000, 3000)
        other = self.rec(self.REF, "other", 500000, 1000)       # better, under the reference handle, not listed
        par = lb.par_of(task, [listed, other], flow=FLOW, names=self.listed(listed))
        self.assertEqual((par["record_hash"], par["name"]), (listed["record_hash"], "ref0"))
        self.assertIsNone(lb.par_of(task, [other], flow=FLOW, names=self.listed(listed)))
        self.assertIsNone(lb.par_of(task, [listed, other], flow=FLOW))

    def test_a_tie_goes_to_the_reference_listed_first(self):
        task = toy_task()
        a = self.rec(self.REF, "a", 1000000, 2000, date="2026-10-30")
        b = self.rec(self.REF, "b", 2000000, 1000, date="2026-10-29")
        names = {a["files"]["sv"]["sha256"]: (0, "first_ref"), b["files"]["sv"]["sha256"]: (1, "second_ref")}
        self.assertEqual(lb.par_of(task, [b, a], flow=FLOW, names=names)["name"], "first_ref")
        names = {a["files"]["sv"]["sha256"]: (1, "first_ref"), b["files"]["sv"]["sha256"]: (0, "second_ref")}
        self.assertEqual(lb.par_of(task, [a, b], flow=FLOW, names=names)["name"], "second_ref")

    def test_a_reference_record_that_does_not_rank_is_not_par(self):
        task = toy_task()
        stale = self.rec(self.REF, "stale", 1000000, 2000, flow=dict(FLOW, script_sha256="8" * 64))
        nocols = make_record(player=self.REF, sv=SV_TEXT + b"// nocols\n")
        names = self.listed(stale, nocols)
        self.assertIsNone(lb.par_of(task, [stale, nocols], flow=FLOW, names=names))
        self.assertEqual(lb.par_of(task, [stale], flow=None, names=names)["record_hash"], stale["record_hash"])

    def test_rendered_on_the_board_and_the_pareto_text(self):
        task = toy_task()
        ref = self.rec(self.REF, "ref", 1000000, 2000)
        board = lb.build_board(task, [ref], flow=FLOW)
        self.assertNotIn("Par,", lb.render_markdown(board))       # a board built alone has no par line
        self.assertNotIn("Par:", lb.render_markdown(board))
        board["par"] = lb.par_of(task, [ref], flow=FLOW, names={ref["files"]["sv"]["sha256"]: (0, "ref_n")})
        md = lb.render_markdown(board)
        self.assertIn("Par, the best proved reference by area x time (the ranked number; lower is better): "
                      f"`ref_n`: 100.0000 um^2 x 2000 ps = 200.00 um2*ns (record `{ref['record_hash'][:12]}`).", md)
        self.assertIn("  Par, the best proved reference by area x time", lb.render_pareto_text(board))
        board["par"] = None
        self.assertIn("Par: none recorded (no record of `svgolf-reference` ranks here", lb.render_markdown(board))

    def test_the_board_command_shows_par(self):
        env = CliEnv(self)
        os.environ["FAKE_SKY"] = "current"
        self.addCleanup(os.environ.pop, "FAKE_SKY", None)
        rc, md, _ = env.run("board", "--task", "toy")
        self.assertEqual(rc, 0)
        self.assertIn("Par: none recorded", md)
        # the reference handle is `seed-references`' own (decided 2026-11-12): par is a listed reference of task.json
        self.assertEqual(env.add(self.REF)[0], 1)
        ref = os.path.join(env.tasks, "toy", "reference")
        os.makedirs(ref)
        sv, lean = env.files("ref_n")
        shutil.copy(sv, os.path.join(ref, "ref_n.sv"))
        shutil.copy(lean, os.path.join(ref, "ref_n.lean"))
        with open(os.path.join(env.tasks, "toy", "task.json"), "w") as fh:
            json.dump(toy_task(leaderboard={"depth_budget": 22},
                               references=[{"sv": "reference/ref_n.sv", "lean": "reference/ref_n.lean"}]), fh)
        rc, out, err = env.run("seed-references", "--task", "toy")
        self.assertEqual(rc, 0, out + err)
        self.assertIn("seeded toy: reference/ref_n.sv", out)
        rc, out, err = env.add("alice")                 # add prints the ranked number of a record it makes
        self.assertEqual(rc, 0, err)
        self.assertIn("(area x time ", out)
        rc, md, _ = env.run("board", "--task", "toy")
        self.assertIn("Par, the best proved reference by area x time (the ranked number; lower is better): "
                      "`ref_n`: ", md)
        rc, js, _ = env.run("board", "--task", "toy", "--format", "json")
        self.assertEqual(json.loads(js)["par"]["player"], self.REF)
        rc, out, _ = env.run("pareto", "--task", "toy")
        self.assertIn("Par, the best proved reference", out)

    def test_every_ranked_task_shows_par_from_the_committed_records(self):
        """The shipped reference records give every listed task a par (site/config.json `listed`/`tutorial`), and
        it agrees with the site's par where the site has a sky130 golden for the reference."""
        with open(os.path.join(SVGOLF, "site", "config.json")) as fh:
            listing = json.load(fh)["tasks"]
        for t, kind in sorted(listing.items()):
            if kind not in ("listed", "tutorial"):
                continue
            with self.subTest(task=t):
                par = lb.par_now(t)
                if REAL_FLOW["yosys"] is None:
                    continue                 # no Yosys here: no record is comparable with this machine's flow
                self.assertIsNotNone(par, f"{t}: no par (seed its references: leaderboard.py seed-references --task {t})")
                task = lb.load_task(lb.DEFAULT_TASKS, t)
                self.assertIn(par["name"], [os.path.splitext(os.path.basename(r["sv"]))[0] for r in task["references"]])

    def test_an_unproved_result_is_refused_by_name(self):
        res = fake_result()
        res.update(accepted=False, stage="unproved", errors=[], notes=["--unproved: every check ..."],
                   unproved_ok=True)
        problems = lb.acceptance_problems(res, toy_task(), SV_SHA)
        self.assertIn("check.py --unproved", problems[0])


def _load_by_path(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(SVGOLF, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


class StatementTest(unittest.TestCase):
    """A record names the trusted statement it was checked under (decided 2026-11-07, round 7b review M1):
    `checker.statement` maps the task's statement files (the statement module and the svgolf/ modules it imports,
    transitively) to their sha256; the board, par, the Pareto view and `verify` treat a record checked under another
    statement, or made before records named theirs, as stale and unranked instead of ranking it."""

    def test_the_statement_files_of_each_kind(self):
        def files(t):
            return lb.statement_files(lb.load_task(lb.DEFAULT_TASKS, t))
        self.assertEqual(files("add"), ["tasks/add/Spec.lean", "SvGolf/Task.lean"])
        self.assertEqual(files("fdivp"), ["tasks/fdivp/Spec.lean", "SvGolf/Task.lean", "tasks/fdivp/IEEE754.lean"])
        self.assertEqual(files("matmul"), ["tasks/matmul/Spec.lean", "SvGolf/TaskSeq.lean", "SvGolf/Task.lean"])
        self.assertEqual(files("arbiter"), ["tasks/arbiter/Spec.lean", "SvGolf/TaskReact.lean", "SvGolf/TaskSeq.lean",
                                            "SvGolf/Task.lean"])
        now = lb.current_statement(lb.load_task(lb.DEFAULT_TASKS, "add"))
        self.assertEqual(now["SvGolf/Task.lean"], lb.sha256_file(os.path.join(lb.SVGOLF, "SvGolf", "Task.lean")))
        with self.assertRaises(lb.Refused):
            lb.statement_files({"name": "x", "statement": {"module": "tasks.nope.Spec"}})

    def ranked(self, sky=(4604416, 2611)):
        return make_record(sky=sky)

    def test_a_record_carries_the_statement_and_is_ranked_only_under_it(self):
        task = toy_task()
        now = {"SvGolf/Task.lean": "a" * 64, "tasks/toy/Spec.lean": "b" * 64}
        res = with_ppa(fake_result(sv_sha=lb.sha256_bytes(SV_TEXT)), area_e4=4604416, delay_ps=2611)
        rec = lb.build_record(task, res, player="alice", assisted_by=[], notes="", submitted_at="2026-11-07",
                              sv_name="/x/toy.sv", sv_bytes=SV_TEXT, lean_name="/x/toy.lean", lean_bytes=LEAN_TEXT,
                              environment=dict(ENV, statement=now))
        self.assertEqual(lb.validate_record(rec), [])
        self.assertEqual(rec["checker"]["statement"], now)
        self.assertIsNone(lb.unranked_reason(rec, task, statement=now))
        other = dict(now, **{"tasks/toy/Spec.lean": "c" * 64})
        why = lb.unranked_reason(rec, task, statement=other)
        self.assertEqual(why, "checked under another statement (tasks/toy/Spec.lean differ)")
        board = lb.build_board(task, [rec], statement=other)
        self.assertEqual((board["ranking"], [r["reason"] for r in board["unranked"]]), ([], [why]))
        self.assertIsNone(lb.par_of(task, [dict(rec, player=lb.REFERENCE_PLAYER)], statement=other,
                                    names={rec["files"]["sv"]["sha256"]: (0, "toy")}))
        self.assertEqual(len(lb.build_board(task, [rec], statement=now)["ranking"]), 1)
        self.assertEqual(len(lb.build_board(task, [rec])["ranking"]), 1)           # not compared without one
        # a record made before records named their statement: stale, not ranked
        old = make_record(sky=(4604416, 2611))
        self.assertNotIn("statement", old["checker"])
        self.assertEqual(lb.unranked_reason(old, task, statement=now),
                         "checked before records named the statement they were checked under (2026-11-07)")
        for bad in ({}, {"SvGolf/Task.lean": "x"}, {"Task": "a" * 64}, ["a" * 64]):
            r2 = copy.deepcopy(rec)
            r2["checker"]["statement"] = bad
            self.assertTrue(any("checker.statement" in p for p in lb.validate_record(r2)), bad)

    def test_verify_calls_another_statement_stale(self):
        tmp = tempfile.mkdtemp(prefix="svgolf-lb-stmt-")
        self.addCleanup(shutil.rmtree, tmp, ignore_errors=True)
        now = {"SvGolf/Task.lean": "a" * 64}
        rec = lb.build_record(toy_task(), fake_result(sv_sha=lb.sha256_bytes(SV_TEXT)), player="alice", assisted_by=[],
                              notes="", submitted_at="2026-11-07", sv_name="/x/toy.sv", sv_bytes=SV_TEXT,
                              lean_name="/x/toy.lean", lean_bytes=LEAN_TEXT, environment=dict(ENV, statement=now))
        path = lb.store_record(tmp, rec, SV_TEXT, LEAN_TEXT)
        r = lb.verify_record(path, rec, toy_task(), statement=now)
        self.assertFalse(any("statement" in x for x in r.stale), r.stale)
        r = lb.verify_record(path, rec, toy_task(), statement={"SvGolf/Task.lean": "d" * 64})
        self.assertEqual(r.status, "stale")
        self.assertIn("checked under another statement (SvGolf/Task.lean differ): not ranked", r.stale)


class ClockedRecordTest(Tmp):
    """The clocked record format (decided 2026-11-07): for a task of a CLOCKED_KINDS kind, acceptance requires
    `stages.postsynth.points` (every point of the task, full mode, every seed, 0 mismatches); the record keeps those
    points; it carries the flow of its kind (`checker.flow` "seq", the hashes of svgolf_seq.ys and ge_seq.json); and the
    board, the rescore (`--seq`) and verify compare it only with the current flow of its own kind. On the arbiter's real
    accepted check result (tests/leaderboard/clocked_arbiter/)."""

    def test_a_seeds_power_up_draws_are_kept_and_checked(self):
        """F5 (2026-11-07): a seed of a clocked check records the power-ups it drew from the salt, Verilator's
        `netlist_randseed` and ls-sv's `lssv_start`; the record keeps both, and validation holds them to their forms."""
        task, res, sv = arbiter_fixture()
        res = copy.deepcopy(res)
        for q in res["stages"]["postsynth"]["points"]:
            for x in q["seeds"]:
                x["netlist_randseed"] = 1234567 + x["seed"]
                x["lssv_start"] = "zeros" if x["seed"] == 0 else f"seed:{100 + x['seed']}"
        rec = arbiter_record(res)
        self.assertEqual(lb.validate_record(rec), [])
        kept = rec["postsynth"]["points"][0]["seeds"]
        self.assertEqual([(x["netlist_randseed"], x["lssv_start"]) for x in kept],
                         [(1234567, "zeros"), (1234568, "seed:101"), (1234569, "seed:102")])
        for k, bad, why in (("netlist_randseed", 0, "Verilator's randSeed"), ("netlist_randseed", 2 ** 31,
                                                                            "Verilator's randSeed"),
                            ("lssv_start", "seed:-1", "ls-sv's power-up"), ("lssv_start", "x", "ls-sv's power-up")):
            r2 = copy.deepcopy(rec)
            r2["postsynth"]["points"][0]["seeds"][1][k] = bad
            self.assertTrue(any(why in p for p in lb.validate_record(r2)), (k, bad))

    def test_the_arbiters_result_is_accepted_and_keeps_its_points(self):
        task, res, sv = arbiter_fixture()
        self.assertEqual(lb.acceptance_problems(res, task, lb.sha256_bytes(sv)), [])
        rec = arbiter_record()
        self.assertEqual(lb.validate_record(rec), [])
        c, s, ps = rec["checker"], rec["score"], rec["postsynth"]
        self.assertEqual((c["flow"], lb.record_flow(rec)), ("seq", "seq"))
        rs = res["stages"]["score"]
        self.assertEqual((c["script_sha256"], c["ge_table_sha256"], c["canon_script_sha256"]),
                         (rs["script_sha256"], rs["ge_table_sha256"], rs["canon_script_sha256"]))
        self.assertTrue(c["verilator"].startswith("Verilator 5.042"))
        self.assertEqual((s["area_um2"], s["period_ps"], s["cycles"], s["time_ps"], s["ffs"], s["area_mge"], s["depth"]),
                         (769.488, 2826, 1, 2826, 16, 188979, 17))
        self.assertEqual(s["scoring_point"], {"N": 8})
        self.assertEqual((ps["mode"], ps["mismatches"]), ("full", 0))
        self.assertEqual(ps["netlist_sha256"], res["ppa"]["netlist_sha256"])
        self.assertEqual([(q["point"], q["params"], q["mode"], q["mismatches"], q["latency"]) for q in ps["points"]],
                         [("N=3", {"N": 3}, "full", 0, None), ("N=5", {"N": 5}, "full", 0, None),
                          ("N=8", {"N": 8}, "full", 0, None)])
        by_point = {x["point"]: x for x in res["stages"]["postsynth"]["points"]}
        for q in ps["points"]:
            self.assertEqual(q["netlist_sha256"], by_point[q["point"]]["netlist_sha256"])
            self.assertEqual([x["seed"] for x in q["seeds"]], [0, 1, 2])
            for kept, given in zip(q["seeds"], by_point[q["point"]]["seeds"]):
                # the facts of the run are kept, its timings are not
                # (this fixture's run predates F5, 2026-11-07: no `netlist_randseed`, `lssv_start` in it)
                self.assertEqual(kept, {k: given[k] for k in ("seed", "cycles", "reset_cycles", "salted", "seed_sha256",
                                                              "segments", "netlist_randseed", "lssv_start")
                                        if k in given})
        self.assertEqual([sum(x["cycles"] for x in q["seeds"]) for q in ps["points"]], [210519, 210683, 211527])
        self.assertNotIn("vectors", ps)

    def test_ranked_and_par_under_the_flow_of_its_kind(self):
        """The finding the format answers (the record's flow is the clocked one, the board compared it with the
        combinational one and never ranked it): compared with the current flow of its kind it ranks, and is par."""
        task, _, _ = arbiter_fixture()
        rec = arbiter_record()
        board = lb.build_board(task, [rec], flow=arbiter_flow())
        self.assertEqual(board["unranked"], [])
        (row,) = board["ranking"]
        self.assertEqual((row["rank"], row["area_e4um2"], row["time_ps"], row["cycles"], row["period_ps"], row["exact"]),
                         (1, 7694880, 2826, 1, 2826, 7694880 * 2826))
        self.assertIn("| 1 | svgolf-reference | Claude (Anthropic) | 2174.57 | 769.4880 | 2826 (1 x 2826) |",
                      lb.render_markdown(board))
        par = lb.par_of(task, [rec], flow=arbiter_flow(), names={rec["files"]["sv"]["sha256"]: (0, "rr_mask")})
        self.assertEqual((par["name"], par["record_hash"]), ("rr_mask", rec["record_hash"]))
        self.assertIn("`rr_mask`: 769.4880 um^2 x 2826 (1 x 2826) ps = 2174.57 um2*ns", lb.fmt_par(par))
        # the combinational flow is another flow for it, by name and by its two hashes
        comb = dict(arbiter_flow(), flow="comb", script_sha256=FLOW["script_sha256"],
                    ge_table_sha256=FLOW["ge_table_sha256"])
        (un,) = lb.build_board(task, [rec], flow=comb)["unranked"]
        self.assertEqual(un["reason"], "checked under another flow (flow, ge_table_sha256, script_sha256 differ)")
        # a clocked task ranks only clocked records, whatever flow it is handed
        other = make_record(dict(toy_task(), name="arbiter", scoring={"params": {"N": 8}, "depth_budget": None}),
                            "comb", res=fake_result(task="arbiter", point={"N": 8}), sky=(90000, 3000))
        self.assertEqual({r["player"]: r["reason"] for r in lb.build_board(task, [rec, other], flow=None)["unranked"]},
                         {"comb": "scored under the comb flow, and a react-family task is scored under the seq flow "
                                  "(svgolf_seq.ys, ge_seq.json)"})

    def test_verified_offline_and_by_rescore(self):
        task, res, sv = arbiter_fixture()
        rec = arbiter_record()
        path = self.store(rec, sv=sv, lean=ARB_LEAN)
        r = lb.verify_record(path, rec, task, flow=arbiter_flow())
        self.assertEqual((r.status, r.fails, r.stale), ("ok", [], []))
        ge_seq_now = lb.sha256_file(os.path.join(SVGOLF, "score", "ge_seq.json"))
        if ge_seq_now == rec["checker"]["ge_table_sha256"]:
            # the area arithmetic is checked against the clocked flow's GE table, the one the record names
            self.assertNotIn("GE table differs from the recorded one: area arithmetic not rechecked", r.notes)
            bad = copy.deepcopy(rec)
            bad["score"]["gates"].update(DFF_P=15, AND=27)      # the same gate count, another area
            bad["record_hash"] = lb.compute_record_hash(bad)
            bpath = self.store(bad, sv=sv, lean=ARB_LEAN)
            self.assertIn("score.area_mge is not the sum of the gate weights in score/ge_seq.json",
                          lb.verify_record(bpath, bad, task).fails)
        # the rescore: score.py --seq's result (the score, the canonical text, the RTLIL) and ppa.py --seq's columns
        rs = res["stages"]["score"]
        honest = dict({k: rs[k] for k in ("area_mge", "depth", "gates", "num_gates", "rtlil_sha256", "sources")},
                      ppa=dict(res["ppa"]))
        r = lb.verify_record(path, rec, task, flow=arbiter_flow(), rescore=lambda _sv: honest)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("rescored: same score", r.notes)
        self.assertIn("ppa columns reproduced", r.notes)
        r = lb.verify_record(path, rec, task, flow=arbiter_flow(),
                             rescore=lambda _sv: dict(honest, ppa=dict(res["ppa"], delay_ps_sky130=2900)))
        self.assertIn("rescore: ppa.delay_ps_sky130 recorded 2826, now 2900", r.fails)
        # under the combinational flow it is stale, and no rescore runs
        called = []
        r = lb.verify_record(path, rec, task, flow=dict(FLOW, flow="comb"), rescore=called.append)
        self.assertEqual((r.status, called), ("stale", []))
        self.assertIn("rescore skipped: the flow has changed", r.notes)
        # a record whose flow is not its task's kind's is stale whatever flow is handed
        r = lb.verify_record(path, rec, dict(task, kind="comb-family"))
        self.assertEqual(r.status, "stale")
        self.assertIn("scored under the seq flow, and a comb-family task is scored under the comb flow "
                      "(svgolf.ys, ge.json): the score is not comparable with the task's", r.stale)

    def test_the_rescore_runs_the_clocked_flow(self):
        seen = []

        class Done:
            returncode, stderr = 0, ""
            stdout = json.dumps({"score": {"area_mge": 1}, "ppa": {"area_e4um2_sky130": 1}})

        def run(argv, **kw):
            seen.append(argv[2:])
            return Done()
        with mock.patch.object(lb.subprocess, "run", run):
            lb.run_rescore("d.sv", "tasks/t", ppa_py="ppa.py", seq=True)
            lb.run_rescore("d.sv", "tasks/t", seq=True)
            lb.run_rescore("d.sv", "tasks/t", ppa_py="ppa.py")
            lb.run_rescore("d.sv", "tasks/t", ppa_py="ppa.py", mapped=False)
        self.assertEqual(seen[0], ["d.sv", "--task", "tasks/t", "--seq", "--no-mapped"])
        self.assertEqual(seen[1][-1], "--seq")
        self.assertEqual(seen[2], ["d.sv", "--task", "tasks/t"])                       # combinational: as before
        self.assertEqual(seen[3], ["d.sv", "--task", "tasks/t", "--no-mapped"])

    def test_each_clocked_rejection_is_refused(self):
        task, base, sv = arbiter_fixture()
        sha = lb.sha256_bytes(sv)

        def problems(change, postsynth="full"):
            res = copy.deepcopy(base)
            change(res)
            return " | ".join(lb.acceptance_problems(res, task, sha, postsynth))

        def pts(res):
            return res["stages"]["postsynth"]["points"]
        self.assertEqual(problems(lambda r: None), "")
        cases = [
            (lambda r: r["stages"]["postsynth"].pop("points"), "has no `stages.postsynth.points`"),
            (lambda r: r["stages"].update(postsynth={"point": "N=8", "vectors": 500, "mismatches": 0}),
             "has no `stages.postsynth.points`"),
            (lambda r: pts(r).pop(1), "did not run at every point of the task: ['N=5'] missing"),
            (lambda r: pts(r).append(dict(pts(r)[0], point="N=4")), "points the task does not list: ['N=4']"),
            (lambda r: pts(r).append(copy.deepcopy(pts(r)[0])), "lists the points ['N=3'] more than once"),
            (lambda r: pts(r)[0].update(mismatches=2), "points['N=3'] did not pass: mismatches 2"),
            (lambda r: pts(r)[0].update(report=[{"seed": 0}]), "did not pass"),
            (lambda r: pts(r)[2].update(mode="light"), "points['N=8'] ran in LIGHT mode"),
            (lambda r: pts(r)[0].update(kind="tx-family"), "a check of the kind 'tx-family'"),
            (lambda r: pts(r)[1]["seeds"].pop(), "did not run every seed of the task: seeds [0, 1], not the task's "
                                                 "0 to 2"),
            (lambda r: pts(r)[1]["seeds"][0].pop("cycles"), "seed 0 does not record its cycles"),
            (lambda r: pts(r)[1]["seeds"][0].pop("segments"), "points['N=5'] seed 0 does not record its segments"),
            (lambda r: pts(r)[0].update(latency=3), "checked the latency 3, not the point's None"),
            (lambda r: pts(r)[0].pop("netlist_sha256"), "has no netlist sha256"),
            (lambda r: r["stages"]["postsynth"].update(netlist_sha256=pts(r)[0]["netlist_sha256"]),
             "not the netlist checked at the scoring point"),
            (lambda r: r["ppa"].update(netlist_sha256="0" * 64), "the `ppa` block weighed another netlist"),
            (lambda r: r["stages"]["score"].pop("flow"), "is scored by the clocked flow"),
            (lambda r: r["score"].pop("time_ps"), "the result's score lacks ['time_ps']"),
            (lambda r: r["score"].update(cycles=2), "score.cycles 2 is not the declared latency"),
        ]
        for change, frag in cases:
            self.assertIn(frag, problems(change), frag)
        # a light check at a point: a light record (marked, never ranked), never an official one
        self.assertEqual(problems(lambda r: pts(r)[2].update(mode="light"), postsynth="light"), "")
        light = copy.deepcopy(base)
        pts(light)[2]["mode"] = "light"
        rec = arbiter_record(light, postsynth="light")
        self.assertEqual((rec["postsynth"]["mode"], [q["mode"] for q in rec["postsynth"]["points"]]),
                         ("light", ["full", "full", "light"]))
        self.assertIn("ran LIGHT", lb.unranked_reason(rec, task, flow=arbiter_flow()))
        # the task's own seeds count: a task that asks for 8 seeds refuses a result with 3
        self.assertIn("not the task's 0 to 7", " | ".join(lb.acceptance_problems(
            base, dict(task, postsynth=dict(task["postsynth"], seeds=8)), sha)))
        # and a combinational task refuses a clocked result
        comb = dict(toy_task(), name="arbiter", scoring={"params": {"N": 8}, "depth_budget": None}, time_limit_s=120)
        self.assertIn("a combinational task is scored by the combinational flow",
                      " | ".join(lb.acceptance_problems(base, comb, sha)))

    def test_every_clocked_kind_keeps_its_own_count(self):
        """A seed keeps the count its kind's check makes (CLOCKED_SEED_UNIT): the transactions of a tx-family or
        stream-family run (check.py logs them, the record counts them), the segments of a react-family one, nothing
        but its cycles for a seq-family one; a seed without its kind's count is refused."""
        for kind, unit in (("tx-family", "transactions"), ("stream-family", "transactions"),
                           ("react-family", "segments"), ("seq-family", None)):
            with self.subTest(kind=kind):
                task = clocked_task(kind=kind)
                res = fake_clocked_result(task, latency=2 if kind in ("tx-family", "stream-family") else None)
                for q in res["stages"]["postsynth"]["points"]:
                    for s in q["seeds"]:
                        s.pop("transactions")
                        if unit == "transactions":
                            s[unit] = [{"tag": "t", "start": 1 + 3 * j} for j in range(24)]
                        elif unit == "segments":
                            s.update(segments=24, longest_segment=70000)
                rec = make_record(task, "p", res=res)
                self.assertEqual(lb.validate_record(rec), [])
                seed = rec["postsynth"]["points"][0]["seeds"][1]
                self.assertEqual(seed, dict({"seed": 1, "cycles": 301, "reset_cycles": 1},
                                            **({unit: 24} if unit else {})))
                self.assertEqual(rec["score"]["cycles"], 2 if kind in ("tx-family", "stream-family") else 1)
                if unit:
                    res["stages"]["postsynth"]["points"][1]["seeds"][0].pop(unit)
                    self.assertIn(f"seed 0 does not record its {unit}",
                                  " | ".join(lb.acceptance_problems(res, task, SV_SHA)))

    def test_each_point_is_held_to_its_own_latency(self):
        """F8 (decided 2026-11-08): check.py has the kernel evaluate the proved latency function at every clocked point
        (`latency_at`) and checks each point at its own `lat p`; acceptance holds every point to that value and the
        scoring point's to the declared n, the record keeps each point's, validation holds the scoring point's to
        `score.cycles` (the others only the kernel gives), and `verify --full` holds each to a fresh check's. A result
        without `latency_at` (an older checker) is held to the declared n at every point, as before."""
        task = clocked_task()                                   # tx-family, points N=2 and N=16 (the scoring point)
        base = fake_clocked_result(task, latency=4)
        base["latency_at"] = {"N=2": 2, "N=16": 4}
        base["stages"]["postsynth"]["points"][0]["latency"] = 2

        def problems(change):
            res = copy.deepcopy(base)
            change(res)
            return " | ".join(lb.acceptance_problems(res, task, SV_SHA))
        self.assertEqual(problems(lambda r: None), "")
        for change, frag in (
                (lambda r: r.pop("latency_at"), "points['N=2'] checked the latency 2, not the point's 4"),
                (lambda r: r["latency_at"].update({"N=2": 3}), "points['N=2'] checked the latency 2, not the point's 3"),
                (lambda r: r["latency_at"].update({"N=16": 5}), "latency_at gives the scoring point 5, not the "
                                                                 "declared 4"),
                (lambda r: r["latency_at"].pop("N=2"), "does not give a latency for each clocked point"),
                (lambda r: r["latency_at"].update({"N=3": 6}), "does not give a latency for each clocked point"),
                (lambda r: r["latency_at"].update({"N=2": 0}), "does not give a latency for each clocked point"),
                (lambda r: r["stages"]["postsynth"]["points"][1].update(latency=2),
                 "points['N=16'] checked the latency 2, not the point's 4")):
            self.assertIn(frag, problems(change), frag)
        # the record keeps each point's latency; the score counts the scoring point's
        rec = make_record(task, "p", res=base)
        self.assertEqual(lb.validate_record(rec), [])
        self.assertEqual([(q["point"], q["latency"]) for q in rec["postsynth"]["points"]], [("N=2", 2), ("N=16", 4)])
        self.assertEqual((rec["score"]["cycles"], rec["score"]["time_ps"]), (4, 4000))

        def invalid(change):
            bad = copy.deepcopy(rec)
            change(bad["postsynth"]["points"])
            return " | ".join(lb.validate_record(bad))
        self.assertIn("score.cycles 4 is not the latency the check used at ['N=16']",
                      invalid(lambda q: q[1].update(latency=2)))
        self.assertIn("declare a latency at some points and none at others", invalid(lambda q: q[0].update(latency=None)))
        self.assertEqual(invalid(lambda q: q[0].update(latency=7)), "")      # another point's is the kernel's to say
        # verify --full: each point's latency against the fresh check's, whatever the flow
        path = self.store(rec)
        r = lb.verify_record(path, rec, task, flow=SEQ, recheck=lambda sv, lean: base)
        self.assertEqual((r.status, r.fails), ("ok", []))
        self.assertIn("rechecked: accepted, same canonical text and axioms", r.notes)
        other = copy.deepcopy(base)
        other["stages"]["postsynth"]["points"][0]["latency"] = 3
        for flow in (SEQ, dict(SEQ, script_sha256="9" * 64)):
            r = lb.verify_record(path, rec, task, flow=flow, recheck=lambda sv, lean: other)
            self.assertIn("recheck: the latency at N=2 recorded 2, now 3", r.fails)
        other["stages"]["postsynth"]["points"].pop(0)
        r = lb.verify_record(path, rec, task, flow=SEQ, recheck=lambda sv, lean: other)
        self.assertIn("recheck: no post-synthesis check at N=2", r.fails)

    def test_a_stored_record_of_several_parameters_stays_valid(self):
        """check.py names a point in the task's parameter order (matmul: `N=2,W=4,AccW=8`) and the record file is
        written with sorted keys, so a reloaded point's params come back as {AccW, N, W}: the point is still named
        after them (found seeding matmul's reference, 2026-11-08: its record was valid in memory and malformed on
        disk)."""
        task = clocked_task(scoring={"params": {"N": 4, "W": 8, "AccW": 32}, "depth_budget": None},
                            postsynth={"points": [{"N": 2, "W": 4, "AccW": 8}, {"N": 4, "W": 8, "AccW": 32}], "seeds": 2})
        res = fake_clocked_result(task, latency=4)
        res["latency_at"] = {"N=2,W=4,AccW=8": 2, "N=4,W=8,AccW=32": 4}
        res["stages"]["postsynth"]["points"][0]["latency"] = 2
        self.assertEqual(lb.acceptance_problems(res, task, SV_SHA), [])
        rec = make_record(task, "p", res=res)
        self.assertEqual(lb.validate_record(rec), [])
        path = self.store(rec)
        with open(path) as fh:
            back = json.load(fh)
        self.assertEqual([(q["point"], list(q["params"])) for q in back["postsynth"]["points"]],
                         [("N=2,W=4,AccW=8", ["AccW", "N", "W"]), ("N=4,W=8,AccW=32", ["AccW", "N", "W"])])
        self.assertEqual(lb.validate_record(back), [])
        self.assertEqual(lb.verify_record(path, back, task, flow=SEQ).status, "ok")
        # still refused: a name of other values, or of a parameter fewer or more
        for name in ("N=2,W=4,AccW=9", "N=2,W=4", "N=2,W=4,AccW=8,K=1", "AccW=8,N=2,W=4,N=2"):
            bad = copy.deepcopy(back)
            bad["postsynth"]["points"][0]["point"] = name
            self.assertIn(f"postsynth.points[0].point {name!r} is not the name of its params",
                          " | ".join(lb.validate_record(bad)), name)

    def test_the_record_is_held_together(self):
        """validate_record (no task needed): the points, their seeds and the record's own score and `ppa` block."""
        rec = arbiter_record()

        def problems(change):
            bad = copy.deepcopy(rec)
            change(bad)
            return " | ".join(lb.validate_record(bad))

        def pts(r):
            return r["postsynth"]["points"]
        cases = [
            (lambda r: r["checker"].pop("flow"), "is the score of a record of the clocked flow"),
            (lambda r: r["checker"].pop("flow"), "postsynth must record vectors and mismatches 0"),
            (lambda r: r["checker"].update(flow="comb"), "checker.flow must be 'seq'"),
            (lambda r: r["postsynth"].pop("points"), "postsynth.points must be a non-empty list"),
            (lambda r: r["postsynth"].update(vectors=500), "unknown keys ['vectors']"),
            (lambda r: r["postsynth"].update(mismatches=1), "postsynth.mismatches must be 0"),
            (lambda r: r["postsynth"].update(mode="light"), "'light' exactly when one of its points ran light"),
            (lambda r: pts(r)[0].update(point="N=4"), "'N=4' is not the name of its params {'N': 3}"),
            (lambda r: pts(r)[0].update(mismatches=3), "postsynth.points[0].mismatches must be 0"),
            (lambda r: pts(r)[0].pop("seeds"), "must have exactly the keys"),
            (lambda r: pts(r)[0]["seeds"].reverse(), "seeds must be the seeds 0 to 2, in order"),
            (lambda r: pts(r)[0]["seeds"][0].update(segments=24, transactions=24), "at most one of segments"),
            (lambda r: pts(r)[0]["seeds"][0].update(segments=-1), "at most one of segments, transactions (a non-"),
            (lambda r: pts(r)[0]["seeds"][0].update(t_lssv_s=1.2), "unknown keys ['t_lssv_s']"),
            (lambda r: pts(r)[1].update(params={"N": 3}, point="N=3"), "lists a point twice"),
            (lambda r: pts(r).pop(2), "has no check at the scoring point"),
            (lambda r: r["postsynth"].update(netlist_sha256=pts(r)[0]["netlist_sha256"]),
             "postsynth.netlist_sha256 is not the netlist checked at the scoring point"),
            (lambda r: r["ppa"].update(netlist_sha256="0" * 64), "the sky130 columns weighed another netlist"),
            (lambda r: pts(r)[2].update(latency=2), "score.cycles 1 is not the latency the check used at ['N=8']"),
            # F8 (2026-11-08): another point's latency is its own `lat p`, but a kind declares one at every point or none
            (lambda r: pts(r)[0].update(latency=2), "declare a latency at some points and none at others: N=3: 2, "
                                                    "N=5: None, N=8: None"),
        ]
        for change, frag in cases:
            self.assertIn(frag, problems(change), frag)
        # a combinational record never carries the clocked form
        comb = make_record()
        comb["postsynth"]["points"] = []
        self.assertIn("postsynth.points is the post-synthesis check of a clocked record", " | ".join(
            lb.validate_record(comb)))

    def test_add_board_and_verify_from_the_command_line(self):
        """`add --from-check` (a --data-dir trial) records the arbiter's result, `board` ranks it and `verify` passes
        it, each comparing it with the clocked flow of this tree, never with the combinational one."""
        task, res, sv = arbiter_fixture()
        tasks, data = os.path.join(self.tmp, "tasks"), os.path.join(self.tmp, "data")
        os.makedirs(os.path.join(tasks, "arbiter"))
        with open(os.path.join(tasks, "arbiter", "task.json"), "w") as fh:
            json.dump(task, fh)
        paths = {}
        for name, data_ in (("rr_mask.sv", sv), ("rr_mask.lean", ARB_LEAN), ("check.json", json.dumps(res).encode())):
            paths[name] = os.path.join(self.tmp, name)
            with open(paths[name], "wb") as fh:
                fh.write(data_)

        def run(*argv):
            return quiet(lb.main, list(argv[:1]) + ["--data-dir", data, "--tasks-dir", tasks] + list(argv[1:]))
        # (the reference handle is refused here since 2026-11-12: `seed-references` alone records under it)
        rc, _, err = run("add", "--task", "arbiter", "--player", lb.REFERENCE_PLAYER, "--sv", paths["rr_mask.sv"],
                         "--lean", paths["rr_mask.lean"], "--date", "2026-11-07", "--from-check", paths["check.json"],
                         "--assisted-by", "Claude (Anthropic)")
        self.assertEqual(rc, 1)
        self.assertIn(lb.RESERVED_HANDLE, err)
        rc, out, err = run("add", "--task", "arbiter", "--player", "arb-golfer", "--sv", paths["rr_mask.sv"],
                           "--lean", paths["rr_mask.lean"], "--date", "2026-11-07", "--from-check", paths["check.json"],
                           "--assisted-by", "Claude (Anthropic)")
        self.assertEqual(rc, 0, err)
        self.assertIn("769.4880 um^2, 2826 (1 x 2826) ps (188.979 GE, depth 17)", out)
        self.assertIn("post-synthesis check (clocked): full mode at 3 point(s), N=3 (3 seeds, 210519 cycles), "
                      "N=5 (3 seeds, 210683 cycles), N=8 (3 seeds, 211527 cycles), 0 mismatches", out)
        rc, md, _ = run("board", "--task", "arbiter", "--all-flows")
        self.assertIn("| 1 | arb-golfer | Claude (Anthropic) | 2174.57 | 769.4880 | 2826 (1 x 2826) |", md)
        rc, js, _ = run("board", "--task", "arbiter", "--format", "json")
        board = json.loads(js)
        if lb.flow_mismatch(lb.flow_of(arbiter_record()), REAL_SEQ_FLOW):
            # this tree's clocked flow is another one than the run's (a later svgolf_seq.ys): stale, and why
            (un,) = board["unranked"]
            self.assertTrue(un["reason"].startswith("checked under another flow ("), un["reason"])
            self.assertNotIn("(flow,", un["reason"])          # compared with the clocked flow, not the combinational
        else:
            self.assertEqual([r["player"] for r in board["ranking"]], ["arb-golfer"])
            self.assertIsNone(board["par"])                 # no reference record here: no par
        rc, out, _ = run("verify", "--offline", "--task", "arbiter")
        self.assertEqual(rc, 0, out)
        self.assertIn("verify (offline): 1 records, 0 failed", out)
        self.assertNotIn("(flow,", out)


class KindsAndFlowsTest(unittest.TestCase):
    """leaderboard.py's kinds, flow files and defaults agree with the checker's own (check.py, check/postsynth.py,
    score/score.py, score/points.py, check/envelope.py)."""

    def test_the_flows_are_score_pys(self):
        self.assertEqual({k: tuple(os.path.basename(p) for p in v) for k, v in score.FLOWS.items()}, lb.FLOW_FILES)
        for name, (script, table) in lb.FLOW_FILES.items():
            now = lb.current_flow(SVGOLF, name)
            self.assertEqual((now["flow"], now["script_sha256"], now["ge_table_sha256"]),
                             (name, lb.sha256_file(os.path.join(SVGOLF, "score", script)),
                              lb.sha256_file(os.path.join(SVGOLF, "score", table))))
        self.assertEqual(lb.current_flow(), lb.current_flow(SVGOLF, "comb"))
        self.assertEqual(lb.current_flows(), {n: lb.current_flow(SVGOLF, n) for n in ("comb", "seq")})

    def test_the_kinds_are_the_checkers(self):
        try:
            check = _load_by_path("svgolf_check_for_lb_test", "check.py")
        except ImportError as e:            # check.py needs python3.12 and its packages
            self.skipTest(f"check.py cannot be loaded here: {e}")
        postsynth, points = check.postsynth, _load_by_path("svgolf_points_for_lb_test", "score/points.py")
        for kind in check.KINDS:
            with self.subTest(kind=kind):
                want = kind in check.CLOCKED_KINDS
                self.assertEqual(kind in lb.CLOCKED_KINDS, want)
                self.assertEqual(kind in postsynth.CLOCKED_KINDS, want)
                self.assertEqual(kind in points.CLOCKED_KINDS, want)
                self.assertEqual(lb.task_flow({"kind": kind}), "seq" if want else "comb")
        self.assertEqual(lb.CLOCKED_SEEDS_DEFAULT, postsynth.CLOCKED_DEFAULTS["seeds"])
        self.assertEqual((lb.CLOCKED_SEEDS_DEFAULT, postsynth.REACT_DEFAULTS["seeds"]), (8, 8))     # F5, 2026-11-07
        self.assertEqual(points.FLOW_FILES, lb.FLOW_FILES)
        for t in lb.all_task_names(lb.DEFAULT_TASKS):
            task = lb.load_task(lb.DEFAULT_TASKS, t)
            if lb.is_clocked_task(task):
                with self.subTest(task=t):
                    pts = lb.clocked_points(task)
                    self.assertIn(lb.scoring_point(task), pts)
                    self.assertEqual([lb.point_text(q) for q in pts], [check.point_str(q) for q in pts])
                    self.assertEqual(lb.clocked_seeds(task), postsynth.config(task)["seeds"])


def asap7_entry_of(rec, area_e5, delay, of=None, cycles=None):
    """An ASAP7 entry (leaderboard/asap7/<task>.json) bound to the record `rec` (its canonical text, RTLIL, GE columns,
    cycles and scored netlist), weighing `area_e5` (1e-5 um^2) and `delay` ps."""
    b = rec.get("ppa") or {}
    return {"sv_sha256": rec["files"]["sv"]["sha256"], "of": of or [f"record:{rec['record_hash']}"],
            "canonical_sha256": rec["canonical_sha256"], "rtlil_sha256": rec["score"].get("rtlil_sha256") or "7" * 64,
            "netlist_sha256": b.get("netlist_sha256") or "8" * 64, "area_mge": rec["score"]["area_mge"],
            "depth": rec["score"]["depth"], "area_e5um2": area_e5, "delay_ps": delay, "cycles": cycles,
            "time_ps": delay * (cycles or 1), "cells": 10, "flops": None, "buffers": 0, "tie_cells": 0,
            "repaired_sha256": "9" * 64, "table_reads_floored": 3}


A7_IDENT = {"ppa_version": "asap7_a0_v1", "liberty_sha256": "1" * 64, "ppa_pins_sha256": "2" * 64,
            "input_drive": "BUFx8_ASAP7_75t_R"}


def asap7_table(task, entries, identity=None, flow=None):
    return {"schema": lb.ASAP7_SCHEMA, "task": task["name"], "scoring_point": lb.scoring_point(task),
            "flow": dict(flow or {"flow": "comb", **FLOW}), "identity": dict(identity or A7_IDENT),
            "ppa_script_sha256": "3" * 64, "designs": sorted(entries, key=lambda e: e["sv_sha256"])}


class Asap7ViewTest(Tmp):
    """The ASAP7 view (decided 2026-11-09: a reader may see the golf scores on ASAP7; sky130 stays the default and the
    records' own columns): its columns kept beside the records (leaderboard/asap7/<task>.json), bound to each record,
    ranked by the same rules, checked by `verify` and `asap7`."""

    def three(self):
        """Three ranked sky130 records whose ASAP7 order differs from their sky130 order."""
        task = toy_task()
        a = make_record(player="alice", sv=b"module a;endmodule\n", sky=(4000000, 2000))    # sky130 8000.0, best
        b = make_record(player="bob", sv=b"module b;endmodule\n", sky=(4100000, 2100))      # sky130 8610.0
        c = make_record(player="carol", sv=b"module c;endmodule\n", sky=(5000000, 1900))    # sky130 9500.0
        table = asap7_table(task, [asap7_entry_of(a, 700000, 600), asap7_entry_of(b, 690000, 560),
                                   asap7_entry_of(c, 800000, 500)])
        return task, [a, b, c], table

    def test_the_file_is_checked_for_shape_and_arithmetic(self):
        task, recs, table = self.three()
        self.assertEqual(lb.asap7_file_problems(table, "toy"), [])
        for mutate, frag in ((lambda t: t["designs"][0].update(time_ps=1), "time_ps"),
                             (lambda t: t["designs"][0].pop("cells"), "keys must be exactly"),
                             (lambda t: t["designs"].reverse(), "sv_sha256 order"),
                             (lambda t: t["designs"][0].update(of=["player:x"]), "`of`"),
                             (lambda t: t.update(schema="x"), "schema"),
                             (lambda t: t["identity"].pop("input_drive"), "identity"),
                             (lambda t: t.update(extra=1), "unexpected")):
            bad = copy.deepcopy(table)
            mutate(bad)
            self.assertTrue(any(frag in p for p in lb.asap7_file_problems(bad, "toy")), frag)
        self.assertTrue(lb.asap7_file_problems(table, "other"))

    def test_the_board_ranks_the_asap7_columns_by_the_same_rules(self):
        task, recs, table = self.three()
        sky = lb.build_board(task, recs, flow=FLOW)
        self.assertEqual([r["player"] for r in sky["ranking"]], ["alice", "bob", "carol"])
        a7 = lb.build_board(task, recs, flow=FLOW, pdk="asap7", asap7=table, asap7_identity=A7_IDENT)
        # 6.9 um^2 x 560 ps (bob) < 7 x 600 (alice) < 8 x 500 (carol): 3.864, 4.0 and 4.2 um2*ns
        self.assertEqual([r["player"] for r in a7["ranking"]], ["bob", "carol", "alice"])
        self.assertEqual([r["exact"] for r in a7["ranking"]], [690000 * 560, 800000 * 500, 700000 * 600])
        self.assertEqual(a7["ranking"][0]["um2ns"], 690000 * 560 / 1e8)
        self.assertEqual([r["rank"] for r in a7["ranking"]], [1, 2, 3])
        self.assertEqual((a7["pdk"], a7["ranked_axes"]), ("asap7", ["area_um2_asap7", "time_ps"]))
        for r in a7["ranking"]:
            self.assertIn("area_e5um2", r)
            self.assertNotIn("area_e4um2", r)
        # Pareto layers on the ASAP7 axes: bob dominates alice; carol is on the front
        self.assertEqual({r["player"] for r in a7["frontier"]}, {"bob", "carol"})
        self.assertEqual(sky["pdk"], "sky130")
        md = lb.render_markdown(a7)
        self.assertIn(lb.ASAP7_BOARD_NOTE, md)
        self.assertIn("| 6.90000 | 560 |", md)
        self.assertIn("| 3.8640 |", md)

    def test_ties_share_a_rank_on_asap7_too(self):
        task, recs, table = self.three()
        for e in table["designs"]:
            e.update(area_e5um2=700000, delay_ps=600, time_ps=600)
        a7 = lb.build_board(task, recs, flow=FLOW, pdk="asap7", asap7=table, asap7_identity=A7_IDENT)
        self.assertEqual([r["rank"] for r in a7["ranking"]], [1, 1, 1])
        # equal products: the board's later keys (GE area, depth, date, hash) order them, as on sky130
        self.assertEqual([r["record_hash"] for r in a7["ranking"]],
                         [r["record_hash"] for r in sorted((lb.row_of(x, "asap7", table) for x in recs),
                                                           key=lb.score_key)])

    def test_a_record_without_comparable_asap7_columns_is_not_ranked_there(self):
        task, (a, b, c), table = self.three()
        cases = []
        cases.append(("no table", None, "no ASAP7 columns for task toy"))
        t1 = copy.deepcopy(table)
        t1["designs"] = [e for e in t1["designs"] if e["sv_sha256"] != a["files"]["sv"]["sha256"]]
        cases.append(("no entry", t1, "no ASAP7 columns for its design"))
        t2 = copy.deepcopy(table)
        lb.asap7_entry(t2, a["files"]["sv"]["sha256"])["netlist_sha256"] = "0" * 64
        cases.append(("another netlist", t2, "not of its netlist"))
        t3 = copy.deepcopy(table)
        lb.asap7_entry(t3, a["files"]["sv"]["sha256"])["area_mge"] += 1
        cases.append(("other GE columns", t3, "not of its netlist"))
        cases.append(("another version", asap7_table(task, table["designs"], identity=dict(A7_IDENT, ppa_version="x")),
                      "another version"))
        cases.append(("another flow", asap7_table(task, table["designs"], flow={"flow": "comb", **GOLD_FLOW}),
                      "another flow"))
        for what, tab, frag in cases:
            with self.subTest(what):
                why = lb.unranked_reason(a, task, flow=FLOW, pdk="asap7", asap7=tab, asap7_identity=A7_IDENT)
                self.assertIn(frag, why or "")
                board = lb.build_board(task, [a, b, c], flow=FLOW, pdk="asap7", asap7=tab, asap7_identity=A7_IDENT)
                self.assertIn(a["record_hash"], [r["record_hash"] for r in board["unranked"]])
                self.assertNotIn(a["record_hash"], [r["record_hash"] for r in board["ranking"]])
        # the sky130 board does not look at the ASAP7 columns at all
        self.assertIsNone(lb.unranked_reason(a, task, flow=FLOW, asap7=None))

    def test_par_of_the_asap7_view(self):
        task, recs, table = self.three()
        refs = [dict(r, player=lb.REFERENCE_PLAYER) for r in recs]
        for r in refs:
            r["record_hash"] = lb.compute_record_hash(r)
        table = asap7_table(task, [asap7_entry_of(r, e["area_e5um2"], e["delay_ps"])
                                   for r, e in zip(refs, (asap7_entry_of(x, 700000, 600) for x in refs))])
        ents = {r["files"]["sv"]["sha256"]: v for r, v in zip(refs, ((700000, 600), (690000, 560), (800000, 500)))}
        for e in table["designs"]:
            e.update(area_e5um2=ents[e["sv_sha256"]][0], delay_ps=ents[e["sv_sha256"]][1], time_ps=ents[e["sv_sha256"]][1])
        names = {r["files"]["sv"]["sha256"]: (i, f"ref{i}") for i, r in enumerate(refs)}
        sky = lb.par_of(task, refs, flow=FLOW, names=names)
        a7 = lb.par_of(task, refs, flow=FLOW, pdk="asap7", asap7=table, asap7_identity=A7_IDENT, names=names)
        self.assertEqual(sky["exact"], 4000000 * 2000)
        self.assertEqual((a7["exact"], a7["area_e5um2"]), (690000 * 560, 690000))
        self.assertIn("6.90000 um^2 x 560 ps = 3.8640 um2*ns", lb.fmt_par(a7))

    def test_verify_checks_the_entry_of_each_record(self):
        task, (a, b, c), table = self.three()
        path = self.store(a, sv=b"module a;endmodule\n")
        fresh = {k: v for k, v in lb.asap7_entry(table, a["files"]["sv"]["sha256"]).items() if k in lb.ASAP7_COMPARED}

        def view(tab, rescore=None, error=None):
            return {"table": tab, "error": error, "identity": A7_IDENT, "rescore": rescore}
        r = lb.verify_record(path, a, task, asap7_view=view(table, rescore=lambda sv: dict(fresh)))
        self.assertEqual(r.fails, [])
        self.assertIn("ASAP7 columns reproduced", r.notes)
        r = lb.verify_record(path, a, task, asap7_view=view(table, rescore=lambda sv: dict(fresh, delay_ps=601)))
        self.assertTrue(any("asap7: delay_ps recorded 600, now 601" in f for f in r.fails), r.fails)
        bad = copy.deepcopy(table)
        lb.asap7_entry(bad, a["files"]["sv"]["sha256"])["canonical_sha256"] = "0" * 64
        r = lb.verify_record(path, a, task, asap7_view=view(bad))
        self.assertTrue(any("not of its netlist: canonical text" in f for f in r.fails), r.fails)
        r = lb.verify_record(path, a, task, asap7_view=view(None))
        self.assertEqual(r.fails, [])
        self.assertTrue(any("no columns for task toy" in n for n in r.notes))
        none = copy.deepcopy(table)
        none["designs"] = [e for e in none["designs"] if e["sv_sha256"] != a["files"]["sv"]["sha256"]]
        r = lb.verify_record(path, a, task, asap7_view=view(none))
        self.assertEqual((r.fails, r.status), ([], "ok"))
        self.assertTrue(any("no columns for this design" in n for n in r.notes))
        r = lb.verify_record(path, a, task, asap7_view=view(None, error="leaderboard/asap7/toy.json: not JSON"))
        self.assertTrue(r.fails)
        old = asap7_table(task, table["designs"], identity=dict(A7_IDENT, ppa_pins_sha256="0" * 64))
        r = lb.verify_record(path, a, task, asap7_view=view(old, rescore=lambda sv: {}))
        self.assertEqual(r.fails, [])
        self.assertTrue(any("another version" in n for n in r.notes))
        r = lb.verify_record(path, a, task)               # without a view: as before the ASAP7 view
        self.assertFalse(any("ASAP7" in n for n in r.notes))

    def test_the_check_covers_every_design_and_binds_it(self):
        task, (a, b, c), table = self.three()
        expected = {"tasks": {}}
        designs = lb.asap7_designs(task, [a, b, c], expected, data_dir=self.data)
        self.assertEqual(sorted(designs), sorted(e["sv_sha256"] for e in table["designs"]))
        self.assertEqual(lb.asap7_check(task, table, designs, identity=A7_IDENT, flow=FLOW), ([], []))
        short = copy.deepcopy(table)
        short["designs"] = short["designs"][1:]
        fails, _ = lb.asap7_check(task, short, designs, identity=A7_IDENT, flow=FLOW)
        self.assertTrue(any(f.startswith("no entry for record:") for f in fails), fails)
        fails, _ = lb.asap7_check(task, table, {k: v for k, v in designs.items() if k != a["files"]["sv"]["sha256"]},
                                  identity=A7_IDENT, flow=FLOW)
        self.assertTrue(any("an entry for no design" in f for f in fails), fails)
        moved = copy.deepcopy(table)
        lb.asap7_entry(moved, b["files"]["sv"]["sha256"])["rtlil_sha256"] = "0" * 64
        fails, _ = lb.asap7_check(task, moved, designs, identity=A7_IDENT, flow=FLOW)
        self.assertTrue(any("rtlil_sha256" in f for f in fails), fails)
        same = lambda e, d: {k: e[k] for k in lb.ASAP7_COMPARED}           # noqa: E731
        self.assertEqual(lb.asap7_check(task, table, designs, identity=A7_IDENT, flow=FLOW, rescore=same), ([], []))
        off = lambda e, d: dict(same(e, d), cells=e["cells"] + 1)          # noqa: E731
        fails, _ = lb.asap7_check(task, table, designs, identity=A7_IDENT, flow=FLOW, rescore=off)
        self.assertEqual(len(fails), 3)
        _, notes = lb.asap7_check(task, table, designs, identity=dict(A7_IDENT, ppa_version="x"), flow=FLOW,
                                  rescore=off)
        self.assertTrue(any("not comparable" in n for n in notes), notes)

    def test_the_columns_of_a_weighing(self):
        score = {"sources": [{"canonical_sha256": "c" * 64}], "rtlil_sha256": "d" * 64, "area_mge": 1000, "depth": 3}
        ppa = {"pdk": "asap7", "area_e5um2_asap7": 699840, "delay_ps_asap7": 563, "netlist_sha256": "e" * 64,
               "cells_asap7": 80, "repair": {"buffers": 1, "tie_cells": 0, "netlist_sha256": "f" * 64},
               "legality": {"table_reads_floored": 124}}
        cols = lb.asap7_columns_of(score, ppa, None)
        self.assertEqual(set(cols), set(lb.ASAP7_COMPARED))
        self.assertEqual((cols["time_ps"], cols["area_e5um2"], cols["buffers"]), (563, 699840, 1))
        self.assertEqual(lb.asap7_columns_of(score, dict(ppa, flops=8), 4)["time_ps"], 4 * 563)
        with self.assertRaises(RuntimeError):
            lb.asap7_columns_of(score, dict(ppa, pdk="sky130"), None)

    def test_the_identity_is_read_from_the_pins(self):
        ident = lb.asap7_identity()
        self.assertEqual(set(ident), set(lb.ASAP7_IDENTITY))
        self.assertEqual(ident["ppa_version"], "asap7_a0_v1")
        self.assertEqual(ident["liberty_sha256"], "5ece07acb7ece6a9fad109eadccbf88cce141dd8aa02f877205ee706cc99057a")
        self.assertEqual(ident["input_drive"], "BUFx8_ASAP7_75t_R")
        self.assertIsNone(lb.asap7_identity(os.path.join(self.tmp, "none.json")))

    def test_the_cli_boards_take_pdk(self):
        task, recs, table = self.three()
        env = CliEnv(self)
        for r, sv in zip(recs, (b"module a;endmodule\n", b"module b;endmodule\n", b"module c;endmodule\n")):
            lb.store_record(env.data, r, sv, LEAN_TEXT)
        a7dir = os.path.join(self.tmp, "asap7")
        os.makedirs(a7dir)
        with open(os.path.join(a7dir, "toy.json"), "w") as fh:
            json.dump(table, fh)
        rc, out, err = env.run("board", "--task", "toy", "--pdk", "asap7", "--all-flows", "--format", "json",
                               "--asap7-dir", a7dir)
        self.assertEqual(rc, 0, err)
        board = json.loads(out)
        self.assertEqual([r["player"] for r in board["ranking"]], ["bob", "carol", "alice"])
        self.assertEqual(board["pdk"], "asap7")
        rc, out, err = env.run("pareto", "--task", "toy", "--pdk", "asap7", "--all-flows", "--asap7-dir", a7dir)
        self.assertEqual(rc, 0, err)
        self.assertIn("Pareto frontier of (ASAP7 area, time)", out)
        rc, out, err = env.run("board", "--task", "toy", "--all-flows", "--format", "json", "--asap7-dir", a7dir)
        self.assertEqual([r["player"] for r in json.loads(out)["ranking"]], ["alice", "bob", "carol"])
        rc, out, err = env.run("pareto", "--task", "toy", "--pdk", "asap7", "--axes", "area_mge,depth")
        self.assertEqual(rc, 2)


class CommittedAsap7Test(unittest.TestCase):
    """The committed ASAP7 columns (leaderboard/asap7/): every file well-formed, covering exactly the designs each task's
    pages show, every entry bound to its sources, measured under the current ASAP7 pins and the pinned flow
    (tests/expected.json), so the site's ASAP7 view ranks every record the sky130 view ranks."""

    def test_every_task_with_designs_has_its_file_and_it_binds(self):
        with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
            expected = json.load(fh)
        recs = lb.good_records(lb.load_records(lb.DEFAULT_DATA))
        ident = lb.asap7_identity()
        for name in lb.all_task_names(lb.DEFAULT_TASKS):
            task = lb.load_task(lb.DEFAULT_TASKS, name)
            designs = lb.asap7_designs(task, recs, expected)
            if not designs:
                continue
            with self.subTest(task=name):
                table, why = lb.read_asap7(name)
                self.assertIsNone(why)
                self.assertIsNotNone(table, f"no leaderboard/asap7/{name}.json")
                pin = expected["flow_seq" if lb.task_flow(task) == lb.SEQ_FLOW else "flow"]
                flow = {"flow": lb.task_flow(task), "yosys": pin["yosys_version"],
                        "canon_script_sha256": pin["canon_script_sha256"], "script_sha256": pin["script_sha256"],
                        "ge_table_sha256": pin["ge_table_sha256"]}
                self.assertEqual(lb.asap7_check(task, table, designs, identity=ident, flow=flow), ([], []))
                mine = [r for r in recs if r["task"] == name]
                sky = lb.build_board(task, mine, flow=flow, identity=lb.ppa_identity(),
                                     input_drive=lb.ppa_setup_now(task).get("input_drive"),
                                     statement=lb.current_statement_or_none(task))
                a7 = lb.build_board(task, mine, flow=flow, statement=lb.current_statement_or_none(task), pdk="asap7",
                                    asap7=table, asap7_identity=ident)
                self.assertEqual({r["record_hash"] for r in a7["ranking"]}, {r["record_hash"] for r in sky["ranking"]})


def git(cwd, *args):
    """git in a test's own repository (no user configuration needed: the identity is given here, an address-free
    one)."""
    return subprocess.run(["git", "-c", "user.name=svgolf test", "-c", "user.email=svgolf-test", "-c",
                           "commit.gpgsign=false", "-c", "init.defaultBranch=main", *args], cwd=cwd,
                          capture_output=True, text=True, check=True).stdout.strip()


class SubmitTest(Tmp):
    """`submit` (decided 2026-11-11): a record of the board's own data directory, checked at the offline level, is
    handed in by a pull request that adds its three files, opened with the player's git and gh. `--dry-run` prints the
    steps and the text and changes nothing; without gh the steps are printed for doing by hand."""

    REPO = "https://github.com/someone/svgolf"

    def setUp(self):
        super().setUp()
        self.env = CliEnv(self)
        p = mock.patch.object(lb, "DEFAULT_DATA", self.env.data)     # the CliEnv's data directory is the board's own
        p.start()
        self.addCleanup(p.stop)

    def record(self, player="alice", extra=()):
        rc, out, err = self.env.add(player, extra=extra)
        self.assertEqual(rc, 0, err)
        rec = next(r for _, r, _ in lb.load_records(self.env.data, "toy") if r["player"] == player)
        return rec

    def submit(self, *argv):
        return self.env.run("submit", "--task", "toy", *argv)

    def test_dry_run_prints_the_steps_and_the_text_and_changes_nothing(self):
        rec = self.record()
        h = rec["record_hash"]
        before = sorted(os.listdir(os.path.join(self.env.data, "toy")))
        with mock.patch.object(lb, "run_submit_steps", side_effect=AssertionError("a dry run ran the steps")), \
                mock.patch.object(lb.shutil, "which", lambda name, which=shutil.which: "/x/gh" if name == "gh"
                                  else which(name)):
            rc, out, err = self.submit("--record", h[:12], "--repo", self.REPO, "--dry-run")
        self.assertEqual(rc, 0, err)
        self.assertEqual(sorted(os.listdir(os.path.join(self.env.data, "toy"))), before)
        self.assertIn(f"[ok] toy/{h[:12]}: alice", out)                    # verify --offline's own line
        self.assertIn(f"board line: `toy` record `{h[:12]}` by `alice`: ", out)
        self.assertIn("submit --dry-run: nothing was changed or sent.", out)
        root = os.path.relpath(lb.SVGOLF)
        for line in ("TMP=$(mktemp -d)",
                     f"git -C {root} fetch --no-tags https://github.com/someone/svgolf.git main",
                     f"BASE=$(git -C {root} rev-parse FETCH_HEAD)",
                     f'GIT_INDEX_FILE="$TMP/index" git -C {root} read-tree "$BASE"',
                     f'TREE=$(GIT_INDEX_FILE="$TMP/index" git -C {root} write-tree)',
                     "gh repo fork someone/svgolf --clone=false --remote=false",
                     "LOGIN=$(gh api user --jq .login)",
                     f'git -C {root} push "https://github.com/$LOGIN/svgolf.git" "$COMMIT:refs/heads/record-toy-{h[:12]}"'):
            self.assertIn(line + "\n", out)
        for ext in (".json", ".sv", ".lean"):
            self.assertIn(f'--cacheinfo "100644,${ {".json": "JSON", ".sv": "SV", ".lean": "LEAN"}[ext]},'
                          f'leaderboard/data/toy/{h}{ext}"', out)
        self.assertIn(f'gh pr create --repo someone/svgolf --base main --head "$LOGIN:record-toy-{h[:12]}" --title '
                      f"'record toy alice {h[:12]}: ", out)
        self.assertIn('--body-file "$TMP/body.md"', out)
        # the pull request's text, as a here-document, with the record's fields
        text = out.split(f"<<'{lb.PR_TEXT_END}'\n", 1)[1].split(f"\n{lb.PR_TEXT_END}\n", 1)[0]
        self.assertEqual([ln[3:] for ln in text.split("\n") if ln.startswith("## ")], list(lb.PR_HEADINGS))
        for want in ("- task: `toy`", "- handle: `alice`", "- assisted by: none (unassisted)",
                     f"- files: `leaderboard/data/toy/{h}.json`, `.sv` and `.lean`", f"[ok] toy/{h[:12]}: alice",
                     lb.PR_CHECK_NOTE, f"`toy` record `{h[:12]}` by `alice`: "):
            self.assertIn(want, text)

    def test_without_gh_the_steps_are_printed_for_doing_by_hand(self):
        rec = self.record("bob", extra=["--assisted-by", "Some Tool [v2]"])
        h = rec["record_hash"]
        with mock.patch.object(lb, "run_submit_steps", side_effect=AssertionError("ran without gh")), \
                mock.patch.object(lb.shutil, "which", lambda name, which=shutil.which: None if name == "gh"
                                  else which(name)):
            rc, out, err = self.submit("--record", h, "--repo", self.REPO + ".git")
        self.assertEqual(rc, 0, err)
        self.assertIn("(gh) is not on PATH, so nothing was changed or sent", out)
        self.assertIn("# fork https://github.com/someone/svgolf on github.com (once), then:\nLOGIN=YOUR_GITHUB_LOGIN\n",
                      out)
        self.assertIn(f"# open https://github.com/someone/svgolf/compare/main...$LOGIN:record-toy-{h[:12]}?expand=1,",
                      out)
        self.assertNotIn("gh pr create", out)
        self.assertNotIn("gh repo fork", out)
        self.assertIn("- assisted by: Some Tool \\[v2\\]", out)        # Markdown-escaped: the player's free text

    def test_what_is_refused(self):
        rec = self.record()
        h = rec["record_hash"]
        rc, _, err = self.submit("--record", h[:8], "--repo", self.REPO)
        self.assertEqual(rc, 1)
        self.assertIn("its first 12 characters or more", err)
        rc, _, err = self.submit("--record", "0" * 12, "--repo", self.REPO)
        self.assertEqual(rc, 1)
        self.assertIn("no record 000000000000 of task toy", err)
        rc, _, err = self.submit("--record", h, "--repo", "https://example.org/someone/svgolf")
        self.assertEqual(rc, 2)
        self.assertIn("is not a GitHub repository", err)
        with mock.patch.object(lb, "site_repo_url", lambda: None):
            rc, _, err = self.submit("--record", h)
        self.assertEqual(rc, 2)
        self.assertIn("no public repository is named here", err)
        with mock.patch.object(lb, "DEFAULT_DATA", os.path.join(self.tmp, "elsewhere")):
            rc, _, err = self.submit("--record", h, "--repo", self.REPO, "--dry-run")
        self.assertEqual(rc, 1)
        self.assertIn("a record made with --data-dir is a private trial", err)
        # a light record never ranks
        light = self.record("lena", extra=["--postsynth", "light"])
        rc, _, err = self.submit("--record", light["record_hash"], "--repo", self.REPO, "--dry-run")
        self.assertEqual(rc, 1)
        self.assertIn("a LIGHT record", err)
        # what verify --offline fails: a stored file that is not the recorded one
        with open(os.path.join(self.env.data, "toy", h + ".sv"), "a") as fh:
            fh.write("// edited\n")
        rc, out, err = self.submit("--record", h, "--repo", self.REPO, "--dry-run")
        self.assertEqual(rc, 1)
        self.assertIn(f"[FAIL] toy/{h[:12]}", out)
        self.assertIn("does not have the recorded sha256", err)
        self.assertNotIn("TMP=", out)

    def test_hostile_arguments_and_the_printed_quoting(self):
        """The review's n-1, n-2, n-3: a word of the printed script stands in double quotes only when its one `$` is an
        earlier step's output, otherwise nothing in it expands; --task is a task's name, never a path; --repo's owner
        and repository are names, never `.` or `..`."""
        self.assertEqual(lb._shell_word("$TMP/index"), '"$TMP/index"')
        self.assertEqual(lb._shell_word("https://github.com/$LOGIN/svgolf.git"), '"https://github.com/$LOGIN/svgolf.git"')
        for w in ("x$(touch PWN)", "record add x$(touch PWN) y", 'a"b$X', "a`b`$X", "$X!"):
            self.assertEqual(lb._shell_word(w), shlex.quote(w), w)
        rec = self.record()
        for task in ("../tasks/toy", "toy/../toy", ".."):
            rc, _, err = self.env.run("submit", "--task", task, "--record", rec["record_hash"], "--repo", self.REPO,
                                      "--dry-run")
            self.assertEqual(rc, 2, task)
            self.assertIn("no such task", err)
        for repo in ("https://github.com/../svgolf", "https://github.com/someone/..", "https://github.com/someone/.",
                     "https://github.com/-x/svgolf"):
            rc, _, err = self.submit("--record", rec["record_hash"], "--repo", repo, "--dry-run")
            self.assertEqual(rc, 2, repo)
            self.assertIn("is not a GitHub repository", err)

    def test_a_record_under_the_reference_handle_is_refused(self):
        """Decided 2026-11-12: the proved references' handle is not a player's; `submit` refuses such a record (one
        made before `add` refused the handle, or by hand) before it verifies anything."""
        rec = make_record(player=lb.REFERENCE_PLAYER)
        lb.store_record(self.env.data, rec, SV_TEXT, LEAN_TEXT)
        rc, out, err = self.submit("--record", rec["record_hash"], "--repo", self.REPO, "--dry-run")
        self.assertEqual(rc, 1)
        self.assertIn(lb.RESERVED_HANDLE, err)
        self.assertNotIn("[ok]", out)
        self.assertNotIn("TMP=", out)

    def test_the_steps_commit_the_three_files_on_main_and_leave_the_players_tree_alone(self):
        """The steps, run for real with git on a repository of this test's own (the public one, a clone of it with
        the record and other work in progress, and a fork; gh's steps left out): the fork's branch is the public
        main plus exactly the three files, and the clone's branch, index and working tree are as they were."""
        up, clone, fork = (os.path.join(self.tmp, n) for n in ("up", "clone", "fork.git"))
        os.makedirs(up)
        git(up, "init", "-q")
        with open(os.path.join(up, "README.md"), "w") as fh:
            fh.write("public\n")
        git(up, "add", "README.md")
        git(up, "commit", "-q", "-m", "public main")
        git(self.tmp, "clone", "-q", up, clone)
        git(self.tmp, "init", "-q", "--bare", fork)
        rec = make_record(task=toy_task())
        lb.store_record(os.path.join(clone, "leaderboard", "data"), rec, SV_TEXT, LEAN_TEXT)
        with open(os.path.join(clone, "README.md"), "a") as fh:
            fh.write("my unfinished edit\n")
        with open(os.path.join(clone, "staged.txt"), "w") as fh:
            fh.write("staged\n")
        git(clone, "add", "staged.txt")
        state = lambda: (git(clone, "rev-parse", "HEAD"), git(clone, "status", "--porcelain"),  # noqa: E731
                         git(clone, "diff", "--cached", "--name-only"), git(clone, "branch", "--list"))
        before = state()
        files = [os.path.relpath(p, clone) for p in lb.record_paths(os.path.join(clone, "leaderboard", "data"),
                                                                     "toy", rec["record_hash"])]
        title, body = lb.submit_text(rec, "a board line", "a verify line")
        steps = [st for st in lb.submit_steps(rec, clone, files, "someone", "svgolf", title) if not st["gh"]]
        swap = {f"{self.REPO}.git": up, "https://github.com/$LOGIN/svgolf.git": fork}
        for st in steps:
            st["argv"] = [swap.get(w, w) for w in st["argv"]]
        ident = {"GIT_AUTHOR_NAME": "p", "GIT_AUTHOR_EMAIL": "player", "GIT_COMMITTER_NAME": "p",
                 "GIT_COMMITTER_EMAIL": "player"}
        with mock.patch.dict(os.environ, ident):
            lb.run_submit_steps(steps, body)
        branch = f"record-toy-{rec['record_hash'][:12]}"
        self.assertEqual(state(), before)
        self.assertEqual(git(fork, "rev-parse", f"{branch}^"), git(up, "rev-parse", "HEAD"))
        self.assertEqual(git(fork, "log", "-1", "--format=%s", branch), title)
        added = git(fork, "diff", "--name-status", f"{branch}^", branch).split("\n")
        self.assertEqual(added, [f"A\tleaderboard/data/toy/{rec['record_hash']}{e}" for e in (".json", ".lean", ".sv")])
        self.assertEqual(git(fork, "show", f"{branch}:README.md"), "public")        # main's, not the clone's edit
        self.assertEqual(git(fork, "show", f"{branch}:leaderboard/data/toy/{rec['record_hash']}.sv") + "\n",
                         SV_TEXT.decode())
        # a step that fails is named, and the temporary directory goes
        made = []
        real = tempfile.mkdtemp

        def mkdtemp(**kw):
            made.append(real(**kw))
            return made[-1]
        with mock.patch.object(lb.tempfile, "mkdtemp", mkdtemp), self.assertRaises(RuntimeError) as e:
            lb.run_submit_steps(steps, body)                    # the branch exists: the push is refused
        self.assertIn("git -C", str(e.exception))
        self.assertIn("push", str(e.exception))
        self.assertFalse(os.path.exists(made[0]))

    def test_the_board_line(self):
        task = toy_task()
        par_rec = make_record(task, lb.REFERENCE_PLAYER, gates={"AND": 5}, sky=(90000, 1000))
        a = make_record(task, "a", gates={"AND": 4}, sky=(80000, 1000))
        b = make_record(task, "b", gates={"AND": 6}, sky=(100000, 1000))
        res = with_ppa(fake_result(gates={"AND": 3}), area_e4=10000, delay_ps=100, ppa_version="sky130_a0_v0")
        old = make_record(task, "old", res=res)
        cur = {"ppa_version": "sky130_a0_v1", "liberty_sha256": "a" * 64, "ppa_pins_sha256": "b" * 64}
        board = lb.build_board(task, [a, b, old], flow=FLOW, identity=cur, input_drive=BUF8)    # the players'
        par = lb.par_of(task, [par_rec, a, b, old], flow=FLOW, identity=cur, input_drive=BUF8,
                        names={par_rec["files"]["sv"]["sha256"]: (0, "toy")})
        h = a["record_hash"]
        self.assertEqual(lb.board_line(board, par, h),
                         f"`toy` record `{h[:12]}` by `a`: 8.0000 um^2 x 1000 ps = 8.00 um2*ns, rank 1 of 2; under par; "
                         f"par `toy`: 9.0000 um^2 x 1000 ps = 9.00 um2*ns (record `{par_rec['record_hash'][:12]}`)")
        self.assertIn("rank 2 of 2; not under par; par ", lb.board_line(board, par, b["record_hash"]))
        self.assertIn("rank 1 of 2; par: none recorded", lb.board_line(board, None, h))
        self.assertEqual(lb.board_line(board, par, old["record_hash"]),
                         f"`toy` record `{old['record_hash'][:12]}` by `old`: not ranked: sky130 columns computed under "
                         "another version (ppa_version differ)")
        self.assertIn("not on the board", lb.board_line(board, par, "f" * 64))
        self.assertIn("are par, not entries", lb.board_line(board, par, par_rec["record_hash"]))

    def test_the_template_has_the_texts_parts(self):
        """.github/pull_request_template.md, the form of a pull request opened by hand, has the parts and fields of the
        text `submit` writes, in the same order."""
        with open(os.path.join(SVGOLF, ".github", "pull_request_template.md"), encoding="utf-8") as fh:
            template = fh.read()
        _, text = lb.submit_text(make_record(task=toy_task()), "a board line", "a verify line")
        parts = lambda t: [ln[3:] for ln in t.split("\n") if ln.startswith("## ")]            # noqa: E731
        fields = lambda t: [ln.split(":", 1)[0] for ln in t.split("\n") if ln.startswith("- ")]  # noqa: E731
        self.assertEqual(parts(template), list(lb.PR_HEADINGS))
        self.assertEqual(parts(text), list(lb.PR_HEADINGS))
        self.assertEqual(fields(template), fields(text))
        self.assertEqual(fields(text), ["- task", "- handle", "- assisted by", "- files"])
        self.assertIn("leaderboard.py submit --task TASK --record HASH", template)
        self.assertIn("a maintainer re-makes the ranked\nnumber on the rating build when the pull request is merged",
                      template)

    def test_the_pinned_flows_are_the_sites(self):
        with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
            expected = json.load(fh)
        flows = lb.pinned_flows()
        self.assertEqual(sorted(flows), [lb.COMB_FLOW, lb.SEQ_FLOW])
        self.assertEqual(flows[lb.COMB_FLOW]["yosys"], expected["flow"]["yosys_version"])
        self.assertEqual(flows[lb.SEQ_FLOW]["script_sha256"], expected["flow_seq"]["script_sha256"])
        ranked = 0
        for name in lb.all_task_names(lb.DEFAULT_TASKS):
            with self.subTest(task=name):
                board, par = lb.board_now(lb.load_task(lb.DEFAULT_TASKS, name), os.path.join(SVGOLF, "leaderboard",
                                                                                               "data"))
                self.assertNotIn(lb.REFERENCE_PLAYER, {r["player"] for r in board["ranking"]})    # par, not an entry
                self.assertEqual(par["player"], lb.REFERENCE_PLAYER)        # every task's par ranks under the pins
                ranked += len(board["ranking"])
        self.assertGreater(ranked, 0)                       # the players' committed records rank, as on the site


def load_pr_check():
    spec = importlib.util.spec_from_file_location("svgolf_pr_check", os.path.join(SVGOLF, "leaderboard", "pr_check.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


pc = load_pr_check()


class PrCheckTest(Tmp):
    """leaderboard/pr_check.py (decided 2026-11-11), on a repository of the test's own with two commits, the base and
    the pull request: it accepts a pull request that only adds records, runs verify --offline on every record and
    verify --full (here through a fake check.py) on the added ones, and writes the board lines and the note on the
    rating build to the summary; it refuses every other change."""

    def setUp(self):
        super().setUp()
        self.repo = os.path.join(self.tmp, "repo")
        os.makedirs(os.path.join(self.repo, "tasks", "toy"))
        with open(os.path.join(self.repo, "tasks", "toy", "task.json"), "w") as fh:
            json.dump(toy_task(), fh)
        self.rdata = os.path.join(self.repo, "leaderboard", "data")
        self.a = make_record(player="alice")
        lb.store_record(self.rdata, self.a, SV_TEXT, LEAN_TEXT)
        git(self.repo, "init", "-q")
        self.commit("the board")
        self.fake = os.path.join(self.tmp, "fake_check.py")
        with open(self.fake, "w") as fh:
            fh.write(FAKE_CHECK.replace("@TEMPLATE@", json.dumps(fake_result()))
                     .replace("@IDENT@", json.dumps(lb.ppa_identity() or {})))
        self.summary = os.path.join(self.tmp, "summary.md")
        with open(self.summary, "w") as fh:
            fh.write("an earlier step's summary\n")
        self.log = os.path.join(self.tmp, "argv.log")
        p = mock.patch.dict(os.environ, {"FAKE_ARGV_LOG": self.log})
        p.start()
        self.addCleanup(p.stop)

    def commit(self, msg):
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", msg)

    def add_record(self, player="bob", sv=None):
        sv = sv or SV_TEXT + f"// {player}\n".encode()
        rec = make_record(player=player, sv=sv)
        lb.store_record(self.rdata, rec, sv, LEAN_TEXT)
        return rec

    def check(self, *argv):
        rc, out, err = quiet(pc.main, ["--repo", self.repo, "--check-py", self.fake, "--sandbox", "off",
                                       "--summary", self.summary, *argv])
        with open(self.summary, encoding="utf-8") as fh:
            return rc, out, err, fh.read()

    def test_a_pull_request_that_adds_a_record(self):
        b = self.add_record()
        self.commit("a record")
        rc, out, err, summary = self.check()
        self.assertEqual(rc, 0, out + err)
        self.assertTrue(summary.startswith("an earlier step's summary\n## The records this pull request adds\n"))
        self.assertIn(out.strip(), summary)
        self.assertIn("Every check passed. It adds 1 record.", summary)
        self.assertIn(f"- `toy` record `{b['record_hash'][:12]}` by `bob`: ", summary)         # its board line
        self.assertNotIn(f"record `{self.a['record_hash'][:12]}`", summary.split("###")[0])     # the base's is not
        self.assertIn("### `leaderboard.py verify --offline`, every record: ok (exit status 0)", summary)
        self.assertIn("verify (offline): 2 records, 0 failed", summary)
        self.assertIn("### `leaderboard.py verify --full --sandbox off`, the records it adds: ok (exit status 0)",
                      summary)
        self.assertIn("verify (full re-check): 1 records, 0 failed", summary)
        self.assertIn(pc.RATING_NOTE, summary)
        self.assertIn("This machine's Yosys", summary)
        with open(self.log) as fh:                          # check.py ran once, on the added record, sandbox as given
            runs = fh.read().splitlines()
        self.assertEqual(len(runs), 1)
        self.assertIn("--sandbox off", runs[0])
        self.assertIn("--postsynth full", runs[0])

    def test_a_failed_check_fails(self):
        b = self.add_record()
        self.commit("a record")
        with mock.patch.dict(os.environ, {"FAKE_MODE": "reject"}):
            rc, out, err, summary = self.check()
        self.assertEqual(rc, 1)
        self.assertIn("**A check failed.** It adds 1 record.", summary)
        self.assertIn("the records it adds: FAILED (exit status 1)", summary)
        self.assertIn(f"[FAIL] toy/{b['record_hash'][:12]}: bob", summary)
        self.assertIn("check.py no longer accepts it", summary)
        self.assertIn("every record: ok (exit status 0)", summary)

    def test_an_added_record_whose_files_were_edited_fails_offline(self):
        b = self.add_record()
        with open(os.path.join(self.rdata, "toy", b["record_hash"] + ".lean"), "ab") as fh:
            fh.write(b"-- edited\n")
        self.commit("an edited record")
        rc, out, err, summary = self.check()
        self.assertEqual(rc, 1)
        self.assertIn("every record: FAILED (exit status 1)", summary)
        self.assertIn("does not have the recorded sha256", summary)

    def test_what_is_not_a_pull_request_of_records(self):
        h = self.a["record_hash"]

        def write(path, text, mode="a"):
            with open(path, mode) as fh:
                fh.write(text)

        def remove():
            for e in (".json", ".sv", ".lean"):
                os.remove(os.path.join(self.rdata, "toy", h + e))
        cases = [
            ("an edit", lambda: write(os.path.join(self.rdata, "toy", h + ".json"), " "),
             f"`leaderboard/data/toy/{h}.json` is changed: a pull request of records adds records and never edits"),
            ("a removal", remove, f"`leaderboard/data/toy/{h}.sv` is deleted"),
            ("another file", lambda: write(os.path.join(self.repo, "check.py"), "print('accepted')\n", "w"),
             "`check.py` is added: it is not a record's file"),
        ]
        for what, change, why in cases:
            with self.subTest(what):
                change()
                self.commit(what)
                rc, out, err, summary = self.check()
                self.assertEqual(rc, 1)
                self.assertIn("### Problems", out)
                self.assertIn(why, out)
                self.assertIn("the records it adds: not run\n\nNot run because of the problems above.", out)
                git(self.repo, "revert", "--no-edit", "HEAD")      # back to the board, as a commit of its own
        # a record without its proof
        b = self.add_record()
        os.remove(os.path.join(self.rdata, "toy", b["record_hash"] + ".lean"))
        self.commit("half a record")
        rc, out, err, summary = self.check()
        self.assertEqual(rc, 1)
        self.assertIn(f"record `toy/{b['record_hash'][:12]}` lacks `{b['record_hash']}.lean`", out)
        self.assertFalse(os.path.exists(self.log))          # check.py never ran

    def test_a_record_under_the_reference_handle_is_refused(self):
        """Decided 2026-11-12 (the review's F3): the proved references' records are par; a pull request cannot add
        one, and the full check does not run."""
        r = self.add_record(player=lb.REFERENCE_PLAYER)
        self.commit("a record under the reference handle")
        rc, out, err, summary = self.check()
        self.assertEqual(rc, 1)
        self.assertIn(f"record `toy/{r['record_hash'][:12]}` is under the handle `{lb.REFERENCE_PLAYER}`, the proved "
                      "references' own", summary)
        self.assertIn("the records it adds: not run", summary)
        self.assertFalse(os.path.exists(self.log))

    def test_a_record_file_must_be_a_plain_file(self):
        """The review's F4 / m-2: a record's file added as a symbolic link (its content would be another path's) or as
        an executable is refused, and the full check does not run."""
        for what, change, word in (
                ("a link", lambda d, h: (os.remove(os.path.join(d, h + ".sv")),
                                         os.symlink(self.a["record_hash"] + ".sv", os.path.join(d, h + ".sv"))),
                 "is added as a symbolic link"),
                ("executables", lambda d, h: [os.chmod(os.path.join(d, h + e), 0o755) for e in (".json", ".sv", ".lean")],
                 "is added as an executable file")):
            with self.subTest(what):
                b = self.add_record(player="bob", sv=SV_TEXT + f"// {what}\n".encode())
                change(os.path.join(self.rdata, "toy"), b["record_hash"])
                self.commit(what)
                rc, out, err, summary = self.check()
                self.assertEqual(rc, 1)
                self.assertIn(word, out)
                self.assertIn("a record's file is a plain file (mode 100644)", out)
                self.assertIn("the records it adds: not run", out)
                self.assertFalse(os.path.exists(self.log))
                git(self.repo, "revert", "--no-edit", "HEAD")

    def test_an_offline_failure_fails_the_check_by_itself(self):
        """The review's F5: a record already on the board that fails `verify --offline`, while the added one passes
        the full check, fails the pull request's check."""
        with open(os.path.join(self.rdata, "toy", self.a["record_hash"] + ".sv"), "ab") as fh:
            fh.write(b"// edited on the base\n")
        self.commit("the base with a broken record")
        self.add_record()
        self.commit("a record")
        rc, out, err, summary = self.check()
        self.assertEqual(rc, 1)
        self.assertIn("**A check failed.** It adds 1 record.", summary)
        self.assertIn("every record: FAILED (exit status 1)", summary)
        self.assertIn("the records it adds: ok (exit status 0)", summary)

    def test_a_record_of_a_task_this_repository_lacks(self):
        """The review's F12: named by the task's name, not by a path of the machine."""
        rec = make_record(task=toy_task(name="nosuch"), player="bob",
                          res=fake_result(task="nosuch", sv_sha=lb.sha256_bytes(SV_TEXT)))
        lb.store_record(self.rdata, rec, SV_TEXT, LEAN_TEXT)
        self.commit("a record of no task")
        rc, out, err, summary = self.check()
        self.assertEqual(rc, 1)
        self.assertIn(f"record `nosuch/{rec['record_hash'][:12]}`: `nosuch` is not a task of this repository (it has "
                      "no `tasks/nosuch/task.json`)", summary)
        self.assertNotIn(self.repo, summary.split("### `leaderboard.py verify")[0])

    def test_refs_that_look_like_options_are_refused(self):
        """The review's m-3: `--base` and `--head` are resolved to commits, and one that begins with `-` is refused, so
        that no argument reaches git as an option (`git diff --output=FILE` would write a file)."""
        self.add_record()
        self.commit("a record")
        out_file = os.path.join(self.tmp, "written-by-git")
        for flag in ("--base", "--head"):
            with self.subTest(flag):
                rc, _, err = quiet(pc.main, ["--repo", self.repo, f"{flag}=--output={out_file}"])
                self.assertEqual(rc, 2)
                self.assertIn("begins with `-`", err)
                self.assertFalse(os.path.exists(out_file))
        head = git(self.repo, "rev-parse", "HEAD")
        self.assertEqual(pc.resolve(self.repo, "HEAD", "--head"), head)
        self.assertEqual(pc.resolve(self.repo, head[:12], "--head"), head)

    def test_usage_and_git_errors(self):
        self.add_record()
        self.commit("a record")
        rc, _, err = quiet(pc.main, ["--repo", self.repo, "--head", "HEAD^1"])
        self.assertEqual(rc, 2)
        self.assertIn("is not the commit checked out", err)
        rc, _, err = quiet(pc.main, ["--repo", self.repo, "--base", "no-such-ref"])
        self.assertEqual(rc, 2)
        self.assertIn("error: git rev-parse --verify --end-of-options no-such-ref^{commit}", err)   # resolved first

    def test_classify_and_the_flow_note(self):
        h, g = "1" * 64, "2" * 64
        f = "100644"
        added, problems = pc.classify([("A", f"leaderboard/data/add/{h}.json", f), ("A", f"leaderboard/data/add/{h}.sv", f),
                                       ("A", f"leaderboard/data/add/{h}.lean", f), ("A", f"leaderboard/data/mul/{g}.sv", f),
                                       ("A", "leaderboard/data/add/notes.txt", f), ("T", f"leaderboard/data/add/{g}.sv", f),
                                       ("A", f"leaderboard/data/mul/{g}.lean", "120000")])
        self.assertEqual(added, {("add", h): {"json", "sv", "lean"}, ("mul", g): {"sv"}})
        self.assertEqual(problems, [
            "`leaderboard/data/add/notes.txt` is added: it is not a record's file, and a pull request of records "
            "changes nothing else (it would bring the checker it runs)",
            f"`leaderboard/data/add/{g}.sv` is changed in type: a pull request of records adds records and never "
            "edits or removes one",
            f"`leaderboard/data/mul/{g}.lean` is added as a symbolic link: a record's file is a plain file (mode "
            "100644)",
            f"record `mul/{g[:12]}` lacks `{g}.json`, `{g}.lean`: a record is its three files"])
        pin = {lb.COMB_FLOW: {"yosys": "Yosys 0.53 (rating)"}}
        self.assertEqual(pc.flow_note(pin, pin), "This machine's Yosys is the rating build's (Yosys 0.53 (rating)), so "
                         "the full check compared the scores too.")
        self.assertIn("This machine's Yosys (none found) is not the rating build's (Yosys 0.53 (rating)), so the full "
                      "check compared no score", pc.flow_note({lb.COMB_FLOW: {"yosys": None}}, pin))


class CommittedDataTest(unittest.TestCase):
    def test_committed_records_are_intact(self):
        """Every record under leaderboard/data/ verifies at the offline level
        (hashes, stored files, arithmetic). Passes vacuously while it is empty."""
        for path, rec, err in lb.load_records(lb.DEFAULT_DATA):
            self.assertIsNone(err, path)
            task = lb.load_task(lb.DEFAULT_TASKS, rec["task"])
            r = lb.verify_record(path, rec, task)
            self.assertEqual(r.fails, [], path)


if __name__ == "__main__":
    unittest.main()
