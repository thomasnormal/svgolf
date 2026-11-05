#!/usr/bin/env python3
"""Tests for leaderboard/leaderboard.py. No Lean, no Yosys run, no network: the
check results are synthetic (same shape as check.py's JSON) and the `add` path
that runs check.py is exercised against a FAKE check.py script.

    python3 tests/leaderboard/test_leaderboard.py          # run
    UPDATE_GOLDEN=1 python3 tests/leaderboard/test_leaderboard.py   # rewrite the golden file

Covers: record round trip, record_hash canonicality and a pinned hash, tamper
detection (record, stored .sv and .lean), refusal of rejected submissions, the
ranked board (decided 11/03: the sky130 A0' area and time rank, GE and depth are
extra columns; a record without sky130 columns, or of another PPA identity or
input drive, is not ranked; a clocked record's time is cycles x period), the
Pareto frontier (dominance, ties, determinism, agreement with score.py's),
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
import io
import json
import os
import random
import shutil
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
import score  # noqa: E402  (only for the cross-check of the Pareto filter)

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
            "solution": {"exit": 0, "seconds": 8.41},
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
    if mode is not None:
        ps = res["stages"]["postsynth"]
        ps.update(mode=mode, full_vectors=500)
        if mode == "light":
            ps["vectors"] = 120
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
        by = {r["player"]: r["postsynth"] for r in board["frontier"] + board["dominated"]}
        self.assertEqual(by, {"fulla": "full", "lighta": "light"})
        md = lb.render_markdown(board)
        self.assertIn(f"`{light['record_hash'][:12]}` light |", md)
        self.assertNotIn(f"`{full['record_hash'][:12]}` light", md)
        self.assertIn(lb.LIGHT_NOTE, md)
        self.assertIn("[light post-synthesis check]", lb.render_pareto_text(board))
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
    """The default board: ranked on the sky130 A0' area and time. `recs` gives each record a sky130 score in the order of
    its GE score (area = ANDs x 1 um^2, time = depth x 100 ps), so the expected orders read in either;
    test_the_board_ranks_sky130_not_ge pulls the two apart."""
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
        self.assertEqual([(r["player"], r["rank"], r["over_budget"]) for r in br],
                         [("a", 1, False), ("d", 1, False), ("e", 3, False), ("c", 4, False),
                          ("f", 5, False), ("b", None, True)])
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
        (un,) = board["unranked"]
        self.assertEqual(un["player"], "old")
        self.assertIn("no sky130 columns (a record made before them): not ranked until it is backfilled", un["reason"])
        # --all-flows ranks every flow, but never a record without the columns
        self.assertEqual([r["player"] for r in lb.build_board(task, [ge, sky, old], flow=None)["unranked"]], ["old"])
        md = lb.render_markdown(board)
        self.assertIn("| # | layer | player | assisted by | area (um^2) | time (ps) | area (GE) | depth |", md)
        self.assertIn("| 1 | 1 | sky | none | 8.0000 | 800 | 11.997 | 9 |", md)
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
        `ppa` block's `delay_ps_sky130`), never the period alone; validate_record holds the three together."""
        task = toy_task()
        res = with_ppa(fake_result(gates={"AND": 5}), area_e4=90000, delay_ps=1000)
        res["score"].update(area_um2=9.0, period_ps=1000, cycles=4, time_ps=4000)
        slow = make_record(task, "clk4", res=res)                  # 4 cycles x 1000 ps
        fast = make_record(task, "comb", gates={"AND": 5}, sky=(90000, 3000))
        self.assertEqual(lb.validate_record(slow), [])
        self.assertEqual(lb.ranked_columns(slow), {"area_e4um2": 90000, "time_ps": 4000, "cycles": 4, "period_ps": 1000})
        board = lb.build_board(task, [slow, fast], flow=FLOW)
        self.assertEqual([r["player"] for r in board["frontier"]], ["comb"])
        self.assertEqual([r["player"] for r in board["dominated"]], ["clk4"])
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
        rc, out, _ = env.run("pareto", "--task", "toy", "--format", "json")
        self.assertEqual([r["player"] for r in json.loads(out)["frontier"]], ["bob", "alice"])
        rc, out, _ = env.run("pareto", "--task", "toy", "--unassisted")
        self.assertEqual(rc, 0)
        self.assertIn("1 of 2 ranked records", out)

        rc, md, _ = env.run("board", "--task", "toy")
        self.assertEqual(rc, 0)
        self.assertIn("Depth budget: depth <= 22", md)
        self.assertIn("Best area under the depth budget", md)
        self.assertIn("over budget", md)         # bob: depth 25 > 22
        rc, js, _ = env.run("board", "--task", "toy", "--format", "json")
        board = json.loads(js)
        self.assertEqual(board["depth_budget"], 22)
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

        def drifting(svgolf=lb.SVGOLF):
            calls.append(1)
            return {"svgolf_revision": "r", "lean_toolchain": "t",
                    "files": {"check.py": str(len(calls)) * 64}}
        with mock.patch.object(lb, "collect_environment", drifting):
            rc, out, err = env.add("alice")
        self.assertEqual(rc, 1)
        self.assertIn("checker files changed while the check ran (check.py)", err)
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
        self.assertEqual(json.loads(js)["frontier"][0]["postsynth"], "light")

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
        put_task(self.task8)
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
        put_task(self.task1)                            # the task chooses buf_1: the buf_8 record is the stale one
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
