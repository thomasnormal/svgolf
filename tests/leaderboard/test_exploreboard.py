#!/usr/bin/env python3.12
"""Tests of the exploration boards (leaderboard/exploreboard.py): what `add` takes and refuses, `problems`, the order,
and that an exploration task is no task of the leaderboard (no records, no par, no board).

    python3.12 tests/leaderboard/test_exploreboard.py
"""
import copy
import importlib.util
import json
import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.dont_write_bytecode = True


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(SVGOLF, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


xb = load("svgolf_exploreboard_test", "leaderboard/exploreboard.py")
lb = load("svgolf_leaderboard_xb_test", "leaderboard/leaderboard.py")


class Board(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp(prefix="svgolf-xb-test-")
        self.boards = os.path.join(self.root, "boards")
        for name, text in (("a.sv", "module gemm; endmodule\n"), ("a.json", '{"cycles": "n", "layout": null}\n')):
            with open(os.path.join(self.root, name), "w") as fh:
                fh.write(text)
        self.result = {
            "task": "gemm", "exploration": True, "unproved_ok": True, "stage": "unproved", "accepted": False,
            "score": {"label": "composed", "version": "composed_asap7_v1", "area_um2": 4000000.5,
                      "area_e5um2": 400000050000, "period_ps": 2100, "cycles": 4600000, "cycles_measured": 4600000,
                      "time_ps": 9660000000,
                      "params": {"LGE": 7, "LAT": 32}, "job": {"lgn": 12, "batch": 4096}, "module_period_ps": 2100,
                      "slowest_module": "gemm_row", "flat_period_ps": 2000, "flat_period_at": {"LGE": 2, "LAT": 3},
                      "sram_area_um2": 700000.0, "sram_bits": 1, "flops": 2, "cells": 3, "ranked": []},
            "stages": {"source": {"sha256": xb.sha256_file(os.path.join(self.root, "a.sv"))},
                       "declare": {"sha256": xb.sha256_file(os.path.join(self.root, "a.json")), "cycles": "n",
                                   "layout": "canonical"},
                       "hier": {"rule": "holds", "flow": {"yosys_version": "Y", "rating_build": True},
                                "ppa_version": "asap7_a0_v1", "hier_script_sha256": "h"},
                       "explore": {"points": [{"params": {"LGE": 2, "LAT": 3}, "netlist": {"seeds": []}},
                                              {"params": {"LGE": 3, "LAT": 2}, "netlist": {"skipped": "x"}}]}}}

    def tearDown(self):
        shutil.rmtree(self.root, ignore_errors=True)

    def entry(self, name="a", result=None, par=False):
        return xb.entry_from_result("gemm", name, "a.sv", "a.json", result or self.result, "A design", "note", par,
                                    root=self.root)

    def test_an_entry_is_a_clean_exploration_run_of_exactly_these_files(self):
        e = self.entry(par=True)
        self.assertEqual((e["name"], e["par"], e["proved"], e["score"]["label"]), ("a", True, False, "composed"))
        self.assertEqual(e["checked"]["points"], [{"LGE": 2, "LAT": 3}, {"LGE": 3, "LAT": 2}])
        self.assertEqual(e["checked"]["netlist_points"], [{"LGE": 2, "LAT": 3}])
        self.assertEqual(xb.score_value(e), 400000050000 * 4600000 * 2100)
        self.assertAlmostEqual(xb.mm2ms(e), 4.0000005 * 4600000 * 2100e-9, places=6)

    def test_what_add_refuses(self):
        def bad(change):
            r = copy.deepcopy(self.result)
            change(r)
            with self.assertRaises(xb.BoardError) as cm:
                self.entry(result=r)
            return str(cm.exception)
        self.assertIn("not a clean exploration run", bad(lambda r: r.update(stage="explore", unproved_ok=False)))
        self.assertIn("not a clean exploration run", bad(lambda r: r.pop("exploration")))
        self.assertIn("no composed score", bad(lambda r: r.pop("score")))
        self.assertIn("is of task", bad(lambda r: r.update(task="matmul")))
        self.assertIn("not the design the result was made on", bad(lambda r: r["stages"]["source"].update(sha256="0")))
        self.assertIn("not the declaration", bad(lambda r: r["stages"]["declare"].update(sha256="0")))
        # the cycle count is the one measured by running the scored job: a result without it, or with another, is no entry
        self.assertIn("not a measured count of the scored job", bad(lambda r: r["score"].pop("cycles_measured")))
        self.assertIn("not a measured count of the scored job", bad(lambda r: r["score"].update(cycles_measured=1)))

    def test_the_board_its_order_and_its_problems(self):
        xb.add("gemm", self.entry("a", par=True), self.boards)
        fast = copy.deepcopy(self.result)
        fast["score"].update(cycles=4000000, cycles_measured=4000000)
        xb.add("gemm", self.entry("b", fast), self.boards)
        board = xb.load("gemm", self.boards)
        self.assertEqual([e["name"] for e in xb.ordered(board)], ["b", "a"])
        self.assertEqual(xb.par_entry(board)["name"], "a")
        self.assertEqual(xb.problems("gemm", self.boards, self.root), [])
        with self.assertRaises(xb.BoardError):                       # a second par
            xb.add("gemm", self.entry("c", par=True), self.boards)
        xb.add("gemm", self.entry("b", self.result), self.boards)    # the same name: replaced
        self.assertEqual(len(xb.load("gemm", self.boards)["entries"]), 2)
        with open(os.path.join(self.root, "a.sv"), "a") as fh:
            fh.write("// changed\n")
        self.assertTrue(all("is not the file the entry was checked on" in p
                            for p in xb.problems("gemm", self.boards, self.root)))
        board["entries"][0]["proved"] = True
        with open(xb.board_path("gemm", self.boards), "w") as fh:
            json.dump(board, fh)
        self.assertTrue(any("must be unproved" in p for p in xb.problems("gemm", self.boards, self.root)))
        board["entries"][1]["score"].pop("cycles_measured")
        with open(xb.board_path("gemm", self.boards), "w") as fh:
            json.dump(board, fh)
        self.assertTrue(any("not the measured count of the scored job" in p
                            for p in xb.problems("gemm", self.boards, self.root)))

    def test_a_players_entry_names_its_player_and_has_a_writeup(self):
        xb.add("gemm", self.entry("a", par=True), self.boards)
        self.assertNotIn("player", self.entry("a"))                   # the maintainers' entries: no player field
        e = xb.entry_from_result("gemm", "p", "a.sv", "a.json", self.result, "A design", "short", root=self.root,
                                 player="some-handle", assisted_by=["a tool"])
        self.assertEqual((e["player"], e["assisted_by"], e["par"]), ("some-handle", ["a tool"], False))
        with self.assertRaises(xb.BoardError):                       # assisted-by without a player
            xb.entry_from_result("gemm", "p", "a.sv", "a.json", self.result, "t", "n", root=self.root,
                                 assisted_by=["a tool"])
        with self.assertRaises(xb.BoardError):                       # a player's entry is never par
            xb.entry_from_result("gemm", "p", "a.sv", "a.json", self.result, "t", "n", True, root=self.root,
                                 player="some-handle")
        xb.add("gemm", e, self.boards)
        self.assertTrue(any("needs its writeup" in p for p in xb.problems("gemm", self.boards, self.root)))
        path = xb.writeup_path("gemm", "p", self.boards)
        os.makedirs(os.path.dirname(path))
        with open(path, "w") as fh:
            fh.write("<h1>A short title</h1>\n\n<p>What it is.</p>\n")
        self.assertEqual(xb.problems("gemm", self.boards, self.root), [])
        with open(path, "w") as fh:
            fh.write("A first line that is no title\n<p>x</p>\n")
        self.assertTrue(any("title line" in p for p in xb.problems("gemm", self.boards, self.root)))
        with open(path, "w") as fh:
            fh.write("<h1>A short title</h1>\n")
        e["note"] = "x" * (xb.NOTES_MAX + 1)                          # the records' rule: the story in the writeup
        xb.add("gemm", e, self.boards)
        self.assertTrue(any("over the cap of 300" in p for p in xb.problems("gemm", self.boards, self.root)))
        e["note"] = "short"
        xb.add("gemm", e, self.boards)
        with open(xb.writeup_path("gemm", "a", self.boards), "w") as fh:     # par is the maintainers': no writeup
            fh.write("<h1>A short title</h1>\n")
        self.assertEqual([p for p in xb.problems("gemm", self.boards, self.root)],
                         ["gemm: writeups/gemm/a.html is the writeup of no player's entry"])

    def test_an_empty_board(self):
        self.assertEqual(xb.load("gemm", self.boards)["entries"], [])
        self.assertEqual(xb.problems("gemm", self.boards, self.root), [])


class Repository(unittest.TestCase):
    def test_an_exploration_task_is_no_task_of_the_leaderboard(self):
        names = xb.task_names()
        self.assertIn("gemm", names)
        for t in names:
            self.assertNotIn(t, lb.all_task_names(lb.DEFAULT_TASKS))
            self.assertTrue(lb.is_explore_task(lb.DEFAULT_TASKS, t))
            self.assertFalse(os.path.isdir(os.path.join(SVGOLF, "leaderboard", "data", t)))
        self.assertFalse(lb.is_explore_task(lb.DEFAULT_TASKS, "matmul"))
        self.assertIn("matmul", lb.all_task_names(lb.DEFAULT_TASKS))

    def test_the_boards_in_the_repository_are_sound(self):
        for t in xb.task_names():
            with self.subTest(task=t):
                self.assertEqual(xb.problems(t), [])
                board = xb.load(t)
                with open(os.path.join(SVGOLF, "tasks", t, "task.json")) as fh:
                    task = json.load(fh)
                listed = {(e["sv"], e["declare"]) for e in task.get("entries", [])}
                for e in board["entries"]:
                    self.assertIn((os.path.relpath(e["sv"], f"tasks/{t}"), os.path.relpath(e["declare"], f"tasks/{t}")),
                                  listed)
                    self.assertEqual(e["score"]["params"], task["scoring"]["params"])
                    self.assertEqual(e["score"]["job"], task["scoring"]["job"])
                    self.assertEqual(e["checked"]["hier_rule"], "holds")
                    self.assertTrue(e["checked"]["flow"]["rating_build"])
                    self.assertTrue(e["checked"]["netlist_points"])
                    self.assertEqual(e["score"]["cycles_measured"], e["score"]["cycles"])
                    # a player's entry is marked so in task.json too (gen.py leaves its files alone)
                    mine = next(x for x in task["entries"] if f"tasks/{t}/{x['sv']}" == e["sv"])
                    self.assertEqual(mine.get("player"), e.get("player"))
                    if "player" in e:
                        self.assertTrue(os.path.isfile(xb.writeup_path(t, e["name"])))


if __name__ == "__main__":
    unittest.main()
