#!/usr/bin/env python3.12
"""Tests of the exploration task `gemm` (no Lean): the oracle, the generator, the SRAM models, the declaration's
grammar, and the simulation check (check/explore.py) on the reference design and on wrong ones.

    python3.12 tests/gemm/test_gemm.py

The simulation tests need Verilator 5 and a C++ compiler and are SKIPPED without them. Each wrong design is the
reference `par` with one edit, and must be refused by the check that is there for it:
  a dropped weight sign and a wrong rounding      refused by the results
  a schedule that depends on the activations      refused by the data-independence check (its results are right)
  a schedule that waits on all-zero weight beats  refused by the data-independence check: its second data set is of
                                                  another kind (two identity matrices would agree)
  an output stage wrong at one shift              refused by the results of the sweep (a job per shift)
  a request one beat too long                     refused by the protocol check
  a cycle formula off by one                      refused by the cycle check
  a cycle formula wrong only at the scored job    refused by the run of the scored job
"""
import copy
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
TASK_DIR = os.path.join(SVGOLF, "tasks", "gemm")
sys.dont_write_bytecode = True
sys.path[:0] = [os.path.join(SVGOLF, "check"), os.path.join(SVGOLF, "score")]
import explore  # noqa: E402

with open(os.path.join(TASK_DIR, "task.json")) as _fh:
    TASK = json.load(_fh)
ORACLE = explore.load_oracle(TASK_DIR, TASK)
HAVE_SIM = shutil.which("verilator") is not None and shutil.which("make") is not None
needs_sim = unittest.skipUnless(HAVE_SIM, "needs Verilator 5, make and a C++ compiler")


def load_gen():
    spec = importlib.util.spec_from_file_location("gemm_gen", os.path.join(TASK_DIR, "reference", "gen.py"))
    mod = importlib.util.module_from_spec(spec)
    sys.path.insert(0, os.path.join(TASK_DIR, "reference"))
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.path.pop(0)
    return mod


def read(rel):
    with open(os.path.join(SVGOLF, rel)) as fh:
        return fh.read()


def small_task(points=1, seeds=2):
    """The task with a short check: the first `points` points, `seeds` seeds, two cycle shapes."""
    t = copy.deepcopy(TASK)
    t["explore"]["points"] = [dict(p, seeds=seeds, netlist=False) for p in t["explore"]["points"][:points]]
    t["explore"]["cycle_shapes"] = [[0, 3], [1, 9]]
    return t


class Oracle(unittest.TestCase):
    def test_the_oracles_self_test(self):
        r = subprocess.run([sys.executable, os.path.join(TASK_DIR, "oracle.py")], capture_output=True, text=True)
        self.assertEqual((r.returncode, r.stdout.strip()), (0, "oracle self-test: ok"), r.stderr)

    def test_the_output_stage_against_exact_fractions(self):
        """`scale` is min(max(round_half_up(sum * M / 2^s) + zp, lo), hi), computed here with fractions."""
        from fractions import Fraction
        import math
        import random
        rng = random.Random(7)
        for _ in range(2000):
            acc = rng.randrange(-(1 << 43), 1 << 43) >> rng.randrange(0, 44)
            job = {"mul": rng.randrange(1 << 16), "shift": rng.randrange(64), "zp": rng.randrange(1 << 16)}
            lo = rng.randrange(1 << 16)
            job.update(lo=lo, hi=rng.randrange(lo, 1 << 16))
            exact = Fraction(acc * job["mul"], 1 << job["shift"])
            r = math.floor(exact + Fraction(1, 2)) if job["shift"] else acc * job["mul"]
            self.assertEqual(ORACLE.scale(acc, job), min(max(r + job["zp"], job["lo"]), job["hi"]))

    def test_the_sums_never_leave_44_bits_at_the_scored_size(self):
        """What the 48-bit accumulators and the reference's output stage rely on: N <= 4096 products below 2^31."""
        self.assertLess(4096 * 32768 * 65535, 1 << 43)
        self.assertEqual(max(p["params"]["LGE"] for p in TASK["explore"]["points"] + [{"params": TASK["scoring"]["params"]}]),
                         TASK["scoring"]["params"]["LGE"])
        self.assertEqual(TASK["scoring"]["params"]["LGE"] + ORACLE.MAX_SCALE, TASK["scoring"]["job"]["lgn"])

    def test_the_canonical_image_is_block_major_one_block_row_per_beat(self):
        n, lge = 8, 1
        W = [[r * 100 + c for c in range(n)] for r in range(n)]
        img = ORACLE.image(W, 3, lge)
        self.assertEqual(len(img), n * n // 2)
        for R in range(4):
            for C in range(4):
                for i in range(2):
                    beat = img[(R * 4 + C) * 2 + i]
                    self.assertEqual([beat & 0xFFFF, beat >> 16], W[R * 2 + i][C * 2:C * 2 + 2])

    def test_a_layout_of_block_sums_stores_exact_values_at_their_width(self):
        import random
        rng = random.Random(3)
        n, lge = 8, 1
        W = [[rng.randrange(-32768, 32768) for _ in range(n)] for _ in range(n)]
        lay = {"default": [{"level": 1, "terms": [[0, 0, 1], [1, 1, 1]], "bits": 17, "tile": 1}]}
        self.assertIsNone(ORACLE.check_layout(lay))
        img = ORACLE.image(W, 3, lge, lay)
        t, e = 4, 2
        self.assertEqual(len(img), t * t // e + (t * t + 16 * e - 1) // (16 * e))      # low plane, then one upper bit each
        up = img[t * t // e]
        for i in range(t):
            for j in range(t):
                v = W[i][j] + W[4 + i][4 + j]
                low = (img[i * 2 + j // 2] >> (16 * (j % 2))) & 0xFFFF
                bit = (up >> (i * t + j)) & 1
                self.assertEqual(((low | bit << 16) ^ 0x10000) - 0x10000, v)

    def test_the_sweep_shows_every_shift_and_the_second_data_set_is_of_another_kind(self):
        pt = {"LGE": 2, "LAT": 3}
        sw = ORACLE.jobs(pt, 0, "sweep")
        self.assertEqual([j["shift"] for j in sw], list(range(64)))
        for j in sw[:55]:                       # above, every legal sum of these sizes rounds to 0
            ys = {v for vec in ORACLE.reference(j) for v in vec}
            self.assertTrue(any(j["lo"] < v < j["hi"] and v != j["zp"] for v in ys), j["tag"])
        import random
        a = ORACLE.jobs(pt, 3, rng=random.Random(1), data_rng=random.Random(2))
        b = ORACLE.jobs(pt, 3, rng=random.Random(1), data_rng=random.Random(3), data_shift=1)
        self.assertEqual([[j[f] for f in ORACLE.JOB_FIELDS] for j in a], [[j[f] for f in ORACLE.JOB_FIELDS] for j in b])
        ident = lambda j: all(j["W"][i][k] == (i == k) for i in range(len(j["W"])) for k in range(len(j["W"])))  # noqa: E731
        self.assertTrue(any(ident(j) for j in a))
        self.assertFalse(any(ident(x) and ident(y) for x, y in zip(a, b)))
        self.assertIn("sweep", TASK["explore"]["shapes"])
        scored = [p for p in TASK["explore"]["points"] if p.get("scored_job")]
        self.assertEqual([p["params"] for p in scored], [TASK["scoring"]["params"]])

    def test_the_environment_drives_garbage_on_idle_lines(self):
        tb = read("tasks/gemm/env/tb.sv")
        for line in ("if (!e_rdv) e_rdd = garbage(lfsr);", "if (!e_xv) e_xd = garbage(", "if (!e_jv) begin"):
            self.assertIn(line, tb)

    def test_a_malformed_layout_is_refused(self):
        for bad in ({}, {"x": []}, {"0": [{"level": 1, "terms": [[0, 0, 1]]}]},
                    {"default": [{"level": 0, "terms": [[0, 0, 0]]}]}, {"default": [{"level": 0, "terms": [[1, 0, 1]]}]},
                    {"default": [{"level": 0, "terms": [[0, 0, 1]], "bits": 15}]},
                    {"default": [{"level": 0, "terms": [[0, 0, 1]], "extra": 1}]}):
            with self.subTest(bad=bad):
                self.assertIsNotNone(ORACLE.check_layout(bad))


class Declaration(unittest.TestCase):
    def test_the_formula_grammar(self):
        f = explore._formula_fn("(batch//(2*e))*max(n, lat+1) + min(batch%(2*e), 1) + ceil_div(n, e) - -1")
        self.assertEqual(f(16, 9, 4, 3), 1 * 16 + 1 + 4 + 1)
        for bad in ("__import__('os')", "n ** 2", "n / 2", "x + 1", "max(n)", "n if e else 1", "ceil_div(n, 0)",
                    "[n][0]", "n.real", "lambda: 1", "min(n, e, key=abs)", "1.5 * n", "True"):
            with self.subTest(bad=bad), self.assertRaises((ValueError, SyntaxError)):
                explore._formula_fn(bad)(8, 8, 8, 8)

    def test_the_declaration_file(self):
        with tempfile.TemporaryDirectory() as d:
            def decl(obj):
                p = os.path.join(d, "x.json")
                with open(p, "w") as fh:
                    json.dump(obj, fh)
                return explore.load_declare(p, ORACLE)
            self.assertEqual(decl({"cycles": "n", "layout": None}), ({"cycles": "n", "layout": None}, None))
            self.assertIn("cycle formula", decl({"cycles": "n**2"})[1])
            self.assertIn("layout", decl({"cycles": "n", "layout": {"9": []}})[1])
            # twice the matrix does not fit 16 bits for every weight matrix: refused here, not when an image is made
            self.assertIn("does not fit its 16 signed bits",
                          decl({"cycles": "n", "layout": {"default": [{"level": 0, "terms": [[0, 0, 2]], "bits": 16}]}})[1])
            self.assertIn("keys", decl({"cycles": "n", "speed": 1})[1])
        self.assertEqual(explore.load_declare(None, ORACLE), ({"cycles": None, "layout": None}, None))

    def test_a_port_width_may_use_a_power_of_two(self):
        self.assertEqual(explore.width_at("16*2**LGE", {"LGE": 7}), 2048)
        self.assertEqual(explore.width_at("(N+1)*2", {"N": 3}), 8)
        for bad in ("3**LGE", "LGE/2", "len(LGE)"):
            with self.subTest(bad=bad), self.assertRaises(explore.InfraError):
                explore.width_at(bad, {"LGE": 2})


class Files(unittest.TestCase):
    def test_the_reference_files_are_the_generators(self):
        r = subprocess.run([sys.executable, os.path.join(TASK_DIR, "reference", "gen.py"), "--check"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_the_sram_models_are_the_catalogues(self):
        self.assertEqual(read("tasks/gemm/env/sram_asap7.sv"), explore.sram_models("sim"))
        table = explore.sram_table()
        self.assertEqual(len(table["blocks"]), 36)
        self.assertEqual({(b["words"], b["addr_bits"]) for b in table["blocks"]}, {(256, 8), (512, 9), (1024, 10)})
        for b in table["blocks"]:
            self.assertEqual(1 << b["addr_bits"], b["words"])
            self.assertIn(f"module {b['name']} (", explore.sram_models("blackbox"))
        self.assertIn("The OpenROAD Project", read("score/sram_asap7.LICENSE"))

    def test_every_entry_of_the_task_is_a_design_and_its_declaration(self):
        for e in TASK["entries"]:
            with self.subTest(entry=e["sv"]):
                self.assertTrue(os.path.isfile(os.path.join(TASK_DIR, e["sv"])))
                declare, why = explore.load_declare(os.path.join(TASK_DIR, e["declare"]), ORACLE)
                self.assertIsNone(why)
                self.assertIsNotNone(declare["cycles"])
                job, sp = TASK["scoring"]["job"], TASK["scoring"]["params"]
                # no design is faster than its streams: the activation beats in, then the result beats out
                self.assertGreater(explore.cycles_at(declare, sp, job["lgn"], job["batch"]),
                                   2 * (job["batch"] << (job["lgn"] - sp["LGE"])))

    def test_the_readme_shows_the_task_jsons_ports(self):
        readme = read("tasks/gemm/README.md")
        for p in TASK["ports"]["inputs"] + TASK["ports"]["outputs"]:
            self.assertIn(p["name"], readme)
        self.assertIn("exploration, unproved entries", readme)


@needs_sim
class Simulation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.mkdtemp(prefix="svgolf-gemm-test-")
        cls.par = read("tasks/gemm/reference/par.sv")
        cls.declare, why = explore.load_declare(os.path.join(TASK_DIR, "reference", "par.json"), ORACLE)
        assert why is None, why

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.work, ignore_errors=True)

    def check(self, name, text, declare=None, task=None):
        d = os.path.join(self.work, name)
        os.makedirs(d)
        sv = os.path.join(d, "design.sv")
        with open(sv, "w") as fh:
            fh.write(text)
        return explore.run(TASK_DIR, task or small_task(), sv, declare or self.declare, d)

    def edit(self, old, new):
        self.assertEqual(self.par.count(old), 1, old)
        return self.par.replace(old, new)

    def refused(self, name, text, declare=None):
        with self.assertRaises(explore.Reject) as cm:
            self.check(name, text, declare)
        return cm.exception.msg

    def test_par_passes_at_two_points(self):
        rec = self.check("par", self.par, task=small_task(points=2, seeds=3))
        self.assertEqual([p["params"] for p in rec["points"]], [{"LGE": 2, "LAT": 3}, {"LGE": 2, "LAT": 1}])
        for p in rec["points"]:
            self.assertTrue(p["results"]["independence"])
            self.assertEqual(len(p["results"]["seeds"]), 3)
            for row in p["cycles"]:
                self.assertEqual(row["declared"], row["measured"][-1])
            self.assertIn("skipped", p.get("netlist", {"skipped": 1}))

    def test_a_dropped_weight_sign_is_refused_by_the_results(self):
        msg = self.refused("sign", self.edit("$signed(w_act) * $signed({1'b0, x_in})",
                                             "$signed({1'b0, w_act[14:0]}) * $signed({1'b0, x_in})"))
        self.assertIn("the reference is", msg)

    def test_rounding_down_is_refused_by_the_results(self):
        msg = self.refused("round", self.edit("($signed({q20[19], q20}) + 21'sd1) >>> 1", "($signed({q20[19], q20})) >>> 1"))
        self.assertIn("the reference is", msg)

    def test_a_schedule_that_reads_the_data_is_refused_by_the_independence_check(self):
        text = self.edit("        M_INGEST: begin\n          if (x_take) begin\n",
                         "        M_INGEST: begin\n          if (~x_ready) x_ready <= 1'b1;\n          if (x_take) begin\n"
                         "            if (x_data[0] & (ic != nbm)) x_ready <= 1'b0;\n")
        msg = self.refused("datadep", text)
        self.assertIn("the schedule depends on the data", msg)

    def test_a_schedule_keyed_on_zero_weight_beats_is_refused_by_the_independence_check(self):
        """One more cycle before a pass when the tile's last beat is all zero. Two identity matrices agree on those
        beats; the second data set is of another kind, so the two runs part."""
        text = self.edit("assign start_pass = (ms == M_TILE) & sh_full & ~xb_rd;",
                         "assign start_pass = (ms == M_TILE) & sh_full & ~xb_rd & (zdel | (wbeat != '0));")
        self.assertEqual(text.count("  logic        x_take, y_take, start_pass, ro_go, rd_take;"), 1)
        text = text.replace("  logic        x_take, y_take, start_pass, ro_go, rd_take;",
                            "  logic        x_take, y_take, start_pass, ro_go, rd_take, zdel;")
        self.assertEqual(text.count("    if (rd_take) wbeat <= rd_data;\n"), 1)
        text = text.replace("    if (rd_take) wbeat <= rd_data;\n", "    if (rd_take) wbeat <= rd_data;\n"
                            "    zdel <= (ms == M_TILE) & sh_full & ~xb_rd & ~start_pass;\n")
        msg = self.refused("zeroskip", text)
        self.assertIn("the schedule depends on the data", msg)

    def test_an_output_stage_wrong_at_one_shift_is_refused_by_the_sweep(self):
        text = self.edit("assign q = $signed({p, 1'b0}) >>> shift;",
                         "assign q = $signed({p, 1'b0}) >>> ((shift == 6'd17) ? 6'd16 : shift);")
        t = small_task(seeds=1)
        t["explore"]["shapes"] = ["sweep"]
        with self.assertRaises(explore.Reject) as cm:
            self.check("shift17", text, task=t)
        self.assertIn("-s17", cm.exception.msg)
        self.assertIn("the reference is", cm.exception.msg)

    def scored_task(self):
        """The short task with its first point marked `scored_job`, the job a small one (N = 32, 9 vectors)."""
        t = small_task(seeds=1)
        t["explore"]["points"][0]["scored_job"] = {"lgn": 5, "batch": 9}
        return t

    def test_the_scored_jobs_run_measures_the_declared_cycles(self):
        rec = self.check("scored", self.par, task=self.scored_task())
        row = rec["points"][0]["scored_job"]
        self.assertEqual((row["lgn"], row["batch"], row["weights"]), (5, 9, "identity"))
        self.assertEqual(row["measured"], [row["declared"]])
        self.assertEqual(row["declared"], explore.cycles_at(self.declare, {"LGE": 2, "LAT": 3}, 5, 9))
        d = os.path.join(self.work, "noscored")
        os.makedirs(d)
        sv = os.path.join(d, "design.sv")
        with open(sv, "w") as fh:
            fh.write(self.par)
        rec = explore.run(TASK_DIR, self.scored_task(), sv, self.declare, d, scored_job=False)
        self.assertIn("skipped", rec["points"][0]["scored_job"])

    def test_a_formula_wrong_only_at_the_scored_job_is_refused_by_its_run(self):
        """Right at every simulated cycle point (n = 4 and 8), 7 cycles short at the job the score is about."""
        wrong = dict(self.declare, cycles="(" + self.declare["cycles"] + ")-7*(n//32)")
        with self.assertRaises(explore.Reject) as cm:
            self.check("scoredformula", self.par, wrong, task=self.scored_task())
        self.assertIn("at the scored job", cm.exception.msg)
        self.assertIn("the simulation of that job measures", cm.exception.msg)

    def test_a_request_past_the_image_is_refused(self):
        msg = self.refused("request", self.edit("rq_len   <= 24'(E);", "rq_len   <= 24'(E + 1);"))
        self.assertTrue("leaves" in msg or "timeout" in msg, msg)

    def test_a_cycle_formula_off_by_one_is_refused_by_the_cycle_check(self):
        msg = self.refused("cycles", self.par, dict(self.declare, cycles=self.declare["cycles"] + "+1"))
        self.assertIn("the declared cycle formula gives", msg)

    def test_without_a_formula_the_check_reports_the_measured_cycles(self):
        rec = self.check("nocycles", self.par, {"cycles": None, "layout": None})
        self.assertTrue(all("declared" not in row and row["measured"] for row in rec["points"][0]["cycles"]))


if __name__ == "__main__":
    unittest.main()
