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
  * never-loaded registers (txtask-v2, decided 2026-11-06): tests/seq_counter/never_loaded/*.sv (first line
    `// expect: <stage>[: <message>]`) are refused at their stage, an array lane no write loads among them (the
    review's section 12), the harmless flop removals accepted; the state registers the fsm pass re-implemented
    before the clocked flow ran `synth -nofsm` (decided 2026-11-06) pass the rule and, since the clocked flow's
    `opt_clean -purge` (decided 2026-11-07) removed the dead techmap wire the netlist lint stopped on (the review's
    section 12.2), every stage but the proof; the log check stays as a backstop (`test_the_fsm_backstop`);
  * the sorter reference (stream-family, at N=3, W=4 of a copy of the task) passes at its latency 2N,
    back to back; its mutants (`STREAM_NEGATIVES`: an output one cycle early, a wrong order, a dropped
    duplicate, out_valid depending on the power-up, out_valid 1 before the first start) and the reference at a
    declared latency 2N - 1 fail at `postsynth`, each with its own message;
  * the arbiter's goalpost (react-family, at N = 3 of a copy of the task, short segments and a 3000-entry
    reset-free run) passes the reactive check from power-up states (seed 0 all zeros); its mutants
    (`REACT_NEGATIVES`: a Mealy output, a grant flop without reset, fixed priority, a time bomb after 1000
    cycles, a self-holding register behind the grant) each fail at their stage on their own clause: the
    Moore sample, G0 (the reset snapshot shows the power-up or the last grant), G4, G4 in the long segment
    (`postsynth`), and the never-loaded register (`score`, txtask-v2, decided 2026-11-06); the goalpost with
    its mask not reset passes the full reactive check (bit for bit only from the same start, the guarantee on
    each run elsewhere: txtask-v2 review section 12, F4); the rotating-priority arbiter (tests/arbiter/designs/
    rotate.sv) passes it at N = 3, 5, 8 (the clocked flow's `opt_clean -purge`, decided 2026-11-07, removed the
    dead techmap wire the netlist lint refused at N = 8); and the salt changes the stimulus, the empty salt
    reproduces it.

    python3.12 tests/checker/test_clocked_post.py
"""
import json
import os
import re
import shutil
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from test_clocked import ARBITER_SV, COUNTER, CNT_SV, MATMUL_SV, SVGOLF, FakeLean, checkpy  # noqa: E402

SEQ_TX = os.path.join(SVGOLF, "tests", "seq_tx")
NEVER_LOADED = os.path.join(COUNTER, "never_loaded")
SORTER_SV = os.path.join(SVGOLF, "tasks", "sorter", "reference", "sorter_ins.sv")
ROTATE_SV = os.path.join(SVGOLF, "tests", "arbiter", "designs", "rotate.sv")
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
    ("out_valid depends on the power-up (the cells' tokens are not reset): from different power-ups of the "
     "netlist and of ls-sv (txtask-v2 revision 2), the two disagree", "        tok[k] <= 1'b0;\n", "",
     "out_valid: the netlist ("),       # either way round: the draws are the salt's (F5), the two disagree
    ("out_valid 1 before the first start (the tokens reset to 1)", "        tok[k] <= 1'b0;\n",
     "        tok[k] <= 1'b1;\n", "out_valid is 1 at cycle 1, before the first start"),
]


# (what, old, new: the arbiter goalpost's text; the stage and the message it fails with)
REACT_NEGATIVES = [
    ("a Mealy output (the next grant, unregistered: gnt = pick, the flop kept as gq)",
     "      gnt <= '0;\n      mask <= '1;\n    end else begin\n      gnt <= pick;\n",
     "      gq <= '0;\n      mask <= '1;\n    end else begin\n      gq <= pick;\n",
     "postsynth", "a combinational path from an input to an output"),
    ("a grant flop without reset", "      gnt <= '0;\n", "", "postsynth", "G0: the reset snapshot shows gnt"),
    ("fixed priority (the mask never moves)", "      if (pick != '0) mask <= ~((pick << 1) - 1'b1);\n", "",
     "postsynth", "G4: client"),
    ("a time bomb (fixed priority after 1000 cycles)",
     "      if (pick != '0) mask <= ~((pick << 1) - 1'b1);\n",
     "      if (pick != '0 && age < 1000) mask <= ~((pick << 1) - 1'b1);\n      if (age < 1000) age <= age + 1'b1;\n",
     "postsynth", "(long (3000 entries)), entry"),
    ("a self-holding register behind the grant (u <= u; if (!u) fixed priority: attack A16)",
     "      gnt <= pick;\n", "      if (!u) gnt <= req & (~req + 1'b1);\n      else gnt <= pick;\n",
     "score", "never-loaded register"),
]


def arbiter_small():
    """A temporary copy of tasks/arbiter (task.json, oracle.py) scored and checked at N=3, 8 segments, the last
    3000 entries long."""
    d = tempfile.mkdtemp(prefix="svgolf-reactsmall-")
    shutil.copy(os.path.join(SVGOLF, "tasks", "arbiter", "oracle.py"), d)
    with open(os.path.join(SVGOLF, "tasks", "arbiter", "task.json")) as fh:
        t = json.load(fh)
    t.update(name="react_arbiter_small", probe_points=["N=1", "N=3"], scoring={"params": {"N": 3}},
             postsynth={"seeds": 2, "segments": 8, "long": 3000})
    with open(os.path.join(d, "task.json"), "w") as fh:
        json.dump(t, fh)
    return d


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
        cls.small, cls.sorter, cls.arbiter = matmul_small(), sorter_small(), arbiter_small()

    @classmethod
    def tearDownClass(cls):
        for d in (cls.small, cls.sorter, cls.arbiter):
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
        self.assertEqual((pt["mismatches"], len(pt["seeds"])), (0, 8))         # S = 8 per point (F5, 2026-11-07)
        self.assertTrue(all(x["cycles"] > 300 and not x["late"] for x in pt["seeds"]))
        for key in ("score", "ppa"):
            self.assertEqual(json.dumps(a[key], sort_keys=True), json.dumps(b[key], sort_keys=True))
        # F5: every seed records what it drew from the (here empty) salt: the stimulus source, Verilator's randSeed,
        # ls-sv's power-up (seed 0 from all zeros on both sides)
        import postsynth
        task = json.load(open(os.path.join(COUNTER, "task.json")))
        for x in pt["seeds"]:
            d = postsynth.seed_draw(task, pt["point"], x["seed"], salt="")
            self.assertEqual((x["seed_sha256"], x["salted"], x["netlist_randseed"], x["netlist_randreset"],
                              x["lssv_start"]),
                             (d["seed_sha256"], False, d["vl_seed"], 0 if x["seed"] == 0 else 2,
                              "zeros" if x["seed"] == 0 else f"seed:{d['lssv_k']}"))

    def test_a_secret_salt_moves_every_draw_and_the_counter_still_passes(self):
        """F5 (2026-11-07): with $SVGOLF_POSTSYNTH_SALT set, every seed's stimulus source, Verilator randSeed and
        ls-sv power-up differ from the empty salt's, the record says `salted`, and a correct design still passes."""
        import postsynth
        with mock.patch.dict(os.environ, {"SVGOLF_POSTSYNTH_SALT": "a competition's secret"}):
            res = self.check(COUNTER, CNT_SV)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        (pt,) = res["stages"]["postsynth"]["points"]
        self.assertEqual((pt["mismatches"], len(pt["seeds"])), (0, 8))
        task = json.load(open(os.path.join(COUNTER, "task.json")))
        for x in pt["seeds"]:
            d = postsynth.seed_draw(task, pt["point"], x["seed"], salt="")
            self.assertTrue(x["salted"])
            self.assertNotEqual(x["seed_sha256"], d["seed_sha256"])
            self.assertNotEqual(x["netlist_randseed"], d["vl_seed"])
            if x["seed"]:
                self.assertNotEqual(x["lssv_start"], f"seed:{d['lssv_k']}")

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


    def test_never_loaded_registers(self):
        """txtask-v2 (decided 2026-11-06): a never-loaded register is refused in every clocked task, at `score`
        (the flow's own log: a flop removed while it is read) or at `fourstate` (a register bit no write reaches is
        an undriven bit); so is an array lane no write loads (opt_mem's const-x lane, the review's section 12); a flop
        removal that keeps one value per register (a constant, a merge, a shared bit, an unread flop, a constant
        array lane) is accepted, and a state register the fsm pass re-implemented before the clocked flow ran
        `synth -nofsm` (decided 2026-11-06) passes the rule. The source-level twin (`clocked_rules`, every write is the register's own value)
        only warns. The fixtures' first line is `// expect: <stage>[: <message>]`, an optional second
        `// warn: <message>` (the warning it must give; without one, it gives none)."""
        for f in sorted(os.listdir(NEVER_LOADED)):
            sv = os.path.join(NEVER_LOADED, f)
            with open(sv) as fh:
                stage, _, want = fh.readline().split("// expect:")[1].strip().partition(": ")
                second = fh.readline()
            warn = second.split("// warn:")[1].strip() if second.startswith("// warn:") else None
            with self.subTest(f):
                res = self.check(COUNTER, sv)
                self.assertEqual(res["stage"], stage, res["errors"])
                if want:
                    self.assertIn(want, res["errors"][0])
                warnings = [w for w in res.get("warnings", []) if w.startswith("clocked_rules: ")]
                if warn:
                    self.assertTrue(any(warn in w for w in warnings), warnings)
                else:
                    self.assertEqual(warnings, [])

    def test_the_fsm_backstop(self):
        """The clocked flow runs `synth -nofsm` (decided 2026-11-06), so no scored log maps an FSM (the reset
        controller `fsm_reset_controller.sv` passes `score` above); should a "Mapping FSM" line ever appear,
        `never_loaded` still refuses at `score` (a synthetic log record here)."""
        sv = os.path.join(NEVER_LOADED, "fsm_reset_controller.sv")
        sres = {"flop_removals": {"fsm_mapped": ["Mapping FSM `$fsm$\\_0_$31' from module `\\cnt'."]}}
        with self.assertRaises(checkpy.Reject) as cm:
            checkpy.never_loaded(sres, sv, "cnt", {"N": 8})
        self.assertEqual(cm.exception.stage, "score")
        self.assertIn("state register re-implemented as a state machine at N=8", cm.exception.msg)
        self.assertIn("backstop", cm.exception.msg)

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

    def test_the_arbiter_goalpost_passes_the_reactive_check(self):
        res = self.check(self.arbiter, ARBITER_SV)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        s = res["score"]
        self.assertEqual((s["cycles"], s["time_ps"], s["ranked"]), (1, s["period_ps"], ["area_um2", "time_ps"]))
        (pt,) = res["stages"]["postsynth"]["points"]
        self.assertEqual((pt["kind"], pt["mismatches"], len(pt["seeds"])), ("react-family", 0, 2))
        for seed in pt["seeds"]:
            self.assertEqual((seed["segments"], seed["longest_segment"], seed["salted"]), (8, 3000, False))
            self.assertGreater(seed["cycles"], 3008)
        self.assertNotEqual(pt["seeds"][0]["seed_sha256"], pt["seeds"][1]["seed_sha256"])

    def test_an_unreset_mask_passes_the_reactive_check(self):
        """The goalpost with the mask NOT reset is correct from every power-up (the mask is the thermometer after
        the first grant; G0 to G4 hold whatever it powered up as) but its grants depend on the mask's power-up,
        which seeds 1 and 2 draw differently for the netlist and for ls-sv: the full reactive check of tasks/arbiter
        (three points, three seeds) compares the two bit for bit only from the same state, and the guarantee on each
        run elsewhere (txtask-v2 review section 12, F4: rejected before, at seed 2, N = 3, cycle 1)."""
        with open(ARBITER_SV) as fh:
            ref = fh.read()
        old = "    if (rst) begin\n      gnt <= '0;\n      mask <= '1;\n    end else begin\n"
        self.assertEqual(ref.count(old), 1)
        work = tempfile.mkdtemp(prefix="svgolf-reactmask-")
        self.addCleanup(shutil.rmtree, work, ignore_errors=True)
        sv = os.path.join(work, "nomask.sv")
        with open(sv, "w") as fh:
            fh.write(ref.replace(old, "    if (rst) gnt <= '0;\n    else begin\n"))
        res = self.check(os.path.join(SVGOLF, "tasks", "arbiter"), sv)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        pts = res["stages"]["postsynth"]["points"]
        self.assertEqual([(p["point"], p["mismatches"], len(p["seeds"])) for p in pts],
                         [("N=3", 0, 8), ("N=5", 0, 8), ("N=8", 0, 8)])
        for p in pts:
            self.assertEqual([s["compared"].split(" (")[0] for s in p["seeds"]],
                             ["the netlist with ls-sv, bit for bit"] + ["each run with the guarantee"] * 7)

    def test_rotating_priority_passes_at_every_point(self):
        """tests/arbiter/designs/rotate.sv, a correct arbiter of another fair policy (rotating priority), through the
        full reactive check of tasks/arbiter (N = 3, 5, 8). Its scored netlist at N = 8 kept a dead public-named
        techmap wire with an undriven bit (`\\_269_.B`) before the clocked flow's last clean-up became `opt_clean
        -purge` (decided 2026-11-07), and the post-synthesis lint refused it there (tasks/arbiter/README.md, F6); now
        it passes at every point, with the gates plain `opt_clean` gave (310.294 GE, depth 13 at N = 8)."""
        res = self.check(os.path.join(SVGOLF, "tasks", "arbiter"), ROTATE_SV)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        pts = res["stages"]["postsynth"]["points"]
        self.assertEqual([(p["point"], p["mismatches"]) for p in pts], [("N=3", 0), ("N=5", 0), ("N=8", 0)])
        self.assertEqual((res["score"]["area_mge"], res["score"]["depth"]), (310294, 13))

    def test_the_salt_moves_the_reactive_stimulus(self):
        import postsynth
        task = {"name": "arbiter"}
        a, ha = postsynth.react_rng(task, "N=3", 0, salt="")
        b, hb = postsynth.react_rng(task, "N=3", 0, salt="")
        c, hc = postsynth.react_rng(task, "N=3", 0, salt="secret")
        self.assertEqual((ha, a.getrandbits(64)), (hb, b.getrandbits(64)))
        self.assertNotEqual(ha, hc)

    def test_the_salt_moves_every_draw_of_every_clocked_kind(self):
        """F5 (2026-11-07): `seed_draw` gives one seed's stimulus source, Verilator randSeed and ls-sv power-up, all
        from sha256(salt, task, point, seed): the empty salt reproduces them, another salt moves each; seed 0 starts
        both sides from all zeros. The transaction kinds' plan (oracle.py `txns` driven by the seed's source) moves
        with the salt too, and the reactive kind's segments."""
        import postsynth
        for name in ("cnt", "matmul", "sorter", "arbiter"):
            task = {"name": name}
            a, b = postsynth.seed_draw(task, "N=3", 1, salt=""), postsynth.seed_draw(task, "N=3", 1, salt="")
            c = postsynth.seed_draw(task, "N=3", 1, salt="secret")
            self.assertEqual((a["seed_sha256"], a["vl_seed"], a["lssv_k"], a["rng"].getrandbits(64)),
                             (b["seed_sha256"], b["vl_seed"], b["lssv_k"], b["rng"].getrandbits(64)))
            self.assertNotEqual((a["seed_sha256"], a["vl_seed"], a["lssv_k"]),
                                (c["seed_sha256"], c["vl_seed"], c["lssv_k"]))
            self.assertTrue(1 <= a["vl_seed"] < 2 ** 31 and 0 <= a["lssv_k"] < 2 ** 64)
            self.assertEqual(postsynth.start_of(0, a), (0, "zeros"))
            self.assertEqual(postsynth.start_of(1, a), (2, f"seed:{a['lssv_k']}"))
        for tdir, kind, pt, dins in ((self.small, "tx", {"N": 2, "W": 4, "AccW": 8},
                                      [("A", 16), ("B", 16), ("rst", 1), ("start", 1)]),
                                     (self.sorter, "stream", {"N": 3, "W": 4},
                                      [("in_data", 4), ("in_valid", 1), ("rst", 1), ("start", 1)]),
                                     (self.arbiter, "react", {"N": 3}, [("req", 3), ("rst", 1)])):
            task = json.load(open(os.path.join(tdir, "task.json")))
            mod = postsynth.clocked_oracle(postsynth.load_oracle(tdir, task), task["kind"])
            cfg = postsynth.config(task)

            def plan(salt):
                d = postsynth.seed_draw(task, postsynth.envelope.point_str(pt), 1, salt=salt)
                if kind == "react":
                    return postsynth.react_plan(task, mod, pt, d["rng"], cfg, dins)[0]
                return postsynth.clocked_plan(task, mod, pt, 1, cfg, dins, d["rng"])[0]
            with self.subTest(kind):
                self.assertEqual(plan(""), plan(""))
                self.assertNotEqual(plan(""), plan("secret"))

    def test_each_reactive_negative_fails_on_its_clause(self):
        with open(ARBITER_SV) as fh:
            ref = fh.read()
        work = tempfile.mkdtemp(prefix="svgolf-reactneg-")
        self.addCleanup(shutil.rmtree, work, ignore_errors=True)
        for k, (what, old, new, stage, want) in enumerate(REACT_NEGATIVES):
            with self.subTest(what):
                self.assertEqual(ref.count(old), 1, what)
                text = ref.replace(old, new)
                if "gq <=" in new:
                    text = text.replace("  logic [N-1:0] mask, mreq, pick;\n",
                                        "  logic [N-1:0] mask, mreq, pick, gq;\n  assign gnt = pick;\n")
                if "age" in new:
                    text = text.replace("  logic [N-1:0] mask, mreq, pick;\n",
                                        "  logic [N-1:0] mask, mreq, pick;\n  logic [10:0] age;\n")
                    text = text.replace("      mask <= '1;\n", "      mask <= '1;\n      age <= '0;\n")
                if "!u" in new:
                    text = text.replace("  logic [N-1:0] mask, mreq, pick;\n",
                                        "  logic [N-1:0] mask, mreq, pick;\n  logic u;\n  always_ff @(posedge clk) u <= u;\n")
                sv = os.path.join(work, f"neg{k}.sv")
                with open(sv, "w") as fh:
                    fh.write(text)
                res = self.check(self.arbiter, sv)
                self.assertEqual(res["stage"], stage, res["errors"])
                points = (res["stages"].get("postsynth") or {}).get("points") or [{}]
                report = points[-1].get("report") or []
                self.assertIn(want, res["errors"][0] + json.dumps(report))


if __name__ == "__main__":
    unittest.main(verbosity=1)
