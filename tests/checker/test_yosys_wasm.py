"""The rating build is the same program on every machine (decided 2026-11-24, score/yosys_wasm.py and
score/reference_build.json): the canonical RTLIL and the scored netlist of five designs are pinned BYTE FOR BYTE (the
sha256 of the whole files, Yosys's banner included), with the GE columns and, where the pinned sky130 liberty is
present, the ranked A0' area and time. Two of the designs are ones on which the native builds of the same Yosys
version disagree (2026-11-24: fdivp's par, 1515 gates, is the smallest such design; the matmul record of quillwren
the smallest such matmul): a host whose C or C++ library leaked into the result would fail here. CI runs this file on
Linux and on macOS (the unit workflow's `rating-build` job). Also: the launcher refuses another module and other
runtime versions (exit status 3, never a fallback to a native Yosys), its self-check prints the pins, and parallel
first runs on a cold cache wait for one compile.

Skipped where the rating build is not installed (`pip install -r requirements.txt`), unless
SVGOLF_REQUIRE_RATING_BUILD=1 (CI), which makes that a failure.

    python3.12 tests/checker/test_yosys_wasm.py
"""

import concurrent.futures
import glob
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import score  # noqa: E402
import yosys_wasm  # noqa: E402

REQUIRE = os.environ.get("SVGOLF_REQUIRE_RATING_BUILD") == "1"
MISSING = score.yosys_missing(score.WASM_YOSYS)

# (task, design: a path under svgolf/ or a design file's sha256 among the records' designs, the pins)
DESIGNS = (
    ("_example", "tasks/_example/reference/band.sv", {
        "sv_sha256": "69299388b006f49d94180cdf29fad24c02995b1f727e5ce458910e60c09816ff",
        "rtlil_sha256": "3c7377615a986766d4d3a2e0409f01aef3300c677aedbc6b8ae1371f725770f1",
        "netlist_sha256": "9329d45a617656d96df7652cbc0466e511002f9808f612d720e0aa043e71346d",
        "area_mge": 21328, "depth": 1, "area_e4um2": 1000960, "delay_ps": 280}),
    ("add", "tasks/add/reference/add_n.sv", {
        "sv_sha256": "6579283e86a83926c68dbaa616514d26e83f7ede393aad333cafb7af3cc47ec5",
        "rtlil_sha256": "8123089e7a0b392865867c65e7e8a251ddeec8dadb199aa1abf2e7cfee1bd73a",
        "netlist_sha256": "93f94b5aa80608d8398de72d3cc97ba6a73892a65e43db29068e4ec8a79b9c5a",
        "area_mge": 112000, "depth": 33, "area_e4um2": 4604416, "delay_ps": 2611}),
    ("arbiter", "tasks/arbiter/reference/rr_mask.sv", {
        "sv_sha256": "f8b02272b7f264d935673b0fa5522fbfb877bdf2985b5c1ad27b861b3a5de784",
        "rtlil_sha256": "7d36a15b93a631f5837799f9c6c5bc3eeedf346693c1b1771a9f129e190aa4d7",
        "netlist_sha256": "d115d9630df1c98ed7080d042688b63718e4aeb62bdf46391c0f33013d565cb8",
        "area_mge": 188979, "depth": 17, "area_e4um2": 7694880, "delay_ps": 2826}),
    # the native builds disagree here (macOS 367515.32 um2*ns, Linux 363424.26): this is the board's number now
    ("fdivp", "tasks/fdivp/reference/fdivp.sv", {
        "sv_sha256": "6accce8480176a433638ac74ce597a3310aef2a72d2439f90f2abb7a16b72310",
        "rtlil_sha256": "d0f467fc10fbf7a6338c10de083560d9d5d86027689b8cbe592928eb59707b4a",
        "netlist_sha256": "eb8764d47f80b77c32763c9eb4eb960a27ba4061998cf5ee2ebf3e9a88fd8c08",
        "area_mge": 2163080, "depth": 292, "area_e4um2": 96442496, "delay_ps": 37683}),
    # and here (quillwren's record: macOS 4836434.72 um2*ns, Linux 5015079.41 under the native builds)
    ("matmul", "308cf75fcf3041cee37886277a811731ba37dc04e7fabf345e57f152f257067d", {
        "sv_sha256": "308cf75fcf3041cee37886277a811731ba37dc04e7fabf345e57f152f257067d",
        "rtlil_sha256": "db4ca8146657a1d979d26ffb3b7d994e92d8e6b8b74ef945177b6c84f7507299",
        "netlist_sha256": "b9a7bc3bd4cf9681869571d63407cd64e7f0bdf381ffab9994a627f7ec5ad755",
        "area_mge": 11241034, "depth": 41, "area_e4um2": 466297216, "delay_ps": 5186}),
)


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def design_path(task, ref):
    """The design file: a path under svgolf/, or the record design of the task with this sha256."""
    if "/" in ref:
        return os.path.join(SVGOLF, ref)
    for p in sorted(glob.glob(os.path.join(SVGOLF, "leaderboard", "data", task, "*.sv"))):
        if sha256_file(p) == ref:
            return p
    raise AssertionError(f"no record design of {task} with sha256 {ref}")


def liberty():
    """(library, pins) of the pinned sky130 liberty, or None where it is not here (`ppa.py --fetch-liberty`)."""
    import ppa
    try:
        return ppa.open_library()
    except ppa.PpaError:
        return None


@unittest.skipIf(MISSING and not REQUIRE, f"the rating build is not installed: {MISSING}")
class RatingBuild(unittest.TestCase):
    def setUp(self):
        self.assertIsNone(MISSING, "SVGOLF_REQUIRE_RATING_BUILD=1, and the rating build cannot run")

    def test_the_netlists_are_pinned_byte_for_byte(self):
        lib = liberty()
        import ppa
        for task_name, ref, pin in DESIGNS:
            with self.subTest(task=task_name):
                sv = design_path(task_name, ref)
                self.assertEqual(sha256_file(sv), pin["sv_sha256"])
                with open(os.path.join(SVGOLF, "tasks", task_name, "task.json"), encoding="utf-8") as fh:
                    task = json.load(fh)
                clocked = task.get("kind") in ("seq-family", "tx-family", "stream-family", "react-family")
                top, params = score.task_scoring_point(task)
                with tempfile.TemporaryDirectory(prefix="svgolf-wasm-pin-") as d:
                    nl, il = os.path.join(d, "netlist.v"), os.path.join(d, "canon.il")
                    res = score.score([sv], top, params, netlist_out=nl, rtlil_out=il,
                                      flow="seq" if clocked else "comb")
                    self.assertTrue(res["rating_build"])
                    self.assertEqual(res["yosys_version"], yosys_wasm.PIN["version_line"])
                    self.assertEqual(sha256_file(il), pin["rtlil_sha256"], "canonical RTLIL")
                    self.assertEqual(res["rtlil_sha256"], pin["rtlil_sha256"])
                    self.assertEqual(sha256_file(nl), pin["netlist_sha256"], "scored netlist")
                    self.assertEqual((res["area_mge"], res["depth"]), (pin["area_mge"], pin["depth"]))
                    if lib is not None:
                        lb, pins = lib
                        with open(nl, encoding="utf-8") as fh:
                            text = fh.read()
                        an = ppa.analyze(text, lb, pins, input_drive=ppa.input_drive_of(task, pins))
                        cols = ppa.columns(an, pins, lb, pin["netlist_sha256"])
                        self.assertEqual((cols["area_e4um2_sky130"], cols["delay_ps_sky130"]),
                                         (pin["area_e4um2"], pin["delay_ps"]))

    def test_the_self_check_prints_the_pins(self):
        p = subprocess.run([sys.executable, os.path.join(SVGOLF, "score", "yosys_wasm.py"), "--self-check"],
                           capture_output=True, text=True, timeout=600)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertIn(yosys_wasm.PIN["wasm_sha256"], p.stdout)
        self.assertIn(yosys_wasm.PIN["version_line"], p.stdout)

    def test_another_module_is_refused(self):
        with tempfile.TemporaryDirectory(prefix="svgolf-wasm-tamper-") as d:
            fake = os.path.join(d, "yosys.wasm")
            with open(yosys_wasm.wasm_path(), "rb") as fh:
                data = bytearray(fh.read())
            data[len(data) // 2] ^= 1
            with open(fake, "wb") as fh:
                fh.write(bytes(data))
            saved, checked = yosys_wasm.wasm_path, dict(yosys_wasm._CHECKED)
            yosys_wasm._CHECKED.clear()
            yosys_wasm.wasm_path = lambda: fake
            try:
                with self.assertRaises(yosys_wasm.PinError) as cm:
                    yosys_wasm.check_pin()
                self.assertIn("sha256", str(cm.exception))
                self.assertEqual(yosys_wasm.main(["-V"]), yosys_wasm.EXIT_PIN)
            finally:
                yosys_wasm.wasm_path = saved
                yosys_wasm._CHECKED.clear()
                yosys_wasm._CHECKED.update(checked)

    def test_another_runtime_is_refused(self):
        saved, checked = dict(yosys_wasm.PIN["packages"]), dict(yosys_wasm._CHECKED)
        yosys_wasm._CHECKED.clear()
        yosys_wasm.PIN["packages"]["wasmtime"] = "0.0.1"
        try:
            with self.assertRaises(yosys_wasm.PinError) as cm:
                yosys_wasm.check_pin()
            self.assertIn("wasmtime", str(cm.exception))
        finally:
            yosys_wasm.PIN["packages"].clear()
            yosys_wasm.PIN["packages"].update(saved)
            yosys_wasm._CHECKED.clear()
            yosys_wasm._CHECKED.update(checked)

    def test_parallel_first_runs_wait_for_one_compile(self):
        """Six cold-cache runs at once raced on the cache file and died with SIGBUS before the lock (measured
        2026-11-24); with it, three at once all print the version line."""
        with tempfile.TemporaryDirectory(prefix="svgolf-wasm-cache-") as cache:
            env = dict(os.environ, YOWASP_CACHE_DIR=cache)
            cmd = [sys.executable, "-B", os.path.join(SVGOLF, "score", "yosys_wasm.py"), "-V"]
            with concurrent.futures.ThreadPoolExecutor(3) as pool:
                runs = list(pool.map(lambda _: subprocess.run(cmd, capture_output=True, text=True, env=env,
                                                              timeout=900), range(3)))
            for p in runs:
                self.assertEqual(p.returncode, 0, p.stderr[-500:])
                self.assertEqual(p.stdout.strip(), yosys_wasm.PIN["version_line"])


if __name__ == "__main__":
    unittest.main()
