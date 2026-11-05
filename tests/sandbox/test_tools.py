#!/usr/bin/env python3.12
"""WP-S: the tools under the sandbox, on designs the source gate would refuse (so the sandbox is what
stops them here). Needs Yosys, Verilator, make and a C++ compiler, and an active sandbox mechanism; each
half skips with a message when its pieces are missing.

    python3.12 tests/sandbox/test_tools.py

  * Yosys `read_verilog` of `$readmemh("/some/host/file")` loads the file into the netlist (unsandboxed: the
    file's bits are in the RTLIL; measured 2026-10-31). Sandboxed: "Can not open file".
  * Verilator compiles `initial $system("echo pwned > marker")` into the model, and RUNNING the model runs
    the command (unsandboxed: the marker exists). Sandboxed (check/postsynth.py's own `vl_build` and
    `vl_run`): the model runs, its fork is denied, no marker.
"""

import os
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
for p in (os.path.join(SVGOLF, "check"), os.path.join(SVGOLF, "score"), HERE):
    sys.path.insert(0, p)
import sandbox  # noqa: E402
import attacks  # noqa: E402
import postsynth  # noqa: E402
import score  # noqa: E402

HAVE_TOOLS = all(shutil.which(t) for t in ("yosys", "verilator", "make", "c++"))


def mechanism_works():
    pol = sandbox.configure("auto", log=lambda *a: None)
    ok = pol.active
    sandbox.configure("off")
    return ok


@unittest.skipUnless(HAVE_TOOLS, "yosys, verilator, make and c++ are needed")
class ToolAttacks(unittest.TestCase):
    def setUp(self):
        self.tmp = os.path.realpath(tempfile.mkdtemp(prefix="wps-tools-"))

    def tearDown(self):
        sandbox.configure("off")
        shutil.rmtree(self.tmp, ignore_errors=True)

    def yosys_leak(self):
        hexfile = os.path.join(self.tmp, "victim.hex")
        with open(hexfile, "w") as fh:
            fh.write("deadbeef\ncafef00d\n")
        sv = os.path.join(self.tmp, "t.sv")
        with open(sv, "w") as fh:
            fh.write(attacks.YOSYS_READMEMH.replace("@HEXFILE@", hexfile))
        work = os.path.join(self.tmp, "ywork")
        shutil.rmtree(work, ignore_errors=True)
        os.makedirs(work)
        out = os.path.join(work, "out.il")
        try:
            score.run_yosys(score.yosys_bin(), f'read_verilog -sv "{sv}"\nhierarchy -top t\nproc\nmemory_collect\n'
                            f'opt_clean\nwrite_rtlil "{out}"\n', work, "leak", reads=[sv])
        except score.ScoreError as e:
            return None, str(e)
        with open(out) as fh:
            return ("1101111010101101" in fh.read()), ""

    def test_yosys_loads_a_host_file_unsandboxed_and_cannot_sandboxed(self):
        leaked, _ = self.yosys_leak()
        self.assertTrue(leaked, "the attack is not real: Yosys did not load the file")
        if not mechanism_works():
            self.skipTest("no sandbox mechanism on this machine")
        sandbox.configure("require", log=lambda *a: None)
        leaked, err = self.yosys_leak()
        self.assertIsNone(leaked)
        self.assertIn("Can not open file", err)

    def verilator_run(self):
        marker = os.path.join(self.tmp, "marker-" + str(len(os.listdir(self.tmp))))
        sv = os.path.join(self.tmp, "hostile.sv")
        with open(sv, "w") as fh:
            fh.write(attacks.VERILATOR_SYSTEM.replace("@MARKER@", marker))
        work = os.path.join(self.tmp, "vwork")
        shutil.rmtree(work, ignore_errors=True)
        os.makedirs(work)
        exe, _, err = postsynth.vl_build([sv], "t", {}, [("a", 4)], [("y", 4)], work, "hostile", 300, rtl=True)
        self.assertIsNone(err, err)
        rows, _, err = postsynth.vl_run(exe, [("a", 4)], [("y", 4)], [{"a": 3}], work, "hostile", 60)
        return os.path.exists(marker), rows, err

    def test_a_compiled_model_runs_system_unsandboxed_and_cannot_sandboxed(self):
        ran, rows, err = self.verilator_run()
        self.assertTrue(ran, "the attack is not real: the model did not run $system")
        if not mechanism_works():
            self.skipTest("no sandbox mechanism on this machine")
        sandbox.configure("require", log=lambda *a: None)
        ran, rows, err = self.verilator_run()
        self.assertFalse(ran, "the model's $system ran inside the sandbox")
        self.assertEqual(rows, [{"y": "0011"}], err)        # the model itself still computes


if __name__ == "__main__":
    unittest.main(verbosity=1)
