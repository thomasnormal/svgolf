#!/usr/bin/env python3.12
"""Validate a `clmul_n` design against the carry-less product in simulation (Verilator).

    python3.12 tests/clmul/validate/sim.py DESIGN.sv [--plan full|quick] [--bad]
    python3.12 tests/clmul/validate/sim.py DESIGN.sv --width N [--vectors K] [--bad]

The testbench is `tb.sv` next to this script (`p !== XOR over the set bits i of b of (a << i)` on 2N-1
bits), built by `verilator --binary --timing`, one model per width. Verilator is 2-state: an `x` output
cannot show up as a mismatch here (the checker's static rules and its `postsynth` stage are the x/z
defence, README.md "Rules"); this script checks the FUNCTION. Plans:

  full   (default; a few minutes: about 2.5 s of C++ build per point) exhaustive at N = 1..8 and
         100 000 random vectors (+ corners) at N = 9, 12, 13, 16, 24, 31, 32, 33, 48, 64;
  quick  (seconds) exhaustive at N = 1..4 and 100 random vectors at N = 8 and N = 9;
  --width N  ONE width, for the per-width baselines: exhaustive when N <= 8, else K random vectors
         (+ corners; default 20 000).

--bad inverts the verdict, for the negative designs: exit status 0 iff at least one point has a
mismatch (the design is functionally wrong somewhere in the plan) and every point ran.

Prints one RESULT (and up to three MISMATCH) lines per point; exit status 0 iff every point ran and found
no mismatch (with --bad: iff every point ran and some point found one). Needs verilator (5).
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TB = os.path.join(HERE, "tb.sv")


def verilator(design, n, exh, nrand, work):
    d = os.path.join(work, f"v{n}_{exh}_{nrand}")
    subprocess.run(["verilator", "--binary", "--timing", "-j", "2", "-Wno-fatal", "-Wno-WIDTH",
                    f"-GN={n}", f"-GEXH={exh}", f"-GNRAND={nrand}", "--top-module", "tb", TB,
                    design, "-Mdir", d, "-o", "vtb"], check=True, capture_output=True, text=True)
    return subprocess.run([os.path.join(d, "vtb")], capture_output=True, text=True).stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("design")
    ap.add_argument("--plan", choices=["full", "quick"], default="full")
    ap.add_argument("--width", type=int)
    ap.add_argument("--vectors", type=int, default=20000)
    ap.add_argument("--bad", action="store_true")
    args = ap.parse_args()
    design = os.path.abspath(args.design)
    if args.width:
        n = args.width
        points = [("verilator", n, 1 if n <= 8 else 0, args.vectors)]
    elif args.plan == "quick":
        points = [("verilator", n, 1, 0) for n in (1, 2, 3, 4)] + [
            ("verilator", n, 0, 100) for n in (8, 9)]
    else:
        points = ([("verilator", n, 1, 0) for n in range(1, 9)]
                  + [("verilator", n, 0, 100000) for n in (9, 12, 13, 16, 24, 31, 32, 33, 48, 64)])
    work = tempfile.mkdtemp(prefix="svgolf-clmul-sim-")
    bad, ran = 0, 0
    try:
        for tool, n, exh, nrand in points:
            try:
                out = verilator(design, n, exh, nrand, work)
            except subprocess.CalledProcessError as e:
                print(f"FAIL {tool} N={n}: {(e.stderr or e.stdout or '')[-800:]}", flush=True)
                bad += 1
                continue
            lines = [ln for ln in out.splitlines() if ln.startswith(("RESULT", "MISMATCH"))]
            for ln in lines[:4]:
                print(f"{tool:9s} {ln}", flush=True)
            m = [re.search(r"errors=(\d+)", ln) for ln in lines if ln.startswith("RESULT")]
            if not m or not m[-1]:
                bad += 1
                continue
            ran += 1
            if int(m[-1].group(1)) != 0:
                bad += 1
        if args.bad:
            ok = ran == len(points) and bad > 0
            print("sim:", "PASS (mismatch found, as expected)" if ok else "FAIL (a negative design agrees "
                  "with the carry-less product on every point, or a point did not run)")
            return 0 if ok else 1
    finally:
        shutil.rmtree(work, ignore_errors=True)
    print("sim:", "PASS" if not bad else f"FAIL ({bad} point(s))")
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
