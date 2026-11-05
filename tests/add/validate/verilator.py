#!/usr/bin/env python3.12
"""Bulk Verilator check of the `add` adders: random vectors, or every input combination.

    python3.12 tests/add/validate/verilator.py [--widths 5,16,33,64] [--vectors 200000]   (from svgolf/)
    python3.12 tests/add/validate/verilator.py --exhaustive --widths 1,2,3,4,5,6,7,8,9,10

Builds each adder (the ripple-carry reference and the two prefix-adder
baselines) with Verilator at each width, drives it from a C++ testbench
with a fixed-seed random stream (plus the all-ones corner cases), and
compares `s` and `cout` against `a + b + cin` computed in 128-bit integers.
Widths up to 64. With --exhaustive, every input combination instead
(2^(2N+1) vectors; widths up to 12). validate.py runs the same designs
through Verilator too, but on few vectors, next to ls-sv's `run2` and with
the mutants; this script is the one for big counts (the arithmetic is
checked in C++, so a vector costs nanoseconds).
Exit status 0 iff every run has zero mismatches.
"""

import argparse
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
# Paths relative to svgolf/.
DESIGNS = ["tasks/add/reference/add_n.sv", "tests/add/baselines/add_n_sklansky.sv",
           "tests/add/baselines/add_n_kogge_stone.sv"]

TB = r"""
#include "Vadd_n.h"
#include "verilated.h"
#include <cstdint>
#include <cstdio>
#include <random>
int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  Vadd_n top;
  const int n = NBITS;
  const unsigned __int128 m = (((unsigned __int128)1) << n) - 1;
  std::mt19937_64 rng(20261028);
  long bad = 0, total = 0;
  const long nvec = EXHAUSTIVE ? (2L << (2 * n)) : NVEC;
  for (long k = 0; k < nvec; ++k) {
    uint64_t a = rng() & (uint64_t)m, b = rng() & (uint64_t)m, c = rng() & 1;
    if (k < 4) { a = (uint64_t)m; b = (k & 1) ? 0 : (uint64_t)m; c = (k >> 1) & 1; }
    if (EXHAUSTIVE) { a = k & (uint64_t)m; b = (k >> n) & (uint64_t)m; c = (k >> (2 * n)) & 1; }
    top.a = a; top.b = b; top.cin = c; top.eval();
    const unsigned __int128 t = (unsigned __int128)a + b + c;
    const uint64_t es = (uint64_t)(t & m), ec = (uint64_t)(t >> n);
    ++total;
    if ((uint64_t)top.s != es || (uint64_t)top.cout != ec) {
      if (bad < 3) printf("mismatch a=%llx b=%llx cin=%llu\n", (unsigned long long)a,
                          (unsigned long long)b, (unsigned long long)c);
      ++bad;
    }
  }
  printf("N=%d %s=%ld bad=%ld\n", n, EXHAUSTIVE ? "exhaustive" : "vectors", total, bad);
  return bad != 0;
}
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--widths", default="5,16,33,64")
    ap.add_argument("--vectors", type=int, default=200000)
    ap.add_argument("--exhaustive", action="store_true")
    args = ap.parse_args()
    widths = [int(w) for w in args.widths.split(",")]
    if any(not 1 <= n <= (12 if args.exhaustive else 64) for n in widths):
        ap.error("widths must be in 1..64 (1..12 with --exhaustive)")
    ver = subprocess.run(["verilator", "--version"], capture_output=True, text=True).stdout.strip()
    print(ver, flush=True)
    work = tempfile.mkdtemp(prefix="svgolf-add-verilator-")
    failures = 0
    try:
        tb = os.path.join(work, "tb.cpp")
        with open(tb, "w") as fh:
            fh.write(TB)
        for rel in DESIGNS:
            for n in widths:
                d = os.path.join(work, f"{os.path.basename(rel)[:-3]}_{n}")
                build = subprocess.run(
                    ["verilator", "--cc", "--exe", "--build", "-O1", "-Wno-fatal", "-Wno-lint",
                     "-Wno-style", f"-GN={n}", "-CFLAGS",
                     f"-DNBITS={n} -DNVEC={args.vectors} -DEXHAUSTIVE={int(args.exhaustive)}",
                     "--top-module", "add_n", "-Mdir", d, os.path.join(SVGOLF, rel), tb],
                    capture_output=True, text=True)
                if build.returncode != 0:
                    print(f"[FAIL] {rel} N={n}: build failed\n{build.stderr[-1500:]}", flush=True)
                    failures += 1
                    continue
                run = subprocess.run([os.path.join(d, "Vadd_n")], capture_output=True, text=True)
                ok = run.returncode == 0
                failures += not ok
                print(f"[{'ok' if ok else 'FAIL'}] {rel}: {run.stdout.strip()}", flush=True)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    print("verilator:", "PASS" if not failures else "FAIL")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
