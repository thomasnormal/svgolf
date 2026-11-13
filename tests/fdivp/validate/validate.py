#!/usr/bin/env python3.12
"""Validation of the `fdivp` designs by simulation: the parametric divider `fdiv #(W, P)` against INDEPENDENT oracles.

    python3.12 tests/fdivp/validate/validate.py [--plan quick|full] [--design SV ...] [--jobs J]
    python3.12 tests/fdivp/validate/validate.py --design SV --formats 5,11 8,8 [--bad] [--samples N]

The designs under test are Verilator models (`run_v.py`: every pair of a format with `W + P <= 14`, or sampled
corner-rich pairs; `run_vec.py`: pre-generated vectors) compared with the C++ oracle `oracle.h` (128-bit integers, the
quotient rounded at the spacing of its binade). The oracles themselves are tied to each other first (step `oracles`):
`tasks/fdivp/oracle.py` (exact `fractions.Fraction`, no floating point), `fdivp_model.oracle_int` (exact integers),
`fdivp_model.oracle_frac` (the repository's `tasks/fdivp/spec_validate/oracle.py`, the one validated against the Lean spec), and
the C++ oracle through `oracle_dump.cpp`: all four agree on every pair of every format with `W + P <= 8`
and on sampled pairs above. The Lean spec itself is tied to the reference by the PROOF (`OutN_fdivBits`), so every
simulated pair of the reference is also a test of the spec at that format (`tasks/fdivp/REVIEW.md`).

Plans (default `quick`, about a minute; `full` is hours):

  quick   oracles on K <= 8 + sampled; the reference exhaustively at 12 formats with K <= 10; sampled corner-rich
          pairs (20,000) at (5, 11), (8, 24), (11, 53), (2, 30)
  full    oracles on K <= 10; the reference exhaustively at every format with K <= 14 (66 formats, 3.8 x 10^9 pairs)
          and at (5, 11) and (8, 8) (2^32 pairs each); 200,000 corner-rich pairs at 12 formats up to (11, 53), (2, 62)

`--design SV --formats W,P ...`: one design (a baseline, an attack, a mutant) at the listed formats (exhaustive for
K <= 14 or with `--exhaustive`, else `--samples` pairs); prints one JSON line per format; with `--bad` the exit status is 0 iff SOME format
shows a mismatch (a wrong design is wrong somewhere), without it iff none does. Exit status 0 = every check passed.
"""

import argparse
import json
import os
import shutil
import struct
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
REFERENCE = os.path.join(SVGOLF, "tasks", "fdivp", "reference", "fdivp.sv")
sys.path.insert(0, HERE)

QUICK_EXH = [(2, 2), (2, 3), (3, 2), (2, 5), (3, 4), (4, 3), (5, 3), (4, 5), (3, 7), (7, 3), (2, 8), (8, 2)]
QUICK_SAMPLED = [(5, 11), (8, 24), (11, 53), (2, 30)]
FULL_SAMPLED = [(8, 24), (11, 53), (2, 30), (6, 30), (15, 48), (2, 62), (3, 60), (12, 20), (20, 12), (16, 16),
                (4, 20), (10, 40)]


def formats_upto(kmax):
    return [(w, k - w) for k in range(4, kmax + 1) for w in range(2, k - 1)]


def say(*a):
    print(*a, flush=True)


def run_json(cmd, cwd=HERE):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    lines = [ln for ln in p.stdout.strip().splitlines() if ln.startswith("{")]
    return (json.loads(lines[-1]) if lines else None), p


def exhaustive(sv, w, p, jobs):
    """Verilator vs oracle.h on every pair (K <= 14) as run_v.py does it: one JSON dict."""
    r, proc = run_json([sys.executable, os.path.join(HERE, "run_v.py"), str(w), str(p), "--sv", sv,
                        "--jobs", str(jobs)])
    return r if r is not None else {"W": w, "P": p, "error": (proc.stdout + proc.stderr)[-300:]}


def sampled(sv, w, p, n, seed=1):
    r, proc = run_json([sys.executable, os.path.join(HERE, "run_v.py"), str(w), str(p), "--sv", sv, "--samples",
                        str(n), "--seed", str(seed)])
    return r if r is not None else {"W": w, "P": p, "error": (proc.stdout + proc.stderr)[-300:]}


def vectors(sv, w, p, n, seed=7):
    """Generated vectors (random, exponent-boundary, tie-shaped, corners) through run_vec.py."""
    proc = subprocess.run([sys.executable, os.path.join(HERE, "run_vec.py"), str(w), str(p), str(n), str(seed),
                           "--sv", sv, "--model3"], cwd=HERE, capture_output=True, text=True)
    out = proc.stdout
    ok = (": 0 disagreements" in out and "oracle_int mismatches: 0" in out and '"mismatches": 0' in out
          and proc.returncode == 0)
    return ok, proc.stdout.strip()


def step_oracles(kmax, samples):
    """The four oracles agree: Fraction (tasks/fdivp/oracle.py), exact integers, spec_validate, and oracle.h."""
    import importlib.util
    sp = importlib.util.spec_from_file_location("fdivp_task_oracle", os.path.join(SVGOLF, "tasks", "fdivp", "oracle.py"))
    OF = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(OF)
    import fdivp_model as M
    tmp = tempfile.mkdtemp(prefix="svgolf-fdivp-oracles-")
    try:
        return _step_oracles(kmax, samples, tmp, OF, M)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)       # the run's own directory, never left behind


def _step_oracles(kmax, samples, tmp, OF, M):
    good = True
    dump = os.path.join(tmp, "oracle_dump")
    c = subprocess.run(["c++", "-O2", "-std=c++17", "-o", dump, os.path.join(HERE, "oracle_dump.cpp"),
                        "-I" + HERE], capture_output=True, text=True)
    if c.returncode:
        say("oracles: C++ build failed:", c.stderr[-300:])
        return False
    for w, p in formats_upto(kmax):
        k = w + p
        n = 1 << k
        fn = os.path.join(tmp, f"od_{w}_{p}.bin")
        subprocess.run([dump, str(w), str(p), fn], check=True)
        data = open(fn, "rb").read()
        arr = struct.unpack(f"<{n * n}I", data)
        bad = 0
        for a in range(n):
            for b in range(n):
                f = OF.fdiv(w, p, a, b)
                if not (f == M.oracle_int(w, p, a, b) == int(arr[a * n + b])
                        and (k > 7 or f == M.oracle_frac(w, p, a, b))):
                    bad += 1
        say(f"oracles ({w},{p}): {n * n} pairs, {bad} disagreements among Fraction / integer / C++"
            + (" / spec-validate" if k <= 7 else ""))
        good &= bad == 0
    import random
    rng = random.Random(5)
    # (the Fraction oracle is slow at formats with a huge exponent range, e.g. (20, 12): not sampled here)
    for w, p in QUICK_SAMPLED + [(3, 20), (4, 20)]:
        k = w + p
        bad = 0
        for _ in range(samples):
            a, b = rng.getrandbits(k), rng.getrandbits(k)
            if rng.random() < 0.4:
                a ^= rng.choice([0, 1, 1 << (k - 1), ((1 << w) - 1) << (p - 1), 1 << (p - 1)])
            if OF.fdiv(w, p, a, b) != M.oracle_int(w, p, a, b):
                bad += 1
        say(f"oracles ({w},{p}): {samples} sampled pairs, {bad} disagreements Fraction / integer")
        good &= bad == 0
    return good


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--plan", choices=["quick", "full"], default="quick")
    ap.add_argument("--design", nargs="*", help="designs to test (default: the reference)")
    ap.add_argument("--formats", nargs="*", help="W,P ... (with --design)")
    ap.add_argument("--bad", action="store_true", help="the design is WRONG: some format must show a mismatch")
    ap.add_argument("--samples", type=int, default=200000)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--exhaustive", action="store_true", help="every pair also above K = 14 (2^32 pairs at K = 16: minutes)")
    a = ap.parse_args()
    good = True
    if a.formats:
        fmts = [tuple(int(x) for x in f.split(",")) for f in a.formats]
        for sv in [os.path.abspath(d) for d in (a.design or [REFERENCE])]:
            tot = 0
            for w, p in fmts:
                r = (exhaustive(sv, w, p, 4 if w + p > 14 else a.jobs) if (w + p <= 14 or a.exhaustive)
                     else sampled(sv, w, p, a.samples))
                say(json.dumps(r))
                tot += r["mismatches"] if "mismatches" in r else (1 << 62)
            ok = tot > 0 if a.bad else tot == 0
            say(f"{os.path.relpath(sv, SVGOLF)}: {'wrong somewhere, as expected' if a.bad and ok else 'mismatches ' + str(tot)}"
                if a.bad else f"{os.path.relpath(sv, SVGOLF)}: {'all agree' if ok else 'MISMATCHES ' + str(tot)}")
            good &= ok
        return 0 if good else 1
    full = a.plan == "full"
    sv = os.path.abspath(a.design[0]) if a.design else REFERENCE
    good &= step_oracles(10 if full else 8, 20000 if full else 3000)
    exh = formats_upto(14) + [(5, 11), (8, 8)] if full else QUICK_EXH
    for w, p in exh:
        r = exhaustive(sv, w, p, 4 if w + p > 14 else a.jobs)
        say("exhaustive", json.dumps(r))
        good &= r.get("mismatches", 1) == 0
    for w, p in (FULL_SAMPLED if full else QUICK_SAMPLED):
        n = 200000 if full else 20000
        ok, out = vectors(sv, w, p, n)
        say("vectors", out.replace("\n", " | "))
        good &= ok
    say("fdivp validate: " + ("OK" if good else "FAILED"))
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
